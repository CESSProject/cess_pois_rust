use anyhow::{anyhow, bail, Context, Result};
use core::panic;
use rand::Rng;
use sha2::Digest;
use std::collections::HashMap;
use std::mem;

use super::prove::{AccProof, Commit, CommitProof, DeletionProof, SpaceProof};
use crate::acc::multi_level_acc::{
    verify_delete_update, verify_insert_update, verify_mutilevel_acc,
};
use crate::acc::RsaKey;
use crate::expanders::generate_idle_file::{get_hash, HASH_SIZE};
use crate::expanders::{
    generate_expanders::calc_parents as generate_expanders_calc_parents,
    generate_idle_file::{new_hash, Hasher as ExpanderHasher},
    Expanders,
};
use crate::expanders::{get_bytes, NodeType};
use crate::tree::{check_index_path, verify_path_proof, PathProof};
use crate::util::copy_data;
use crate::{acc, expanders};

pub const MAX_BUF_SIZE: i32 = 1 * 16;
pub static mut SPACE_CHALS: i64 = 22;
pub const PICK: i32 = 1;

#[derive(Clone, Debug)]
pub struct Record {
    pub key: acc::RsaKey,
    pub acc: Vec<u8>,
    pub front: i64,
    pub rear: i64,
    pub record: i64,
}
#[derive(Clone, Debug)]
pub struct ProverNode {
    pub id: Vec<u8>,
    pub commit_buf: Vec<Commit>,
    pub buf_size: i32,
    pub record: Option<Record>,
}

#[derive(Clone, Debug)]
pub struct Verifier {
    pub expanders: Expanders,
    pub nodes: HashMap<String, ProverNode>,
}

impl Verifier {
    pub fn new(k: i64, n: i64, d: i64) -> Self {
        unsafe {
            SPACE_CHALS = (n as f64).log2().floor() as i64;
        }

        Verifier {
            expanders: Expanders::new(k, n, d),
            nodes: HashMap::new(),
        }
    }

    pub fn register_prover_node(
        &mut self,
        id: &[u8],
        key: RsaKey,
        acc: &[u8],
        front: i64,
        rear: i64,
    ) {
        let node = ProverNode::new(&id, key, acc, front, rear);
        let id = hex::encode(id);
        self.nodes.insert(id, node);
    }

    pub fn get_node(&self, id: &[u8]) -> Result<&ProverNode> {
        let id = hex::encode(id);
        let node = self
            .nodes
            .get(&id)
            .with_context(|| format!("Node not found."))?;
        Ok(node)
    }

    pub fn is_logout(&self, id: &[u8]) -> bool {
        let id = hex::encode(id);
        !self.nodes.contains_key(&id)
    }

    pub fn logout_prover_node(&self, id: &[u8]) -> Result<(Vec<u8>, i64, i64)> {
        let node = self.get_node(id);

        match node {
            Ok(node) => {
                let (acc, front, rear) = match &node.record {
                    Some(record) => (record.acc.clone(), record.front, record.rear),
                    None => panic!("Record not found."),
                };

                Ok((acc, front, rear))
            }
            Err(err) => {
                bail!(err);
            }
        }
    }

    pub fn receive_commits(&mut self, id: &[u8], commits: &mut [Commit]) -> bool {
        let id = hex::encode(id);

        let p_node = match self.nodes.get(&id) {
            Some(node) => node.clone(),
            None => return false,
        };

        if !p_node.id.eq(&hex::decode(id).unwrap()) {
            return false;
        }

        if commits.len() > (MAX_BUF_SIZE - p_node.buf_size) as usize {
            let commits = &mut commits[..(MAX_BUF_SIZE - p_node.buf_size) as usize];
            return self.validate_commit(&p_node, commits);
        } else {
            return self.validate_commit(&p_node, commits);
        }
    }

    fn validate_commit(&mut self, p_node: &ProverNode, commits: &mut [Commit]) -> bool {
        let mut p_node = p_node.clone();
        for i in 0..commits.len() {
            if commits[i].file_index <= p_node.record.as_ref().unwrap().front {
                return false;
            }

            if commits[i].roots.len() != (self.expanders.k + 2) as usize {
                return false;
            }
            // TODO: find a way to reset the hasher instead of creating new object
            let hash = new_hash();
            let result = match hash {
                // TODO: write a generic function for the below task.
                ExpanderHasher::SHA256(hash) => {
                    let mut hash = hash;
                    for j in 0..commits[i].roots.len() - 1 {
                        hash.update(&commits[i].roots[j]);
                    }

                    let result = hash.finalize();
                    result.to_vec()
                }
                ExpanderHasher::SHA512(hash) => {
                    let mut hash = hash;
                    for j in 0..commits[i].roots.len() - 1 {
                        hash.update(&commits[i].roots[j]);
                    }

                    let result = hash.finalize();
                    result.to_vec()
                }
            };

            if commits[i].roots[self.expanders.k as usize + 1] != result[..] {
                return false;
            }

            p_node.commit_buf.push(commits[i].clone());
            p_node.buf_size += 1;
        }
        if let Some(node) = self.nodes.get_mut(&hex::encode(&p_node.id)) {
            *node = p_node;
        }

        true
    }

    pub fn commit_challenges(&mut self, id: &[u8], left: i32, right: i32) -> Result<Vec<Vec<i64>>> {
        // let id = hex::encode(id);
        // let p_node = self
        //     .nodes
        //     .get(&id)
        //     .with_context(|| format!("Prover node not found"))?;

        let p_node = match self.get_node(id) {
            Ok(node) => node,
            Err(err) => {
                bail!(err);
            }
        };

        if right - left <= 0 || right > p_node.buf_size || left < 0 {
            let err = anyhow!("bad file number");
            bail!("generate commit challenges error: {}", err);
        }
        let mut challenges: Vec<Vec<i64>> = Vec::with_capacity((right - left) as usize);
        let mut rng = rand::thread_rng();
        for i in left..right {
            // let idx = i - left;
            let mut inner_vec = vec![0; self.expanders.k as usize + 2];
            inner_vec[0] = p_node.commit_buf[i as usize].file_index;
            let r = rng.gen_range(0..self.expanders.n);
            inner_vec[1] = r + self.expanders.n * self.expanders.k;

            for j in 2..=(self.expanders.k + 1) as usize {
                let r = rng.gen_range(0..(self.expanders.d + 1));
                inner_vec[j] = r;
            }

            challenges.push(inner_vec);
        }
        Ok(challenges)
    }

    pub fn space_challenges(&self, params: i64) -> Result<Vec<i64>> {
        //let mut inner_vec = vec![0; self.expanders.k as usize + 2];
        let mut challenges: Vec<i64> = vec![0; params as usize];
        let mut mp: HashMap<i64, ()> = HashMap::new();
        let mut rng = rand::thread_rng();
        for i in 0..params {
            loop {
                let mut r = rng.gen_range(0..self.expanders.n);
                if mp.contains_key(&r) {
                    continue;
                }
                mp.insert(r, ());
                r += self.expanders.n * self.expanders.k;
                challenges[i as usize] = r;
                break;
            }
        }

        Ok(challenges)
    }

    pub fn verify_commit_proofs(
        &self,
        id: &[u8],
        chals: Vec<Vec<i64>>,
        proofs: Vec<Vec<CommitProof>>,
    ) -> Result<()> {
        // let id_str = hex::encode(id);
        // let p_node = self
        //     .nodes
        //     .get(&id_str)
        //     .with_context(|| format!("verify commit proofs error: Prover node not found"))?;
        let p_node = match self.get_node(id) {
            Ok(node) => node,
            Err(err) => {
                bail!(err);
            }
        };

        if chals.len() != proofs.len() || chals.len() > p_node.buf_size as usize {
            let err = anyhow!("bad proof data");
            bail!("verify commit proofs error: {}", err);
        }

        if let Err(err) = self.verify_node_dependencies(id, chals.clone(), proofs.clone(), PICK) {
            bail!("verify commit proofs error {}", err);
        }

        let mut index = 0;
        for i in 0..p_node.buf_size {
            if chals[0][0] == p_node.commit_buf[i as usize].file_index {
                index = i;
                break;
            }
        }
        let front_side = (mem::size_of::<NodeType>() + id.len() + 8) as i32;
        let hash_size = HASH_SIZE;
        let mut label =
            vec![0; front_side as usize + (self.expanders.d + 1) as usize * hash_size as usize];
        for i in 0..proofs.len() {
            if chals[i][1] != proofs[i][0].node.index as i64 {
                let err = anyhow!("bad expanders node index");
                bail!("verify commit proofs error {}", err);
            }

            let mut idx: NodeType;
            for j in 1..chals[i].len() {
                if j == 1 {
                    idx = chals[i][1] as NodeType;
                } else {
                    idx = proofs[i][j - 2].parents[chals[i][j] as usize].index as NodeType;
                }

                let layer = idx as i64 / self.expanders.n;
                let mut root = &p_node.commit_buf[index as usize + i].roots[layer as usize];
                let path_proof = PathProof {
                    locs: proofs[i][j - 1].node.locs.clone(),
                    path: proofs[i][j - 1].node.paths.clone(),
                };
                if !verify_path_proof(root, &proofs[i][j - 1].node.label, path_proof) {
                    let err = anyhow!("verify path proof error");
                    bail!("verify commit proofs error: {}", err);
                }

                if proofs[i][j - 1].parents.len() <= 0 {
                    continue;
                }

                copy_data(&mut label, &[id, &get_bytes(chals[i][0]), &get_bytes(idx)]);

                let mut size = front_side;

                for p in &proofs[i][j - 1].parents {
                    if p.index as i64 >= layer * self.expanders.n {
                        root = &p_node.commit_buf[index as usize + i as usize].roots[layer as usize]
                    } else {
                        root = &p_node.commit_buf[index as usize + i as usize].roots
                            [layer as usize - 1]
                    }
                    let path_proof = PathProof {
                        locs: p.locs.clone(),
                        path: p.paths.clone(),
                    };
                    if !verify_path_proof(root, &p.label, path_proof) {
                        let err = anyhow!("verify parent path proof error");
                        bail!("verify commit proofs error: {}", err);
                    }
                    label[(size as usize)..(size + HASH_SIZE) as usize].copy_from_slice(&p.label);
                    size += HASH_SIZE
                }
                if !get_hash(&label).eq(&proofs[i][j - 1].node.label) {
                    let err = anyhow!("verify label error");
                    bail!("verify commit proofs error: {}", err);
                }
            }
        }
        Ok(())
    }

    pub fn verify_node_dependencies(
        &self,
        id: &[u8],
        chals: Vec<Vec<i64>>,
        proofs: Vec<Vec<CommitProof>>,
        pick: i32,
    ) -> Result<()> {
        let mut pick = pick;
        if pick as usize > proofs.len() {
            pick = proofs.len() as i32;
        }
        let mut rng = rand::thread_rng();
        for _ in 0..pick {
            let r1 = rng.gen_range(0..proofs.len());
            let r2 = rng.gen_range(0..proofs[r1].len());
            let proof = &proofs[r1][r2];
            let mut node = expanders::Node::new(proof.node.index);
            generate_expanders_calc_parents(&self.expanders, &mut node, id, chals[r1][0]);
            for j in 0..node.parents.len() {
                if node.parents[j] != proof.parents[j].index {
                    let err = anyhow!("node relationship mismatch");
                    bail!("verify node dependencies error: {}", err);
                }
            }
        }
        Ok(())
    }

    pub fn verify_acc(&mut self, id: &[u8], chals: Vec<Vec<i64>>, proof: AccProof) -> Result<()> {
        let id_str = hex::encode(id);

        if let Some(p_node) = self.nodes.get_mut(&id_str) {
            if chals.len() != proof.indexs.len() || chals.len() > p_node.buf_size as usize {
                let err = anyhow!("bad proof data");
                bail!("verify acc proofs error: {}", err);
            }

            let mut index = 0;
            for i in 0..p_node.buf_size {
                if chals[0][0] == p_node.commit_buf[i as usize].file_index {
                    index = i;
                    break;
                }
            }

            let mut label = vec![0u8; id.len() + 8 + HASH_SIZE as usize];

            for i in 0..chals.len() {
                if chals[i][0] != proof.indexs[i]
                    || chals[i][0] != p_node.record.as_ref().unwrap().rear + i as i64 + 1
                {
                    let err = anyhow!("bad file index");
                    bail!("verify acc proofs error: {}", err);
                }

                copy_data(
                    &mut label,
                    &[
                        id,
                        &get_bytes(chals[i][0]),
                        &p_node.commit_buf[i + index as usize].roots[self.expanders.k as usize],
                    ],
                );

                if !get_hash(&label).eq(&proof.labels[i]) {
                    let err = anyhow!("verify file label error");
                    bail!("verify acc proofs error: {}", err);
                }
            }

            if !verify_insert_update(
                p_node.record.clone().unwrap().key,
                proof.wit_chains,
                proof.labels,
                proof.acc_path.clone(),
                p_node.record.clone().unwrap().acc,
            ) {
                let err = anyhow!("verify muti-level acc error");
                bail!("verify acc proofs error: {}", err);
            }

            p_node.record.as_mut().unwrap().acc = proof.acc_path.last().cloned().unwrap();
            p_node.commit_buf.splice(
                index as usize..(index as usize + chals.len()) as usize,
                std::iter::empty(),
            );
            p_node.buf_size -= chals.len() as i32;
            p_node.record.as_mut().unwrap().rear += chals.len() as i64;
        } else {
            let err = anyhow!("Prover node not found");
            bail!("verify acc proofs error: {}", err);
        }

        Ok(())
    }

    pub fn verify_space(
        &self,
        p_node: &ProverNode,
        chals: Vec<i64>,
        proof: &mut SpaceProof,
    ) -> Result<()> {
        if chals.len() <= 0
            || p_node.record.as_ref().unwrap().record + 1 != proof.left
            || p_node.record.as_ref().unwrap().rear + 1 < proof.right
        {
            let err = anyhow!("bad proof data");
            bail!("verify space proofs error: {}", err);
        }
        let mut label: Vec<u8> = vec![0; p_node.id.len() + 8 + HASH_SIZE as usize];
        for i in 0..proof.roots.len() {
            for j in 0..chals.len() {
                if chals[j] != proof.proofs[i][j].index as i64 {
                    let err = anyhow!("bad file index");
                    bail!("verify space proofs error: {}", err);
                }
                let path_proof = PathProof {
                    locs: proof.proofs[i][j].locs.clone(),
                    path: proof.proofs[i][j].paths.clone(),
                };

                if !check_index_path(chals[j], &path_proof.locs) {
                    let err = anyhow!("verify index path error");
                    bail!("verify space proofs error: {}", err);
                }
                if !verify_path_proof(&proof.roots[i], &proof.proofs[i][j].label, path_proof) {
                    let err = anyhow!("verify path proof error");
                    bail!("verify space proofs error: {}", err);
                }
            }
            copy_data(
                &mut label,
                &[
                    &p_node.id,
                    &get_bytes(proof.left + i as i64),
                    &proof.roots[i],
                ],
            );

            if !get_hash(&label).eq(&proof.wit_chains[i].elem) {
                let err = anyhow!("verify file label error");
                bail!("verify space proofs error: {}", err);
            }
            //VerifyMutilevelAcc
            if !verify_mutilevel_acc(
                &p_node.record.as_ref().unwrap().key,
                Some(&mut proof.wit_chains[i]),
                &p_node.record.as_ref().unwrap().acc,
            ) {
                let err = anyhow!("verify acc proof error");
                bail!("verify space proofs error: {}", err);
            }
        }
        Ok(())
    }

    pub fn space_verification_handle<'a>(
        &'a mut self,
        id: &'a [u8],
        key: acc::RsaKey,
        acc: &'a [u8],
        front: i64,
        rear: i64,
    ) -> impl FnMut(&[i64], &mut SpaceProof) -> Result<bool> + 'a {
        let mut p_node = ProverNode::new(id, key, acc, front, rear);

        move |chals: &[i64], proof: &mut SpaceProof| -> Result<bool> {
            if let Err(_) = self.verify_space(&mut p_node, chals.to_vec(), proof) {
                return Ok(false);
            }
            p_node.record.as_mut().unwrap().record = proof.right - 1;
            if p_node.record.as_ref().unwrap().record == p_node.record.as_ref().unwrap().rear {
                Ok(true)
            } else {
                Ok(false)
            }
        }
    }

    pub fn verify_deletion(&mut self, id: &[u8], proof: &mut DeletionProof) -> Result<()> {
        let id_str = hex::encode(id);
        let p_node = self
            .nodes
            .get_mut(&id_str)
            .with_context(|| format!("Prover node not found"))?;

        if p_node.buf_size > 0 {
            let err = anyhow!("commit proof not finished");
            bail!("verify deletion proofs error: {}", err);
        }
        let lens = proof.roots.len();
        if lens
            > (p_node.record.as_ref().unwrap().rear - p_node.record.as_ref().unwrap().front)
                as usize
        {
            let err = anyhow!("file number out of range");
            bail!("verify deletion proofs error: {}", err);
        }
        let mut labels: Vec<Vec<u8>> = Vec::new();
        for i in 0..lens {
            let mut label: Vec<u8> = vec![0; id.len() + 8 + HASH_SIZE as usize];
            copy_data(
                &mut label,
                &[
                    id,
                    &get_bytes(p_node.record.as_ref().unwrap().front + i as i64 + 1),
                    &proof.roots[i],
                ],
            );

            labels.push(get_hash(&label));
        }

        if verify_delete_update(
            p_node.record.as_ref().unwrap().key.clone(),
            &mut proof.wit_chain,
            labels,
            proof.acc_path.clone(),
            &p_node.record.as_ref().unwrap().acc,
        ) {
            let err = anyhow!("verify acc proof error");
            bail!("verify deletion proofs error: {}", err);
        }

        p_node.record.as_mut().unwrap().front += lens as i64;

        Ok(())
    }
}

impl ProverNode {
    pub fn new(id: &[u8], key: RsaKey, acc: &[u8], front: i64, rear: i64) -> Self {
        Self {
            id: id.to_vec(),
            commit_buf: Vec::<Commit>::with_capacity(MAX_BUF_SIZE as usize),
            buf_size: 0,
            record: Some(Record {
                acc: acc.to_vec(),
                front,
                rear,
                key,
                record: front,
            }),
        }
    }
}
