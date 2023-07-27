use anyhow::{anyhow, bail, Context, Result};
use core::panic;
use rand::Rng;
use sha2::Digest;
use std::collections::HashMap;
use std::mem;

use super::prove::{AccProof, CommitProof, Commits, DeletionProof, SpaceProof};
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
use lazy_static::lazy_static;
use std::sync::Mutex;

lazy_static! {
    pub static ref CLUSTER_SIZE: Mutex<i64> = Mutex::new(8);
    pub static ref SPACE_CHALS: Mutex<i64> = Mutex::new(8);
}

pub const IDLE_SET_LEN: i64 = 32;
pub const PICK: i32 = 4;

#[derive(Clone, Debug)]
pub struct Record {
    pub key: acc::RsaKey,
    pub acc: Vec<u8>,
    pub front: i64,
    pub rear: i64,
    pub record: i64,
}
#[derive(Clone, Default, Debug)]
pub struct ProverNode {
    pub id: Vec<u8>,
    pub commit_buf: Commits,
    pub record: Option<Record>,
}

#[derive(Clone, Debug)]
pub struct Verifier {
    pub expanders: Expanders,
    pub nodes: HashMap<String, ProverNode>,
}

impl Verifier {
    pub fn new(k: i64, n: i64, d: i64) -> Self {
        {
            let mut space_chals = SPACE_CHALS.lock().unwrap();
            *space_chals = k;

            let mut cluster_size = CLUSTER_SIZE.lock().unwrap();
            *cluster_size = k;
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
            .with_context(|| format!("prover node not found."))?;
        Ok(node)
    }

    pub fn is_logout(&self, id: &[u8]) -> bool {
        let id = hex::encode(id);
        !self.nodes.contains_key(&id)
    }

    pub fn logout_prover_node(&mut self, id: &[u8]) -> Result<(Vec<u8>, i64, i64)> {
        let node = self.get_node(id);

        match node {
            Ok(node) => {
                let (acc, front, rear) = match &node.record {
                    Some(record) => (record.acc.clone(), record.front, record.rear),
                    None => panic!("Record not found."),
                };
                let id = hex::encode(id);
                self.nodes.remove(&id);
                Ok((acc, front, rear))
            }
            Err(_) => Ok((vec![], 0, 0)),
        }
    }

    pub fn receive_commits(&mut self, id: &[u8], commits: &Commits) -> bool {
        let id = hex::encode(id);

        match self.nodes.get_mut(&id) {
            Some(p_node) => {
                if !p_node.id.eq(&hex::decode(id).unwrap()) {
                    return false;
                }
        
                for i in 0..commits.file_indexs.len() {
                    if commits.file_indexs[i] <= p_node.record.as_ref().unwrap().rear {
                        return false;
                    }
                }
        
                let root_num;
                {
                    let cluster_size = CLUSTER_SIZE.lock().unwrap();
                    root_num = (*cluster_size + self.expanders.k) * IDLE_SET_LEN + 1;
                }
                if commits.roots.len() != root_num as usize {
                    return false;
                }
        
                let hash = new_hash();
        
                let result = match hash {
                    ExpanderHasher::SHA256(hash) => {
                        let mut hash = hash;
                        for j in 0..commits.roots.len() - 1 {
                            hash.update(commits.roots[j].clone());
                        }
        
                        let result = hash.finalize();
                        result.to_vec()
                    }
                    ExpanderHasher::SHA512(hash) => {
                        let mut hash = hash;
                        for j in 0..commits.roots.len() - 1 {
                            hash.update(commits.roots[j].clone());
                        }
        
                        let result = hash.finalize();
                        result.to_vec()
                    }
                };
                if !commits.roots[commits.roots.len() - 1].eq(&result) {
                    return false;
                }
        
                p_node.commit_buf = commits.clone();
                return true;
            },
            None => return false,
        };
    }

    pub fn commit_challenges(&mut self, id: &[u8]) -> Result<Vec<Vec<i64>>> {
        let p_node = match self.get_node(id) {
            Ok(node) => node,
            Err(err) => {
                bail!("generate commit challenges error: {}", err);
            }
        };

        let mut challenges: Vec<Vec<i64>> = Vec::with_capacity(IDLE_SET_LEN as usize);

        let mut rng = rand::thread_rng();
        let cluster_size;
        {
            let value = CLUSTER_SIZE.lock().unwrap();
            cluster_size = *value;
        }
        let start = (p_node.commit_buf.file_indexs[0] - 1) / cluster_size;
        for i in 0..IDLE_SET_LEN {
            let mut inner_vec = vec![0; (self.expanders.k + cluster_size + 1) as usize];
            inner_vec[0] = start + i + 1;
            for j in 1..=cluster_size {
                let mut r = rng.gen_range(0..self.expanders.n);
                r += self.expanders.n * self.expanders.k;
                inner_vec[j as usize] = r;
            }
            let mut r = rng.gen_range(0..self.expanders.n);
            r += self.expanders.n * (self.expanders.k - 1);
            inner_vec[cluster_size as usize + 1] = r;

            for j in cluster_size as usize + 2..inner_vec.len() {
                let r = rng.gen_range(0..self.expanders.d + 1);
                inner_vec[j] = r;
            }

            challenges.push(inner_vec);
        }
        Ok(challenges)
    }

    pub fn space_challenges(&self, params: i64) -> Result<Vec<i64>> {
        //Randomly select several nodes from idle files as random challenges
        let mut params = params;
        {
            let space_chals = SPACE_CHALS.lock().unwrap();
            if params < *space_chals {
                params = *space_chals;
            }
        }
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
        let p_node = match self.get_node(id) {
            Ok(node) => node,
            Err(err) => {
                bail!("verify commit proofs error: {}", err);
            }
        };

        if chals.len() != proofs.len() || chals.len() != IDLE_SET_LEN as usize {
            let err = anyhow!("bad proof data");
            bail!("verify commit proofs error: {}", err);
        }

        if let Err(err) = self.verify_node_dependencies(id, chals.clone(), proofs.clone(), PICK) {
            bail!("verify commit proofs error {}", err);
        }

        let front_size = (mem::size_of::<NodeType>() + id.len() + 8 + 8) as i32;
        let hash_size = HASH_SIZE;
        let mut label = vec![
            0;
            front_size as usize
                + (self.expanders.d + 1) as usize * hash_size as usize
                + IDLE_SET_LEN as usize * hash_size as usize
        ];

        let zero = vec![
            0;
            (self.expanders.d + 1) as usize * hash_size as usize
                + IDLE_SET_LEN as usize * hash_size as usize
        ];

        let cluster_size;
        {
            let value = CLUSTER_SIZE.lock().unwrap();
            cluster_size = *value;
        }
        let mut hash: Vec<u8>;
        let mut idx: NodeType;
        for i in 0..proofs.len() {
            for j in 1..cluster_size as usize + 1 {
                if chals[i][j] != proofs[i][j - 1].node.index as i64 {
                    let err = anyhow!("bad expanders node index");
                    bail!("verify commit proofs error {}", err);
                }
            }
            
            for j in 1..chals[i].len() {
                if j <= cluster_size as usize + 1 {
                    idx = chals[i][j] as NodeType;
                } else {
                    idx = proofs[i][j - 2].parents[chals[i][j] as usize].index as NodeType;
                }

                let layer: i64;
                if j <= cluster_size as usize {
                    layer = self.expanders.k + j as i64 - 1;
                } else {
                    layer = idx as i64 / self.expanders.n;
                }
                let mut root = &p_node.commit_buf.roots[layer as usize * IDLE_SET_LEN as usize
                    + (chals[i][0] as usize - 1) % IDLE_SET_LEN as usize];
                let path_proof = PathProof {
                    locs: proofs[i][j - 1].node.locs.clone(),
                    path: proofs[i][j - 1].node.paths.clone(),
                };
                if !verify_path_proof(root, &proofs[i][j - 1].node.label, path_proof) {
                    let err = anyhow!("verify path proof error");
                    bail!("verify commit proofs error: {}", err);
                }

                if layer >= self.expanders.k {
                    copy_data(
                        &mut label,
                        &[
                            id,
                            &get_bytes(chals[i][0]),
                            &get_bytes((chals[i][0] - 1) * cluster_size + j as i64),
                            &get_bytes(idx),
                        ],
                    );
                } else {
                    copy_data(
                        &mut label,
                        &[
                            id,
                            &get_bytes(chals[i][0]),
                            &get_bytes(0 as i64),
                            &get_bytes(idx),
                        ],
                    );
                }

                if layer > 0 {
                    let mut size = front_size;
                    let mut logical_layer = layer;
                    if logical_layer > self.expanders.k {
                        logical_layer = self.expanders.k;
                    }
                    
                    for p in &proofs[i][j - 1].parents {
                        if p.index as i64 >= logical_layer * self.expanders.n {
                            root = &p_node.commit_buf.roots[layer as usize * IDLE_SET_LEN as usize
                                + (chals[i][0] - 1) as usize % IDLE_SET_LEN as usize]
                        } else {
                            root = &p_node.commit_buf.roots[(logical_layer as usize - 1)
                                * IDLE_SET_LEN as usize
                                + (chals[i][0] - 1) as usize % IDLE_SET_LEN as usize];
                        }
                        let path_proof = PathProof {
                            locs: p.locs.clone(),
                            path: p.paths.clone(),
                        };
                        if !verify_path_proof(root, &p.label, path_proof) {
                            let err = anyhow!("verify parent path proof error");
                            bail!("verify commit proofs error: {}", err);
                        }
                        label[(size as usize)..(size + HASH_SIZE) as usize]
                            .copy_from_slice(&p.label);
                        size += HASH_SIZE
                    }

                    let roots_slice: Vec<&[u8]> = p_node.commit_buf.roots
                        [(layer as usize - 1) * IDLE_SET_LEN as usize..layer as usize * IDLE_SET_LEN as usize]
                        .iter()
                        .map(|v| v.as_slice())
                        .collect();
                    copy_data(&mut label[size as usize..], &roots_slice);
                } else {
                    copy_data(&mut label[front_size as usize..], &[&zero]);
                }

                if (chals[i][0] - 1) % IDLE_SET_LEN > 0 {
                    let data = &mut label.clone();
                    let idx =
                        (layer * IDLE_SET_LEN + (chals[i][0] - 1) % IDLE_SET_LEN - 1) as usize;
                    if idx < p_node.commit_buf.roots.len() {
                        data.extend_from_slice(&p_node.commit_buf.roots[idx]);
                    }
                    hash = get_hash(data);
                } else {
                    hash = get_hash(&label);
                }

                if !hash.eq(&proofs[i][j - 1].node.label) {
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

        let mut clusters = vec![0; chals.len()];
        for i in 0..chals.len() {
            clusters[i] = chals[i][0];
        }

        let mut rng = rand::thread_rng();
        for _ in 0..pick {
            let r1 = rng.gen_range(0..proofs.len());
            let r2 = rng.gen_range(0..proofs[r1].len());

            let index = r2;
            let proof = &proofs[r1][index];
            let mut node = expanders::Node::new(proof.node.index);
            let cluster_size;
            {
                let value = CLUSTER_SIZE.lock().unwrap();
                cluster_size = *value;
            }
            if index < cluster_size as usize {
                let mut data = clusters.clone();
                data.push(index as i64 + 1);
                generate_expanders_calc_parents(&self.expanders, &mut node, id, &data);
            } else {
                generate_expanders_calc_parents(&self.expanders, &mut node, id, &clusters);
            }

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
        let cluster_size;
        {
            let value = CLUSTER_SIZE.lock().unwrap();
            cluster_size = *value;
        }
        match self.nodes.get_mut(&id_str) {
            Some(p_node) => {
                if chals.len() != proof.indexs.len() / cluster_size as usize
                    || chals.len() != IDLE_SET_LEN as usize
                {
                    let err = anyhow!("bad proof data");
                    bail!("verify acc proofs error: {}", err);
                }

                let mut label = vec![0u8; id.len() + 8 + HASH_SIZE as usize];

                for i in 0..chals.len() {
                    for j in 0..cluster_size as usize {
                        if proof.indexs[i * cluster_size as usize+j] as usize
                            != (chals[i][0] - 1) as usize * cluster_size as usize + j + 1
                            || p_node.record.as_ref().unwrap().rear as usize
                                + i * cluster_size as usize
                                + j
                                + 1
                                != (chals[i][0] - 1) as usize * cluster_size as usize + j + 1
                        {
                            let err = anyhow!("bad file index");
                            bail!("verify acc proofs error: {}", err);
                        }
                        copy_data(
                            &mut label,
                            &[
                                id,
                                &get_bytes((chals[i][0] - 1) * cluster_size + j as i64 + 1),
                                &p_node.commit_buf.roots
                                    [(self.expanders.k as usize + j) * IDLE_SET_LEN as usize + i],
                            ],
                        );

                        if !get_hash(&label).eq(&proof.labels[i * cluster_size as usize + j]) {
                            let err = anyhow!("verify file label error");
                            bail!("verify acc proofs error: {}", err);
                        }
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

                let mut record = p_node.record.as_mut().unwrap();
                record.acc = proof.acc_path.last().cloned().unwrap();
                p_node.commit_buf = Commits {
                    ..Default::default()
                };

                record.rear += chals.len() as i64 * cluster_size;
            }
            None => {
                let err = anyhow!("prover node not found");
                bail!("verify acc proofs error: {}", err);
            }
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
            .with_context(|| format!("verify deletion proofs error: prover node not found"))?;

        let lens = proof.roots.len();
        let record = p_node.record.as_ref().unwrap();
        if lens > (record.rear - record.front) as usize {
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
                    &get_bytes(record.front + i as i64 + 1),
                    &proof.roots[i],
                ],
            );

            labels.push(get_hash(&label));
        }

        if verify_delete_update(
            record.key.clone(),
            &mut proof.wit_chain,
            labels,
            proof.acc_path.clone(),
            &record.acc,
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
            commit_buf: Default::default(),
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
