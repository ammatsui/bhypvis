// Metaedge extraction constructions and substitution for hypergraphs with binding
// copying and glueing shared subhypergraphs (Definition 3.12, 3.15)

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::bhyp::{BHyp, BHyp_with_interface, EdgeId, Label, NodeId, SourceWithBinding};
use crate::categorical::{
    pushout, pushout_complement, coproduct, 
    PushoutResult, PushoutComplementError, CoproductResult,
    BHypMorphism,
};
use crate::bhyp_op::{is_safe};

/// Error types for substitution operations
#[derive(Debug, Clone)]
pub enum SubstitutionError {
    MetavariableNotFound(String),
    ArityMismatch { expected: usize, got: usize },
    InterfaceMismatch(String),
    PushoutComplementFailed(PushoutComplementError),
    InvalidConstruction(String),
}

impl fmt::Display for SubstitutionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SubstitutionError::MetavariableNotFound(name) => 
                write!(f, "Metavariable '{}' not found", name),
            SubstitutionError::ArityMismatch { expected, got } => 
                write!(f, "Arity mismatch: expected {}, got {}", expected, got),
            SubstitutionError::InterfaceMismatch(msg) => 
                write!(f, "Interface mismatch: {}", msg),
            SubstitutionError::PushoutComplementFailed(e) => 
                write!(f, "Pushout complement failed: {}", e),
            SubstitutionError::InvalidConstruction(msg) => 
                write!(f, "Invalid construction: {}", msg),
        }
    }
}

impl From<PushoutComplementError> for SubstitutionError {
    fn from(e: PushoutComplementError) -> Self {
        SubstitutionError::PushoutComplementFailed(e)
    }
}

// ============================================================================
// Construction B.2: Interface of a Metaedge (I_M)
// ============================================================================

/// The interface I_M of a metaedge M is a discrete hypergraph
/// with vertices corresponding to sources and targets of M
#[derive(Debug, Clone)]
pub struct MetaedgeInterface {
    /// The discrete BHyp (no edges, only nodes)
    pub graph: BHyp,
    /// Interface nodes corresponding to source positions
    pub source_nodes: Vec<NodeId>,
    /// Interface nodes corresponding to target positions  
    pub target_nodes: Vec<NodeId>,
}

impl MetaedgeInterface {
    /// Construct I_M from a metaedge's source and target counts
    /// |V_M| = |s(M)| + |t(M)| = k_i + k_o
    pub fn new(num_sources: usize, num_targets: usize) -> Self {
        let mut graph = BHyp::new();
        
        let source_nodes: Vec<NodeId> = (0..num_sources)
            .map(|_| graph.add_node())
            .collect();
        
        let target_nodes: Vec<NodeId> = (0..num_targets)
            .map(|_| graph.add_node())
            .collect();
        
        MetaedgeInterface {
            graph,
            source_nodes,
            target_nodes,
        }
    }
    
    /// Total number of interface nodes
    pub fn size(&self) -> usize {
        self.source_nodes.len() + self.target_nodes.len()
    }
}

// ============================================================================
// Construction B.3: n · (I_M) - n copies of the interface
// ============================================================================

/// Create n disjoint copies of a metaedge interface
/// Returns the coproduct n · I_M and injection maps for each copy
pub fn n_copies_of_interface(
    interface: &MetaedgeInterface,
    n: usize,
) -> (BHyp, Vec<HashMap<NodeId, NodeId>>) {
    if n == 0 {
        return (BHyp::new(), Vec::new());
    }
    
    let mut result = BHyp::new();
    let mut injections = Vec::with_capacity(n);
    
    for _ in 0..n {
        let mut injection = HashMap::new();
        
        // Copy source nodes
        for &src_node in &interface.source_nodes {
            let new_node = result.add_node();
            injection.insert(src_node, new_node);
        }
        
        // Copy target nodes
        for &tgt_node in &interface.target_nodes {
            let new_node = result.add_node();
            injection.insert(tgt_node, new_node);
        }
        
        injections.push(injection);
    }
    
    (result, injections)
}

// ============================================================================
// Construction B.4: n · M - n copies of the metaedge itself
// ============================================================================

/// A single metaedge as a hypergraph: one edge with its interface vertices
#[derive(Debug, Clone)]
pub struct MetaedgeBHyp {
    pub graph: BHyp,
    pub edge: EdgeId,
    pub source_nodes: Vec<NodeId>,
    pub target_nodes: Vec<NodeId>,
    pub name: String,
    pub arity: usize,
}

impl MetaedgeBHyp {
    /// Create a metaedge hypergraph M = ({*}, V_M) with one edge
    pub fn new(name: String, arity: usize, num_targets: usize) -> Self {
        let mut graph = BHyp::new();
        
        let source_nodes: Vec<NodeId> = (0..arity)
            .map(|_| graph.add_node())
            .collect();
        
        let target_nodes: Vec<NodeId> = (0..num_targets)
            .map(|_| graph.add_node())
            .collect();
        
        let sources_with_binding: Vec<SourceWithBinding> = source_nodes.iter()
            .map(|&source| SourceWithBinding { source, bound: vec![] })
            .collect();
        
        let edge = graph.add_edge(
            sources_with_binding,
            target_nodes.clone(),
            Some(Label::Meta(name.clone(), arity)),
        ).expect("Failed to create metaedge");
        
        MetaedgeBHyp {
            graph,
            edge,
            source_nodes,
            target_nodes,
            name,
            arity,
        }
    }
    
    /// Get the interface of this metaedge
    pub fn interface(&self) -> MetaedgeInterface {
        MetaedgeInterface::new(self.source_nodes.len(), self.target_nodes.len())
    }
    
    /// Create the canonical inclusion I_M -> M
    pub fn interface_inclusion(&self) -> (MetaedgeInterface, HashMap<NodeId, NodeId>, HashMap<EdgeId, EdgeId>) {
        let interface = self.interface();
        
        let mut node_map = HashMap::new();
        for (iface_node, &m_node) in interface.source_nodes.iter().zip(&self.source_nodes) {
            node_map.insert(*iface_node, m_node);
        }
        for (iface_node, &m_node) in interface.target_nodes.iter().zip(&self.target_nodes) {
            node_map.insert(*iface_node, m_node);
        }
        
        // No edges in interface
        let edge_map = HashMap::new();
        
        (interface, node_map, edge_map)
    }
}

/// Create n disjoint copies of a metaedge: n · M
pub fn n_copies_of_metaedge(
    meta: &MetaedgeBHyp,
    n: usize,
) -> (BHyp, Vec<HashMap<NodeId, NodeId>>, Vec<HashMap<EdgeId, EdgeId>>) {
    if n == 0 {
        return (BHyp::new(), Vec::new(), Vec::new());
    }
    
    // Use coproduct repeatedly
    let mut result = meta.graph.clone();
    let mut node_injections = vec![meta.graph.nodes().iter().map(|&n| (n, n)).collect()];
    let mut edge_injections = vec![meta.graph.edges().iter().map(|&e| (e, e)).collect()];
    
    for _ in 1..n {
        let coprod = coproduct(&result, &meta.graph);
        
        // Update previous injections to go through first injection
        let updated_node_injs: Vec<HashMap<NodeId, NodeId>> = node_injections.iter()
            .map(|inj: &HashMap<NodeId, NodeId>| {
                inj.iter()
                    .map(|(&k, &v)| (k, coprod.first_injection_nodes[&v]))
                    .collect()
            })
            .collect();
        
        let updated_edge_injs: Vec<HashMap<EdgeId, EdgeId>> = edge_injections.iter()
            .map(|inj: &HashMap<EdgeId, EdgeId>| {
                inj.iter()
                    .map(|(&k, &v)| (k, coprod.first_injection_edges[&v]))
                    .collect()
            })
            .collect();
        
        node_injections = updated_node_injs;
        edge_injections = updated_edge_injs;
        
        // Add new injection for this copy
        let new_node_inj: HashMap<NodeId, NodeId> = meta.graph.nodes().iter()
            .map(|&n| (n, coprod.second_injection_nodes[&n]))
            .collect();
        let new_edge_inj: HashMap<EdgeId, EdgeId> = meta.graph.edges().iter()
            .map(|&e| (e, coprod.second_injection_edges[&e]))
            .collect();
        
        node_injections.push(new_node_inj);
        edge_injections.push(new_edge_inj);
        
        result = coprod.coproduct;
    }
    
    (result, node_injections, edge_injections)
}

// ============================================================================
// Construction: n·̂T - n copies of T glued along free vertices
// ============================================================================

/// Free vertices of T are those in I_T + O_T not in the image of f: I_M -> I_T + O_T
#[derive(Debug, Clone)]
pub struct FreeVertices {
    pub vertices: HashSet<NodeId>,
}

/// Create n copies of T, glued along free vertices (n·̂T from Definition 3.10)
/// 
/// This is computed as: pushout of (F_T <- F_T × n -> n · T)
/// where F_T is the set of free vertices
pub fn n_glued_copies_of_t(
    t: &BHyp_with_interface,
    n: usize,
    free_vertices: &HashSet<NodeId>,
) -> (BHyp, Vec<HashMap<NodeId, NodeId>>, Vec<HashMap<EdgeId, EdgeId>>) {
    if n == 0 {
        return (BHyp::new(), Vec::new(), Vec::new());
    }
    
    if n == 1 {
        let node_map: HashMap<_, _> = t.nodes().iter().map(|&n| (n, n)).collect();
        let edge_map: HashMap<_, _> = t.edges().iter().map(|&e| (e, e)).collect();
        return (t.bhyp().clone(), vec![node_map], vec![edge_map]);
    }
    
    // First create n disjoint copies using coproduct
    let (n_copies, mut node_injs, mut edge_injs) = {
        let mut result = t.bhyp().clone();
        let mut n_injs = vec![t.nodes().iter().map(|&n| (n, n)).collect::<HashMap<_, _>>()];
        let mut e_injs = vec![t.edges().iter().map(|&e| (e, e)).collect::<HashMap<_, _>>()];
        
        for _ in 1..n {
            let coprod = coproduct(&result, t.bhyp());
            
            // Update previous injections
            n_injs = n_injs.iter()
                .map(|inj| inj.iter()
                    .map(|(&k, &v)| (k, coprod.first_injection_nodes[&v]))
                    .collect())
                .collect();
            e_injs = e_injs.iter()
                .map(|inj| inj.iter()
                    .map(|(&k, &v)| (k, coprod.first_injection_edges[&v]))
                    .collect())
                .collect();
            
            // Add new copy's injection
            n_injs.push(t.nodes().iter()
                .map(|&n| (n, coprod.second_injection_nodes[&n]))
                .collect());
            e_injs.push(t.edges().iter()
                .map(|&e| (e, coprod.second_injection_edges[&e]))
                .collect());
            
            result = coprod.coproduct;
        }
        
        (result, n_injs, e_injs)
    };
    
    // Now glue along free vertices using pushout
    // We identify free vertices across all copies
    // This is: pushout(n·T <- n·F_T -> F_T)
    
    if free_vertices.is_empty() {
        return (n_copies, node_injs, edge_injs);
    }
    
    // Build the span for glueing:
    // - Left: n·T (the n disjoint copies)
    // - Middle: n·F_T (n copies of free vertices, discrete)
    // - Right: F_T (single copy of free vertices, discrete)
    
    // Create n·F_T (discrete graph)
    let mut n_free = BHyp::new();
    let mut n_free_to_n_copies: HashMap<NodeId, NodeId> = HashMap::new();
    
    for (copy_idx, node_inj) in node_injs.iter().enumerate() {
        for &free_v in free_vertices {
            let nf_node = n_free.add_node();
            // Maps to the corresponding node in n·T
            if let Some(&copies_node) = node_inj.get(&free_v) {
                n_free_to_n_copies.insert(nf_node, copies_node);
            }
        }
    }
    
    // Create F_T (single copy, discrete)
    let mut f_t = BHyp::new();
    let mut f_t_nodes: HashMap<NodeId, NodeId> = HashMap::new(); // original -> f_t node
    for &free_v in free_vertices {
        let ft_node = f_t.add_node();
        f_t_nodes.insert(free_v, ft_node);
    }
    
    // n·F_T -> F_T maps each copy's free vertex to the single copy
    let mut n_free_to_f_t: HashMap<NodeId, NodeId> = HashMap::new();
    let mut idx = 0;
    for _ in 0..n {
        for &free_v in free_vertices {
            let nf_node = NodeId(idx);
            if let Some(&ft_node) = f_t_nodes.get(&free_v) {
                n_free_to_f_t.insert(nf_node, ft_node);
            }
            idx += 1;
        }
    }
    
    // Compute pushout: n·T ⊔_{n·F_T} F_T
    let pushout_result = pushout(
        &n_free,
        &n_copies,
        &f_t,
        &n_free_to_n_copies,
        &HashMap::new(), // no edges in n_free
        &n_free_to_f_t,
        &HashMap::new(), // no edges in n_free
    );
    
    // Update injections to go through the pushout
    let final_node_injs: Vec<HashMap<NodeId, NodeId>> = node_injs.iter()
        .map(|inj| {
            inj.iter()
                .map(|(&orig, &copies_node)| {
                    let final_node = pushout_result.first_to_pushout_nodes
                        .get(&copies_node)
                        .copied()
                        .unwrap_or(copies_node);
                    (orig, final_node)
                })
                .collect()
        })
        .collect();
    
    let final_edge_injs: Vec<HashMap<EdgeId, EdgeId>> = edge_injs.iter()
        .map(|inj| {
            inj.iter()
                .map(|(&orig, &copies_edge)| {
                    let final_edge = pushout_result.first_to_pushout_edges
                        .get(&copies_edge)
                        .copied()
                        .unwrap_or(copies_edge);
                    (orig, final_edge)
                })
                .collect()
        })
        .collect();
    
    (pushout_result.pushout, final_node_injs, final_edge_injs)
}

// ============================================================================
// Substitution Data (Definition 3.10)
// ============================================================================

/// A substitution θ: M ↦ T
/// Given by map f: I_M -> I_T + O_T and span I_G <- K -> I_{F_T}
#[derive(Debug, Clone)]
pub struct Substitution {
    /// Metavariable name
    pub meta_name: String,
    /// Replacement hypergraph T with interface
    pub replacement: BHyp_with_interface,
    /// Map f: I_M -> I_T + O_T (source index -> replacement interface node)
    pub interface_map: HashMap<usize, NodeId>,
}

impl Substitution {
    pub fn new(meta_name: String, replacement: BHyp_with_interface) -> Self {
        Substitution {
            meta_name,
            replacement,
            interface_map: HashMap::new(),
        }
    }
    
    /// Set interface mapping (which T nodes correspond to M's sources/targets)
    pub fn with_interface_map(mut self, map: HashMap<usize, NodeId>) -> Self {
        self.interface_map = map;
        self
    }
    
    /// Compute free vertices: F_T = (I_T + O_T) \ Im(f)
    pub fn free_vertices(&self) -> HashSet<NodeId> {
        let mapped: HashSet<NodeId> = self.interface_map.values().copied().collect();
        let all_interface: HashSet<NodeId> = self.replacement.input_interface_nodes()
            .union(&self.replacement.output_interface_nodes())
            .copied()
            .collect();
        
        all_interface.difference(&mapped).copied().collect()
    }
}

/// Shared variables K (discrete hypergraph)
#[derive(Debug, Clone)]
pub struct SharedVariables {
    pub graph: BHyp,
    /// K -> I_G
    pub to_host_input: HashMap<NodeId, NodeId>,
    /// K -> I_{F_T}  
    pub to_replacement_free: HashMap<NodeId, NodeId>,
}

impl SharedVariables {
    pub fn empty() -> Self {
        SharedVariables {
            graph: BHyp::new(),
            to_host_input: HashMap::new(),
            to_replacement_free: HashMap::new(),
        }
    }
    
    pub fn add(&mut self, host_node: NodeId, repl_node: NodeId) -> NodeId {
        let k_node = self.graph.add_node();
        self.to_host_input.insert(k_node, host_node);
        self.to_replacement_free.insert(k_node, repl_node);
        k_node
    }
}

// ============================================================================
// Main Substitution Algorithm (Definition 3.10)
// ============================================================================

/// Result of substitution
#[derive(Debug)]
pub struct SubstitutionResult {
    pub result: BHyp_with_interface,
    pub host_to_result: HashMap<NodeId, NodeId>,
    pub replacement_to_result: Vec<HashMap<NodeId, NodeId>>,
}

/// Apply substitution θ: M ↦ T to hypergraph G
/// 
/// Constructed via DPO in bHyp:
/// ```text
///     n·M ⊔ K  <──  n·(I_M) ⊔ K  ──>  n·̂T
///        ↓              ↓               ↓
///        G   <─────    C    ─────>   G[M/T]
/// ```
/// 
/// Where:
/// - n = multiplicity of M in G
/// - K = shared variables
/// - n·̂T = n copies of T glued along free vertices
pub fn apply_substitution(
    g: &BHyp_with_interface,
    subst: &Substitution,
    shared: &SharedVariables,
) -> Result<SubstitutionResult, SubstitutionError> {
    
    // Step 1: Find all instances of metavariable M in G
    let instances = find_metavariable_instances(g.bhyp(), &subst.meta_name);
    let n = instances.len();
    
    if n == 0 {
        return Err(SubstitutionError::MetavariableNotFound(subst.meta_name.clone()));
    }
    
    
    // Step 2: Construct n·M ⊔ K (left side of span)
    let meta_template = MetaedgeBHyp::new(
        subst.meta_name.clone(),
        instances[0].arity,
        instances[0].targets.len(),
    );
    
    let (n_m, n_m_node_injs, n_m_edge_injs) = n_copies_of_metaedge(&meta_template, n);
    
    // Coproduct with K
    let n_m_coprod_k = if shared.graph.nodes().is_empty() {
        (n_m.clone(), 
         n_m.nodes().iter().map(|&n| (n, n)).collect(),
         n_m.edges().iter().map(|&e| (e, e)).collect(),
         HashMap::new(),
         HashMap::new())
    } else {
        let coprod = coproduct(&n_m, &shared.graph);
        (coprod.coproduct,
         coprod.first_injection_nodes,
         coprod.first_injection_edges,
         coprod.second_injection_nodes,
         coprod.second_injection_edges)
    };
    let (l_graph, l_nm_nodes, l_nm_edges, l_k_nodes, _l_k_edges) = n_m_coprod_k;
    
    // Step 3: Construct n·(I_M) ⊔ K (middle of span)
    let (n_i_m, n_i_m_injs) = n_copies_of_interface(&meta_template.interface(), n);
    
    let k_graph = if shared.graph.nodes().is_empty() {
        (n_i_m.clone(),
         n_i_m.nodes().iter().map(|&n| (n, n)).collect::<HashMap<_, _>>(),
         HashMap::new())
    } else {
        let coprod = coproduct(&n_i_m, &shared.graph);
        (coprod.coproduct,
         coprod.first_injection_nodes,
         coprod.second_injection_nodes)
    };
    let (k_total, k_nim_nodes, k_shared_nodes) = k_graph;
    
    // Step 4: Construct n·̂T (right side of span)
    let free_vertices = subst.free_vertices();
    let (n_hat_t, n_hat_t_node_injs, n_hat_t_edge_injs) = n_glued_copies_of_t(
        &subst.replacement,
        n,
        &free_vertices,
    );
    
    // Step 5: Build morphism L <- K (n·M ⊔ K <- n·(I_M) ⊔ K)
    // The interface I_M embeds into M
    let (iface, iface_to_m_nodes, _) = meta_template.interface_inclusion();
    
    let mut l_from_k_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    let mut l_from_k_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
    
    // Map n·(I_M) part
    for (copy_idx, nim_inj) in n_i_m_injs.iter().enumerate() {
        for (&iface_node, &nim_node) in nim_inj {
            // iface_node in I_M -> nim_node in n·(I_M)
            // Need to map to corresponding node in n·M
            if let Some(&m_node) = iface_to_m_nodes.get(&iface_node) {
                if let Some(&nm_node) = n_m_node_injs[copy_idx].get(&m_node) {
                    if let Some(&l_node) = l_nm_nodes.get(&nm_node) {
                        if let Some(&k_node) = k_nim_nodes.get(&nim_node) {
                            l_from_k_nodes.insert(k_node, l_node);
                        }
                    }
                }
            }
        }
    }
    
    // Map K (shared) part - identity on K nodes
    for (&k_orig, &k_in_total) in &k_shared_nodes {
        if let Some(&l_node) = l_k_nodes.get(&k_orig) {
            l_from_k_nodes.insert(k_in_total, l_node);
        }
    }
    
    // Step 6: Build morphism K -> R (n·(I_M) ⊔ K -> n·̂T)
    let mut r_from_k_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    let mut r_from_k_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
    
    // Map n·(I_M) to n·̂T via the interface map f: I_M -> I_T + O_T
    for (copy_idx, nim_inj) in n_i_m_injs.iter().enumerate() {
        for (src_idx, &iface_node) in iface.source_nodes.iter().enumerate() {
            if let Some(&nim_node) = nim_inj.get(&iface_node) {
                if let Some(&t_node) = subst.interface_map.get(&src_idx) {
                    if let Some(&nht_node) = n_hat_t_node_injs.get(copy_idx)
                        .and_then(|inj| inj.get(&t_node)) 
                    {
                        if let Some(&k_node) = k_nim_nodes.get(&nim_node) {
                            r_from_k_nodes.insert(k_node, nht_node);
                        }
                    }
                }
            }
        }
    }
    
    // Map K (shared) to free vertices in n·̂T
    for (&k_orig, &k_in_total) in &k_shared_nodes {
        if let Some(&repl_node) = shared.to_replacement_free.get(&k_orig) {
            // Find this node in n·̂T (it's shared across copies)
            if let Some(&nht_node) = n_hat_t_node_injs.get(0)
                .and_then(|inj| inj.get(&repl_node))
            {
                r_from_k_nodes.insert(k_in_total, nht_node);
            }
        }
    }
    
    // Step 7: Build matching morphism L -> G (n·M ⊔ K -> G)
    let mut match_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    let mut match_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
    
    // Map n·M part
    for (copy_idx, (node_inj, edge_inj)) in n_m_node_injs.iter()
        .zip(n_m_edge_injs.iter())
        .enumerate() 
    {
        let inst = &instances[copy_idx];
        
        // Map source nodes
        for (src_idx, &m_src) in meta_template.source_nodes.iter().enumerate() {
            if let Some(&nm_node) = node_inj.get(&m_src) {
                if let Some(&l_node) = l_nm_nodes.get(&nm_node) {
                    match_nodes.insert(l_node, inst.sources[src_idx]);
                }
            }
        }
        
        // Map target nodes
        for (tgt_idx, &m_tgt) in meta_template.target_nodes.iter().enumerate() {
            if let Some(&nm_node) = node_inj.get(&m_tgt) {
                if let Some(&l_node) = l_nm_nodes.get(&nm_node) {
                    match_nodes.insert(l_node, inst.targets[tgt_idx]);
                }
            }
        }
        
        // Map the metaedge
        if let Some(&nm_edge) = edge_inj.get(&meta_template.edge) {
            if let Some(&l_edge) = l_nm_edges.get(&nm_edge) {
                match_edges.insert(l_edge, inst.edge_id);
            }
        }
    }
    
    // Map K (shared) to G
    for (&k_orig, &k_in_l) in &l_k_nodes {
        if let Some(&g_node) = shared.to_host_input.get(&k_orig) {
            match_nodes.insert(k_in_l, g_node);
        }
    }
    
    // Step 8: Compute pushout complement C = PC(G <- L <- K)
    let pc_result = pushout_complement(
        &k_total,
        &l_graph,
        g.bhyp(),
        &l_from_k_nodes,
        &l_from_k_edges,
        &match_nodes,
        &match_edges,
    )?;
    
    // Step 9: Compute pushout G[M/T] = PO(C <- K -> n·̂T)
    let final_pushout = pushout(
        &k_total,
        &pc_result.complement,
        &n_hat_t,
        &pc_result.interface_to_complement_nodes,
        &pc_result.interface_to_complement_edges,
        &r_from_k_nodes,
        &r_from_k_edges,
    );
    
    // Step 10: Build result mappings
    let mut host_to_result: HashMap<NodeId, NodeId> = HashMap::new();
    
    // Nodes from G that survived to C, then to result
    for (&c_node, &g_node) in &pc_result.complement_to_original_nodes {
        if let Some(&result_node) = final_pushout.first_to_pushout_nodes.get(&c_node) {
            host_to_result.insert(g_node, result_node);
        }
    }
    
    // Nodes from replacement
    let replacement_to_result: Vec<HashMap<NodeId, NodeId>> = n_hat_t_node_injs.iter()
        .map(|inj| {
            inj.iter()
                .filter_map(|(&t_node, &nht_node)| {
                    final_pushout.second_to_pushout_nodes.get(&nht_node)
                        .map(|&r_node| (t_node, r_node))
                })
                .collect()
        })
        .collect();
    
    Ok(SubstitutionResult {
        result: BHyp_with_interface::from_bhyp(final_pushout.pushout),
        host_to_result,
        replacement_to_result,
    })
}

// ============================================================================
// Helper: Find metavariable instances
// ============================================================================

#[derive(Debug, Clone)]
pub struct MetaedgeInstance {
    pub edge_id: EdgeId,
    pub name: String,
    pub arity: usize,
    pub sources: Vec<NodeId>,
    pub targets: Vec<NodeId>,
}

pub fn find_metavariable_instances(bhyp: &BHyp, meta_name: &str) -> Vec<MetaedgeInstance> {
    let mut instances = Vec::new();
    
    for &edge_id in bhyp.edges() {
        if let Some(Label::Meta(name, arity)) = bhyp.get_label(edge_id) {
            if name == meta_name {
                let sources = bhyp.get_sources(edge_id).unwrap_or_default();
                let targets = bhyp.get_targets(edge_id).cloned().unwrap_or_default();
                
                instances.push(MetaedgeInstance {
                    edge_id,
                    name: name.clone(),
                    arity: *arity,
                    sources,
                    targets,
                });
            }
        }
    }
    
    instances
}

pub fn extract_all_metaedges(bhyp: &BHyp) -> Vec<MetaedgeInstance> {
    let mut instances = Vec::new();
    
    for &edge_id in bhyp.edges() {
        if let Some(Label::Meta(name, arity)) = bhyp.get_label(edge_id) {
            let sources = bhyp.get_sources(edge_id).unwrap_or_default();
            let targets = bhyp.get_targets(edge_id).cloned().unwrap_or_default();
            
            instances.push(MetaedgeInstance {
                edge_id,
                name: name.clone(),
                arity: *arity,
                sources,
                targets,
            });
        }
    }
    
    instances
}


// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_metaedge_interface() {
        let iface = MetaedgeInterface::new(2, 1);
        assert_eq!(iface.source_nodes.len(), 2);
        assert_eq!(iface.target_nodes.len(), 1);
        assert_eq!(iface.size(), 3);
        assert!(iface.graph.is_discrete());
    }

    #[test]
    fn test_n_copies_of_interface() {
        let iface = MetaedgeInterface::new(2, 1);
        let (copies, injections) = n_copies_of_interface(&iface, 3);
        
        assert_eq!(copies.nodes().len(), 9); // 3 * 3 nodes
        assert_eq!(injections.len(), 3);
        assert!(copies.is_discrete());
    }

    #[test]
    fn test_metaedge_bhyp() {
        let meta = MetaedgeBHyp::new("M".to_string(), 2, 1);
        
        assert_eq!(meta.source_nodes.len(), 2);
        assert_eq!(meta.target_nodes.len(), 1);
        assert_eq!(meta.graph.edges().len(), 1);
        
        let (iface, node_map, _) = meta.interface_inclusion();
        assert_eq!(iface.size(), 3);
        assert_eq!(node_map.len(), 3);
    }

    #[test]
    fn test_n_copies_of_metaedge() {
        let meta = MetaedgeBHyp::new("M".to_string(), 1, 1);
        let (copies, node_injs, edge_injs) = n_copies_of_metaedge(&meta, 2);
        
        assert_eq!(copies.nodes().len(), 4); // 2 * 2 nodes
        assert_eq!(copies.edges().len(), 2); // 2 edges
        assert_eq!(node_injs.len(), 2);
        assert_eq!(edge_injs.len(), 2);
    }

    #[test]
    fn test_find_metavariable_instances() {
        let mut g = BHyp::new();
        let n1 = g.add_node();
        let n2 = g.add_node();
        let n3 = g.add_node();
        let n4 = g.add_node();
        
        g.add_edge(
            vec![SourceWithBinding { source: n1, bound: vec![] }],
            vec![n2],
            Some(Label::Meta("M".to_string(), 1)),
        ).unwrap();
        
        g.add_edge(
            vec![SourceWithBinding { source: n3, bound: vec![] }],
            vec![n4],
            Some(Label::Meta("M".to_string(), 1)),
        ).unwrap();
        
        let instances = find_metavariable_instances(&g, "M");
        assert_eq!(instances.len(), 2);
    }

    #[test]
    fn test_substitution_free_vertices() {
        let mut t = BHyp::new();
        let t_in1 = t.add_node();
        let t_in2 = t.add_node();
        let t_out = t.add_node();
        t.add_edge(
            vec![
                SourceWithBinding { source: t_in1, bound: vec![] },
                SourceWithBinding { source: t_in2, bound: vec![] },
            ],
            vec![t_out],
            Some(Label::Symbol("f".to_string())),
        ).unwrap();
        
        let t_iface = BHyp_with_interface::from_bhyp(t);
        
        // Map only source index 0 to t_in1
        let mut interface_map = HashMap::new();
        interface_map.insert(0, t_in1);
        
        let subst = Substitution::new("M".to_string(), t_iface)
            .with_interface_map(interface_map);
        
        let free = subst.free_vertices();
        // t_in2 and t_out should be free (not mapped from M's interface)
        assert!(free.contains(&t_in2) || free.contains(&t_out));
    }

    #[test]
    fn test_safety_simple() {
        let mut g = BHyp::new();
        let n1 = g.add_node();
        let n2 = g.add_node();
        g.add_edge(
            vec![SourceWithBinding { source: n1, bound: vec![] }],
            vec![n2],
            Some(Label::Symbol("f".to_string())),
        ).unwrap();
        
        let gi = BHyp_with_interface::from_bhyp(g);
        assert!(is_safe(&gi));
    }

    #[test]
    fn test_safety_with_binding() {
        let mut g = BHyp::new();
        let x = g.add_node();
        let body = g.add_node();
        let out = g.add_node();
        
        g.add_edge(
            vec![SourceWithBinding { source: body, bound: vec![x] }],
            vec![out],
            Some(Label::Symbol("λ".to_string())),
        ).unwrap();
        
        let gi = BHyp_with_interface::from_bhyp(g);
        assert!(is_safe(&gi));
    }

    #[test]
    fn test_safety_double_bound_fails() {
        let mut g = BHyp::new();
        let x = g.add_node();
        let b1 = g.add_node();
        let b2 = g.add_node();
        let o1 = g.add_node();
        let o2 = g.add_node();
        
        g.add_edge(
            vec![SourceWithBinding { source: b1, bound: vec![x] }],
            vec![o1],
            Some(Label::Symbol("λ".to_string())),
        ).unwrap();
        
        g.add_edge(
            vec![SourceWithBinding { source: b2, bound: vec![x] }],
            vec![o2],
            Some(Label::Symbol("λ".to_string())),
        ).unwrap();
        
        let gi = BHyp_with_interface::from_bhyp(g);
        assert!(!is_safe(&gi));
    }

    #[test]
    fn test_safety_bound_as_target_fails() {
        let mut g = BHyp::new();
        let x = g.add_node();
        let body = g.add_node();
        let out = g.add_node();
        let src = g.add_node();
        
        g.add_edge(
            vec![SourceWithBinding { source: body, bound: vec![x] }],
            vec![out],
            Some(Label::Symbol("λ".to_string())),
        ).unwrap();
        
        g.add_edge(
            vec![SourceWithBinding { source: src, bound: vec![] }],
            vec![x], // x is target but also bound
            Some(Label::Symbol("f".to_string())),
        ).unwrap();
        
        let gi = BHyp_with_interface::from_bhyp(g);
        assert!(!is_safe(&gi));
    }
}