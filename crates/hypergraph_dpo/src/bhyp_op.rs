// copying, glueing, subhypergraph extractions
// safety checks 
// and other operations with bHyps
use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::bhyp::{BHyp, BHyp_with_interface, EdgeId, Label, NodeId, SourceWithBinding};
use crate::categorical::{
    pushout, pushout_complement, coproduct, 
    PushoutResult, PushoutComplementError, CoproductResult,
    BHypMorphism,
};


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
// Copying and Glueing (Definition 3.12, 3.15)
// ============================================================================

/// Copy a shared subgraph T at vertex v with out(v) >= 2 (Definition 3.12)
/// Result: Ĝ_T computed as pushout complement
/// 
/// ```text
///     T  <────  (n·T)*
///     ↓    ⌟      ↓
///     G  <────   Ĝ_T
/// ```
/// 

/// Error types for copying operations
#[derive(Debug, Clone)]
pub enum CopyingError {
    InvalidConstruction(String),
}

impl fmt::Display for CopyingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CopyingError::InvalidConstruction(msg) => 
                write!(f, "Invalid construction: {}", msg),
        }
    }
}


pub fn copy_subgraph(
    g: &BHyp_with_interface,
    subgraph_edges: &HashSet<EdgeId>,
    copy_vertex: NodeId,
) -> Result<BHyp_with_interface, CopyingError> {
    let n = g.out_degree(copy_vertex);
    if n < 2 {
        return Err(CopyingError::InvalidConstruction(
            "copy_vertex must have out-degree >= 2".to_string()
        ));
    }
    
    // Extract subgraph T
    let t = extract_subgraph(g.bhyp(), subgraph_edges)?;
    
    // Find output vertex (copy_vertex) in T
    let t_output: HashSet<NodeId> = t.nodes().iter()
        .filter(|&&n| {
            // Check if this node corresponds to copy_vertex
            // (simplified - in practice need proper tracking)
            t.out_degree(n) == 0
        })
        .copied()
        .collect();
    
    // Create (n·T)* - n copies sharing free (output) vertices
    let t_with_iface = BHyp_with_interface::from_bhyp(t.clone());
    let (n_t_star, node_injs, edge_injs) = n_glued_copies_of_t(
        &t_with_iface,
        n,
        &t_output,
    );
    
    // Build inclusion T -> G
    let t_to_g_nodes: HashMap<NodeId, NodeId> = t.nodes().iter()
        .map(|&n| (n, n)) // Assumes T nodes are subset of G nodes
        .collect();
    let t_to_g_edges: HashMap<EdgeId, EdgeId> = t.edges().iter()
        .map(|&e| (e, e))
        .collect();
    
    // Build inclusion (n·T)* -> Ĝ_T (to be computed)
    // First injection of T into (n·T)*
    let t_to_nt_nodes = &node_injs[0];
    let t_to_nt_edges = &edge_injs[0];
    
    // Compute pushout complement: Ĝ_T such that G = pushout(T <- T -> Ĝ_T) ... 
    // Actually for copying we need: Ĝ_T = pushout(G <- T -> (n·T)*)
    
    // Build the identity span on T for the pushout
    let t_id_nodes: HashMap<NodeId, NodeId> = t.nodes().iter().map(|&n| (n, n)).collect();
    let t_id_edges: HashMap<EdgeId, EdgeId> = t.edges().iter().map(|&e| (e, e)).collect();
    
    let result = pushout(
        &t,
        g.bhyp(),
        &n_t_star,
        &t_to_g_nodes,
        &t_to_g_edges,
        t_to_nt_nodes,
        t_to_nt_edges,
    );
    
    Ok(BHyp_with_interface::from_bhyp(result.pushout))
}

/// Extract a subgraph given a set of edges
fn extract_subgraph(g: &BHyp, edges: &HashSet<EdgeId>) -> Result<BHyp, CopyingError> {
    let mut result = BHyp::new();
    let mut node_map: HashMap<NodeId, NodeId> = HashMap::new();
    
    // Collect all nodes referenced by the edges
    let mut nodes: HashSet<NodeId> = HashSet::new();
    for &edge in edges {
        if let Some(sources) = g.get_sources(edge) {
            nodes.extend(sources);
        }
        if let Some(targets) = g.get_targets(edge) {
            nodes.extend(targets.iter().copied());
        }
        if let Some(swbs) = g.get_sources_with_binding(edge) {
            for swb in swbs {
                nodes.extend(swb.bound.iter().copied());
            }
        }
    }
    
    // Create nodes
    for &node in &nodes {
        let new_node = result.add_node();
        node_map.insert(node, new_node);
    }
    
    // Create edges
    for &edge in edges {
        if let (Some(swbs), Some(targets)) = (
            g.get_sources_with_binding(edge),
            g.get_targets(edge),
        ) {
            let new_swbs: Vec<_> = swbs.iter()
                .map(|swb| SourceWithBinding {
                    source: node_map[&swb.source],
                    bound: swb.bound.iter().map(|&b| node_map[&b]).collect(),
                })
                .collect();
            let new_targets: Vec<_> = targets.iter()
                .map(|&t| node_map[&t])
                .collect();
            let label = g.get_label(edge).cloned();
            
            result.add_edge(new_swbs, new_targets, label)
                .map_err(|e| CopyingError::InvalidConstruction(e))?;
        }
    }
    
    Ok(result)
}

/// Glue multiple inclusions of H in G (Definition 3.15)
/// Result: Ĝ = pushout(G <- n·H -> H)
pub fn glue_subgraph(
    g: &BHyp_with_interface,
    h: &BHyp,
    inclusions: &[HashMap<NodeId, NodeId>], // Each: H -> G
) -> Result<BHyp_with_interface, CopyingError> {
    let n = inclusions.len();
    if n < 2 {
        return Ok(g.clone());
    }
    
    // Create n·H (n disjoint copies of H)
    let (n_h, n_h_injs, _) = {
        let mut result = h.clone();
        let mut injs = vec![h.nodes().iter().map(|&n| (n, n)).collect::<HashMap<_, _>>()];
        
        for _ in 1..n {
            let coprod = coproduct(&result, h);
            injs = injs.iter()
                .map(|inj| inj.iter()
                    .map(|(&k, &v)| (k, coprod.first_injection_nodes[&v]))
                    .collect())
                .collect();
            injs.push(h.nodes().iter()
                .map(|&n| (n, coprod.second_injection_nodes[&n]))
                .collect());
            result = coprod.coproduct;
        }
        
        let edge_injs: Vec<HashMap<EdgeId, EdgeId>> = vec![HashMap::new(); n]; // simplified
        (result, injs, edge_injs)
    };
    
    // Build n·H -> G (using the inclusions)
    let mut nh_to_g_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    for (i, (inj, incl)) in n_h_injs.iter().zip(inclusions.iter()).enumerate() {
        for (&h_node, &nh_node) in inj {
            if let Some(&g_node) = incl.get(&h_node) {
                nh_to_g_nodes.insert(nh_node, g_node);
            }
        }
    }
    
    // Build n·H -> H (fold all copies to single H)
    let mut nh_to_h_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    for inj in &n_h_injs {
        for (&h_node, &nh_node) in inj {
            nh_to_h_nodes.insert(nh_node, h_node);
        }
    }
    
    // Compute pushout: Ĝ = G ⊔_{n·H} H
    let result = pushout(
        &n_h,
        g.bhyp(),
        h,
        &nh_to_g_nodes,
        &HashMap::new(), // edges - simplified
        &nh_to_h_nodes,
        &HashMap::new(),
    );
    
    Ok(BHyp_with_interface::from_bhyp(result.pushout))
}
