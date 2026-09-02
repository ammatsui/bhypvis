// // copying, glueing, etc

// //- Copying: duplicates a shared sub-hypergraph
// // - Glueing: merges multiple inclusions of a sub-hypergraph (inverse of copying)

use std::collections::{HashMap, HashSet};

use crate::bhyp::{BHyp, BHyp_with_interface, EdgeId, Label, NodeId, SourceWithBinding};
use crate::categorical::{
    BHypMorphism, CategoricalError, MorphismError, PushoutResult, Span, 
    compute_coproduct, compute_pullback, compute_pushout, compute_pushout_complement, identity_morphism,
};

/// Errors specific to copying and glueing operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CopyError {
    /// The node is not in the output interface of the sub-hypergraph
    NodeNotInOutput(NodeId),
    /// The sub-hypergraph is not valid
    InvalidSubhypergraph(String),
    /// Categorical construction failed
    CategoricalError(CategoricalError),
    /// Morphism error
    MorphismError(MorphismError),
}

/// Errors specific to copying and glueing operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GlueError {
    /// The sub-hypergraph is not valid
    InvalidSubhypergraph(String),
    /// Categorical construction failed
    CategoricalError(CategoricalError),
    /// Morphism error
    MorphismError(MorphismError),
    /// Inclusions are not compatible
    IncompatibleInclusions(String),
}

impl From<CategoricalError> for CopyError {
    fn from(e: CategoricalError) -> Self {
        CopyError::CategoricalError(e)
    }
}

impl From<CategoricalError> for GlueError {
    fn from(e: CategoricalError) -> Self {
        GlueError::CategoricalError(e)
    }
}

impl From<MorphismError> for CopyError {
    fn from(e: MorphismError) -> Self {
        CopyError::MorphismError(e)
    }
}

impl From<MorphismError> for GlueError {
    fn from(e: MorphismError) -> Self {
        GlueError::MorphismError(e)
    }
}

impl std::fmt::Display for CopyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CopyError::NodeNotInOutput(n) => {
                write!(f, "Node {:?} not in output interface of sub-hypergraph", n)
            }
            CopyError::InvalidSubhypergraph(s) => {
                write!(f, "Invalid sub-hypergraph: {}", s)
            }
            CopyError::CategoricalError(e) => write!(f, "Categorical error: {}", e),
            CopyError::MorphismError(e) => write!(f, "Morphism error: {}", e),
        }
    }
}


impl std::fmt::Display for GlueError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
           
            GlueError::InvalidSubhypergraph(s) => {
                write!(f, "Invalid sub-hypergraph: {}", s)
            }

            GlueError::CategoricalError(e) => write!(f, "Categorical error: {}", e),
            GlueError::MorphismError(e) => write!(f, "Morphism error: {}", e),
            
            GlueError::IncompatibleInclusions(s) => {
                write!(f, "Incompatible inclusions: {}", s)
            }
        }
    }
}

/// Result of a copying operation
/// result of the specific pushout complement with projections
#[derive(Debug, Clone)]
pub struct CopyResult {
    /// The resulting hypergraph with copied sub-hypergraph
    pub result: BHyp,
    /// morphism onto the original bhyp
    pub morphism: BHypMorphism,
    /// The number of copies created
    pub num_copies: usize,
}

/// Result of a glueing operation  
/// result of the specific pushout with projections
#[derive(Debug, Clone)]
pub struct GlueResult {
    /// The resulting hypergraph with glued sub-hypergraph
    pub result: BHyp,
    /// Morphism from the original onto the glued
    pub morphism: BHypMorphism,
}


//// i think that could be moved to categorical.rs

/// Finds all monomorphic inclusions (occurrences) of pattern H in target G.
pub fn find_all_ccurrences(pattern: &BHyp, target: &BHyp) -> Vec<BHypMorphism> {
    let mut results = Vec::new();
    let pattern_edges: Vec<EdgeId> = pattern.edges().iter().copied().collect();
    
    let mut node_map = HashMap::new();
    let mut edge_map = HashMap::new();
    
    backtrack_match(
        0,
        &pattern_edges,
        pattern,
        target,
        &mut node_map,
        &mut edge_map,
        &mut results,
    );
    
    results
}

fn backtrack_match(
    edge_idx: usize,
    pattern_edges: &[EdgeId],
    pattern: &BHyp,
    target: &BHyp,
    current_node_map: &mut HashMap<NodeId, NodeId>,
    current_edge_map: &mut HashMap<EdgeId, EdgeId>,
    results: &mut Vec<BHypMorphism>,
) {
    // Base Case: All edges matched
    if edge_idx == pattern_edges.len() {
        // (Assuming no isolated nodes in H. If H has isolated nodes, you'd 
        // need a secondary loop here to map remaining unmapped nodes in pattern.nodes())
        if let Ok(m) = BHypMorphism::new(
            pattern.clone(), 
            target.clone(), 
            current_node_map.clone(), 
            current_edge_map.clone()
        ) {
            results.push(m);
        }
        return;
    }

    let p_edge = pattern_edges[edge_idx];
    
    for &t_edge in target.edges() {
        // 1. Check Label
        if pattern.get_label(p_edge) != target.get_label(t_edge) { continue; }
        
        // 2. Prevent mapping multiple pattern edges to the same target edge
        if current_edge_map.values().any(|&e| e == t_edge) { continue; }
        
        let p_sources = pattern.get_sources_with_binding(p_edge).unwrap();
        let p_targets = pattern.get_targets(p_edge).unwrap();
        
        let t_sources = target.get_sources_with_binding(t_edge).unwrap();
        let t_targets = target.get_targets(t_edge).unwrap();
        
        // 3. Arity and Co-arity must match
        if p_sources.len() != t_sources.len() || p_targets.len() != t_targets.len() { continue; }
        
        let mut local_node_additions = Vec::new();
        let mut valid = true;
        
        // Helper to enforce injectivity while mapping nodes
        let mut try_map_node = |p_n: NodeId, t_n: NodeId| -> bool {
            if let Some(&existing) = current_node_map.get(&p_n) {
                existing == t_n // Must agree with previous mappings
            } else {
                // Must be injective: target node can't already be mapped to a different pattern node
                if current_node_map.values().any(|&n| n == t_n) {
                    return false;
                }
                current_node_map.insert(p_n, t_n);
                local_node_additions.push(p_n);
                true
            }
        };
        
        // 4. Map Targets
        for (i, &p_n) in p_targets.iter().enumerate() {
            if !try_map_node(p_n, t_targets[i]) { valid = false; break; }
        }
        
        // 5. Map Sources and Bindings
        if valid {
            for (i, p_swb) in p_sources.iter().enumerate() {
                let t_swb = &t_sources[i];
                if p_swb.bound.len() != t_swb.bound.len() { valid = false; break; }
                
                if !try_map_node(p_swb.source, t_swb.source) { valid = false; break; }
                
                for (j, &p_b) in p_swb.bound.iter().enumerate() {
                    if !try_map_node(p_b, t_swb.bound[j]) { valid = false; break; }
                }
                if !valid { break; }
            }
        }
        
        // 6. Recurse if valid
        if valid {
            current_edge_map.insert(p_edge, t_edge);
            backtrack_match(edge_idx + 1, pattern_edges, pattern, target, current_node_map, current_edge_map, results);
            current_edge_map.remove(&p_edge);
        }
        
        // 7. Backtrack (undo local mappings)
        for p_n in local_node_additions {
            current_node_map.remove(&p_n);
        }
    }
}


/// Check if T is a subhypergraph of G, and if so return the inclusion morphism
pub fn find_subhypergraph_inclusion(t: &BHyp, g: &BHyp) -> Option<BHypMorphism> {
    // T can only be a subhypergraph if it has at most as many nodes and edges as G
    if t.nodes().len() > g.nodes().len() || t.edges().len() > g.edges().len() {
        return None;
    }

    let t_nodes: Vec<NodeId> = t.nodes().iter().copied().collect();
    let g_nodes: Vec<NodeId> = g.nodes().iter().copied().collect();

    // Empty T is always a subhypergraph of G
    if t_nodes.is_empty() && t.edges().is_empty() {
        return Some(BHypMorphism::new(
            t.clone(), g.clone(), HashMap::new(), HashMap::new()
        ).unwrap());
    }

    // For small graphs, try all possible injective mappings from T to G
    fn try_inclusion(
        t: &BHyp,
        g: &BHyp,
        t_nodes: &[NodeId],
        g_nodes: &[NodeId],
        node_map: &mut HashMap<NodeId, NodeId>,
        idx: usize,
        used: &mut HashSet<NodeId>,
    ) -> Option<HashMap<EdgeId, EdgeId>> {
        if idx == t_nodes.len() {
            // Check if this node mapping induces a valid edge inclusion
            let mut edge_map: HashMap<EdgeId, EdgeId> = HashMap::new();

            for &e_t in t.edges() {
                let mut found = false;
                for &e_g in g.edges() {
                    if edge_map.values().any(|&e| e == e_g) {
                        continue;
                    }

                    // Check compatibility
                    let swbs_t = t.get_sources_with_binding(e_t).unwrap();
                    let swbs_g = g.get_sources_with_binding(e_g).unwrap();
                    let targets_t = t.get_targets(e_t).unwrap();
                    let targets_g = g.get_targets(e_g).unwrap();

                    if swbs_t.len() != swbs_g.len() || targets_t.len() != targets_g.len() {
                        continue;
                    }

                    let mut compatible = true;

                    // Check sources and bindings
                    for (s_t, s_g) in swbs_t.iter().zip(swbs_g.iter()) {
                        if node_map[&s_t.source] != s_g.source {
                            compatible = false;
                            break;
                        }
                        if s_t.bound.len() != s_g.bound.len() {
                            compatible = false;
                            break;
                        }
                        for (b_t, b_g) in s_t.bound.iter().zip(s_g.bound.iter()) {
                            if node_map[b_t] != *b_g {
                                compatible = false;
                                break;
                            }
                        }
                        if !compatible {
                            break;
                        }
                    }

                    if !compatible {
                        continue;
                    }

                    // Check targets
                    for (t_t, t_g) in targets_t.iter().zip(targets_g.iter()) {
                        if node_map[t_t] != *t_g {
                            compatible = false;
                            break;
                        }
                    }

                    if !compatible {
                        continue;
                    }

                    // Check labels
                    if t.get_label(e_t) != g.get_label(e_g) {
                        continue;
                    }

                    edge_map.insert(e_t, e_g);
                    found = true;
                    break;
                }

                if !found {
                    return None;
                }
            }

            return Some(edge_map);
        }

        let n_t = t_nodes[idx];
        for &n_g in g_nodes {
            if used.contains(&n_g) {
                continue;
            }

            node_map.insert(n_t, n_g);
            used.insert(n_g);

            if let Some(edge_map) = try_inclusion(t, g, t_nodes, g_nodes, node_map, idx + 1, used) {
                return Some(edge_map);
            }

            node_map.remove(&n_t);
            used.remove(&n_g);
        }

        None
    }

    let mut node_map = HashMap::new();
    let mut used = HashSet::new();

    if let Some(edge_map) = try_inclusion(t, g, &t_nodes, &g_nodes, &mut node_map, 0, &mut used) {
        Some(BHypMorphism::new(
            t.clone(), g.clone(), node_map, edge_map
        ).unwrap())
    } else {
        None
    }
}

/// Check if T is a subhypergraph of G (without returning the morphism)
pub fn is_subhypergraph(t: &BHyp, g: &BHyp) -> bool {
    find_subhypergraph_inclusion(t, g).is_some()
}





// hypergraph inclusion 
pub fn build_inclusion(t: &BHyp, g: &BHyp) -> Result<BHypMorphism, MorphismError> {
    if is_subhypergraph(&t, &g) {
        
        let option = find_subhypergraph_inclusion(&t, &g);

// Converts Some(bhyp) -> Ok(bhyp)
// Converts None -> Err(CopyError::InvalidSubhypergraph(...))
    let result = option.ok_or(
    MorphismError::DomainMismatch
);   
return result
    }

    return Err(MorphismError::DomainMismatch);

    
        // let mut node_map = HashMap::new();
        // let mut edge_map = HashMap::new();

        // // For a strict inclusion, f(v) = v
        // for &node in h1.nodes() {
        //     if h2.nodes().contains(&node) {
        //         node_map.insert(node, node);
        //     }
        // }

        // // For a strict inclusion, f(e) = e
        // for &edge in h1.edges() {
        //     if h2.edges().contains(&edge) {
        //         edge_map.insert(edge, edge);
        //     }
        // }

        // BHypMorphism::new(
        //     h1.clone(), 
        //     h2.clone(),
        //     node_map,
        //     edge_map
        // )
}

// ============================================================================
// Safe Copying Conditions (Definition 3.11)
// ============================================================================

/// Check the safe copying conditions from Definition 3.11
/// 
/// For G ∈ sbHyp, v ∈ G such that out(v) ≥ 2, T is a sub-hypergraph such that:
/// 1. ∀e ∈ T, e' ∈ G^i_e : e' ∈ T 
///    (if T contains an edge with a body, the entire body must be in T)
/// 2. ∀e' ∈ T, e' ∈ G^i_e, ∃e1 ∈ T, e1 ∉ G^i_e : e ∈ T
///    (when copying part of a body with edges outside, must copy the carrier edge)
pub fn check_safe_copying_conditions(
    // ToDo: add test where condition is satisfied and assert result is safe;
    // add test where condition is violated and assert result is not safe
    g: &BHyp,
    t: &BHyp,
    shared_node: NodeId,
) -> bool {
    let t_inclusion = build_inclusion(t, g).unwrap();

    let t_int = BHyp_with_interface::from_bhyp(t.clone());
    // Get edges in T (in G's edge space)
    let t_edges_in_g: HashSet<EdgeId> = t_inclusion.edge_image();
    
    // Condition 1: If T contains an edge e with a body, the body edges must be in T
    for &t_e in t.edges() {
        let g_e = t_inclusion.map_edge(t_e).unwrap();
        
        // Check each source that might have a body
        if let Some(swbs) = g.get_sources_with_binding(g_e) {
            for (i, swb) in swbs.iter().enumerate() {
                if !swb.bound.is_empty() {
                    // This source has binding, compute its body
                    if let Some(body_edges) = g.compute_body_edges(g_e, i) {
                        for &body_e in &body_edges {
                            if !t_edges_in_g.contains(&body_e) {
                                return false;
                            }
                        }
                    }
                }
            }
        }
    }
    
    // Condition 2: If T contains edge e' that's in some body G^i_e, and T contains
    // edges outside that body, then the carrier edge e must also be in T
    for &t_e in t.edges() {
        let g_e_prime = t_inclusion.map_edge(t_e).unwrap();
        
        // Check if g_e_prime is in any body
        for &carrier_e in g.edges() {
            if let Some(swbs) = g.get_sources_with_binding(carrier_e) {
                for (i, swb) in swbs.iter().enumerate() {
                    if !swb.bound.is_empty() {
                        if let Some(body_edges) = g.compute_body_edges(carrier_e, i) {
                            if body_edges.contains(&g_e_prime) {
                                // g_e_prime is in the body of carrier_e at source i
                                // Check if T has edges outside this body
                                let has_edge_outside = t_edges_in_g.iter()
                                    .any(|&e| !body_edges.contains(&e) && e != carrier_e);
                                
                                if has_edge_outside && !t_edges_in_g.contains(&carrier_e) {
                                    return false;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    
    true
}

fn check_copying_conditions(
    g: &BHyp,
    t: &BHyp,
    shared_node: Span,
) -> Result<(), CopyError> {
   
    let t_inclusion = build_inclusion(t, g).unwrap();

    let t_int = BHyp_with_interface::from_bhyp(t.clone());

    let k_node = shared_node.middle.nodes().iter().next().unwrap();

    let im = shared_node.to_l.map_node(*k_node).unwrap();
    
    // Check that shared_node is in T's output interface
    if !t_int.is_output(im) {
        return Err(CopyError::NodeNotInOutput(im));
    }
 
    
    Ok(())
    
}


// ============================================================================
// Copying (Definition 3.12)
// ============================================================================

/// Create n copies of a sub-hypergraph T, sharing free vertices
/// 
/// This creates (n·T)* which is n copies of T glued along their free vertices (input interface).
/// Also returns morphism projectino onto the single T
fn compute_n_copies(
    // ToDo: add optional interface paremeter (input interface by default) for glueing
    t: &BHyp,
    n: usize,
) -> Result<(BHyp, BHypMorphism), CopyError> {
    if n == 0 {
        return Err(CopyError::InvalidSubhypergraph("Cannot create 0 copies".to_string()));
    }
    
    // the result is pushout (T <- K-> (n-1)T) with K the interface
    // actually K = input interface, output should be copied
    if n == 1 {
        let id_nodes: HashMap<NodeId, NodeId> = t.nodes().iter()
            .map(|&n| (n, n)).collect();
        let id_edges: HashMap<EdgeId, EdgeId> = t.edges().iter()
            .map(|&e| (e, e)).collect();
        let projection = BHypMorphism::new(
            t.clone(),
            t.clone(),
            id_nodes,
            id_edges,
        )?;
        return Ok((t.clone(), projection));
    }

    // Start with first copy
    let mut result = t.clone();
    let mut res_map = identity_morphism(&result);
   

    let ti = BHyp_with_interface::from_bhyp(t.clone());
    let k = ti.input_interface();
    // to do: add free outputs to k
    
    let k_to_t = BHypMorphism::new(
            k.clone(),
            t.clone(),
            ti.input_map().clone(),
            HashMap::new(),
        )?;
    
    // interface map to the copied stays the same but changes codomain
    let mut k_to_tn = BHypMorphism::new(
            k.clone(),
            result.clone(),
            ti.input_map().clone(),
            HashMap::new(),
        )?;

    // projection starts as id, then gets composed with the next one
    let mut projection = identity_morphism(&t);
    
    // For copies 2..n, use pushout to glue along input and output interface
    for _copy_idx in 1..n {

        let next = compute_pushout(&k_to_tn, &k_to_t).unwrap();

       

        // build the projection maps
        let mut proj_nodes: HashMap<NodeId, NodeId> = HashMap::new();
        let mut proj_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

    // 1. Invert the nodes map

    // first inverse T -> T(n+1), projecting the id back from the n+1st copy
    for (&t_id, &next_id) in next.morphism_from_c.on_nodes().iter() {
        proj_nodes.insert(next_id, t_id);
    }
    
    // Second inverse: Compose (T(n+1) <- Tn) with (Tn -> T)
    // Iterate over morphism_from_b to see how Tn got mapped into the new T(n+1)
   for (&tn_id, &next_id) in next.morphism_from_b.on_nodes().iter() {
    // Look up what that Tn node originally mapped to in T
    if let Some(&t_id) = projection.on_nodes().get(&tn_id) {
        proj_nodes.insert(next_id, t_id);
    }
}


    // 2. Invert the edges map
    for (&t_id, &glued_id) in next.morphism_from_c.on_edges().iter() {
        proj_edges.insert(glued_id, t_id);
    }
    
    for (&tn_id, &glued_id) in next.morphism_from_b.on_edges().iter() {
    if let Some(&t_id) = projection.on_edges().get(&tn_id) {
        proj_edges.insert(glued_id, t_id);
    }
}


    // update the result
        result = next.pushout.clone();
         
        // Track where the interface nodes ended up in the newly glued graph T(n+1)
        let mut new_k_map = HashMap::new();
        for (&k_id, &tn_id) in k_to_tn.on_nodes().iter() {
            if let Some(&next_id) = next.morphism_from_b.on_nodes().get(&tn_id) {
                new_k_map.insert(k_id, next_id);
            }
        }

        // Create the updated interface morphism using the NEW glued IDs
        k_to_tn = BHypMorphism::new(
            k.clone(),
            result.clone(),
            new_k_map, // <-- Use the newly calculated map here
            HashMap::new(),
        )?;


    // create the projection map 
    projection = BHypMorphism::new(
        result.clone(),
        t.clone(),
        proj_nodes,
        proj_edges
    ).unwrap();


        
    }
 
    // make sure correct number of edges
    assert_eq!(result.edges().len(), n * t.edges().len());

    Ok((result, projection))
}

/// Perform copying of a shared sub-hypergraph (Definition 3.12)
///
/// Given G ∈ sbHyp, v ∈ G with out(v) ≥ 2, and T a safe sub-hypergraph with v ∈ O_T,
/// define Ĝ_T (G with copied T) as a pushout complement:
///
/// ```text
///     T ←─────── (n·T)*
///     │            │
///     ▼     ⌟      ▼
///     G ←─────── Ĝ_T
/// ```
///
/// where n = out(v) and (n·T)* is n copies of T sharing free vertices.
pub fn copy_subhypergraph(
    g: &BHyp,
    t: &BHyp,
    shared_node: Span, // make it a span relating two vertices one in g one in t, G <- K -> T
) -> Result<BHyp, CopyError> {
    // ToDo test  if n = 1 should equal original bhyp
    // Check safe copying conditions
    let incl = build_inclusion(t, g).unwrap();
    check_copying_conditions(g, t, shared_node.clone())?;

    // let g_node = shared_node.to_l.on_nodes().get(&shared_k_node).unwrap();
    // let n = shared_node.left.out_degree(*g_node);
    
    let k_node = shared_node.middle.nodes().iter().next().unwrap();
    let n = g.out_degree(shared_node.clone().to_l.map_node(*k_node).unwrap());

    assert!(n > 0);
    
    // Create (n·T)* - n copies sharing free vertices
    let (n_copies, projection) = compute_n_copies(t, n)?;
    
    // Use pushout complement to get result
    let pushout_complement = compute_pushout_complement(&projection, &incl)?;
    
    Ok(pushout_complement.complement)
}


#[cfg(test)]
mod copying_tests {
    use super::*;
    use crate::{bhyp::{BHyp, BHyp_with_interface, Label, SourceWithBinding}, categorical::are_isomorphic};

   
   
    // ============================================================================
    // Safe Copying Conditions Tests
    // ============================================================================

    #[test]
    fn test_safe_copying_conditions_satisfied() {
        let mut g = BHyp::new();
        let n_src = g.add_node();
        let n_bound = g.add_node();
        let n_mid = g.add_node();
        let n_tgt = g.add_node();

        // e1 binds n_bound
        let _e1 = g.add_edge(
            vec![SourceWithBinding { source: n_src, bound: vec![n_bound] }],
            vec![n_mid],
            Some(Label::Symbol("lambda".to_string())),
        ).unwrap();

        // e2 is in the body of e1 (because its source is the bound variable)
        let _e2 = g.add_edge(
            vec![SourceWithBinding { source: n_bound, bound: vec![] }],
            vec![n_tgt],
            Some(Label::Symbol("f".to_string())),
        ).unwrap();

        // T is the exact same as G (trivially satisfies copying conditions)
        let t = g.clone();
        
        let is_safe = check_safe_copying_conditions(&g, &t, n_mid);
        assert!(is_safe, "Condition should be satisfied when the body edge is fully included in T");
    }


    #[test]
    fn test_safe_copying_conditions_violated() {
        let mut g = BHyp::new();
        let n_src = g.add_node();
        let n_bound = g.add_node();
        let n_mid = g.add_node();
        let n_tgt = g.add_node();

        let _e1 = g.add_edge(
            vec![SourceWithBinding { source: n_src, bound: vec![n_bound] }],
            vec![n_mid],
            Some(Label::Symbol("lambda".to_string())),
        ).unwrap();

        let e2 = g.add_edge(
            vec![SourceWithBinding { source: n_bound, bound: vec![] }],
            vec![n_tgt],
            Some(Label::Symbol("f".to_string())),
        ).unwrap();

        // We want T to contain e1, but NOT e2. 
        // This violates Condition 1: if T has e1, it must contain e1's entire body.
        let mut t_int = BHyp_with_interface::from_bhyp(g.clone());
        t_int.remove_edge(e2).unwrap();
        t_int.remove_node(n_tgt).unwrap();
        
        let t = t_int.bhyp().clone();

        let is_safe = check_safe_copying_conditions(&g, &t, n_mid);
        assert!(!is_safe, "Condition must be violated because e2 (part of e1's body) is missing from T");
    }

    // ============================================================================
    // Sub-hypergraph Copying Tests
    // ============================================================================


     #[test]
    fn test_compute_n_copies_one() {
        // Create a simple graph T: (n_in) -> (n_out)
        let mut t = BHyp::new();
        let n_in = t.add_node();
        let n_out = t.add_node();
        
        t.add_edge(
            vec![SourceWithBinding { source: n_in, bound: vec![] }],
            vec![n_out],
            Some(Label::Symbol("e".to_string()))
        ).unwrap();
        

        let n = 1;
        let (result, _) = compute_n_copies(&t, n).unwrap();
        
        // the resulting graph should be the same as the original one
        assert_eq!(result.nodes().len(), t.nodes().len());
        assert_eq!(result.edges().len(), t.edges().len());
    
       
        assert!(are_isomorphic(&t, &result));
    
    }

    #[test]
    fn test_copy_subhypergraph_n_equals_1() {
        let mut g = BHyp::new();
        let n1 = g.add_node();
        let shared_node = g.add_node();
        let n3 = g.add_node();

        // Part inside T
        let _e1 = g.add_edge(
            vec![SourceWithBinding { source: n1, bound: vec![] }], 
            vec![shared_node], 
            None
        ).unwrap();
        
        // Part outside T (This gives shared_node an out-degree of 1 in G)
        let e2 = g.add_edge(
            vec![SourceWithBinding { source: shared_node, bound: vec![] }], 
            vec![n3], 
            None
        ).unwrap();

        // T is just n1 -> e1 -> shared_node
        // let mut t_int = BHyp_with_interface::from_bhyp(g.clone());
        // t_int.remove_edge(e2).unwrap();
        // t_int.remove_node(n3).unwrap();
        
        // let t = t_int.bhyp().clone();

        let mut t = BHyp::new();
        let tn1 = t.add_node();
        let tshared_node = t.add_node();
        

        // Part inside T
        let _te1 = t.add_edge(
            vec![SourceWithBinding { source: tn1, bound: vec![] }], 
            vec![tshared_node], 
            None
        ).unwrap();

        // Sanity check: In G, shared_node has out_degree = 1. So n = 1.
        assert_eq!(g.out_degree(shared_node), 1);
        

        let mut k =  BHyp::new();
        let x = k.add_node();

        // shared node maps
        let r = BHypMorphism::new(
            k.clone(),
            g.clone(),
            [(x, shared_node)].into_iter().collect(),
            HashMap::new(),

        ).unwrap();

        let l = BHypMorphism::new(
            k.clone(),
            t.clone(),
            [(x, tshared_node)].into_iter().collect(),
            HashMap::new(),

        ).unwrap();

        let shared_node = Span{
            left : g.clone(),
            middle : k,
            right : t.clone(),
            to_l: l,
            to_r: r};

        

        // Perform the copy
        let result = copy_subhypergraph(&g, &t, shared_node).expect("Copy operation failed");

        // When n = 1, the pushout complement should yield a graph isomorphic/identical to the original G.
        assert_eq!(result.nodes().len(), g.nodes().len(), "Result should have the same number of nodes as G");
        assert_eq!(result.edges().len(), g.edges().len(), "Result should have the same number of edges as G");
        
        assert!(are_isomorphic(&result, &g));
    
    }

    #[test]
    fn test_compute_n_copies_multiple() {
        // Create a simple graph T: (n_in) -> (n_out)
        let mut t = BHyp::new();
        let n_in = t.add_node();
        let n_out = t.add_node();
        
        t.add_edge(
            vec![SourceWithBinding { source: n_in, bound: vec![] }],
            vec![n_out],
            Some(Label::Symbol("e".to_string()))
        ).unwrap();
        

        let n = 3;
        let (result, _) = compute_n_copies(&t, n).unwrap();
        
        // Because n_in and n_out are interfaces, they act as the glue points.
        // 3 copies glued at the interface means the resulting graph has exactly 
        // 4 nodes (the shared input interfaces, copied output) and 3 parallel edges.
        assert_eq!(result.nodes().len(), 4, "Copies should share the input interface vertices");
        assert_eq!(result.edges().len(), 3, "There should be exactly 3 edges from the 3 copies");
    
       let mut tt = BHyp::new();
        let n_in = tt.add_node();
        let o1 = tt.add_node();
        let o2 = tt.add_node();
        let o3 = tt.add_node();
        
        tt.add_edge(
            vec![SourceWithBinding { source: n_in, bound: vec![] }],
            vec![o1],
            Some(Label::Symbol("e".to_string()))
        ).unwrap();
        tt.add_edge(
            vec![SourceWithBinding { source: n_in, bound: vec![] }],
            vec![o2],
            Some(Label::Symbol("e".to_string()))
        ).unwrap();
        tt.add_edge(
            vec![SourceWithBinding { source: n_in, bound: vec![] }],
            vec![o3],
            Some(Label::Symbol("e".to_string()))
        ).unwrap();

        assert!(are_isomorphic(&tt, &result));
    
    }

    #[test]
    fn copy_simple_subhyp() {
        // Create a simple graph T: (n_in) -> (n_out)
        let mut t = BHyp::new();
        let n_in = t.add_node();
        let n_out = t.add_node();
        
        t.add_edge(
            vec![SourceWithBinding { source: n_in, bound: vec![] }],
            vec![n_out],
            Some(Label::Symbol("e".to_string()))
        ).unwrap();  

        // create g containing sharing of T
        let mut g = BHyp::new();
        let t_in = g.add_node();
        let t_out = g.add_node();

        let x1 = g.add_node();
        let x2 = g.add_node();
        let x3 = g.add_node();
        
        g.add_edge(
            vec![SourceWithBinding { source: t_in, bound: vec![] }],
            vec![t_out],
            Some(Label::Symbol("e".to_string()))
        ).unwrap();
        g.add_edge(
            vec![SourceWithBinding { source: t_out, bound: vec![] }],
            vec![x1],
            Some(Label::Symbol("f1".to_string()))
        ).unwrap();
        g.add_edge(
            vec![SourceWithBinding { source: t_out, bound: vec![] }],
            vec![x2],
            Some(Label::Symbol("f2".to_string()))
        ).unwrap();
        g.add_edge(
            vec![SourceWithBinding { source: t_out, bound: vec![] }],
            vec![x3],
            Some(Label::Symbol("f3".to_string()))
        ).unwrap();


        let mut k =  BHyp::new();
        let x = k.add_node();

        // shared node maps
        let r = BHypMorphism::new(
            k.clone(),
            g.clone(),
            [(x, t_out)].into_iter().collect(),
            HashMap::new(),

        ).unwrap();

        let l = BHypMorphism::new(
            k.clone(),
            t.clone(),
            [(x, n_out)].into_iter().collect(),
            HashMap::new(),

        ).unwrap();

        let shared_node = Span{
            left : g.clone(),
            middle : k,
            right : t.clone(),
            to_l: l,
            to_r: r};

        // Perform the copy
        let k_node = shared_node.middle.nodes().iter().next().unwrap();
        let n = g.out_degree(shared_node.clone().to_l.map_node(*k_node).unwrap());

        assert_eq!(n, 3);
      
        let result = copy_subhypergraph(
            &g, &t, shared_node).unwrap();

        // result should have 6 edges and 7 nodes
        assert_eq!(result.nodes().len(), 7);
        assert_eq!(result.edges().len(), 6);

        let mut exp = BHyp::new();
        let t_in = exp.add_node();

        let x1 = exp.add_node();
        let x2 = exp.add_node();
        let x3 = exp.add_node();

        let y1 = exp.add_node();
        let y2 = exp.add_node();
        let y3 = exp.add_node();
        
        exp.add_edge(
            vec![SourceWithBinding { source: t_in, bound: vec![] }],
            vec![y1],
            Some(Label::Symbol("e".to_string()))
        ).unwrap();
        exp.add_edge(
            vec![SourceWithBinding { source: t_in, bound: vec![] }],
            vec![y2],
            Some(Label::Symbol("e".to_string()))
        ).unwrap();
        exp.add_edge(
            vec![SourceWithBinding { source: t_in, bound: vec![] }],
            vec![y3],
            Some(Label::Symbol("e".to_string()))
        ).unwrap();

        exp.add_edge(
            vec![SourceWithBinding { source: y1, bound: vec![] }],
            vec![x1],
            Some(Label::Symbol("f1".to_string()))
        ).unwrap();
        exp.add_edge(
            vec![SourceWithBinding { source: y2, bound: vec![] }],
            vec![x2],
            Some(Label::Symbol("f2".to_string()))
        ).unwrap();
        exp.add_edge(
            vec![SourceWithBinding { source: y3, bound: vec![] }],
            vec![x3],
            Some(Label::Symbol("f3".to_string()))
        ).unwrap();

        assert!(are_isomorphic(&exp, &result));

    
    }

    #[test]
    fn test_copying_fails_when_node_not_in_output() {
        let mut g = BHyp::new();
        let n1 = g.add_node();
        let n2 = g.add_node();

        // Edge goes from n1 -> n2
        g.add_edge(
            vec![SourceWithBinding { source: n1, bound: vec![] }], 
            vec![n2], 
            None
        ).unwrap();

        let t = g.clone();

        let mut k =  BHyp::new();
        let x = k.add_node();

        // shared node maps
        let r = BHypMorphism::new(
            k.clone(),
            g.clone(),
            [(x, n1)].into_iter().collect(),
            HashMap::new(),

        ).unwrap();

        let l = BHypMorphism::new(
            k.clone(),
            t.clone(),
            [(x, n1)].into_iter().collect(),
            HashMap::new(),

        ).unwrap();

        let shared_node = Span{
            left : g.clone(),
            middle : k,
            right : t.clone(),
            to_l: l,
            to_r: r};

        // Perform the copy
    //    let result = copy_subhypergraph(&g, &t, shared_node).expect("Copy operation failed");

        
        // n1 is the source (in_degree = 0, out_degree = 1).
        // It is NOT in the output interface of T.
        let result = copy_subhypergraph(&g, &t, shared_node);
        
        assert!(
            matches!(result, Err(CopyError::NodeNotInOutput(_))),
            "Should return a NodeNotInOutput error because n1 is not in T's output interface"
        );
    }
}


// ============================================================================
// Glueing (Definition 3.15)
// ============================================================================

/// Perform glueing of multiple inclusions of H in G (Definition 3.15)
///
/// Given H, G ∈ sbHyp and different inclusions m1: H ↪ G, ..., mn: H ↪ G,
/// the result of glueing H in G is obtained as pushout: PO(G ← n·H → H)
///
/// ```text
///     n·H ←────── H
///      │          │
///      ▼    ⌟     ▼
///      G ←────── Ĝ
/// ```


pub fn glue_subhypergraph(
    g: &BHyp,
    h: &BHyp
) -> Result<GlueResult, GlueError> {
    // find n, n inclusions --> that's also useful later for metavar extraction
    let inclusions = find_all_ccurrences(h, g);

    let n = inclusions.len();
    if n == 0 {
         return Err(GlueError::InvalidSubhypergraph("Not a subhypergraph!".to_string()));
    }

    // todo add optionsl interface parameter
    // build projection n H -> H
    let (nH, proj) = compute_n_copies(h, n).unwrap();
    // build inclusion n H -> G
    let incl = build_inclusion(&nH, g).unwrap();
    // build pushout (G <- n H -> H)
    let pushout_res = compute_pushout(&incl, &proj)?;

    Ok(GlueResult {
        result: pushout_res.pushout,
        morphism: pushout_res.morphism_from_b, 
    })
    
    
}



#[cfg(test)]
mod glueing_tests {
    use super::*;
    use crate::{bhyp::{BHyp, BHyp_with_interface, Label, SourceWithBinding}, categorical::are_isomorphic};
    

    #[test]
    pub fn find_all_occurence() {
        
    }


    #[test]
    pub fn glue_one_occurence() {
        
    }

    #[test]
    pub fn glue_simple_subhyp() {
        // Create a simple graph T: (n_in) -> (n_out)
        let mut t = BHyp::new();
        let n_in = t.add_node();
        let n_out = t.add_node();
        
        t.add_edge(
            vec![SourceWithBinding { source: n_in, bound: vec![] }],
            vec![n_out],
            Some(Label::Symbol("e".to_string()))
        ).unwrap();

        // create the graph with multiple t
        let mut exp = BHyp::new();

        let t_in = exp.add_node();

        let x1 = exp.add_node();
        let x2 = exp.add_node();
        let x3 = exp.add_node();

        let y1 = exp.add_node();
        let y2 = exp.add_node();
        let y3 = exp.add_node();
        
        exp.add_edge(
            vec![SourceWithBinding { source: t_in, bound: vec![] }],
            vec![y1],
            Some(Label::Symbol("e".to_string()))
        ).unwrap();
        exp.add_edge(
            vec![SourceWithBinding { source: t_in, bound: vec![] }],
            vec![y2],
            Some(Label::Symbol("e".to_string()))
        ).unwrap();
        exp.add_edge(
            vec![SourceWithBinding { source: t_in, bound: vec![] }],
            vec![y3],
            Some(Label::Symbol("e".to_string()))
        ).unwrap();

        exp.add_edge(
            vec![SourceWithBinding { source: y1, bound: vec![] }],
            vec![x1],
            Some(Label::Symbol("f1".to_string()))
        ).unwrap();
        exp.add_edge(
            vec![SourceWithBinding { source: y2, bound: vec![] }],
            vec![x2],
            Some(Label::Symbol("f2".to_string()))
        ).unwrap();
        exp.add_edge(
            vec![SourceWithBinding { source: y3, bound: vec![] }],
            vec![x3],
            Some(Label::Symbol("f3".to_string()))
        ).unwrap();

       // glue
       let res = glue_subhypergraph(&exp, &t).unwrap();

       assert_eq!(res.result.edges().len(), 4);
       assert_eq!(res.result.nodes().len(), 5);

       // create g containing sharing of T
        let mut g = BHyp::new();
        let t_in = g.add_node();
        let t_out = g.add_node();

        let x1 = g.add_node();
        let x2 = g.add_node();
        let x3 = g.add_node();
        
        g.add_edge(
            vec![SourceWithBinding { source: t_in, bound: vec![] }],
            vec![t_out],
            Some(Label::Symbol("e".to_string()))
        ).unwrap();
        g.add_edge(
            vec![SourceWithBinding { source: t_out, bound: vec![] }],
            vec![x1],
            Some(Label::Symbol("f1".to_string()))
        ).unwrap();
        g.add_edge(
            vec![SourceWithBinding { source: t_out, bound: vec![] }],
            vec![x2],
            Some(Label::Symbol("f2".to_string()))
        ).unwrap();
        g.add_edge(
            vec![SourceWithBinding { source: t_out, bound: vec![] }],
            vec![x3],
            Some(Label::Symbol("f3".to_string()))
        ).unwrap();

        assert!(are_isomorphic(&g, &res.result));


    }

    #[test]
    pub fn copy_glue_roundtrip() {
        
    }
   
}

// // ============================================================================
// // Equality modulo copying/glueing (Definition 3.16)
// // ============================================================================

// /// Check if two hypergraphs are equal modulo copying and glueing
// /// 
// /// G =_{bHyp} H if one can be turned into the other by a finite sequence
// /// of copying and glueing operations.
// ///
// /// This is a simplified check that tests for isomorphism after normalizing
// /// shared structures.
// pub fn equal_modulo_copy_glue(g: &BHyp, h: &BHyp) -> bool {
//     // For a full implementation, we would need to:
//     // 1. Enumerate all possible copying/glueing sequences
//     // 2. Check if any sequence transforms G into H
    
//     // Simplified: check if they have the same "semantic content"
//     // by comparing after fully expanding all shared subgraphs
    
//     use crate::categorical::are_isomorphic;
    
//     // First, quick check: if isomorphic, they're equal
//     if are_isomorphic(g, h) {
//         return true;
//     }
    
//     // Check if node/edge counts differ only by sharing factors
//     // This is a heuristic - full implementation would be more complex
    
//     // If both are discrete (no edges), just compare node counts
//     if g.is_discrete() && h.is_discrete() {
//         return g.nodes().len() == h.nodes().len();
//     }
    
//     // For non-trivial cases, we'd need more sophisticated analysis
//     // This is left as a TODO for full implementation
//     false
// }

// // ============================================================================
// // Helper: Find all inclusions of H in G
// // ============================================================================

// /// Find all monomorphic inclusions of H into G
// pub fn find_all_inclusions(h: &BHyp, g: &BHyp) -> Vec<BHypMorphism> {
//     let mut inclusions = Vec::new();
    
//     // If H is empty, there's exactly one inclusion (empty morphism)
//     if h.is_empty() {
//         if let Ok(inc) = BHypMorphism::new(
//             h.clone(),
//             g.clone(),
//             HashMap::new(),
//             HashMap::new(),
//         ) {
//             inclusions.push(inc);
//         }
//         return inclusions;
//     }
    
//     // For non-empty H, try all possible node mappings
//     let h_nodes: Vec<NodeId> = h.nodes().iter().copied().collect();
//     let g_nodes: Vec<NodeId> = g.nodes().iter().copied().collect();
    
//     if h_nodes.len() > g_nodes.len() {
//         return inclusions;
//     }
    
//     // Generate all injective mappings from H nodes to G nodes
//     fn generate_mappings(
//         h_nodes: &[NodeId],
//         g_nodes: &[NodeId],
//         current_map: &mut HashMap<NodeId, NodeId>,
//         used: &mut HashSet<NodeId>,
//         idx: usize,
//         results: &mut Vec<HashMap<NodeId, NodeId>>,
//     ) {
//         if idx == h_nodes.len() {
//             results.push(current_map.clone());
//             return;
//         }
        
//         let h_n = h_nodes[idx];
//         for &g_n in g_nodes {
//             if !used.contains(&g_n) {
//                 current_map.insert(h_n, g_n);
//                 used.insert(g_n);
//                 generate_mappings(h_nodes, g_nodes, current_map, used, idx + 1, results);
//                 current_map.remove(&h_n);
//                 used.remove(&g_n);
//             }
//         }
//     }
    
//     let mut node_mappings = Vec::new();
//     let mut current_map = HashMap::new();
//     let mut used = HashSet::new();
//     generate_mappings(&h_nodes, &g_nodes, &mut current_map, &mut used, 0, &mut node_mappings);
    
//     // For each node mapping, try to find a compatible edge mapping
//     for node_map in node_mappings {
//         let mut edge_map = HashMap::new();
//         let mut valid = true;
        
//         for &h_e in h.edges() {
//             let h_swbs = h.get_sources_with_binding(h_e).unwrap();
//             let h_targets = h.get_targets(h_e).unwrap();
//             let h_label = h.get_label(h_e);
            
//             // Find matching edge in G
//             let mut found = false;
//             for &g_e in g.edges() {
//                 if edge_map.values().any(|&e| e == g_e) {
//                     continue;
//                 }
                
//                 let g_swbs = g.get_sources_with_binding(g_e).unwrap();
//                 let g_targets = g.get_targets(g_e).unwrap();
//                 let g_label = g.get_label(g_e);
                
//                 // Check compatibility
//                 if h_swbs.len() != g_swbs.len() || h_targets.len() != g_targets.len() {
//                     continue;
//                 }
//                 if h_label != g_label {
//                     continue;
//                 }
                
//                 let mut matches = true;
                
//                 // Check sources and bindings
//                 for (h_swb, g_swb) in h_swbs.iter().zip(g_swbs.iter()) {
//                     if node_map.get(&h_swb.source) != Some(&g_swb.source) {
//                         matches = false;
//                         break;
//                     }
//                     if h_swb.bound.len() != g_swb.bound.len() {
//                         matches = false;
//                         break;
//                     }
//                     for (h_b, g_b) in h_swb.bound.iter().zip(g_swb.bound.iter()) {
//                         if node_map.get(h_b) != Some(g_b) {
//                             matches = false;
//                             break;
//                         }
//                     }
//                 }
                
//                 // Check targets
//                 if matches {
//                     for (h_t, g_t) in h_targets.iter().zip(g_targets.iter()) {
//                         if node_map.get(h_t) != Some(g_t) {
//                             matches = false;
//                             break;
//                         }
//                     }
//                 }
                
//                 if matches {
//                     edge_map.insert(h_e, g_e);
//                     found = true;
//                     break;
//                 }
//             }
            
//             if !found {
//                 valid = false;
//                 break;
//             }
//         }
        
//         if valid && edge_map.len() == h.edges().len() {
//             if let Ok(inc) = BHypMorphism::new(
//                 h.clone(),
//                 g.clone(),
//                 node_map,
//                 edge_map,
//             ) {
//                 inclusions.push(inc);
//             }
//         }
//     }
    
//     inclusions
// }

// // ============================================================================
// // Tests
// // ============================================================================

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn test_subhypergraph_from_edges() {
//         let mut g = BHyp::new();
//         let n1 = g.add_node();
//         let n2 = g.add_node();
//         let n3 = g.add_node();
        
//         let e1 = g.add_edge(
//             vec![SourceWithBinding { source: n1, bound: vec![] }],
//             vec![n2],
//             Some(Label::Symbol("f".to_string())),
//         ).unwrap();
        
//         let e2 = g.add_edge(
//             vec![SourceWithBinding { source: n2, bound: vec![] }],
//             vec![n3],
//             Some(Label::Symbol("g".to_string())),
//         ).unwrap();
        
//         // Create subhypergraph from just e1
//         let edges: HashSet<EdgeId> = [e1].into_iter().collect();
//         let sub = Subhypergraph::from_edges(&g, &edges).unwrap();
        
//         assert_eq!(sub.subgraph.nodes().len(), 2);
//         assert_eq!(sub.subgraph.edges().len(), 1);
//         assert_eq!(sub.output_nodes.len(), 1); // n2 maps to output
//         assert_eq!(sub.input_nodes.len(), 1);  // n1 maps to input
//     }

//     #[test]
//     fn test_create_n_copies_shared() {
//         let mut t = BHyp::new();
//         let t1 = t.add_node(); // input/shared
//         let t2 = t.add_node(); // output
//         t.add_edge(
//             vec![SourceWithBinding { source: t1, bound: vec![] }],
//             vec![t2],
//             Some(Label::Symbol("f".to_string())),
//         ).unwrap();
        
//         let sub = Subhypergraph {
//             subgraph: t.clone(),
//             inclusion: BHypMorphism::new(
//                 t.clone(), t.clone(),
//                 [(t1, t1), (t2, t2)].into_iter().collect(),
//                 [(EdgeId(0), EdgeId(0))].into_iter().collect(),
//             ).unwrap(),
//             output_nodes: [t2].into_iter().collect(),
//             input_nodes: [t1].into_iter().collect(),
//         };
        
//         let (copies, morphisms) = create_n_copies_shared(&sub, 3).unwrap();
        
//         // Should have 3 edges (one per copy) but fewer than 6 nodes due to sharing
//         assert_eq!(copies.edges().len(), 3);
//         assert_eq!(morphisms.len(), 3);
//         // Input node is shared, output nodes are distinct
//         // So: 1 shared input + 3 distinct outputs = 4 nodes
//         assert_eq!(copies.nodes().len(), 4);
//     }

//     #[test]
//     fn test_find_all_inclusions_empty() {
//         let h = BHyp::new();
//         let mut g = BHyp::new();
//         g.add_node();
        
//         let inclusions = find_all_inclusions(&h, &g);
//         assert_eq!(inclusions.len(), 1);
//     }

//     #[test]
//     fn test_find_all_inclusions_single_node() {
//         let mut h = BHyp::new();
//         h.add_node();
        
//         let mut g = BHyp::new();
//         g.add_node();
//         g.add_node();
//         g.add_node();
        
//         let inclusions = find_all_inclusions(&h, &g);
//         // Should find 3 inclusions (one for each G node)
//         assert_eq!(inclusions.len(), 3);
//     }

//     #[test]
//     fn test_find_all_inclusions_with_edge() {
//         let mut h = BHyp::new();
//         let h1 = h.add_node();
//         let h2 = h.add_node();
//         h.add_edge(
//             vec![SourceWithBinding { source: h1, bound: vec![] }],
//             vec![h2],
//             Some(Label::Symbol("f".to_string())),
//         ).unwrap();
        
//         let mut g = BHyp::new();
//         let g1 = g.add_node();
//         let g2 = g.add_node();
//         let g3 = g.add_node();
//         // Two f-labeled edges
//         g.add_edge(
//             vec![SourceWithBinding { source: g1, bound: vec![] }],
//             vec![g2],
//             Some(Label::Symbol("f".to_string())),
//         ).unwrap();
//         g.add_edge(
//             vec![SourceWithBinding { source: g2, bound: vec![] }],
//             vec![g3],
//             Some(Label::Symbol("f".to_string())),
//         ).unwrap();
        
//         let inclusions = find_all_inclusions(&h, &g);
//         // Should find 2 inclusions
//         assert_eq!(inclusions.len(), 2);
//     }

//     #[test]
//     fn test_glue_subhypergraph_two_copies() {
//         // Create G with two separate copies of H
//         let mut g = BHyp::new();
//         let g1 = g.add_node();
//         let g2 = g.add_node();
//         let g3 = g.add_node();
//         let g4 = g.add_node();
        
//         let ge1 = g.add_edge(
//             vec![SourceWithBinding { source: g1, bound: vec![] }],
//             vec![g2],
//             Some(Label::Symbol("f".to_string())),
//         ).unwrap();
//         let ge2 = g.add_edge(
//             vec![SourceWithBinding { source: g3, bound: vec![] }],
//             vec![g4],
//             Some(Label::Symbol("f".to_string())),
//         ).unwrap();
        
//         // H is a single f-edge
//         let mut h = BHyp::new();
//         let h1 = h.add_node();
//         let h2 = h.add_node();
//         let he = h.add_edge(
//             vec![SourceWithBinding { source: h1, bound: vec![] }],
//             vec![h2],
//             Some(Label::Symbol("f".to_string())),
//         ).unwrap();
        
//         // Two inclusions
//         let inc1 = BHypMorphism::new(
//             h.clone(), g.clone(),
//             [(h1, g1), (h2, g2)].into_iter().collect(),
//             [(he, ge1)].into_iter().collect(),
//         ).unwrap();
        
//         let inc2 = BHypMorphism::new(
//             h.clone(), g.clone(),
//             [(h1, g3), (h2, g4)].into_iter().collect(),
//             [(he, ge2)].into_iter().collect(),
//         ).unwrap();
        
//         let result = glue_subhypergraph(&g, &h, &[inc1, inc2]).unwrap();
        
//         // After glueing, should have 2 nodes and 1 edge
//         assert_eq!(result.result.nodes().len(), 2);
//         assert_eq!(result.result.edges().len(), 1);
//     }

//     #[test]
//     fn test_glue_requires_two_inclusions() {
//         let h = BHyp::new();
//         let g = BHyp::new();
        
//         let result = glue_subhypergraph(&g, &h, &[]);
//         assert!(matches!(result, Err(CopyGlueError::InsufficientInclusions)));
//     }

//     #[test]
//     fn test_equal_modulo_isomorphic() {
//         let mut g = BHyp::new();
//         g.add_node();
        
//         let mut h = BHyp::new();
//         h.add_node();
        
//         assert!(equal_modulo_copy_glue(&g, &h));
//     }

//      #[test]
//     fn test_copy_glue_id() {
//         let mut g = BHyp::new();
//         // To Do
//     }
// }