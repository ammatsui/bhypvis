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

        let next = compute_pushout(&k_to_t, &k_to_tn).unwrap();

        // update the result and k_to_tn
        result = next.pushout.clone();
         
        k_to_tn = BHypMorphism::new(
            k.clone(),
            result.clone(),
            ti.input_map().clone(),
            HashMap::new(),
        )?;

        // build the projection maps
        let mut proj_nodes: HashMap<NodeId, NodeId> = HashMap::new();
        let mut proj_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

    // 1. Invert the nodes map
    for (&t_id, &result_id) in next.morphism_from_c.on_nodes().iter() {
        proj_nodes.insert(result_id, t_id);
    }
    
    for (&t_id, &result_id) in next.morphism_from_b.on_nodes().iter() {
        // For interface nodes that were glued, `glued_id` is the same for both t1 and t2.
        // Overwriting is safe because both copies agree that it maps back to the same `t_id`.
        proj_nodes.insert(result_id, t_id);
    }

    // 2. Invert the edges map
    for (&t_id, &glued_id) in next.morphism_from_c.on_edges().iter() {
        proj_edges.insert(glued_id, t_id);
    }
    
    for (&t_id, &glued_id) in next.morphism_from_b.on_edges().iter() {
        proj_edges.insert(glued_id, t_id);
    }

    // create the projection map 
    projection = BHypMorphism::new(
        result.clone(),
        t.clone(),
        proj_nodes,
        proj_edges
    ).unwrap();


        
    }

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
    shared_node: Span, // make it a span relating two vertices one in g one in t
) -> Result<BHyp, CopyError> {
    // ToDo test  if n = 1 should equal original bhyp
    // Check safe copying conditions
    let incl = build_inclusion(t, g).unwrap();
    check_copying_conditions(g, t, shared_node.clone())?;
    
    let k_node = shared_node.middle.nodes().iter().next().unwrap();
    let n = g.out_degree(shared_node.clone().to_r.map_node(*k_node).unwrap());
    
    // Create (n·T)* - n copies sharing free vertices
    let (n_copies, projection) = compute_n_copies(t, n)?;
    
    // Use pushout complement to get result
    let pushout_complement = compute_pushout_complement(&incl, &projection)?;
    
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
        // 2 nodes (the shared interfaces) and 3 parallel edges.
        assert_eq!(result.nodes().len(), 2, "Copies should share the interface vertices");
        assert_eq!(result.edges().len(), 3, "There should be exactly 3 edges from the 3 copies");
    
       let mut tt = BHyp::new();
        let n_in = tt.add_node();
        let n_out = tt.add_node();
        
        tt.add_edge(
            vec![SourceWithBinding { source: n_in, bound: vec![] }],
            vec![n_out],
            Some(Label::Symbol("e".to_string()))
        ).unwrap();
        tt.add_edge(
            vec![SourceWithBinding { source: n_in, bound: vec![] }],
            vec![n_out],
            Some(Label::Symbol("e".to_string()))
        ).unwrap();
        tt.add_edge(
            vec![SourceWithBinding { source: n_in, bound: vec![] }],
            vec![n_out],
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
      
        let result = copy_subhypergraph(
            &g, &t, shared_node).unwrap();

        // result should have 6 edges
        assert_eq!(result.nodes().len(), 5);
        assert_eq!(result.edges().len(), 7);

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
            vec![x1],
            Some(Label::Symbol("f2".to_string()))
        ).unwrap();
        exp.add_edge(
            vec![SourceWithBinding { source: y3, bound: vec![] }],
            vec![x1],
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


// // ============================================================================
// // Glueing (Definition 3.15)
// // ============================================================================

// /// Perform glueing of multiple inclusions of H in G (Definition 3.15)
// ///
// /// Given H, G ∈ sbHyp and different inclusions m1: H ↪ G, ..., mn: H ↪ G,
// /// the result of glueing H in G is obtained as pushout: PO(G ← n·H → H)
// ///
// /// ```text
// ///     n·H ←────── H
// ///      │          │
// ///      ▼    ⌟     ▼
// ///      G ←────── Ĝ
// /// ```
// pub fn glue_subhypergraph(
//     g: &BHyp,
//     h: &BHyp,
//     inclusions: &[BHypMorphism],
// ) -> Result<GlueResult, CopyGlueError> {
//     if inclusions.len() < 2 {
//         return Err(CopyGlueError::InsufficientInclusions);
//     }
    
//     // Verify all inclusions are valid monomorphisms from H to G
//     for (i, inc) in inclusions.iter().enumerate() {
//         if !inc.is_monomorphism() {
//             return Err(CopyGlueError::IncompatibleInclusions(
//                 format!("Inclusion {} is not a monomorphism", i)
//             ));
//         }
//         // Check domain is H and codomain is G
//         if inc.domain().nodes() != h.nodes() || inc.domain().edges() != h.edges() {
//             return Err(CopyGlueError::IncompatibleInclusions(
//                 format!("Inclusion {} has wrong domain", i)
//             ));
//         }
//         if inc.codomain().nodes() != g.nodes() || inc.codomain().edges() != g.edges() {
//             return Err(CopyGlueError::IncompatibleInclusions(
//                 format!("Inclusion {} has wrong codomain", i)
//             ));
//         }
//     }
    
//     let n = inclusions.len();
    
//     // Create n·H (n disjoint copies of H)
//     let mut n_h = BHyp::new();
//     let mut copy_nodes: Vec<HashMap<NodeId, NodeId>> = Vec::new();
//     let mut copy_edges: Vec<HashMap<EdgeId, EdgeId>> = Vec::new();
    
//     for _ in 0..n {
//         let mut h_to_nh_nodes = HashMap::new();
//         let mut h_to_nh_edges = HashMap::new();
        
//         // Add nodes for this copy
//         let mut sorted_nodes: Vec<_> = h.nodes().iter().copied().collect();
//         sorted_nodes.sort();
//         for h_n in sorted_nodes {
//             let nh_n = n_h.add_node();
//             h_to_nh_nodes.insert(h_n, nh_n);
//         }
        
//         // Add edges for this copy
//         let mut sorted_edges: Vec<_> = h.edges().iter().copied().collect();
//         sorted_edges.sort();
//         for h_e in sorted_edges {
//             let swbs = h.get_sources_with_binding(h_e).unwrap();
//             let targets = h.get_targets(h_e).unwrap();
//             let label = h.get_label(h_e).cloned();
            
//             let new_swbs: Vec<SourceWithBinding> = swbs.iter().map(|swb| {
//                 SourceWithBinding {
//                     source: h_to_nh_nodes[&swb.source],
//                     bound: swb.bound.iter().map(|&b| h_to_nh_nodes[&b]).collect(),
//                 }
//             }).collect();
//             let new_targets: Vec<NodeId> = targets.iter()
//                 .map(|&t| h_to_nh_nodes[&t])
//                 .collect();
            
//             let nh_e = n_h.add_edge(new_swbs, new_targets, label)
//                 .map_err(|s| CopyGlueError::InvalidSubhypergraph(s))?;
//             h_to_nh_edges.insert(h_e, nh_e);
//         }
        
//         copy_nodes.push(h_to_nh_nodes);
//         copy_edges.push(h_to_nh_edges);
//     }
    
//     // Build morphism n·H → G using the inclusions
//     let mut nh_to_g_nodes: HashMap<NodeId, NodeId> = HashMap::new();
//     let mut nh_to_g_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
    
//     for (i, inc) in inclusions.iter().enumerate() {
//         for (&h_n, &nh_n) in &copy_nodes[i] {
//             nh_to_g_nodes.insert(nh_n, inc.map_node(h_n).unwrap());
//         }
//         for (&h_e, &nh_e) in &copy_edges[i] {
//             nh_to_g_edges.insert(nh_e, inc.map_edge(h_e).unwrap());
//         }
//     }
    
//     let nh_to_g = BHypMorphism::new(
//         n_h.clone(),
//         g.clone(),
//         nh_to_g_nodes,
//         nh_to_g_edges,
//     )?;
    
//     // Build morphism n·H → H (fold all copies to single H)
//     let mut nh_to_h_nodes: HashMap<NodeId, NodeId> = HashMap::new();
//     let mut nh_to_h_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
    
//     for i in 0..n {
//         for (&h_n, &nh_n) in &copy_nodes[i] {
//             nh_to_h_nodes.insert(nh_n, h_n);
//         }
//         for (&h_e, &nh_e) in &copy_edges[i] {
//             nh_to_h_edges.insert(nh_e, h_e);
//         }
//     }
    
//     let nh_to_h = BHypMorphism::new(
//         n_h.clone(),
//         h.clone(),
//         nh_to_h_nodes,
//         nh_to_h_edges,
//     )?;
    
//     // Compute pushout: PO(G ← n·H → H)
//     let pushout_result = compute_pushout(&nh_to_g, &nh_to_h)?;
    
//     // The glued morphism is H → result
//     let glued_nodes: HashMap<NodeId, NodeId> = h.nodes().iter()
//         .map(|&h_n| (h_n, pushout_result.morphism_from_c.map_node(h_n).unwrap()))
//         .collect();
//     let glued_edges: HashMap<EdgeId, EdgeId> = h.edges().iter()
//         .map(|&h_e| (h_e, pushout_result.morphism_from_c.map_edge(h_e).unwrap()))
//         .collect();
    
//     let glued_morphism = BHypMorphism::new(
//         h.clone(),
//         pushout_result.pushout.clone(),
//         glued_nodes,
//         glued_edges,
//     )?;
    
//     Ok(GlueResult {
//         result: pushout_result.pushout,
//         glued_morphism,
//     })
// }

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