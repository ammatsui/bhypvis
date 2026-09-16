// // copying, glueing, etc

// //- Copying: duplicates a shared sub-hypergraph
// // - Glueing: merges multiple inclusions of a sub-hypergraph (inverse of copying)

use std::collections::{HashMap, HashSet};

use crate::bhyp::{BHyp, BHyp_with_interface, EdgeId, Label, NodeId, SourceWithBinding};
use crate::categorical::{
    BHypMorphism, CategoricalError, MorphismError, PushoutResult, Span, 
    are_isomorphic, compute_pushout, compute_pushout_complement, build_inclusion,
    identity_morphism, find_all_occurrences, find_subhypergraph_inclusion, is_subhypergraph
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


    /// Create n copies of a sub-hypergraph T, sharing free vertices.
///
/// This creates (n·T)*, i.e. n copies of T glued along the chosen interface.
/// Also returns:
/// - projection: (n·T)* -> T
/// - inclusions: Vec<T -> (n·T)*>, one inclusion for each copy
pub fn compute_n_copies(
    t: &BHyp,
    n: usize,
    // Optional interface: (K, K -> T). If None, defaults to T's input interface,
    // for gluing along it.
    interface: Option<(BHyp, BHypMorphism)>,
) -> Result<(BHyp, BHypMorphism, Vec<BHypMorphism>), CopyError> {
    if n == 0 {
        return Err(CopyError::InvalidSubhypergraph(
            "Cannot create 0 copies".to_string(),
        ));
    }

    // Identity on T.
    let id_nodes: HashMap<NodeId, NodeId> = t
        .nodes()
        .iter()
        .map(|&node| (node, node))
        .collect();

    let id_edges: HashMap<EdgeId, EdgeId> = t
        .edges()
        .iter()
        .map(|&edge| (edge, edge))
        .collect();

    let id_t = BHypMorphism::new(
        t.clone(),
        t.clone(),
        id_nodes,
        id_edges,
    )?;

    // If n == 1, result is T itself.
    if n == 1 {
        let projection = id_t.clone();
        let inclusions = vec![id_t];

        return Ok((t.clone(), projection, inclusions));
    }

    // Start with first copy.
    let mut result = t.clone();

    // Current projection:
    //
    //     result -> T
    //
    // Initially id_T.
    let mut projection = id_t.clone();

    // Current inclusions:
    //
    //     T -> result
    //
    // Initially just id_T.
    let mut inclusions: Vec<BHypMorphism> = vec![id_t];

    // ---------------------------------------------------------------------
    // 1. Resolve the interface K and its injection into T.
    // ---------------------------------------------------------------------

    let (k, k_to_t) = match interface {
        Some((custom_k, custom_morphism)) => (custom_k, custom_morphism),
        None => {
            // Default behavior: use the input interface.
            let ti = BHyp_with_interface::from_bhyp(t.clone());

            let default_k = ti.input_interface().clone();

            let default_morphism = BHypMorphism::new(
                default_k.clone(),
                t.clone(),
                ti.input_map().clone(),
                HashMap::new(),
            )?;

            (default_k, default_morphism)
        }
    };

    // Interface map to the current copied object.
    //
    // Initially:
    //
    //     K -> T = result
    //
    let mut k_to_tn = BHypMorphism::new(
        k.clone(),
        result.clone(),
        k_to_t.on_nodes().clone(),
        k_to_t.on_edges().clone(),
    )?;

    // ---------------------------------------------------------------------
    // 2. For copies 2..n, glue another T along K.
    // ---------------------------------------------------------------------

    for _copy_idx in 1..n {
        // Pushout:
        //
        //     result <- K -> T
        //
        // producing:
        //
        //     next.pushout = result glued with fresh T along K
        //
        // with injections:
        //
        //     next.morphism_from_b : result -> next.pushout
        //     next.morphism_from_c : T      -> next.pushout
        //
        let next = compute_pushout(&k_to_tn, &k_to_t)?;

        // -----------------------------------------------------------------
        // Build the new projection:
        //
        //     next.pushout -> T
        //
        // On the newly added T copy, projection is identity.
        // On the old result part, projection is previous projection.
        // -----------------------------------------------------------------

        let mut proj_nodes: HashMap<NodeId, NodeId> = HashMap::new();
        let mut proj_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

        // New copy T -> pushout, invert to define projection back to T.
        for (&t_node, &po_node) in next.morphism_from_c.on_nodes().iter() {
            proj_nodes.insert(po_node, t_node);
        }

        for (&t_edge, &po_edge) in next.morphism_from_c.on_edges().iter() {
            proj_edges.insert(po_edge, t_edge);
        }

        // Old result -> pushout, compose old projection result -> T.
        for (&old_node, &po_node) in next.morphism_from_b.on_nodes().iter() {
            if let Some(&t_node) = projection.on_nodes().get(&old_node) {
                proj_nodes.insert(po_node, t_node);
            }
        }

        for (&old_edge, &po_edge) in next.morphism_from_b.on_edges().iter() {
            if let Some(&t_edge) = projection.on_edges().get(&old_edge) {
                proj_edges.insert(po_edge, t_edge);
            }
        }

        // -----------------------------------------------------------------
        // Build updated inclusions.
        //
        // Old inclusions:
        //
        //     incl_i : T -> result
        //
        // become:
        //
        //     T --incl_i--> result --next.morphism_from_b--> pushout
        //
        // New inclusion is:
        //
        //     next.morphism_from_c : T -> pushout
        // -----------------------------------------------------------------

        let mut updated_inclusions: Vec<BHypMorphism> = Vec::new();

        for old_incl in inclusions.iter() {
            let mut new_incl_nodes: HashMap<NodeId, NodeId> = HashMap::new();
            let mut new_incl_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

            // Nodes: T -> old result -> new pushout.
            for (&t_node, &old_result_node) in old_incl.on_nodes().iter() {
                let po_node = next
                    .morphism_from_b
                    .map_node(old_result_node)
                    .ok_or_else(|| {
                        CopyError::InvalidSubhypergraph(format!(
                            "pushout injection from old result does not map node {:?}",
                            old_result_node
                        ))
                    })?;

                new_incl_nodes.insert(t_node, po_node);
            }

            // Edges: T -> old result -> new pushout.
            for (&t_edge, &old_result_edge) in old_incl.on_edges().iter() {
                let po_edge = next
                    .morphism_from_b
                    .map_edge(old_result_edge)
                    .ok_or_else(|| {
                        CopyError::InvalidSubhypergraph(format!(
                            "pushout injection from old result does not map edge {:?}",
                            old_result_edge
                        ))
                    })?;

                new_incl_edges.insert(t_edge, po_edge);
            }

            let updated_incl = BHypMorphism::new(
                t.clone(),
                next.pushout.clone(),
                new_incl_nodes,
                new_incl_edges,
            )?;

            updated_inclusions.push(updated_incl);
        }

        // Add inclusion of the newly glued copy.
        //
        // This is exactly the pushout injection:
        //
        //     T -> next.pushout
        //
        let new_copy_inclusion = BHypMorphism::new(
            t.clone(),
            next.pushout.clone(),
            next.morphism_from_c.on_nodes().clone(),
            next.morphism_from_c.on_edges().clone(),
        )?;

        updated_inclusions.push(new_copy_inclusion);

        // -----------------------------------------------------------------
        // Update result.
        // -----------------------------------------------------------------

        result = next.pushout.clone();

        // -----------------------------------------------------------------
        // Update K -> result for the next iteration.
        //
        // Track where the interface nodes ended up through the old-result
        // injection:
        //
        //     K -> old result -> new result
        // -----------------------------------------------------------------

        let mut new_k_nodes = HashMap::new();

        for (&k_node, &old_result_node) in k_to_tn.on_nodes().iter() {
            if let Some(&po_node) = next.morphism_from_b.on_nodes().get(&old_result_node) {
                new_k_nodes.insert(k_node, po_node);
            }
        }

        let mut new_k_edges = HashMap::new();

        for (&k_edge, &old_result_edge) in k_to_tn.on_edges().iter() {
            if let Some(&po_edge) = next.morphism_from_b.on_edges().get(&old_result_edge) {
                new_k_edges.insert(k_edge, po_edge);
            }
        }

        k_to_tn = BHypMorphism::new(
            k.clone(),
            result.clone(),
            new_k_nodes,
            new_k_edges,
        )?;

        // Update projection.
        projection = BHypMorphism::new(
            result.clone(),
            t.clone(),
            proj_nodes,
            proj_edges,
        )?;

        // Update inclusions.
        inclusions = updated_inclusions;
    }

    // If K contains edges, glued edges collapse, so this assertion only makes
    // sense when K is discrete.
    if k.edges().is_empty() {
        assert_eq!(result.edges().len(), n * t.edges().len());
    }

    if inclusions.len() != n {
        return Err(CopyError::InvalidSubhypergraph(format!(
            "internal error: expected {} inclusions, got {}",
            n,
            inclusions.len()
        )));
    }

    Ok((result, projection, inclusions))

}


pub fn compute_n_copies_with_interface(
    t_int: &BHyp_with_interface,
    n: usize,
    interface: Option<(BHyp, BHypMorphism)>,
) -> Result<(BHyp_with_interface, BHypMorphism, Vec<BHypMorphism>), CopyError> {
    
    // 1. Resolve the interface (if None, efficiently use the already-computed input interface)
    let resolved_interface = match interface {
        Some(custom) => Some(custom),
        None => {
            let default_k = t_int.input_interface().clone();
            let default_morphism = BHypMorphism::new(
                default_k.clone(),
                t_int.bhyp().clone(),
                t_int.input_map().clone(),
                HashMap::new(),
            ).map_err(|e| CopyError::MorphismError(e))?;
            
            Some((default_k, default_morphism))
        }
    };

    // 2. Reuse the core logic (no duplication!)
    let (raw_result, projection, incls) = compute_n_copies(
        t_int.bhyp(), 
        n, 
        resolved_interface
    )?;

    // 3. Wrap the result, automatically recalculating the new interface boundaries
    let final_result = BHyp_with_interface::from_bhyp(raw_result);

    Ok((final_result, projection, incls))
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
    shared_node: Span, // G <- K -> T
) -> Result<BHyp, CopyError> {
    // Inclusion T -> G
    let incl = build_inclusion(t, g)?;

    check_copying_conditions(g, t, shared_node.clone())?;

    let k_node = shared_node
        .middle
        .nodes()
        .iter()
        .next()
        .copied()
        .ok_or_else(|| {
            CopyError::InvalidSubhypergraph(
                "shared_node.middle must contain the distinguished node".to_string(),
            )
        })?;

    let g_node = shared_node
        .to_l
        .map_node(k_node)
        .ok_or_else(|| {
            CopyError::InvalidSubhypergraph(format!(
                "shared_node.to_l does not map distinguished node {:?}",
                k_node
            ))
        })?;

    let n = g.out_degree(g_node);

    // if n < 2 {
    //     return Err(CopyError::InvalidConstruction(format!(
    //         "copy_subhypergraph requires out_degree({:?}) >= 2, got {}",
    //         g_node, n
    //     )));
    // }

    // (n·T)* -> T
    //
    // compute_n_copies(t, n, None) should build n copies of T glued along
    // free interface nodes, and projection : (n·T)* -> T.
    let (_n_copies, projection, _incls) = compute_n_copies(t, n, None)?;

    // Pushout complement:
    //
    //     T  <───────  (n·T)*
    //     │               │
    //     ▼       ⌟       ▼
    //     G  <───────    Ĝ_T
    //
    let pc = compute_pushout_complement(&projection, &incl)?;

    Ok(pc.complement)
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
        let (result, _, _) = compute_n_copies(&t, n, None).unwrap();
        
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
        let (result, _, _) = compute_n_copies(&t, n, None).unwrap();
        
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
    // T: n_in --e--> n_out
    let mut t = BHyp::new();
    let n_in = t.add_node();
    let n_out = t.add_node();

    t.add_edge(
        vec![SourceWithBinding {
            source: n_in,
            bound: vec![],
        }],
        vec![n_out],
        Some(Label::Symbol("e".to_string())),
    )
    .unwrap();

    // G contains T, and t_out has out-degree 3.
    //
    //       e
    // t_in ---> t_out
    //             | f1
    //             v
    //             x1
    //             | f2 etc...
    //
    let mut g = BHyp::new();
    let g_t_in = g.add_node();
    let g_t_out = g.add_node();

    let x1 = g.add_node();
    let x2 = g.add_node();
    let x3 = g.add_node();

    g.add_edge(
        vec![SourceWithBinding {
            source: g_t_in,
            bound: vec![],
        }],
        vec![g_t_out],
        Some(Label::Symbol("e".to_string())),
    )
    .unwrap();

    g.add_edge(
        vec![SourceWithBinding {
            source: g_t_out,
            bound: vec![],
        }],
        vec![x1],
        Some(Label::Symbol("f1".to_string())),
    )
    .unwrap();

    g.add_edge(
        vec![SourceWithBinding {
            source: g_t_out,
            bound: vec![],
        }],
        vec![x2],
        Some(Label::Symbol("f2".to_string())),
    )
    .unwrap();

    g.add_edge(
        vec![SourceWithBinding {
            source: g_t_out,
            bound: vec![],
        }],
        vec![x3],
        Some(Label::Symbol("f3".to_string())),
    )
    .unwrap();

    // K is the one-node graph selecting the node to be copied.
    let mut k = BHyp::new();
    let k_selected = k.add_node();

    // K -> G selects g_t_out.
    let k_to_g = BHypMorphism::new(
        k.clone(),
        g.clone(),
        [(k_selected, g_t_out)].into_iter().collect(),
        HashMap::new(),
    )
    .unwrap();

    // K -> T selects n_out.
    let k_to_t = BHypMorphism::new(
        k.clone(),
        t.clone(),
        [(k_selected, n_out)].into_iter().collect(),
        HashMap::new(),
    )
    .unwrap();

    // IMPORTANT:
    //
    // Span convention is:
    //
    //     left <- middle -> right
    //
    // Here:
    //
    //     G <- K -> T
    //
    let shared_node = Span {
        left: g.clone(),
        middle: k,
        right: t.clone(),
        to_l: k_to_g,
        to_r: k_to_t,
    };

    // Sanity check: the selected G node has out-degree 3.
    let k_node = shared_node.middle.nodes().iter().next().copied().unwrap();
    let selected_g_node = shared_node.to_l.map_node(k_node).unwrap();
    let n = g.out_degree(selected_g_node);

    assert_eq!(selected_g_node, g_t_out);
    assert_eq!(n, 3);

    let result = copy_subhypergraph(&g, &t, shared_node).unwrap();
    

    // Expected:
    //
    // t_in is shared.
    // t_out is copied into y1, y2, y3.
    // Each y_i gets one outgoing f_i edge.
    //
    // Nodes:
    //   t_in, x1, x2, x3, y1, y2, y3 = 7
    //
    // Edges:
    //   three e edges + f1 + f2 + f3 = 6
    assert_eq!(result.nodes().len(), 7);
    assert_eq!(result.edges().len(), 6);

    let mut exp = BHyp::new();

    let exp_t_in = exp.add_node();

    let exp_x1 = exp.add_node();
    let exp_x2 = exp.add_node();
    let exp_x3 = exp.add_node();

    let y1 = exp.add_node();
    let y2 = exp.add_node();
    let y3 = exp.add_node();

    exp.add_edge(
        vec![SourceWithBinding {
            source: exp_t_in,
            bound: vec![],
        }],
        vec![y1],
        Some(Label::Symbol("e".to_string())),
    )
    .unwrap();

    exp.add_edge(
        vec![SourceWithBinding {
            source: exp_t_in,
            bound: vec![],
        }],
        vec![y2],
        Some(Label::Symbol("e".to_string())),
    )
    .unwrap();

    exp.add_edge(
        vec![SourceWithBinding {
            source: exp_t_in,
            bound: vec![],
        }],
        vec![y3],
        Some(Label::Symbol("e".to_string())),
    )
    .unwrap();

    exp.add_edge(
        vec![SourceWithBinding {
            source: y1,
            bound: vec![],
        }],
        vec![exp_x1],
        Some(Label::Symbol("f1".to_string())),
    )
    .unwrap();

    exp.add_edge(
        vec![SourceWithBinding {
            source: y2,
            bound: vec![],
        }],
        vec![exp_x2],
        Some(Label::Symbol("f2".to_string())),
    )
    .unwrap();

    exp.add_edge(
        vec![SourceWithBinding {
            source: y3,
            bound: vec![],
        }],
        vec![exp_x3],
        Some(Label::Symbol("f3".to_string())),
    )
    .unwrap();

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
    let inclusions = find_all_occurrences(h, g);

    let n = inclusions.len();
    if n == 0 {
         return Err(GlueError::InvalidSubhypergraph("Not a subhypergraph!".to_string()));
    }

    // todo add optionsl interface parameter
    // build projection n H -> H
    let (nH, proj, _) = compute_n_copies(h, n, None).unwrap();
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