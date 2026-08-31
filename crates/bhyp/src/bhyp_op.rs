// // copying, glueing, etc

// //- Copying: duplicates a shared sub-hypergraph
// // - Glueing: merges multiple inclusions of a sub-hypergraph (inverse of copying)

// use std::collections::{HashMap, HashSet};

// use crate::bhyp::{BHyp, BHyp_with_interface, EdgeId, Label, NodeId, SourceWithBinding};
// use crate::categorical::{
//     compute_pushout, compute_pullback, compute_pushout_complement,
//     BHypMorphism, CategoricalError, MorphismError, PushoutResult,
// };

// /// Errors specific to copying and glueing operations
// #[derive(Debug, Clone, PartialEq, Eq)]
// pub enum CopyGlueError {
//     /// The vertex doesn't have enough out-degree for copying
//     InsufficientOutDegree { node: NodeId, required: usize, actual: usize },
//     /// The sub-hypergraph doesn't satisfy safe copying conditions
//     UnsafeCopyingCondition(String),
//     /// The node is not in the output interface of the sub-hypergraph
//     NodeNotInOutput(NodeId),
//     /// The sub-hypergraph is not valid
//     InvalidSubhypergraph(String),
//     /// Categorical construction failed
//     CategoricalError(CategoricalError),
//     /// Morphism error
//     MorphismError(MorphismError),
//     /// Glueing requires at least 2 inclusions
//     InsufficientInclusions,
//     /// Inclusions are not compatible
//     IncompatibleInclusions(String),
// }

// impl From<CategoricalError> for CopyGlueError {
//     fn from(e: CategoricalError) -> Self {
//         CopyGlueError::CategoricalError(e)
//     }
// }

// impl From<MorphismError> for CopyGlueError {
//     fn from(e: MorphismError) -> Self {
//         CopyGlueError::MorphismError(e)
//     }
// }

// impl std::fmt::Display for CopyGlueError {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match self {
//             CopyGlueError::InsufficientOutDegree { node, required, actual } => {
//                 write!(f, "Node {:?} has out-degree {} but {} required", node, actual, required)
//             }
//             CopyGlueError::UnsafeCopyingCondition(s) => {
//                 write!(f, "Unsafe copying condition: {}", s)
//             }
//             CopyGlueError::NodeNotInOutput(n) => {
//                 write!(f, "Node {:?} not in output interface of sub-hypergraph", n)
//             }
//             CopyGlueError::InvalidSubhypergraph(s) => {
//                 write!(f, "Invalid sub-hypergraph: {}", s)
//             }
//             CopyGlueError::CategoricalError(e) => write!(f, "Categorical error: {}", e),
//             CopyGlueError::MorphismError(e) => write!(f, "Morphism error: {}", e),
//             CopyGlueError::InsufficientInclusions => {
//                 write!(f, "Glueing requires at least 2 inclusions")
//             }
//             CopyGlueError::IncompatibleInclusions(s) => {
//                 write!(f, "Incompatible inclusions: {}", s)
//             }
//         }
//     }
// }

// /// Result of a copying operation
// #[derive(Debug, Clone)]
// pub struct CopyResult {
//     /// The resulting hypergraph with copied sub-hypergraph
//     pub result: BHyp,
//     /// Morphism from n copies of T to the result
//     pub copies_morphism: BHypMorphism,
//     /// The number of copies created
//     pub num_copies: usize,
// }

// /// Result of a glueing operation  
// #[derive(Debug, Clone)]
// pub struct GlueResult {
//     /// The resulting hypergraph with glued sub-hypergraph
//     pub result: BHyp,
//     /// Morphism from the single H to the result
//     pub glued_morphism: BHypMorphism,
// }

// /// Represents a sub-hypergraph T of G with its inclusion morphism
// #[derive(Debug, Clone)]
// pub struct Subhypergraph {
//     /// The sub-hypergraph
//     pub subgraph: BHyp,
//     /// Inclusion morphism T -> G
//     pub inclusion: BHypMorphism,
//     /// Output interface nodes (in T's node space)
//     pub output_nodes: HashSet<NodeId>,
//     /// Input interface nodes (in T's node space)  
//     pub input_nodes: HashSet<NodeId>,
// }

// impl Subhypergraph {
//     /// Create a subhypergraph from a set of edges in G
//     pub fn from_edges(g: &BHyp, edges: &HashSet<EdgeId>) -> Result<Self, CopyGlueError> {
//         let mut subgraph = BHyp::new();
//         let mut g_to_t_nodes: HashMap<NodeId, NodeId> = HashMap::new();
//         let mut g_to_t_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
        
//         // Collect all nodes incident to the edges
//         let mut incident_nodes: HashSet<NodeId> = HashSet::new();
//         for &e in edges {
//             if let Some(swbs) = g.get_sources_with_binding(e) {
//                 for swb in swbs {
//                     incident_nodes.insert(swb.source);
//                     for &b in &swb.bound {
//                         incident_nodes.insert(b);
//                     }
//                 }
//             }
//             if let Some(targets) = g.get_targets(e) {
//                 for &t in targets {
//                     incident_nodes.insert(t);
//                 }
//             }
//         }
        
//         // Create nodes in subgraph
//         let mut sorted_nodes: Vec<_> = incident_nodes.iter().copied().collect();
//         sorted_nodes.sort();
//         for g_n in sorted_nodes {
//             let t_n = subgraph.add_node();
//             g_to_t_nodes.insert(g_n, t_n);
//         }
        
//         // Create edges in subgraph
//         let mut sorted_edges: Vec<_> = edges.iter().copied().collect();
//         sorted_edges.sort();
//         for g_e in sorted_edges {
//             let swbs = g.get_sources_with_binding(g_e).unwrap();
//             let targets = g.get_targets(g_e).unwrap();
//             let label = g.get_label(g_e).cloned();
            
//             let new_swbs: Vec<SourceWithBinding> = swbs.iter().map(|swb| {
//                 SourceWithBinding {
//                     source: g_to_t_nodes[&swb.source],
//                     bound: swb.bound.iter().map(|&b| g_to_t_nodes[&b]).collect(),
//                 }
//             }).collect();
            
//             let new_targets: Vec<NodeId> = targets.iter()
//                 .map(|&t| g_to_t_nodes[&t])
//                 .collect();
            
//             let t_e = subgraph.add_edge(new_swbs, new_targets, label)
//                 .map_err(|s| CopyGlueError::InvalidSubhypergraph(s))?;
//             g_to_t_edges.insert(g_e, t_e);
//         }
        
//         // Compute interface nodes
//         let mut output_nodes = HashSet::new();
//         let mut input_nodes = HashSet::new();
        
//         for (&g_n, &t_n) in &g_to_t_nodes {
//             // Output: nodes with no outgoing edges within T
//             let has_outgoing_in_t = subgraph.out_degree(t_n) > 0;
//             if !has_outgoing_in_t {
//                 output_nodes.insert(t_n);
//             }
            
//             // Input: nodes with no incoming edges within T and not bound
//             let has_incoming_in_t = subgraph.in_degree(t_n) > 0;
//             let is_bound_in_t = subgraph.in_binding_degree(t_n) > 0;
//             if !has_incoming_in_t && !is_bound_in_t {
//                 input_nodes.insert(t_n);
//             }
//         }
        
//         // Build inclusion morphism T -> G
//         let t_to_g_nodes: HashMap<NodeId, NodeId> = g_to_t_nodes.iter()
//             .map(|(&g_n, &t_n)| (t_n, g_n))
//             .collect();
//         let t_to_g_edges: HashMap<EdgeId, EdgeId> = g_to_t_edges.iter()
//             .map(|(&g_e, &t_e)| (t_e, g_e))
//             .collect();
        
//         let inclusion = BHypMorphism::new(
//             subgraph.clone(),
//             g.clone(),
//             t_to_g_nodes,
//             t_to_g_edges,
//         )?;
        
//         Ok(Subhypergraph {
//             subgraph,
//             inclusion,
//             output_nodes,
//             input_nodes,
//         })
//     }
    
//     /// Create a subhypergraph containing a single node (discrete)
//     pub fn discrete_node(g: &BHyp, node: NodeId) -> Result<Self, CopyGlueError> {
//         if !g.nodes().contains(&node) {
//             return Err(CopyGlueError::InvalidSubhypergraph(
//                 format!("Node {:?} not in graph", node)
//             ));
//         }
        
//         let mut subgraph = BHyp::new();
//         let t_n = subgraph.add_node();
        
//         let inclusion = BHypMorphism::new(
//             subgraph.clone(),
//             g.clone(),
//             [(t_n, node)].into_iter().collect(),
//             HashMap::new(),
//         )?;
        
//         Ok(Subhypergraph {
//             subgraph,
//             inclusion,
//             output_nodes: [t_n].into_iter().collect(),
//             input_nodes: [t_n].into_iter().collect(),
//         })
//     }
// }

// // ============================================================================
// // Safe Copying Conditions (Definition 3.11)
// // ============================================================================

// /// Check the safe copying conditions from Definition 3.11
// /// 
// /// For G ∈ sbHyp, v ∈ G such that out(v) ≥ 2, T is a sub-hypergraph such that:
// /// 1. ∀e ∈ T, e' ∈ G^i_e : e' ∈ T 
// ///    (if T contains an edge with a body, the entire body must be in T)
// /// 2. ∀e' ∈ T, e' ∈ G^i_e, ∃e1 ∈ T, e1 ∉ G^i_e : e ∈ T
// ///    (when copying part of a body with edges outside, must copy the carrier edge)
// pub fn check_safe_copying_conditions(
//     g: &BHyp,
//     t: &Subhypergraph,
//     shared_node: NodeId,
// ) -> Result<(), CopyGlueError> {
//     // Check that shared_node is in T's output interface
//     let g_node = t.inclusion.map_node(
//         *t.output_nodes.iter().find(|&&n| {
//             t.inclusion.map_node(n) == Some(shared_node)
//         }).ok_or(CopyGlueError::NodeNotInOutput(shared_node))?
//     ).unwrap();
    
//     if g_node != shared_node {
//         return Err(CopyGlueError::NodeNotInOutput(shared_node));
//     }
    
//     // Check out-degree condition
//     let out_deg = g.out_degree(shared_node);
//     if out_deg < 2 {
//         return Err(CopyGlueError::InsufficientOutDegree {
//             node: shared_node,
//             required: 2,
//             actual: out_deg,
//         });
//     }
    
//     // Get edges in T (in G's edge space)
//     let t_edges_in_g: HashSet<EdgeId> = t.inclusion.edge_image();
    
//     // Condition 1: If T contains an edge e with a body, the body edges must be in T
//     for &t_e in t.subgraph.edges() {
//         let g_e = t.inclusion.map_edge(t_e).unwrap();
        
//         // Check each source that might have a body
//         if let Some(swbs) = g.get_sources_with_binding(g_e) {
//             for (i, swb) in swbs.iter().enumerate() {
//                 if !swb.bound.is_empty() {
//                     // This source has binding, compute its body
//                     if let Some(body_edges) = g.compute_body_edges(g_e, i) {
//                         for &body_e in &body_edges {
//                             if !t_edges_in_g.contains(&body_e) {
//                                 return Err(CopyGlueError::UnsafeCopyingCondition(
//                                     format!(
//                                         "Edge {:?} in T has body containing edge {:?} not in T",
//                                         g_e, body_e
//                                     )
//                                 ));
//                             }
//                         }
//                     }
//                 }
//             }
//         }
//     }
    
//     // Condition 2: If T contains edge e' that's in some body G^i_e, and T contains
//     // edges outside that body, then the carrier edge e must also be in T
//     for &t_e in t.subgraph.edges() {
//         let g_e_prime = t.inclusion.map_edge(t_e).unwrap();
        
//         // Check if g_e_prime is in any body
//         for &carrier_e in g.edges() {
//             if let Some(swbs) = g.get_sources_with_binding(carrier_e) {
//                 for (i, swb) in swbs.iter().enumerate() {
//                     if !swb.bound.is_empty() {
//                         if let Some(body_edges) = g.compute_body_edges(carrier_e, i) {
//                             if body_edges.contains(&g_e_prime) {
//                                 // g_e_prime is in the body of carrier_e at source i
//                                 // Check if T has edges outside this body
//                                 let has_edge_outside = t_edges_in_g.iter()
//                                     .any(|&e| !body_edges.contains(&e) && e != carrier_e);
                                
//                                 if has_edge_outside && !t_edges_in_g.contains(&carrier_e) {
//                                     return Err(CopyGlueError::UnsafeCopyingCondition(
//                                         format!(
//                                             "T contains edge {:?} in body of {:?}, and edges outside, but not the carrier",
//                                             g_e_prime, carrier_e
//                                         )
//                                     ));
//                                 }
//                             }
//                         }
//                     }
//                 }
//             }
//         }
//     }
    
//     Ok(())
// }

// // ============================================================================
// // Copying (Definition 3.12)
// // ============================================================================

// /// Create n copies of a sub-hypergraph T, sharing free vertices
// /// 
// /// This creates (n·T)* which is n copies of T glued along their free vertices (input interface).
// fn create_n_copies_shared(
//     t: &Subhypergraph,
//     n: usize,
// ) -> Result<(BHyp, Vec<BHypMorphism>), CopyGlueError> {
//     if n == 0 {
//         return Err(CopyGlueError::InvalidSubhypergraph("Cannot create 0 copies".to_string()));
//     }
    
//     if n == 1 {
//         let id_nodes: HashMap<NodeId, NodeId> = t.subgraph.nodes().iter()
//             .map(|&n| (n, n)).collect();
//         let id_edges: HashMap<EdgeId, EdgeId> = t.subgraph.edges().iter()
//             .map(|&e| (e, e)).collect();
//         let morphism = BHypMorphism::new(
//             t.subgraph.clone(),
//             t.subgraph.clone(),
//             id_nodes,
//             id_edges,
//         )?;
//         return Ok((t.subgraph.clone(), vec![morphism]));
//     }
    
//     // Start with first copy
//     let mut result = t.subgraph.clone();
//     let mut morphisms: Vec<BHypMorphism> = Vec::new();
    
//     // First morphism is identity
//     let first_nodes: HashMap<NodeId, NodeId> = t.subgraph.nodes().iter()
//         .map(|&n| (n, n)).collect();
//     let first_edges: HashMap<EdgeId, EdgeId> = t.subgraph.edges().iter()
//         .map(|&e| (e, e)).collect();
//     morphisms.push(BHypMorphism::new(
//         t.subgraph.clone(),
//         result.clone(),
//         first_nodes,
//         first_edges,
//     )?);
    
//     // For copies 2..n, use pushout to glue along input interface
//     for _copy_idx in 1..n {
//         // Create discrete input interface
//         let mut input_interface = BHyp::new();
//         let mut interface_to_t: HashMap<NodeId, NodeId> = HashMap::new();
//         let mut interface_to_result: HashMap<NodeId, NodeId> = HashMap::new();
        
//         // The input nodes are shared
//         for &t_input in &t.input_nodes {
//             let iface_n = input_interface.add_node();
//             interface_to_t.insert(iface_n, t_input);
//             // Map to the corresponding node in result (via first morphism)
//             interface_to_result.insert(iface_n, morphisms[0].map_node(t_input).unwrap());
//         }
        
//         // Morphism from interface to T (new copy)
//         let iface_to_t = BHypMorphism::new(
//             input_interface.clone(),
//             t.subgraph.clone(),
//             interface_to_t.clone(),
//             HashMap::new(),
//         )?;
        
//         // Morphism from interface to current result
//         let iface_to_result = BHypMorphism::new(
//             input_interface.clone(),
//             result.clone(),
//             interface_to_result,
//             HashMap::new(),
//         )?;
        
//         // Compute pushout to glue the new copy
//         let pushout = compute_pushout(&iface_to_result, &iface_to_t)?;
        
//         // Update result
//         let old_result = result;
//         result = pushout.pushout;
        
//         // Update existing morphisms to go through the new pushout
//         for morph in &mut morphisms {
//             let new_nodes: HashMap<NodeId, NodeId> = morph.on_nodes().iter()
//                 .map(|(&t_n, &old_r_n)| {
//                     (t_n, pushout.morphism_from_b.map_node(old_r_n).unwrap())
//                 })
//                 .collect();
//             let new_edges: HashMap<EdgeId, EdgeId> = morph.on_edges().iter()
//                 .map(|(&t_e, &old_r_e)| {
//                     (t_e, pushout.morphism_from_b.map_edge(old_r_e).unwrap())
//                 })
//                 .collect();
//             *morph = BHypMorphism::new(
//                 t.subgraph.clone(),
//                 result.clone(),
//                 new_nodes,
//                 new_edges,
//             )?;
//         }
        
//         // Add morphism for the new copy
//         let new_copy_nodes: HashMap<NodeId, NodeId> = t.subgraph.nodes().iter()
//             .map(|&t_n| (t_n, pushout.morphism_from_c.map_node(t_n).unwrap()))
//             .collect();
//         let new_copy_edges: HashMap<EdgeId, EdgeId> = t.subgraph.edges().iter()
//             .map(|&t_e| (t_e, pushout.morphism_from_c.map_edge(t_e).unwrap()))
//             .collect();
//         morphisms.push(BHypMorphism::new(
//             t.subgraph.clone(),
//             result.clone(),
//             new_copy_nodes,
//             new_copy_edges,
//         )?);
//     }
    
//     Ok((result, morphisms))
// }

// /// Perform copying of a shared sub-hypergraph (Definition 3.12)
// ///
// /// Given G ∈ sbHyp, v ∈ G with out(v) ≥ 2, and T a safe sub-hypergraph with v ∈ O_T,
// /// define Ĝ_T (G with copied T) as a pushout complement:
// ///
// /// ```text
// ///     T ←─────── (n·T)*
// ///     │            │
// ///     ▼     ⌟      ▼
// ///     G ←─────── Ĝ_T
// /// ```
// ///
// /// where n = out(v) and (n·T)* is n copies of T sharing free vertices.
// pub fn copy_subhypergraph(
//     g: &BHyp,
//     t: &Subhypergraph,
//     shared_node: NodeId,
// ) -> Result<CopyResult, CopyGlueError> {
//     // Check safe copying conditions
//     check_safe_copying_conditions(g, t, shared_node)?;
    
//     let n = g.out_degree(shared_node);
    
//     // Create (n·T)* - n copies sharing free vertices
//     let (n_copies, copy_morphisms) = create_n_copies_shared(t, n)?;
    
//     // Build morphism from (n·T)* to G
//     // Each copy maps to G via the inclusion, but we need to handle the sharing
//     let n_copies_to_g_nodes: HashMap<NodeId, NodeId> = HashMap::new();
//     let n_copies_to_g_edges: HashMap<NodeId, EdgeId> = HashMap::new();
    
//     // For the shared output node (shared_node), all copies map to the same G node
//     // For non-shared nodes, we need to track which copy goes where
    
//     // This is complex because we need to find n distinct occurrences of T in G
//     // For now, implement a simpler version that works when T is clearly identifiable
    
//     // Find all edges that use shared_node as a source
//     let mut using_edges: Vec<EdgeId> = Vec::new();
//     for &e in g.edges() {
//         if let Some(swbs) = g.get_sources_with_binding(e) {
//             if swbs.iter().any(|swb| swb.source == shared_node) {
//                 using_edges.push(e);
//             }
//         }
//     }
    
//     if using_edges.len() < n {
//         return Err(CopyGlueError::InvalidSubhypergraph(
//             format!("Expected {} uses of shared node but found {}", n, using_edges.len())
//         ));
//     }
    
//     // Build the result using pushout complement
//     // We compute: G_T = G ⊔_T (n·T)*
//     // This is pushout of: T → G and T → (n·T)* (diagonal inclusion into first copy)
    
//     // Morphism T → (n·T)* (first copy embedding)
//     let t_to_n_copies = copy_morphisms[0].clone();
    
//     // Use pushout to get result
//     let pushout_result = compute_pushout(&t.inclusion, &t_to_n_copies)?;
    
//     // Build the morphism from n·T* to result
//     let copies_to_result_nodes: HashMap<NodeId, NodeId> = n_copies.nodes().iter()
//         .map(|&nc_n| (nc_n, pushout_result.morphism_from_c.map_node(nc_n).unwrap()))
//         .collect();
//     let copies_to_result_edges: HashMap<EdgeId, EdgeId> = n_copies.edges().iter()
//         .map(|&nc_e| (nc_e, pushout_result.morphism_from_c.map_edge(nc_e).unwrap()))
//         .collect();
    
//     let copies_morphism = BHypMorphism::new(
//         n_copies,
//         pushout_result.pushout.clone(),
//         copies_to_result_nodes,
//         copies_to_result_edges,
//     )?;
    
//     Ok(CopyResult {
//         result: pushout_result.pushout,
//         copies_morphism,
//         num_copies: n,
//     })
// }

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