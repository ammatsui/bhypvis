// Metaedge extraction constructions and substitution for hypergraphs with binding
// copying and glueing shared subhypergraphs (Definition 3.12, 3.15)

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::bhyp::{BHyp, BHyp_with_interface, EdgeId, Label, NodeId, SourceWithBinding};
use crate::categorical::{
    BHypMorphism, CategoricalError, Span, 
    are_isomorphic, find_all_occurrences,
    compute_coproduct, compute_pushout, compute_pushout_complement, dpo
};
use crate::copy::{compute_n_copies, compute_n_copies_with_interface};
// use crate::safety::{is_safe};

/// Error types for substitution operations
#[derive(Debug, Clone)]
pub enum SubstitutionError {
    MetavariableNotFound(String),
    ArityMismatch { expected: usize, got: usize },
    InterfaceMismatch(String),
    PushoutComplementFailed(CategoricalError),
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

impl From<CategoricalError> for SubstitutionError {
    fn from(e: CategoricalError) -> Self {
        SubstitutionError::PushoutComplementFailed(e)
    }
}

// ============================================================================
// Construction B.2: Interface of a Metaedge (I_M)
// ============================================================================

// / The interface I_M of a metaedge M is a discrete hypergraph
// / with vertices corresponding to sources and targets of M
pub fn construct_meta_hypergraph(label: Label) -> Result<BHyp, String> {
    // 1. Extract the name and arity, ensuring it's actually a metavariable
    let (name, arity) = match &label {
        Label::Meta(name, arity) => (name.clone(), *arity),
        Label::Symbol(_) => return Err("Expected a Meta label, but got a Symbol".to_string()),
    };

    let mut graph = BHyp::new();

    // 2. Create the source nodes based on the arity
    let mut sources = Vec::with_capacity(arity);
    for _ in 0..arity {
        let node = graph.add_node();
        sources.push(SourceWithBinding {
            source: node,
            bound: vec![], // Metavariables typically do not bind variables internally
        });
    }

    // 3. Create a single target node representing the output of the metavariable
    let target = graph.add_node();

    // 4. Add the edge to the hypergraph
    graph.add_edge(
        sources, 
        vec![target], 
        Some(label)
    )?;

    Ok(graph)
}


// // ============================================================================
// // Substitution Data (Definition 3.10)
// // ============================================================================

// /// A substitution θ: M ↦ T
// /// Given by map f: I_M -> I_T + O_T and span I_G <- K -> I_{F_T}
#[derive(Debug, Clone)]
pub struct Substitution {
    /// Metavariable name
    pub meta_name: Label,
    /// Replacement hypergraph T with interface
    pub replacement: BHyp_with_interface,
    /// Map f: I_M -> I_T + O_T (source index -> replacement interface node)
    pub interface_map: HashMap<NodeId, NodeId>,
}

impl Substitution {
    pub fn new(meta_name: Label, replacement: BHyp_with_interface) -> Self {
        Substitution {
            meta_name,
            replacement,
            interface_map: HashMap::new(),
        }
    }
    
    /// Set interface mapping (which T nodes correspond to M's sources/targets)
    pub fn with_interface_map(mut self, map: HashMap<NodeId, NodeId>) -> Self {
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


// ============================================================================
// Main Substitution Algorithm (Definition 3.10)
// ============================================================================

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
    shared: &Span, // I_G <- K -> I_T
) -> Result<BHyp_with_interface, SubstitutionError> {
    
    // 1. Find all occurrences of M in G
    let met = construct_meta_hypergraph(subst.meta_name.clone())
        .map_err(|e| SubstitutionError::InvalidConstruction(e))?;
    
    let occurrences = find_all_occurrences(&met, &g.bhyp());
    let n = occurrences.len();
    
    if n == 0 {
        return Ok(g.clone());
    }
    
    let mut i_m = BHyp_with_interface::from_bhyp(met.clone());
    
    // 2. Build n copies of M 
    let empty_k = BHyp::new();
    let empty_morphism = BHypMorphism::new(
        empty_k.clone(),
        met.clone(),
        HashMap::new(), 
        HashMap::new(),
    ).map_err(|e| SubstitutionError::InvalidConstruction(e.to_string()))?;

    let (mut n_m, proj) = compute_n_copies_with_interface(
        &i_m, 
        n, 
        Some((empty_k, empty_morphism))
    ).map_err(|e| SubstitutionError::InvalidConstruction(format!("{:?}", e)))?;

    // 3. Compute n T, glued at I_T \ im interface_map(I_M)
    let t_interface_nodes = subst.replacement.combined_interface_nodes();
    let m_image_in_t: HashSet<NodeId> = subst.interface_map.values().cloned().collect();

    let mut i_f = BHyp::new();
    let mut i_f_map_nodes = HashMap::new();

    // Filter: Keep interface nodes of T that are NOT in the image from M
    for &node in &t_interface_nodes {
        if !m_image_in_t.contains(&node) {
            let i_f_node = i_f.add_node();
            i_f_map_nodes.insert(i_f_node, node);
        }
    }

    let kt_to_t = BHypMorphism::new(
        i_f.clone(),
        subst.replacement.bhyp().clone(),
        i_f_map_nodes,
        HashMap::new(), 
    ).map_err(|e| SubstitutionError::InvalidConstruction(e.to_string()))?;

    let (n_t_glued, t_proj) = compute_n_copies_with_interface(
        &subst.replacement,
        n,
        Some((i_f, kt_to_t))
    ).map_err(|e| SubstitutionError::InvalidConstruction(format!("{:?}", e)))?;
        
    // 4. Compute the objects for the top span n M + K <- n Im + K -> n T 
    // n·I_M 
    let nim_result = compute_coproduct(n_m.input_interface(), n_m.output_interface())
        .map_err(|e| SubstitutionError::InvalidConstruction(format!("{:?}", e)))?;
    let nim_graph = &nim_result.pushout;

    // n·M ⊔ K
    let nm_k_result = compute_coproduct(n_m.bhyp(), &shared.middle)
        .map_err(|e| SubstitutionError::InvalidConstruction(format!("{:?}", e)))?;
    let nm_k = &nm_k_result.pushout;

    // n·I_M ⊔ K
    let nim_k_result = compute_coproduct(nim_graph, &shared.middle)
        .map_err(|e| SubstitutionError::InvalidConstruction(format!("{:?}", e)))?;
    let nim_k = &nim_k_result.pushout;

    // 5. Construct `to_l`: (n·I_M ⊔ K) -> (n·M ⊔ K)
    let mut to_l_nodes = HashMap::new();
    
    for (&nim_n, &nim_k_n) in nim_k_result.morphism_from_b.on_nodes() {
        let nm_n = if let Some((&in_n, _)) = nim_result.morphism_from_b.on_nodes().iter().find(|(_, &v)| v == nim_n) {
            n_m.input_map()[&in_n]
        } else if let Some((&out_n, _)) = nim_result.morphism_from_c.on_nodes().iter().find(|(_, &v)| v == nim_n) {
            n_m.output_map()[&out_n]
        } else {
            unreachable!()
        };
        let final_nm_k_n = nm_k_result.morphism_from_b.map_node(nm_n).unwrap();
        to_l_nodes.insert(nim_k_n, final_nm_k_n);
    }
    
    for (&k_n, &nim_k_n) in nim_k_result.morphism_from_c.on_nodes() {
        let final_nm_k_n = nm_k_result.morphism_from_c.map_node(k_n).unwrap();
        to_l_nodes.insert(nim_k_n, final_nm_k_n);
    }

    let to_l_morph = BHypMorphism::new(nim_k.clone(), nm_k.clone(), to_l_nodes, HashMap::new())
        .map_err(|e| SubstitutionError::InvalidConstruction(e.to_string()))?;

    // 6. Construct `to_r`: (n·I_M ⊔ K) -> n·T̂
    let mut to_r_nodes = HashMap::new();

    // find inclusions t into n T
    let t_incl = find_all_occurrences(&subst.replacement.bhyp(), &n_t_glued.bhyp());
    
    for (i, m_inj) in occurrences.iter().enumerate() {
        let t_inj = &t_incl[i];
        for &m_n in m_inj.domain().nodes() {
            if let Some(&t_target_n) = subst.interface_map.get(&m_n.0) {
                let nm_n = m_inj.map_node(m_n).unwrap();
                let nim_n_opt = nim_result.morphism_from_b.on_nodes().iter().find_map(|(&in_n, &nim_n)| {
                    if n_m.input_map()[&in_n] == nm_n { Some(nim_n) } else { None }
                }).or_else(|| {
                    nim_result.morphism_from_c.on_nodes().iter().find_map(|(&out_n, &nim_n)| {
                        if n_m.output_map()[&out_n] == nm_n { Some(nim_n) } else { None }
                    })
                });

                if let Some(nim_n) = nim_n_opt {
                    let nim_k_n = nim_k_result.morphism_from_b.map_node(nim_n).unwrap();
                    let nt_n = t_inj.map_node(t_target_n).unwrap();
                    to_r_nodes.insert(nim_k_n, nt_n);
                }
            }
        }
    }
    
    for (&k_n, &nim_k_n) in nim_k_result.morphism_from_c.on_nodes() {
        let nt_n = shared.to_r.map_node(k_n).unwrap();
        to_r_nodes.insert(nim_k_n, nt_n);
    }

    let to_r_morph = BHypMorphism::new(nim_k.clone(), n_t_glued.bhyp().clone(), to_r_nodes, HashMap::new())
        .map_err(|e| SubstitutionError::InvalidConstruction(e.to_string()))?;

    let top_span = Span {
        left: nm_k.clone(),
        middle: nim_k.clone(),
        right: n_t_glued.bhyp().clone(),
        to_l: to_l_morph,
        to_r: to_r_morph
    };

    // 7. Construct matching morphism: n·M ⊔ K -> G
    let mut match_nodes = HashMap::new();
    let mut match_edges = HashMap::new();

    for (&k_n, &nm_k_n) in nm_k_result.morphism_from_c.on_nodes() {
        match_nodes.insert(nm_k_n, shared.to_l.map_node(k_n).unwrap());
    }
    for (&k_e, &nm_k_e) in nm_k_result.morphism_from_c.on_edges() {
        match_edges.insert(nm_k_e, shared.to_l.map_edge(k_e).unwrap());
    }

    for (i, occ) in occurrences.iter().enumerate() {
        let injection = &occurrences[i];
        for &m_n in injection.domain().nodes() {
            let nm_n = injection.map_node(m_n).unwrap();
            let nm_k_n = nm_k_result.morphism_from_b.map_node(nm_n).unwrap();
            match_nodes.insert(nm_k_n, occ.map_node(m_n).unwrap());
        }
        for &m_e in injection.domain().edges() {
            let nm_e = injection.map_edge(m_e).unwrap();
            let nm_k_e = nm_k_result.morphism_from_b.map_edge(nm_e).unwrap();
            match_edges.insert(nm_k_e, occ.map_edge(m_e).unwrap());
        }
    }

    let match_morphism = BHypMorphism::new(nm_k.clone(), g.bhyp().clone(), match_nodes, match_edges)
        .map_err(|e| SubstitutionError::InvalidConstruction(e.to_string()))?;

    // 8. Apply DPO
    let result_span = dpo(&top_span, g.bhyp(), &match_morphism)
        .map_err(|e| SubstitutionError::InvalidConstruction(format!("DPO Failed: {:?}", e)))?;

    Ok(BHyp_with_interface::from_bhyp(result_span.right))
}




#[cfg(test)]
mod subst_tests {
    use super::*;

    // ============================================================================
    // Tests for construct_meta_hypergraph
    // ============================================================================

    #[test]
    fn test_construct_meta_hypergraph_arity_0() {
        let label = Label::Meta("X".to_string(), 0);
        let result = construct_meta_hypergraph(label.clone()).unwrap();
        
        // Arity 0: 0 source nodes + 1 target node = 1 node total
        assert_eq!(result.nodes().len(), 1);
        assert_eq!(result.edges().len(), 1);
        
        // The single edge should have 0 sources and 1 target
        let edge_id = result.edges().iter().next().unwrap();
        assert_eq!(result.get_sources(*edge_id).unwrap().len(), 0);
        assert_eq!(result.get_targets(*edge_id).unwrap().len(), 1);
        assert_eq!(result.get_label(*edge_id), Some(&label));
    }

    #[test]
    fn test_construct_meta_hypergraph_arity_1() {
        let label = Label::Meta("Y".to_string(), 1);
        let result = construct_meta_hypergraph(label.clone()).unwrap();
        
        // Arity 1: 1 source node + 1 target node = 2 nodes
        assert_eq!(result.nodes().len(), 2);
        assert_eq!(result.edges().len(), 1);
        
        let edge_id = result.edges().iter().next().unwrap();
        assert_eq!(result.get_sources(*edge_id).unwrap().len(), 1);
        assert_eq!(result.get_targets(*edge_id).unwrap().len(), 1);
    }

    #[test]
    fn test_construct_meta_hypergraph_arity_3() {
        let label = Label::Meta("Z".to_string(), 3);
        let result = construct_meta_hypergraph(label).unwrap();
        
        // Arity 3: 3 source nodes + 1 target node = 4 nodes
        assert_eq!(result.nodes().len(), 4);
        assert_eq!(result.edges().len(), 1);
        
        let edge_id = result.edges().iter().next().unwrap();
        assert_eq!(result.get_sources(*edge_id).unwrap().len(), 3);
        assert_eq!(result.get_targets(*edge_id).unwrap().len(), 1);
    }

    #[test]
    fn test_construct_meta_hypergraph_symbol_fails() {
        let label = Label::Symbol("not_meta".to_string());
        let result = construct_meta_hypergraph(label);
        
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Expected a Meta label"));
    }

    #[test]
    fn test_construct_meta_hypergraph_nodes_are_distinct() {
        let label = Label::Meta("M".to_string(), 2);
        let result = construct_meta_hypergraph(label).unwrap();
        
        let nodes: Vec<_> = result.nodes().iter().collect();
        assert_eq!(nodes.len(), 3);
        
        // All nodes should be distinct
        let unique: HashSet<_> = nodes.iter().collect();
        assert_eq!(unique.len(), 3);
    }

    // ============================================================================
    // Tests for Substitution::free_vertices
    // ============================================================================

    #[test]
    fn test_free_vertices_all_mapped() {
        // T with interface, all mapped from I_M
        let mut t = BHyp::new();
        let n0 = t.add_node();
        let n1 = t.add_node();
        let n2 = t.add_node();
        
        let t_with_interface = BHyp_with_interface::from_bhyp(t.clone());
            
        
        let subst = Substitution {
            meta_name: Label::Meta("X".to_string(), 2),
            replacement: t_with_interface,
            interface_map: *t_with_interface.clone().input_map().clone(),
        };
        
        let free = subst.free_vertices();
        assert!(free.is_empty(), "All interface vertices are mapped, so no free vertices");
    }

    #[test]
    fn test_free_vertices_some_free() {
        let mut t = BHyp::new();
        let n0 = t.add_node();
        let n1 = t.add_node();
        let n2 = t.add_node();
        let n3 = t.add_node();
        
        // inputs: [n0, n1], outputs: [n2, n3]
        let t_with_interface = BHyp_with_interface::from_bhyp(t.clone());
        
        // Only map n0 and n2, leaving n1 and n3 free
        let mut interface_map = HashMap::new();
        interface_map.insert(0, n0);
        interface_map.insert(1, n2);
        
        let subst = Substitution {
            meta_name: Label::Meta("X".to_string(), 1),
            replacement: t_with_interface,
            interface_map: *t_with_interface.clone().input_map(),
        };
        
        let free = subst.free_vertices();
        assert_eq!(free.len(), 2);
        assert!(free.contains(&n1));
        assert!(free.contains(&n3));
    }

    #[test]
    fn test_free_vertices_none_mapped() {
        let mut t = BHyp::new();
        let n0 = t.add_node();
        let n1 = t.add_node();
        
        let t_with_interface = BHyp_with_interface::from_bhyp(
            t.clone());
        
        let subst = Substitution {
            meta_name: Label::Meta("X".to_string(), 0),
            replacement: t_with_interface,
            interface_map: HashMap::new(),
        };
        
        let free = subst.free_vertices();
        assert_eq!(free.len(), 2);
        assert!(free.contains(&n0));
        assert!(free.contains(&n1));
    }

    #[test]
    fn test_free_vertices_internal_nodes_not_counted() {
        // Internal nodes (not in interface) should not appear in free_vertices
        let mut t = BHyp::new();
        let n_in = t.add_node();
        let n_internal = t.add_node();  // Not in interface
        let n_out = t.add_node();
        
        // Add edge through internal node
        t.add_edge(
            vec![SourceWithBinding { source: n_in, bound: vec![] }],
            vec![n_internal],
            Some(Label::Symbol("f".to_string()))
        ).unwrap();
        t.add_edge(
            vec![SourceWithBinding { source: n_internal, bound: vec![] }],
            vec![n_out],
            Some(Label::Symbol("g".to_string()))
        ).unwrap();
        
        let t_with_interface = BHyp_with_interface::from_bhyp(t.clone());

        
        let subst = Substitution {
            meta_name: Label::Meta("X".to_string(), 1),
            replacement: t_with_interface,
            interface_map: HashMap::new(),
        };
        
        let free = subst.free_vertices();
        
        // Only interface nodes count, not internal
        assert_eq!(free.len(), 2);
        assert!(free.contains(&n_in));
        assert!(free.contains(&n_out));
        assert!(!free.contains(&n_internal));
    }

    // ============================================================================
    // Tests for apply_substitution - Basic Cases
    // ============================================================================

    #[test]
    fn test_apply_substitution_no_occurrences() {
        // G has no metaedge M, so substitution should return G unchanged
        let mut g = BHyp::new();
        let n0 = g.add_node();
        let n1 = g.add_node();
        g.add_edge(
            vec![SourceWithBinding { source: n0, bound: vec![] }],
            vec![n1],
            Some(Label::Symbol("f".to_string()))
        ).unwrap();
        
        let g_int = BHyp_with_interface::from_bhyp(g.clone());
        
        // Substitution for metavariable M (not in G)
        let mut t = BHyp::new();
        let t0 = t.add_node();
        let t1 = t.add_node();
        let t_int = BHyp_with_interface::from_bhyp(t.clone());
        
        let subst = Substitution {
            meta_name: Label::Meta("M".to_string(), 1),
            replacement: t_int,
            interface_map: HashMap::new(),
        };
        
        // Empty shared span
        let k = BHyp::new();
        let shared = Span {
            left: g.clone(),
            middle: k.clone(),
            right: subst.replacement.bhyp().clone(),
            to_l: BHypMorphism::new(k.clone(), g.clone(), HashMap::new(), HashMap::new()).unwrap(),
            to_r: BHypMorphism::new(k.clone(), subst.replacement.bhyp().clone(), HashMap::new(), HashMap::new()).unwrap(),
        };
        
        let result = apply_substitution(&g_int, &subst, &shared).unwrap();
        
        // Result should be isomorphic to G
        assert!(are_isomorphic(result.bhyp(), &g));
    }

    #[test]
    fn test_apply_substitution_single_occurrence_simple() {
        // G contains one metaedge M, replace with T
        let mut g = BHyp::new();
        let g_in = g.add_node();
        let g_out = g.add_node();
        let m_edge = g.add_edge(
            vec![SourceWithBinding { source: g_in, bound: vec![] }],
            vec![g_out],
            Some(Label::Meta("M".to_string(), 1))
        ).unwrap();
        
        let g_int = BHyp_with_interface::from_bhyp(g.clone());
        
        // Replacement T: single edge with label "T"
        let mut t = BHyp::new();
        let t_in = t.add_node();
        let t_out = t.add_node();
        t.add_edge(
            vec![SourceWithBinding { source: t_in, bound: vec![] }],
            vec![t_out],
            Some(Label::Symbol("T".to_string()))
        ).unwrap();
        
        let t_int = BHyp_with_interface::from_bhyp(t.clone());
        
        // Interface map: M's source -> T's input, M's target -> T's output
        let mut interface_map = HashMap::new();
        interface_map.insert(0, t_in);   // M source 0 -> T input
        interface_map.insert(1, t_out);  // M target -> T output
        
        let subst = Substitution {
            meta_name: Label::Meta("M".to_string(), 1),
            replacement: t_int.clone(),
            interface_map: *t_int.clone().input_map(),
        };
        
        // Empty shared span (no shared vertices)
        let k = BHyp::new();
        let shared = Span {
            left: g.clone(),
            middle: k.clone(),
            right: t.clone(),
            to_l: BHypMorphism::new(k.clone(), g.clone(), HashMap::new(), HashMap::new()).unwrap(),
            to_r: BHypMorphism::new(k.clone(), t.clone(), HashMap::new(), HashMap::new()).unwrap(),
        };
        
        let result = apply_substitution(&g_int, &subst, &shared).unwrap();
        
        // Result should have 2 nodes, 1 edge labeled "T"
        assert_eq!(result.bhyp().nodes().len(), 2);
        assert_eq!(result.bhyp().edges().len(), 1);
        
        let edge_id = result.bhyp().edges().iter().next().unwrap();
        assert_eq!(result.bhyp().get_label(*edge_id), Some(Label::Symbol("T".to_string())).as_ref());
    }

    #[test]
    fn test_apply_substitution_multiple_occurrences() {
        // G contains two metaedges M in parallel
        let mut g = BHyp::new();
        let g_in = g.add_node();
        let g_mid1 = g.add_node();
        let g_mid2 = g.add_node();
        let g_out = g.add_node();
        
        // Two M edges
        g.add_edge(
            vec![SourceWithBinding { source: g_in, bound: vec![] }],
            vec![g_mid1],
            Some(Label::Meta("M".to_string(), 1))
        ).unwrap();
        g.add_edge(
            vec![SourceWithBinding { source: g_in, bound: vec![] }],
            vec![g_mid2],
            Some(Label::Meta("M".to_string(), 1))
        ).unwrap();
        
        // Regular edge connecting to output
        g.add_edge(
            vec![
                SourceWithBinding { source: g_mid1, bound: vec![] },
                SourceWithBinding { source: g_mid2, bound: vec![] }
            ],
            vec![g_out],
            Some(Label::Symbol("join".to_string()))
        ).unwrap();
        
        let g_int = BHyp_with_interface::from_bhyp(g.clone());
    
        // Replacement T
        let mut t = BHyp::new();
        let t_in = t.add_node();
        let t_out = t.add_node();
        t.add_edge(
            vec![SourceWithBinding { source: t_in, bound: vec![] }],
            vec![t_out],
            Some(Label::Symbol("replaced".to_string()))
        ).unwrap();
        
        let t_int = BHyp_with_interface::from_bhyp(t.clone());
        
        let mut interface_map = HashMap::new();
        interface_map.insert(0, t_in);
        interface_map.insert(1, t_out);
        
        let subst = Substitution {
            meta_name: Label::Meta("M".to_string(), 1),
            replacement: t_int,
            interface_map: *t_int.clone().input_map(),
        };
        
        let k = BHyp::new();
        let shared = Span {
            left: g.clone(),
            middle: k.clone(),
            right: t.clone(),
            to_l: BHypMorphism::new(k.clone(), g.clone(), HashMap::new(), HashMap::new()).unwrap(),
            to_r: BHypMorphism::new(k.clone(), t.clone(), HashMap::new(), HashMap::new()).unwrap(),
        };
        
        let result = apply_substitution(&g_int, &subst, &shared).unwrap();
        
        // Should have replaced both M edges with "replaced" edges
        // Count edges with label "replaced"
        let replaced_count = result.bhyp().edges().iter()
            .filter(|&e| {
                result.bhyp().get_edge(e)
                    .map(|edge| edge.label == Some(Label::Symbol("replaced".to_string())))
                    .unwrap_or(false)
            })
            .len();
        
        assert_eq!(replaced_count, 2, "Both M edges should be replaced");
        
        // Should still have the "join" edge
        let join_count = result.bhyp().edges().iter()
            .filter(|&e| {
                result.bhyp().get_edge(*e)
                    .map(|edge| edge.label == Some(Label::Symbol("join".to_string())))
                    .unwrap_or(false)
            })
            .len();
        
        assert_eq!(join_count, 1, "Join edge should be preserved");
    }

    // ============================================================================
    // Tests for apply_substitution - Shared Vertices
    // ============================================================================

    #[test]
    fn test_apply_substitution_with_shared_vertex() {
        // G has metaedge M and another edge sharing a vertex
        let mut g = BHyp::new();
        let g_in = g.add_node();
        let g_shared = g.add_node();  // Shared between M and f
        let g_out = g.add_node();
        
        g.add_edge(
            vec![SourceWithBinding { source: g_in, bound: vec![] }],
            vec![g_shared],
            Some(Label::Meta("M".to_string(), 1))
        ).unwrap();
        g.add_edge(
            vec![SourceWithBinding { source: g_shared, bound: vec![] }],
            vec![g_out],
            Some(Label::Symbol("f".to_string()))
        ).unwrap();
        
        let g_int = BHyp_with_interface::from_bhyp(g.clone());
        
        // Replacement T
        let mut t = BHyp::new();
        let t_in = t.add_node();
        let t_out = t.add_node();
        t.add_edge(
            vec![SourceWithBinding { source: t_in, bound: vec![] }],
            vec![t_out],
            Some(Label::Symbol("T".to_string()))
        ).unwrap();
        
        let t_int = BHyp_with_interface::from_bhyp(t.clone());
        
        let mut interface_map = HashMap::new();
        interface_map.insert(0, t_in);
        interface_map.insert(1, t_out);
        
        let subst = Substitution {
            meta_name: Label::Meta("M".to_string(), 1),
            replacement: t_int,
            interface_map,
        };
        
        // Shared span: K contains the shared vertex
        let mut k = BHyp::new();
        let k_node = k.add_node();
        
        let shared = Span {
            left: g.clone(),
            middle: k.clone(),
            right: t.clone(),
            to_l: BHypMorphism::new(
                k.clone(), 
                g.clone(), 
                [(k_node, g_shared)].into_iter().collect(), 
                HashMap::new()
            ).unwrap(),
            to_r: BHypMorphism::new(
                k.clone(), 
                t.clone(), 
                [(k_node, t_out)].into_iter().collect(), 
                HashMap::new()
            ).unwrap(),
        };
        
        let result = apply_substitution(&g_int, &subst, &shared).unwrap();
        
        // Result should have T edge connected to f edge via shared vertex
        assert_eq!(result.bhyp().edges().len(), 2);
        
        // Verify connectivity: there should be a vertex with both in-degree and out-degree
        let has_connector = result.bhyp().nodes().any(|&n| {
            result.bhyp().in_degree(n) > 0 && result.bhyp().out_degree(n) > 0
        });
        assert!(has_connector, "Shared vertex should connect T to f");
    }

    // ============================================================================
    // Tests for apply_substitution - Free Vertices (Gluing)
    // ============================================================================

    #[test]
    fn test_apply_substitution_free_vertices_glued() {
        // G has two M edges, T has free vertices that should be glued
        let mut g = BHyp::new();
        let g_in = g.add_node();
        let g_out1 = g.add_node();
        let g_out2 = g.add_node();
        
        g.add_edge(
            vec![SourceWithBinding { source: g_in, bound: vec![] }],
            vec![g_out1],
            Some(Label::Meta("M".to_string(), 1))
        ).unwrap();
        g.add_edge(
            vec![SourceWithBinding { source: g_in, bound: vec![] }],
            vec![g_out2],
            Some(Label::Meta("M".to_string(), 1))
        ).unwrap();
        
        let g_int = BHyp_with_interface::from_bhyp(g.clone());
        
        // Replacement T with extra interface vertex (free)
        let mut t = BHyp::new();
        let t_in = t.add_node();
        let t_free = t.add_node();  // Free vertex - will be glued across copies
        let t_out = t.add_node();
        
        t.add_edge(
            vec![SourceWithBinding { source: t_in, bound: vec![] }],
            vec![t_free],
            Some(Label::Symbol("a".to_string()))
        ).unwrap();
        t.add_edge(
            vec![SourceWithBinding { source: t_free, bound: vec![] }],
            vec![t_out],
            Some(Label::Symbol("b".to_string()))
        ).unwrap();
        
        // t_free is in the interface but NOT mapped from M
        let t_int = BHyp_with_interface::from_bhyp(t.clone());
        
        let mut interface_map = HashMap::new();
        interface_map.insert(0, t_in);   // M source -> T input
        interface_map.insert(1, t_out);  // M target -> T output
        // t_free is NOT in interface_map, so it's free
        
        let t_int_clone = t_int.clone();
        let subst = Substitution {
            meta_name: Label::Meta("M".to_string(), 1),
            replacement: t_int_clone,
            interface_map: t_int_clone.input_map().clone(),
        };
        
        // Verify t_free is detected as free
        let free = subst.free_vertices();
        assert!(free.contains(&t_free), "t_free should be a free vertex");
        
        let k = BHyp::new();
        let shared = Span {
            left: g.clone(),
            middle: k.clone(),
            right: t.clone(),
            to_l: BHypMorphism::new(k.clone(), g.clone(), HashMap::new(), HashMap::new()).unwrap(),
            to_r: BHypMorphism::new(k.clone(), t.clone(), HashMap::new(), HashMap::new()).unwrap(),
        };
        
        let result = apply_substitution(&g_int, &subst, &shared).unwrap();
        
        // With 2 copies of T glued at t_free:
        // - Each copy has edges "a" and "b"
        // - The free vertex is shared between copies
        // - So we should have 4 edges total (2 "a" + 2 "b")
        // - But fewer nodes than 2*3 = 6 because t_free is glued
        
        assert_eq!(result.bhyp().edges().len(), 4);
        
        // Node count: 2 copies would have 6 nodes, but gluing t_free gives 5
        // Plus original g_in (if preserved structure), actual count depends on DPO
        // The key assertion is that free vertices are glued
        let node_count = result.bhyp().nodes().len();
        assert!(node_count < 6, "Free vertices should be glued, reducing node count");
    }

    // ============================================================================
    // Tests for apply_substitution - Higher Arity
    // ============================================================================

    #[test]
    fn test_apply_substitution_arity_2() {
        // Metaedge M with arity 2 (binary operation)
        let mut g = BHyp::new();
        let g_in1 = g.add_node();
        let g_in2 = g.add_node();
        let g_out = g.add_node();
        
        g.add_edge(
            vec![
                SourceWithBinding { source: g_in1, bound: vec![] },
                SourceWithBinding { source: g_in2, bound: vec![] }
            ],
            vec![g_out],
            Some(Label::Meta("M".to_string(), 2))
        ).unwrap();
        
        let g_int = BHyp_with_interface::new(g.clone(), vec![g_in1, g_in2], vec![g_out]);
        
        // Replacement T: composition of two unary operations
        let mut t = BHyp::new();
        let t_in1 = t.add_node();
        let t_in2 = t.add_node();
        let t_mid = t.add_node();
        let t_out = t.add_node();
        
        t.add_edge(
            vec![SourceWithBinding { source: t_in1, bound: vec![] }],
            vec![t_mid],
            Some(Label::Symbol("f".to_string()))
        ).unwrap();
        t.add_edge(
            vec![
                SourceWithBinding { source: t_mid, bound: vec![] },
                SourceWithBinding { source: t_in2, bound: vec![] }
            ],
            vec![t_out],
            Some(Label::Symbol("g".to_string()))
        ).unwrap();
        
        let t_int = BHyp_with_interface::new(t.clone(), vec![t_in1, t_in2], vec![t_out]);
        
        let mut interface_map = HashMap::new();
        interface_map.insert(0, t_in1);  // M source 0 -> T input 1
        interface_map.insert(1, t_in2);  // M source 1 -> T input 2
        interface_map.insert(2, t_out);  // M target -> T output
        
        let subst = Substitution {
            meta_name: Label::Meta("M".to_string(), 2),
            replacement: t_int,
            interface_map,
        };
        
        let k = BHyp::new();
        let shared = Span {
            left: g.clone(),
            middle: k.clone(),
            right: t.clone(),
            to_l: BHypMorphism::new(k.clone(), g.clone(), HashMap::new(), HashMap::new()).unwrap(),
            to_r: BHypMorphism::new(k.clone(), t.clone(), HashMap::new(), HashMap::new()).unwrap(),
        };
        
        let result = apply_substitution(&g_int, &subst, &shared).unwrap();
        
        // Result should have edges "f" and "g" instead of M
        assert_eq!(result.bhyp().edges().len(), 2);
        
        // No Meta edges should remain
        let has_meta = result.bhyp().edges().any(|&e| {
            result.bhyp().get_edge(e)
                .map(|edge| matches!(edge.label, Some(Label::Meta(_, _))))
                .unwrap_or(false)
        });
        assert!(!has_meta, "Metaedge should be replaced");
    }

    // ============================================================================
    // Tests for apply_substitution - Edge Cases
    // ============================================================================

    #[test]
    fn test_apply_substitution_empty_replacement() {
        // Replace M with empty T (just interface nodes, no edges)
        let mut g = BHyp::new();
        let g_in = g.add_node();
        let g_out = g.add_node();
        
        g.add_edge(
            vec![SourceWithBinding { source: g_in, bound: vec![] }],
            vec![g_out],
            Some(Label::Meta("M".to_string(), 1))
        ).unwrap();
        
        let g_int = BHyp_with_interface::new(g.clone(), vec![g_in], vec![g_out]);
        
        // Empty replacement (nodes only)
        let mut t = BHyp::new();
        let t_in = t.add_node();
        let t_out = t.add_node();
        // No edges!
        
        let t_int = BHyp_with_interface::new(t.clone(), vec![t_in], vec![t_out]);
        
        let mut interface_map = HashMap::new();
        interface_map.insert(0, t_in);
        interface_map.insert(1, t_out);
        
        let subst = Substitution {
            meta_name: Label::Meta("M".to_string(), 1),
            replacement: t_int,
            interface_map,
        };
        
        let k = BHyp::new();
        let shared = Span {
            left: g.clone(),
            middle: k.clone(),
            right: t.clone(),
            to_l: BHypMorphism::new(k.clone(), g.clone(), HashMap::new(), HashMap::new()).unwrap(),
            to_r: BHypMorphism::new(k.clone(), t.clone(), HashMap::new(), HashMap::new()).unwrap(),
        };
        
        let result = apply_substitution(&g_int, &subst, &shared).unwrap();
        
        // Result should have no edges (M removed, T has no edges)
        assert_eq!(result.bhyp().edges().len(), 0);
        // But should preserve nodes
        assert!(result.bhyp().nodes().len() >= 2);
    }

    #[test]
    fn test_apply_substitution_complex_replacement() {
        // Replace M with a complex T that has multiple edges and internal structure
        let mut g = BHyp::new();
        let g_in = g.add_node();
        let g_out = g.add_node();
        
        g.add_edge(
            vec![SourceWithBinding { source: g_in, bound: vec![] }],
            vec![g_out],
            Some(Label::Meta("M".to_string(), 1))
        ).unwrap();
        
        let g_int = BHyp_with_interface::new(g.clone(), vec![g_in], vec![g_out]);
        
        // Complex replacement with diamond pattern
        let mut t = BHyp::new();
        let t_in = t.add_node();
        let t_a = t.add_node();
        let t_b = t.add_node();
        let t_out = t.add_node();
        
        t.add_edge(
            vec![SourceWithBinding { source: t_in, bound: vec![] }],
            vec![t_a],
            Some(Label::Symbol("left".to_string()))
        ).unwrap();
        t.add_edge(
            vec![SourceWithBinding { source: t_in, bound: vec![] }],
            vec![t_b],
            Some(Label::Symbol("right".to_string()))
        ).unwrap();
        t.add_edge(
            vec![
                SourceWithBinding { source: t_a, bound: vec![] },
                SourceWithBinding { source: t_b, bound: vec![] }
            ],
            vec![t_out],
            Some(Label::Symbol("merge".to_string()))
        ).unwrap();
        
        let t_int = BHyp_with_interface::new(t.clone(), vec![t_in], vec![t_out]);
        
        let mut interface_map = HashMap::new();
        interface_map.insert(0, t_in);
        interface_map.insert(1, t_out);
        
        let subst = Substitution {
            meta_name: Label::Meta("M".to_string(), 1),
            replacement: t_int,
            interface_map,
        };
        
        let k = BHyp::new();
        let shared = Span {
            left: g.clone(),
            middle: k.clone(),
            right: t.clone(),
            to_l: BHypMorphism::new(k.clone(), g.clone(), HashMap::new(), HashMap::new()).unwrap(),
            to_r: BHypMorphism::new(k.clone(), t.clone(), HashMap::new(), HashMap::new()).unwrap(),
        };
        
        let result = apply_substitution(&g_int, &subst, &shared).unwrap();
        
        // Result should have 3 edges (left, right, merge)
        assert_eq!(result.bhyp().edges().len(), 3);
        
        // Verify diamond structure by checking node degrees
        let nodes: Vec<_> = result.bhyp().nodes().collect();
        
        // Find the "in" node (out-degree 2, in-degree 0)
        let in_node = nodes.iter().find(|&&n| {
            result.bhyp().out_degree(n) == 2 && result.bhyp().in_degree(n) == 0
        });
        assert!(in_node.is_some(), "Should have input node with out-degree 2");
        
        // Find the "out" node (in-degree 1, out-degree 0)
        let out_node = nodes.iter().find(|&&n| {
            result.bhyp().in_degree(n) == 1 && result.bhyp().out_degree(n) == 0
        });
        assert!(out_node.is_some(), "Should have output node");
    }

    // ============================================================================
    // Tests for Error Handling
    // ============================================================================

    #[test]
    fn test_substitution_error_display() {
        let errors = vec![
            SubstitutionError::MetavariableNotFound("X".to_string()),
            SubstitutionError::ArityMismatch { expected: 2, got: 3 },
            SubstitutionError::InterfaceMismatch("test".to_string()),
            SubstitutionError::InvalidConstruction("bad".to_string()),
        ];
        
        for error in errors {
            let display = format!("{}", error);
            assert!(!display.is_empty());
        }
    }

    #[test]
    fn test_substitution_builder_pattern() {
        let mut t = BHyp::new();
        let t_in = t.add_node();
        let t_out = t.add_node();
        let t_int = BHyp_with_interface::new(t, vec![t_in], vec![t_out]);
        
        let mut map = HashMap::new();
        map.insert(0, t_in);
        map.insert(1, t_out);
        
        let subst = Substitution::new(Label::Meta("M".to_string(), 1), t_int)
            .with_interface_map(map.clone());
        
        assert_eq!(subst.meta_name, Label::Meta("M".to_string(), 1));
        assert_eq!(subst.interface_map, map);
    }

    // ============================================================================
    // Integration Tests
    // ============================================================================

    #[test]
    fn test_substitution_preserves_non_meta_edges() {
        // G has both metaedge M and regular edges - regular edges should be preserved
        let mut g = BHyp::new();
        let n0 = g.add_node();
        let n1 = g.add_node();
        let n2 = g.add_node();
        let n3 = g.add_node();
        
        // Regular edge
        g.add_edge(
            vec![SourceWithBinding { source: n0, bound: vec![] }],
            vec![n1],
            Some(Label::Symbol("regular1".to_string()))
        ).unwrap();
        
        // Metaedge
        g.add_edge(
            vec![SourceWithBinding { source: n1, bound: vec![] }],
            vec![n2],
            Some(Label::Meta("M".to_string(), 1))
        ).unwrap();
        
        // Another regular edge
        g.add_edge(
            vec![SourceWithBinding { source: n2, bound: vec![] }],
            vec![n3],
            Some(Label::Symbol("regular2".to_string()))
        ).unwrap();
        
        let g_int = BHyp_with_interface::new(g.clone(), vec![n0], vec![n3]);
        
        // Replacement
        let mut t = BHyp::new();
        let t_in = t.add_node();
        let t_out = t.add_node();
        t.add_edge(
            vec![SourceWithBinding { source: t_in, bound: vec![] }],
            vec![t_out],
            Some(Label::Symbol("replaced".to_string()))
        ).unwrap();
        
        let t_int = BHyp_with_interface::new(t.clone(), vec![t_in], vec![t_out]);
        
        let mut interface_map = HashMap::new();
        interface_map.insert(0, t_in);
        interface_map.insert(1, t_out);
        
        let subst = Substitution {
            meta_name: Label::Meta("M".to_string(), 1),
            replacement: t_int,
            interface_map,
        };
        
        let k = BHyp::new();
        let shared = Span {
            left: g.clone(),
            middle: k.clone(),
            right: t.clone(),
            to_l: BHypMorphism::new(k.clone(), g.clone(), HashMap::new(), HashMap::new()).unwrap(),
            to_r: BHypMorphism::new(k.clone(), t.clone(), HashMap::new(), HashMap::new()).unwrap(),
        };
        
        let result = apply_substitution(&g_int, &subst, &shared).unwrap();
        
        // Should have 3 edges: regular1, replaced, regular2
        assert_eq!(result.bhyp().edges().len(), 3);
        
        // Check that regular edges are preserved
        let labels: HashSet<_> = result.bhyp().edges()
            .filter_map(|&e| result.bhyp().get_edge(e).and_then(|edge| edge.label.clone()))
            .collect();
        
        assert!(labels.contains(&Label::Symbol("regular1".to_string())));
        assert!(labels.contains(&Label::Symbol("regular2".to_string())));
        assert!(labels.contains(&Label::Symbol("replaced".to_string())));
        assert!(!labels.iter().any(|l| matches!(l, Label::Meta(_, _))));
    }

    #[test]
    fn test_sequential_substitutions() {
        // Apply two different substitutions in sequence
        let mut g = BHyp::new();
        let n0 = g.add_node();
        let n1 = g.add_node();
        let n2 = g.add_node();
        
        g.add_edge(
            vec![SourceWithBinding { source: n0, bound: vec![] }],
            vec![n1],
            Some(Label::Meta("M".to_string(), 1))
        ).unwrap();
        g.add_edge(
            vec![SourceWithBinding { source: n1, bound: vec![] }],
            vec![n2],
            Some(Label::Meta("N".to_string(), 1))
        ).unwrap();
        
        let g_int = BHyp_with_interface::new(g.clone(), vec![n0], vec![n2]);
        
        // First substitution: M -> T_m
        let mut t_m = BHyp::new();
        let t_m_in = t_m.add_node();
        let t_m_out = t_m.add_node();
        t_m.add_edge(
            vec![SourceWithBinding { source: t_m_in, bound: vec![] }],
            vec![t_m_out],
            Some(Label::Symbol("replaced_M".to_string()))
        ).unwrap();
        
        let t_m_int = BHyp_with_interface::new(t_m.clone(), vec![t_m_in], vec![t_m_out]);
        
        let mut interface_map_m = HashMap::new();
        interface_map_m.insert(0, t_m_in);
        interface_map_m.insert(1, t_m_out);
        
        let subst_m = Substitution {
            meta_name: Label::Meta("M".to_string(), 1),
            replacement: t_m_int,
            interface_map: interface_map_m,
        };
        
        let k = BHyp::new();
        let shared_m = Span {
            left: g.clone(),
            middle: k.clone(),
            right: t_m.clone(),
            to_l: BHypMorphism::new(k.clone(), g.clone(), HashMap::new(), HashMap::new()).unwrap(),
            to_r: BHypMorphism::new(k.clone(), t_m.clone(), HashMap::new(), HashMap::new()).unwrap(),
        };
        
        let result1 = apply_substitution(&g_int, &subst_m, &shared_m).unwrap();
        
        // Second substitution: N -> T_n
        let mut t_n = BHyp::new();
        let t_n_in = t_n.add_node();
        let t_n_out = t_n.add_node();
        t_n.add_edge(
            vec![SourceWithBinding { source: t_n_in, bound: vec![] }],
            vec![t_n_out],
            Some(Label::Symbol("replaced_N".to_string()))
        ).unwrap();
        
        let t_n_int = BHyp_with_interface::new(t_n.clone(), vec![t_n_in], vec![t_n_out]);
        
        let mut interface_map_n = HashMap::new();
        interface_map_n.insert(0, t_n_in);
        interface_map_n.insert(1, t_n_out);
        
        let subst_n = Substitution {
            meta_name: Label::Meta("N".to_string(), 1),
            replacement: t_n_int,
            interface_map: interface_map_n,
        };
        
        let shared_n = Span {
            left: result1.bhyp().clone(),
            middle: k.clone(),
            right: t_n.clone(),
            to_l: BHypMorphism::new(k.clone(), result1.bhyp().clone(), HashMap::new(), HashMap::new()).unwrap(),
            to_r: BHypMorphism::new(k.clone(), t_n.clone(), HashMap::new(), HashMap::new()).unwrap(),
        };
        
        let result2 = apply_substitution(&result1, &subst_n, &shared_n).unwrap();
        
        // Final result should have no metaedges
        let has_meta = result2.bhyp().edges().any(|&e| {
            result2.bhyp().get_edge(e)
                .map(|edge| matches!(edge.label, Some(Label::Meta(_, _))))
                .unwrap_or(false)
        });
        assert!(!has_meta, "All metaedges should be replaced");
        
        // Should have exactly 2 edges
        assert_eq!(result2.bhyp().edges().len(), 2);
    }

        #[test]
fn test_substitution_copying_commutativity_with_functions() {
    // Validates Lemma 3.14: Substitution and copying commutativity[cite: 3]
    // Uses actual function calls to `apply_substitution` and `copy_subhypergraph`

    // 1. Construct the initial graph G
    let mut g = BHyp::new();
    let n_in = g.add_node();
    let shared_v = g.add_node();
    let n_out1 = g.add_node();
    let n_out2 = g.add_node();
    
    // Metaedge M
    let _m_edge = g.add_edge(
        vec![SourceWithBinding { source: n_in, bound: vec![] }],
        vec![shared_v],
        Some(Label::Symbol("M".to_string()))
    ).unwrap();
    
    // Edge 1 and Edge 2 branching from shared_v
    let _e1 = g.add_edge(
        vec![SourceWithBinding { source: shared_v, bound: vec![] }],
        vec![n_out1],
        Some(Label::Symbol("1".to_string()))
    ).unwrap();
    let _e2 = g.add_edge(
        vec![SourceWithBinding { source: shared_v, bound: vec![] }],
        vec![n_out2],
        Some(Label::Symbol("2".to_string()))
    ).unwrap();

    let g_int = BHyp_with_interface::from_bhyp(g.clone());

    // 2. Construct Sub-hypergraph M (for copying)
    let mut m_sub = BHyp::new();
    let m_sub_in = m_sub.add_node();
    let m_sub_out = m_sub.add_node();
    m_sub.add_edge(
        vec![SourceWithBinding { source: m_sub_in, bound: vec![] }],
        vec![m_sub_out],
        Some(Label::Symbol("M".to_string()))
    ).unwrap();

    // 3. Construct Replacement T (for substitution)
    let mut t_sub = BHyp::new();
    let t_sub_in = t_sub.add_node();
    let t_sub_out = t_sub.add_node();
    t_sub.add_edge(
        vec![SourceWithBinding { source: t_sub_in, bound: vec![] }],
        vec![t_sub_out],
        Some(Label::Symbol("T".to_string()))
    ).unwrap();

    let mut t_int = BHyp_with_interface::from_bhyp(t_sub.clone());
    let mut interface_map = HashMap::new();
    interface_map.insert(m_sub_in, t_sub_in);
    interface_map.insert(m_sub_out, t_sub_out);
    
    let subst = Substitution {
        meta_name: Label::Meta("M".to_string(), 1),
        replacement: t_int.clone(),
        interface_map,
    };

    // 4. Construct Spans for Shared Nodes (K)
    let mut k = BHyp::new();
    let k_node = k.add_node();

    // Shared span for copying M in G
    let copy_m_span = Span {
        left: g.clone(),
        middle: k.clone(),
        right: m_sub.clone(),
        to_l: BHypMorphism::new(k.clone(), g.clone(), [(k_node, shared_v)].into_iter().collect(), HashMap::new()).unwrap(),
        to_r: BHypMorphism::new(k.clone(), m_sub.clone(), [(k_node, m_sub_out)].into_iter().collect(), HashMap::new()).unwrap(),
    };

    // Shared span for substituting M -> T in G
    let subst_span = Span {
        left: g.clone(),
        middle: k.clone(),
        right: t_int.bhyp().clone(),
        to_l: BHypMorphism::new(k.clone(), g.clone(), [(k_node, shared_v)].into_iter().collect(), HashMap::new()).unwrap(),
        to_r: BHypMorphism::new(k.clone(), t_int.bhyp().clone(), [(k_node, t_sub_out)].into_iter().collect(), HashMap::new()).unwrap(),
    };

    // ==========================================
    // Path A: Substitute first, then Copy[cite: 3]
    // ==========================================
    let g_subst = apply_substitution(&g_int, &subst, &subst_span)
        .expect("Substitution failed on Path A");

    // Span needs to be updated to map to the new shared vertex in the substituted graph
    let shared_v_subst = g_subst.bhyp().nodes().iter().find(|&&n| g_subst.bhyp().out_degree(n) == 2).unwrap();
    let copy_t_span = Span {
        left: g_subst.bhyp().clone(),
        middle: k.clone(),
        right: t_sub.clone(),
        to_l: BHypMorphism::new(k.clone(), g_subst.bhyp().clone(), [(k_node, *shared_v_subst)].into_iter().collect(), HashMap::new()).unwrap(),
        to_r: BHypMorphism::new(k.clone(), t_sub.clone(), [(k_node, t_sub_out)].into_iter().collect(), HashMap::new()).unwrap(),
    };

    let path_a_result = copy_subhypergraph(g_subst.bhyp(), &t_sub, copy_t_span)
        .expect("Copy failed on Path A");

    // ==========================================
    // Path B: Copy first, then Substitute[cite: 3]
    // ==========================================
    let g_copied = copy_subhypergraph(&g, &m_sub, copy_m_span)
        .expect("Copy failed on Path B");

    let g_copied_int = BHyp_with_interface::from_bhyp(g_copied.clone());
    
    // Shared span updated for the copied graph before substitution
    let shared_v_copied = g_copied.nodes().iter().find(|&&n| g_copied.out_degree(n) == 2).unwrap();
    let subst_span_copied = Span {
        left: g_copied.clone(),
        middle: k.clone(),
        right: t_int.bhyp().clone(),
        to_l: BHypMorphism::new(k.clone(), g_copied.clone(), [(k_node, *shared_v_copied)].into_iter().collect(), HashMap::new()).unwrap(),
        to_r: BHypMorphism::new(k.clone(), t_int.bhyp().clone(), [(k_node, t_sub_out)].into_iter().collect(), HashMap::new()).unwrap(),
    };

    let path_b_result = apply_substitution(&g_copied_int, &subst, &subst_span_copied)
        .expect("Substitution failed on Path B");

    // ==========================================
    // Assert Commutativity
    // ==========================================
    assert!(
        are_isomorphic(&path_a_result, path_b_result.bhyp()),
        "Substitution and copying must commute, but the resulting graphs are not isomorphic."
    );
}
   
}



