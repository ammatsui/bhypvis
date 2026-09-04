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
            if let Some(&t_target_n) = subst.interface_map.get(&m_n) {
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

    #[test]
    fn test_construct_meta_hypergraph_arity_0() {
        let label = Label::Meta("X".to_string(), 0);
        let result = construct_meta_hypergraph(label.clone()).unwrap();

        assert_eq!(result.nodes().len(), 1);
        assert_eq!(result.edges().len(), 1);

        let edge_id = result.edges().iter().next().unwrap();
        assert_eq!(result.get_sources(*edge_id).unwrap().len(), 0);
        assert_eq!(result.get_targets(*edge_id).unwrap().len(), 1);
        assert_eq!(result.get_label(*edge_id), Some(&label));
    }

    #[test]
    fn test_construct_meta_hypergraph_arity_1() {
        let label = Label::Meta("Y".to_string(), 1);
        let result = construct_meta_hypergraph(label.clone()).unwrap();

        assert_eq!(result.nodes().len(), 2);
        assert_eq!(result.edges().len(), 1);

        let edge_id = result.edges().iter().next().unwrap();
        assert_eq!(result.get_sources(*edge_id).unwrap().len(), 1);
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
    fn test_free_vertices_all_mapped() {
        let mut t = BHyp::new();
        let n0 = t.add_node();
        let _n1 = t.add_node();
        let n2 = t.add_node();

        let t_with_interface = BHyp_with_interface::from_bhyp(t.clone());
        let interface_map: HashMap<NodeId, NodeId> = t_with_interface
            .input_map()
            .iter()
            .chain(t_with_interface.output_map().iter())
            .map(|(&k, &v)| (k, v))
            .collect();

        let subst = Substitution {
            meta_name: Label::Meta("X".to_string(), 2),
            replacement: t_with_interface,
            interface_map,
        };

        assert!(subst.free_vertices().is_empty());
        let _ = (n0, n2);
    }


#[test]
fn test_apply_substitution_replaces_metaedge() {
    // Create G with metaedge M: g_in --[M]--> g_out
    let mut g = BHyp::new();
    let g_in = g.add_node();
    let g_out = g.add_node();
    g.add_edge(
        vec![SourceWithBinding { source: g_in, bound: vec![] }],
        vec![g_out],
        Some(Label::Meta("M".to_string(), 1)),
    ).unwrap();

    let g_int = BHyp_with_interface::from_bhyp(g.clone());

    // Create replacement T: t_in --[replaced]--> t_out
    let mut t = BHyp::new();
    let t_in = t.add_node();
    let t_out = t.add_node();
    t.add_edge(
        vec![SourceWithBinding { source: t_in, bound: vec![] }],
        vec![t_out],
        Some(Label::Symbol("replaced".to_string())),
    ).unwrap();

    let t_int = BHyp_with_interface::from_bhyp(t.clone());
    
    // CRITICAL FIX: interface_map maps M's nodes to T's nodes
    // M (from construct_meta_hypergraph with arity 1) has:
    //   - NodeId(0): source
    //   - NodeId(1): target
    // We map these to T's corresponding nodes
    let met = construct_meta_hypergraph(Label::Meta("M".to_string(), 1)).unwrap();
    let met_nodes: Vec<NodeId> = met.nodes().iter().copied().collect();
    
    // Find which node is source and which is target in met
    let met_edge = met.edges().iter().next().unwrap();
    let met_sources = met.get_sources(*met_edge).unwrap();
    let met_targets = met.get_targets(*met_edge).unwrap();
    
    let m_source = met_sources[0];  // The source node of M
    let m_target = met_targets[0];          // The target node of M
    
    let mut interface_map = HashMap::new();
    interface_map.insert(m_source, t_in);   // M's source -> T's input
    interface_map.insert(m_target, t_out);  // M's target -> T's output

    let subst = Substitution {
        meta_name: Label::Meta("M".to_string(), 1),
        replacement: t_int,
        interface_map,
    };

    // Empty shared span (K is empty)
    let k = BHyp::new();
    let shared = Span {
        left: g.clone(),
        middle: k.clone(),
        right: t.clone(),
        to_l: BHypMorphism::new(
            k.clone(),
            g.clone(),
            HashMap::new(),
            HashMap::new(),
        ).unwrap(),
        to_r: BHypMorphism::new(
            k.clone(),
            t.clone(),
            HashMap::new(),
            HashMap::new(),
        ).unwrap(),
    };

    let result = apply_substitution(&g_int, &subst, &shared).unwrap();
    assert_eq!(result.bhyp().edges().len(), 1);
    assert!(!result.bhyp().edges().iter().any(|&e| 
        matches!(result.bhyp().get_label(e), Some(Label::Meta(_, _)))
    ));
}





    #[test]
    fn test_substitution_builder_pattern() {
        let mut t = BHyp::new();
        let t_in = t.add_node();
        let t_out = t.add_node();
        let t_int = BHyp_with_interface::from_bhyp(t);

        let mut map = HashMap::new();
        let in_key = *t_int.input_map().keys().next().unwrap();
        let out_key = *t_int.output_map().keys().next().unwrap();
        map.insert(in_key, t_in);
        map.insert(out_key, t_out);

        let subst = Substitution::new(Label::Meta("M".to_string(), 1), t_int)
            .with_interface_map(map.clone());

        assert_eq!(subst.meta_name, Label::Meta("M".to_string(), 1));
        assert_eq!(subst.interface_map, map);
    }
}



