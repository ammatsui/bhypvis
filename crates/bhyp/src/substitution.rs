// Metaedge extraction constructions and substitution for hypergraphs with binding
// copying and glueing shared subhypergraphs (Definition 3.12, 3.15)


//Substitution::interface_map: NodeId in canonical M -> NodeId in replacement interface graph
// note: thats a problem but for now 
// do not resolve combined_interface_nodes() entries through input_map() / output_map(); they are already concrete T nodes.
use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::bhyp::{BHyp, BHyp_with_interface, EdgeId, Label, NodeId, SourceWithBinding};
use crate::categorical::{
    BHypMorphism, CategoricalError, Span, 
    are_isomorphic, find_all_occurrences,
    compute_coproduct, compute_pushout, compute_pushout_complement, dpo
};
use crate::copy::{compute_n_copies, copy_subhypergraph, compute_n_copies_with_interface};
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
///     n·M ⊔ K  <──  n·(I_M) ⊔ K  ──>  n·T̂
///        ↓              ↓               ↓
///        G   <─────    C    ─────>   G[M/T]
/// ```
///
/// Where:
/// - n = multiplicity of M in G
/// - K = shared variables
/// - n·T̂ = n copies of T glued along free vertices
pub fn apply_substitution(
    g: &BHyp_with_interface,
    subst: &Substitution,
    shared: &Span,
) -> Result<BHyp_with_interface, SubstitutionError> {
    // ---------------------------------------------------------------------
    // 1. Find all occurrences of M in G.
    // ---------------------------------------------------------------------

    let met = construct_meta_hypergraph(subst.meta_name.clone())
        .map_err(SubstitutionError::InvalidConstruction)?;

    let occurrences = find_all_occurrences(&met, &g.bhyp());
    let n = occurrences.len();

    if n == 0 {
        return Ok(g.clone());
    }

    let i_m = BHyp_with_interface::from_bhyp(met.clone());

    // The canonical meta-hypergraph should contain exactly one edge.
    let met_edges: Vec<EdgeId> = met.edges().iter().copied().collect();

    if met_edges.len() != 1 {
        return Err(SubstitutionError::InvalidConstruction(format!(
            "canonical meta-hypergraph for {:?} should have exactly one edge, found {}",
            subst.meta_name,
            met_edges.len()
        )));
    }

    let met_edge = met_edges[0];

    // API returns grouped sources/targets, so flatten.
    let met_sources: HashSet<NodeId> = met
        .get_sources(met_edge)
        .iter()
        .flatten()
        .copied()
        .collect();

    let met_targets: HashSet<NodeId> = met
        .get_targets(met_edge)
        .iter()
        .flatten()
        .copied()
        .collect();

    // Resolve replacement interface node into concrete T node.
    //
    // IMPORTANT:
    // input_interface and output_interface can both contain e.g. NodeId(0),
    // so the replacement interface node alone is ambiguous.
    //
    // We disambiguate using the M-side port:
    // - M source  -> replacement input_map
    // - M target  -> replacement output_map
    let replacement_iface_to_bhyp_node_for_m_port =
        |m_iface_node: NodeId,
         replacement_iface_node: NodeId|
         -> Result<NodeId, SubstitutionError> {
            if met_sources.contains(&m_iface_node) {
                subst
                    .replacement
                    .input_map()
                    .get(&replacement_iface_node)
                    .copied()
                    .ok_or_else(|| {
                        SubstitutionError::InvalidConstruction(format!(
                            "M source {:?} maps to replacement input interface node {:?}, \
                             but that node has no backing node in T",
                            m_iface_node, replacement_iface_node
                        ))
                    })
            } else if met_targets.contains(&m_iface_node) {
                subst
                    .replacement
                    .output_map()
                    .get(&replacement_iface_node)
                    .copied()
                    .ok_or_else(|| {
                        SubstitutionError::InvalidConstruction(format!(
                            "M target {:?} maps to replacement output interface node {:?}, \
                             but that node has no backing node in T",
                            m_iface_node, replacement_iface_node
                        ))
                    })
            } else {
                Err(SubstitutionError::InvalidConstruction(format!(
                    "M interface node {:?} is neither source nor target of canonical metaedge {:?}",
                    m_iface_node, subst.meta_name
                )))
            }
        };

    // ---------------------------------------------------------------------
    // 2. Build n copies of M.
    //
    // Since the interface is empty, this is just n disjoint copies of M.
    //
    // New API returns:
    //
    //     m_incl[i] : M -> n·M
    //     m_proj    : n·M -> M
    // ---------------------------------------------------------------------

    let empty_k = BHyp::new();

    let empty_morphism = BHypMorphism::new(
        empty_k.clone(),
        met.clone(),
        HashMap::new(),
        HashMap::new(),
    )
    .map_err(|e| SubstitutionError::InvalidConstruction(e.to_string()))?;

    let (n_m, _m_proj, m_incl) = compute_n_copies_with_interface(
        &i_m,
        n,
        Some((empty_k, empty_morphism)),
    )
    .map_err(|e| SubstitutionError::InvalidConstruction(format!("{:?}", e)))?;

    if m_incl.len() != n {
        return Err(SubstitutionError::InvalidConstruction(format!(
            "expected {} inclusions M -> n·M, got {}",
            n,
            m_incl.len()
        )));
    }

    println!("here! created n copies of M");

    // ---------------------------------------------------------------------
    // 3. Build n·T̂.
    //
    // n·T̂ is n copies of T glued along the free interface:
    //
    //     I_F = I_T \ image(I_M -> I_T)
    //
    // Everything here should be represented as concrete T.bhyp() nodes.
    // ---------------------------------------------------------------------

    let mut m_image_in_t: HashSet<NodeId> = HashSet::new();

    for (&m_iface_node, &replacement_iface_node) in &subst.interface_map {
        let t_node = replacement_iface_to_bhyp_node_for_m_port(
            m_iface_node,
            replacement_iface_node,
        )?;

        m_image_in_t.insert(t_node);
    }

    // Do not use combined_interface_nodes() here. Build concrete T interface
    // directly from input_map/output_map values.
    let t_interface_nodes: HashSet<NodeId> = subst
        .replacement
        .input_map()
        .values()
        .chain(subst.replacement.output_map().values())
        .copied()
        .collect();

    let mut i_f = BHyp::new();
    let mut i_f_map_nodes = HashMap::new();

    for &t_bhyp_node in &t_interface_nodes {
        if !m_image_in_t.contains(&t_bhyp_node) {
            let i_f_node = i_f.add_node();
            i_f_map_nodes.insert(i_f_node, t_bhyp_node);
        }
    }

    let kt_to_t = BHypMorphism::new(
        i_f.clone(),
        subst.replacement.bhyp().clone(),
        i_f_map_nodes,
        HashMap::new(),
    )
    .map_err(|e| SubstitutionError::InvalidConstruction(e.to_string()))?;

    let (n_t_glued, t_proj, t_incl) = compute_n_copies_with_interface(
        &subst.replacement,
        n,
        Some((i_f, kt_to_t)),
    )
    .map_err(|e| SubstitutionError::InvalidConstruction(format!("{:?}", e)))?;

    if t_incl.len() != n {
        return Err(SubstitutionError::InvalidConstruction(format!(
            "expected {} inclusions T -> n·T̂, got {}",
            n,
            t_incl.len()
        )));
    }

    println!("here! compute n copies of T, glued");

    // ---------------------------------------------------------------------
    // 4. Build objects in the top span.
    //
    //     n·M ⊔ K  <──  n·I_M ⊔ K  ──>  n·T̂
    // ---------------------------------------------------------------------

    let nim_result = compute_coproduct(n_m.input_interface(), n_m.output_interface())
        .map_err(|e| SubstitutionError::InvalidConstruction(format!("{:?}", e)))?;

    let nim_graph = &nim_result.pushout;

    let nm_k_result = compute_coproduct(n_m.bhyp(), &shared.middle)
        .map_err(|e| SubstitutionError::InvalidConstruction(format!("{:?}", e)))?;

    let nm_k = &nm_k_result.pushout;

    let nim_k_result = compute_coproduct(nim_graph, &shared.middle)
        .map_err(|e| SubstitutionError::InvalidConstruction(format!("{:?}", e)))?;

    let nim_k = &nim_k_result.pushout;

    println!("here! created top-span objects");

    // ---------------------------------------------------------------------
    // 5. Construct to_l:
    //
    //     to_l : n·I_M ⊔ K -> n·M ⊔ K
    //
    // n·I_M part uses n_m.input_map/output_map.
    // K part uses coproduct injections.
    // ---------------------------------------------------------------------

    let mut to_l_nodes = HashMap::new();

    // n·I_M part.
    for (&nim_node, &nim_k_node) in nim_k_result.morphism_from_b.on_nodes() {
        let nm_node = if let Some((&in_node, _)) = nim_result
            .morphism_from_b
            .on_nodes()
            .iter()
            .find(|(_, &v)| v == nim_node)
        {
            n_m.input_map()[&in_node]
        } else if let Some((&out_node, _)) = nim_result
            .morphism_from_c
            .on_nodes()
            .iter()
            .find(|(_, &v)| v == nim_node)
        {
            n_m.output_map()[&out_node]
        } else {
            return Err(SubstitutionError::InvalidConstruction(format!(
                "node {:?} of n·I_M not found in input/output interface coproduct injections",
                nim_node
            )));
        };

        let nm_k_node = nm_k_result
            .morphism_from_b
            .map_node(nm_node)
            .ok_or_else(|| {
                SubstitutionError::InvalidConstruction(format!(
                    "coproduct injection n·M -> n·M ⊔ K does not map node {:?}",
                    nm_node
                ))
            })?;

        to_l_nodes.insert(nim_k_node, nm_k_node);
    }

    // K part.
    for (&k_node, &nim_k_node) in nim_k_result.morphism_from_c.on_nodes() {
        let nm_k_node = nm_k_result
            .morphism_from_c
            .map_node(k_node)
            .ok_or_else(|| {
                SubstitutionError::InvalidConstruction(format!(
                    "coproduct injection K -> n·M ⊔ K does not map node {:?}",
                    k_node
                ))
            })?;

        to_l_nodes.insert(nim_k_node, nm_k_node);
    }

    for &node in nim_k.nodes() {
        if !to_l_nodes.contains_key(&node) {
            return Err(SubstitutionError::InvalidConstruction(format!(
                "to_l is incomplete: node {:?} in n·I_M ⊔ K has no mapping",
                node
            )));
        }
    }

    let to_l_morph = BHypMorphism::new(
        nim_k.clone(),
        nm_k.clone(),
        to_l_nodes,
        HashMap::new(),
    )
    .map_err(|e| SubstitutionError::InvalidConstruction(e.to_string()))?;

    println!("here! created to_l");

    // ---------------------------------------------------------------------
    // 6. Construct to_r:
    //
    //     to_r : n·I_M ⊔ K -> n·T̂
    //
    // A. n·I_M part:
    //
    //      copy i of I_M maps to copy i of T through subst.interface_map.
    //
    // B. K part:
    //
    //      K maps through shared.to_r : K -> T,
    //      then is lifted into n·T̂ through t_proj.
    // ---------------------------------------------------------------------

    let mut to_r_nodes = HashMap::new();

    // Given a concrete node in n·M, find the corresponding node in n·I_M.
    let find_nim_node_for_nm_node = |nm_node: NodeId| -> Option<NodeId> {
        for (&in_iface_node, &mapped_nm_node) in n_m.input_map() {
            if mapped_nm_node == nm_node {
                return nim_result.morphism_from_b.map_node(in_iface_node);
            }
        }

        for (&out_iface_node, &mapped_nm_node) in n_m.output_map() {
            if mapped_nm_node == nm_node {
                return nim_result.morphism_from_c.map_node(out_iface_node);
            }
        }

        None
    };

    // A. n·I_M part, copywise.
    //
    // The copy ordering is now reliable:
    //
    //     occurrences[i] corresponds to m_incl[i] corresponds to t_incl[i].
    for i in 0..n {
        let m_copy_incl = &m_incl[i];
        let t_copy_incl = &t_incl[i];

        for (&m_iface_node, &replacement_iface_node) in &subst.interface_map {
            // M -> n·M
            let nm_node = m_copy_incl.map_node(m_iface_node).ok_or_else(|| {
                SubstitutionError::InvalidConstruction(format!(
                    "M-copy inclusion {} does not map meta interface node {:?}",
                    i, m_iface_node
                ))
            })?;

            // n·M interface node -> n·I_M
            let nim_node = find_nim_node_for_nm_node(nm_node).ok_or_else(|| {
                SubstitutionError::InvalidConstruction(format!(
                    "node {:?} in n·M is not present in n·I_M",
                    nm_node
                ))
            })?;

            // n·I_M -> n·I_M ⊔ K
            let nim_k_node = nim_k_result
                .morphism_from_b
                .map_node(nim_node)
                .ok_or_else(|| {
                    SubstitutionError::InvalidConstruction(format!(
                        "coproduct injection n·I_M -> n·I_M ⊔ K does not map node {:?}",
                        nim_node
                    ))
                })?;

            // M interface node -> replacement interface node -> concrete T node.
            let t_node = replacement_iface_to_bhyp_node_for_m_port(
                m_iface_node,
                replacement_iface_node,
            )?;

            // T -> n·T̂, using the same copy index.
            let nt_node = t_copy_incl.map_node(t_node).ok_or_else(|| {
                SubstitutionError::InvalidConstruction(format!(
                    "T-copy inclusion {} does not map replacement node {:?}",
                    i, t_node
                ))
            })?;

            to_r_nodes.insert(nim_k_node, nt_node);
        }
    }

    // B. K part.
    //
    // shared.to_r : K -> T.
    //
    // We need K -> n·T̂.
    // Since t_proj : n·T̂ -> T, lift the concrete T node into n·T̂.
    //
    // For nodes glued along I_F, this lift should be unique.
    let lift_t_node_to_nt = |t_node: NodeId| -> Result<NodeId, SubstitutionError> {
        let mut candidates = Vec::new();

        for &nt_node in n_t_glued.bhyp().nodes() {
            if t_proj.map_node(nt_node) == Some(t_node) {
                candidates.push(nt_node);
            }
        }

        match candidates.len() {
            0 => Err(SubstitutionError::InvalidConstruction(format!(
                "could not lift T node {:?} into n·T̂ using t_proj",
                t_node
            ))),

            1 => Ok(candidates[0]),

            _ => Err(SubstitutionError::InvalidConstruction(format!(
                "ambiguous lift of T node {:?} into n·T̂: candidates {:?}",
                t_node, candidates
            ))),
        }
    };

    for (&k_node, &nim_k_node) in nim_k_result.morphism_from_c.on_nodes() {
        let t_node = shared.to_r.map_node(k_node).ok_or_else(|| {
            SubstitutionError::InvalidConstruction(format!(
                "shared.to_r does not map K node {:?}",
                k_node
            ))
        })?;

        let nt_node = lift_t_node_to_nt(t_node)?;

        to_r_nodes.insert(nim_k_node, nt_node);
    }

    for &node in nim_k.nodes() {
        if !to_r_nodes.contains_key(&node) {
            return Err(SubstitutionError::InvalidConstruction(format!(
                "to_r is incomplete: node {:?} in n·I_M ⊔ K has no mapping",
                node
            )));
        }
    }

    let to_r_morph = BHypMorphism::new(
        nim_k.clone(),
        n_t_glued.bhyp().clone(),
        to_r_nodes,
        HashMap::new(),
    )
    .map_err(|e| SubstitutionError::InvalidConstruction(e.to_string()))?;

    println!("here! created to_r");

    let top_span = Span {
        left: nm_k.clone(),
        middle: nim_k.clone(),
        right: n_t_glued.bhyp().clone(),
        to_l: to_l_morph,
        to_r: to_r_morph,
    };

    println!("here! created top span");

    // ---------------------------------------------------------------------
    // 7. Construct matching morphism:
    //
    //     match : n·M ⊔ K -> G
    //
    // n·M part:
    //
    //     M --m_incl[i]--> n·M --coproduct--> n·M ⊔ K
    //     M --occurrences[i]--> G
    //
    // K part:
    //
    //     K --shared.to_l--> G
    // ---------------------------------------------------------------------

    let mut match_nodes = HashMap::new();
    let mut match_edges = HashMap::new();

    // K part.
    for (&k_node, &nm_k_node) in nm_k_result.morphism_from_c.on_nodes() {
        let g_node = shared.to_l.map_node(k_node).ok_or_else(|| {
            SubstitutionError::InvalidConstruction(format!(
                "shared.to_l does not map K node {:?}",
                k_node
            ))
        })?;

        match_nodes.insert(nm_k_node, g_node);
    }

    for (&k_edge, &nm_k_edge) in nm_k_result.morphism_from_c.on_edges() {
        let g_edge = shared.to_l.map_edge(k_edge).ok_or_else(|| {
            SubstitutionError::InvalidConstruction(format!(
                "shared.to_l does not map K edge {:?}",
                k_edge
            ))
        })?;

        match_edges.insert(nm_k_edge, g_edge);
    }

    // n·M part, copywise.
    //
    // The critical point is that m_incl[i] is now the real inclusion produced
    // by compute_n_copies_with_interface, so copy ordering is stable.
    for i in 0..n {
        let m_copy_incl = &m_incl[i];
        let occ = &occurrences[i];

        for &m_node in met.nodes() {
            let nm_node = m_copy_incl.map_node(m_node).ok_or_else(|| {
                SubstitutionError::InvalidConstruction(format!(
                    "M-copy inclusion {} does not map meta node {:?}",
                    i, m_node
                ))
            })?;

            let nm_k_node = nm_k_result
                .morphism_from_b
                .map_node(nm_node)
                .ok_or_else(|| {
                    SubstitutionError::InvalidConstruction(format!(
                        "coproduct injection n·M -> n·M ⊔ K does not map node {:?}",
                        nm_node
                    ))
                })?;

            let g_node = occ.map_node(m_node).ok_or_else(|| {
                SubstitutionError::InvalidConstruction(format!(
                    "occurrence {} does not map meta node {:?}",
                    i, m_node
                ))
            })?;

            match_nodes.insert(nm_k_node, g_node);
        }

        for &m_edge in met.edges() {
            let nm_edge = m_copy_incl.map_edge(m_edge).ok_or_else(|| {
                SubstitutionError::InvalidConstruction(format!(
                    "M-copy inclusion {} does not map meta edge {:?}",
                    i, m_edge
                ))
            })?;

            let nm_k_edge = nm_k_result
                .morphism_from_b
                .map_edge(nm_edge)
                .ok_or_else(|| {
                    SubstitutionError::InvalidConstruction(format!(
                        "coproduct injection n·M -> n·M ⊔ K does not map edge {:?}",
                        nm_edge
                    ))
                })?;

            let g_edge = occ.map_edge(m_edge).ok_or_else(|| {
                SubstitutionError::InvalidConstruction(format!(
                    "occurrence {} does not map meta edge {:?}",
                    i, m_edge
                ))
            })?;

            match_edges.insert(nm_k_edge, g_edge);
        }
    }

    for &node in nm_k.nodes() {
        if !match_nodes.contains_key(&node) {
            return Err(SubstitutionError::InvalidConstruction(format!(
                "match morphism is incomplete: node {:?} in n·M ⊔ K has no mapping",
                node
            )));
        }
    }

    for &edge in nm_k.edges() {
        if !match_edges.contains_key(&edge) {
            return Err(SubstitutionError::InvalidConstruction(format!(
                "match morphism is incomplete: edge {:?} in n·M ⊔ K has no mapping",
                edge
            )));
        }
    }

    let match_morphism = BHypMorphism::new(
        nm_k.clone(),
        g.bhyp().clone(),
        match_nodes,
        match_edges,
    )
    .map_err(|e| SubstitutionError::InvalidConstruction(e.to_string()))?;

    println!("here! created matching");

    // Optional debug check.
    eprintln!("--- boundary consistency check ---");

    for (&middle_node, &left_node) in top_span.to_l.on_nodes() {
        let g_node = match_morphism.map_node(left_node);
        let right_node = top_span.to_r.map_node(middle_node);

        eprintln!(
            "middle {:?} -> left {:?} -> G {:?}; middle {:?} -> right {:?}",
            middle_node, left_node, g_node, middle_node, right_node
        );
    }

    // ---------------------------------------------------------------------
    // 8. Apply DPO.
    // ---------------------------------------------------------------------

    let result_span = dpo(&top_span, g.bhyp(), &match_morphism)
        .map_err(|e| {
            SubstitutionError::InvalidConstruction(format!("DPO Failed: {:?}", e))
        })?;

    println!("here! applied dpo");

    Ok(BHyp_with_interface::from_bhyp(result_span.right))
}

// pub fn apply_substitution(
//     g: &BHyp_with_interface,
//     subst: &Substitution,
//     shared: &Span, // I_G <- K -> I_T
// ) -> Result<BHyp_with_interface, SubstitutionError> {
    
//     // 1. Find all occurrences of M in G
//     let met = construct_meta_hypergraph(subst.meta_name.clone())
//         .map_err(|e| SubstitutionError::InvalidConstruction(e))?;
    
//     let occurrences = find_all_occurrences(&met, &g.bhyp());
//     let n = occurrences.len();
    
//     if n == 0 {
//         return Ok(g.clone());
//     }
    
//     let i_m = BHyp_with_interface::from_bhyp(met.clone());
    
//     // 2. Build n copies of M 
//     let empty_k = BHyp::new();
//     let empty_morphism = BHypMorphism::new(
//         empty_k.clone(),
//         met.clone(),
//         HashMap::new(), 
//         HashMap::new(),
//     ).map_err(|e| SubstitutionError::InvalidConstruction(e.to_string()))?;

//     let (n_m, _proj) = compute_n_copies_with_interface(
//         &i_m, 
//         n, 
//         Some((empty_k.clone(), empty_morphism))
//     ).map_err(|e| SubstitutionError::InvalidConstruction(format!("{:?}", e)))?;

//     // 3. Compute n T, glued at free vertices (I_T \ im(interface_map))
//     // 
//     // interface_map maps M's nodes -> T's internal nodes
//     // We need to find which T internal nodes are NOT in the image,
//     // then find their corresponding interface nodes for gluing.
    
//     let m_image_in_t: HashSet<NodeId> = subst.interface_map.values().cloned().collect();
    
//     // Build reverse maps: T internal node -> interface node
//     let mut t_node_to_input_iface: HashMap<NodeId, NodeId> = HashMap::new();
//     let mut t_node_to_output_iface: HashMap<NodeId, NodeId> = HashMap::new();
    
//     for (&iface_node, &t_node) in subst.replacement.input_map() {
//         t_node_to_input_iface.insert(t_node, iface_node);
//     }
//     for (&iface_node, &t_node) in subst.replacement.output_map() {
//         t_node_to_output_iface.insert(t_node, iface_node);
//     }
    
//     // Collect all T internal nodes that have interface mappings
//     let t_interface_internal_nodes: HashSet<NodeId> = subst.replacement.input_map()
//         .values()
//         .chain(subst.replacement.output_map().values())
//         .copied()
//         .collect();
    
//     // Build i_f: the free vertices (T internal nodes not in image of interface_map)
//     // These need to be glued across copies
//     let mut i_f = BHyp::new();
//     let mut i_f_map_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    
//     for &t_internal_node in &t_interface_internal_nodes {
//         if !m_image_in_t.contains(&t_internal_node) {
//             // This is a free vertex - add to gluing interface
//             let i_f_node = i_f.add_node();
//             i_f_map_nodes.insert(i_f_node, t_internal_node);
//         }
//     }

//     let kt_to_t = BHypMorphism::new(
//         i_f.clone(),
//         subst.replacement.bhyp().clone(),
//         i_f_map_nodes,
//         HashMap::new(), 
//     ).map_err(|e| SubstitutionError::InvalidConstruction(e.to_string()))?;

//     let (n_t_glued, _t_proj) = compute_n_copies_with_interface(
//         &subst.replacement,
//         n,
//         Some((i_f, kt_to_t))
//     ).map_err(|e| SubstitutionError::InvalidConstruction(format!("{:?}", e)))?;
        
//     // 4. Compute the objects for the top span n M + K <- n Im + K -> n T 
//     // n·I_M 
//     let nim_result = compute_coproduct(n_m.input_interface(), n_m.output_interface())
//         .map_err(|e| SubstitutionError::InvalidConstruction(format!("{:?}", e)))?;
//     let nim_graph = &nim_result.pushout;

//     // n·M ⊔ K
//     let nm_k_result = compute_coproduct(n_m.bhyp(), &shared.middle)
//         .map_err(|e| SubstitutionError::InvalidConstruction(format!("{:?}", e)))?;
//     let nm_k = &nm_k_result.pushout;

//     // n·I_M ⊔ K
//     let nim_k_result = compute_coproduct(nim_graph, &shared.middle)
//         .map_err(|e| SubstitutionError::InvalidConstruction(format!("{:?}", e)))?;
//     let nim_k = &nim_k_result.pushout;

//     // 5. Construct `to_l`: (n·I_M ⊔ K) -> (n·M ⊔ K)
//     let mut to_l_nodes = HashMap::new();
    
//     for (&nim_n, &nim_k_n) in nim_k_result.morphism_from_b.on_nodes() {
//         let nm_n = if let Some((&in_n, _)) = nim_result.morphism_from_b.on_nodes().iter().find(|(_, &v)| v == nim_n) {
//             n_m.input_map()[&in_n]
//         } else if let Some((&out_n, _)) = nim_result.morphism_from_c.on_nodes().iter().find(|(_, &v)| v == nim_n) {
//             n_m.output_map()[&out_n]
//         } else {
//             return Err(SubstitutionError::InvalidConstruction(
//                 format!("Node {:?} not found in nim_result mappings", nim_n)
//             ));
//         };
//         let final_nm_k_n = nm_k_result.morphism_from_b.map_node(nm_n)
//             .ok_or_else(|| SubstitutionError::InvalidConstruction(
//                 format!("Node {:?} has no mapping in nm_k_result", nm_n)
//             ))?;
//         to_l_nodes.insert(nim_k_n, final_nm_k_n);
//     }
    
//     for (&k_n, &nim_k_n) in nim_k_result.morphism_from_c.on_nodes() {
//         let final_nm_k_n = nm_k_result.morphism_from_c.map_node(k_n)
//             .ok_or_else(|| SubstitutionError::InvalidConstruction(
//                 format!("K node {:?} has no mapping in nm_k_result", k_n)
//             ))?;
//         to_l_nodes.insert(nim_k_n, final_nm_k_n);
//     }

//     let to_l_morph = BHypMorphism::new(nim_k.clone(), nm_k.clone(), to_l_nodes, HashMap::new())
//         .map_err(|e| SubstitutionError::InvalidConstruction(e.to_string()))?;

//     // 6. Construct `to_r`: (n·I_M ⊔ K) -> n·T̂
//     // 6. Construct `to_r`: (n·I_M ⊔ K) -> n·T̂
// let mut to_r_nodes = HashMap::new();

// // Find inclusions of T into n_t_glued
// let t_incl = find_all_occurrences(&subst.replacement.bhyp(), &n_t_glued.bhyp());

// if t_incl.len() != n {
//     return Err(SubstitutionError::InvalidConstruction(
//         format!("Expected {} occurrences of T in n_t_glued, found {}", n, t_incl.len())
//     ));
// }

// // We need to map: for each copy i, for each interface node of M,
// // find corresponding node in nim_k and map it to the corresponding node in n_t_glued

// // Get the single edge in met to find sources and targets
// let met_edge = *met.edges().iter().next().unwrap();
// let met_sources: Vec<NodeId> = met.get_sources(met_edge).unwrap();
// let met_targets: Vec<NodeId> = met.get_targets(met_edge).unwrap().clone();

// // Build a mapping from met node -> position and type (source idx or target idx)
// #[derive(Debug, Clone, Copy)]
// enum MetNodePosition {
//     Source(usize),
//     Target(usize),
// }

// let mut met_node_positions: HashMap<NodeId, MetNodePosition> = HashMap::new();
// for (idx, src) in met_sources.iter().enumerate() {
//     met_node_positions.insert(*src, MetNodePosition::Source(idx));
// }
// for (idx, tgt) in met_targets.iter().enumerate() {
//     met_node_positions.insert(*tgt, MetNodePosition::Target(idx));
// }

// // Now for each copy i
// for i in 0..n {
//     let t_inj = &t_incl[i];
    
//     // For each mapped node in interface_map
//     for (&m_node, &t_internal_node) in &subst.interface_map {
//         let pos = match met_node_positions.get(&m_node) {
//             Some(p) => p,
//             None => continue, // Not an interface node
//         };
        
//         // Find the corresponding node in nim for copy i
//         // This depends on how compute_n_copies_with_interface orders copies
//         // We need to use the projection morphisms from that function
        
//         // n_m.input_interface has nodes for all copies
//         // n_m.input_map maps interface_node -> n_m internal node
//         // We need to find the i-th copy's version of m_node
        
//         // The interface of i_m (single M) has certain nodes
//         // After n copies, n_m.input_interface has n times as many nodes
        
//         let i_m_input_nodes: Vec<NodeId> = i_m.input_interface().nodes().iter().copied().collect();
//         let i_m_output_nodes: Vec<NodeId> = i_m.output_interface().nodes().iter().copied().collect();
        
//         let nim_n = match pos {
//             MetNodePosition::Source(src_idx) => {
//                 // Find the interface node in i_m that maps to this source
//                 let i_m_iface_node = i_m_input_nodes.iter().find(|&&iface_n| {
//                     i_m.input_map().get(&iface_n) == Some(&m_node)
//                 });
                
//                 if let Some(&iface_n) = i_m_iface_node {
//                     // Now find the corresponding node in n_m for copy i
//                     // This is where we need the projection info
//                     // For now, assume nodes are ordered: copy 0's nodes, then copy 1's, etc.
//                     let n_m_input_nodes: Vec<NodeId> = n_m.input_interface().nodes().iter().copied().collect();
//                     let nodes_per_copy = i_m_input_nodes.len();
//                     let n_m_iface_node = n_m_input_nodes.get(i * nodes_per_copy + src_idx)ok_;
                    
//                     // Map through nim_result
//                     nim_result.morphism_from_b.map_node(*n_m_iface_node)
//                 } else {
//                     None
//                 }
//             }
//             MetNodePosition::Target(tgt_idx) => {
//                 let i_m_iface_node = i_m_output_nodes.iter().find(|&&iface_n| {
//                     i_m.output_map().get(&iface_n) == Some(&m_node)
//                 });
                
//                 if let Some(&iface_n) = i_m_iface_node {
//                     let n_m_output_nodes: Vec<NodeId> = n_m.output_interface().nodes().iter().copied().collect();
//                     let nodes_per_copy = i_m_output_nodes.len();
//                     let n_m_iface_node = n_m_output_nodes.get(i * nodes_per_copy + tgt_idx)?;
                    
//                     nim_result.morphism_from_c.map_node(*n_m_iface_node)
//                 } else {
//                     None
//                 }
//             }
//         };
        
//         if let Some(nim_n) = nim_n {
//             if let Some(nim_k_n) = nim_k_result.morphism_from_b.map_node(nim_n) {
//                 if let Some(nt_n) = t_inj.map_node(t_internal_node) {
//                     to_r_nodes.insert(nim_k_n, nt_n);
//                 }
//             }
//         }
//     }
// }

// // Map K nodes
// for (&k_n, &nim_k_n) in nim_k_result.morphism_from_c.on_nodes() {
//     let nt_n = shared.to_r.map_node(k_n)
//         .ok_or_else(|| SubstitutionError::InvalidConstruction(
//             format!("K node {:?} has no mapping in shared.to_r", k_n)
//         ))?;
//     to_r_nodes.insert(nim_k_n, nt_n);
// }



//     let to_r_morph = BHypMorphism::new(nim_k.clone(), n_t_glued.bhyp().clone(), to_r_nodes, HashMap::new())
//         .map_err(|e| SubstitutionError::InvalidConstruction(e.to_string()))?;

//     let top_span = Span {
//         left: nm_k.clone(),
//         middle: nim_k.clone(),
//         right: n_t_glued.bhyp().clone(),
//         to_l: to_l_morph,
//         to_r: to_r_morph
//     };

//     // 7. Construct matching morphism: n·M ⊔ K -> G
//     let mut match_nodes = HashMap::new();
//     let mut match_edges = HashMap::new();

//     for (&k_n, &nm_k_n) in nm_k_result.morphism_from_c.on_nodes() {
//         match_nodes.insert(nm_k_n, shared.to_l.map_node(k_n)
//             .ok_or_else(|| SubstitutionError::InvalidConstruction(
//                 format!("K node {:?} has no mapping in shared.to_l", k_n)
//             ))?);
//     }
//     for (&k_e, &nm_k_e) in nm_k_result.morphism_from_c.on_edges() {
//         match_edges.insert(nm_k_e, shared.to_l.map_edge(k_e)
//             .ok_or_else(|| SubstitutionError::InvalidConstruction(
//                 format!("K edge {:?} has no mapping in shared.to_l", k_e)
//             ))?);
//     }

//     for (_i, occ) in occurrences.iter().enumerate() {
//         for &m_n in occ.domain().nodes() {
//             let nm_n = occ.map_node(m_n).ok_or_else(|| SubstitutionError::InvalidConstruction(
//                 format!("M node {:?} has no mapping in occurrence", m_n)
//             ))?;
//             let nm_k_n = nm_k_result.morphism_from_b.map_node(nm_n)
//                 .ok_or_else(|| SubstitutionError::InvalidConstruction(
//                     format!("n_m node {:?} has no mapping in nm_k_result", nm_n)
//                 ))?;
//             match_nodes.insert(nm_k_n, occ.map_node(m_n).unwrap());
//         }
//         for &m_e in occ.domain().edges() {
//             let nm_e = occ.map_edge(m_e).ok_or_else(|| SubstitutionError::InvalidConstruction(
//                 format!("M edge {:?} has no mapping in occurrence", m_e)
//             ))?;
//             let nm_k_e = nm_k_result.morphism_from_b.map_edge(nm_e)
//                 .ok_or_else(|| SubstitutionError::InvalidConstruction(
//                     format!("n_m edge {:?} has no mapping in nm_k_result", nm_e)
//                 ))?;
//             match_edges.insert(nm_k_e, occ.map_edge(m_e).unwrap());
//         }
//     }

//     let match_morphism = BHypMorphism::new(nm_k.clone(), g.bhyp().clone(), match_nodes, match_edges)
//         .map_err(|e| SubstitutionError::InvalidConstruction(e.to_string()))?;

//     // 8. Apply DPO
//     let result_span = dpo(&top_span, g.bhyp(), &match_morphism)
//         .map_err(|e| SubstitutionError::InvalidConstruction(format!("DPO Failed: {:?}", e)))?;

//     Ok(BHyp_with_interface::from_bhyp(result_span.right))
// }

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

let t_in_iface = t_int
    .input_map()
    .iter()
    .find_map(|(&iface_node, &t_node)| {
        if t_node == t_in {
            Some(iface_node)
        } else {
            None
        }
    })
    .expect("could not find input interface node for t_in");

let t_out_iface = t_int
    .output_map()
    .iter()
    .find_map(|(&iface_node, &t_node)| {
        if t_node == t_out {
            Some(iface_node)
        } else {
            None
        }
    })
    .expect("could not find output interface node for t_out");

interface_map.insert(m_source, t_in_iface);
interface_map.insert(m_target, t_out_iface);


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

#[test]
fn test_copy_subst_commute() {
    // create G
    let mut g = BHyp::new();
    let m1 = g.add_node();
    let m2 = g.add_node();
    let mo = g.add_node();
    let g1 = g.add_node();
    let go1 = g.add_node();
    let go2 = g.add_node();

    g.add_edge(
        vec![SourceWithBinding { source: m1, bound: vec![] }, 
        SourceWithBinding { source: m2, bound: vec![] }],
        vec![mo],
        Some(Label::Meta("M".to_string(), 2)),
    ).unwrap();

    g.add_edge(
        vec![SourceWithBinding { source: mo, bound: vec![] }, 
        SourceWithBinding { source: g1, bound: vec![] }],
        vec![go2],
        Some(Label::Symbol("G2".to_string())),
    ).unwrap();

    g.add_edge(
        vec![SourceWithBinding { source: mo, bound: vec![] }],
        vec![go1],
        Some(Label::Symbol("G1".to_string())),
    ).unwrap();

    // create subhyp M (matching structure in G)
    let mut m = BHyp::new();
    let m_n1 = m.add_node();
    let m_n2 = m.add_node();
    let m_out = m.add_node();
    
    m.add_edge(
        vec![SourceWithBinding { source: m_n1, bound: vec![] }, 
        SourceWithBinding { source: m_n2, bound: vec![] }],
        vec![m_out],
        Some(Label::Meta("M".to_string(), 2)),
    ).unwrap();

    // create replacement T 
    let mut t = BHyp::new();
    let t1 = t.add_node();
    let t2 = t.add_node();
    let t3 = t.add_node();
    let t_out = t.add_node();
    
    t.add_edge(
        vec![SourceWithBinding {source: t1, bound: vec![]},
        SourceWithBinding {source: t2, bound: vec![]},
        SourceWithBinding {source: t3, bound: vec![]}], 
        vec![t_out], 
        Some(Label::Symbol("T".to_string())),
    ).unwrap();

    // Create T with interface
    let t_with_interface = BHyp_with_interface::from_bhyp(
        t.clone());

    // Create interface map: M's nodes -> T's nodes; on the interface level

// Get the interface nodes (not t1, t2, t_out directly!)
let t_input_interface_nodes: Vec<NodeId> = t_with_interface.input_interface().nodes().iter().copied().collect();
let t_output_interface_nodes: Vec<NodeId> = t_with_interface.output_interface().nodes().iter().copied().collect();

// Map met nodes to T's INTERFACE nodes
let met = construct_meta_hypergraph(Label::Meta("M".to_string(), 2)).unwrap();
let met_edge = met.edges().iter().next().unwrap();
let met_sources = met.get_sources(*met_edge).unwrap();
let met_targets = met.get_targets(*met_edge).unwrap();

let mut interface_map = HashMap::new();
// Need to find which interface nodes correspond to t1, t2, t_out
// by looking at input_map and output_map
for (&iface_node, &t_node) in t_with_interface.input_map() {
    if t_node == t1 {
        interface_map.insert(met_sources[0], iface_node);
    } else if t_node == t2 {
        interface_map.insert(met_sources[1], iface_node);
    }
}
for (&iface_node, &t_node) in t_with_interface.output_map() {
    if t_node == t_out {
        interface_map.insert(met_targets[0], iface_node);
    }
}

    // Create substitution
    let subst = Substitution::new(
        Label::Meta("M".to_string(), 2), 
        t_with_interface.clone()
    ).with_interface_map(interface_map);

    // Create shared span for copy_subhypergraph: G <- K -> M
    // Following the pattern from copy_simple_subhyp
    let mut k = BHyp::new();
    let k_node = k.add_node();

    // K -> G: maps k_node to mo (the shared output node in G)
    let to_l = BHypMorphism::new(
        k.clone(),
        g.clone(),
        [(k_node, mo)].into_iter().collect(),
        HashMap::new(),
    ).unwrap();

    // K -> M: maps k_node to m_out (the output node in M)
    let to_r = BHypMorphism::new(
        k.clone(),
        m.clone(),
        [(k_node, m_out)].into_iter().collect(),
        HashMap::new(),
    ).unwrap();

    let shared_span_for_copy = Span {
        left: g.clone(),
        middle: k.clone(),
        right: m.clone(),
        to_l,
        to_r,
    };

    // Verify out_degree for copying (should be 2: G1 and G2 edges)
    let n = g.out_degree(mo);
    assert_eq!(n, 2);

    // PATH 1: copy then substitute
    // copy_subhypergraph(g, m, shared_span) - copies M at shared output node mo
    let gm_copied = copy_subhypergraph(&g, &m, shared_span_for_copy).unwrap();

    assert_eq!(gm_copied.edges().len(), 4); // original 2 edges + 2 copies of M
    assert_eq!(gm_copied.nodes().len(), 7);

    // gm_copied should now have 2 copies of M
    // Create empty shared span for substitution
    let empty_k = BHyp::new();
    let empty_to_gm = BHypMorphism::new(empty_k.clone(), gm_copied.clone(), HashMap::new(), HashMap::new()).unwrap();
    let empty_to_t = BHypMorphism::new(empty_k.clone(), t.clone(), HashMap::new(), HashMap::new()).unwrap();
    
    let shared_span_for_subst_copied = Span {
        left: gm_copied.clone(),
        middle: empty_k.clone(),
        right: t.clone(),
        to_l: empty_to_gm.clone(),
        to_r: empty_to_t.clone(),
    };

    let gm_copied_with_interface = BHyp_with_interface::from_bhyp(gm_copied.clone());
    let path1_result = apply_substitution(&gm_copied_with_interface, &subst, &shared_span_for_subst_copied).unwrap();

    assert_eq!(path1_result.bhyp().edges().len(), 4); // original 2 edges + 2 copies of T
    assert_eq!(path1_result.bhyp().nodes().len(), 8); // todo: fix, free of T got copied

    // PATH 2: substitute then copy
    // apply_substitution(g, subst, shared_span) - replaces single M with T
    let empty_to_g = BHypMorphism::new(
        empty_k.clone(), 
        g.clone(), 
        HashMap::new(), 
        HashMap::new()).unwrap();
    
    let shared_span_for_subst = Span {
        left: g.clone(),
        middle: empty_k.clone(),
        right: t.clone(),
        to_l: empty_to_g,
        to_r: empty_to_t.clone(),
    };

    let g_with_interface = BHyp_with_interface::from_bhyp(g.clone());
    let g_substituted = apply_substitution(&g_with_interface, &subst, &shared_span_for_subst).unwrap();
    let g_subst_bhyp = g_substituted.bhyp();

    assert_eq!(g_subst_bhyp.edges().len(), 3); // original 2 edges, M replaced by T
    assert_eq!(g_subst_bhyp.nodes().len(), 7); // original

    // Find t_out in g_substituted (the target of the T-labeled edge)
    let t_edge_in_gs = g_subst_bhyp.edges().iter().find(|&e| {
        g_subst_bhyp.get_label(*e) == Some(&Label::Symbol("T".to_string()))
    }).unwrap();
    let t_out_in_gs = g_subst_bhyp.get_targets(*t_edge_in_gs).unwrap()[0];

assert_eq!(
    g_subst_bhyp.out_degree(t_out_in_gs),
    2,
    "T output was not glued to old M output / mo"
);


    // Create shared span for copying T in substituted graph
    let mut k_t = BHyp::new();
    let k_t_node = k_t.add_node();

    let to_l_t = BHypMorphism::new(
        k_t.clone(),
        g_subst_bhyp.clone(),
        [(k_t_node, t_out_in_gs)].into_iter().collect(),
        HashMap::new(),
    ).unwrap();

    let to_r_t = BHypMorphism::new(
        k_t.clone(),
        t.clone(),
        [(k_t_node, t_out)].into_iter().collect(),
        HashMap::new(),
    ).unwrap();

    let shared_span_for_copy_t = Span {
        left: g_subst_bhyp.clone(),
        middle: k_t,
        right: t.clone(),
        to_l: to_l_t,
        to_r: to_r_t,
    };

    // copy_subhypergraph(g_substituted, t, shared_span)
    let path2_result = copy_subhypergraph(&g_subst_bhyp, &t, shared_span_for_copy_t).unwrap();
    
    assert_eq!(path2_result.edges().len(), 4); // original 2 edges + 2 copies of T
    assert_eq!(path2_result.nodes().len(), 8); // todo: fix, free of T got copied

    // assert results are isomorphic
    assert!(are_isomorphic(&path1_result.bhyp(), &path2_result));
}

}



