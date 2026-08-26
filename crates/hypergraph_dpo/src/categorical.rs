// logical for categorical constructions
// morphisms,
// pushout complements, pushouts, DPO, etc.

// bhyp_categorical.rs
// Categorical operations module for BHyp: morphisms, pushouts, pushout complements, and DPO

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::bhyp::{BHyp, BHyp_with_interface, EdgeId, Label, NodeId, SourceWithBinding};

/// Error types for morphism construction
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MorphismError {
    /// A node in the domain is not mapped
    MissingNodeMapping(NodeId),
    /// An edge in the domain is not mapped
    MissingEdgeMapping(EdgeId),
    /// The mapping doesn't preserve sources
    IncompatibleSources(EdgeId),
    /// The mapping doesn't preserve targets
    IncompatibleTargets(EdgeId),
    /// The mapping doesn't preserve labels
    IncompatibleLabels(EdgeId),
    /// The mapping doesn't preserve binding structure
    IncompatibleBinding(EdgeId),
    /// Target node doesn't exist in codomain
    TargetNodeNotFound(NodeId),
    /// Target edge doesn't exist in codomain
    TargetEdgeNotFound(EdgeId),
}

impl fmt::Display for MorphismError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MorphismError::MissingNodeMapping(n) => write!(f, "Node {:?} has no mapping", n),
            MorphismError::MissingEdgeMapping(e) => write!(f, "Edge {:?} has no mapping", e),
            MorphismError::IncompatibleSources(e) => {
                write!(f, "Edge {:?} mapping doesn't preserve sources", e)
            }
            MorphismError::IncompatibleTargets(e) => {
                write!(f, "Edge {:?} mapping doesn't preserve targets", e)
            }
            MorphismError::IncompatibleLabels(e) => {
                write!(f, "Edge {:?} mapping doesn't preserve labels", e)
            }
            MorphismError::IncompatibleBinding(e) => {
                write!(f, "Edge {:?} mapping doesn't preserve binding", e)
            }
            MorphismError::TargetNodeNotFound(n) => {
                write!(f, "Target node {:?} not in codomain", n)
            }
            MorphismError::TargetEdgeNotFound(e) => {
                write!(f, "Target edge {:?} not in codomain", e)
            }
        }
    }
}

/// A morphism between two BHyp instances
/// Consists of a function on nodes and a function on edges that preserve structure
#[derive(Debug, Clone)]
pub struct BHypMorphism<'a> {
    /// The domain hypergraph
    domain: &'a BHyp,
    /// The codomain hypergraph
    codomain: &'a BHyp,
    /// Mapping from domain nodes to codomain nodes
    on_nodes: HashMap<NodeId, NodeId>,
    /// Mapping from domain edges to codomain edges
    on_edges: HashMap<EdgeId, EdgeId>,
}

impl<'a> BHypMorphism<'a> {
    /// Create a new morphism with validation
    pub fn new(
        domain: &'a BHyp,
        codomain: &'a BHyp,
        on_nodes: HashMap<NodeId, NodeId>,
        on_edges: HashMap<EdgeId, EdgeId>,
    ) -> Result<Self, MorphismError> {
        let morphism = BHypMorphism {
            domain,
            codomain,
            on_nodes,
            on_edges,
        };
        morphism.validate()?;
        Ok(morphism)
    }

    /// Create a morphism without validation (unsafe)
    pub fn new_unchecked(
        domain: &'a BHyp,
        codomain: &'a BHyp,
        on_nodes: HashMap<NodeId, NodeId>,
        on_edges: HashMap<EdgeId, EdgeId>,
    ) -> Self {
        BHypMorphism {
            domain,
            codomain,
            on_nodes,
            on_edges,
        }
    }

    /// Validate that this is a valid morphism
    pub fn validate(&self) -> Result<(), MorphismError> {
        // Check all domain nodes are mapped
        for &node in self.domain.nodes() {
            if !self.on_nodes.contains_key(&node) {
                return Err(MorphismError::MissingNodeMapping(node));
            }
            let target = self.on_nodes[&node];
            if !self.codomain.nodes().contains(&target) {
                return Err(MorphismError::TargetNodeNotFound(target));
            }
        }

        // Check all domain edges are mapped
        for &edge in self.domain.edges() {
            if !self.on_edges.contains_key(&edge) {
                return Err(MorphismError::MissingEdgeMapping(edge));
            }
            let target_edge = self.on_edges[&edge];
            if !self.codomain.edges().contains(&target_edge) {
                return Err(MorphismError::TargetEdgeNotFound(target_edge));
            }

            // Check source preservation
            if let (Some(dom_swbs), Some(cod_swbs)) = (
                self.domain.get_sources_with_binding(edge),
                self.codomain.get_sources_with_binding(target_edge),
            ) {
                if dom_swbs.len() != cod_swbs.len() {
                    return Err(MorphismError::IncompatibleSources(edge));
                }

                for (dom_swb, cod_swb) in dom_swbs.iter().zip(cod_swbs.iter()) {
                    // Check source node mapping
                    if self.on_nodes[&dom_swb.source] != cod_swb.source {
                        return Err(MorphismError::IncompatibleSources(edge));
                    }
                    // Check bound nodes mapping
                    if dom_swb.bound.len() != cod_swb.bound.len() {
                        return Err(MorphismError::IncompatibleBinding(edge));
                    }
                    for (dom_bound, cod_bound) in dom_swb.bound.iter().zip(cod_swb.bound.iter()) {
                        if self.on_nodes[dom_bound] != *cod_bound {
                            return Err(MorphismError::IncompatibleBinding(edge));
                        }
                    }
                }
            }

            // Check target preservation
            if let (Some(dom_targets), Some(cod_targets)) = (
                self.domain.get_targets(edge),
                self.codomain.get_targets(target_edge),
            ) {
                if dom_targets.len() != cod_targets.len() {
                    return Err(MorphismError::IncompatibleTargets(edge));
                }
                for (dom_t, cod_t) in dom_targets.iter().zip(cod_targets.iter()) {
                    if self.on_nodes[dom_t] != *cod_t {
                        return Err(MorphismError::IncompatibleTargets(edge));
                    }
                }
            }

            // Check label preservation
            match (
                self.domain.get_label(edge),
                self.codomain.get_label(target_edge),
            ) {
                (Some(l1), Some(l2)) if l1 != l2 => {
                    return Err(MorphismError::IncompatibleLabels(edge));
                }
                (Some(_), None) | (None, Some(_)) => {
                    return Err(MorphismError::IncompatibleLabels(edge));
                }
                _ => {}
            }
        }

        Ok(())
    }

    /// Get the domain
    pub fn domain(&self) -> &BHyp {
        self.domain
    }

    /// Get the codomain
    pub fn codomain(&self) -> &BHyp {
        self.codomain
    }

    /// Get the node mapping
    pub fn on_nodes(&self) -> &HashMap<NodeId, NodeId> {
        &self.on_nodes
    }

    /// Get the edge mapping
    pub fn on_edges(&self) -> &HashMap<EdgeId, EdgeId> {
        &self.on_edges
    }

    /// Apply the morphism to a node
    pub fn map_node(&self, node: NodeId) -> Option<NodeId> {
        self.on_nodes.get(&node).copied()
    }

    /// Apply the morphism to an edge
    pub fn map_edge(&self, edge: EdgeId) -> Option<EdgeId> {
        self.on_edges.get(&edge).copied()
    }

    /// Get the image of nodes under this morphism
    pub fn node_image(&self) -> HashSet<NodeId> {
        self.on_nodes.values().copied().collect()
    }

    /// Get the image of edges under this morphism
    pub fn edge_image(&self) -> HashSet<EdgeId> {
        self.on_edges.values().copied().collect()
    }
}

/// Properties of morphisms
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MorphismProperty {
    Monomorphism,
    Epimorphism,
    Isomorphism,
    Neither,
}

impl<'a> BHypMorphism<'a> {
    /// Check if this morphism is a monomorphism (injective on nodes and edges)
    pub fn is_monomorphism(&self) -> bool {
        // Check injectivity on nodes
        let node_values: Vec<_> = self.on_nodes.values().collect();
        let node_set: HashSet<_> = node_values.iter().collect();
        if node_values.len() != node_set.len() {
            return false;
        }

        // Check injectivity on edges
        let edge_values: Vec<_> = self.on_edges.values().collect();
        let edge_set: HashSet<_> = edge_values.iter().collect();
        edge_values.len() == edge_set.len()
    }

    /// Check if this morphism is an epimorphism (surjective on nodes and edges)
    pub fn is_epimorphism(&self) -> bool {
        // Check surjectivity on nodes
        let node_image = self.node_image();
        if node_image != *self.codomain.nodes() {
            return false;
        }

        // Check surjectivity on edges
        let edge_image = self.edge_image();
        edge_image == *self.codomain.edges()
    }

    /// Check if this morphism is an isomorphism (bijective)
    pub fn is_isomorphism(&self) -> bool {
        self.is_monomorphism() && self.is_epimorphism()
    }

    /// Classify the morphism type
    pub fn classify(&self) -> MorphismProperty {
        let mono = self.is_monomorphism();
        let epi = self.is_epimorphism();

        match (mono, epi) {
            (true, true) => MorphismProperty::Isomorphism,
            (true, false) => MorphismProperty::Monomorphism,
            (false, true) => MorphismProperty::Epimorphism,
            (false, false) => MorphismProperty::Neither,
        }
    }

    /// Check if this is the identity morphism
    pub fn is_identity(&self) -> bool {
        if !std::ptr::eq(self.domain, self.codomain) {
            return false;
        }
        self.on_nodes.iter().all(|(k, v)| k == v) && self.on_edges.iter().all(|(k, v)| k == v)
    }
}

/// Create the identity morphism on a BHyp
pub fn identity_morphism(bhyp: &BHyp) -> BHypMorphism {
    let on_nodes: HashMap<_, _> = bhyp.nodes().iter().map(|&n| (n, n)).collect();
    let on_edges: HashMap<_, _> = bhyp.edges().iter().map(|&e| (e, e)).collect();
    BHypMorphism::new_unchecked(bhyp, bhyp, on_nodes, on_edges)
}

/// Compose two morphisms: g ∘ f
pub fn compose<'a>(
    f: &BHypMorphism<'a>,
    g: &BHypMorphism<'a>,
    result_codomain: &'a BHyp,
) -> Result<BHypMorphism<'a>, MorphismError> {
    // f: A -> B, g: B -> C => g ∘ f: A -> C
    let on_nodes: HashMap<_, _> = f
        .on_nodes
        .iter()
        .filter_map(|(&k, &v)| g.on_nodes.get(&v).map(|&w| (k, w)))
        .collect();

    let on_edges: HashMap<_, _> = f
        .on_edges
        .iter()
        .filter_map(|(&k, &v)| g.on_edges.get(&v).map(|&w| (k, w)))
        .collect();

    BHypMorphism::new(f.domain, result_codomain, on_nodes, on_edges)
}

// ============================================================================
// Pushout and Pushout Complement
// ============================================================================

/// Result of a pushout computation
#[derive(Debug, Clone)]
pub struct PushoutResult {
    /// The pushout object (new hypergraph)
    pub pushout: BHyp,
    /// Mapping from first object's nodes to pushout nodes
    pub first_to_pushout_nodes: HashMap<NodeId, NodeId>,
    /// Mapping from second object's nodes to pushout nodes
    pub second_to_pushout_nodes: HashMap<NodeId, NodeId>,
    /// Mapping from first object's edges to pushout edges
    pub first_to_pushout_edges: HashMap<EdgeId, EdgeId>,
    /// Mapping from second object's edges to pushout edges
    pub second_to_pushout_edges: HashMap<EdgeId, EdgeId>,
}

/// Compute the pushout of two morphisms with a common domain
/// Given f: C -> A and g: C -> B, compute pushout P with morphisms A -> P and B -> P
///
/// ```text
///     C --f--> A
///     |        |
///     g        |
///     |        v
///     v        P
///     B ------>
/// ```
pub fn pushout(
    c: &BHyp,
    a: &BHyp,
    b: &BHyp,
    f_nodes: &HashMap<NodeId, NodeId>, // C -> A on nodes
    f_edges: &HashMap<EdgeId, EdgeId>, // C -> A on edges
    g_nodes: &HashMap<NodeId, NodeId>, // C -> B on nodes
    g_edges: &HashMap<EdgeId, EdgeId>, // C -> B on edges
) -> PushoutResult {
    let mut pushout = BHyp::new();

    // Create node mappings using union-find style equivalence classes
    // Nodes in A and B that come from the same node in C should be identified

    // Maps: original node -> representative in pushout
    let mut a_to_pushout_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    let mut b_to_pushout_nodes: HashMap<NodeId, NodeId> = HashMap::new();

    // First, handle nodes from C that map to both A and B - these get identified
    let mut identified_a_nodes: HashSet<NodeId> = HashSet::new();
    let mut identified_b_nodes: HashSet<NodeId> = HashSet::new();

    for &c_node in c.nodes() {
        if let (Some(&a_node), Some(&b_node)) = (f_nodes.get(&c_node), g_nodes.get(&c_node)) {
            // This node from C maps to both A and B, so identify them
            let p_node = pushout.add_node();
            a_to_pushout_nodes.insert(a_node, p_node);
            b_to_pushout_nodes.insert(b_node, p_node);
            identified_a_nodes.insert(a_node);
            identified_b_nodes.insert(b_node);
        }
    }

    // Add remaining nodes from A
    for &a_node in a.nodes() {
        if !identified_a_nodes.contains(&a_node) {
            let p_node = pushout.add_node();
            a_to_pushout_nodes.insert(a_node, p_node);
        }
    }

    // Add remaining nodes from B
    for &b_node in b.nodes() {
        if !identified_b_nodes.contains(&b_node) {
            let p_node = pushout.add_node();
            b_to_pushout_nodes.insert(b_node, p_node);
        }
    }

    // Handle edges similarly
    let mut a_to_pushout_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
    let mut b_to_pushout_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
    let mut identified_a_edges: HashSet<EdgeId> = HashSet::new();
    let mut identified_b_edges: HashSet<EdgeId> = HashSet::new();

    // Edges from C that map to both A and B get identified
    for &c_edge in c.edges() {
        if let (Some(&a_edge), Some(&b_edge)) = (f_edges.get(&c_edge), g_edges.get(&c_edge)) {
            // Transform the edge using the node mapping from A
            if let (Some(a_swbs), Some(a_targets)) =
                (a.get_sources_with_binding(a_edge), a.get_targets(a_edge))
            {
                let new_swbs: Vec<_> = a_swbs
                    .iter()
                    .map(|swb| SourceWithBinding {
                        source: a_to_pushout_nodes[&swb.source],
                        bound: swb
                            .bound
                            .iter()
                            .map(|&b| a_to_pushout_nodes[&b])
                            .collect(),
                    })
                    .collect();
                let new_targets: Vec<_> = a_targets
                    .iter()
                    .map(|&t| a_to_pushout_nodes[&t])
                    .collect();
                let label = a.get_label(a_edge).cloned();

                if let Ok(p_edge) = pushout.add_edge(new_swbs, new_targets, label) {
                    a_to_pushout_edges.insert(a_edge, p_edge);
                    b_to_pushout_edges.insert(b_edge, p_edge);
                    identified_a_edges.insert(a_edge);
                    identified_b_edges.insert(b_edge);
                }
            }
        }
    }

    // Add remaining edges from A
    for &a_edge in a.edges() {
        if !identified_a_edges.contains(&a_edge) {
            if let (Some(swbs), Some(targets)) =
                (a.get_sources_with_binding(a_edge), a.get_targets(a_edge))
            {
                let new_swbs: Vec<_> = swbs
                    .iter()
                    .map(|swb| SourceWithBinding {
                        source: a_to_pushout_nodes[&swb.source],
                        bound: swb
                            .bound
                            .iter()
                            .map(|&b| a_to_pushout_nodes[&b])
                            .collect(),
                    })
                    .collect();
                let new_targets: Vec<_> = targets.iter().map(|&t| a_to_pushout_nodes[&t]).collect();
                let label = a.get_label(a_edge).cloned();

                if let Ok(p_edge) = pushout.add_edge(new_swbs, new_targets, label) {
                    a_to_pushout_edges.insert(a_edge, p_edge);
                }
            }
        }
    }

    // Add remaining edges from B
    for &b_edge in b.edges() {
        if !identified_b_edges.contains(&b_edge) {
            if let (Some(swbs), Some(targets)) =
                (b.get_sources_with_binding(b_edge), b.get_targets(b_edge))
            {
                let new_swbs: Vec<_> = swbs
                    .iter()
                    .map(|swb| SourceWithBinding {
                        source: b_to_pushout_nodes[&swb.source],
                        bound: swb
                            .bound
                            .iter()
                            .map(|&b| b_to_pushout_nodes[&b])
                            .collect(),
                    })
                    .collect();
                let new_targets: Vec<_> = targets.iter().map(|&t| b_to_pushout_nodes[&t]).collect();
                let label = b.get_label(b_edge).cloned();

                if let Ok(p_edge) = pushout.add_edge(new_swbs, new_targets, label) {
                    b_to_pushout_edges.insert(b_edge, p_edge);
                }
            }
        }
    }

    PushoutResult {
        pushout,
        first_to_pushout_nodes: a_to_pushout_nodes,
        second_to_pushout_nodes: b_to_pushout_nodes,
        first_to_pushout_edges: a_to_pushout_edges,
        second_to_pushout_edges: b_to_pushout_edges,
    }
}

/// Error types for pushout complement
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PushoutComplementError {
    /// The morphism is not a monomorphism
    NotMonomorphism,
    /// Dangling edge condition violated
    DanglingEdge(EdgeId),
    /// Identification condition violated
    IdentificationViolated,
    /// No pushout complement exists
    NoComplement,
}

impl fmt::Display for PushoutComplementError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PushoutComplementError::NotMonomorphism => {
                write!(f, "Morphism must be a monomorphism")
            }
            PushoutComplementError::DanglingEdge(e) => {
                write!(f, "Dangling edge condition violated for {:?}", e)
            }
            PushoutComplementError::IdentificationViolated => {
                write!(f, "Identification condition violated")
            }
            PushoutComplementError::NoComplement => {
                write!(f, "No pushout complement exists")
            }
        }
    }
}

/// Result of pushout complement computation
#[derive(Debug, Clone)]
pub struct PushoutComplementResult {
    /// The pushout complement object
    pub complement: BHyp,
    /// Mapping from interface nodes to complement nodes
    pub interface_to_complement_nodes: HashMap<NodeId, NodeId>,
    /// Mapping from interface edges to complement edges
    pub interface_to_complement_edges: HashMap<EdgeId, EdgeId>,
    /// Mapping from complement nodes to original graph nodes
    pub complement_to_original_nodes: HashMap<NodeId, NodeId>,
    /// Mapping from complement edges to original graph edges
    pub complement_to_original_edges: HashMap<EdgeId, EdgeId>,
}

/// Compute pushout complement for DPO rewriting
///
/// Given:
/// - L: left-hand side of rule
/// - K: interface (shared part)
/// - G: host graph
/// - match: L -> G (matching morphism)
/// - l: K -> L (interface embedding)
///
/// Compute D such that:
/// ```text
///     K --l--> L
///     |        |
///     d        match
///     |        |
///     v   PO   v
///     D -----> G
/// ```
///
/// D = G - (match(L) - match(l(K)))
pub fn pushout_complement(
    k: &BHyp,                          // Interface
    l: &BHyp,                          // Left-hand side
    g: &BHyp,                          // Host graph
    l_nodes: &HashMap<NodeId, NodeId>, // K -> L on nodes
    l_edges: &HashMap<EdgeId, EdgeId>, // K -> L on edges
    match_nodes: &HashMap<NodeId, NodeId>, // L -> G on nodes
    match_edges: &HashMap<EdgeId, EdgeId>, // L -> G on edges
) -> Result<PushoutComplementResult, PushoutComplementError> {
    // Step 1: Compute the image of K in G via L
    let k_image_nodes: HashSet<NodeId> = k
        .nodes()
        .iter()
        .filter_map(|&kn| l_nodes.get(&kn).and_then(|&ln| match_nodes.get(&ln).copied()))
        .collect();

    let k_image_edges: HashSet<EdgeId> = k
        .edges()
        .iter()
        .filter_map(|&ke| l_edges.get(&ke).and_then(|&le| match_edges.get(&le).copied()))
        .collect();

    // Step 2: Compute the image of L in G
    let l_image_nodes: HashSet<NodeId> = match_nodes.values().copied().collect();
    let l_image_edges: HashSet<EdgeId> = match_edges.values().copied().collect();

    // Step 3: Nodes and edges to remove = L_image - K_image
    let nodes_to_remove: HashSet<NodeId> =
        l_image_nodes.difference(&k_image_nodes).copied().collect();
    let edges_to_remove: HashSet<EdgeId> =
        l_image_edges.difference(&k_image_edges).copied().collect();

    // Step 4: Check dangling condition
    // No edge in G - edges_to_remove should have a source or target in nodes_to_remove
    for &edge in g.edges() {
        if edges_to_remove.contains(&edge) {
            continue;
        }

        if let Some(swbs) = g.get_sources_with_binding(edge) {
            for swb in swbs {
                if nodes_to_remove.contains(&swb.source) {
                    return Err(PushoutComplementError::DanglingEdge(edge));
                }
                for &bound in &swb.bound {
                    if nodes_to_remove.contains(&bound) {
                        return Err(PushoutComplementError::DanglingEdge(edge));
                    }
                }
            }
        }

        if let Some(targets) = g.get_targets(edge) {
            for &target in targets {
                if nodes_to_remove.contains(&target) {
                    return Err(PushoutComplementError::DanglingEdge(edge));
                }
            }
        }
    }

    // Step 5: Build the complement D
    let mut complement = BHyp::new();

    // Nodes in D: G_nodes - nodes_to_remove
    let mut g_to_d_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    let mut d_to_g_nodes: HashMap<NodeId, NodeId> = HashMap::new();

    for &g_node in g.nodes() {
        if !nodes_to_remove.contains(&g_node) {
            let d_node = complement.add_node();
            g_to_d_nodes.insert(g_node, d_node);
            d_to_g_nodes.insert(d_node, g_node);
        }
    }

    // Edges in D: G_edges - edges_to_remove
    let mut g_to_d_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
    let mut d_to_g_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

    for &g_edge in g.edges() {
        if !edges_to_remove.contains(&g_edge) {
            if let (Some(swbs), Some(targets)) =
                (g.get_sources_with_binding(g_edge), g.get_targets(g_edge))
            {
                let new_swbs: Vec<_> = swbs
                    .iter()
                    .map(|swb| SourceWithBinding {
                        source: g_to_d_nodes[&swb.source],
                        bound: swb.bound.iter().map(|&b| g_to_d_nodes[&b]).collect(),
                    })
                    .collect();
                let new_targets: Vec<_> = targets.iter().map(|&t| g_to_d_nodes[&t]).collect();
                let label = g.get_label(g_edge).cloned();

                if let Ok(d_edge) = complement.add_edge(new_swbs, new_targets, label) {
                    g_to_d_edges.insert(g_edge, d_edge);
                    d_to_g_edges.insert(d_edge, g_edge);
                }
            }
        }
    }

    // Step 6: Build interface mapping K -> D
    let mut interface_to_d_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    let mut interface_to_d_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

    for &k_node in k.nodes() {
        if let Some(&l_node) = l_nodes.get(&k_node) {
            if let Some(&g_node) = match_nodes.get(&l_node) {
                if let Some(&d_node) = g_to_d_nodes.get(&g_node) {
                    interface_to_d_nodes.insert(k_node, d_node);
                }
            }
        }
    }

    for &k_edge in k.edges() {
        if let Some(&l_edge) = l_edges.get(&k_edge) {
            if let Some(&g_edge) = match_edges.get(&l_edge) {
                if let Some(&d_edge) = g_to_d_edges.get(&g_edge) {
                    interface_to_d_edges.insert(k_edge, d_edge);
                }
            }
        }
    }

    Ok(PushoutComplementResult {
        complement,
        interface_to_complement_nodes: interface_to_d_nodes,
        interface_to_complement_edges: interface_to_d_edges,
        complement_to_original_nodes: d_to_g_nodes,
        complement_to_original_edges: d_to_g_edges,
    })
}

// ============================================================================
// Double Pushout (DPO) Rewriting
// ============================================================================

/// A rewrite rule for DPO consisting of L <- K -> R
#[derive(Debug, Clone)]
pub struct RewriteRule {
    /// Left-hand side
    pub left: BHyp,
    /// Interface (kernel)
    pub interface: BHyp,
    /// Right-hand side
    pub right: BHyp,
    /// Morphism K -> L (on nodes)
    pub l_nodes: HashMap<NodeId, NodeId>,
    /// Morphism K -> L (on edges)
    pub l_edges: HashMap<EdgeId, EdgeId>,
    /// Morphism K -> R (on nodes)
    pub r_nodes: HashMap<NodeId, NodeId>,
    /// Morphism K -> R (on edges)
    pub r_edges: HashMap<EdgeId, EdgeId>,
}

impl RewriteRule {
    /// Create a new rewrite rule
    pub fn new(
        left: BHyp,
        interface: BHyp,
        right: BHyp,
        l_nodes: HashMap<NodeId, NodeId>,
        l_edges: HashMap<EdgeId, EdgeId>,
        r_nodes: HashMap<NodeId, NodeId>,
        r_edges: HashMap<EdgeId, EdgeId>,
    ) -> Self {
        RewriteRule {
            left,
            interface,
            right,
            l_nodes,
            l_edges,
            r_nodes,
            r_edges,
        }
    }
}

/// Result of DPO rewriting
#[derive(Debug, Clone)]
pub struct DPOResult {
    /// The resulting hypergraph H
    pub result: BHyp,
    /// Mapping from the right-hand side to the result
    pub right_to_result_nodes: HashMap<NodeId, NodeId>,
    pub right_to_result_edges: HashMap<EdgeId, EdgeId>,
    /// The intermediate graph D (pushout complement)
    pub complement: BHyp,
}

/// Apply DPO rewriting
///
/// ```text
///     L <--l-- K --r--> R
///     |        |        |
///   match      d        |
///     |        |        |
///     v   PO   v   PO   v
///     G <----- D -----> H
/// ```
pub fn dpo(
    rule: &RewriteRule,
    g: &BHyp,
    match_nodes: &HashMap<NodeId, NodeId>,
    match_edges: &HashMap<EdgeId, EdgeId>,
) -> Result<DPOResult, PushoutComplementError> {
    // Step 1: Compute pushout complement D
    let complement_result = pushout_complement(
        &rule.interface,
        &rule.left,
        g,
        &rule.l_nodes,
        &rule.l_edges,
        match_nodes,
        match_edges,
    )?;

    // Step 2: Compute pushout of K -> D and K -> R
    let pushout_result = pushout(
        &rule.interface,
        &complement_result.complement,
        &rule.right,
        &complement_result.interface_to_complement_nodes,
        &complement_result.interface_to_complement_edges,
        &rule.r_nodes,
        &rule.r_edges,
    );

    Ok(DPOResult {
        result: pushout_result.pushout,
        right_to_result_nodes: pushout_result.second_to_pushout_nodes,
        right_to_result_edges: pushout_result.second_to_pushout_edges,
        complement: complement_result.complement,
    })
}

// ============================================================================
// Additional Categorical Operations: Coproduct and Coequalizer
// ============================================================================

/// Result of coproduct computation
#[derive(Debug, Clone)]
pub struct CoproductResult {
    /// The coproduct object
    pub coproduct: BHyp,
    /// First injection (nodes)
    pub first_injection_nodes: HashMap<NodeId, NodeId>,
    /// First injection (edges)
    pub first_injection_edges: HashMap<EdgeId, EdgeId>,
    /// Second injection (nodes)
    pub second_injection_nodes: HashMap<NodeId, NodeId>,
    /// Second injection (edges)
    pub second_injection_edges: HashMap<EdgeId, EdgeId>,
}

/// Compute the coproduct (disjoint union) of two hypergraphs
pub fn coproduct(a: &BHyp, b: &BHyp) -> CoproductResult {
    let mut coprod = BHyp::new();

    let mut a_to_coprod_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    let mut b_to_coprod_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    let mut a_to_coprod_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
    let mut b_to_coprod_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

    // Add all nodes from A
    for &a_node in a.nodes() {
        let c_node = coprod.add_node();
        a_to_coprod_nodes.insert(a_node, c_node);
    }

    // Add all nodes from B
    for &b_node in b.nodes() {
        let c_node = coprod.add_node();
        b_to_coprod_nodes.insert(b_node, c_node);
    }

    // Add all edges from A
    for &a_edge in a.edges() {
        if let (Some(swbs), Some(targets)) = (a.get_sources_with_binding(a_edge), a.get_targets(a_edge))
        {
            let new_swbs: Vec<_> = swbs
                .iter()
                .map(|swb| SourceWithBinding {
                    source: a_to_coprod_nodes[&swb.source],
                    bound: swb
                        .bound
                        .iter()
                        .map(|&b| a_to_coprod_nodes[&b])
                        .collect(),
                })
                .collect();
            let new_targets: Vec<_> = targets
                .iter()
                .map(|&t| a_to_coprod_nodes[&t])
                .collect();
            let label = a.get_label(a_edge).cloned();

            if let Ok(c_edge) = coprod.add_edge(new_swbs, new_targets, label) {
                a_to_coprod_edges.insert(a_edge, c_edge);
            }
        }
    }

    // Add all edges from B
    for &b_edge in b.edges() {
        if let (Some(swbs), Some(targets)) = (b.get_sources_with_binding(b_edge), b.get_targets(b_edge))
        {
            let new_swbs: Vec<_> = swbs
                .iter()
                .map(|swb| SourceWithBinding {
                    source: b_to_coprod_nodes[&swb.source],
                    bound: swb
                        .bound
                        .iter()
                        .map(|&b| b_to_coprod_nodes[&b])
                        .collect(),
                })
                .collect();
            let new_targets: Vec<_> = targets
                .iter()
                .map(|&t| b_to_coprod_nodes[&t])
                .collect();
            let label = b.get_label(b_edge).cloned();

            if let Ok(c_edge) = coprod.add_edge(new_swbs, new_targets, label) {
                b_to_coprod_edges.insert(b_edge, c_edge);
            }
        }
    }

    CoproductResult {
        coproduct: coprod,
        first_injection_nodes: a_to_coprod_nodes,
        first_injection_edges: a_to_coprod_edges,
        second_injection_nodes: b_to_coprod_nodes,
        second_injection_edges: b_to_coprod_edges,
    }
}

/// Result of coequalizer computation
#[derive(Debug, Clone)]
pub struct CoequalizerResult {
    /// The coequalizer object
    pub coequalizer: BHyp,
    /// Mapping from the codomain to the coequalizer (nodes)
    pub projection_nodes: HashMap<NodeId, NodeId>,
    /// Mapping from the codomain to the coequalizer (edges)
    pub projection_edges: HashMap<EdgeId, EdgeId>,
}

/// Compute the coequalizer of two parallel morphisms f, g: A -> B
/// Returns h: B -> C such that h ∘ f = h ∘ g
pub fn coequalizer(
    _a: &BHyp,
    b: &BHyp,
    f_nodes: &HashMap<NodeId, NodeId>,
    f_edges: &HashMap<EdgeId, EdgeId>,
    g_nodes: &HashMap<NodeId, NodeId>,
    g_edges: &HashMap<EdgeId, EdgeId>,
) -> CoequalizerResult {
    // Build equivalence classes for nodes
    // Two nodes are equivalent if they are both images of some node in A under f and g

    let mut node_equiv: HashMap<NodeId, NodeId> = HashMap::new();

    // Initialize: each node is its own representative
    for &node in b.nodes() {
        node_equiv.insert(node, node);
    }

    // Union nodes that should be identified
    for (&_a_node, &f_node) in f_nodes {
        if let Some(&g_node) = g_nodes.get(&_a_node) {
            // f(a) and g(a) should be identified
            let f_rep = find_representative(&node_equiv, f_node);
            let g_rep = find_representative(&node_equiv, g_node);
            if f_rep != g_rep {
                // Union: make f_rep point to g_rep
                node_equiv.insert(f_rep, g_rep);
            }
        }
    }

    // Build similar equivalence for edges
    let mut edge_equiv: HashMap<EdgeId, EdgeId> = HashMap::new();
    for &edge in b.edges() {
        edge_equiv.insert(edge, edge);
    }

    for (&_a_edge, &f_edge) in f_edges {
        if let Some(&g_edge) = g_edges.get(&_a_edge) {
            let f_rep = find_representative_edge(&edge_equiv, f_edge);
            let g_rep = find_representative_edge(&edge_equiv, g_edge);
            if f_rep != g_rep {
                edge_equiv.insert(f_rep, g_rep);
            }
        }
    }

    // Build the coequalizer
    let mut coeq = BHyp::new();
    let mut b_to_coeq_nodes: HashMap<NodeId, NodeId> = HashMap::new();
    let mut b_to_coeq_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

    // Create nodes for each equivalence class
    let mut rep_to_coeq: HashMap<NodeId, NodeId> = HashMap::new();
    for &b_node in b.nodes() {
        let rep = find_representative(&node_equiv, b_node);
        if !rep_to_coeq.contains_key(&rep) {
            let c_node = coeq.add_node();
            rep_to_coeq.insert(rep, c_node);
        }
        b_to_coeq_nodes.insert(b_node, rep_to_coeq[&rep]);
    }

    // Create edges (only for representative edges)
    let mut rep_edge_to_coeq: HashMap<EdgeId, EdgeId> = HashMap::new();
    for &b_edge in b.edges() {
        let rep = find_representative_edge(&edge_equiv, b_edge);
        if !rep_edge_to_coeq.contains_key(&rep) {
            // Only process the representative edge
            if let (Some(swbs), Some(targets)) =
                (b.get_sources_with_binding(rep), b.get_targets(rep))
            {
                let new_swbs: Vec<_> = swbs
                    .iter()
                    .map(|swb| SourceWithBinding {
                        source: b_to_coeq_nodes[&swb.source],
                        bound: swb
                            .bound
                            .iter()
                            .map(|&bn| b_to_coeq_nodes[&bn])
                            .collect(),
                    })
                    .collect();
                let new_targets: Vec<_> = targets
                    .iter()
                    .map(|&t| b_to_coeq_nodes[&t])
                    .collect();
                let label = b.get_label(rep).cloned();

                if let Ok(c_edge) = coeq.add_edge(new_swbs, new_targets, label) {
                    rep_edge_to_coeq.insert(rep, c_edge);
                }
            }
        }
        b_to_coeq_edges.insert(b_edge, rep_edge_to_coeq[&rep]);
    }

    CoequalizerResult {
        coequalizer: coeq,
        projection_nodes: b_to_coeq_nodes,
        projection_edges: b_to_coeq_edges,
    }
}

fn find_representative(equiv: &HashMap<NodeId, NodeId>, node: NodeId) -> NodeId {
    let mut current = node;
    while equiv.get(&current).copied() != Some(current) {
        if let Some(&next) = equiv.get(&current) {
            current = next;
        } else {
            break;
        }
    }
    current
}

fn find_representative_edge(equiv: &HashMap<EdgeId, EdgeId>, edge: EdgeId) -> EdgeId {
    let mut current = edge;
    while equiv.get(&current).copied() != Some(current) {
        if let Some(&next) = equiv.get(&current) {
            current = next;
        } else {
            break;
        }
    }
    current
}

// ============================================================================
// Convex Match Check
// ============================================================================

/// Check if a matching is convex
/// A match is convex if every path in the codomain between two nodes in the image
/// lies entirely within the image
pub fn is_convex_match(
    domain: &BHyp,
    codomain: &BHyp,
    match_nodes: &HashMap<NodeId, NodeId>,
    match_edges: &HashMap<EdgeId, EdgeId>,
) -> bool {
    // First check that the match is injective (mono)
    let node_values: HashSet<_> = match_nodes.values().collect();
    if node_values.len() != match_nodes.len() {
        return false;
    }

    let edge_values: HashSet<_> = match_edges.values().collect();
    if edge_values.len() != match_edges.len() {
        return false;
    }

    let image_nodes: HashSet<NodeId> = match_nodes.values().copied().collect();
    let image_edges: HashSet<EdgeId> = match_edges.values().copied().collect();

    // Check that all paths between image nodes stay within the image
    for &start in &image_nodes {
        for &end in &image_nodes {
            if start == end {
                continue;
            }
            // Find all paths from start to end in codomain
            // Check that all edges on these paths are in the image
            if !all_paths_in_image(codomain, start, end, &image_nodes, &image_edges) {
                return false;
            }
        }
    }

    true
}

/// Check if all paths between two nodes stay within the image
fn all_paths_in_image(
    graph: &BHyp,
    start: NodeId,
    end: NodeId,
    image_nodes: &HashSet<NodeId>,
    image_edges: &HashSet<EdgeId>,
) -> bool {
    // DFS to find paths and check they stay in image
    fn dfs(
        graph: &BHyp,
        current: NodeId,
        end: NodeId,
        visited: &mut HashSet<NodeId>,
        image_nodes: &HashSet<NodeId>,
        image_edges: &HashSet<EdgeId>,
    ) -> bool {
        if current == end {
            return true;
        }

        if visited.contains(&current) {
            return true; // Already processed this node
        }
        visited.insert(current);

        // Find edges starting from current
        for &edge in graph.edges() {
            if let Some(sources) = graph.get_sources(edge) {
                if sources.contains(&current) {
                    // This edge starts at current
                    // If we're in the image, the edge must be in the image too
                    if image_nodes.contains(&current) && !image_edges.contains(&edge) {
                        // Found a path that exits the image - check if it leads back
                        if let Some(targets) = graph.get_targets(edge) {
                            for &target in targets {
                                if image_nodes.contains(&target) {
                                    // Path exits and re-enters image - not convex
                                    return false;
                                }
                            }
                        }
                    }

                    // Continue DFS through targets
                    if let Some(targets) = graph.get_targets(edge) {
                        for &target in targets {
                            if !dfs(graph, target, end, visited, image_nodes, image_edges) {
                                return false;
                            }
                        }
                    }
                }
            }
        }

        true
    }

    let mut visited = HashSet::new();
    dfs(graph, start, end, &mut visited, image_nodes, image_edges)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_morphism_creation() {
        let mut g1 = BHyp::new();
        let n1 = g1.add_node();
        let n2 = g1.add_node();
        g1.add_edge(
            vec![SourceWithBinding {
                source: n1,
                bound: vec![],
            }],
            vec![n2],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        let mut g2 = BHyp::new();
        let m1 = g2.add_node();
        let m2 = g2.add_node();
        let m3 = g2.add_node();
        g2.add_edge(
            vec![SourceWithBinding {
                source: m1,
                bound: vec![],
            }],
            vec![m2],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        // Create an injective morphism g1 -> g2
        let on_nodes: HashMap<_, _> = [(n1, m1), (n2, m2)].into_iter().collect();
        let on_edges: HashMap<_, _> = [(EdgeId(0), EdgeId(0))].into_iter().collect();

        let morphism = BHypMorphism::new(&g1, &g2, on_nodes, on_edges).unwrap();

        assert!(morphism.is_monomorphism());
        assert!(!morphism.is_epimorphism()); // m3 is not in image
    }

    #[test]
    fn test_isomorphism() {
        let mut g1 = BHyp::new();
        let n1 = g1.add_node();
        let n2 = g1.add_node();
        g1.add_edge(
            vec![SourceWithBinding {
                source: n1,
                bound: vec![],
            }],
            vec![n2],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        let mut g2 = BHyp::new();
        let m1 = g2.add_node();
        let m2 = g2.add_node();
        g2.add_edge(
            vec![SourceWithBinding {
                source: m1,
                bound: vec![],
            }],
            vec![m2],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        let on_nodes: HashMap<_, _> = [(n1, m1), (n2, m2)].into_iter().collect();
        let on_edges: HashMap<_, _> = [(EdgeId(0), EdgeId(0))].into_iter().collect();

        let morphism = BHypMorphism::new(&g1, &g2, on_nodes, on_edges).unwrap();

        assert!(morphism.is_isomorphism());
        assert_eq!(morphism.classify(), MorphismProperty::Isomorphism);
    }

    #[test]
    fn test_pushout_simple() {
        // Create a simple span C <- A -> B
        // C: single node
        let mut c = BHyp::new();
        let c_node = c.add_node();

        // A: two nodes with edge
        let mut a = BHyp::new();
        let a1 = a.add_node();
        let a2 = a.add_node();
        a.add_edge(
            vec![SourceWithBinding {
                source: a1,
                bound: vec![],
            }],
            vec![a2],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        // B: two nodes with edge
        let mut b = BHyp::new();
        let b1 = b.add_node();
        let b2 = b.add_node();
        b.add_edge(
            vec![SourceWithBinding {
                source: b1,
                bound: vec![],
            }],
            vec![b2],
            Some(Label::Symbol("g".to_string())),
        )
        .unwrap();

        // Morphisms: c_node maps to a1 and b1
        let f_nodes: HashMap<_, _> = [(c_node, a1)].into_iter().collect();
        let f_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
        let g_nodes: HashMap<_, _> = [(c_node, b1)].into_iter().collect();
        let g_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

        let result = pushout(&c, &a, &b, &f_nodes, &f_edges, &g_nodes, &g_edges);

        // Pushout should have 3 nodes (a1=b1 identified, a2, b2)
        assert_eq!(result.pushout.nodes().len(), 3);
        // Pushout should have 2 edges
        assert_eq!(result.pushout.edges().len(), 2);
    }

    #[test]
    fn test_coproduct() {
        let mut a = BHyp::new();
        let a1 = a.add_node();
        let a2 = a.add_node();
        a.add_edge(
            vec![SourceWithBinding {
                source: a1,
                bound: vec![],
            }],
            vec![a2],
            None,
        )
        .unwrap();

        let mut b = BHyp::new();
        let b1 = b.add_node();

        let result = coproduct(&a, &b);

        // Coproduct should have 3 nodes
        assert_eq!(result.coproduct.nodes().len(), 3);
        // Coproduct should have 1 edge
        assert_eq!(result.coproduct.edges().len(), 1);

        // Check injections are defined
        assert!(result.first_injection_nodes.contains_key(&a1));
        assert!(result.first_injection_nodes.contains_key(&a2));
        assert!(result.second_injection_nodes.contains_key(&b1));
    }

    #[test]
    fn test_pushout_complement_simple() {
        // Create a simple example
        // K: single node (interface)
        let mut k = BHyp::new();
        let k_node = k.add_node();

        // L: two nodes with edge (left-hand side)
        let mut l = BHyp::new();
        let l1 = l.add_node();
        let l2 = l.add_node();
        l.add_edge(
            vec![SourceWithBinding {
                source: l1,
                bound: vec![],
            }],
            vec![l2],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        // G: three nodes, two edges (host graph)
        let mut g = BHyp::new();
        let g1 = g.add_node();
        let g2 = g.add_node();
        let g3 = g.add_node();
        g.add_edge(
            vec![SourceWithBinding {
                source: g1,
                bound: vec![],
            }],
            vec![g2],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();
        g.add_edge(
            vec![SourceWithBinding {
                source: g1,
                bound: vec![],
            }],
            vec![g3],
            Some(Label::Symbol("h".to_string())),
        )
        .unwrap();

        // K -> L: k_node maps to l1
        let l_nodes: HashMap<_, _> = [(k_node, l1)].into_iter().collect();
        let l_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

        // L -> G: l1 -> g1, l2 -> g2
        let match_nodes: HashMap<_, _> = [(l1, g1), (l2, g2)].into_iter().collect();
        let match_edges: HashMap<_, _> = [(EdgeId(0), EdgeId(0))].into_iter().collect();

        let result =
            pushout_complement(&k, &l, &g, &l_nodes, &l_edges, &match_nodes, &match_edges).unwrap();

        // Complement should have 2 nodes (g1 preserved via k, g3 stays, g2 removed)
        assert_eq!(result.complement.nodes().len(), 2);
        // Complement should have 1 edge (the h edge stays)
        assert_eq!(result.complement.edges().len(), 1);
    }

    #[test]
    fn test_dpo_simple() {
        // Simple rule: f -> g
        // K: single node
        let mut k = BHyp::new();
        let k_node = k.add_node();

        // L: two nodes with f edge
        let mut l = BHyp::new();
        let l1 = l.add_node();
        let l2 = l.add_node();
        l.add_edge(
            vec![SourceWithBinding {
                source: l1,
                bound: vec![],
            }],
            vec![l2],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        // R: two nodes with g edge
        let mut r = BHyp::new();
        let r1 = r.add_node();
        let r2 = r.add_node();
        r.add_edge(
            vec![SourceWithBinding {
                source: r1,
                bound: vec![],
            }],
            vec![r2],
            Some(Label::Symbol("g".to_string())),
        )
        .unwrap();

        let rule = RewriteRule::new(
            l.clone(),
            k.clone(),
            r.clone(),
            [(k_node, l1)].into_iter().collect(),
            HashMap::new(),
            [(k_node, r1)].into_iter().collect(),
            HashMap::new(),
        );

        // G: same as L
        let mut g = BHyp::new();
        let g1 = g.add_node();
        let g2 = g.add_node();
        g.add_edge(
            vec![SourceWithBinding {
                source: g1,
                bound: vec![],
            }],
            vec![g2],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();

        let match_nodes: HashMap<_, _> = [(l1, g1), (l2, g2)].into_iter().collect();
        let match_edges: HashMap<_, _> = [(EdgeId(0), EdgeId(0))].into_iter().collect();

        let result = dpo(&rule, &g, &match_nodes, &match_edges).unwrap();

        // Result should have 2 nodes
        assert_eq!(result.result.nodes().len(), 2);
        // Result should have 1 edge labeled "g"
        assert_eq!(result.result.edges().len(), 1);

        let edge = result.result.edges().iter().next().unwrap();
        assert_eq!(
            result.result.get_label(*edge),
            Some(&Label::Symbol("g".to_string()))
        );
    }
}