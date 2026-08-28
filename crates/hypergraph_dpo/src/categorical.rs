// implementation for categorical constructions
// morphisms,
// pushout complements, pushouts, DPO, etc.


use std::collections::{HashMap, HashSet};
use std::fmt;

// Assuming these are imported from the bhyp module
use crate::bhyp::{BHyp, EdgeId, Label, NodeId, SourceWithBinding};

/// Error types for morphism construction
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MorphismError {
    MissingNodeMapping(NodeId),
    MissingEdgeMapping(EdgeId),
    IncompatibleSources(EdgeId),
    IncompatibleTargets(EdgeId),
    IncompatibleLabels(EdgeId),
    IncompatibleBinding(EdgeId),
    TargetNodeNotFound(NodeId),
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

/// Error types for categorical constructions
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CategoricalError {
    MorphismError(MorphismError),
    /// Pushout complement doesn't exist (gluing condition violated)
    GluingConditionViolated(String),
    /// Identification condition violated
    IdentificationConditionViolated(String),
    /// Dangling condition violated
    DanglingConditionViolated(String),
    /// Morphisms don't share the same domain
    DomainMismatch,
    /// Morphisms don't share the same codomain
    CodomainMismatch,
    /// General construction failure
    ConstructionFailed(String),
}

impl fmt::Display for CategoricalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CategoricalError::MorphismError(e) => write!(f, "Morphism error: {}", e),
            CategoricalError::GluingConditionViolated(s) => {
                write!(f, "Gluing condition violated: {}", s)
            }
            CategoricalError::IdentificationConditionViolated(s) => {
                write!(f, "Identification condition violated: {}", s)
            }
            CategoricalError::DanglingConditionViolated(s) => {
                write!(f, "Dangling condition violated: {}", s)
            }
            CategoricalError::DomainMismatch => write!(f, "Morphisms don't share the same domain"),
            CategoricalError::CodomainMismatch => {
                write!(f, "Morphisms don't share the same codomain")
            }
            CategoricalError::ConstructionFailed(s) => write!(f, "Construction failed: {}", s),
        }
    }
}

impl From<MorphismError> for CategoricalError {
    fn from(e: MorphismError) -> Self {
        CategoricalError::MorphismError(e)
    }
}

/// A morphism between two BHyp instances
#[derive(Debug, Clone)]
pub struct BHypMorphism {
    /// The domain hypergraph (owned)
    domain: BHyp,
    /// The codomain hypergraph (owned)
    codomain: BHyp,
    /// Mapping from domain nodes to codomain nodes
    on_nodes: HashMap<NodeId, NodeId>,
    /// Mapping from domain edges to codomain edges
    on_edges: HashMap<EdgeId, EdgeId>,
}

impl BHypMorphism {
    /// Create a new morphism with validation
    pub fn new(
        domain: BHyp,
        codomain: BHyp,
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
        domain: BHyp,
        codomain: BHyp,
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
                    if self.on_nodes[&dom_swb.source] != cod_swb.source {
                        return Err(MorphismError::IncompatibleSources(edge));
                    }
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

    pub fn domain(&self) -> &BHyp {
        &self.domain
    }

    pub fn codomain(&self) -> &BHyp {
        &self.codomain
    }

    pub fn on_nodes(&self) -> &HashMap<NodeId, NodeId> {
        &self.on_nodes
    }

    pub fn on_edges(&self) -> &HashMap<EdgeId, EdgeId> {
        &self.on_edges
    }

    pub fn map_node(&self, node: NodeId) -> Option<NodeId> {
        self.on_nodes.get(&node).copied()
    }

    pub fn map_edge(&self, edge: EdgeId) -> Option<EdgeId> {
        self.on_edges.get(&edge).copied()
    }

    pub fn node_image(&self) -> HashSet<NodeId> {
        self.on_nodes.values().copied().collect()
    }

    pub fn edge_image(&self) -> HashSet<EdgeId> {
        self.on_edges.values().copied().collect()
    }

    /// Check if this morphism is a monomorphism (injective on nodes and edges)
    pub fn is_monomorphism(&self) -> bool {
        let node_values: Vec<_> = self.on_nodes.values().collect();
        let node_set: HashSet<_> = node_values.iter().collect();
        if node_values.len() != node_set.len() {
            return false;
        }

        let edge_values: Vec<_> = self.on_edges.values().collect();
        let edge_set: HashSet<_> = edge_values.iter().collect();
        edge_values.len() == edge_set.len()
    }

    /// Check if this morphism is an epimorphism (surjective on nodes and edges)
    pub fn is_epimorphism(&self) -> bool {
        let node_image = self.node_image();
        if node_image != *self.codomain.nodes() {
            return false;
        }

        let edge_image = self.edge_image();
        edge_image == *self.codomain.edges()
    }

    /// Check if this morphism is an isomorphism (bijective)
    pub fn is_isomorphism(&self) -> bool {
        self.is_monomorphism() && self.is_epimorphism()
    }

    /// Check if this is the identity morphism
    pub fn is_identity(&self) -> bool {
        // Check same structure
        if self.domain.nodes().len() != self.codomain.nodes().len() {
            return false;
        }
        if self.domain.edges().len() != self.codomain.edges().len() {
            return false;
        }
        self.on_nodes.iter().all(|(k, v)| k == v) && self.on_edges.iter().all(|(k, v)| k == v)
    }
}

/// Create the identity morphism on a BHyp
pub fn identity_morphism(bhyp: &BHyp) -> BHypMorphism {
    let on_nodes: HashMap<_, _> = bhyp.nodes().iter().map(|&n| (n, n)).collect();
    let on_edges: HashMap<_, _> = bhyp.edges().iter().map(|&e| (e, e)).collect();
    BHypMorphism::new_unchecked(bhyp.clone(), bhyp.clone(), on_nodes, on_edges)
}


// ============================================================================
// Pushout and Pushout Complement
// ============================================================================


/// Result of a pushout computation
#[derive(Debug, Clone)]
pub struct PushoutResult {
    /// The pushout object D
    pub pushout: BHyp,
    /// Universal morphism from B to D
    pub morphism_from_b: BHypMorphism,
    /// Universal morphism from C to D
    pub morphism_from_c: BHypMorphism,
}

/// Result of a pullback computation
#[derive(Debug, Clone)]
pub struct PullbackResult {
    /// The pullback object P
    pub pullback: BHyp,
    /// Universal morphism from P to B
    pub morphism_to_b: BHypMorphism,
    /// Universal morphism from P to C
    pub morphism_to_c: BHypMorphism,
}

/// Result of a pushout complement computation
#[derive(Debug, Clone)]
pub struct PushoutComplementResult {
    /// The pushout complement object C
    pub complement: BHyp,
    /// Morphism from A to C
    pub morphism_from_a: BHypMorphism,
    /// Morphism from C to B
    pub morphism_to_b: BHypMorphism,
}

/// Compute the pushout of two morphisms f: A -> B and g: A -> C
/// Returns the pushout D together with morphisms B -> D and C -> D
///
/// ```
///     A ---f---> B
///     |          |
///     g          g'
///     |          |
///     v          v
///     C ---f'--> D
/// ```
pub fn compute_pushout(
    f: &BHypMorphism,
    g: &BHypMorphism,
) -> Result<PushoutResult, CategoricalError> {
    // Verify f and g have the same domain
    if f.domain.nodes() != g.domain.nodes() || f.domain.edges() != g.domain.edges() {
        return Err(CategoricalError::DomainMismatch);
    }

    let mut pushout = BHyp::new();

    // Track node equivalences: nodes in B and C that come from the same node in A
    // We use union-find style equivalence classes

    // Create a mapping for all nodes
    // Key: (source, node_id) where source is 'B' or 'C'
    // Value: node id in the pushout
    let mut node_to_pushout: HashMap<(char, NodeId), NodeId> = HashMap::new();

    // First, identify nodes from A in both B and C
    let mut equivalences: Vec<((char, NodeId), (char, NodeId))> = Vec::new();
    for &a_node in f.domain.nodes() {
        let b_node = f.map_node(a_node).unwrap();
        let c_node = g.map_node(a_node).unwrap();
        equivalences.push((('B', b_node), ('C', c_node)));
    }

    // Build equivalence classes using union-find
    let mut parent: HashMap<(char, NodeId), (char, NodeId)> = HashMap::new();

    fn find(
        parent: &mut HashMap<(char, NodeId), (char, NodeId)>,
        x: (char, NodeId),
    ) -> (char, NodeId) {
        if !parent.contains_key(&x) {
            parent.insert(x, x);
            return x;
        }
        if parent[&x] == x {
            return x;
        }
        let root = find(parent, parent[&x]);
        parent.insert(x, root);
        root
    }

    fn union(
        parent: &mut HashMap<(char, NodeId), (char, NodeId)>,
        x: (char, NodeId),
        y: (char, NodeId),
    ) {
        let rx = find(parent, x);
        let ry = find(parent, y);
        if rx != ry {
            parent.insert(rx, ry);
        }
    }

    // Initialize all nodes
    for &node in f.codomain.nodes() {
        parent.insert(('B', node), ('B', node));
    }
    for &node in g.codomain.nodes() {
        parent.insert(('C', node), ('C', node));
    }

    // Apply equivalences
    for (x, y) in equivalences {
        union(&mut parent, x, y);
    }

    // Create pushout nodes for each equivalence class
    let mut class_to_pushout_node: HashMap<(char, NodeId), NodeId> = HashMap::new();

    for &node in f.codomain.nodes() {
        let root = find(&mut parent, ('B', node));
        if !class_to_pushout_node.contains_key(&root) {
            let pushout_node = pushout.add_node();
            class_to_pushout_node.insert(root, pushout_node);
        }
        node_to_pushout.insert(('B', node), class_to_pushout_node[&root]);
    }

    for &node in g.codomain.nodes() {
        let root = find(&mut parent, ('C', node));
        if !class_to_pushout_node.contains_key(&root) {
            let pushout_node = pushout.add_node();
            class_to_pushout_node.insert(root, pushout_node);
        }
        node_to_pushout.insert(('C', node), class_to_pushout_node[&root]);
    }

    // Similarly for edges
    let mut edge_to_pushout: HashMap<(char, EdgeId), EdgeId> = HashMap::new();
    let mut edge_equivalences: Vec<((char, EdgeId), (char, EdgeId))> = Vec::new();

    for &a_edge in f.domain.edges() {
        let b_edge = f.map_edge(a_edge).unwrap();
        let c_edge = g.map_edge(a_edge).unwrap();
        edge_equivalences.push((('B', b_edge), ('C', c_edge)));
    }

    let mut edge_parent: HashMap<(char, EdgeId), (char, EdgeId)> = HashMap::new();

    fn find_edge(
        parent: &mut HashMap<(char, EdgeId), (char, EdgeId)>,
        x: (char, EdgeId),
    ) -> (char, EdgeId) {
        if !parent.contains_key(&x) {
            parent.insert(x, x);
            return x;
        }
        if parent[&x] == x {
            return x;
        }
        let root = find_edge(parent, parent[&x]);
        parent.insert(x, root);
        root
    }

    fn union_edge(
        parent: &mut HashMap<(char, EdgeId), (char, EdgeId)>,
        x: (char, EdgeId),
        y: (char, EdgeId),
    ) {
        let rx = find_edge(parent, x);
        let ry = find_edge(parent, y);
        if rx != ry {
            parent.insert(rx, ry);
        }
    }

    for &edge in f.codomain.edges() {
        edge_parent.insert(('B', edge), ('B', edge));
    }
    for &edge in g.codomain.edges() {
        edge_parent.insert(('C', edge), ('C', edge));
    }

    for (x, y) in edge_equivalences {
        union_edge(&mut edge_parent, x, y);
    }

    // Create pushout edges for each equivalence class
    let mut class_to_pushout_edge: HashMap<(char, EdgeId), EdgeId> = HashMap::new();

    // Process B edges first
    for &edge in f.codomain.edges() {
        let root = find_edge(&mut edge_parent, ('B', edge));
        if !class_to_pushout_edge.contains_key(&root) {
            // Get edge info from B
            let swbs = f.codomain.get_sources_with_binding(edge).unwrap();
            let targets = f.codomain.get_targets(edge).unwrap();
            let label = f.codomain.get_label(edge).cloned();

            // Map to pushout
            let new_swbs: Vec<SourceWithBinding> = swbs
                .iter()
                .map(|swb| SourceWithBinding {
                    source: node_to_pushout[&('B', swb.source)],
                    bound: swb
                        .bound
                        .iter()
                        .map(|&b| node_to_pushout[&('B', b)])
                        .collect(),
                })
                .collect();

            let new_targets: Vec<NodeId> = targets
                .iter()
                .map(|&t| node_to_pushout[&('B', t)])
                .collect();

            let pushout_edge = pushout.add_edge(new_swbs, new_targets, label).unwrap();
            class_to_pushout_edge.insert(root, pushout_edge);
        }
        edge_to_pushout.insert(('B', edge), class_to_pushout_edge[&root]);
    }

    // Process C edges
    for &edge in g.codomain.edges() {
        let root = find_edge(&mut edge_parent, ('C', edge));
        if !class_to_pushout_edge.contains_key(&root) {
            // Get edge info from C
            let swbs = g.codomain.get_sources_with_binding(edge).unwrap();
            let targets = g.codomain.get_targets(edge).unwrap();
            let label = g.codomain.get_label(edge).cloned();

            // Map to pushout
            let new_swbs: Vec<SourceWithBinding> = swbs
                .iter()
                .map(|swb| SourceWithBinding {
                    source: node_to_pushout[&('C', swb.source)],
                    bound: swb
                        .bound
                        .iter()
                        .map(|&b| node_to_pushout[&('C', b)])
                        .collect(),
                })
                .collect();

            let new_targets: Vec<NodeId> = targets
                .iter()
                .map(|&t| node_to_pushout[&('C', t)])
                .collect();

            let pushout_edge = pushout.add_edge(new_swbs, new_targets, label).unwrap();
            class_to_pushout_edge.insert(root, pushout_edge);
        }
        edge_to_pushout.insert(('C', edge), class_to_pushout_edge[&root]);
    }

    // Build the universal morphisms
    let b_to_d_nodes: HashMap<NodeId, NodeId> = f
        .codomain
        .nodes()
        .iter()
        .map(|&n| (n, node_to_pushout[&('B', n)]))
        .collect();
    let b_to_d_edges: HashMap<EdgeId, EdgeId> = f
        .codomain
        .edges()
        .iter()
        .map(|&e| (e, edge_to_pushout[&('B', e)]))
        .collect();

    let c_to_d_nodes: HashMap<NodeId, NodeId> = g
        .codomain
        .nodes()
        .iter()
        .map(|&n| (n, node_to_pushout[&('C', n)]))
        .collect();
    let c_to_d_edges: HashMap<EdgeId, EdgeId> = g
        .codomain
        .edges()
        .iter()
        .map(|&e| (e, edge_to_pushout[&('C', e)]))
        .collect();

    let b_to_d =
        BHypMorphism::new(f.codomain.clone(), pushout.clone(), b_to_d_nodes, b_to_d_edges)?;
    let c_to_d =
        BHypMorphism::new(g.codomain.clone(), pushout.clone(), c_to_d_nodes, c_to_d_edges)?;

    Ok(PushoutResult {
        pushout,
        morphism_from_b : b_to_d,
        morphism_from_c : c_to_d,
    })
}

/// Compute the pullback of two morphisms f: B -> D and g: C -> D
/// Returns the pullback P together with morphisms P -> B and P -> C
///
/// ```
///     P ---p1---> B
///     |           |
///     p2          f
///     |           |
///     v           v
///     C ---g----> D
/// ```
pub fn compute_pullback(
    f: &BHypMorphism,
    g: &BHypMorphism,
) -> Result<PullbackResult, CategoricalError> {
    // Verify f and g have the same codomain
    if f.codomain.nodes() != g.codomain.nodes() || f.codomain.edges() != g.codomain.edges() {
        return Err(CategoricalError::CodomainMismatch);
    }

    let mut pullback = BHyp::new();

    // Pullback nodes: pairs (b, c) where f(b) = g(c)
    let mut pullback_nodes: Vec<(NodeId, NodeId)> = Vec::new();
    let mut pair_to_pullback_node: HashMap<(NodeId, NodeId), NodeId> = HashMap::new();

    for &b_node in f.domain.nodes() {
        for &c_node in g.domain.nodes() {
            if f.map_node(b_node) == g.map_node(c_node) {
                let p_node = pullback.add_node();
                pullback_nodes.push((b_node, c_node));
                pair_to_pullback_node.insert((b_node, c_node), p_node);
            }
        }
    }

    // Pullback edges: pairs (b_edge, c_edge) where f(b_edge) = g(c_edge)
    // and all sources/targets match
    let mut p_to_b_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
    let mut p_to_c_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

    for &b_edge in f.domain.edges() {
        for &c_edge in g.domain.edges() {
            if f.map_edge(b_edge) == g.map_edge(c_edge) {
                // Check that sources and targets can be paired
                let b_swbs = f.domain.get_sources_with_binding(b_edge).unwrap();
                let c_swbs = g.domain.get_sources_with_binding(c_edge).unwrap();
                let b_targets = f.domain.get_targets(b_edge).unwrap();
                let c_targets = g.domain.get_targets(c_edge).unwrap();

                if b_swbs.len() != c_swbs.len() || b_targets.len() != c_targets.len() {
                    continue;
                }

                // Check all pairs exist
                let mut valid = true;
                let mut new_swbs = Vec::new();

                for (b_swb, c_swb) in b_swbs.iter().zip(c_swbs.iter()) {
                    if let Some(&p_source) = pair_to_pullback_node.get(&(b_swb.source, c_swb.source))
                    {
                        if b_swb.bound.len() != c_swb.bound.len() {
                            valid = false;
                            break;
                        }
                        let mut bound = Vec::new();
                        for (&b_bound, &c_bound) in b_swb.bound.iter().zip(c_swb.bound.iter()) {
                            if let Some(&p_bound) = pair_to_pullback_node.get(&(b_bound, c_bound)) {
                                bound.push(p_bound);
                            } else {
                                valid = false;
                                break;
                            }
                        }
                        if !valid {
                            break;
                        }
                        new_swbs.push(SourceWithBinding {
                            source: p_source,
                            bound,
                        });
                    } else {
                        valid = false;
                        break;
                    }
                }

                if !valid {
                    continue;
                }

                let mut new_targets = Vec::new();
                for (&b_t, &c_t) in b_targets.iter().zip(c_targets.iter()) {
                    if let Some(&p_t) = pair_to_pullback_node.get(&(b_t, c_t)) {
                        new_targets.push(p_t);
                    } else {
                        valid = false;
                        break;
                    }
                }

                if !valid {
                    continue;
                }

                let label = f.domain.get_label(b_edge).cloned();
                let p_edge = pullback.add_edge(new_swbs, new_targets, label).unwrap();
                p_to_b_edges.insert(p_edge, b_edge);
                p_to_c_edges.insert(p_edge, c_edge);
            }
        }
    }

    // Build morphisms P -> B and P -> C
    let p_to_b_nodes: HashMap<NodeId, NodeId> = pair_to_pullback_node
        .iter()
        .map(|(&(b, _), &p)| (p, b))
        .collect();
    let p_to_c_nodes: HashMap<NodeId, NodeId> = pair_to_pullback_node
        .iter()
        .map(|(&(_, c), &p)| (p, c))
        .collect();

    let p_to_b =
        BHypMorphism::new(pullback.clone(), f.domain.clone(), p_to_b_nodes, p_to_b_edges)?;
    let p_to_c =
        BHypMorphism::new(pullback.clone(), g.domain.clone(), p_to_c_nodes, p_to_c_edges)?;

    Ok(PullbackResult {
        pullback,
        morphism_to_b: p_to_b,
        morphism_to_c: p_to_c,
    })
}

/// Compute the pushout complement of morphisms l: K -> L and m: L -> G
/// Returns C (the context) with morphisms K -> C and C -> G such that
/// the square is a pushout
///
/// Given:
/// ```
///     K ---l---> L
///     |          |
///     k          m
///     |          |
///     v          v
///     C -------> G
/// ```
///
/// We compute C and the morphisms k: K -> C and c: C -> G
pub fn compute_pushout_complement(
    l: &BHypMorphism,
    m: &BHypMorphism,
) -> Result<PushoutComplementResult, CategoricalError> {
    // l: K -> L, m: L -> G
    // We need to verify the gluing condition and construct C = G \ (m(L) \ m(l(K)))

    // Gluing condition 1: Identification condition
    // If m identifies two elements of L, they must both be in l(K)
    // For nodes
    for &l1 in m.domain.nodes() {
        for &l2 in m.domain.nodes() {
            if l1 != l2 && m.map_node(l1) == m.map_node(l2) {
                // Both l1 and l2 must be in the image of l
                let l1_in_image = l.on_nodes.values().any(|&n| n == l1);
                let l2_in_image = l.on_nodes.values().any(|&n| n == l2);
                if !l1_in_image || !l2_in_image {
                    return Err(CategoricalError::IdentificationConditionViolated(format!(
                        "Nodes {:?} and {:?} are identified but not both in l(K)",
                        l1, l2
                    )));
                }
            }
        }
    }

    // For edges
    for &e1 in m.domain.edges() {
        for &e2 in m.domain.edges() {
            if e1 != e2 && m.map_edge(e1) == m.map_edge(e2) {
                let e1_in_image = l.on_edges.values().any(|&e| e == e1);
                let e2_in_image = l.on_edges.values().any(|&e| e == e2);
                if !e1_in_image || !e2_in_image {
                    return Err(CategoricalError::IdentificationConditionViolated(format!(
                        "Edges {:?} and {:?} are identified but not both in l(K)",
                        e1, e2
                    )));
                }
            }
        }
    }

    // Gluing condition 2: Dangling condition
    // For each node n in L \ l(K), if m(n) is source/target of an edge in G,
    // that edge must be in m(L)
    let l_node_image: HashSet<NodeId> = l.node_image();
    let l_edge_image: HashSet<EdgeId> = l.edge_image();

    for &l_node in m.domain.nodes() {
        if !l_node_image.contains(&l_node) {
            // l_node is in L \ l(K)
            let g_node = m.map_node(l_node).unwrap();

            // Check if g_node is connected to edges not in m(L)
            for &g_edge in m.codomain.edges() {
                let in_m_image = m.on_edges.values().any(|&e| e == g_edge);
                if !in_m_image {
                    // Check if g_node is involved in g_edge
                    if let Some(swbs) = m.codomain.get_sources_with_binding(g_edge) {
                        for swb in swbs {
                            if swb.source == g_node || swb.bound.contains(&g_node) {
                                return Err(CategoricalError::DanglingConditionViolated(format!(
                                    "Node {:?} in L\\l(K) is connected to edge {:?} not in m(L)",
                                    l_node, g_edge
                                )));
                            }
                        }
                    }
                    if let Some(targets) = m.codomain.get_targets(g_edge) {
                        if targets.contains(&g_node) {
                            return Err(CategoricalError::DanglingConditionViolated(format!(
                                "Node {:?} in L\\l(K) is target of edge {:?} not in m(L)",
                                l_node, g_edge
                            )));
                        }
                    }
                }
            }
        }
    }

    // Construct C = G minus (m(L \ l(K)))
    let mut complement = BHyp::new();

    // Nodes to keep in C: nodes in G that are either:
    // 1. Not in m(L), or
    // 2. In m(l(K))
    let m_l_image: HashSet<NodeId> = m.node_image();
    let m_l_k_image: HashSet<NodeId> = l
        .on_nodes
        .values()
        .filter_map(|&k_img| m.map_node(k_img))
        .collect();

    let mut g_to_c_nodes: HashMap<NodeId, NodeId> = HashMap::new();

    for &g_node in m.codomain.nodes() {
        let in_m_l = m_l_image.contains(&g_node);
        let in_m_l_k = m_l_k_image.contains(&g_node);

        if !in_m_l || in_m_l_k {
            let c_node = complement.add_node();
            g_to_c_nodes.insert(g_node, c_node);
        }
    }

    // Edges to keep in C
    let m_edge_image: HashSet<EdgeId> = m.edge_image();
    let m_l_k_edge_image: HashSet<EdgeId> = l
        .on_edges
        .values()
        .filter_map(|&k_img| m.map_edge(k_img))
        .collect();

    let mut g_to_c_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

    for &g_edge in m.codomain.edges() {
        let in_m_l = m_edge_image.contains(&g_edge);
        let in_m_l_k = m_l_k_edge_image.contains(&g_edge);

        if !in_m_l || in_m_l_k {
            let swbs = m.codomain.get_sources_with_binding(g_edge).unwrap();
            let targets = m.codomain.get_targets(g_edge).unwrap();
            let label = m.codomain.get_label(g_edge).cloned();

            // Map to C
            let new_swbs: Vec<SourceWithBinding> = swbs
                .iter()
                .map(|swb| SourceWithBinding {
                    source: g_to_c_nodes[&swb.source],
                    bound: swb.bound.iter().map(|&b| g_to_c_nodes[&b]).collect(),
                })
                .collect();

            let new_targets: Vec<NodeId> = targets.iter().map(|&t| g_to_c_nodes[&t]).collect();

            let c_edge = complement.add_edge(new_swbs, new_targets, label).unwrap();
            g_to_c_edges.insert(g_edge, c_edge);
        }
    }

    // Build morphism k: K -> C
    let k_to_c_nodes: HashMap<NodeId, NodeId> = l
        .domain
        .nodes()
        .iter()
        .map(|&k_node| {
            let l_node = l.map_node(k_node).unwrap();
            let g_node = m.map_node(l_node).unwrap();
            let c_node = g_to_c_nodes[&g_node];
            (k_node, c_node)
        })
        .collect();

    let k_to_c_edges: HashMap<EdgeId, EdgeId> = l
        .domain
        .edges()
        .iter()
        .map(|&k_edge| {
            let l_edge = l.map_edge(k_edge).unwrap();
            let g_edge = m.map_edge(l_edge).unwrap();
            let c_edge = g_to_c_edges[&g_edge];
            (k_edge, c_edge)
        })
        .collect();

    // Build morphism c: C -> G (inclusion)
    let c_to_g_nodes: HashMap<NodeId, NodeId> = g_to_c_nodes.iter().map(|(&g, &c)| (c, g)).collect();
    let c_to_g_edges: HashMap<EdgeId, EdgeId> = g_to_c_edges.iter().map(|(&g, &c)| (c, g)).collect();

    let k_to_c =
        BHypMorphism::new(l.domain.clone(), complement.clone(), k_to_c_nodes, k_to_c_edges)?;
    let c_to_g =
        BHypMorphism::new(complement.clone(), m.codomain.clone(), c_to_g_nodes, c_to_g_edges)?;

    Ok(PushoutComplementResult {
        complement,
        morphism_from_a: k_to_c,
        morphism_to_b: c_to_g,
    })
}

/// Check if two BHyp instances are isomorphic
pub fn are_isomorphic(g1: &BHyp, g2: &BHyp) -> bool {
    if g1.nodes().len() != g2.nodes().len() || g1.edges().len() != g2.edges().len() {
        return false;
    }

    // Try to find an isomorphism (brute force for small graphs)
    // This is a simplified check - for larger graphs, more sophisticated algorithms would be needed

    let g1_nodes: Vec<NodeId> = g1.nodes().iter().copied().collect();
    let g2_nodes: Vec<NodeId> = g2.nodes().iter().copied().collect();

    if g1_nodes.is_empty() && g2_nodes.is_empty() {
        return g1.edges().is_empty() && g2.edges().is_empty();
    }

    // For small graphs, try all permutations
    fn try_isomorphism(
        g1: &BHyp,
        g2: &BHyp,
        g1_nodes: &[NodeId],
        g2_nodes: &[NodeId],
        node_map: &mut HashMap<NodeId, NodeId>,
        idx: usize,
        used: &mut HashSet<NodeId>,
    ) -> bool {
        if idx == g1_nodes.len() {
            // Check if this node mapping induces a valid edge mapping
            let mut edge_map: HashMap<EdgeId, EdgeId> = HashMap::new();

            for &e1 in g1.edges() {
                let mut found = false;
                for &e2 in g2.edges() {
                    if edge_map.values().any(|&e| e == e2) {
                        continue;
                    }

                    // Check compatibility
                    let swbs1 = g1.get_sources_with_binding(e1).unwrap();
                    let swbs2 = g2.get_sources_with_binding(e2).unwrap();
                    let targets1 = g1.get_targets(e1).unwrap();
                    let targets2 = g2.get_targets(e2).unwrap();

                    if swbs1.len() != swbs2.len() || targets1.len() != targets2.len() {
                        continue;
                    }

                    let mut compatible = true;

                    for (s1, s2) in swbs1.iter().zip(swbs2.iter()) {
                        if node_map[&s1.source] != s2.source {
                            compatible = false;
                            break;
                        }
                        if s1.bound.len() != s2.bound.len() {
                            compatible = false;
                            break;
                        }
                        for (b1, b2) in s1.bound.iter().zip(s2.bound.iter()) {
                            if node_map[b1] != *b2 {
                                compatible = false;
                                break;
                            }
                        }
                    }

                    if !compatible {
                        continue;
                    }

                    for (t1, t2) in targets1.iter().zip(targets2.iter()) {
                        if node_map[t1] != *t2 {
                            compatible = false;
                            break;
                        }
                    }

                    if !compatible {
                        continue;
                    }

                    // Check labels
                    if g1.get_label(e1) != g2.get_label(e2) {
                        continue;
                    }

                    edge_map.insert(e1, e2);
                    found = true;
                    break;
                }

                if !found {
                    return false;
                }
            }

            return true;
        }

        let n1 = g1_nodes[idx];
        for &n2 in g2_nodes {
            if used.contains(&n2) {
                continue;
            }

            node_map.insert(n1, n2);
            used.insert(n2);

            if try_isomorphism(g1, g2, g1_nodes, g2_nodes, node_map, idx + 1, used) {
                return true;
            }

            node_map.remove(&n1);
            used.remove(&n2);
        }

        false
    }

    let mut node_map = HashMap::new();
    let mut used = HashSet::new();
    try_isomorphism(g1, g2, &g1_nodes, &g2_nodes, &mut node_map, 0, &mut used)
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper to create a simple graph: two nodes, one edge
    fn create_simple_graph() -> BHyp {
        let mut g = BHyp::new();
        let n1 = g.add_node();
        let n2 = g.add_node();
        g.add_edge(
            vec![SourceWithBinding {
                source: n1,
                bound: vec![],
            }],
            vec![n2],
            Some(Label::Symbol("f".to_string())),
        )
        .unwrap();
        g
    }

    /// Helper to create a graph with binding
    fn create_binding_graph() -> BHyp {
        let mut g = BHyp::new();
        let n1 = g.add_node();
        let n2 = g.add_node();
        let n3 = g.add_node();
        // Edge from n1 to n3, binding n2 at the source
        g.add_edge(
            vec![SourceWithBinding {
                source: n1,
                bound: vec![n2],
            }],
            vec![n3],
            Some(Label::Symbol("lambda".to_string())),
        )
        .unwrap();
        g
    }

    // ========================================================================
    // Morphism Tests
    // ========================================================================

    #[test]
    fn test_identity_morphism_is_valid() {
        let g = create_simple_graph();
        let id = identity_morphism(&g);
        assert!(id.validate().is_ok());
    }

    #[test]
    fn test_identity_morphism_is_isomorphism() {
        let g = create_simple_graph();
        let id = identity_morphism(&g);
        assert!(id.is_isomorphism());
    }

    #[test]
    fn test_identity_morphism_is_monomorphism() {
        let g = create_simple_graph();
        let id = identity_morphism(&g);
        assert!(id.is_monomorphism());
    }

    #[test]
    fn test_identity_morphism_is_epimorphism() {
        let g = create_simple_graph();
        let id = identity_morphism(&g);
        assert!(id.is_epimorphism());
    }

    #[test]
    fn test_identity_morphism_is_identity() {
        let g = create_simple_graph();
        let id = identity_morphism(&g);
        assert!(id.is_identity());
    }

    #[test]
    fn test_identity_on_binding_graph() {
        let g = create_binding_graph();
        let id = identity_morphism(&g);
        assert!(id.is_isomorphism());
        assert!(id.is_monomorphism());
        assert!(id.is_epimorphism());
    }

    #[test]
    fn test_inclusion_morphism_is_mono_not_epi() {
        // Create a subgraph inclusion
        let mut small = BHyp::new();
        let n1 = small.add_node();

        let mut large = BHyp::new();
        let m1 = large.add_node();
        let _m2 = large.add_node();

        let on_nodes = [(n1, m1)].into_iter().collect();
        let on_edges = HashMap::new();

        let morph = BHypMorphism::new(small, large, on_nodes, on_edges).unwrap();
        assert!(morph.is_monomorphism());
        assert!(!morph.is_epimorphism());
        assert!(!morph.is_isomorphism());
    }

    #[test]
    fn test_surjective_non_injective_morphism() {
        // Create a quotient-like morphism
        let mut domain = BHyp::new();
        let n1 = domain.add_node();
        let n2 = domain.add_node();

        let mut codomain = BHyp::new();
        let m1 = codomain.add_node();

        let on_nodes = [(n1, m1), (n2, m1)].into_iter().collect();
        let on_edges = HashMap::new();

        let morph = BHypMorphism::new(domain, codomain, on_nodes, on_edges).unwrap();
        assert!(!morph.is_monomorphism());
        assert!(morph.is_epimorphism());
        assert!(!morph.is_isomorphism());
    }

    // ========================================================================
    // Pushout Tests
    // ========================================================================

    #[test]
    fn test_pushout_of_identities() {
        let g = create_simple_graph();
        let id1 = identity_morphism(&g);
        let id2 = identity_morphism(&g);

        let result = compute_pushout(&id1, &id2).unwrap();

        // Pushout of id, id should be isomorphic to the original
        assert!(are_isomorphic(&result.pushout, &g));
    }

    #[test]
    fn test_pushout_is_coproduct_when_domain_empty() {
        // When domain is empty, pushout = coproduct
        let empty = BHyp::new();

        let mut g1 = BHyp::new();
        let _n1 = g1.add_node();

        let mut g2 = BHyp::new();
        let _n2 = g2.add_node();

        let f = BHypMorphism::new(empty.clone(), g1.clone(), HashMap::new(), HashMap::new()).unwrap();
        let g = BHypMorphism::new(empty, g2.clone(), HashMap::new(), HashMap::new()).unwrap();

        let result = compute_pushout(&f, &g).unwrap();

        // Coproduct should have 2 nodes (one from each)
        assert_eq!(result.pushout.nodes().len(), 2);
    }

    #[test]
    fn test_pushout_glues_shared_elements() {
        // K = single node, L = two nodes with K's node as one
        // R = two nodes with K's node as one
        // Pushout should identify the K-images

        let mut k = BHyp::new();
        let k_node = k.add_node();

        let mut l = BHyp::new();
        let l_node1 = l.add_node(); // This is where k_node maps
        let _l_node2 = l.add_node();

        let mut r = BHyp::new();
        let r_node1 = r.add_node(); // This is where k_node maps
        let _r_node2 = r.add_node();

        let f = BHypMorphism::new(
            k.clone(),
            l,
            [(k_node, l_node1)].into_iter().collect(),
            HashMap::new(),
        )
        .unwrap();

        let g = BHypMorphism::new(
            k,
            r,
            [(k_node, r_node1)].into_iter().collect(),
            HashMap::new(),
        )
        .unwrap();

        let result = compute_pushout(&f, &g).unwrap();

        // Should have 3 nodes: shared node + 2 distinct nodes
        assert_eq!(result.pushout.nodes().len(), 3);
    }

    // ========================================================================
    // Pullback Tests
    // ========================================================================

    #[test]
    fn test_pullback_of_identities() {
        let g = create_simple_graph();
        let id1 = identity_morphism(&g);
        let id2 = identity_morphism(&g);

        let result = compute_pullback(&id1, &id2).unwrap();

        // Pullback of id, id should be isomorphic to the original
        assert!(are_isomorphic(&result.pullback, &g));
    }

    #[test]
    fn test_pullback_is_product_when_codomain_discrete() {
        // When codomain has no edges, pullback includes all pairs
        let mut d = BHyp::new();
        let d_node = d.add_node();

        let mut b = BHyp::new();
        let b_node = b.add_node();

        let mut c = BHyp::new();
        let c_node = c.add_node();

        let f = BHypMorphism::new(
            b.clone(),
            d.clone(),
            [(b_node, d_node)].into_iter().collect(),
            HashMap::new(),
        )
        .unwrap();

        let g = BHypMorphism::new(
            c.clone(),
            d,
            [(c_node, d_node)].into_iter().collect(),
            HashMap::new(),
        )
        .unwrap();

        let result = compute_pullback(&f, &g).unwrap();

        // Pullback should have 1 node (the pair that maps to d_node)
        assert_eq!(result.pullback.nodes().len(), 1);
    }

    #[test]
    fn test_pullback_empty_when_images_disjoint() {
        let mut d = BHyp::new();
        let d_node1 = d.add_node();
        let d_node2 = d.add_node();

        let mut b = BHyp::new();
        let b_node = b.add_node();

        let mut c = BHyp::new();
        let c_node = c.add_node();

        let f = BHypMorphism::new(
            b,
            d.clone(),
            [(b_node, d_node1)].into_iter().collect(),
            HashMap::new(),
        )
        .unwrap();

        let g = BHypMorphism::new(
            c,
            d,
            [(c_node, d_node2)].into_iter().collect(),
            HashMap::new(),
        )
        .unwrap();

        let result = compute_pullback(&f, &g).unwrap();

        // No common image -> empty pullback
        assert!(result.pullback.is_empty());
    }

    // ========================================================================
    // Pushout Complement Tests
    // ========================================================================

    #[test]
    fn test_pushout_complement_exists_simple() {
        // K = single node, L = single node, G = two nodes
        // L embeds as one of G's nodes
        // Pushout complement should exist and be 2 nodes

        let mut k = BHyp::new();
        let k_node = k.add_node();

        let mut l = BHyp::new();
        let l_node = l.add_node();

        let mut g = BHyp::new();
        let g_node1 = g.add_node();
        let _g_node2 = g.add_node();

        let l_morph = BHypMorphism::new(
            k.clone(),
            l.clone(),
            [(k_node, l_node)].into_iter().collect(),
            HashMap::new(),
        )
        .unwrap();

        let m_morph = BHypMorphism::new(
            l,
            g.clone(),
            [(l_node, g_node1)].into_iter().collect(),
            HashMap::new(),
        )
        .unwrap();

        let result = compute_pushout_complement(&l_morph, &m_morph).unwrap();

        // Context should have 2 nodes: the one from K and the extra one from G
        assert_eq!(result.complement.nodes().len(), 2);
    }

    #[test]
    fn test_pushout_complement_roundtrip() {
        // Verify: PO of PC gives back original G
        // K -> L -> G gives PC = C
        // Then K -> C and K -> L should pushout to G

        let mut k = BHyp::new();
        let k_node = k.add_node();

        let mut l = BHyp::new();
        let l_node1 = l.add_node();
        let l_node2 = l.add_node();

        let mut g = BHyp::new();
        let g_node1 = g.add_node();
        let g_node2 = g.add_node();
        let g_node3 = g.add_node();

        // K -> L: k_node maps to l_node1
        let l_morph = BHypMorphism::new(
            k.clone(),
            l.clone(),
            [(k_node, l_node1)].into_iter().collect(),
            HashMap::new(),
        )
        .unwrap();

        // L -> G: l_node1 -> g_node1, l_node2 -> g_node2
        let m_morph = BHypMorphism::new(
            l.clone(),
            g.clone(),
            [(l_node1, g_node1), (l_node2, g_node2)].into_iter().collect(),
            HashMap::new(),
        )
        .unwrap();

        let pc_result = compute_pushout_complement(&l_morph, &m_morph).unwrap();

        // Now compute pushout of K -> L and K -> C
        let po_result = compute_pushout(&l_morph, &pc_result.morphism_from_a).unwrap();

        // The pushout should be isomorphic to G
        assert!(are_isomorphic(&po_result.pushout, &g));
    }

    #[test]
    fn test_pushout_complement_dangling_condition() {
        // Create a case where dangling condition is violated
        // K = empty, L = one node, G = one node with edge
        // The edge in G would be "dangling" when we try to remove L\K

        let k = BHyp::new();

        let mut l = BHyp::new();
        let l_node = l.add_node();

        let mut g = BHyp::new();
        let g_node = g.add_node();
        let g_node2 = g.add_node();
        g.add_edge(
            vec![SourceWithBinding {
                source: g_node,
                bound: vec![],
            }],
            vec![g_node2],
            None,
        )
        .unwrap();

        let l_morph =
            BHypMorphism::new(k.clone(), l.clone(), HashMap::new(), HashMap::new()).unwrap();

        let m_morph = BHypMorphism::new(
            l,
            g,
            [(l_node, g_node)].into_iter().collect(),
            HashMap::new(),
        )
        .unwrap();

        let result = compute_pushout_complement(&l_morph, &m_morph);
        assert!(matches!(
            result,
            Err(CategoricalError::DanglingConditionViolated(_))
        ));
    }

    #[test]
    fn test_pushout_complement_identification_condition() {
        // Create a case where identification condition is violated
        // K = empty, L = two nodes, G = one node (L's nodes identified)

        let k = BHyp::new();

        let mut l = BHyp::new();
        let l_node1 = l.add_node();
        let l_node2 = l.add_node();

        let mut g = BHyp::new();
        let g_node = g.add_node();

        let l_morph =
            BHypMorphism::new(k.clone(), l.clone(), HashMap::new(), HashMap::new()).unwrap();

        let m_morph = BHypMorphism::new(
            l,
            g,
            [(l_node1, g_node), (l_node2, g_node)].into_iter().collect(),
            HashMap::new(),
        )
        .unwrap();

        let result = compute_pushout_complement(&l_morph, &m_morph);
        assert!(matches!(
            result,
            Err(CategoricalError::IdentificationConditionViolated(_))
        ));
    }

    // ========================================================================
    // Combined / Integration Tests
    // ========================================================================

    #[test]
    fn test_po_of_pc_equals_original_with_edges() {
        // More complex test with edges

        let mut k = BHyp::new();
        let k_n1 = k.add_node();
        let k_n2 = k.add_node();

        let mut l = BHyp::new();
        let l_n1 = l.add_node();
        let l_n2 = l.add_node();
        l.add_edge(
            vec![SourceWithBinding {
                source: l_n1,
                bound: vec![],
            }],
            vec![l_n2],
            Some(Label::Symbol("a".to_string())),
        )
        .unwrap();

        let mut g = BHyp::new();
        let g_n1 = g.add_node();
        let g_n2 = g.add_node();
        let g_n3 = g.add_node();
        let g_n4 = g.add_node();
        let e1 = g
            .add_edge(
                vec![SourceWithBinding {
                    source: g_n1,
                    bound: vec![],
                }],
                vec![g_n2],
                Some(Label::Symbol("a".to_string())),
            )
            .unwrap();
        g.add_edge(
            vec![SourceWithBinding {
                source: g_n3,
                bound: vec![],
            }],
            vec![g_n4],
            Some(Label::Symbol("b".to_string())),
        )
        .unwrap();

        // K -> L
        let l_morph = BHypMorphism::new(
            k.clone(),
            l.clone(),
            [(k_n1, l_n1), (k_n2, l_n2)].into_iter().collect(),
            HashMap::new(),
        )
        .unwrap();

        // L -> G
        let l_e = *l.edges().iter().next().unwrap();
        let m_morph = BHypMorphism::new(
            l.clone(),
            g.clone(),
            [(l_n1, g_n1), (l_n2, g_n2)]
                .into_iter()
                .collect(),
            [(l_e, e1)].into_iter().collect(),
        )
        .unwrap();

        let pc_result = compute_pushout_complement(&l_morph, &m_morph).unwrap();

        // Verify complement structure
        assert_eq!(pc_result.complement.nodes().len(), 2); // g_n3, g_n4
        assert_eq!(pc_result.complement.edges().len(), 1); // the "b" edge

        // Compute pushout
        let po_result = compute_pushout(&l_morph, &pc_result.morphism_from_a).unwrap();

        // Should be isomorphic to G
        assert_eq!(po_result.pushout.nodes().len(), g.nodes().len());
        assert_eq!(po_result.pushout.edges().len(), g.edges().len());
        assert!(are_isomorphic(&po_result.pushout, &g));
    }

    #[test]
    fn test_binding_preserved_in_pushout() {
        let mut a = BHyp::new();
        let a_n1 = a.add_node();
        let a_n2 = a.add_node();

        let mut b = BHyp::new();
        let b_n1 = b.add_node();
        let b_n2 = b.add_node();
        let b_n3 = b.add_node();
        b.add_edge(
            vec![SourceWithBinding {
                source: b_n1,
                bound: vec![b_n2],
            }],
            vec![b_n3],
            Some(Label::Symbol("lam".to_string())),
        )
        .unwrap();

        let mut c = BHyp::new();
        let c_n1 = c.add_node();
        let c_n2 = c.add_node();

        let f = BHypMorphism::new(
            a.clone(),
            b.clone(),
            [(a_n1, b_n1), (a_n2, b_n2)].into_iter().collect(),
            HashMap::new(),
        )
        .unwrap();

        let g = BHypMorphism::new(
            a,
            c.clone(),
            [(a_n1, c_n1), (a_n2, c_n2)].into_iter().collect(),
            HashMap::new(),
        )
        .unwrap();

        let result = compute_pushout(&f, &g).unwrap();

        // Check that the edge in the pushout preserves binding
        assert_eq!(result.pushout.edges().len(), 1);
        let po_edge = *result.pushout.edges().iter().next().unwrap();
        let swbs = result.pushout.get_sources_with_binding(po_edge).unwrap();
        assert_eq!(swbs.len(), 1);
        assert_eq!(swbs[0].bound.len(), 1);
    }

    #[test]
    fn test_empty_graph_operations() {
        let empty = BHyp::new();
        let id = identity_morphism(&empty);

        assert!(id.is_isomorphism());
        assert!(id.is_monomorphism());
        assert!(id.is_epimorphism());
        assert!(id.is_identity());

        let po = compute_pushout(&id, &id).unwrap();
        assert!(po.pushout.is_empty());

        let pb = compute_pullback(&id, &id).unwrap();
        assert!(pb.pullback.is_empty());
    }
}


// // ============================================================================
// // Double Pushout (DPO) Rewriting
// // ============================================================================

// /// A rewrite rule for DPO consisting of L <- K -> R
// #[derive(Debug, Clone)]
// pub struct RewriteRule {
//     /// Left-hand side
//     pub left: BHyp,
//     /// Interface (kernel)
//     pub interface: BHyp,
//     /// Right-hand side
//     pub right: BHyp,
//     /// Morphism K -> L (on nodes)
//     pub l_nodes: HashMap<NodeId, NodeId>,
//     /// Morphism K -> L (on edges)
//     pub l_edges: HashMap<EdgeId, EdgeId>,
//     /// Morphism K -> R (on nodes)
//     pub r_nodes: HashMap<NodeId, NodeId>,
//     /// Morphism K -> R (on edges)
//     pub r_edges: HashMap<EdgeId, EdgeId>,
// }

// impl RewriteRule {
//     /// Create a new rewrite rule
//     pub fn new(
//         left: BHyp,
//         interface: BHyp,
//         right: BHyp,
//         l_nodes: HashMap<NodeId, NodeId>,
//         l_edges: HashMap<EdgeId, EdgeId>,
//         r_nodes: HashMap<NodeId, NodeId>,
//         r_edges: HashMap<EdgeId, EdgeId>,
//     ) -> Self {
//         RewriteRule {
//             left,
//             interface,
//             right,
//             l_nodes,
//             l_edges,
//             r_nodes,
//             r_edges,
//         }
//     }
// }

// /// Result of DPO rewriting
// #[derive(Debug, Clone)]
// pub struct DPOResult {
//     /// The resulting hypergraph H
//     pub result: BHyp,
//     /// Mapping from the right-hand side to the result
//     pub right_to_result_nodes: HashMap<NodeId, NodeId>,
//     pub right_to_result_edges: HashMap<EdgeId, EdgeId>,
//     /// The intermediate graph D (pushout complement)
//     pub complement: BHyp,
// }

// /// Apply DPO rewriting
// ///
// /// ```text
// ///     L <--l-- K --r--> R
// ///     |        |        |
// ///   match      d        |
// ///     |        |        |
// ///     v   PO   v   PO   v
// ///     G <----- D -----> H
// /// ```
// pub fn dpo(
//     rule: &RewriteRule,
//     g: &BHyp,
//     match_nodes: &HashMap<NodeId, NodeId>,
//     match_edges: &HashMap<EdgeId, EdgeId>,
// ) -> Result<DPOResult, PushoutComplementError> {
//     // Step 1: Compute pushout complement D
//     let complement_result = pushout_complement(
//         &rule.interface,
//         &rule.left,
//         g,
//         &rule.l_nodes,
//         &rule.l_edges,
//         match_nodes,
//         match_edges,
//     )?;

//     // Step 2: Compute pushout of K -> D and K -> R
//     let pushout_result = pushout(
//         &rule.interface,
//         &complement_result.complement,
//         &rule.right,
//         &complement_result.interface_to_complement_nodes,
//         &complement_result.interface_to_complement_edges,
//         &rule.r_nodes,
//         &rule.r_edges,
//     );

//     Ok(DPOResult {
//         result: pushout_result.pushout,
//         right_to_result_nodes: pushout_result.second_to_pushout_nodes,
//         right_to_result_edges: pushout_result.second_to_pushout_edges,
//         complement: complement_result.complement,
//     })
// }

// // ============================================================================
// // Additional Categorical Operations: Coproduct and Coequalizer
// // ============================================================================

// /// Result of coproduct computation
// #[derive(Debug, Clone)]
// pub struct CoproductResult {
//     /// The coproduct object
//     pub coproduct: BHyp,
//     /// First injection (nodes)
//     pub first_injection_nodes: HashMap<NodeId, NodeId>,
//     /// First injection (edges)
//     pub first_injection_edges: HashMap<EdgeId, EdgeId>,
//     /// Second injection (nodes)
//     pub second_injection_nodes: HashMap<NodeId, NodeId>,
//     /// Second injection (edges)
//     pub second_injection_edges: HashMap<EdgeId, EdgeId>,
// }

// /// Compute the coproduct (disjoint union) of two hypergraphs
// pub fn coproduct(a: &BHyp, b: &BHyp) -> CoproductResult {
//     let mut coprod = BHyp::new();

//     let mut a_to_coprod_nodes: HashMap<NodeId, NodeId> = HashMap::new();
//     let mut b_to_coprod_nodes: HashMap<NodeId, NodeId> = HashMap::new();
//     let mut a_to_coprod_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
//     let mut b_to_coprod_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

//     // Add all nodes from A
//     for &a_node in a.nodes() {
//         let c_node = coprod.add_node();
//         a_to_coprod_nodes.insert(a_node, c_node);
//     }

//     // Add all nodes from B
//     for &b_node in b.nodes() {
//         let c_node = coprod.add_node();
//         b_to_coprod_nodes.insert(b_node, c_node);
//     }

//     // Add all edges from A
//     for &a_edge in a.edges() {
//         if let (Some(swbs), Some(targets)) = (a.get_sources_with_binding(a_edge), a.get_targets(a_edge))
//         {
//             let new_swbs: Vec<_> = swbs
//                 .iter()
//                 .map(|swb| SourceWithBinding {
//                     source: a_to_coprod_nodes[&swb.source],
//                     bound: swb
//                         .bound
//                         .iter()
//                         .map(|&b| a_to_coprod_nodes[&b])
//                         .collect(),
//                 })
//                 .collect();
//             let new_targets: Vec<_> = targets
//                 .iter()
//                 .map(|&t| a_to_coprod_nodes[&t])
//                 .collect();
//             let label = a.get_label(a_edge).cloned();

//             if let Ok(c_edge) = coprod.add_edge(new_swbs, new_targets, label) {
//                 a_to_coprod_edges.insert(a_edge, c_edge);
//             }
//         }
//     }

//     // Add all edges from B
//     for &b_edge in b.edges() {
//         if let (Some(swbs), Some(targets)) = (b.get_sources_with_binding(b_edge), b.get_targets(b_edge))
//         {
//             let new_swbs: Vec<_> = swbs
//                 .iter()
//                 .map(|swb| SourceWithBinding {
//                     source: b_to_coprod_nodes[&swb.source],
//                     bound: swb
//                         .bound
//                         .iter()
//                         .map(|&b| b_to_coprod_nodes[&b])
//                         .collect(),
//                 })
//                 .collect();
//             let new_targets: Vec<_> = targets
//                 .iter()
//                 .map(|&t| b_to_coprod_nodes[&t])
//                 .collect();
//             let label = b.get_label(b_edge).cloned();

//             if let Ok(c_edge) = coprod.add_edge(new_swbs, new_targets, label) {
//                 b_to_coprod_edges.insert(b_edge, c_edge);
//             }
//         }
//     }

//     CoproductResult {
//         coproduct: coprod,
//         first_injection_nodes: a_to_coprod_nodes,
//         first_injection_edges: a_to_coprod_edges,
//         second_injection_nodes: b_to_coprod_nodes,
//         second_injection_edges: b_to_coprod_edges,
//     }
// }

// /// Result of coequalizer computation
// #[derive(Debug, Clone)]
// pub struct CoequalizerResult {
//     /// The coequalizer object
//     pub coequalizer: BHyp,
//     /// Mapping from the codomain to the coequalizer (nodes)
//     pub projection_nodes: HashMap<NodeId, NodeId>,
//     /// Mapping from the codomain to the coequalizer (edges)
//     pub projection_edges: HashMap<EdgeId, EdgeId>,
// }

// /// Compute the coequalizer of two parallel morphisms f, g: A -> B
// /// Returns h: B -> C such that h ∘ f = h ∘ g
// pub fn coequalizer(
//     _a: &BHyp,
//     b: &BHyp,
//     f_nodes: &HashMap<NodeId, NodeId>,
//     f_edges: &HashMap<EdgeId, EdgeId>,
//     g_nodes: &HashMap<NodeId, NodeId>,
//     g_edges: &HashMap<EdgeId, EdgeId>,
// ) -> CoequalizerResult {
//     // Build equivalence classes for nodes
//     // Two nodes are equivalent if they are both images of some node in A under f and g

//     let mut node_equiv: HashMap<NodeId, NodeId> = HashMap::new();

//     // Initialize: each node is its own representative
//     for &node in b.nodes() {
//         node_equiv.insert(node, node);
//     }

//     // Union nodes that should be identified
//     for (&_a_node, &f_node) in f_nodes {
//         if let Some(&g_node) = g_nodes.get(&_a_node) {
//             // f(a) and g(a) should be identified
//             let f_rep = find_representative(&node_equiv, f_node);
//             let g_rep = find_representative(&node_equiv, g_node);
//             if f_rep != g_rep {
//                 // Union: make f_rep point to g_rep
//                 node_equiv.insert(f_rep, g_rep);
//             }
//         }
//     }

//     // Build similar equivalence for edges
//     let mut edge_equiv: HashMap<EdgeId, EdgeId> = HashMap::new();
//     for &edge in b.edges() {
//         edge_equiv.insert(edge, edge);
//     }

//     for (&_a_edge, &f_edge) in f_edges {
//         if let Some(&g_edge) = g_edges.get(&_a_edge) {
//             let f_rep = find_representative_edge(&edge_equiv, f_edge);
//             let g_rep = find_representative_edge(&edge_equiv, g_edge);
//             if f_rep != g_rep {
//                 edge_equiv.insert(f_rep, g_rep);
//             }
//         }
//     }

//     // Build the coequalizer
//     let mut coeq = BHyp::new();
//     let mut b_to_coeq_nodes: HashMap<NodeId, NodeId> = HashMap::new();
//     let mut b_to_coeq_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

//     // Create nodes for each equivalence class
//     let mut rep_to_coeq: HashMap<NodeId, NodeId> = HashMap::new();
//     for &b_node in b.nodes() {
//         let rep = find_representative(&node_equiv, b_node);
//         if !rep_to_coeq.contains_key(&rep) {
//             let c_node = coeq.add_node();
//             rep_to_coeq.insert(rep, c_node);
//         }
//         b_to_coeq_nodes.insert(b_node, rep_to_coeq[&rep]);
//     }

//     // Create edges (only for representative edges)
//     let mut rep_edge_to_coeq: HashMap<EdgeId, EdgeId> = HashMap::new();
//     for &b_edge in b.edges() {
//         let rep = find_representative_edge(&edge_equiv, b_edge);
//         if !rep_edge_to_coeq.contains_key(&rep) {
//             // Only process the representative edge
//             if let (Some(swbs), Some(targets)) =
//                 (b.get_sources_with_binding(rep), b.get_targets(rep))
//             {
//                 let new_swbs: Vec<_> = swbs
//                     .iter()
//                     .map(|swb| SourceWithBinding {
//                         source: b_to_coeq_nodes[&swb.source],
//                         bound: swb
//                             .bound
//                             .iter()
//                             .map(|&bn| b_to_coeq_nodes[&bn])
//                             .collect(),
//                     })
//                     .collect();
//                 let new_targets: Vec<_> = targets
//                     .iter()
//                     .map(|&t| b_to_coeq_nodes[&t])
//                     .collect();
//                 let label = b.get_label(rep).cloned();

//                 if let Ok(c_edge) = coeq.add_edge(new_swbs, new_targets, label) {
//                     rep_edge_to_coeq.insert(rep, c_edge);
//                 }
//             }
//         }
//         b_to_coeq_edges.insert(b_edge, rep_edge_to_coeq[&rep]);
//     }

//     CoequalizerResult {
//         coequalizer: coeq,
//         projection_nodes: b_to_coeq_nodes,
//         projection_edges: b_to_coeq_edges,
//     }
// }

// fn find_representative(equiv: &HashMap<NodeId, NodeId>, node: NodeId) -> NodeId {
//     let mut current = node;
//     while equiv.get(&current).copied() != Some(current) {
//         if let Some(&next) = equiv.get(&current) {
//             current = next;
//         } else {
//             break;
//         }
//     }
//     current
// }

// fn find_representative_edge(equiv: &HashMap<EdgeId, EdgeId>, edge: EdgeId) -> EdgeId {
//     let mut current = edge;
//     while equiv.get(&current).copied() != Some(current) {
//         if let Some(&next) = equiv.get(&current) {
//             current = next;
//         } else {
//             break;
//         }
//     }
//     current
// }

// // ============================================================================
// // Convex Match Check
// // ============================================================================

// /// Check if a matching is convex
// /// A match is convex if every path in the codomain between two nodes in the image
// /// lies entirely within the image
// pub fn is_convex_match(
//     domain: &BHyp,
//     codomain: &BHyp,
//     match_nodes: &HashMap<NodeId, NodeId>,
//     match_edges: &HashMap<EdgeId, EdgeId>,
// ) -> bool {
//     // First check that the match is injective (mono)
//     let node_values: HashSet<_> = match_nodes.values().collect();
//     if node_values.len() != match_nodes.len() {
//         return false;
//     }

//     let edge_values: HashSet<_> = match_edges.values().collect();
//     if edge_values.len() != match_edges.len() {
//         return false;
//     }

//     let image_nodes: HashSet<NodeId> = match_nodes.values().copied().collect();
//     let image_edges: HashSet<EdgeId> = match_edges.values().copied().collect();

//     // Check that all paths between image nodes stay within the image
//     for &start in &image_nodes {
//         for &end in &image_nodes {
//             if start == end {
//                 continue;
//             }
//             // Find all paths from start to end in codomain
//             // Check that all edges on these paths are in the image
//             if !all_paths_in_image(codomain, start, end, &image_nodes, &image_edges) {
//                 return false;
//             }
//         }
//     }

//     true
// }

// /// Check if all paths between two nodes stay within the image
// fn all_paths_in_image(
//     graph: &BHyp,
//     start: NodeId,
//     end: NodeId,
//     image_nodes: &HashSet<NodeId>,
//     image_edges: &HashSet<EdgeId>,
// ) -> bool {
//     // DFS to find paths and check they stay in image
//     fn dfs(
//         graph: &BHyp,
//         current: NodeId,
//         end: NodeId,
//         visited: &mut HashSet<NodeId>,
//         image_nodes: &HashSet<NodeId>,
//         image_edges: &HashSet<EdgeId>,
//     ) -> bool {
//         if current == end {
//             return true;
//         }

//         if visited.contains(&current) {
//             return true; // Already processed this node
//         }
//         visited.insert(current);

//         // Find edges starting from current
//         for &edge in graph.edges() {
//             if let Some(sources) = graph.get_sources(edge) {
//                 if sources.contains(&current) {
//                     // This edge starts at current
//                     // If we're in the image, the edge must be in the image too
//                     if image_nodes.contains(&current) && !image_edges.contains(&edge) {
//                         // Found a path that exits the image - check if it leads back
//                         if let Some(targets) = graph.get_targets(edge) {
//                             for &target in targets {
//                                 if image_nodes.contains(&target) {
//                                     // Path exits and re-enters image - not convex
//                                     return false;
//                                 }
//                             }
//                         }
//                     }

//                     // Continue DFS through targets
//                     if let Some(targets) = graph.get_targets(edge) {
//                         for &target in targets {
//                             if !dfs(graph, target, end, visited, image_nodes, image_edges) {
//                                 return false;
//                             }
//                         }
//                     }
//                 }
//             }
//         }

//         true
//     }

//     let mut visited = HashSet::new();
//     dfs(graph, start, end, &mut visited, image_nodes, image_edges)
// }

// // ============================================================================
// // Tests
// // ============================================================================

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn test_morphism_creation() {
//         let mut g1 = BHyp::new();
//         let n1 = g1.add_node();
//         let n2 = g1.add_node();
//         g1.add_edge(
//             vec![SourceWithBinding {
//                 source: n1,
//                 bound: vec![],
//             }],
//             vec![n2],
//             Some(Label::Symbol("f".to_string())),
//         )
//         .unwrap();

//         let mut g2 = BHyp::new();
//         let m1 = g2.add_node();
//         let m2 = g2.add_node();
//         let m3 = g2.add_node();
//         g2.add_edge(
//             vec![SourceWithBinding {
//                 source: m1,
//                 bound: vec![],
//             }],
//             vec![m2],
//             Some(Label::Symbol("f".to_string())),
//         )
//         .unwrap();

//         // Create an injective morphism g1 -> g2
//         let on_nodes: HashMap<_, _> = [(n1, m1), (n2, m2)].into_iter().collect();
//         let on_edges: HashMap<_, _> = [(EdgeId(0), EdgeId(0))].into_iter().collect();

//         let morphism = BHypMorphism::new(&g1, &g2, on_nodes, on_edges).unwrap();

//         assert!(morphism.is_monomorphism());
//         assert!(!morphism.is_epimorphism()); // m3 is not in image
//     }

//     #[test]
//     fn test_isomorphism() {
//         let mut g1 = BHyp::new();
//         let n1 = g1.add_node();
//         let n2 = g1.add_node();
//         g1.add_edge(
//             vec![SourceWithBinding {
//                 source: n1,
//                 bound: vec![],
//             }],
//             vec![n2],
//             Some(Label::Symbol("f".to_string())),
//         )
//         .unwrap();

//         let mut g2 = BHyp::new();
//         let m1 = g2.add_node();
//         let m2 = g2.add_node();
//         g2.add_edge(
//             vec![SourceWithBinding {
//                 source: m1,
//                 bound: vec![],
//             }],
//             vec![m2],
//             Some(Label::Symbol("f".to_string())),
//         )
//         .unwrap();

//         let on_nodes: HashMap<_, _> = [(n1, m1), (n2, m2)].into_iter().collect();
//         let on_edges: HashMap<_, _> = [(EdgeId(0), EdgeId(0))].into_iter().collect();

//         let morphism = BHypMorphism::new(&g1, &g2, on_nodes, on_edges).unwrap();

//         assert!(morphism.is_isomorphism());
//         assert_eq!(morphism.classify(), MorphismProperty::Isomorphism);
//     }

//     #[test]
//     fn test_pushout_simple() {
//         // Create a simple span C <- A -> B
//         // C: single node
//         let mut c = BHyp::new();
//         let c_node = c.add_node();

//         // A: two nodes with edge
//         let mut a = BHyp::new();
//         let a1 = a.add_node();
//         let a2 = a.add_node();
//         a.add_edge(
//             vec![SourceWithBinding {
//                 source: a1,
//                 bound: vec![],
//             }],
//             vec![a2],
//             Some(Label::Symbol("f".to_string())),
//         )
//         .unwrap();

//         // B: two nodes with edge
//         let mut b = BHyp::new();
//         let b1 = b.add_node();
//         let b2 = b.add_node();
//         b.add_edge(
//             vec![SourceWithBinding {
//                 source: b1,
//                 bound: vec![],
//             }],
//             vec![b2],
//             Some(Label::Symbol("g".to_string())),
//         )
//         .unwrap();

//         // Morphisms: c_node maps to a1 and b1
//         let f_nodes: HashMap<_, _> = [(c_node, a1)].into_iter().collect();
//         let f_edges: HashMap<EdgeId, EdgeId> = HashMap::new();
//         let g_nodes: HashMap<_, _> = [(c_node, b1)].into_iter().collect();
//         let g_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

//         let result = pushout(&c, &a, &b, &f_nodes, &f_edges, &g_nodes, &g_edges);

//         // Pushout should have 3 nodes (a1=b1 identified, a2, b2)
//         assert_eq!(result.pushout.nodes().len(), 3);
//         // Pushout should have 2 edges
//         assert_eq!(result.pushout.edges().len(), 2);
//     }

//     #[test]
//     fn test_coproduct() {
//         let mut a = BHyp::new();
//         let a1 = a.add_node();
//         let a2 = a.add_node();
//         a.add_edge(
//             vec![SourceWithBinding {
//                 source: a1,
//                 bound: vec![],
//             }],
//             vec![a2],
//             None,
//         )
//         .unwrap();

//         let mut b = BHyp::new();
//         let b1 = b.add_node();

//         let result = coproduct(&a, &b);

//         // Coproduct should have 3 nodes
//         assert_eq!(result.coproduct.nodes().len(), 3);
//         // Coproduct should have 1 edge
//         assert_eq!(result.coproduct.edges().len(), 1);

//         // Check injections are defined
//         assert!(result.first_injection_nodes.contains_key(&a1));
//         assert!(result.first_injection_nodes.contains_key(&a2));
//         assert!(result.second_injection_nodes.contains_key(&b1));
//     }

//     #[test]
//     fn test_pushout_complement_simple() {
//         // Create a simple example
//         // K: single node (interface)
//         let mut k = BHyp::new();
//         let k_node = k.add_node();

//         // L: two nodes with edge (left-hand side)
//         let mut l = BHyp::new();
//         let l1 = l.add_node();
//         let l2 = l.add_node();
//         l.add_edge(
//             vec![SourceWithBinding {
//                 source: l1,
//                 bound: vec![],
//             }],
//             vec![l2],
//             Some(Label::Symbol("f".to_string())),
//         )
//         .unwrap();

//         // G: three nodes, two edges (host graph)
//         let mut g = BHyp::new();
//         let g1 = g.add_node();
//         let g2 = g.add_node();
//         let g3 = g.add_node();
//         g.add_edge(
//             vec![SourceWithBinding {
//                 source: g1,
//                 bound: vec![],
//             }],
//             vec![g2],
//             Some(Label::Symbol("f".to_string())),
//         )
//         .unwrap();
//         g.add_edge(
//             vec![SourceWithBinding {
//                 source: g1,
//                 bound: vec![],
//             }],
//             vec![g3],
//             Some(Label::Symbol("h".to_string())),
//         )
//         .unwrap();

//         // K -> L: k_node maps to l1
//         let l_nodes: HashMap<_, _> = [(k_node, l1)].into_iter().collect();
//         let l_edges: HashMap<EdgeId, EdgeId> = HashMap::new();

//         // L -> G: l1 -> g1, l2 -> g2
//         let match_nodes: HashMap<_, _> = [(l1, g1), (l2, g2)].into_iter().collect();
//         let match_edges: HashMap<_, _> = [(EdgeId(0), EdgeId(0))].into_iter().collect();

//         let result =
//             pushout_complement(&k, &l, &g, &l_nodes, &l_edges, &match_nodes, &match_edges).unwrap();

//         // Complement should have 2 nodes (g1 preserved via k, g3 stays, g2 removed)
//         assert_eq!(result.complement.nodes().len(), 2);
//         // Complement should have 1 edge (the h edge stays)
//         assert_eq!(result.complement.edges().len(), 1);
        
     

//     }

//     #[test]
//     fn test_dpo_simple() {
//         // Simple rule: f -> g
//         // K: single node
//         let mut k = BHyp::new();
//         let k_node = k.add_node();

//         // L: two nodes with f edge
//         let mut l = BHyp::new();
//         let l1 = l.add_node();
//         let l2 = l.add_node();
//         l.add_edge(
//             vec![SourceWithBinding {
//                 source: l1,
//                 bound: vec![],
//             }],
//             vec![l2],
//             Some(Label::Symbol("f".to_string())),
//         )
//         .unwrap();

//         // R: two nodes with g edge
//         let mut r = BHyp::new();
//         let r1 = r.add_node();
//         let r2 = r.add_node();
//         r.add_edge(
//             vec![SourceWithBinding {
//                 source: r1,
//                 bound: vec![],
//             }],
//             vec![r2],
//             Some(Label::Symbol("g".to_string())),
//         )
//         .unwrap();

//         let rule = RewriteRule::new(
//             l.clone(),
//             k.clone(),
//             r.clone(),
//             [(k_node, l1)].into_iter().collect(),
//             HashMap::new(),
//             [(k_node, r1)].into_iter().collect(),
//             HashMap::new(),
//         );

//         // G: same as L
//         let mut g = BHyp::new();
//         let g1 = g.add_node();
//         let g2 = g.add_node();
//         g.add_edge(
//             vec![SourceWithBinding {
//                 source: g1,
//                 bound: vec![],
//             }],
//             vec![g2],
//             Some(Label::Symbol("f".to_string())),
//         )
//         .unwrap();

//         let match_nodes: HashMap<_, _> = [(l1, g1), (l2, g2)].into_iter().collect();
//         let match_edges: HashMap<_, _> = [(EdgeId(0), EdgeId(0))].into_iter().collect();

//         let result = dpo(&rule, &g, &match_nodes, &match_edges).unwrap();

//         // Result should have 2 nodes
//         assert_eq!(result.result.nodes().len(), 2);
//         // Result should have 1 edge labeled "g"
//         assert_eq!(result.result.edges().len(), 1);

//         let edge = result.result.edges().iter().next().unwrap();
//         assert_eq!(
//             result.result.get_label(*edge),
//             Some(&Label::Symbol("g".to_string()))
//         );
//     }
// }