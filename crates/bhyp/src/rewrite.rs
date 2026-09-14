// rewriting module
// contexts, context composition substitution 
// context with its hole filled

// rewrite rules with metavariables,
// rewrite rule application  


use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::bhyp::{BHyp, BHyp_with_interface, EdgeId, Label, NodeId, SourceWithBinding};
use crate::categorical::{
    BHypMorphism, CategoricalError, MorphismError, Span, 
    are_isomorphic, find_all_occurrences, find_subhypergraph_inclusion, build_inclusion,
    compute_coproduct, compute_pushout, compute_pushout_complement, dpo
};
use crate::copy::{compute_n_copies, copy_subhypergraph, compute_n_copies_with_interface};
use crate::substitution::{Substitution, SubstitutionError, apply_substitution, apply_substitution_span,
construct_meta_hypergraph};



// context is an equivalence class, given by 
// a context-hypergraph and a shape-hypergraph, 
// together with the inclusion morphism




    /// Errors for context construction and operations.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum ContextError {
        InclusionNotMono,
        InvalidInclusion(MorphismError),
        InvalidContext(String),
        HoleShapeMismatch(String),
        InterfaceMismatch(String),
        NoIsomorphism(String),
        PushoutFailed(CategoricalError),
        MorphismFailed(MorphismError),
    }

    impl fmt::Display for ContextError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                ContextError::InclusionNotMono => {
                    write!(f, "context inclusion H -> G is not monic")
                }
                ContextError::InvalidInclusion(e) => {
                    write!(f, "invalid context inclusion: {}", e)
                }
                ContextError::InvalidContext(s) => write!(f, "invalid context: {}", s),
                ContextError::HoleShapeMismatch(s) => {
                    write!(f, "hole/shape mismatch: {}", s)
                }
                ContextError::InterfaceMismatch(s) => {
                    write!(f, "interface mismatch: {}", s)
                }
                ContextError::NoIsomorphism(s) => write!(f, "no isomorphism: {}", s),
                ContextError::PushoutFailed(e) => write!(f, "pushout failed: {}", e),
                ContextError::MorphismFailed(e) => write!(f, "morphism failed: {}", e),
            }
        }
    }

    impl From<MorphismError> for ContextError {
        fn from(e: MorphismError) -> Self {
            ContextError::MorphismFailed(e)
        }
    }

    impl From<CategoricalError> for ContextError {
        fn from(e: CategoricalError) -> Self {
            ContextError::PushoutFailed(e)
        }
    }

    


#[derive(Debug, Clone)]
pub struct Context {
    /// The context hypergraph, which contains the hole
    pub shape: BHyp,
    /// The hole hypergraph, which defines the equivalence class of contexts
    pub hole: BHyp,
    /// The inclusion morphism from the hole to the shape
    pub inclusion: BHypMorphism,
}



    impl Context {
        /// Construct a context from a validated inclusion H -> G.
        pub fn new(
            hole: BHyp,
            shape: BHyp,
            inclusion: BHypMorphism,
        ) -> Result<Self, ContextError> {
            if inclusion.domain().nodes() != hole.nodes()
                || inclusion.domain().edges() != hole.edges()
                || inclusion.codomain().nodes() != shape.nodes()
                || inclusion.codomain().edges() != shape.edges()
            {
                return Err(ContextError::InvalidContext(
                    "inclusion domain/codomain do not match supplied hole/shape".to_string(),
                ));
            }

            inclusion
                .validate()
                .map_err(ContextError::InvalidInclusion)?;

            if !inclusion.is_monomorphism() {
                return Err(ContextError::InclusionNotMono);
            }

            
            Ok(Context {
                shape,
                hole,
                inclusion
            })
        }

        /// Build a context by searching for a monic inclusion H -> G.
        pub fn from_hole_and_shape(hole: &BHyp, shape: &BHyp) -> Result<Self, ContextError> {
            let inclusion = build_inclusion(hole, shape)
                .map_err(ContextError::InvalidInclusion)?;
       
            Self::new(hole.clone(), shape.clone(), inclusion)
        }

        /// Build a context directly from an existing monomorphism H -> G.
        pub fn from_inclusion(inclusion: BHypMorphism) -> Result<Self, ContextError> {
            let hole = inclusion.domain().clone();
            let shape = inclusion.codomain().clone();
            Self::new(hole, shape, inclusion)
        }

        pub fn shape(&self) -> &BHyp {
            &self.shape
        }

        pub fn hole(&self) -> &BHyp {
            &self.hole
        }

        pub fn inclusion(&self) -> &BHypMorphism {
            &self.inclusion
        }

        /// Compose contexts.
        ///
        /// If:
        ///
        /// ```text
        /// outer : H1 -> G1
        /// inner : H2 -> G2
        /// ```
        ///
        /// and `G2 ≅ H1`, then:
        ///
        /// ```text
        /// outer[inner] : H2 -> G1
        /// ```
        ///
        /// The implementation finds an isomorphism `G2 -> H1` and composes:
        ///
        /// ```text
        /// H2 -> G2 -> H1 -> G1
        /// ```
        pub fn compose(&self, inner: &Context) -> Result<Context, ContextError> {
            let iso_g2_to_h1 = find_isomorphism(inner.shape(), self.hole()).ok_or_else(|| {
                ContextError::NoIsomorphism(
                    "inner shape G2 is not isomorphic to outer hole H1".to_string(),
                )
            })?;

            let h2_to_g2 = inner.inclusion();
            let h1_to_g1 = self.inclusion();

            let mut h2_to_g1_nodes = HashMap::new();
            for &h2_n in inner.hole().nodes() {
                let g2_n = h2_to_g2.map_node(h2_n).ok_or_else(|| {
                    ContextError::HoleShapeMismatch(format!(
                        "inner inclusion does not map node {:?}",
                        h2_n
                    ))
                })?;

                let h1_n = iso_g2_to_h1.map_node(g2_n).ok_or_else(|| {
                    ContextError::HoleShapeMismatch(format!(
                        "isomorphism G2 -> H1 does not map node {:?}",
                        g2_n
                    ))
                })?;

                let g1_n = h1_to_g1.map_node(h1_n).ok_or_else(|| {
                    ContextError::HoleShapeMismatch(format!(
                        "outer inclusion does not map node {:?}",
                        h1_n
                    ))
                })?;

                h2_to_g1_nodes.insert(h2_n, g1_n);
            }

            let mut h2_to_g1_edges = HashMap::new();
            for &h2_e in inner.hole().edges() {
                let g2_e = h2_to_g2.map_edge(h2_e).ok_or_else(|| {
                    ContextError::HoleShapeMismatch(format!(
                        "inner inclusion does not map edge {:?}",
                        h2_e
                    ))
                })?;

                let h1_e = iso_g2_to_h1.map_edge(g2_e).ok_or_else(|| {
                    ContextError::HoleShapeMismatch(format!(
                        "isomorphism G2 -> H1 does not map edge {:?}",
                        g2_e
                    ))
                })?;

                let g1_e = h1_to_g1.map_edge(h1_e).ok_or_else(|| {
                    ContextError::HoleShapeMismatch(format!(
                        "outer inclusion does not map edge {:?}",
                        h1_e
                    ))
                })?;

                h2_to_g1_edges.insert(h2_e, g1_e);
            }

            let composed_inclusion = BHypMorphism::new(
                inner.hole().clone(),
                self.shape().clone(),
                h2_to_g1_nodes,
                h2_to_g1_edges,
            )?;

            Context::new(
                inner.hole().clone(),
                self.shape().clone(),
                composed_inclusion,
            )
        }

        /// Fill this context's hole with a filler graph, using an explicitly supplied
        /// interface map `hole -> filler`.
        ///
        /// Computes:
        ///
        /// ```text
        ///       H  ---->  G
        ///       |         |
        ///       v         v
        ///       T  ---->  G[H := T]
        /// ```
        ///
        /// as a pushout of `H -> G` and `H -> T`.
        pub fn fill_with_map(
            &self,
            filler: &BHyp,
            hole_to_filler: &BHypMorphism,
        ) -> Result<BHyp, ContextError> {
            if hole_to_filler.domain().nodes() != self.hole.nodes()
                || hole_to_filler.domain().edges() != self.hole.edges()
            {
                return Err(ContextError::HoleShapeMismatch(
                    "filler interface map domain must be the context hole".to_string(),
                ));
            }

            if hole_to_filler.codomain().nodes() != filler.nodes()
                || hole_to_filler.codomain().edges() != filler.edges()
            {
                return Err(ContextError::HoleShapeMismatch(
                    "filler interface map codomain must be the filler graph".to_string(),
                ));
            }

            hole_to_filler
                .validate()
                .map_err(ContextError::InvalidInclusion)?;

            let po = compute_pushout(self.inclusion(), hole_to_filler)?;
            Ok(po.pushout)
        }

        /// Fill this context's hole with a filler graph with interface.
        ///
        /// This checks that the combined interface of the filler is exactly the image
        /// of the hole under a found inclusion `H -> filler`.
        pub fn fill_with(
            &self,
            filler: &BHyp_with_interface,
        ) -> Result<BHyp, ContextError> {
            let h_to_t = find_subhypergraph_inclusion(self.hole(), filler.bhyp()).ok_or_else(|| {
                ContextError::InterfaceMismatch(
                    "could not find an inclusion H -> filler".to_string(),
                )
            })?;

            check_filler_interface_matches_hole(self.hole(), filler, &h_to_t)?;

            self.fill_with_map(filler.bhyp(), &h_to_t)
        }

        pub fn complement(&self) -> Result<BHyp, ContextError> {
            let ihole = BHyp_with_interface::from_bhyp(self.hole().clone());
            let iface = ihole.combined_interface();

            let i_map = BHypMorphism::new(
                iface.clone(),
                self.shape().clone(),
                ihole.combined_interface_map(),
                HashMap::new()
            )?;
            let pc = compute_pushout_complement(
                &i_map,
                &self.inclusion).unwrap();
            Ok(pc.complement)
        }
    }

    impl PartialEq for Context {
        fn eq(&self, other: &Self) -> bool {
        let c1 = match self.complement() {
            Ok(c) => c,
            Err(_) => return false,
        };

        let c2 = match other.complement() {
            Ok(c) => c,
            Err(_) => return false,
        };

        find_isomorphism(&c1, &c2).is_some()
    }
}

    impl Eq for Context {}

    /// Convenience free function for context composition.
    pub fn compose_contexts(
        outer: &Context,
        inner: &Context,
    ) -> Result<Context, ContextError> {
        outer.compose(inner)
    }

    /// Convenience free function for hole filling.
    pub fn fill_hole(
        ctx: &Context,
        filler: &BHyp_with_interface,
    ) -> Result<BHyp, ContextError> {
        ctx.fill_with(filler)
    }

    /// Check that filler's combined interface is exactly the image of the hole.
    fn check_filler_interface_matches_hole(
        hole: &BHyp,
        filler: &BHyp_with_interface,
        hole_to_filler: &BHypMorphism,
    ) -> Result<(), ContextError> {
        let hole_image_nodes: HashSet<NodeId> = hole
            .nodes()
            .iter()
            .filter_map(|&n| hole_to_filler.map_node(n))
            .collect();

        let filler_interface_nodes = filler.combined_interface_nodes();

        if hole_image_nodes != filler_interface_nodes {
            return Err(ContextError::InterfaceMismatch(format!(
                "filler combined interface nodes {:?} do not match hole image {:?}",
                filler_interface_nodes, hole_image_nodes
            )));
        }

        Ok(())
    }

    /// Find an isomorphism a -> b, if one exists.
    pub fn find_isomorphism(a: &BHyp, b: &BHyp) -> Option<BHypMorphism> {
        if a.nodes().len() != b.nodes().len() || a.edges().len() != b.edges().len() {
            return None;
        }

        let occurrences = find_all_occurrences(a, b);
        occurrences.into_iter().find(|m| m.is_isomorphism())
    }



///////////////////////////////////////////////
/// Rewrite rules and rewriting
//////////////////////////////////////////////


#[derive(Debug, Clone)]
pub enum RewriteRuleError {
        InvalidSpan(String),
        InvalidMorphism(String),
        MetavariableMismatch {
            left: HashSet<Label>,
            right: HashSet<Label>,
        },
        MissingSubstitution(Label),
        ExtraSubstitution(Label),
        SubstitutionFailed(SubstitutionError),
        DpoFailed(CategoricalError),
        ContextFailed(String),
        ContextNotAllowed,
        MatchIsNotMono,
        MatchDomainMismatch,
        ConstructionFailed(String),
    }

    impl fmt::Display for RewriteRuleError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                RewriteRuleError::InvalidSpan(s) => write!(f, "invalid rewrite span: {}", s),
                RewriteRuleError::InvalidMorphism(s) => write!(f, "invalid morphism: {}", s),
                RewriteRuleError::MetavariableMismatch { left, right } => {
                    write!(
                        f,
                        "L and R contain different metavariables: left={:?}, right={:?}",
                        left, right
                    )
                }
                RewriteRuleError::MissingSubstitution(l) => {
                    write!(f, "missing substitution for metavariable {:?}", l)
                }
                RewriteRuleError::ExtraSubstitution(l) => {
                    write!(f, "substitution supplied for non-present metavariable {:?}", l)
                }
                RewriteRuleError::SubstitutionFailed(e) => {
                    write!(f, "substitution failed: {}", e)
                }
                RewriteRuleError::DpoFailed(e) => write!(f, "DPO failed: {}", e),
                RewriteRuleError::ContextFailed(s) => write!(f, "context failed: {}", s),
                RewriteRuleError::ContextNotAllowed => {
                    write!(f, "match context is not in the allowed context set")
                }
                RewriteRuleError::MatchIsNotMono => write!(f, "rewrite match is not monic"),
                RewriteRuleError::MatchDomainMismatch => {
                    write!(f, "match domain is not the instantiated rule left-hand side")
                }
                RewriteRuleError::ConstructionFailed(s) => {
                    write!(f, "construction failed: {}", s)
                }
            }
        }
    }

    impl From<SubstitutionError> for RewriteRuleError {
        fn from(e: SubstitutionError) -> Self {
            RewriteRuleError::SubstitutionFailed(e)
        }
    }

    impl From<CategoricalError> for RewriteRuleError {
        fn from(e: CategoricalError) -> Self {
            RewriteRuleError::DpoFailed(e)
        }
    }

    impl From<ContextError> for RewriteRuleError {
        fn from(e: ContextError) -> Self {
            RewriteRuleError::ContextFailed(e.to_string())
        }
    }

// =========================================================================
// RuleSubstitution
// =========================================================================

    /// A substitution to be used when instantiating a general rewrite rule.
    ///
    /// Since instantiating a rule substitutes into both L and R, 
    /// need to substitution spans.
    ///
    /// - `shared_for_left`:  L <- K_L -> T
    /// - `shared_for_right`: R <- K_R -> T
#[derive(Debug, Clone)]
    pub struct RuleSubstitution {
        pub substitution: Substitution,
        pub shared_for_left: Span,
        pub shared_for_right: Span,
    }

    impl RuleSubstitution {
        pub fn new(
            substitution: Substitution,
            shared_for_left: Span,
            shared_for_right: Span,
        ) -> Self {
            RuleSubstitution {
                substitution,
                shared_for_left,
                shared_for_right,
            }
        }

        pub fn meta_label(&self) -> &Label {
            &self.substitution.meta_name
        }
    }

// helper function: applying substitution to a span,
// returning a new span 
pub fn transport_node_through_span(
    dpo_result: &Span,
    old_node: NodeId,
) -> Option<NodeId> {
    for (&c_node, &g_node) in dpo_result.to_l.on_nodes() {
        if g_node == old_node {
            return dpo_result.to_r.map_node(c_node);
        }
    }

    None
}

pub fn transport_edge_through_span(
    dpo_result: &Span,
    old_edge: EdgeId,
) -> Option<EdgeId> {
    for (&c_edge, &g_edge) in dpo_result.to_l.on_edges() {
        if g_edge == old_edge {
            return dpo_result.to_r.map_edge(c_edge);
        }
    }

    None
}

pub fn apply_substitution_to_span(
    span: &Span,
    subst: &Substitution,
    shared_l: &Span,
    shared_r: &Span,
) -> Result<Span, SubstitutionError> {
    let l_with_interface = BHyp_with_interface::from_bhyp(span.left.clone());
    let r_with_interface = BHyp_with_interface::from_bhyp(span.right.clone());

    let l_dpo = apply_substitution_span(
        &l_with_interface,
        subst,
        shared_l,
    )?;

    let r_dpo = apply_substitution_span(
        &r_with_interface,
        subst,
        shared_r,
    )?;

    let k_prime = span.middle.clone();

    let mut k_to_l_prime_nodes = HashMap::new();
    let mut k_to_r_prime_nodes = HashMap::new();

    for &k_node in span.middle.nodes() {
        let old_l_node = span.to_l.map_node(k_node).ok_or_else(|| {
            SubstitutionError::InvalidConstruction(format!(
                "span.to_l does not map K node {:?}",
                k_node
            ))
        })?;

        let old_r_node = span.to_r.map_node(k_node).ok_or_else(|| {
            SubstitutionError::InvalidConstruction(format!(
                "span.to_r does not map K node {:?}",
                k_node
            ))
        })?;

        let new_l_node = transport_node_through_span(&l_dpo, old_l_node).ok_or_else(|| {
            SubstitutionError::InvalidConstruction(format!(
                "K node {:?} maps to L node {:?}, but that node did not survive substitution",
                k_node, old_l_node
            ))
        })?;

        let new_r_node = transport_node_through_span(&r_dpo, old_r_node).ok_or_else(|| {
            SubstitutionError::InvalidConstruction(format!(
                "K node {:?} maps to R node {:?}, but that node did not survive substitution",
                k_node, old_r_node
            ))
        })?;

        k_to_l_prime_nodes.insert(k_node, new_l_node);
        k_to_r_prime_nodes.insert(k_node, new_r_node);
    }

    let mut k_to_l_prime_edges = HashMap::new();
    let mut k_to_r_prime_edges = HashMap::new();

    for &k_edge in span.middle.edges() {
        let old_l_edge = span.to_l.map_edge(k_edge).ok_or_else(|| {
            SubstitutionError::InvalidConstruction(format!(
                "span.to_l does not map K edge {:?}",
                k_edge
            ))
        })?;

        let old_r_edge = span.to_r.map_edge(k_edge).ok_or_else(|| {
            SubstitutionError::InvalidConstruction(format!(
                "span.to_r does not map K edge {:?}",
                k_edge
            ))
        })?;

        let new_l_edge = transport_edge_through_span(&l_dpo, old_l_edge).ok_or_else(|| {
            SubstitutionError::InvalidConstruction(format!(
                "K edge {:?} maps to L edge {:?}, but that edge did not survive substitution",
                k_edge, old_l_edge
            ))
        })?;

        let new_r_edge = transport_edge_through_span(&r_dpo, old_r_edge).ok_or_else(|| {
            SubstitutionError::InvalidConstruction(format!(
                "K edge {:?} maps to R edge {:?}, but that edge did not survive substitution",
                k_edge, old_r_edge
            ))
        })?;

        k_to_l_prime_edges.insert(k_edge, new_l_edge);
        k_to_r_prime_edges.insert(k_edge, new_r_edge);
    }

    let to_l_prime = BHypMorphism::new(
        k_prime.clone(),
        l_dpo.right.clone(),
        k_to_l_prime_nodes,
        k_to_l_prime_edges,
    )
    .map_err(|e| SubstitutionError::InvalidConstruction(e.to_string()))?;

    let to_r_prime = BHypMorphism::new(
        k_prime.clone(),
        r_dpo.right.clone(),
        k_to_r_prime_nodes,
        k_to_r_prime_edges,
    )
    .map_err(|e| SubstitutionError::InvalidConstruction(e.to_string()))?;

    Ok(Span {
        left: l_dpo.right,
        middle: k_prime,
        right: r_dpo.right,
        to_l: to_l_prime,
        to_r: to_r_prime,
    })
}

    // =========================================================================
    // General rewrite rule
    // =========================================================================

    /// A general rewrite rule with metavariables:
    ///
    /// ```text
    /// L <- K -> R
    /// ```
    ///
    /// In the `Span` convention:
    ///
    /// - `left = L`
    /// - `middle = K`
    /// - `right = R`
    /// - `to_l : K -> L`
    /// - `to_r : K -> R`
    #[derive(Debug, Clone)]
    pub struct RewriteRule {
        span: Span,
        metavariables: HashSet<Label>,
    }

    impl RewriteRule {
        pub fn new(span: Span) -> Result<Self, RewriteRuleError> {
            validate_span(&span)?;

            if !span.to_l.is_monomorphism() {
                return Err(RewriteRuleError::InvalidSpan(
                    "K -> L must be monic".to_string(),
                ));
            }

            if !span.to_r.is_monomorphism() {
                return Err(RewriteRuleError::InvalidSpan(
                    "K -> R must be monic".to_string(),
                ));
            }

            let left_metas = metavariables_in(&span.left);
            let right_metas = metavariables_in(&span.right);

            if left_metas != right_metas {
                return Err(RewriteRuleError::MetavariableMismatch {
                    left: left_metas,
                    right: right_metas,
                });
            }

            Ok(RewriteRule {
                span,
                metavariables: left_metas,
            })
        }

        pub fn span(&self) -> &Span {
            &self.span
        }

        pub fn left(&self) -> &BHyp {
            &self.span.left
        }

        pub fn interface(&self) -> &BHyp {
            &self.span.middle
        }

        pub fn right(&self) -> &BHyp {
            &self.span.right
        }

        pub fn metavariables(&self) -> &HashSet<Label> {
            &self.metavariables
        }

        /// Instantiate all metavariables in this rule.
        ///
        /// This applies each supplied substitution to L and R, leaving K fixed.
        /// 
        /// // todo: K needs to be updated too?
        ///
        /// The resulting rule is an ordinary DPO rule:
        ///
        /// ```text
        /// L[V/T] <- K[I_V/I_T] -> R[V/T]
        /// ```
        ///
        pub fn instance(
            &self,
            substitutions: &[RuleSubstitution],
        ) -> Result<InstantiatedRewriteRule, RewriteRuleError> {
           

            let mut instantiated_left =
                BHyp_with_interface::from_bhyp(self.span.left.clone());

            let mut instantiated_right =
                BHyp_with_interface::from_bhyp(self.span.right.clone());

            let mut subst_span = self.span.clone();

            // by assumption, the rhs of the susbtitutions
            // don't contain any metavariables, so we can apply them in any order
            for rs in substitutions {
                let new_span = apply_substitution_to_span(
                    &subst_span,
                    &rs.substitution,
                    &rs.shared_for_left,
                    &rs.shared_for_right,
                )?;

                instantiated_left = BHyp_with_interface::from_bhyp(new_span.left.clone());

                instantiated_right = BHyp_with_interface::from_bhyp(new_span.right.clone());
                subst_span = new_span.clone();

                // sanity check
                assert!(are_isomorphic(&subst_span.left, &instantiated_left.bhyp()));
            }

            // let left_bhyp = instantiated_left.bhyp().clone();
            // let right_bhyp = instantiated_right.bhyp().clone();


            // let instantiated_span = Span {
            //     left: left_bhyp,
            //     middle: self.span.middle.clone(),
            //     right: right_bhyp,
            //     to_l: k_to_left,
            //     to_r: k_to_right,
            // };

            InstantiatedRewriteRule::new(subst_span)
        }

        /// Instantiate, check context, and apply DPO-I.
        pub fn apply_rewrite_rule(
            &self,
            target: &BHyp,
            match_morphism: &BHypMorphism,
            substitutions: &[RuleSubstitution],
            allowed_contexts: &[Context],
        ) -> Result<BHyp, RewriteRuleError> {
            let instance = self.instance(substitutions)?;
            instance.apply_dpoi(target, match_morphism, allowed_contexts)
        }
}
    
    // =========================================================================
    // Instantiated rewrite rule
    // =========================================================================

    /// An ordinary DPO rule without remaining metavariables:
    ///
    /// ```text
    /// L' <- K -> R'
    /// ```
    #[derive(Debug, Clone)]
    pub struct InstantiatedRewriteRule {
        span: Span,
    }

    impl InstantiatedRewriteRule {
        pub fn new(span: Span) -> Result<Self, RewriteRuleError> {
            validate_span(&span)?;

            if !span.to_l.is_monomorphism() {
                return Err(RewriteRuleError::InvalidSpan(
                    "K -> instantiated L must be monic".to_string(),
                ));
            }

            if !span.to_r.is_monomorphism() {
                return Err(RewriteRuleError::InvalidSpan(
                    "K -> instantiated R must be monic".to_string(),
                ));
            }

            Ok(InstantiatedRewriteRule { span })
        }

        pub fn span(&self) -> &Span {
            &self.span
        }

        pub fn left(&self) -> &BHyp {
            &self.span.left
        }

        pub fn interface(&self) -> &BHyp {
            &self.span.middle
        }

        pub fn right(&self) -> &BHyp {
            &self.span.right
        }

        /// Apply the instantiated rule by DPO-I after checking that the induced
        /// match context is allowed.
        ///
        /// Given:
        ///
        /// ```text
        /// L' <- K -> R'
        /// m : L' -> G
        /// ```
        ///
        /// first form the context `[m : L' -> G]`. Then require it to be equal
        /// to one of `allowed_contexts`. Equality is delegated to your `Context`
        /// implementation, i.e. complement-isomorphism.
        pub fn apply_dpoi(
            &self,
            target: &BHyp,
            match_morphism: &BHypMorphism,
            allowed_contexts: &[Context],
        ) -> Result<BHyp, RewriteRuleError> {
            self.validate_match(target, match_morphism)?;

            let match_context = Context::from_inclusion(match_morphism.clone())?;

            let allowed = allowed_contexts.iter().any(|ctx| ctx == &match_context);

            if !allowed {
                return Err(RewriteRuleError::ContextNotAllowed);
            }

            let result_span = dpo(&self.span, target, match_morphism)?;

            Ok(result_span.right)
        }

        /// Same as `apply_dpoi`, but without the context restriction.
        ///
        /// Useful for tests, raw DPO rewriting, or systems where all contexts are
        /// allowed.
        pub fn apply_unrestricted(
            &self,
            target: &BHyp,
            match_morphism: &BHypMorphism,
        ) -> Result<BHyp, RewriteRuleError> {
            self.validate_match(target, match_morphism)?;

            let result_span = dpo(&self.span, target, match_morphism)?;

            Ok(result_span.right)
        }

        fn validate_match(
            &self,
            target: &BHyp,
            match_morphism: &BHypMorphism,
        ) -> Result<(), RewriteRuleError> {
            if match_morphism.domain().nodes() != self.span.left.nodes()
                || match_morphism.domain().edges() != self.span.left.edges()
            {
                return Err(RewriteRuleError::MatchDomainMismatch);
            }

            if match_morphism.codomain().nodes() != target.nodes()
                || match_morphism.codomain().edges() != target.edges()
            {
                return Err(RewriteRuleError::InvalidMorphism(
                    "match codomain is not target graph".to_string(),
                ));
            }

            if !match_morphism.is_monomorphism() {
                return Err(RewriteRuleError::MatchIsNotMono);
            }

            match_morphism
                .validate()
                .map_err(|e| RewriteRuleError::InvalidMorphism(e.to_string()))?;

            Ok(())
        }
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    /// Collect all metavariable labels appearing as edge labels.
    pub fn metavariables_in(g: &BHyp) -> HashSet<Label> {
        let mut out = HashSet::new();

        for &e in g.edges() {
            if let Some(Label::Meta(name, arity)) = g.get_label(e) {
                out.insert(Label::Meta(name.clone(), *arity));
            }
        }

        out
    }

    pub fn validate_span(span: &Span) -> Result<(), RewriteRuleError> {
        if span.to_l.domain().nodes() != span.middle.nodes()
            || span.to_l.domain().edges() != span.middle.edges()
        {
            return Err(RewriteRuleError::InvalidSpan(
                "to_l domain is not K".to_string(),
            ));
        }

        if span.to_l.codomain().nodes() != span.left.nodes()
            || span.to_l.codomain().edges() != span.left.edges()
        {
            return Err(RewriteRuleError::InvalidSpan(
                "to_l codomain is not L".to_string(),
            ));
        }

        if span.to_r.domain().nodes() != span.middle.nodes()
            || span.to_r.domain().edges() != span.middle.edges()
        {
            return Err(RewriteRuleError::InvalidSpan(
                "to_r domain is not K".to_string(),
            ));
        }

        if span.to_r.codomain().nodes() != span.right.nodes()
            || span.to_r.codomain().edges() != span.right.edges()
        {
            return Err(RewriteRuleError::InvalidSpan(
                "to_r codomain is not R".to_string(),
            ));
        }

        span.to_l
            .validate()
            .map_err(|e| RewriteRuleError::InvalidMorphism(e.to_string()))?;

        span.to_r
            .validate()
            .map_err(|e| RewriteRuleError::InvalidMorphism(e.to_string()))?;

        Ok(())
    }

    /// Convenience constructor for an empty sharing span `G <- ∅ -> T`.
    pub fn empty_sharing_span(g: &BHyp, t: &BHyp) -> Result<Span, RewriteRuleError> {
        let k = BHyp::new();

        let to_l = BHypMorphism::new(
            k.clone(),
            g.clone(),
            HashMap::new(),
            HashMap::new(),
        )
        .map_err(|e| RewriteRuleError::InvalidMorphism(e.to_string()))?;

        let to_r = BHypMorphism::new(
            k.clone(),
            t.clone(),
            HashMap::new(),
            HashMap::new(),
        )
        .map_err(|e| RewriteRuleError::InvalidMorphism(e.to_string()))?;

        Ok(Span {
            left: g.clone(),
            middle: k,
            right: t.clone(),
            to_l,
            to_r,
        })
    }

    /// Convenience constructor for a `RuleSubstitution` where no shared variables
    /// are used on either side.
    pub fn rule_substitution_no_sharing(
        substitution: Substitution,
        left_graph: &BHyp,
        right_graph: &BHyp,
    ) -> Result<RuleSubstitution, RewriteRuleError> {
        let replacement = substitution.replacement.bhyp().clone();

        let shared_for_left = empty_sharing_span(left_graph, &replacement)?;
        let shared_for_right = empty_sharing_span(right_graph, &replacement)?;

        Ok(RuleSubstitution {
            substitution,
            shared_for_left,
            shared_for_right,
        })
    }




    
#[cfg(test)]
mod context_tests {
    use crate::categorical::identity_morphism;

use super::*;

    #[test]
    fn test_simple_context() {
        // \lambda x. [] context
        // G
        let mut g = BHyp::new();
        let g_o = g.add_node();
        let g_x = g.add_node();
        let g_h = g.add_node();

        g.add_edge(
        vec![SourceWithBinding {
            source: g_h,
            bound: vec![g_x],
        }],
        vec![g_o],
        Some(Label::Symbol("λ".to_string())),
        ).unwrap();

        g.add_edge(
            vec![SourceWithBinding {
                source: g_x,
                bound: vec![],
            }], vec![g_h], 
            Some(Label::Symbol("e".to_string()))
        ).unwrap();

        // create hole H just 
        let mut h = BHyp::new();
        let h_o = h.add_node();
        let h_i = h.add_node();
        h.add_edge(
            vec![SourceWithBinding {
                source: h_i,
                bound: vec![],
            }],
            vec![h_o],
            Some(Label::Symbol("e".to_string())),
        ).unwrap();

        let ctxt = Context::from_hole_and_shape(&h, &g).unwrap();

        let compl = ctxt.complement().unwrap();

        assert_eq!(compl.nodes().len(), 3);
        assert_eq!(compl.edges().len(), 1);

    
    }

    #[test]
    fn test_simple_context_filling() {
        // \lambda x. [] context
        // G
        let mut g = BHyp::new();
        let g_o = g.add_node();
        let g_x = g.add_node();
        let g_h = g.add_node();

        g.add_edge(
        vec![SourceWithBinding {
            source: g_h,
            bound: vec![g_x],
        }],
        vec![g_o],
        Some(Label::Symbol("λ".to_string())),
        ).unwrap();

        g.add_edge(
            vec![SourceWithBinding {
                source: g_x,
                bound: vec![],
            }], vec![g_h], 
            Some(Label::Symbol("e".to_string()))
        ).unwrap();

        // create hole H just 
        let mut h = BHyp::new();
        let h_o = h.add_node();
        let h_i = h.add_node();
        h.add_edge(
            vec![SourceWithBinding {
                source: h_i,
                bound: vec![],
            }],
            vec![h_o],
            Some(Label::Symbol("e".to_string())),
        ).unwrap();

        let ctxt = Context::from_hole_and_shape(&h, &g).unwrap();
        // fill with the original hole H, should get back G
        let filled = ctxt.fill_with_map(&h, &identity_morphism(&h)).unwrap();
        assert!(are_isomorphic(&filled, &g));

    }
    
    #[test]
    fn test_simple_context_equiv() {
        // \lambda x. [] context
        // G
        let mut g = BHyp::new();
        let g_o = g.add_node();
        let g_x = g.add_node();
        let g_h = g.add_node();

        g.add_edge(
        vec![SourceWithBinding {
            source: g_h,
            bound: vec![g_x],
        }],
        vec![g_o],
        Some(Label::Symbol("λ".to_string())),
        ).unwrap();

        g.add_edge(
            vec![SourceWithBinding {
                source: g_x,
                bound: vec![],
            }], vec![g_h], 
            Some(Label::Symbol("e".to_string()))
        ).unwrap();

        // create hole H just 
        let mut h = BHyp::new();
        let h_o = h.add_node();
        let h_i = h.add_node();
        h.add_edge(
            vec![SourceWithBinding {
                source: h_i,
                bound: vec![],
            }],
            vec![h_o],
            Some(Label::Symbol("e".to_string())),
        ).unwrap();

        let ctxt1 = Context::from_hole_and_shape(&h, &g).unwrap();

        // ctxt2 has simple hole just interface
        // \lambda x. [] context
        // G
        let mut g2 = BHyp::new();
        let g_o = g2.add_node();
        let g_x = g2.add_node();
        let g_h = g2.add_node();

        g2.add_edge(
        vec![SourceWithBinding {
            source: g_h,
            bound: vec![g_x],
        }],
        vec![g_o],
        Some(Label::Symbol("λ".to_string())),
        ).unwrap();

        

        // create hole H just 
        let mut h2 = BHyp::new();
        let h_o = h2.add_node();
        let h_i = h2.add_node();

        let ctxt2_inclusion = BHypMorphism::new(
            h2.clone(),
            g2.clone(),
            HashMap::from([(h_o, g_h), (h_i, g_x)]),
            HashMap::new()
        ).unwrap();
        

        let ctxt2 = Context::from_inclusion(ctxt2_inclusion).unwrap();

        assert_eq!(ctxt1, ctxt2);


    }

    #[test]
    fn test_context_composition() {

    }


}

   
#[cfg(test)]
mod rewrite_tests {
    use super::*;


    fn labels(g: &BHyp) -> Vec<Label> {
        g.edges()
            .iter()
            .filter_map(|e| g.get_label(*e).cloned())
            .collect()
    }

    fn count_label(g: &BHyp, label: &Label) -> usize {
        labels(g).iter().filter(|l| *l == label).count()
    }

    fn contains_label(g: &BHyp, label: &Label) -> bool {
        count_label(g, label) > 0
    }

    #[test]
    fn test_example_beta_rule_instance_v_to_lambda_x_tx() {
        // This is the paper-style example:
        //
        //     app(λ x. M[x], V)  <- K ->  M[V]
        //
        // instantiated by
        //
        //     V ↦ λ x. t(x)
        //
        // The instantiated rule should be:
        //
        //     app(λ x. M[x], λ y. t(y)) <- K -> M[λ y. t(y)]
        //
        // up to graph isomorphism / fresh node names.

        let m = Label::Meta("M".to_string(), 1);
        let v = Label::Meta("V".to_string(), 0);
        let app = Label::Symbol("app".to_string());
        let lam = Label::Symbol("λ".to_string());
        let t_label = Label::Symbol("t".to_string());

        // ------------------------------------------------------------------
        // Build L = app(λ x. M[x], V)
        // ------------------------------------------------------------------

        let mut l = BHyp::new();

        let l_x = l.add_node();
        let l_m_out = l.add_node();
        let l_lam_out = l.add_node();
        let l_v_out = l.add_node();
        let l_app_out = l.add_node();

        // M[x]
        l.add_edge(
            vec![SourceWithBinding {
                source: l_x,
                bound: vec![],
            }],
            vec![l_m_out],
            Some(m.clone()),
        )
        .unwrap();

        // λ x. M[x]
        l.add_edge(
            vec![SourceWithBinding {
                source: l_m_out,
                bound: vec![l_x],
            }],
            vec![l_lam_out],
            Some(lam.clone()),
        )
        .unwrap();

        // V
        l.add_edge(vec![], vec![l_v_out], Some(v.clone()))
            .unwrap();

        // app(λ x. M[x], V)
        l.add_edge(
            vec![
                SourceWithBinding {
                    source: l_lam_out,
                    bound: vec![],
                },
                SourceWithBinding {
                    source: l_v_out,
                    bound: vec![],
                },
            ],
            vec![l_app_out],
            Some(app.clone()),
        )
        .unwrap();

        // ------------------------------------------------------------------
        // Build R = M[V]
        // ------------------------------------------------------------------

        let mut r = BHyp::new();

        let r_v_out = r.add_node();
        let r_m_out = r.add_node();

        // V
        r.add_edge(vec![], vec![r_v_out], Some(v.clone()))
            .unwrap();

        // M[V]
        r.add_edge(
            vec![SourceWithBinding {
                source: r_v_out,
                bound: vec![],
            }],
            vec![r_m_out],
            Some(m.clone()),
        )
        .unwrap();

        // ------------------------------------------------------------------
        // Build K.
        //
        // For this test we use the minimal discrete interface preserving only
        // the outside/result node of the redex.
        // ------------------------------------------------------------------

        let mut k = BHyp::new();
        let k_out = k.add_node();

        let to_l = BHypMorphism::new(
            k.clone(),
            l.clone(),
            HashMap::from([(k_out, l_app_out)]),
            HashMap::new(),
        )
        .unwrap();

        let to_r = BHypMorphism::new(
            k.clone(),
            r.clone(),
            HashMap::from([(k_out, r_m_out)]),
            HashMap::new(),
        )
        .unwrap();

        let rule_span = Span {
            left: l.clone(),
            middle: k.clone(),
            right: r.clone(),
            to_l,
            to_r,
        };

        let rule = RewriteRule::new(rule_span).unwrap();

        assert!(rule.metavariables().contains(&m));
        assert!(rule.metavariables().contains(&v));

        // ------------------------------------------------------------------
        // Build replacement T = λ x. t(x)
        // ------------------------------------------------------------------

        let mut t_graph = BHyp::new();

        let t_x = t_graph.add_node();
        let t_body = t_graph.add_node();
        let t_out = t_graph.add_node();

        // t(x)
        t_graph
            .add_edge(
                vec![SourceWithBinding {
                    source: t_x,
                    bound: vec![],
                }],
                vec![t_body],
                Some(t_label.clone()),
            )
            .unwrap();

        // λ x. t(x)
        t_graph
            .add_edge(
                vec![SourceWithBinding {
                    source: t_body,
                    bound: vec![t_x],
                }],
                vec![t_out],
                Some(lam.clone()),
            )
            .unwrap();

        let t_with_interface = BHyp_with_interface::from_bhyp(t_graph.clone());

        // ------------------------------------------------------------------
        // Build the Substitution V ↦ T.
        //
        // V is nullary, so construct_meta_hypergraph(V) has one output/target
        // node. The substitution interface map sends that canonical V-target
        // node to the output interface node of T corresponding to t_out.
        // ------------------------------------------------------------------

        let v_meta_graph = construct_meta_hypergraph(v.clone()).unwrap();

        let v_edge = *v_meta_graph.edges().iter().next().unwrap();
        let v_target = v_meta_graph.get_targets(v_edge).unwrap()[0];

        let t_out_iface = t_with_interface
            .output_map()
            .iter()
            .find_map(|(iface_node, concrete_node)| {
                if *concrete_node == t_out {
                    Some(*iface_node)
                } else {
                    None
                }
            })
            .expect("λ x. t(x) output node should be in the output interface");

        let substitution = Substitution {
            meta_name: v.clone(),
            replacement: t_with_interface,
            interface_map: HashMap::from([(v_target, t_out_iface)]),
        };

        let rule_subst = rule_substitution_no_sharing(substitution, rule.left(), rule.right())
            .unwrap();

        // ------------------------------------------------------------------
        // Instantiate the rule.
        // ------------------------------------------------------------------

        let inst = rule.instance(&[rule_subst]).unwrap();

        // V should be gone from both sides.
        assert!(!contains_label(inst.left(), &v));
        assert!(!contains_label(inst.right(), &v));

        // M is not substituted, so it remains.
        assert!(contains_label(inst.left(), &m));
        assert!(contains_label(inst.right(), &m));

        // Left should contain:
        //
        //   app
        //   outer λ
        //   replacement λ
        //   t
        //   M
        //
        assert_eq!(count_label(inst.left(), &app), 1);
        assert_eq!(count_label(inst.left(), &lam), 2);
        assert_eq!(count_label(inst.left(), &t_label), 1);
        assert_eq!(count_label(inst.left(), &m), 1);
        assert_eq!(count_label(inst.left(), &v), 0);

        // Right should contain:
        //
        //   M
        //   replacement λ
        //   t
        //
        assert_eq!(count_label(inst.right(), &app), 0);
        assert_eq!(count_label(inst.right(), &lam), 1);
        assert_eq!(count_label(inst.right(), &t_label), 1);
        assert_eq!(count_label(inst.right(), &m), 1);
        assert_eq!(count_label(inst.right(), &v), 0);

        // ------------------------------------------------------------------
        // Optional stronger checks: compare against manually built expected
        // instantiated graphs.
        // ------------------------------------------------------------------

        // Expected L' = app(λ x. M[x], λ y. t(y))
        let mut expected_l = BHyp::new();

        let el_x = expected_l.add_node();
        let el_m_out = expected_l.add_node();
        let el_outer_lam_out = expected_l.add_node();

        let el_y = expected_l.add_node();
        let el_t_out = expected_l.add_node();
        let el_inner_lam_out = expected_l.add_node();

        let el_app_out = expected_l.add_node();

        // M[x]
        expected_l
            .add_edge(
                vec![SourceWithBinding {
                    source: el_x,
                    bound: vec![],
                }],
                vec![el_m_out],
                Some(m.clone()),
            )
            .unwrap();

        // λ x. M[x]
        expected_l
            .add_edge(
                vec![SourceWithBinding {
                    source: el_m_out,
                    bound: vec![el_x],
                }],
                vec![el_outer_lam_out],
                Some(lam.clone()),
            )
            .unwrap();

        // t(y)
        expected_l
            .add_edge(
                vec![SourceWithBinding {
                    source: el_y,
                    bound: vec![],
                }],
                vec![el_t_out],
                Some(t_label.clone()),
            )
            .unwrap();

        // λ y. t(y)
        expected_l
            .add_edge(
                vec![SourceWithBinding {
                    source: el_t_out,
                    bound: vec![el_y],
                }],
                vec![el_inner_lam_out],
                Some(lam.clone()),
            )
            .unwrap();

        // app(λ x. M[x], λ y. t(y))
        expected_l
            .add_edge(
                vec![
                    SourceWithBinding {
                        source: el_outer_lam_out,
                        bound: vec![],
                    },
                    SourceWithBinding {
                        source: el_inner_lam_out,
                        bound: vec![],
                    },
                ],
                vec![el_app_out],
                Some(app.clone()),
            )
            .unwrap();

        assert!(are_isomorphic(inst.left(), &expected_l));

        // Expected R' = M[λ y. t(y)]
        let mut expected_r = BHyp::new();

        let er_y = expected_r.add_node();
        let er_t_out = expected_r.add_node();
        let er_lam_out = expected_r.add_node();
        let er_m_out = expected_r.add_node();

        // t(y)
        expected_r
            .add_edge(
                vec![SourceWithBinding {
                    source: er_y,
                    bound: vec![],
                }],
                vec![er_t_out],
                Some(t_label.clone()),
            )
            .unwrap();

        // λ y. t(y)
        expected_r
            .add_edge(
                vec![SourceWithBinding {
                    source: er_t_out,
                    bound: vec![er_y],
                }],
                vec![er_lam_out],
                Some(lam.clone()),
            )
            .unwrap();

        // M[λ y. t(y)]
        expected_r
            .add_edge(
                vec![SourceWithBinding {
                    source: er_lam_out,
                    bound: vec![],
                }],
                vec![er_m_out],
                Some(m.clone()),
            )
            .unwrap();

        assert!(are_isomorphic(inst.right(), &expected_r));
    }
}