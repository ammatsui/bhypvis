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