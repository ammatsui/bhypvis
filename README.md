# bhyp — Hypergraphs with Binding (Rust crate)

This crate implements hypergraphs with binding (BHyp) and a set of categorical
constructions and rewriting tools built on them. It focuses on modeling
structures with scoped/bound variables (e.g. lambda-terms) as hypergraphs,
and provides utilities for matching, copying, glueing, substitution and
double-pushout (DPO) rewriting over these graphs.

This README summarizes the library design, core types and operations,
how to use the public API, and known limitations.

**Repository layout**
- **crates/bhyp/src/**: main library modules — `bhyp.rs`, `categorical.rs`,
  `copy.rs`, `substitution.rs`, `rewrite.rs`, `safety.rs`, `visualisation.rs`.
- `Cargo.toml`: crate definition.

**High-level overview**

- BHyp: a hypergraph-with-binding data structure that records nodes, hyper-
  edges, explicit source positions with bound variables, and targets. Binding
  is represented at the edge source level using `SourceWithBinding` records.
- BHyp_with_interface: a BHyp plus a discrete input/output interface (a
  cospan I_G -> G <- O_G) computed from node degrees; useful for glueing and
  copying constructions.
- Categorical constructions: morphisms, spans/cospans, pushouts,
  pullbacks, pushout complements and DPO-based rewriting utilities live in
  `categorical.rs` and expose high-level APIs used by copying/substitution
  and rewriting.
- Copying/glueing: functions to compute n copies of a sub-hypergraph glued
  along a chosen interface; used to implement metavariable expansion and
  controlled duplication of shared structure.
- Substitution: constructs a meta-hypergraph for a metavariable label,
  finds occurrences, creates copies of replacement graphs glued along free
  interface nodes, and performs the DPO steps to replace occurrences.
- Rewriting/Contexts: support for contextual composition, instantiation of
  rewrite rules with metavariables, and performing DPO rewrites using
  instantiated left/right spans.
- Safety checks: functions to enforce several structural safety conditions
  (uniqueness of bindings, non-leaking of bound variables, proper nesting
  of bodies, etc.). See `safety.rs` for the exact predicates.
- Visualization: Graphviz/DOT helpers to render BHyp and categorical squares.

Core types and notable API (summary)

- `BHyp` (in `bhyp.rs`)
  - `new()`, `add_node()`, `add_edge(...)` — build hypergraphs with binding.
  - `NodeId`, `EdgeId` — lightweight identifiers.
  - `Label::Symbol(String)` and `Label::Meta(String, usize)` — symbols vs
    metavariables (name + arity).
  - Accessors: `get_sources_with_binding`, `get_targets`, `get_arity`,
    `compute_body`, `compute_body_edges`, degree computations, etc.

- `BHyp_with_interface`
  - `from_bhyp(b: BHyp)` — compute input/output interfaces and maps.
  - `input_interface()`, `output_interface()`, `input_map()`, `output_map()`
    return the discrete interfaces and maps into the underlying `BHyp`.

- `categorical` utilities
  - `BHypMorphism` — morphisms between BHyp instances (node/edge maps).
  - `find_all_occurrences(pattern: &BHyp, target: &BHyp)` — find monomorphic
    inclusions of a pattern in a target; returns a vector of inclusion
    morphisms.
  - `compute_pushout`, `compute_pullback`, `compute_pushout_complement`
    — core categorical constructions used to glue graphs and compute DPO
    steps. Results include the resulting graph and the induced morphisms.
  - `dpo(...)` helper used by higher-level rewrite code.

- `copy` utilities
  - `compute_n_copies(t: &BHyp, n: usize, interface: Option<(BHyp, BHypMorphism)>)`
    — produce n copies of `T` glued along the given interface (defaults to
    input interface). Returns the glued graph, a projection morphism and the
    inclusions for each copy.
  - `copy_subhypergraph` / glueing helpers for inverse operations.

- `substitution` utilities
  - `construct_meta_hypergraph(label: Label)` — builds the canonical
    discrete meta-edge hypergraph for a metavariable label (sources and a
    single target, labeled by the metavariable).
  - `Substitution { meta_name, replacement: BHyp_with_interface, interface_map }`
    — substitution descriptor mapping the metaedge ports into concrete
    interface nodes of the replacement.
  - `apply_substitution_span` / `apply_substitution` — apply substitution to
    a (cospan/span) graph via DPO: builds n copies of the metaedge,
    constructs n·T̂ (copies of T glued along free vertices), and performs the
    pushout/complement steps to produce the rewritten graph.

- `rewrite` / contexts
  - `Context` abstraction: a shape, a hole and inclusion morphism.
  - `RewriteRule` (general, with metavariables) and
    `InstantiatedRewriteRule` (after substituting metavariables).
  - Helpers to instantiate rules with `RuleSubstitution` (left/right
    sharing spans) and to perform DPO rewriting using the instantiated rule.

- `safety` predicates
  - `check_safety(&BHyp)` and `check_safety_with_interface(&BHyp_with_interface)`
    return `Ok(())` if graph satisfies the safety conditions, or a
    `Vec<SafetyViolation>` describing failures.

- `visualisation` helpers
  - DOT exporters: `bhyp_to_dot`, `bhyp_with_interface_to_dot`, pushout/pullback
    diagram renderers and convenience `*_labelled` variants.

How the core operations are defined (precise behaviour)

- Matching / occurrences: occurrences are monomorphic inclusions of the
  meta-hypergraph into a target BHyp. The matcher enumerates injective
  node/edge maps respecting sources, targets and binding structure. Results
  are `BHypMorphism` inclusion morphisms.

- Copying and glueing: `compute_n_copies` constructs the pushout-based glue
  that yields n copies of a subgraph T identified along the chosen interface
  (usually the input interface). Internally it iteratively computes pushouts
  to glue another copy while preserving a projection morphism onto a single
  representative copy.

- Substitution: substituting a metavariable M with T proceeds as follows:
  1. Build the canonical meta-hypergraph I_M (discrete vertices for M's
     sources/target and a single metaedge).
  2. Find all occurrences (n) of M in G via `find_all_occurrences`.
  3. Build n disjoint copies of M (n·M) using copying helpers.
  4. Build n·T̂: n copies of `T` glued along the free interface (free
     vertices = (I_T + O_T) \\ Im(f)). This respects `Substitution.interface_map`
     which maps M's interface ports into concrete `T` interface nodes.
  5. Use pushout complements and pushouts (DPO square) to replace n·M in G
     by n·T̂ producing G[M/T]. The library exposes both span-level and
     BHyp_with_interface-level entry points (`apply_substitution_span`,
     `apply_substitution`).

- Rewriting (DPO): rewriting uses the usual DPO square construction with
  pushout complements. When rules contain metavariables they are first
  instantiated via substitutions that produce plain (meta-free) left and
  right graphs; the instantiated rule is then applied with DPO.

Usage examples (short)

- Build a small BHyp by hand:

```rust
use bhyp::BHyp;
let mut g = BHyp::new();
let n1 = g.add_node();
let n2 = g.add_node();
// add_edge(sources_with_binding, targets, Some(Label::Symbol("f".into())))
// see `add_edge` signature for the `SourceWithBinding` structure
```

- Compute an interface and find occurrences:

```rust
use bhyp::BHyp_with_interface;
let gi = BHyp_with_interface::from_bhyp(g.clone());
// build meta hypergraph for metavariable M of arity 2
let m = substitution::construct_meta_hypergraph(Label::Meta("M".into(), 2)).unwrap();
let occ = categorical::find_all_occurrences(&m, &g);
```

- Apply a substitution (high-level):

```rust
use substitution::Substitution;
// build replacement BHyp_with_interface `t_with_iface`
let subst = Substitution::new(Label::Meta("M".into(), 2), t_with_iface)
    .with_interface_map(interface_map);
let result_span = substitution::apply_substitution_span(&g_with_iface, &subst, &shared_span)?;
// or apply_substitution(...) -> BHyp_with_interface
```

Limitations and notes

- Poor error handling and primitive tests.
- Part of future work is implementing safety checks for copying, glueing,
rewrite rules, and substiution.
- Matching is monomorphic and exhaustive: `find_all_occurrences` enumerates
  all injective occurrences. This can be expensive for large graphs; there
  are no optimized indexing strategies implemented (yet).
- The copying/glueing and substitution pipelines rely on the cospan-based
  interface computations and pushout complement existence. Some complex
  identifications may make the pushout complement not exist — the library
  surfaces these as `CategoricalError` / `SubstitutionError` results.
- The crate exposes many lower-level categorical primitives; advanced uses
  (custom interfaces, non-standard gluing) may require composing morphisms
  and pushouts manually.
- Documentation in code currently contains `// Lines ... omitted` placeholders
  (in this repository snapshot) — consult the actual source docs/comments in
  `crates/bhyp/src/*.rs` for up-to-date line-level details if needed.

Contributing & running tests

- Build and test via cargo in the workspace root:

```bash
cd crates/bhyp
cargo test
```

License

See the repository top-level `Cargo.toml` for licensing information.
