module

public import GraphMinor.GM02.FeasibilityMaps
public import GraphMinor.GM02.TerminationVertices
public import GraphMinor.GM02.FeasiblePathSupport
public import Mathlib.Combinatorics.Graph.Simple

/-!
# Restricting recursive path problems to actual vertices

The induced graphs in II (3.2) may use fewer vertices than their parent
ambient type. Every path between distinct prescribed endpoints stays in
the graph's vertex set. Restrict its walks to that subtype, or forget the
subtype in the reverse direction. Feasibility is therefore unchanged.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v

/-- The path shadow of a simple graph is the same simple graph. -/
theorem pathGraph_ofSimpleGraph {α : Type u} (F : SimpleGraph α) :
    pathGraph (Graph.ofSimpleGraph F) = F := by
  ext a b
  change ((Graph.ofSimpleGraph F).Adj a b ∧ a ≠ b) ↔ F.Adj a b
  rw [Graph.ofSimpleGraph_adj_iff]
  exact ⟨And.left, fun h => ⟨h, F.ne_of_adj h⟩⟩

/-- Forgetting the attached endpoint memberships recovers every original pair. -/
theorem Termination.onVertices_map_pairs {α : Type u} {S : Set α} (A : Termination S) :
    A.onVertices.pairs.image (Sym2.map Subtype.val) = A.pairs := by
  change (A.pairs.attach.image (fun p => p.val.attachWith (A.vertex_mem p.val p.property))).image
    (Sym2.map Subtype.val) = A.pairs
  rw [Finset.image_image]
  have he : (Sym2.map Subtype.val ∘ fun p : {p // p ∈ A.pairs} =>
      p.val.attachWith (A.vertex_mem p.val p.property)) = Subtype.val := by
    funext p
    exact Sym2.attachWith_map_subtypeVal _
  rw [he]
  exact Finset.attach_image_val (s := A.pairs)

/-- Restrict a prescribed path to the actual graph vertices. -/
noncomputable def PairPath.onVertices {α : Type u} {β : Type v} {G : Graph α β}
    {p : Sym2 α} (P : PairPath (pathGraph G) p) (hp : ¬p.IsDiag) :
    PairPath ((pathGraph G).induce V(G)) (p.attachWith (fun _ ha =>
      P.vertices_subset hp (P.endpoint_mem ha))) where
  start := ⟨P.start, P.vertices_subset hp P.walk.start_mem_support⟩
  finish := ⟨P.finish, P.vertices_subset hp P.walk.end_mem_support⟩
  ends_eq := by
    apply Sym2.map.injective Subtype.val_injective
    simpa only [Sym2.map_mk, Sym2.attachWith_map_subtypeVal] using P.ends_eq
  walk := P.walk.induce V(G) (fun a ha => P.vertices_subset hp ha)
  isPath := by
    apply Walk.IsPath.of_map (f := (SimpleGraph.Embedding.induce V(G)).toHom)
    rw [Walk.map_induce]
    exact P.isPath

/-- The restricted path has exactly the original support after forgetting
its vertex-membership proofs. -/
theorem PairPath.onVertices_vertices {α : Type u} {β : Type v} {G : Graph α β}
    {p : Sym2 α} (P : PairPath (pathGraph G) p) (hp : ¬p.IsDiag) :
    Subtype.val '' (P.onVertices hp).vertices = P.vertices := by
  change Subtype.val '' {a | a ∈ (P.walk.induce V(G) _).support} = {a | a ∈ P.walk.support}
  rw [Walk.support_induce]
  ext a
  simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_attachWith]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro ha
    exact ⟨⟨a, P.vertices_subset hp ha⟩, ha, rfl⟩

/-- Actual-vertex restriction preserves feasibility, as required to number
the smaller induced instances in Graph Minors II (3.2), pages 316–317. -/
theorem feasible_onVertices_iff {α : Type u} {β : Type v} (G : Graph α β)
    (A : Termination V(G)) :
    A.onVertices.Feasible (Graph.ofSimpleGraph ((pathGraph G).induce V(G))) ↔ A.Feasible G := by
  constructor
  · intro h
    let φ : pathGraph (Graph.ofSimpleGraph ((pathGraph G).induce V(G))) →g pathGraph G :=
      (SimpleGraph.Embedding.induce V(G)).toHom.comp
        (SimpleGraph.Hom.ofLE (by rw [pathGraph_ofSimpleGraph]))
    have hi : Function.Injective φ := Subtype.val_injective
    have hf := h.mapHom φ hi
    have hpairs : (A.onVertices.mapEmbedding ⟨φ, hi⟩).pairs = A.pairs :=
      A.onVertices_map_pairs
    exact (feasible_iff_of_pairs_eq _ _ G hpairs).1 hf
  · rintro ⟨P, hP⟩
    unfold Termination.Feasible
    rw [pathGraph_ofSimpleGraph]
    let pre (p : {p // p ∈ A.onVertices.pairs}) : {p // p ∈ A.pairs} :=
      ⟨p.val.map Subtype.val, (A.mem_onVertices_pairs p.val).1 p.property⟩
    let Q (p : {p // p ∈ A.onVertices.pairs}) : PairPath ((pathGraph G).induce V(G)) p.val :=
      { start := ((P (pre p)).onVertices (A.not_diag _ (pre p).property)).start
        finish := ((P (pre p)).onVertices (A.not_diag _ (pre p).property)).finish
        ends_eq := by
          apply Sym2.map.injective Subtype.val_injective
          change s((P (pre p)).start, (P (pre p)).finish) = (pre p).val
          exact (P (pre p)).ends_eq
        walk := ((P (pre p)).onVertices (A.not_diag _ (pre p).property)).walk
        isPath := ((P (pre p)).onVertices (A.not_diag _ (pre p).property)).isPath }
    refine ⟨Q, ?_⟩
    intro p q hpq
    have hne : pre p ≠ pre q := by
      intro he
      apply hpq
      apply Subtype.ext
      apply Sym2.map.injective Subtype.val_injective
      exact congrArg Subtype.val he
    apply Set.disjoint_left.2
    intro a hap haq
    have hp := (P (pre p)).onVertices_vertices (A.not_diag _ (pre p).property)
    have hq := (P (pre q)).onVertices_vertices (A.not_diag _ (pre q).property)
    apply Set.disjoint_left.1 (hP (pre p) (pre q) hne)
    · rw [← hp]
      exact ⟨a, hap, rfl⟩
    · rw [← hq]
      exact ⟨a, haq, rfl⟩

end GraphMinor.GM02
