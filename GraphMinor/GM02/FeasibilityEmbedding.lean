module

public import GraphMinor.GM02.EmbeddedSimpleGraph

/-!
# Feasibility after an injective change of vertex names

Push a simple graph and its terminal pairs into a larger vertex type.
The forward direction maps the disjoint paths. For the reverse direction,
all graph edges lie in the image. Restrict paths to that image and use
the inverse graph isomorphism. Unused isolated vertices cannot affect
feasibility of the mapped terminal pairs.
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v

/-- Injectively renaming a simple graph and its termination preserves feasibility, even with extra isolates. -/
theorem feasible_mapEmbedding_iff {α : Type u} {β : Type v} {S : Set α}
    (F : SimpleGraph α) (A : Termination S) (f : α ↪ β) :
    (A.mapEmbedding f).Feasible (Graph.ofSimpleGraph (F.map f)) ↔
      A.Feasible (Graph.ofSimpleGraph F) := by
  constructor
  · intro h
    let H := embeddedSimpleGraph F f
    have hshadow : pathGraph H = F.map f := embeddedSimpleGraph_pathGraph F f
    have hsupport : (A.mapEmbedding f).support ⊆ Set.range f := by
      rw [Termination.mapEmbedding_support]
      rintro _ ⟨a, _, rfl⟩
      exact ⟨a, rfl⟩
    let B : Termination (Set.range f) := (A.mapEmbedding f).rebase hsupport
    have hH : B.Feasible H := by
      change ∃ P : ∀ p : {p // p ∈ B.pairs}, PairPath (pathGraph H) p.val,
        ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices
      rw [hshadow]
      unfold Termination.Feasible at h
      rw [pathGraph_ofSimpleGraph] at h
      exact h
    have hB := (feasible_onVertices_iff H B).2 hH
    let K := Graph.ofSimpleGraph ((pathGraph H).induce V(H))
    let iso := embeddedSimpleGraphIso F f
    have hK : pathGraph K = (F.map f).induce (Set.range f) := by
      rw [pathGraph_ofSimpleGraph, hshadow]
      rfl
    let back : pathGraph K →g pathGraph (Graph.ofSimpleGraph F) :=
      { toFun := iso.symm
        map_rel' := by
          intro a b hab
          rw [pathGraph_ofSimpleGraph]
          exact iso.symm.map_rel_iff.2 (hK.le hab) }
    have hback := hB.mapHom back iso.symm.injective
    have hpairs : (B.onVertices.mapEmbedding ⟨back, iso.symm.injective⟩).pairs = A.pairs := by
      apply Finset.image_injective (Sym2.map.injective f.injective)
      change (B.onVertices.pairs.image (Sym2.map iso.symm)).image (Sym2.map f) =
        A.pairs.image (Sym2.map f)
      rw [Finset.image_image]
      have hcomp : Sym2.map f ∘ Sym2.map iso.symm = Sym2.map Subtype.val := by
        funext p
        induction p using Sym2.inductionOn with
        | hf a b =>
          change s(f (iso.symm a), f (iso.symm b)) = s(a.val, b.val)
          exact congrArg₂ Sym2.mk (congrArg Subtype.val (iso.apply_symm_apply a))
            (congrArg Subtype.val (iso.apply_symm_apply b))
      rw [hcomp, B.onVertices_map_pairs]
      rfl
    exact (feasible_iff_of_pairs_eq _ A (Graph.ofSimpleGraph F) hpairs).1 hback
  · intro h
    let forward : pathGraph (Graph.ofSimpleGraph F) →g pathGraph (Graph.ofSimpleGraph (F.map f)) :=
      { toFun := f
        map_rel' := by
          intro a b hab
          rw [pathGraph_ofSimpleGraph] at hab ⊢
          exact SimpleGraph.map_adj_apply.2 hab }
    exact h.mapHom forward f.injective

end GraphMinor.GM02
