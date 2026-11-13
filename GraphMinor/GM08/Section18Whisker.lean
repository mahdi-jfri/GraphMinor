module

public import GraphMinor.GM07.Defs
import GraphMinor.GM07.Section8

/-!
# A surrounding circle reached from another cuff

A closed arc-connected normal set may contain a circle off the boundary
which surrounds a cuff, and also meet a different cuff. When all its boundary
contacts are on that second cuff, trim a connecting line between the circle
and the boundary. The circle and trimmed line form a schism of type (vi).
This is a one-cuff extraction case in the use of VII Section 8 by VIII (18.1).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

/-- Extract the type (vi) schism of VIII Section 18, page 285, from a
surrounding circle off the boundary and a path to a different cuff. The
extraction stays inside the given normal set and preserves the vertex bound. -/
theorem exists_normal_schism_of_surrounding_circle_and_boundary {S : Type w}
    [TopologicalSpace S] (hS : IsSurface S) (G : Drawing S) {X A C D : Set S}
    (hX : IsClosed X) (hXarc : IsArcConnected X) (hnX : G.IsNormal X)
    (hA : IsOArc A) (hAX : A ⊆ X) (hoff : A ∩ bd S = ∅)
    (hsur : GM07.SurroundsCuff A D) (hC : C ∈ cuffs S) (hD : D ∈ cuffs S)
    (hCD : C ≠ D) (hmeet : (X ∩ bd S).Nonempty) (hbd : X ∩ bd S ⊆ C) :
    ∃ Y : Set S, Y ⊆ X ∧ GM07.IsSchism Y ∧ G.IsNormal Y ∧
      (G.V ∩ Y).ncard ≤ (G.V ∩ X).ncard := by
  have : T2Space S := hS.2.1
  have hdis : Disjoint A (X ∩ bd S) := disjoint_left.mpr fun x hxA hx => by
    have : x ∈ A ∩ bd S := ⟨hxA, hx.2⟩
    rw [hoff] at this
    exact this
  obtain ⟨P, u, v, hPX, hu, hv, hP, hPA, hPbd⟩ :=
    GM07.exists_connecting_line_between_disjoint_closed hXarc hAX inter_subset_left
      (GM07.IsOArc.isSolid hA).2 (hX.inter (isClosed_bd S))
      (GM07.IsOArc.isConnected hA).nonempty hmeet hdis
  have huv : u ≠ v := fun heq => disjoint_left.mp hdis hu (heq ▸ hv)
  have hPbd' : P ∩ bd S = {v} := by
    ext x
    constructor
    · intro hx
      exact hPbd.subset ⟨hx.1, hPX hx.1, hx.2⟩
    · rintro rfl
      exact ⟨hP.right_mem, hv.2⟩
  have hYbd : (A ∪ P) ∩ bd S = {v} := by
    rw [union_inter_distrib_right, hoff, empty_union, hPbd']
  have hYX : A ∪ P ⊆ X := union_subset hAX hPX
  have hsch : GM07.IsSchism (A ∪ P) := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨v, A, P, C, D, u, hA, hP, huv, hPA, rfl, hC, hD, hCD, hbd hv, hsur, hYbd⟩))))
  exact ⟨A ∪ P, hYX, hsch, fun x hx => hnX ⟨hYX hx.1, hx.2⟩,
    ncard_le_ncard (fun x hx => ⟨hx.1, hYX hx.2⟩) (G.finite_V.inter_of_left X)⟩

end GraphMinor.GM08
