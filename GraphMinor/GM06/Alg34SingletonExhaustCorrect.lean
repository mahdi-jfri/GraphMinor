module

public import GraphMinor.GM06.Alg34SingletonCorrect
public import GraphMinor.Compute.GM06Alg34SingletonReduce

/-!
# Feasibility under exhaustive singleton deletion

A found finite label represents an actual singleton block. Apply the
proved (3.3)(i) equivalence, use the computed representation of the
induced drawing, and repeat along the decreasing vertex recursion.
Every visited finite payload represents a drawing and a division, and
the exhausted payload has exactly the original feasibility answer.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]

/-- All represented division vertices belong to the represented drawing. -/
theorem divisionUnion_subset {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}
    (h : GM06DrawingRep x G Δ) : divisionUnion Δ ⊆ G.V := by
  rintro p ⟨δ, hδ, hp⟩
  obtain ⟨L, _, hL⟩ := h.division.subset hδ
  obtain ⟨v, _, hv⟩ := hL.symm ▸ hp
  exact hv ▸ (h.vertex v).property

/-- The finite singleton search returns an actual singleton of the
represented division, with the explicit supplied vertex bijection. -/
theorem findSingleton_mem {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}
    (h : GM06DrawingRep x G Δ) (v : Fin x.n)
    (hfind : gm06FindSingleton x.division = some v) : {(h.vertex v).val} ∈ Δ := by
  obtain ⟨B, hB, hblock⟩ := gm06FindSingleton_sound x.division v hfind
  apply h.division.symm.subset
  refine ⟨B, hB, ?_⟩
  change GM06DrawingData.block B = {v} at hblock
  change (fun a => (h.vertex a).val) '' GM06DrawingData.block B = {(h.vertex v).val}
  rw [hblock]
  simp only [Set.image_singleton]

/-- Exhausting (3.3)(i) retains an actual drawing representation and a
valid division, and preserves exactly the finite feasibility answer. -/
theorem reduceSingletons_correct {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}
    (h : GM06DrawingRep x G Δ) (hD : IsDivision Δ) :
    ∃ (G' : Drawing S) (Δ' : Set (Set S)),
      Nonempty (GM06DrawingRep (gm06ReduceSingletons x) G' Δ') ∧ IsDivision Δ' ∧
      (IsFeasible x.graph x.divisionSet ↔
        IsFeasible (gm06ReduceSingletons x).graph (gm06ReduceSingletons x).divisionSet) := by
  induction x using gm06ReduceSingletons.induct generalizing G Δ with
  | case1 x hnone =>
    rw [gm06ReduceSingletons, hnone]
    exact ⟨G, Δ, ⟨h⟩, hD, Iff.rfl⟩
  | case2 x v hfind ih =>
    have hv := h.findSingleton_mem v hfind
    obtain ⟨hnew⟩ := h.singletonData_rep v hD h.divisionUnion_subset hv
    have hD' : IsDivision (Δ \ {{(h.vertex v).val}}) :=
      ⟨hD.1.subset sdiff_subset, fun δ hδ => hD.2.1 δ hδ.1, hD.2.2.subset sdiff_subset⟩
    obtain ⟨G', Δ', hrep', hD'', hfeas'⟩ := ih hnew hD'
    rw [gm06ReduceSingletons, hfind]
    exact ⟨G', Δ', hrep', hD'',
      (h.singletonData_feasible_iff v hD h.divisionUnion_subset hv).trans hfeas'⟩

end GraphMinor.Compute.GM06DrawingRep
