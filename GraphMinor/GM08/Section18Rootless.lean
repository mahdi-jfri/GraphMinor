module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18Reduction
import GraphMinor.GM08.Section18ZeroAlpha
import GraphMinor.GM08.Section18Drawing
import GraphMinor.GM12.Section3SchismaticCandidate

/-!
# VIII (18.1) for a graft without roots

Equal cuff counts force the host drawing to have no boundary vertices.
Its alpha minimum can therefore be chosen on a normal schism. The
uniform simulation threshold then gives the required alternative on
surfaces with any number of cuffs.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe u v w

/-- Graph Minors VIII (18.1), pages 285–286, when the target graft has
no roots. The proof applies on a surface with any number of cuffs. -/
theorem Proofs.theorem_18_1_rootless {S : Type w} [TopologicalSpace S]
    [T1Space S] [ConnectedSpace S] (hS : IsSurface S)
    (a b c : ℕ) (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    {α : Type u} {β : Type v} {Y : Graft α β} (DY : GraftDrawing Y.G Y.T S)
    (hroot : Y.T = ∅) :
    ∃ N : ℕ, ∀ (X : Graft α β) (DX : GraftDrawing X.G X.T S),
      IsGraftSimulatedIn Y X ∨
      (∃ C ∈ cuffs S, (DX.drawing.V ∩ C).ncard ≠ (DY.drawing.V ∩ C).ncard) ∨
      (∃ F : Set S, GM07.IsSchism F ∧ DX.drawing.IsNormal F ∧
        (DX.drawing.V ∩ F).ncard ≤ N) ∨
      (∃ C ∈ cuffs S, ∃ F : Set S, DX.drawing.IsNormal F ∧ IsOArc F ∧ GM07.SurroundsCuff F C ∧
        F ∩ bd S ⊆ C ∧ (DX.drawing.V ∩ F).ncard < (DX.drawing.V ∩ C).ncard) := by
  classical
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hYbd : DY.drawing.V ∩ bd S = ∅ := by
    apply (ncard_eq_zero (DY.drawing.finite_V.inter_of_left (bd S))).mp
    rw [← ncard_roots_eq_boundary_vertices DY, hroot, ncard_empty]
  have hYcuff : ∀ C ∈ cuffs S, (DY.drawing.V ∩ C).ncard = 0 := by
    intro C hC
    have hh : DY.drawing.V ∩ C = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x hx
      have hxbd : x ∈ bd S := GM07.connectedComponentIn_subset_of_cuff hC hx.2
      have hh : x ∈ DY.drawing.V ∩ bd S := ⟨hx.1, hxbd⟩
      rw [hYbd] at hh
      exact hh
    rw [hh, ncard_empty]
  obtain ⟨N, hN⟩ := exists_simulation_or_cuff_count_or_surrounding_or_schismatic
    hS a b c h3 he hncyl DY
  refine ⟨N, fun X DX => ?_⟩
  by_cases hdiff : ∃ C ∈ cuffs S,
      (DX.drawing.V ∩ C).ncard ≠ (DY.drawing.V ∩ C).ncard
  · exact Or.inr (Or.inl hdiff)
  have hXbd : DX.drawing.V ∩ bd S = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxV, hxbd⟩
    let C := connectedComponentIn (bd S) x
    have hC : C ∈ cuffs S := ⟨x, hxbd, rfl⟩
    have hcount : (DX.drawing.V ∩ C).ncard = (DY.drawing.V ∩ C).ncard := by
      by_contra hn
      exact hdiff ⟨C, hC, hn⟩
    have hempty : DX.drawing.V ∩ C = ∅ :=
      (ncard_eq_zero (DX.drawing.finite_V.inter_of_left C)).mp (hcount.trans (hYcuff C hC))
    have hh : x ∈ DX.drawing.V ∩ C := ⟨hxV, mem_connectedComponentIn hxbd⟩
    rw [hempty] at hh
    exact hh
  rcases hN X DX with hsim | hcounts | hsur | ⟨F, hF, hnF, hcard⟩
  · exact Or.inl hsim
  · exact (hdiff hcounts).elim
  · exact Or.inr (Or.inr (Or.inr hsur))
  · obtain ⟨P, hP, hnP, hpcount⟩ := exists_normal_schism_at_alpha_of_no_boundary_vertices
      hS h3 he hncyl DX.drawing DX.isProper hXbd
    have hα : GM07.alpha DX.drawing < N :=
      (GM12.alpha_le_normal_schismatic_count hF hnF).trans_lt (by rwa [inter_comm])
    exact Or.inr (Or.inr (Or.inl ⟨P, hP, hnP, hpcount ▸ Nat.le_of_lt hα⟩))

end GraphMinor.GM08
