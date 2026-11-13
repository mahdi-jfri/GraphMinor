module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18Reduction
import GraphMinor.GM08.Section18CircleSchism
import GraphMinor.GM12.Section3LoopCuffClassification
import GraphMinor.GM12.Section3ThetaSurrounding

/-!
# VIII (18.1) on a surface with one cuff

A branched schismatic set has loops surrounding distinct cuffs. Thus on
one cuff the minimum schismatic set is a circle. The normal-circle
extraction supplies the printed small-schism alternative.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe u v w

private theorem isOArc_of_schismatic_one_cuff {S : Type w} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsSurface S) {C X : Set S} (hc : cuffs S = {C})
    (hx : GM07.IsSchismatic X) : IsOArc X := by
  have : T2Space S := hS.2.1
  have hc' : C ∈ cuffs S := by rw [hc]; exact mem_singleton C
  have huniq : ∀ D ∈ cuffs S, D = C := fun D hD => mem_singleton_iff.mp (hc ▸ hD)
  rcases hx.1 with ho | hbar | hwedge | htheta
  · exact ho
  · obtain ⟨A, B, P, a, b, hA, hB, hAB, hP, ha, hb, hPA, hPB, heq⟩ := hbar
    obtain ⟨D, E, hD, hE, hDE⟩ := GM12.surrounding_cuffs_of_schismatic_x1
      hS ⟨C, hc'⟩ hA hB hAB hP ha hb hPA hPB (heq ▸ hx)
    exact (hDE ((huniq D hD.1).trans (huniq E hE.1).symm)).elim
  · obtain ⟨A, B, a, hA, hB, hAB, heq⟩ := hwedge
    obtain ⟨D, E, hD, hE, hDE⟩ := GM12.surrounding_cuffs_of_schismatic_x2
      hS ⟨C, hc'⟩ hA hB hAB (heq ▸ hx)
    exact (hDE ((huniq D hD.1).trans (huniq E hE.1).symm)).elim
  · obtain ⟨P, Q, R, a, b, hab, hP, hQ, hR, hPQ, hPR, hQR, heq⟩ := htheta
    obtain ⟨D, E, _, hD, hE, _, hDE, _⟩ := GM12.surrounding_pairs_of_schismatic_theta
      hS ⟨C, hc'⟩ hab hP hQ hR hPQ hPR hQR (heq ▸ hx)
    exact (hDE ((huniq D hD.1).trans (huniq E hE.1).symm)).elim

/-- Graph Minors VIII (18.1), pages 285–286, for a surface with exactly
one cuff. These are all four printed alternatives, with no extra proof
hypotheses. -/
theorem Proofs.theorem_18_1_one_cuff {S : Type w} [TopologicalSpace S]
    [T1Space S] [ConnectedSpace S] (hS : IsSurface S)
    (a b c : ℕ) (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    {C : Set S} (hc : cuffs S = {C})
    {α : Type u} {β : Type v} {Y : Graft α β} (DY : GraftDrawing Y.G Y.T S) :
    ∃ N : ℕ, ∀ (X : Graft α β) (DX : GraftDrawing X.G X.T S),
      IsGraftSimulatedIn Y X ∨
      (∃ C ∈ cuffs S, (DX.drawing.V ∩ C).ncard ≠ (DY.drawing.V ∩ C).ncard) ∨
      (∃ F : Set S, GM07.IsSchism F ∧ DX.drawing.IsNormal F ∧
        (DX.drawing.V ∩ F).ncard ≤ N) ∨
      (∃ C ∈ cuffs S, ∃ F : Set S, DX.drawing.IsNormal F ∧ IsOArc F ∧ GM07.SurroundsCuff F C ∧
        F ∩ bd S ⊆ C ∧ (DX.drawing.V ∩ F).ncard < (DX.drawing.V ∩ C).ncard) := by
  obtain ⟨N, hN⟩ := exists_simulation_or_cuff_count_or_surrounding_or_schismatic
    hS a b c h3 he hncyl DY
  refine ⟨N, fun X DX => ?_⟩
  rcases hN X DX with hsim | hcounts | hsur | ⟨F, hF, hnF, hcard⟩
  · exact Or.inl hsim
  · exact Or.inr (Or.inl hcounts)
  · exact Or.inr (Or.inr (Or.inr hsur))
  · obtain ⟨P, _, hP, hnP, hle⟩ := exists_normal_schism_of_non_nearPlanar_oArc
      hS a b c h3 he DX.drawing DX.isProper (isOArc_of_schismatic_one_cuff hS hc hF) hnF hF.2.1
    exact Or.inr (Or.inr (Or.inl ⟨P, hP, hnP, hle.trans (Nat.le_of_lt hcard)⟩))

end GraphMinor.GM08
