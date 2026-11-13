module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.CutOArc
import GraphMinor.Surface.ModelCriterion

/-!
# Two-sided cuts in handle surfaces

The cut construction in Graph Minors V, (8.10), has two boundary circles
when the original surface is a sphere with handles. The library cut
construction allows one boundary circle as well. Its normal-word
calculation would give the original surface a crosscap. The model
criterion rules this out for a handle surface.
-/

public section

namespace GraphMinor.GM05

open Set Topology Function Surface

universe u

/-- A circle in a closed handle surface has a cut with two disjoint
boundary lifts. This refines the library circle-cut construction by
excluding its one-sided case with the model criterion. -/
theorem exists_two_sided_handle_cut {S : Type u} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsClosedSurface S) {g₀ : ℕ}
    (eS : S ≃ₜ SurfaceModel g₀ 0 0) {F : Set S} (hO : IsOArc F) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (ψ : Y → S), IsSurface Y ∧ IsCutting ψ F ∧
      ∃ X X' : Set Y, Disjoint X X' ∧ X ∪ X'=ψ ⁻¹' F ∧ IsOArc X ∧ IsOArc X' ∧
        BijOn ψ X F ∧ BijOn ψ X' F := by
  let : CompactSpace S := hS.1
  let : T2Space S := hS.2.1
  have hsurface : IsSurface S := ⟨hS.1,hS.2.1,fun x ↦ (hS.2.2 x).isManifoldPoint⟩
  have hd : Disjoint F (bd S) := Set.disjoint_left.mpr fun x _ hx ↦ hx (hS.2.2 x)
  obtain ⟨Y,tY,t2Y,ψ,hY,hψ,hcase,Z₁,Z₂,u,c,X₁,Y₁,X₂,Y₂,h7,h8,hi,hun,huc,hfu,hfc⟩ :=
    exists_cut_loop hsurface hO hd
  let : CompactSpace Y := hY.1
  have hdcuff := cuff_statement Y hY
  rcases hcase with htwo|hQ
  · exact ⟨Y,tY,ψ,hY,hψ,htwo⟩
  · exfalso
    have ne₀ : (ψ ⁻¹' F).Nonempty := by
      obtain ⟨e⟩ := id hQ
      exact ⟨_, (e 1).2⟩
    have hYc := connected_of_cut hψ hY hQ.isPreconnected rfl ne₀
    obtain ⟨a, b, c', ⟨e⟩⟩ := classification.{u} Y hY hYc
    obtain ⟨x, hx⟩ := ne₀
    have hQb := hψ.2.2.2.2
    have hC : connectedComponentIn (bd Y) x ∈ cuffs Y := ⟨_, hQb hx, rfl⟩
    obtain ⟨φ₀⟩ := hdcuff.2.2 _ hC
    have eQ := oarc_eq φ₀ hQ (hQ.isPreconnected.subset_connectedComponentIn hx hQb)
    obtain ⟨i, hi', φ, g, hg, hs⟩ := exists_one_hole e hC
    obtain ⟨hN, hLf⟩ := erase_facts c' i
    obtain ⟨a₀, ξ, η, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := h7.paths h8 hi huc hfu hfc hψ.1
    rw [hun] at c5 c6
    have L : ArcLift ψ F a₀ ξ η := ⟨c1, c2, c3, c4, c5, fun y y' he hne' => by
      by_cases hy : ψ y ∈ F
      · exact c6 y y' he hne' hy
      · exact absurd (hψ.2.2.1 hy (show ψ y' ∈ Fᶜ from he ▸ hy) he) hne'⟩
    have m0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
    have m1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
    have hξ : ∀ t ∈ Icc (0 : ℝ) 1, ξ t ∈ connectedComponentIn (bd Y) x := fun t ht => by
      rw [← eQ]
      show ψ (ξ t) ∈ F
      rw [c3 t ht, ← c5]
      exact mem_image_of_mem _ ht
    have hη : ∀ t ∈ Icc (0 : ℝ) 1, η t ∈ connectedComponentIn (bd Y) x := fun t ht => by
      rw [← eQ]
      show ψ (η t) ∈ F
      rw [c4 t ht, ← c5]
      exact mem_image_of_mem _ ht
    rcases c9 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exfalso
      have injξ : InjOn ξ (Ico 0 1) := fun p hp q hq he => c7 hp hq (by
        rw [← c3 p (Ico_subset_Icc_self hp), ← c3 q (Ico_subset_Icc_self hq), he])
      have him := loop_image φ c1 hξ injξ e1.symm
      obtain ⟨v, hv, hve⟩ := him.symm.subset (hη 0 m0)
      have ha : a₀ v = a₀ 0 := by rw [← c3 v hv, hve, c4 0 m0]
      rcases eq_or_lt_of_le hv.2 with rfl | hv1
      · exact c8 0 m0 (e1.symm.trans hve)
      · have := c7 ⟨hv.1, hv1⟩ ⟨le_rfl, zero_lt_one⟩ ha
        subst this
        exact c8 0 m0 hve
    · obtain ⟨g', -, hp, -⟩ := loop_one_aux hY L hψ.1 hψ.2.1 hC φ hi' hLf hg hs hξ hη (conc_inj c3 c4 c7 c8 e1 e2) e1 e2
      obtain ⟨w, h5, h6⟩ := nf_blkD (a := a) (b := b) (c := c') hi' hN hLf
      obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
      rw [length_erase_range hi'] at e'
      have hc := (modelCriterion.2 g₀ 0 0 a (b+1) (c'-1)).mp ⟨eS.symm.trans e'⟩
      have hb := hc.2.2.mp rfl
      omega

end GraphMinor.GM05
