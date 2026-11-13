module

public import GraphMinor.GM07.CuffShift
import GraphMinor.GM07.Taper
import GraphMinor.GM07.Section11f

/-!
# Making boundary contacts finite

In the extraction step of VIII (18.1), push a normal set off a cuff
except at drawing vertices. The collar taper fixes the drawing and all
other cuffs. Thus it preserves normality and the vertex count, while
retaining the homotopy needed for the planarity tests.
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

/-- Push every normal set off a chosen cuff except at drawing vertices.
This supplies finite boundary contacts without increasing the count in
VIII (18.1). The same map works for every normal set. -/
theorem exists_normal_cuff_push {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) (G : Drawing S) {C : Set S} (hC : C ∈ cuffs S) :
    ∃ (h : S → S) (H : unitInterval × S → S), GM07.IsCuffShift C h H ∧
      (∀ x ∈ G.U, h x = x) ∧
      ∀ X : Set S, G.IsNormal X → G.IsNormal (h '' X) ∧
        (h '' X) ∩ C ⊆ G.V ∧ (G.V ∩ h '' X).ncard = (G.V ∩ X).ncard := by
  have : T2Space S := hS.2.1
  let Z := G.U ∪ (bd S \ C)
  have hZ : IsClosed Z := G.isClosed_U.union (GM07.isClosed_bd_diff_cuff hS hC)
  obtain ⟨φ⟩ := (cuff_statement S hS).2.2 C hC
  obtain ⟨H, hH, h0, hi, hfix, hback, hcuff, hfixall, _⟩ :=
    GM07.exists_taper_sides hS hC φ hZ
  let h : S → S := fun x => H (1, x)
  have hfixU : ∀ x ∈ G.U, h x = x := fun x hx => hfix x (Or.inl hx)
  have hbackU : ∀ x, h x ∈ G.U → x ∈ G.U := by
    intro x hx
    have hxZ := hback x (Or.inl hx)
    have heq : h x = x := hfix x hxZ
    exact heq ▸ hx
  refine ⟨h, H, ⟨hH.comp (continuous_const.prodMk continuous_id), hH, hi, h0,
    fun _ => rfl, ?_⟩, hfixU, fun X hnX => ?_⟩
  · intro x hxbd hxC
    exact ⟨hfix x (Or.inr ⟨hxbd, hxC⟩), fun t => hfixall t x (Or.inr ⟨hxbd, hxC⟩)⟩
  · have hn : G.IsNormal (h '' X) := by
      rintro z ⟨⟨x, hx, rfl⟩, hzU⟩
      have hxU := hbackU x hzU
      rw [hfixU x hxU]
      exact hnX ⟨hx, hxU⟩
    refine ⟨hn, ?_, ?_⟩
    · rintro z ⟨hzX, hzC⟩
      obtain ⟨x, _, rfl⟩ := hzX
      have hzZ := hcuff x hzC
      have hzU : h x ∈ G.U := hzZ.resolve_right (fun hh => hh.2 hzC)
      exact hn ⟨mem_image_of_mem h ‹x ∈ X›, hzU⟩
    · congr 1
      ext x
      constructor
      · rintro ⟨hxV, y, hy, he⟩
        have hyU : y ∈ G.U := hbackU y (he ▸ G.V_subset_U hxV)
        have hyx : y = x := (hfixU y hyU).symm.trans he
        exact ⟨hxV, hyx ▸ hy⟩
      · rintro ⟨hxV, hxX⟩
        exact ⟨hxV, x, hxX, hfixU x (G.V_subset_U hxV)⟩

end GraphMinor.GM08
