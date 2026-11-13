module

public import GraphMinor.Surface.TopologyStatements
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Ordered boundary parameters give alternating port pairs

Part IV, Sections 7b and 7c of the planarity note traverses a disc boundary
and reads its ports in that order. Four ports in strict parameter order
alternate when the first is paired with the third. The two closed boundary
arcs between that opposite pair separate the other two ports after the
opposite pair is removed. This file proves that order-to-crossing step.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Topology Surface

private theorem components_ne_of_closed_boundary_arcs {C L R : Set ℂ} {a c b d : ℂ}
    (hL : IsClosed L) (hR : IsClosed R) (hcover : L ∪ R = C)
    (hinter : L ∩ R = {a,c}) (hbL : b ∈ L) (hbR : b ∉ R) (hdR : d ∈ R) (hdL : d ∉ L) :
    connectedComponentIn (C \ {a,c}) b ≠ connectedComponentIn (C \ {a,c}) d := by
  have hbC : b ∈ C \ {a,c} := by
    refine ⟨hcover ▸ Or.inl hbL, ?_⟩
    intro he
    have hm : b ∈ L ∩ R := hinter.symm ▸ he
    exact hbR hm.2
  have hdC : d ∈ C \ {a,c} := by
    refine ⟨hcover ▸ Or.inr hdR, ?_⟩
    intro he
    have hm : d ∈ L ∩ R := hinter.symm ▸ he
    exact hdL hm.1
  intro he
  let K := connectedComponentIn (C \ {a,c}) b
  have hbK : b ∈ K := mem_connectedComponentIn hbC
  have hdK : d ∈ K := by
    change d ∈ connectedComponentIn (C \ {a,c}) b
    rw [he]
    exact mem_connectedComponentIn hdC
  have hKsub : K ⊆ C \ {a,c} := connectedComponentIn_subset _ _
  have hKcover : K ⊆ Lᶜ ∪ Rᶜ := by
    intro x hx
    by_cases hxL : x ∈ L
    · refine Or.inr (fun hxR => (hKsub hx).2 ?_)
      have hm : x ∈ L ∩ R := ⟨hxL,hxR⟩
      exact hinter ▸ hm
    · exact Or.inl hxL
  obtain ⟨x,hxK,hxL,hxR⟩ := isPreconnected_connectedComponentIn (F := C \ {a,c}) (x := b)
    Lᶜ Rᶜ hL.isOpen_compl hR.isOpen_compl hKcover ⟨d,hdK,hdL⟩ ⟨b,hbK,hbR⟩
  have hxC : x ∈ L ∪ R := hcover.symm ▸ (hKsub hxK).1
  exact hxC.elim hxL hxR

/-- Part IV, Sections 7b and 7c: four strictly ordered interior parameters
of a once-around boundary traversal give crossing opposite pairs. The
traversal is injective on each half-open unit interval. -/
theorem pairsCrossOn_of_ordered_boundary_parameters {f : ℝ → ℂ} (hf : Continuous f)
    (hinj : InjOn f (Ico (0 : ℝ) 1)) (hinj' : InjOn f (Ioc (0 : ℝ) 1))
    {s t r q : ℝ}
    (hs : 0 < s) (hst : s < t) (htr : t < r) (hrq : r < q) (hq : q < 1) :
    PairsCrossOn (f '' Icc (0 : ℝ) 1) (f s) (f r) (f t) (f q) := by
  have hs1 : s < 1 := hst.trans (htr.trans (hrq.trans hq))
  have ht0 : 0 < t := hs.trans hst
  have ht1 : t < 1 := htr.trans (hrq.trans hq)
  have hr0 : 0 < r := ht0.trans htr
  have hr1 : r < 1 := hrq.trans hq
  have hq0 : 0 < q := hr0.trans hrq
  have hfi : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, f x = f y → x = y := by
    intro x hx y hy he
    by_cases hy1 : y < 1
    · exact hinj ⟨hx.1.le,hx.2⟩ ⟨hy.1,hy1⟩ he
    · exact hinj' ⟨hx.1,hx.2.le⟩ ⟨by simpa only [le_antisymm hy.2 (le_of_not_gt hy1)] using zero_lt_one,hy.2⟩ he
  have hneq : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1, x ≠ y → f x ≠ f y := by
    intro x hx y hy hne he
    exact hne (hfi x hx y ⟨hy.1.le,hy.2.le⟩ he)
  let L := f '' Icc s r
  let R := f '' Icc r 1 ∪ f '' Icc 0 s
  have hL : IsClosed L := (isCompact_Icc.image hf).isClosed
  have hR : IsClosed R := (isCompact_Icc.image hf).isClosed.union (isCompact_Icc.image hf).isClosed
  have hcover : L ∪ R = f '' Icc (0 : ℝ) 1 := by
    apply Subset.antisymm
    · rintro x (⟨θ,hθ,rfl⟩ | ⟨θ,hθ,rfl⟩ | ⟨θ,hθ,rfl⟩)
      · exact ⟨θ,⟨hs.le.trans hθ.1,hθ.2.trans hr1.le⟩,rfl⟩
      · exact ⟨θ,⟨hr0.le.trans hθ.1,hθ.2⟩,rfl⟩
      · exact ⟨θ,⟨hθ.1,hθ.2.trans hs1.le⟩,rfl⟩
    · rintro x ⟨θ,hθ,rfl⟩
      by_cases hθs : θ ≤ s
      · exact Or.inr (Or.inr ⟨θ,⟨hθ.1,hθs⟩,rfl⟩)
      · by_cases hθr : θ ≤ r
        · exact Or.inl ⟨θ,⟨(le_of_not_ge hθs),hθr⟩,rfl⟩
        · exact Or.inr (Or.inl ⟨θ,⟨(le_of_not_ge hθr),hθ.2⟩,rfl⟩)
  have hinter : L ∩ R = {f s,f r} := by
    apply Subset.antisymm
    · rintro x ⟨⟨θ,hθ,rfl⟩,hxR⟩
      rcases hxR with ⟨ρ,hρ,he⟩ | ⟨ρ,hρ,he⟩
      · have heq : θ = ρ := hfi θ ⟨hs.trans_le hθ.1,hθ.2.trans_lt hr1⟩
          ρ ⟨hr0.le.trans hρ.1,hρ.2⟩ he.symm
        have hθr : θ = r := le_antisymm hθ.2 (heq.symm ▸ hρ.1)
        exact Or.inr (congrArg f hθr)
      · have heq : θ = ρ := hfi θ ⟨hs.trans_le hθ.1,hθ.2.trans_lt hr1⟩
          ρ ⟨hρ.1,hρ.2.trans hs1.le⟩ he.symm
        have hθs : θ = s := le_antisymm (heq.symm ▸ hρ.2) hθ.1
        exact Or.inl (congrArg f hθs)
    · intro x hx
      rcases hx with hxs | hxr
      · subst x
        exact ⟨⟨s,⟨le_rfl,(hst.trans htr).le⟩,rfl⟩,Or.inr ⟨s,⟨hs.le,le_rfl⟩,rfl⟩⟩
      · subst x
        exact ⟨⟨r,⟨(hst.trans htr).le,le_rfl⟩,rfl⟩,Or.inl ⟨r,⟨le_rfl,hr1.le⟩,rfl⟩⟩
  have hsr := hneq s ⟨hs,hs1⟩ r ⟨hr0,hr1⟩ (hst.trans htr).ne
  have htq := hneq t ⟨ht0,ht1⟩ q ⟨hq0,hq⟩ (htr.trans hrq).ne
  have hst' := hneq s ⟨hs,hs1⟩ t ⟨ht0,ht1⟩ hst.ne
  have hsq := hneq s ⟨hs,hs1⟩ q ⟨hq0,hq⟩ (hst.trans (htr.trans hrq)).ne
  have hrt := hneq r ⟨hr0,hr1⟩ t ⟨ht0,ht1⟩ htr.ne'
  have hrq' := hneq r ⟨hr0,hr1⟩ q ⟨hq0,hq⟩ hrq.ne
  have hbL : f t ∈ L := ⟨t,⟨hst.le,htr.le⟩,rfl⟩
  have hdR : f q ∈ R := Or.inl ⟨q,⟨hrq.le,hq.le⟩,rfl⟩
  have hbR : f t ∉ R := by
    intro hm
    have he : f t ∈ L ∩ R := ⟨hbL,hm⟩
    rw [hinter] at he
    exact he.elim hst'.symm hrt.symm
  have hdL : f q ∉ L := by
    intro hm
    have he : f q ∈ L ∩ R := ⟨hm,hdR⟩
    rw [hinter] at he
    exact he.elim hsq.symm hrq'.symm
  refine ⟨⟨s,⟨hs.le,hs1.le⟩,rfl⟩,⟨t,⟨ht0.le,ht1.le⟩,rfl⟩,
    ⟨r,⟨hr0.le,hr1.le⟩,rfl⟩,⟨q,⟨hq0.le,hq.le⟩,rfl⟩,
    hsr,htq,hst',hsq,hrt,hrq',?_⟩
  exact components_ne_of_closed_boundary_arcs hL hR hcover hinter hbL hbR hdR hdL

end GraphMinor.LRPlanarity
