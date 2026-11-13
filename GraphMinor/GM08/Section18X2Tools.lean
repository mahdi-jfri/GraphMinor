module

public import GraphMinor.GM08.Section18Complexity
public import GraphMinor.GM19.CutMap
import GraphMinor.GM08.Section18SurroundSides
import GraphMinor.GM19.FeatureOrient
import GraphMinor.Surface.CutComp
import GraphMinor.GM07.Section3

/-!
# Tools for the cut along two circles that meet at one point

* `image_subset_or_of_clopen`: if `Σ` is the union of two closed sets that
  meet only inside the cut set `F`, then each connected piece of the cut
  surface maps into one of them. The inside of the piece misses the lift of `F`
  and is connected, and it is dense in the piece.
* `mem_closure_image_sdiff`: a point of a piece `V` of a cut maps into the
  closure of the points that only `V` covers.
* `isCutMap_sum_compl`: a cut of an open and closed part, put next to the
  rest, is a cut of the whole surface.
* `ncard_preimage_le_of_fiber`: lift counts of single points add up.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

variable {S T : Type w} [TopologicalSpace S] [TopologicalSpace T]

/-- In a connected piece `Q` of a surface, the points off the boundary form a
connected set that is dense in `Q`. -/
theorem isPreconnected_and_closure_of_clopen (hT : IsSurface T) {Q : Set T} (hQ : IsClopen Q)
    [ConnectedSpace Q] : IsPreconnected (Q \ bd T) ∧ Q ⊆ closure (Q \ bd T) := by
  have hQs : IsSurface Q := isSurface_sub hT hQ
  have : T2Space Q := hQs.2.1
  have heq : Q \ bd T = Subtype.val '' (bd Q)ᶜ := by
    ext z
    constructor
    · rintro ⟨hzQ, hzb⟩
      exact ⟨⟨z, hzQ⟩, fun h => hzb ((mem_bd_sub hQ.isOpen).mp h), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, fun h => hy ((mem_bd_sub hQ.isOpen).mpr h)⟩
  rw [heq]
  refine ⟨(GM19.isPreconnected_compl_bd hQs).image _ continuous_subtype_val.continuousOn, ?_⟩
  intro z hz
  have hd := (dense_compl_bd hQs).closure_eq
  have : (⟨z, hz⟩ : Q) ∈ closure (bd Q)ᶜ := hd ▸ mem_univ _
  exact (image_closure_subset_closure_image continuous_subtype_val) ⟨_, this, rfl⟩

/-- **A connected piece maps into one side.** Let `Σ` be the union of two
closed sets `P₁, P₂` that meet only inside `F`. A map that sends no inner
point of a connected open and closed piece into `F` sends the piece into `P₁` or
into `P₂`. -/
theorem image_subset_or_of_clopen (hT : IsSurface T) {θ : T → S} (hθ : Continuous θ)
    {F P₁ P₂ : Set S} (hP₁ : IsClosed P₁) (hP₂ : IsClosed P₂) (hcov : P₁ ∪ P₂ = univ)
    (hint : P₁ ∩ P₂ ⊆ F) {Q : Set T} (hQ : IsClopen Q) [ConnectedSpace Q]
    (hbd : ∀ z ∈ Q, θ z ∈ F → z ∈ bd T) : θ '' Q ⊆ P₁ ∨ θ '' Q ⊆ P₂ := by
  obtain ⟨hc, hcl⟩ := isPreconnected_and_closure_of_clopen hT hQ
  have hi : IsPreconnected (θ '' (Q \ bd T)) := hc.image _ hθ.continuousOn
  have hsub : θ '' (Q \ bd T) ⊆ P₁ ∪ P₂ := fun _ _ => hcov ▸ mem_univ _
  have hmiss : θ '' (Q \ bd T) ∩ (P₁ ∩ P₂) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro _ ⟨⟨z, hz, rfl⟩, hzP⟩
    exact hz.2 (hbd z hz.1 (hint hzP))
  have himg : θ '' Q ⊆ closure (θ '' (Q \ bd T)) :=
    (image_mono hcl).trans (image_closure_subset_closure_image hθ)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hi) P₁ P₂ hP₁ hP₂ hsub hmiss with h | h
  · exact Or.inl (himg.trans (closure_minimal h hP₁))
  · exact Or.inr (himg.trans (closure_minimal h hP₂))

/-- **The points only one side covers.** For a cut map along `F`, a point of
a connected open and closed piece `V` maps into the closure of the points over
which `V` holds a point and `Vᶜ` holds none. -/
theorem mem_closure_image_sdiff (hT : IsSurface T) {θ : T → S} {F : Set S}
    (hc : GM19.IsCutMap θ F) {V : Set T} (hV : IsClopen V) [ConnectedSpace V] {y : T}
    (hy : y ∈ V) : θ y ∈ closure (θ '' V \ θ '' Vᶜ) := by
  obtain ⟨-, hcl⟩ := isPreconnected_and_closure_of_clopen hT hV
  have hsub : θ '' (V \ bd T) ⊆ θ '' V \ θ '' Vᶜ := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨⟨z, hz.1, rfl⟩, ?_⟩
    rintro ⟨w, hw, hwz⟩
    by_cases hzF : θ z ∈ F
    · exact hz.2 (hc.2.2.2.2 hzF)
    · have : w = z := hc.2.2.1 (show θ w ∈ Fᶜ by rw [hwz]; exact hzF) hzF hwz
      exact hw (this ▸ hz.1)
  exact closure_mono hsub ((image_closure_subset_closure_image hc.1) ⟨y, hcl hy, rfl⟩)

/-- **Cutting one open and closed part, for cut maps.** A cut map of `V` along
`F ⊆ V`, put next to the rest of the surface, is a cut map of the whole surface
along `F`. -/
theorem isCutMap_sum_compl {V F : Set T} (hFV : F ⊆ V) {Y : Type w} [TopologicalSpace Y]
    {ρ : Y → V} (hρ : GM19.IsCutMap ρ (Subtype.val ⁻¹' F)) :
    GM19.IsCutMap (Sum.elim (Subtype.val ∘ ρ) (Subtype.val : (Vᶜ : Set T) → T)) F := by
  refine ⟨continuous_sum_dom.mpr ⟨continuous_subtype_val.comp hρ.1, continuous_subtype_val⟩,
    ?_, ?_, fun x => ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ V
    · obtain ⟨y, hy⟩ := hρ.2.1 ⟨x, hx⟩
      exact ⟨Sum.inl y, congrArg Subtype.val hy⟩
    · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩
  · rintro (y₁ | y₁) hy₁ (y₂ | y₂) hy₂ heq
    · congr 1
      exact hρ.2.2.1 hy₁ hy₂ (Subtype.ext heq)
    · exfalso
      change (ρ y₁).1 = y₂.1 at heq
      exact y₂.2 (heq ▸ (ρ y₁).2)
    · exfalso
      change y₁.1 = (ρ y₂).1 at heq
      exact y₁.2 (heq.symm ▸ (ρ y₂).2)
    · congr 1
      exact Subtype.ext heq
  · have hsub : Sum.elim (Subtype.val ∘ ρ) (Subtype.val : (Vᶜ : Set T) → T) ⁻¹' {x} ⊆
        Sum.inl '' (⋃ h : x ∈ V, ρ ⁻¹' {⟨x, h⟩}) ∪ Sum.inr '' {z | z.1 = x} := by
      rintro (y | z) hy
      · refine Or.inl ⟨y, ?_, rfl⟩
        have hx : x ∈ V := (show (ρ y).1 = x from hy) ▸ (ρ y).2
        exact mem_iUnion.mpr ⟨hx, Subtype.ext hy⟩
      · exact Or.inr ⟨z, hy, rfl⟩
    refine Set.Finite.subset (Set.Finite.union (Set.Finite.image _ ?_) (Set.Finite.image _ ?_)) hsub
    · by_cases hx : x ∈ V
      · exact (hρ.2.2.2.1 ⟨x, hx⟩).subset (iUnion_subset fun _ => subset_rfl)
      · rw [iUnion_eq_empty.mpr fun h => absurd h hx]
        exact finite_empty
    · refine Set.Subsingleton.finite fun a ha b hb => Subtype.ext (ha.trans hb.symm)
  · rintro (y | z) hy
    · exact GM07.mem_bd_inl (hρ.2.2.2.2 hy)
    · exact absurd (hFV hy) z.2

omit [TopologicalSpace T] in
/-- Over a point of `V`, the glued map has the points of the cut of `V`. -/
theorem ncard_preimage_sum_compl {V : Set T} {Y : Type w} {ρ : Y → V} {x : T} (hx : x ∈ V) :
    (Sum.elim (Subtype.val ∘ ρ) (Subtype.val : (Vᶜ : Set T) → T) ⁻¹' {x}).ncard =
      (ρ ⁻¹' {⟨x, hx⟩}).ncard := by
  have heq : Sum.elim (Subtype.val ∘ ρ) (Subtype.val : (Vᶜ : Set T) → T) ⁻¹' {x} =
      Sum.inl '' (ρ ⁻¹' {⟨x, hx⟩}) := by
    ext (y | z)
    · simp only [Sum.elim_inl, Function.comp_apply, mem_preimage, mem_singleton_iff, mem_image,
        Subtype.ext_iff, Sum.inl.injEq]
      constructor
      · intro h
        exact ⟨y, h, rfl⟩
      · rintro ⟨y', hy', rfl⟩
        exact hy'
    · simp only [Sum.elim_inr, mem_preimage, mem_singleton_iff, mem_image, reduceCtorEq,
        and_false, exists_false, iff_false]
      intro hzx
      exact z.2 (hzx ▸ hx)
  rw [heq, ncard_image_of_injective _ Sum.inl_injective]

omit [TopologicalSpace T] in
/-- Over a point off `V`, the glued map has one point. -/
theorem ncard_preimage_sum_compl_of_notMem {V : Set T} {Y : Type w} {ρ : Y → V} {x : T}
    (hx : x ∉ V) :
    (Sum.elim (Subtype.val ∘ ρ) (Subtype.val : (Vᶜ : Set T) → T) ⁻¹' {x}).ncard = 1 := by
  refine ncard_eq_one.mpr ⟨Sum.inr ⟨x, hx⟩, ?_⟩
  ext (y | z)
  · simp only [Sum.elim_inl, Function.comp_apply, mem_preimage, mem_singleton_iff,
      reduceCtorEq, iff_false]
    intro h
    exact hx (h ▸ (ρ y).2)
  · simp only [Sum.elim_inr, mem_preimage, mem_singleton_iff, Sum.inr.injEq, Subtype.ext_iff]

open Classical in
/-- **Lift counts add up.** If each point of a finite set `B` has at most two
points over it, except that one point `u` may have four, then `B` has at most
`2 |B| + 2` points over it. -/
theorem ncard_preimage_le_of_fiber {X Z : Type*} {f : X → Z} {u : Z} {B : Set Z}
    (hB : B.Finite) (hfin : ∀ y, (f ⁻¹' {y}).Finite)
    (h : ∀ y ∈ B, (f ⁻¹' {y}).ncard ≤ 2 + if y = u then 2 else 0) :
    (f ⁻¹' B).ncard ≤ 2 * B.ncard + 2 := by
  classical
  suffices key : (f ⁻¹' B).ncard ≤ 2 * B.ncard + if u ∈ B then 2 else 0 by
    split_ifs at key <;> omega
  induction B, hB using Set.Finite.induction_on with
  | empty => simp
  | @insert a s has hs ih =>
    have hpre : f ⁻¹' insert a s = f ⁻¹' {a} ∪ f ⁻¹' s := by
      rw [← preimage_union, insert_eq]
    have hfs : (f ⁻¹' s).Finite := hs.preimage' fun y _ => hfin y
    have h1 := ncard_union_le (f ⁻¹' {a}) (f ⁻¹' s)
    have h2 := h a (mem_insert a s)
    have h3 := ih fun y hy => h y (mem_insert_of_mem a hy)
    rw [hpre, ncard_insert_of_notMem has hs]
    by_cases hau : a = u
    · subst hau
      simp only [if_pos rfl, mem_insert_iff, true_or, if_neg has] at h2 h3 ⊢
      omega
    · have : (u ∈ insert a s) ↔ u ∈ s := by
        simp only [mem_insert_iff]
        exact ⟨fun h => h.resolve_left fun h' => hau h'.symm, Or.inr⟩
      simp only [if_neg hau, this] at h2 h3 ⊢
      split_ifs at h3 ⊢ <;> omega

end GraphMinor.GM08
