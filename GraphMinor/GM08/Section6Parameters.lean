module

public import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.ArcTools
import GraphMinor.GM08.Section6Components
import GraphMinor.GM08.Section6Chord
import GraphMinor.GM08.Section6Excursions

/-!
# Parameter intervals for removed boundary arcs

For VIII (6.2), page 264, the portion of the first boundary inside an
excursion disc is connected and open relative to that boundary. After
cutting at a common retained arc, this file identifies that portion with
an open parameter interval and identifies its closure with the corresponding
closed interval.
-/

public section

namespace GraphMinor.GM08

open Set Topology Surface

universe u

local notation "𝕀" => unitInterval

/-- A connected open part of an embedded arc, avoiding both endpoints,
is parametrized by an open subinterval. Its closure is parametrized by
the corresponding closed subinterval. -/
theorem exists_parameters_for_connected_open_part_of_arc
    {X : Type u} [TopologicalSpace X] [T2Space X] {f : 𝕀 → X} (hf : IsArcMap f)
    {O : Set X} (hO : IsOpen O) (hpre : IsPreconnected (range f ∩ O))
    (hne : (range f ∩ O).Nonempty) (h0 : f 0 ∉ O) (h1 : f 1 ∉ O) :
    ∃ a b : 𝕀, a < b ∧ range f ∩ O = f '' Ioo a b ∧
      closure (range f ∩ O) = f '' Icc a b := by
  let Q : Set 𝕀 := f ⁻¹' O
  let J : Set ℝ := Subtype.val '' Q
  have hemb := hf.1.isClosedEmbedding hf.2
  have hQP : f '' Q = range f ∩ O := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, rfl⟩, ht⟩
    · rintro ⟨⟨t, rfl⟩, ht⟩
      exact ⟨t, ht, rfl⟩
  have hQpre : IsPreconnected Q := by
    apply hemb.isEmbedding.isInducing.isPreconnected_image.mp
    rwa [hQP]
  have hJpre : IsPreconnected J := hQpre.image Subtype.val continuous_subtype_val.continuousOn
  have hJne : J.Nonempty := by
    obtain ⟨x, ⟨t, rfl⟩, ht⟩ := hne
    exact ⟨t.1, t, ht, rfl⟩
  have hJsub : J ⊆ Icc 0 1 := by
    rintro _ ⟨t, _, rfl⟩
    exact t.2
  have hJdesc : J = Ioo (0 : ℝ) 1 ∩ (extI f) ⁻¹' O := by
    ext r
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht0 : t ≠ 0 := fun he => h0 (he ▸ ht)
      have ht1 : t ≠ 1 := fun he => h1 (he ▸ ht)
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact lt_of_le_of_ne t.2.1 (fun he => ht0 (Subtype.ext he.symm))
      · exact lt_of_le_of_ne t.2.2 (fun he => ht1 (Subtype.ext he))
      · change f t ∈ O at ht
        change extI f t.1 ∈ O
        rw [extI_coe]
        exact ht
    · rintro ⟨hr, hrf⟩
      let t : 𝕀 := ⟨r, hr.1.le, hr.2.le⟩
      refine ⟨t, ?_, rfl⟩
      change f t ∈ O
      change extI f r ∈ O at hrf
      rwa [extI_of_mem f ⟨hr.1.le, hr.2.le⟩] at hrf
  have hJopen : IsOpen J := by
    rw [hJdesc]
    exact isOpen_Ioo.inter (hO.preimage (continuous_extI hf.1))
  obtain ⟨a, b, ha, hab, hb, hJeq, _⟩ :=
    exists_endpoints_of_open_preconnected_subset_unitInterval hJopen hJpre hJne hJsub
  let α : 𝕀 := ⟨a, ha, hab.le.trans hb⟩
  let β : 𝕀 := ⟨b, ha.trans hab.le, hb⟩
  have hαβ : α < β := hab
  have hQeq : Q = Ioo α β := by
    ext t
    have ht : t ∈ Q ↔ t.1 ∈ J := by
      constructor
      · intro ht
        exact ⟨t, ht, rfl⟩
      · rintro ⟨s, hs, he⟩
        exact (Subtype.ext he : s = t) ▸ hs
    rw [hJeq] at ht
    exact ht
  have hPeq : range f ∩ O = f '' Ioo α β := by rw [← hQP, hQeq]
  refine ⟨α, β, hαβ, hPeq, ?_⟩
  rw [hPeq, hemb.closure_image_eq, closure_Ioo hαβ.ne]

/-- Removing the open part of an embedded arc leaves exactly its two
endpoints. This identifies the endpoints after passing between the two
parametrizations in the excursion construction. -/
theorem range_sdiff_open_arc_image {X : Type u} [TopologicalSpace X]
    {a : 𝕀 → X} (ha : IsArcMap a) :
    range a \ a '' Ioo (0 : 𝕀) 1 = {a 0, a 1} := by
  apply subset_antisymm
  · rintro x ⟨⟨t, rfl⟩, hnot⟩
    by_cases ht0 : t = 0
    · exact Or.inl (congrArg a ht0)
    by_cases ht1 : t = 1
    · exact Or.inr (congrArg a ht1)
    exact False.elim (hnot ⟨t, ⟨lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht0),
      lt_of_le_of_ne (unitInterval.le_one t) ht1⟩, rfl⟩)
  · rintro x (rfl | rfl)
    · refine ⟨⟨0, rfl⟩, ?_⟩
      rintro ⟨t, ht, he⟩
      exact (ne_of_gt ht.1) (ha.2 he)
    · refine ⟨⟨1, rfl⟩, ?_⟩
      rintro ⟨t, ht, he⟩
      exact (ne_of_lt ht.2) (ha.2 he)

/-- Once a common old boundary arc is retained, every removed boundary arc
is an open interval on its complementary parametrization. This connects
the geometric excursion discs to the interval gluing construction of
VIII (6.2). -/
theorem exists_parameters_for_removed_boundary_arc
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x) {D E : Set S} (hE : IsClosedDisc E)
    (hDE : D ⊆ E) {q f a b ℓ : 𝕀 → S}
    (hOld : IsTwoArcs q f) (hOldr : range q ∪ range f = discBd D)
    (hNew : IsTwoArcs a b) (hNewr : range a ∪ range b = discBd D)
    (hEb : discBd E = range a ∪ range ℓ) (ha0 : a 0 = ℓ 0) (ha1 : a 1 = ℓ 1)
    (hmeet : ∀ r, ℓ r ∈ D → r = 0 ∨ r = 1) (hqE : range q ⊆ discBd E) :
    ∃ α β : 𝕀, α < β ∧ discInt E ∩ discBd D = f '' Ioo α β ∧
      closure (discInt E ∩ discBd D) = f '' Icc α β := by
  have hP : range f ∩ discInt E = discInt E ∩ discBd D := by
    apply subset_antisymm
    · rintro x ⟨hxf, hxE⟩
      exact ⟨hxE, hOldr ▸ Or.inr hxf⟩
    · rintro x ⟨hxE, hxD⟩
      rw [← hOldr] at hxD
      rcases hxD with hxq | hxf
      · exact False.elim (hxE.2 (hqE hxq))
      · exact ⟨hxf, hxE⟩
  have hremoved := removed_arc_eq_old_boundary_inside hDE hNew hNewr hEb ha0 ha1 hmeet
  have hpre : IsPreconnected (range f ∩ discInt E) := by
    rw [hP, hremoved]
    exact isPreconnected_Ioo.image b hNew.2.1.continuousOn
  have hne : (range f ∩ discInt E).Nonempty := by
    rw [hP, hremoved]
    let m : 𝕀 := ⟨1 / 2, by constructor <;> norm_num⟩
    refine ⟨b m, m, ?_, rfl⟩
    constructor
    · change (0 : ℝ) < 1 / 2
      norm_num
    · change (1 / 2 : ℝ) < 1
      norm_num
  have hf0 : f 0 ∉ discInt E := fun h => h.2 (hqE ⟨0, hOld.3.symm⟩)
  have hf1 : f 1 ∉ discInt E := fun h => h.2 (hqE ⟨1, hOld.4.symm⟩)
  obtain ⟨α, β, hαβ, heq, hcl⟩ := exists_parameters_for_connected_open_part_of_arc
    hOld.2 (hE.isOpen_discInt hman) hpre hne hf0 hf1
  exact ⟨α, β, hαβ, hP.symm.trans heq, by rwa [hP] at hcl⟩

/-- Two embedded parametrizations of the same open arc have the same
unordered pair of endpoints. This matches the parameter interval ends to
the ends of its replacement excursion in VIII (6.2). -/
theorem endpoints_eq_of_same_open_arc {X : Type u} [TopologicalSpace X] [T2Space X]
    {f b : 𝕀 → X} (hf : IsArcMap f) (hb : IsArcMap b) {α β : 𝕀} (hαβ : α < β)
    (heq : f '' Ioo α β = b '' Ioo (0 : 𝕀) 1) :
    ({f α, f β} : Set X) = {b 0, b 1} := by
  have hcl := congrArg closure heq
  rw [(hf.1.isClosedEmbedding hf.2).closure_image_eq,
    closure_Ioo hαβ.ne, closure_open_arc_image_eq_range hb.1] at hcl
  have hd : f '' Icc α β \ f '' Ioo α β = range b \ b '' Ioo (0 : 𝕀) 1 := by
    rw [hcl, heq]
  rw [← image_sdiff hf.2, Icc_sdiff_Ioo_same hαβ.le,
    image_pair, range_sdiff_open_arc_image hb] at hd
  exact hd

/-- Orient an excursion to agree with the order of its removed parameter
interval. Reversing its parametrization changes neither its full image
nor its open image. -/
theorem exists_oriented_arc_with_same_images {X : Type u} [TopologicalSpace X]
    {ℓ : 𝕀 → X} (hℓ : IsArcMap ℓ) {x y : X} (hxy : x ≠ y)
    (hend : ({x, y} : Set X) = {ℓ 0, ℓ 1}) :
    ∃ a : 𝕀 → X, IsArcMap a ∧ a 0 = x ∧ a 1 = y ∧ range a = range ℓ ∧
      a '' Ioo (0 : 𝕀) 1 = ℓ '' Ioo (0 : 𝕀) 1 := by
  have hxmem : x ∈ ({ℓ 0, ℓ 1} : Set X) := by
    rw [← hend]
    exact Or.inl rfl
  have hymem : y ∈ ({ℓ 0, ℓ 1} : Set X) := by
    rw [← hend]
    exact Or.inr rfl
  have hx : x = ℓ 0 ∨ x = ℓ 1 := by simpa only [mem_insert_iff, mem_singleton_iff] using hxmem
  have hy : y = ℓ 0 ∨ y = ℓ 1 := by simpa only [mem_insert_iff, mem_singleton_iff] using hymem
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · exact False.elim (hxy (hx.trans hy.symm))
    · exact ⟨ℓ, hℓ, hx.symm, hy.symm, rfl, rfl⟩
  · rcases hy with hy | hy
    · let a : 𝕀 → X := ℓ ∘ unitInterval.symm
      have ha : IsArcMap a := ⟨hℓ.1.comp unitInterval.continuous_symm,
        hℓ.2.comp unitInterval.symm_bijective.injective⟩
      have hsymm : ∀ t ∈ Ioo (0 : 𝕀) 1, unitInterval.symm t ∈ Ioo (0 : 𝕀) 1 := by
        intro t ht
        constructor
        · change (0 : ℝ) < 1 - t.1
          linarith [show t.1 < (1 : ℝ) from ht.2]
        · change 1 - t.1 < (1 : ℝ)
          linarith [show (0 : ℝ) < t.1 from ht.1]
      refine ⟨a, ha, ?_, ?_, ?_, ?_⟩
      · change ℓ (unitInterval.symm 0) = x
        rw [unitInterval.symm_zero]
        exact hx.symm
      · change ℓ (unitInterval.symm 1) = y
        rw [unitInterval.symm_one]
        exact hy.symm
      · apply subset_antisymm
        · rintro _ ⟨t, rfl⟩
          exact ⟨unitInterval.symm t, rfl⟩
        · rintro _ ⟨t, rfl⟩
          exact ⟨unitInterval.symm t, congrArg ℓ (unitInterval.symm_symm t)⟩
      · apply subset_antisymm
        · rintro _ ⟨t, ht, rfl⟩
          exact ⟨unitInterval.symm t, hsymm t ht, rfl⟩
        · rintro _ ⟨t, ht, rfl⟩
          exact ⟨unitInterval.symm t, hsymm t ht, congrArg ℓ (unitInterval.symm_symm t)⟩
    · exact False.elim (hxy (hx.trans hy.symm))

/-- Inclusion of enlargement discs implies inclusion of their removed
parameter intervals, because disc interiors are monotone and the boundary
parametrization is injective. -/
theorem removed_parameter_intervals_mono {S : Type u} [TopologicalSpace S]
    (hman : ∀ x : S, IsManifoldPoint x) {D E C : Set S} (hD : IsClosedDisc D)
    (hDE : D ⊆ E) {f : 𝕀 → S} (hf : IsArcMap f) {α β γ δ : 𝕀}
    (hleft : discInt D ∩ C = f '' Ioo α β)
    (hright : discInt E ∩ C = f '' Ioo γ δ) :
    Ioo α.1 β.1 ⊆ Ioo γ.1 δ.1 := by
  intro x hx
  let u : 𝕀 := ⟨x, α.2.1.trans hx.1.le, hx.2.le.trans β.2.2⟩
  have hfu : f u ∈ discInt D ∩ C := by
    rw [hleft]
    exact ⟨u, hx, rfl⟩
  have hfv : f u ∈ discInt E ∩ C :=
    ⟨discInt_mono hman hD hDE hfu.1, hfu.2⟩
  rw [hright] at hfv
  obtain ⟨v, hv, he⟩ := hfv
  have hveq : v = u := hf.2 he
  have huI : u ∈ Ioo γ δ := hveq ▸ hv
  exact huI

end GraphMinor.GM08
