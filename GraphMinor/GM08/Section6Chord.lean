module

public import GraphMinor.Surface.DiscGrow

/-!
# The exact boundary after adding one excursion

The infinite-crossing proof of VIII (6.2), page 264, needs to know which
arc of the first boundary is replaced by an excursion of the second curve.
This file strengthens the one-chord disc construction by retaining that
boundary description. The proof chooses the side of the chord that contains
the old disc, merging two discs when the first chosen side lies outside it.
-/

public section

namespace GraphMinor.GM08

open Set Topology Surface

universe u

local notation "𝕀" => unitInterval

private theorem splice_boundary {X : Type u} {A B C K : Set X}
    (hAB : A ∩ B = K) (hAC : A ∩ C = K) :
    ((A ∪ C) ∪ (A ∪ B)) \ (A \ K) = B ∪ C := by
  ext x
  have h1 := Set.ext_iff.mp hAB x
  have h2 := Set.ext_iff.mp hAC x
  simp only [mem_inter_iff] at h1 h2
  simp only [mem_union, mem_sdiff]
  tauto

/-- Adding a chord outside a closed disc replaces exactly one of its two
boundary arcs. This is the one-excursion step of VIII (6.2), with the
boundary data needed for gluing infinitely many such steps. -/
theorem exists_disc_of_chord_exact_boundary {S : Type u} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x) {Y D : Set S}
    (hDY : D ⊆ Y) (hD : IsClosedDisc D)
    (H : ∀ F : Set S, F ⊆ Y → IsOArc F → ∃ Δ : Set S, Δ ⊆ Y ∧ IsClosedDisc Δ ∧ discBd Δ = F)
    {ℓ : 𝕀 → S} (hℓ : IsArcMap ℓ) (hℓY : range ℓ ⊆ Y)
    (h0 : ℓ 0 ∈ discBd D) (h1 : ℓ 1 ∈ discBd D)
    (hmeet : ∀ r, ℓ r ∈ D → r = 0 ∨ r = 1) :
    ∃ D₁ : Set S, ∃ a b : 𝕀 → S,
      D₁ ⊆ Y ∧ IsClosedDisc D₁ ∧ D ⊆ D₁ ∧ IsTwoArcs a b ∧
      a 0 = ℓ 0 ∧ a 1 = ℓ 1 ∧ range a ∪ range b = discBd D ∧
      discBd D₁ = range a ∪ range ℓ := by
  have hne : ℓ 0 ≠ ℓ 1 := fun h => zero_ne_one (hℓ.2 h)
  obtain ⟨a, b, hab, ha0, ha1, hr⟩ := (hD.isOArc_discBd).exists_arcs h0 h1 hne
  have hbdD : discBd D ⊆ D := discBd_subset D
  have haD : range a ⊆ discBd D := hr ▸ subset_union_left
  have hbD : range b ⊆ discBd D := hr ▸ subset_union_right
  have hmeetℓ : ∀ s t, a s = ℓ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t he
    rcases hmeet t (hbdD (haD ⟨s, he⟩)) with rfl | rfl
    · exact .inl ⟨hab.1.2 (by rw [he, ha0]), rfl⟩
    · exact .inr ⟨hab.1.2 (by rw [he, ha1]), rfl⟩
  have hO : IsOArc (range a ∪ range ℓ) :=
    oArc_of_two_arcs hab.1 hℓ ha0 ha1 hmeetℓ
  have hsubY : range a ∪ range ℓ ⊆ Y :=
    union_subset (haD.trans (hbdD.trans hDY)) hℓY
  obtain ⟨Δ, hΔY, hΔ, hΔb⟩ := H _ hsubY hO
  have hsubΔ : range a ∪ range ℓ ⊆ Δ := hΔb ▸ discBd_subset Δ
  -- the inside of `D` misses the boundary of `Δ`
  have hdisj : Disjoint (discInt D) (discBd Δ) := by
    rw [hΔb, Set.disjoint_left]
    rintro x ⟨hx, hx'⟩ (⟨s, rfl⟩ | ⟨t, rfl⟩)
    · exact hx' (haD ⟨s, rfl⟩)
    · rcases hmeet t hx with rfl | rfl
      · exact hx' h0
      · exact hx' h1
  rcases hΔ.side hman hD.isPreconnected_discInt hdisj with hin | hout
  · refine ⟨Δ, a, b, hΔY, hΔ, ?_, hab, ha0, ha1, hr, hΔb⟩
    exact hD.subset_closure_discInt.trans
      (closure_minimal (hin.trans (discInt_subset Δ)) hΔ.isClosed)
  -- the other arc of `D` lies outside `Δ`
  have hbout : ∀ t, t ≠ 0 → t ≠ 1 → b t ∉ Δ := by
    intro t ht0 ht1 hmem
    have hbt : b t ∉ discBd Δ := by
      rw [hΔb]
      rintro (⟨s, hs⟩ | ⟨r, hr'⟩)
      · rcases hab.5 s t hs with ⟨-, rfl⟩ | ⟨-, rfl⟩
        · exact ht0 rfl
        · exact ht1 rfl
      · have hbDt : b t ∈ D := hbdD (hbD ⟨t, rfl⟩)
        rw [← hr'] at hbDt
        rcases hmeet r hbDt with rfl | rfl
        · apply ht0
          apply hab.2.2
          rw [← hr', hab.3, ha0]
        · apply ht1
          apply hab.2.2
          rw [← hr', hab.4, ha1]
    have hint : b t ∈ discInt Δ := ⟨hmem, hbt⟩
    have hbtcl : b t ∈ closure (discInt D) := hD.subset_closure_discInt (hbdD (hbD ⟨t, rfl⟩))
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp hbtcl _ (hΔ.isOpen_discInt hman) hint
    exact Set.disjoint_left.mp hout hw2 hw1.1
  have hinter : Δ ∩ D = range a := by
    ext x
    constructor
    · rintro ⟨hx, hx'⟩
      by_cases hb : x ∈ discBd D
      · rw [← hr] at hb
        rcases hb with hb | ⟨t, rfl⟩
        · exact hb
        · by_cases ht0 : t = 0
          · subst ht0
            exact ⟨0, hab.3.symm⟩
          by_cases ht1 : t = 1
          · subst ht1
            exact ⟨1, hab.4.symm⟩
          exact absurd hx (hbout t ht0 ht1)
      · exact absurd hx (Set.disjoint_left.mp hout ⟨hx', hb⟩)
    · intro hx
      exact ⟨hsubΔ (.inl hx), hbdD (haD hx)⟩
  have hu := disc_union.{u} Δ D (range a) (a 0) (a 1) hΔ hD hab.1.isLineWithEnds hinter
    (hΔb ▸ subset_union_left) haD
  have hba : IsTwoArcs b a := by
    refine ⟨hab.2, hab.1, hab.3.symm, hab.4.symm, ?_⟩
    intro s t he
    rcases hab.5 t s he.symm with h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr ⟨h.2, h.1⟩
  have hAB : range a ∩ range b = {a 0, a 1} := by
    ext x
    constructor
    · rintro ⟨⟨s, rfl⟩, t, he⟩
      rcases hab.5 s t he.symm with h | h
      · exact Or.inl (congrArg a h.1)
      · exact Or.inr (congrArg a h.1)
    · rintro (rfl | rfl)
      · exact ⟨⟨0, rfl⟩, 0, hab.3⟩
      · exact ⟨⟨1, rfl⟩, 1, hab.4⟩
  have hAC : range a ∩ range ℓ = {a 0, a 1} := by
    ext x
    constructor
    · rintro ⟨⟨s, rfl⟩, t, he⟩
      rcases hmeetℓ s t he.symm with h | h
      · exact Or.inl (congrArg a h.1)
      · exact Or.inr (congrArg a h.1)
    · rintro (rfl | rfl)
      · exact ⟨⟨0, rfl⟩, 0, ha0.symm⟩
      · exact ⟨⟨1, rfl⟩, 1, ha1.symm⟩
  refine ⟨Δ ∪ D, b, a, union_subset hΔY hDY, hu.1, subset_union_right,
    hba, hab.3.trans ha0, hab.4.trans ha1, ?_, ?_⟩
  · rw [union_comm]
    exact hr
  · rw [hu.2, hΔb, ← hr]
    exact splice_boundary hAB hAC

/-- The open arc removed from the old boundary is exactly the part of that
boundary lying in the interior of the enlarged disc. This identifies the
intervals used to order and select excursions in VIII (6.2). -/
theorem removed_arc_eq_old_boundary_inside {S : Type u} [TopologicalSpace S]
    {D D₁ : Set S} {a b ℓ : 𝕀 → S} (hsub : D ⊆ D₁) (hab : IsTwoArcs a b)
    (hr : range a ∪ range b = discBd D) (hbd : discBd D₁ = range a ∪ range ℓ)
    (ha0 : a 0 = ℓ 0) (ha1 : a 1 = ℓ 1)
    (hmeet : ∀ r, ℓ r ∈ D → r = 0 ∨ r = 1) :
    discInt D₁ ∩ discBd D = b '' Ioo (0 : 𝕀) 1 := by
  have hbD : ∀ t, b t ∈ D := fun t =>
    discBd_subset D (hr ▸ Or.inr ⟨t, rfl⟩)
  have hbinside : ∀ t ∈ Ioo (0 : 𝕀) 1, b t ∈ discInt D₁ := by
    intro t ht
    refine ⟨hsub (hbD t), ?_⟩
    rw [hbd]
    rintro (⟨s, hs⟩ | ⟨s, hs⟩)
    · rcases hab.5 s t hs with h | h
      · exact (ne_of_gt ht.1) h.2
      · exact (ne_of_lt ht.2) h.2
    · rcases hmeet s (hs.symm ▸ hbD t) with hs0 | hs1
      · subst s
        exact (ne_of_gt ht.1) (hab.2.2
          (hs.symm.trans (ha0.symm.trans hab.3.symm)))
      · subst s
        exact (ne_of_lt ht.2) (hab.2.2
          (hs.symm.trans (ha1.symm.trans hab.4.symm)))
  apply subset_antisymm
  · rintro x ⟨hx, hxb⟩
    rw [← hr] at hxb
    rcases hxb with hxa | ⟨t, rfl⟩
    · exact False.elim (hx.2 (hbd ▸ Or.inl hxa))
    · have ht0 : t ≠ 0 := by
        rintro rfl
        exact hx.2 (hbd ▸ Or.inl ⟨0, hab.3.symm⟩)
      have ht1 : t ≠ 1 := by
        rintro rfl
        exact hx.2 (hbd ▸ Or.inl ⟨1, hab.4.symm⟩)
      exact ⟨t, ⟨lt_of_le_of_ne (unitInterval.nonneg t) ht0.symm,
        lt_of_le_of_ne (unitInterval.le_one t) ht1⟩, rfl⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨hbinside t ht, hr ▸ Or.inr ⟨t, rfl⟩⟩

/-- A closed disc lies in a set that contains its boundary, provided the
complement of that set is connected and has a point outside the disc.
For VIII (6.2), the containing set is another disc missing the chosen point. -/
theorem disc_subset_of_boundary_subset_and_connected_compl
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x) {A B : Set S} (hA : IsClosedDisc A)
    (hBc : IsPreconnected Bᶜ) (hbd : discBd A ⊆ B)
    {z : S} (hzA : z ∉ A) (hzB : z ∉ B) : A ⊆ B := by
  have hd : Disjoint Bᶜ (discBd A) :=
    Set.disjoint_left.mpr (fun _ hx hb => hx (hbd hb))
  rcases hA.side hman hBc hd with hin | hout
  · exact False.elim (hzA (hin hzB).1)
  · intro x hx
    by_contra hxb
    exact Set.disjoint_left.mp hout hxb hx

/-- If the open part of an outside excursion enters a previously enlarged
disc, its whole associated disc lies there. The open excursion is connected
and cannot cross that disc's boundary, which consists of the old boundary
and a disjoint excursion. This is the nested case in VIII (6.2). -/
theorem chord_disc_subset_of_open_excursion_meets
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x) {D E F : Set S} {a b : 𝕀 → S}
    (hE : IsClosedDisc E) (hF : IsClosedDisc F) (hDE : D ⊆ E)
    (hEb : discBd E ⊆ D ∪ range a) (hFb : discBd F ⊆ D ∪ range b)
    (hb : IsArcMap b) (houtside : ∀ t ∈ Ioo (0 : 𝕀) 1, b t ∉ D)
    (hdis : Disjoint (b '' Ioo (0 : 𝕀) 1) (range a))
    (hEc : IsPreconnected Eᶜ) {z : S} (hzE : z ∉ E) (hzF : z ∉ F)
    (hmeet : (b '' Ioo (0 : 𝕀) 1 ∩ discInt E).Nonempty) : F ⊆ E := by
  have hP : IsPreconnected (b '' Ioo (0 : 𝕀) 1) :=
    isPreconnected_Ioo.image b hb.1.continuousOn
  have hPbd : Disjoint (b '' Ioo (0 : 𝕀) 1) (discBd E) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨t, ht, rfl⟩ hxb
    rcases hEb hxb with hD | ha
    · exact houtside t ht hD
    · exact Set.disjoint_left.mp hdis ⟨t, ht, rfl⟩ ha
  have hPE : b '' Ioo (0 : 𝕀) 1 ⊆ E := by
    rcases hE.side hman hP hPbd with hin | hout
    · exact hin.trans (discInt_subset E)
    · obtain ⟨x, hxP, hxE⟩ := hmeet
      exact False.elim (Set.disjoint_left.mp hout hxP hxE.1)
  have hbE : range b ⊆ E := by
    rintro _ ⟨t, rfl⟩
    apply closure_minimal hPE hE.isClosed
    apply mem_closure_image hb.1.continuousAt
    rw [closure_Ioo zero_ne_one]
    exact ⟨unitInterval.nonneg t, unitInterval.le_one t⟩
  exact disc_subset_of_boundary_subset_and_connected_compl hman hF hEc
    (hFb.trans (union_subset hDE hbE)) hzF hzE

/-- Two enlarged discs whose new boundary portions do not cross are nested
if their removed old boundary arcs overlap. The added lobe of the first
disc is a closed disc by `disc_difference`; its interior misses the second
boundary, so separation forces that lobe into the second disc. -/
theorem disc_subset_of_overlapping_removed_arcs
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x) {D E F L : Set S} {s t : S}
    (hD : IsClosedDisc D) (hE : IsClosedDisc E) (hF : IsClosedDisc F)
    (hDE : D ⊆ E) (hDF : D ⊆ F) (hL : IsLineWithEnds L s t)
    (hmeet : discBd D ∩ discBd E = L)
    (hDext : discBd D ⊆ closure Dᶜ)
    (hcross : Disjoint (discBd F \ D) E)
    (hoverlap : (discBd D ∩ (discInt E ∩ discInt F)).Nonempty) : E ⊆ F := by
  let K := closure (E \ D)
  obtain ⟨hK, hKb, hKD⟩ := disc_difference D E L s t hD hE hDE hL hmeet
  have hKE : K ⊆ E := closure_minimal sdiff_subset hE.isClosed
  have hKintD : Disjoint (discInt K) D := by
    apply Set.disjoint_left.mpr
    intro x hxK hxD
    have hxb : x ∈ discBd D \ (L \ {s, t}) := hKD ▸ ⟨hxK.1, hxD⟩
    apply hxK.2
    rw [hKb]
    exact ⟨Or.inl hxb.1, hxb.2⟩
  have hKintFb : Disjoint (discInt K) (discBd F) := by
    apply Set.disjoint_left.mpr
    intro x hxK hxF
    have hxD : x ∉ D := fun h => Set.disjoint_left.mp hKintD hxK h
    exact Set.disjoint_left.mp hcross ⟨hxF, hxD⟩ (hKE hxK.1)
  obtain ⟨x, hxD, hxE, hxF⟩ := hoverlap
  have hxK : x ∈ K := by
    apply mem_closure_iff.mpr
    intro U hU hxU
    obtain ⟨y, hyU, hyD⟩ := mem_closure_iff.mp (hDext hxD)
      (U ∩ discInt E) (hU.inter (hE.isOpen_discInt hman)) ⟨hxU, hxE⟩
    exact ⟨y, hyU.1, ⟨hyU.2.1, hyD⟩⟩
  have hxKcl : x ∈ closure (discInt K) := hK.subset_closure_discInt hxK
  obtain ⟨y, hyF, hyK⟩ := mem_closure_iff.mp hxKcl
    (discInt F) (hF.isOpen_discInt hman) hxF
  have hKF : K ⊆ F := by
    rcases hF.side hman hK.isPreconnected_discInt hKintFb with hin | hout
    · exact hK.subset_closure_discInt.trans
        (closure_minimal (hin.trans (discInt_subset F)) hF.isClosed)
    · exact False.elim (Set.disjoint_left.mp hout hyK hyF.1)
  intro z hzE
  by_cases hzD : z ∈ D
  · exact hDF hzD
  · exact hKF (subset_closure ⟨hzE, hzD⟩)

/-- The old and enlarged boundaries meet exactly in the retained arc.
This lets `disc_difference` identify the added lobe of an excursion. -/
theorem old_new_boundary_inter_eq_kept_arc {S : Type u} [TopologicalSpace S]
    {D E : Set S} {a b ℓ : 𝕀 → S} (hr : range a ∪ range b = discBd D)
    (hbd : discBd E = range a ∪ range ℓ) (ha0 : a 0 = ℓ 0) (ha1 : a 1 = ℓ 1)
    (hmeet : ∀ r, ℓ r ∈ D → r = 0 ∨ r = 1) :
    discBd D ∩ discBd E = range a := by
  apply subset_antisymm
  · rintro x ⟨hxD, hxE⟩
    rw [hbd] at hxE
    rcases hxE with hx | ⟨r, rfl⟩
    · exact hx
    · rcases hmeet r (discBd_subset D hxD) with hr0 | hr1
      · subst r
        exact ⟨0, ha0⟩
      · subst r
        exact ⟨1, ha1⟩
  · intro x hx
    exact ⟨hr ▸ Or.inl hx, hbd ▸ Or.inl hx⟩

/-- Enlargements along disjoint excursions are nested whenever their
removed old boundary arcs overlap. This gives the geometric comparison
used to select maximal excursions in the proof of VIII (6.2). -/
theorem chord_discs_nested_or_removed_arcs_disjoint
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x) {D E F L : Set S} {s t : S} {a b : 𝕀 → S}
    (hD : IsClosedDisc D) (hE : IsClosedDisc E) (hF : IsClosedDisc F)
    (hDE : D ⊆ E) (hDF : D ⊆ F) (hL : IsLineWithEnds L s t)
    (hline : discBd D ∩ discBd E = L)
    (hDext : discBd D ⊆ closure Dᶜ)
    (hEb : discBd E ⊆ D ∪ range a) (hFb : discBd F ⊆ D ∪ range b)
    (hb : IsArcMap b) (hb0 : b 0 ∈ D) (hb1 : b 1 ∈ D)
    (houtside : ∀ r ∈ Ioo (0 : 𝕀) 1, b r ∉ D)
    (hdis : Disjoint (b '' Ioo (0 : 𝕀) 1) (range a))
    (hEc : IsPreconnected Eᶜ) {z : S} (hzE : z ∉ E) (hzF : z ∉ F) :
    E ⊆ F ∨ F ⊆ E ∨ Disjoint (discBd D ∩ discInt E) (discBd D ∩ discInt F) := by
  by_cases hin : (b '' Ioo (0 : 𝕀) 1 ∩ discInt E).Nonempty
  · exact Or.inr (Or.inl (chord_disc_subset_of_open_excursion_meets hman
      hE hF hDE hEb hFb hb houtside hdis hEc hzE hzF hin))
  have hcross : Disjoint (discBd F \ D) E := by
    apply Set.disjoint_left.mpr
    rintro x ⟨hxFb, hxD⟩ hxE
    rcases hFb hxFb with hD | ⟨r, rfl⟩
    · exact hxD hD
    · have hr0 : r ≠ 0 := fun he => hxD (he ▸ hb0)
      have hr1 : r ≠ 1 := fun he => hxD (he ▸ hb1)
      have hr : r ∈ Ioo (0 : 𝕀) 1 :=
        ⟨lt_of_le_of_ne (unitInterval.nonneg r) hr0.symm,
          lt_of_le_of_ne (unitInterval.le_one r) hr1⟩
      have hnotbd : b r ∉ discBd E := by
        intro hbdE
        rcases hEb hbdE with hD | ha
        · exact hxD hD
        · exact Set.disjoint_left.mp hdis ⟨r, hr, rfl⟩ ha
      exact hin ⟨b r, ⟨r, hr, rfl⟩, hxE, hnotbd⟩
  by_cases hoverlap : (discBd D ∩ (discInt E ∩ discInt F)).Nonempty
  · exact Or.inl (disc_subset_of_overlapping_removed_arcs hman hD hE hF
      hDE hDF hL hline hDext hcross hoverlap)
  · right
    right
    apply Set.disjoint_left.mpr
    rintro x ⟨hxD, hxE⟩ ⟨_, hxF⟩
    exact hoverlap ⟨x, hxD, hxE, hxF⟩

/-- The new boundary outside the old disc is exactly the open excursion.
Consequently different excursion components give different enlarged discs. -/
theorem enlarged_boundary_sdiff_old_disc_eq_excursion
    {S : Type u} [TopologicalSpace S] {D E J : Set S} {a ℓ : 𝕀 → S}
    (hEb : discBd E = range a ∪ range ℓ) (haD : range a ⊆ D)
    (hℓ0 : ℓ 0 ∈ D) (hℓ1 : ℓ 1 ∈ D)
    (hopen : ℓ '' Ioo (0 : 𝕀) 1 = J) (hJD : J ⊆ Dᶜ) : discBd E \ D = J := by
  apply subset_antisymm
  · rintro x ⟨hxE, hxD⟩
    rw [hEb] at hxE
    rcases hxE with hxa | ⟨t, rfl⟩
    · exact False.elim (hxD (haD hxa))
    · have ht0 : t ≠ 0 := fun h => hxD (h ▸ hℓ0)
      have ht1 : t ≠ 1 := fun h => hxD (h ▸ hℓ1)
      rw [← hopen]
      exact ⟨t, ⟨lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht0),
        lt_of_le_of_ne (unitInterval.le_one t) ht1⟩, rfl⟩
  · intro x hxJ
    have hxℓ : x ∈ range ℓ := (image_subset_range _ _) (hopen.symm ▸ hxJ)
    exact ⟨hEb ▸ Or.inr hxℓ, hJD hxJ⟩

end GraphMinor.GM08
