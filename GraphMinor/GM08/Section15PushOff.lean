module

public import GraphMinor.GM08.Section15Pocket
public import GraphMinor.Surface.EdgeLens
public import GraphMinor.Surface.DiscArcs
public import GraphMinor.Surface.DiscUnion
public import GraphMinor.Surface.PlaneDisc
public import GraphMinor.GM07.CuffArc

/-!
# Graph Minors VIII, printed (15.1): pushing a disc past a line of its boundary

This file serves Claim C (`exists_exposed_region`) of Lemma 4 of the proof of the printed (15.1) in
`Section15PrintedFinal.lean`.

The pushing steps of Lemma 4 all have the same form. A closed disc `P` has a line `ℓ` on its
boundary, and `ℓ` is part of the drawing. We want a slightly larger disc that has `ℓ`, except its
two ends, inside. We put a thin lens around `ℓ` that meets a given closed set `Z` only at the ends
of `ℓ` (`Surface.exists_edge_lens_sides`). The line `ℓ` cuts the lens into two halves
(`Surface.disc_iArc`), and one half lies outside `P`. Adding that half to `P`
(`Surface.disc_union`) gives the new disc (`exists_pushOff`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

local notation "𝕀" => unitInterval

/-- An `O`-arc made of two arcs `a`, `b` with common ends: without the two ends, it has exactly two
components, the insides of `a` and of `b`. -/
theorem componentsIn_twoArcs {T : Type*} [TopologicalSpace T] [T2Space T] {a b : 𝕀 → T}
    (hab : IsTwoArcs a b) :
    componentsIn ((range a ∪ range b) \ {a 0, a 1}) = {a '' Ioo 0 1, b '' Ioo 0 1} := by
  have ha := hab.arc_left
  have hb := hab.arc_right
  have hmid : (⟨1 / 2, by norm_num, by norm_num⟩ : 𝕀) ∈ Ioo (0 : 𝕀) 1 :=
    ⟨by change (0 : ℝ) < 1 / 2; norm_num, by change (1 / 2 : ℝ) < 1; norm_num⟩
  have hsplit : ∀ {c : 𝕀 → T}, IsArcMap c → c 0 = a 0 → c 1 = a 1 →
      c '' Ioo 0 1 = range c \ {a 0, a 1} := by
    intro c hc h0 h1
    ext x
    constructor
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      rintro (h | h)
      · rw [← h0] at h; exact ht0.ne' (hc.2 h)
      · rw [← h1] at h; exact ht1.ne (hc.2 h)
    · rintro ⟨⟨t, rfl⟩, hx⟩
      refine ⟨t, ⟨?_, ?_⟩, rfl⟩
      · refine lt_of_le_of_ne t.2.1 fun h => hx (Or.inl ?_)
        rw [← h0, ← h]
      · refine lt_of_le_of_ne t.2.2 fun h => hx (Or.inr ?_)
        rw [← h1, h]; rfl
  have hA := hsplit ha rfl rfl
  have hB := hsplit hb hab.zero hab.one
  have hpre : ∀ {c : 𝕀 → T}, IsArcMap c → IsPreconnected (c '' Ioo 0 1) := fun hc =>
    ordConnected_Ioo.isPreconnected.image _ hc.1.continuousOn
  have hcl : ∀ {c : 𝕀 → T}, IsArcMap c → closure (c '' Ioo 0 1) ⊆ range c := fun hc =>
    closure_minimal (image_subset_range _ _)
      (isCompact_range hc.1).isClosed
  have hmeet : ∀ x, x ∈ range a → x ∈ range b → x = a 0 ∨ x = a 1 := by
    rintro _ ⟨s, rfl⟩ ⟨t, ht⟩
    rcases hab.meet s t ht.symm with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have heq : (range a ∪ range b) \ {a 0, a 1} = a '' Ioo 0 1 ∪ b '' Ioo 0 1 := by
    rw [hA, hB, union_sdiff_distrib]
  rw [heq]
  refine componentsIn_union_eq_pair (hpre ha) (hpre hb) ⟨_, mem_image_of_mem _ hmid⟩
    ⟨_, mem_image_of_mem _ hmid⟩ ?_ ?_
  · refine disjoint_left.mpr fun x hx hx' => ?_
    rw [hB] at hx'
    exact hx'.2 (hmeet x (hcl ha hx) hx'.1)
  · refine disjoint_left.mpr fun x hx hx' => ?_
    rw [hA] at hx
    exact hx.2 (hmeet x hx.1 (hcl hb hx'))

/-- A member of `componentsIn F` is a preconnected subset of `F`. -/
theorem isPreconnected_and_subset_of_mem_componentsIn {T : Type*} [TopologicalSpace T]
    {F C : Set T} (hC : C ∈ componentsIn F) : IsPreconnected C ∧ C ⊆ F := by
  obtain ⟨x, -, rfl⟩ := hC
  exact ⟨isPreconnected_connectedComponentIn, connectedComponentIn_subset _ _⟩

/-- **Pushing a disc past a line of its boundary.** Let `P` be a closed disc in a closed surface,
`ℓ ⊆ bd P` a line with ends `u ≠ v`, and `Z` a closed set that meets `ℓ` only at its ends and holds
the rest of `bd P`. Then a larger closed disc `P'` has all of `ℓ` except its ends inside, and
`P' \ P` misses `Z`. Its boundary is `bd P` with the inside of `ℓ` replaced by an arc `g` from `u`
to `v` that meets `P` only at its ends.

We put a lens around `ℓ` that meets `Z` only at `u` and `v` (`exists_edge_lens_sides`), and cut it
along `ℓ` into two closed discs (`disc_iArc`). Each half without `ℓ` is connected and misses
`bd P`, so it is inside `P` or outside `P`. A point of `ℓ` other than its ends is a limit of points
outside `P`, and the lens is a neighbourhood of it, so one half is outside `P`. That half meets
`P` exactly in `ℓ`, and `disc_union` glues it to `P`. Its outer side is one of the two arcs of the
lens boundary between `u` and `v` (`componentsIn_twoArcs`). -/
theorem exists_pushOff {T : Type} [TopologicalSpace T] (hT : IsClosedSurface T)
    {P ℓ Z : Set T} {u v : T} (hP : IsClosedDisc P) (hℓ : IsLineWithEnds ℓ u v) (huv : u ≠ v)
    (hℓP : ℓ ⊆ discBd P) (hZ : IsClosed Z) (hℓZ : ℓ ∩ Z ⊆ {u, v}) (hbdZ : discBd P ⊆ ℓ ∪ Z) :
    ∃ P' : Set T, ∃ g : 𝕀 → T, IsClosedDisc P' ∧ P ⊆ P' ∧ Disjoint (P' \ P) Z ∧
      ℓ \ {u, v} ⊆ discInt P' ∧ IsArcMap g ∧ g 0 = u ∧ g 1 = v ∧ range g ⊆ P' ∧
      range g ∩ P ⊆ {u, v} ∧ discBd P' = (discBd P \ (ℓ \ {u, v})) ∪ range g := by
  classical
  have ht2 : T2Space T := hT.2.1
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  obtain ⟨α, hα, hαr, hα0, hα1⟩ := hℓ.exists_arc
  have huℓ : u ∈ ℓ := hαr ▸ hα0 ▸ mem_range_self 0
  have hvℓ : v ∈ ℓ := hαr ▸ hα1 ▸ mem_range_self 1
  have hℓP' : ℓ ⊆ P := hℓP.trans (discBd_subset P)
  obtain ⟨D, -, -, hD, hℓD, hDZ, huD, hvD, hbdℓ, -⟩ := exists_edge_lens_sides hT hℓ huv hZ hℓZ
  have hℓbd : ℓ ∩ discBd D = {u, v} := by
    refine Subset.antisymm (fun x hx => hbdℓ ⟨hx.2, hx.1⟩) ?_
    rintro x (rfl | rfl)
    · exact ⟨huℓ, huD⟩
    · exact ⟨hvℓ, hvD⟩
  have hDuv : ∀ x ∈ D, x ∈ Z → x ∈ ℓ := fun x hxD hxZ => by
    rcases hDZ ⟨hxD, hxZ⟩ with rfl | rfl
    · exact huℓ
    · exact hvℓ
  obtain ⟨A₁, A₂, Δ₁, Δ₂, -, hcomp, hΔ₁, hΔ₂, hcup, hcap, hb₁, hb₂, hcompD⟩ :=
    disc_iArc D ℓ u v hD hℓD huv hℓ hℓbd
  have hside : ∀ Δ, Δ \ ℓ ∈ componentsIn (D \ ℓ) → Δ \ ℓ ⊆ discInt P ∨ Disjoint (Δ \ ℓ) P := by
    intro Δ hΔ
    obtain ⟨hpre, hsub⟩ := isPreconnected_and_subset_of_mem_componentsIn hΔ
    refine hP.side hman hpre (disjoint_left.mpr fun y hy hyb => ?_)
    rcases hbdZ hyb with h | h
    · exact (hsub hy).2 h
    · exact (hsub hy).2 (hDuv y (hsub hy).1 h)
  -- A point of `D` outside `P`.
  have hmid : (⟨1 / 2, by norm_num, by norm_num⟩ : 𝕀) ∈ Ioo (0 : 𝕀) 1 :=
    ⟨by change (0 : ℝ) < 1 / 2; norm_num, by change (1 / 2 : ℝ) < 1; norm_num⟩
  set w := α ⟨1 / 2, by norm_num, by norm_num⟩ with hw
  have hwℓ : w ∈ ℓ := hαr ▸ mem_range_self _
  have hwuv : w ∉ ({u, v} : Set T) := by
    rintro (h | h)
    · rw [← hα0] at h; exact hmid.1.ne' (hα.2 h)
    · rw [← hα1] at h; exact hmid.2.ne (hα.2 h)
  have hwint : w ∈ discInt D := ⟨hℓD hwℓ, fun h => hwuv (hℓbd ▸ ⟨hwℓ, h⟩)⟩
  have hwcl : w ∈ closure Pᶜ :=
    GM07.discBd_subset_closure_compl hman hP (fun x _ => hT.2.2 x) (hℓP hwℓ)
  obtain ⟨y, hyD, hyP⟩ := mem_closure_iff.mp hwcl _ (hD.isOpen_discInt hman) hwint
  have hyℓ : y ∉ ℓ := fun h => hyP (hℓP' h)
  have key : ∃ Δ A', IsClosedDisc Δ ∧ Δ ⊆ D ∧ ℓ ⊆ Δ ∧ Disjoint (Δ \ ℓ) P ∧
      discBd Δ = A' ∪ ℓ ∧ A' ∈ componentsIn (discBd D \ {u, v}) := by
    have hyD' : y ∈ Δ₁ ∪ Δ₂ := hcup.ge hyD.1
    rcases hyD' with h | h
    · rcases hside Δ₁ (by rw [hcompD]; exact Or.inl rfl) with h' | h'
      · exact absurd (h' ⟨h, hyℓ⟩).1 hyP
      · exact ⟨Δ₁, A₁, hΔ₁, subset_union_left.trans hcup.le,
          fun x hx => (hcap.ge hx).1, h', hb₁, by rw [hcomp]; exact Or.inl rfl⟩
    · rcases hside Δ₂ (by rw [hcompD]; exact Or.inr rfl) with h' | h'
      · exact absurd (h' ⟨h, hyℓ⟩).1 hyP
      · exact ⟨Δ₂, A₂, hΔ₂, subset_union_right.trans hcup.le,
          fun x hx => (hcap.ge hx).2, h', hb₂, by rw [hcomp]; exact Or.inr rfl⟩
  obtain ⟨Δ, A', hΔ, hΔD, hℓΔ, hΔP, hbΔ, hA'⟩ := key
  have hA'sub := (isPreconnected_and_subset_of_mem_componentsIn hA').2
  have hA'ℓ : ∀ x ∈ A', x ∉ ℓ := fun x hx hxℓ =>
    (hA'sub hx).2 (hℓbd ▸ ⟨hxℓ, (hA'sub hx).1⟩)
  have hA'Δ : A' ⊆ Δ := fun x hx => discBd_subset Δ (hbΔ ▸ Or.inl hx)
  have hPΔ : P ∩ Δ = ℓ := by
    refine Subset.antisymm (fun x ⟨hxP, hxΔ⟩ => ?_) fun x hx => ⟨hℓP' hx, hℓΔ hx⟩
    by_contra hxℓ
    exact disjoint_left.mp hΔP ⟨hxΔ, hxℓ⟩ hxP
  have hℓbdΔ : ℓ ⊆ discBd Δ := hbΔ ▸ subset_union_right
  obtain ⟨hP', hbP'⟩ := disc_union P Δ ℓ u v hP hΔ hℓ hPΔ hℓP hℓbdΔ
  -- The outer arc.
  obtain ⟨a, b, hab, ha0, ha1, hr⟩ := hD.isOArc_discBd.exists_arcs huD hvD huv
  have hc := componentsIn_twoArcs hab
  rw [hr, ha0, ha1] at hc
  rw [hc] at hA'
  have hgex : ∃ g : 𝕀 → T, IsArcMap g ∧ g 0 = u ∧ g 1 = v ∧ A' = g '' Ioo 0 1 := by
    rcases hA' with h | h
    · exact ⟨a, hab.arc_left, ha0, ha1, h⟩
    · exact ⟨b, hab.arc_right, hab.zero.trans ha0, hab.one.trans ha1, h⟩
  obtain ⟨g, hg, hg0, hg1, hA'g⟩ := hgex
  have hrg : range g = A' ∪ {u, v} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      by_cases h0 : t = 0
      · exact Or.inr (Or.inl (h0 ▸ hg0))
      by_cases h1 : t = 1
      · exact Or.inr (Or.inr (h1 ▸ hg1))
      refine Or.inl (hA'g ▸ ⟨t, ⟨?_, ?_⟩, rfl⟩)
      · exact lt_of_le_of_ne t.2.1 fun h => h0 h.symm
      · exact lt_of_le_of_ne t.2.2 fun h => h1 h
    · rintro (hx | rfl | rfl)
      · rw [hA'g] at hx
        obtain ⟨t, -, rfl⟩ := hx
        exact mem_range_self t
      · exact ⟨0, hg0⟩
      · exact ⟨1, hg1⟩
  refine ⟨P ∪ Δ, g, hP', subset_union_left, ?_, ?_, hg, hg0, hg1, ?_, ?_, ?_⟩
  · refine disjoint_left.mpr fun x ⟨hx, hxP⟩ hxZ => ?_
    have hxΔ : x ∈ Δ := hx.resolve_left hxP
    exact hxP (hℓP' (hDuv x (hΔD hxΔ) hxZ))
  · intro x hx
    refine ⟨Or.inl (hℓP' hx.1), fun hb => ?_⟩
    rw [hbP'] at hb
    exact hb.2 hx
  · rw [hrg]
    rintro x (hx | rfl | rfl)
    · exact Or.inr (hA'Δ hx)
    · exact Or.inl (hℓP' huℓ)
    · exact Or.inl (hℓP' hvℓ)
  · rw [hrg]
    rintro x ⟨hx | hx, hxP⟩
    · exact absurd hxP (disjoint_left.mp hΔP ⟨hA'Δ hx, hA'ℓ x hx⟩)
    · exact hx
  · rw [hbP', hrg]
    ext x
    simp only [mem_sdiff, mem_union, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hx | hx, hxn⟩
      · exact Or.inl ⟨hx, hxn⟩
      · rw [hbΔ] at hx
        rcases hx with hx | hx
        · exact Or.inr (Or.inl hx)
        · by_contra hcon
          push Not at hcon
          exact hxn ⟨hx, fun h => by rcases h with rfl | rfl <;> simp_all⟩
    · rintro (⟨hx, hxn⟩ | hx | hx | hx)
      · exact ⟨Or.inl hx, hxn⟩
      · exact ⟨Or.inr (hbΔ ▸ Or.inl hx), fun h => hA'ℓ x hx h.1⟩
      · subst hx; exact ⟨Or.inl (hℓP huℓ), fun h => h.2 (Or.inl rfl)⟩
      · subst hx; exact ⟨Or.inl (hℓP hvℓ), fun h => h.2 (Or.inr rfl)⟩

/-- An open set inside a closed disc of a closed surface misses the boundary of the disc. -/
theorem subset_discInt_of_isOpen {T : Type} [TopologicalSpace T] (hT : IsClosedSurface T)
    {O Δ : Set T} (hΔ : IsClosedDisc Δ) (hO : IsOpen O) (hOΔ : O ⊆ Δ) : O ⊆ discInt Δ := by
  have : T2Space T := hT.2.1
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  intro x hx
  refine ⟨hOΔ hx, fun hb => ?_⟩
  obtain ⟨y, hyO, hyΔ⟩ := mem_closure_iff.mp
    (GM07.discBd_subset_closure_compl hman hΔ (fun z _ => hT.2.2 z) hb) O hO hx
  exact hyΔ (hOΔ hyO)

/-- **No edge can be pushed into the pocket.** This is the common step of parts (i) and (ii) of
Claim C. Let `D₁`, `D₂` be closed sets of a closed
surface, `D₁` a closed disc, such that every closed disc `Δ ⊇ D₁` that misses the inside of `D₂`
and meets the drawing on its boundary only in `bd D₁` has no drawing inside except in `D₁` (this
is what `Tube.image_inter_discInt_subset_of_maximal` gives). Let `e` be an edge outside
`D₁ ∪ D₂` whose ends lie in `D₁`. Then no closed disc `P ⊇ D₁` that misses the inside of `D₂` has
the closure of `e` on its boundary and the rest of its boundary in `D₁`.

If `e` has two ends, push `P` past the closure of `e` (`exists_pushOff`). The new disc has `e`
inside, and meets the drawing on its boundary only in the ends of `e`, which lie on `bd D₁`. This
contradicts the hypothesis. If `e` is a loop at `a`, split its closure at a point `m ∈ e` into two
arcs. Push `P` past the first arc. Its new boundary arc `g₁` runs from `a` to `m`. Then push past
the line made of the second half of `g₁` and the second arc. Now `m` is inside, and the boundary
meets the drawing only at `a`. -/
theorem false_of_edge_on_discBd {T : Type} [TopologicalSpace T] (hT : IsClosedSurface T)
    (Γ : Drawing T) {D₁ D₂ P e : Set T} (hD₁ : IsClosedDisc D₁) (hD₂ : IsClosed D₂)
    (hpush : ∀ Δ : Set T, IsClosedDisc Δ → D₁ ⊆ Δ → Disjoint Δ (discInt D₂) →
      discBd Δ ∩ Γ.U ⊆ discBd D₁ → Γ.U ∩ discInt Δ ⊆ D₁)
    (he : e ∈ Γ.E) (heD : Disjoint e (D₁ ∪ D₂))
    (hP : IsClosedDisc P) (hD₁P : D₁ ⊆ P) (hPD₂ : Disjoint P (discInt D₂))
    (heP : closure e ⊆ discBd P) (hbdP : discBd P \ e ⊆ D₁) : False := by
  classical
  have ht2 : T2Space T := hT.2.1
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  have heU : e ⊆ Γ.U := fun x hx => (he.2.1 hx).1
  have heV : ∀ x ∈ e, x ∉ Γ.V := fun x hx => (he.2.1 hx).2
  have hdiff := Γ.closure_diff_V he
  have hZe : IsClosed (Γ.U \ e) := GM11.isClosed_U_sdiff_edge Γ he
  have hP' : discBd P ⊆ P := discBd_subset P
  have hclP : closure e ⊆ P := heP.trans hP'
  have heP' : e ⊆ P := subset_closure.trans hclP
  have hclV : ∀ x ∈ closure e, x ∉ e → x ∈ closure e ∩ Γ.V := fun x hx hxe =>
    ⟨hx, by_contra fun h => hxe (hdiff ▸ ⟨hx, h⟩)⟩
  have heD₁ : ∀ x ∈ e, x ∉ D₁ := fun x hx h => disjoint_left.mp heD hx (Or.inl h)
  have heD₂ : ∀ x ∈ e, x ∉ D₂ := fun x hx h => disjoint_left.mp heD hx (Or.inr h)
  have hint₁ : discInt D₁ ⊆ discInt P :=
    subset_discInt_of_isOpen hT hP (hD₁.isOpen_discInt hman) fun x hx => hD₁P hx.1
  have hbdP₁ : ∀ x ∈ discBd P, x ∉ e → x ∈ discBd D₁ := by
    intro x hx hxe
    by_contra hcon
    exact (hint₁ ⟨hbdP ⟨hx, hxe⟩, hcon⟩).2 hx
  have finish : ∀ P', IsClosedDisc P' → P ⊆ P' → Disjoint P' (discInt D₂) →
      discBd P' ∩ Γ.U ⊆ discBd D₁ → ∀ z ∈ e, z ∈ discInt P' → False :=
    fun P' h1 h2 h3 h4 z hz hz' =>
      heD₁ z hz (hpush P' h1 (hD₁P.trans h2) h3 h4 ⟨heU hz, hz'⟩)
  obtain ⟨z₀, hz₀⟩ := he.1
  rcases Γ.edge_cond e he with ⟨a, b, hab, hcap, hL⟩ | ⟨a, hcap, hO⟩
  · -- An edge with two ends: one push.
    set Zc : Set T := (Γ.U \ e) ∪ D₁ ∪ D₂ with hZcdef
    have hZc : IsClosed Zc := (hZe.union hD₁.isClosed).union hD₂
    have hℓZ : closure e ∩ Zc ⊆ {a, b} := by
      rintro x ⟨hx, hxZ⟩
      by_cases hxe : x ∈ e
      · rcases hxZ with (h | h) | h
        · exact absurd hxe h.2
        · exact absurd h (heD₁ x hxe)
        · exact absurd h (heD₂ x hxe)
      · exact hcap ▸ hclV x hx hxe
    have hbdZ : discBd P ⊆ closure e ∪ Zc := fun x hx => by
      by_cases hxe : x ∈ e
      · exact Or.inl (subset_closure hxe)
      · exact Or.inr (Or.inl (Or.inr (hbdP ⟨hx, hxe⟩)))
    obtain ⟨P', g, hP'd, hPP', hdis, hint, -, -, -, hgP', hgP, hbd'⟩ :=
      exists_pushOff hT hP hL hab heP hZc hℓZ hbdZ
    have hnotZ : ∀ x ∈ P', x ∉ P → x ∉ Zc := fun x hx hxP hxZ =>
      disjoint_left.mp hdis ⟨hx, hxP⟩ hxZ
    have hab' : ∀ x ∈ ({a, b} : Set T), x ∈ discBd D₁ := by
      intro x hx
      have hxV : x ∈ closure e ∩ Γ.V := hcap ▸ hx
      exact hbdP₁ x (heP hxV.1) fun h => heV x h hxV.2
    refine finish P' hP'd hPP' ?_ ?_ z₀ hz₀ (hint ⟨subset_closure hz₀, fun h => heV z₀ hz₀
      (hcap.ge h).2⟩)
    · refine disjoint_left.mpr fun x hx hxi => ?_
      by_cases hxP : x ∈ P
      · exact disjoint_left.mp hPD₂ hxP hxi
      · exact hnotZ x hx hxP (Or.inr (discInt_subset _ hxi))
    · rw [hbd']
      rintro x ⟨hx | hx, hxU⟩
      · exact hbdP₁ x hx.1 fun hxe => hx.2 ⟨subset_closure hxe, fun h =>
          heV x hxe (hcap.ge h).2⟩
      · by_cases hxP : x ∈ P
        · exact hab' x (hgP ⟨hx, hxP⟩)
        · obtain ⟨t, rfl⟩ := hx
          have hxP' : g t ∈ P' := hgP' ⟨t, rfl⟩
          refine absurd (Or.inl (Or.inl ⟨hxU, fun h => hxP (heP' h)⟩)) (hnotZ _ hxP' hxP)
  · -- A loop at `a`: two pushes.
    have ha : a ∈ closure e := (hcap.ge rfl).1
    have haV : a ∈ Γ.V := (hcap.ge rfl).2
    have hae : a ∉ e := fun h => heV a h haV
    have haD₁ : a ∈ discBd D₁ := hbdP₁ a (heP ha) hae
    have hclVa : ∀ x ∈ closure e, x ∉ e → x = a := fun x hx hxe => by
      have := hclV x hx hxe
      rw [hcap] at this
      exact this
    set m := z₀ with hm
    have hme : m ∈ e := hz₀
    have hma : m ≠ a := fun h => hae (h ▸ hme)
    obtain ⟨α, β, htwo, hα0, hα1, hr⟩ := hO.exists_arcs ha (subset_closure hme) hma.symm
    have hβ0 : β 0 = a := htwo.zero.trans hα0
    have hβ1 : β 1 = m := htwo.one.trans hα1
    have hαcl : range α ⊆ closure e := hr ▸ subset_union_left
    have hβcl : range β ⊆ closure e := hr ▸ subset_union_right
    have hmeet : ∀ x ∈ range α, x ∈ range β → x = a ∨ x = m := by
      rintro _ ⟨s, rfl⟩ ⟨t, ht⟩
      rcases htwo.meet s t ht.symm with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact Or.inl hα0
      · exact Or.inr hα1
    -- First push, past `range α`.
    set Zc₁ : Set T := (Γ.U \ e) ∪ D₁ ∪ D₂ ∪ range β with hZc₁def
    have hZc₁ : IsClosed Zc₁ :=
      ((hZe.union hD₁.isClosed).union hD₂).union (isCompact_range htwo.arc_right.1).isClosed
    have hℓ₁ : IsLineWithEnds (range α) a m := hα0 ▸ hα1 ▸ htwo.arc_left.isLineWithEnds
    have hℓ₁Z : range α ∩ Zc₁ ⊆ {a, m} := by
      rintro x ⟨hx, hxZ⟩
      rcases hxZ with ((h | h) | h) | h
      · exact Or.inl (hclVa x (hαcl hx) h.2)
      · by_cases hxe : x ∈ e
        · exact absurd h (heD₁ x hxe)
        · exact Or.inl (hclVa x (hαcl hx) hxe)
      · by_cases hxe : x ∈ e
        · exact absurd h (heD₂ x hxe)
        · exact Or.inl (hclVa x (hαcl hx) hxe)
      · exact hmeet x hx h
    have hbdZ₁ : discBd P ⊆ range α ∪ Zc₁ := fun x hx => by
      by_cases hxe : x ∈ e
      · rcases (hr.ge (subset_closure hxe) : x ∈ range α ∪ range β) with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl (Or.inl (Or.inr (hbdP ⟨hx, hxe⟩))))
    obtain ⟨P₁, g₁, hP₁, hPP₁, hdis₁, -, hg₁, hg₁0, hg₁1, hg₁P₁, hg₁P, hbd₁⟩ :=
      exists_pushOff hT hP hℓ₁ hma.symm ((hαcl.trans heP)) hZc₁ hℓ₁Z hbdZ₁
    have hnot₁ : ∀ x ∈ P₁, x ∉ P → x ∉ Zc₁ := fun x hx hxP hxZ =>
      disjoint_left.mp hdis₁ ⟨hx, hxP⟩ hxZ
    -- The point `c = g₁ (1/2)` and the line `ℓ₂`.
    set h : 𝕀 := ⟨1 / 2, by norm_num, by norm_num⟩ with hhdef
    have hh0 : h ≠ 0 := fun h' => by
      have := congrArg Subtype.val h'
      norm_num [hhdef] at this
    have hh1 : h ≠ 1 := fun h' => by
      have := congrArg Subtype.val h'
      norm_num [hhdef] at this
    set c := g₁ h with hcdef
    have hca : c ≠ a := fun h' => hh0 (hg₁.2 (h'.trans hg₁0.symm))
    have hcP : c ∉ P := by
      intro hcP
      rcases hg₁P ⟨⟨h, rfl⟩, hcP⟩ with h' | h'
      · exact hca h'
      · exact hh1 (hg₁.2 (h'.trans hg₁1.symm))
    have hcU : c ∉ Γ.U := fun hcU =>
      hnot₁ c (hg₁P₁ ⟨h, rfl⟩) hcP (Or.inl (Or.inl (Or.inl ⟨hcU, fun h' => hcP (heP' h')⟩)))
    have hmP : m ∈ P := heP' hme
    have hmc : m ≠ c := fun h' => hcP (h' ▸ hmP)
    have hL₁ : IsLineWithEnds (range (subArc g₁ h 1)) c m := by
      have := (hg₁.sub hh1).isLineWithEnds
      rwa [subArc_zero, subArc_one, hg₁1] at this
    have hL₂ : IsLineWithEnds (range β) m a := (hβ0 ▸ hβ1 ▸ htwo.arc_right.isLineWithEnds).symm
    have hr₁ : range (subArc g₁ h 1) = g₁ '' Icc h 1 := range_subArc g₁ (le_of_lt
      (lt_of_le_of_ne unitInterval.le_one' hh1))
    have hr₀ : range (subArc g₁ 0 h) = g₁ '' Icc 0 h := range_subArc g₁ unitInterval.nonneg'
    have hL₁₂ : range (subArc g₁ h 1) ∩ range β = {m} := by
      refine Subset.antisymm ?_ ?_
      · rintro x ⟨hx1, hx2⟩
        rw [hr₁] at hx1
        obtain ⟨t, ht, rfl⟩ := hx1
        rcases hg₁P ⟨⟨t, rfl⟩, hclP (hβcl hx2)⟩ with h' | h'
        · have := hg₁.2 (h'.trans hg₁0.symm)
          subst this
          exact absurd (le_antisymm ht.1 unitInterval.nonneg') hh0
        · exact h'
      · rintro x rfl
        exact ⟨hr₁ ▸ ⟨1, ⟨unitInterval.le_one', le_rfl⟩, hg₁1⟩, ⟨1, hβ1⟩⟩
    have hℓ₂ := hL₁.union hL₂ hL₁₂
    set ℓ₂ := range (subArc g₁ h 1) ∪ range β with hℓ₂def
    have hmℓ₂ : m ∈ ℓ₂ := Or.inr ⟨1, hβ1⟩
    -- Second push, past `ℓ₂`.
    set Zc₂ : Set T := (Γ.U \ e) ∪ D₁ ∪ D₂ ∪ range (subArc g₁ 0 h) with hZc₂def
    have hZc₂ : IsClosed Zc₂ := ((hZe.union hD₁.isClosed).union hD₂).union
      (isCompact_range (hg₁.sub hh0.symm).1).isClosed
    have hℓ₂P₁ : ℓ₂ ⊆ discBd P₁ := by
      rw [hbd₁]
      rintro x (hx | hx)
      · exact Or.inr (range_subArc_subset _ _ _ hx)
      · refine Or.inl ⟨heP (hβcl hx), fun h' => ?_⟩
        rcases hmeet x h'.1 hx with rfl | rfl
        · exact h'.2 (Or.inl rfl)
        · exact h'.2 (Or.inr rfl)
    have hbase : ∀ x, x ∈ (Γ.U \ e) ∪ D₁ ∪ D₂ → x ∈ Zc₁ := fun x hx => Or.inl hx
    have hℓ₂Z : ℓ₂ ∩ Zc₂ ⊆ {c, a} := by
      rintro x ⟨hx | hx, hxZ⟩
      · rw [hr₁] at hx
        obtain ⟨t, ht, rfl⟩ := hx
        rcases hxZ with hxZ | hxZ
        · by_cases hxP : g₁ t ∈ P
          · rcases hg₁P ⟨⟨t, rfl⟩, hxP⟩ with h' | h'
            · have := hg₁.2 (h'.trans hg₁0.symm)
              subst this
              exact absurd (le_antisymm ht.1 unitInterval.nonneg') hh0
            · rw [h'] at hxZ
              rcases hxZ with (h'' | h'') | h''
              · exact absurd hme h''.2
              · exact absurd h'' (heD₁ m hme)
              · exact absurd h'' (heD₂ m hme)
          · exact absurd (hbase _ hxZ) (hnot₁ _ (hg₁P₁ ⟨t, rfl⟩) hxP)
        · rw [hr₀] at hxZ
          obtain ⟨s, hs, hst⟩ := hxZ
          have := hg₁.2 hst
          subst this
          exact Or.inl (by rw [le_antisymm hs.2 ht.1])
      · rcases hxZ with hxZ | hxZ
        · by_cases hxe : x ∈ e
          · rcases hxZ with (h' | h') | h'
            · exact absurd hxe h'.2
            · exact absurd h' (heD₁ x hxe)
            · exact absurd h' (heD₂ x hxe)
          · exact Or.inr (hclVa x (hβcl hx) hxe)
        · rw [hr₀] at hxZ
          obtain ⟨s, hs, rfl⟩ := hxZ
          rcases hg₁P ⟨⟨s, rfl⟩, hclP (hβcl hx)⟩ with h' | h'
          · exact Or.inr h'
          · have := hg₁.2 (h'.trans hg₁1.symm)
            subst this
            exact absurd (le_antisymm unitInterval.le_one' hs.2) hh1
    have hbdZ₂ : discBd P₁ ⊆ ℓ₂ ∪ Zc₂ := by
      rw [hbd₁]
      rintro x (⟨hx, hxα⟩ | ⟨t, rfl⟩)
      · by_cases hxe : x ∈ e
        · rcases (hr.ge (subset_closure hxe) : x ∈ range α ∪ range β) with h' | h'
          · by_cases hxa : x = a
            · exact absurd (hxa ▸ hxe) hae
            · by_cases hxm : x = m
              · exact Or.inl (hxm ▸ hmℓ₂)
              · exact absurd ⟨h', by rintro (h'' | h'') <;> contradiction⟩ hxα
          · exact Or.inl (Or.inr h')
        · exact Or.inr (Or.inl (Or.inl (Or.inr (hbdP ⟨hx, hxe⟩))))
      · by_cases ht : t ≤ h
        · exact Or.inr (Or.inr (hr₀ ▸ ⟨t, ⟨unitInterval.nonneg', ht⟩, rfl⟩))
        · exact Or.inl (Or.inl (hr₁ ▸ ⟨t, ⟨le_of_lt (not_le.mp ht), unitInterval.le_one'⟩, rfl⟩))
    obtain ⟨P₂, g₂, hP₂, hP₁P₂, hdis₂, hint₂, -, -, -, hg₂P₂, hg₂P₁, hbd₂⟩ :=
      exists_pushOff hT hP₁ hℓ₂ hca hℓ₂P₁ hZc₂ hℓ₂Z hbdZ₂
    have hnot₂ : ∀ x ∈ P₂, x ∉ P₁ → x ∉ Zc₂ := fun x hx hxP hxZ =>
      disjoint_left.mp hdis₂ ⟨hx, hxP⟩ hxZ
    have hmℓ₂' : m ∈ ℓ₂ \ {c, a} := ⟨hmℓ₂, by rintro (h' | h'); exacts [hmc h', hma h']⟩
    refine finish P₂ hP₂ (hPP₁.trans hP₁P₂) ?_ ?_ m hme (hint₂ hmℓ₂')
    · refine disjoint_left.mpr fun x hx hxi => ?_
      have hxD₂ : x ∈ D₂ := discInt_subset _ hxi
      by_cases hx₁ : x ∈ P₁
      · by_cases hxP : x ∈ P
        · exact disjoint_left.mp hPD₂ hxP hxi
        · exact hnot₁ x hx₁ hxP (Or.inl (Or.inr hxD₂))
      · exact hnot₂ x hx hx₁ (Or.inl (Or.inr hxD₂))
    · rw [hbd₂]
      rintro x ⟨hx | hx, hxU⟩
      · -- `x` on the old boundary of `P₁`, off the inside of `ℓ₂`.
        obtain ⟨hx, hxℓ⟩ := hx
        rw [hbd₁] at hx
        rcases hx with ⟨hxP, hxα⟩ | ⟨t, rfl⟩
        · by_cases hxe : x ∈ e
          · rcases (hr.ge (subset_closure hxe) : x ∈ range α ∪ range β) with h' | h'
            · by_cases hxm : x = m
              · exact absurd (hxm ▸ hmℓ₂') hxℓ
              · have hxam : x ∉ ({a, m} : Set T) := by
                  rintro (h'' | h'')
                  · exact hae (h'' ▸ hxe)
                  · exact hxm h''
                exact absurd ⟨h', hxam⟩ hxα
            · by_cases hxc : x = c
              · exact absurd (hxc ▸ heP' hxe) hcP
              · have hxca : x ∉ ({c, a} : Set T) := by
                  rintro (h'' | h'')
                  · exact hxc h''
                  · exact hae (h'' ▸ hxe)
                exact absurd ⟨Or.inr h', hxca⟩ hxℓ
          · exact hbdP₁ x hxP hxe
        · by_cases hxP : g₁ t ∈ P
          · rcases hg₁P ⟨⟨t, rfl⟩, hxP⟩ with h' | h'
            · rw [show g₁ t = a from h']; exact haD₁
            · exact absurd (h' ▸ hmℓ₂') hxℓ
          · exact absurd (Or.inl (Or.inl (Or.inl ⟨hxU, fun h' => hxP (heP' h')⟩)))
              (hnot₁ _ (hg₁P₁ ⟨t, rfl⟩) hxP)
      · by_cases hx₁ : x ∈ P₁
        · rcases hg₂P₁ ⟨hx, hx₁⟩ with h' | h'
          · rw [show x = c from h'] at hxU; exact absurd hxU hcU
          · rw [show x = a from h']; exact haD₁
        · exact absurd (Or.inl (Or.inl (Or.inl ⟨hxU, fun h' => hx₁ (hPP₁ (heP' h'))⟩)))
            (hnot₂ x (hg₂P₂ hx) hx₁)

/-- A preconnected nonempty subset of a set with two components lies in one of them. -/
theorem subset_or_subset_of_componentsIn_eq_pair {T : Type*} [TopologicalSpace T]
    {F X C₁ C₂ : Set T} (hF : componentsIn F = {C₁, C₂}) (hX : IsPreconnected X)
    (hXn : X.Nonempty) (hXF : X ⊆ F) : X ⊆ C₁ ∨ X ⊆ C₂ := by
  obtain ⟨x, hx⟩ := hXn
  have hmem : connectedComponentIn F x ∈ componentsIn F := ⟨x, hXF hx, rfl⟩
  rw [hF] at hmem
  have hsub := hX.subset_connectedComponentIn hx hXF
  rcases hmem with h | h
  · exact Or.inl (h ▸ hsub)
  · exact Or.inr (h ▸ hsub)

/-- **Claim C, parts (i)–(iii).** In a sphere, let `D₁`, `D₂` be closed discs as in
`false_of_edge_on_discBd`, with `D₁` outside the inside of `D₂`, and the drawing outside the inside
of `D₂`. Let `e` be an edge outside `D₁ ∪ D₂` whose ends lie on `bd D₁`. Then `e` is a loop that
bounds a closed disc meeting `D₁ ∪ D₂` only at its end.

If `e` has two ends `a ≠ b`, it is a chord of the closed disc `E` outside `D₁`, and cuts `E` into
two closed discs (`disc_iArc`). The inside of `D₂` lies in one of them. The other one, `K`, meets
`D₁` in an arc of `bd D₁` from `a` to `b`, so `D₁ ∪ K` is a closed disc (`disc_union`) with the
closure of `e` on its boundary: this contradicts `false_of_edge_on_discBd`. If `e` is a loop, its
closure bounds two closed discs (`sphere_disc`). The insides of `D₁` and of `D₂` each lie on one
side. If they lie on different sides, the side of `D₁` contradicts `false_of_edge_on_discBd`. If
they lie on the same side, the other side is the disc we want. -/
theorem exists_loopDisc {T : Type} [TopologicalSpace T] (hT : IsClosedSurface T)
    (hsph : IsSphere T) (Γ : Drawing T) {D₁ D₂ e : Set T} (hD₁ : IsClosedDisc D₁)
    (hD₂ : IsClosedDisc D₂) (hDD : Disjoint D₁ (discInt D₂)) (hUD : Disjoint Γ.U (discInt D₂))
    (hpush : ∀ Δ : Set T, IsClosedDisc Δ → D₁ ⊆ Δ → Disjoint Δ (discInt D₂) →
      discBd Δ ∩ Γ.U ⊆ discBd D₁ → Γ.U ∩ discInt Δ ⊆ D₁)
    (he : e ∈ Γ.E) (heD : Disjoint e (D₁ ∪ D₂)) (hends : closure e ∩ Γ.V ⊆ discBd D₁) :
    ∃ De : Set T, IsClosedDisc De ∧ discBd De = closure e ∧
      De ∩ (D₁ ∪ D₂) ⊆ closure e ∩ Γ.V := by
  classical
  have ht2 : T2Space T := hT.2.1
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  have heV : ∀ x ∈ e, x ∉ Γ.V := fun x hx => (he.2.1 hx).2
  have hdiff := Γ.closure_diff_V he
  have hclU := Γ.closure_subset_U he
  have hclV : ∀ x ∈ closure e, x ∉ e → x ∈ closure e ∩ Γ.V := fun x hx hxe =>
    ⟨hx, by_contra fun h => hxe (hdiff ▸ ⟨hx, h⟩)⟩
  have heD₁ : ∀ x ∈ e, x ∉ D₁ := fun x hx h => disjoint_left.mp heD hx (Or.inl h)
  have hclD : ∀ x ∈ closure e, x ∈ D₁ ∪ D₂ → x ∈ closure e ∩ Γ.V := fun x hx hxD =>
    hclV x hx fun hxe => disjoint_left.mp heD hxe hxD
  have hint₂ : (discInt D₂).Nonempty := hD₂.nonempty_discInt
  have hpre₂ := hD₂.isPreconnected_discInt
  have hint₂e : ∀ x ∈ discInt D₂, x ∉ closure e := fun x hx hxe =>
    disjoint_left.mp hUD (hclU hxe) hx
  have hP₂cl : ∀ {Δ : Set T}, IsClosed Δ → discInt D₂ ⊆ Δ → D₂ ⊆ Δ := fun hΔ h =>
    hD₂.subset_closure_discInt.trans (closure_minimal h hΔ)
  have hP₁cl : ∀ {Δ : Set T}, IsClosed Δ → discInt D₁ ⊆ Δ → D₁ ⊆ Δ := fun hΔ h =>
    hD₁.subset_closure_discInt.trans (closure_minimal h hΔ)
  rcases Γ.edge_cond e he with ⟨a, b, hab, hcap, hL⟩ | ⟨a, hcap, hO⟩
  · exfalso
    obtain ⟨hE, hbE⟩ := GM12.isClosedDisc_closure_compl_of_sphere hT hsph hD₁
    set E := closure (univ \ D₁) with hEdef
    have heE : closure e ⊆ E := closure_mono fun x hx => ⟨mem_univ x, heD₁ x hx⟩
    have haV : a ∈ closure e ∩ Γ.V := hcap.ge (Or.inl rfl)
    have hbV : b ∈ closure e ∩ Γ.V := hcap.ge (Or.inr rfl)
    have hebd : closure e ∩ discBd E = {a, b} := by
      refine Subset.antisymm (fun x ⟨hx, hxb⟩ => ?_) ?_
      · rw [hbE] at hxb
        exact hcap ▸ hclV x hx fun hxe => heD₁ x hxe (discBd_subset _ hxb)
      · rintro x (rfl | rfl)
        · exact ⟨haV.1, hbE ▸ hends haV⟩
        · exact ⟨hbV.1, hbE ▸ hends hbV⟩
    obtain ⟨A₁, A₂, K₁, K₂, -, hcomp, hK₁, hK₂, hcup, hcap', hbK₁, hbK₂, hcompK⟩ :=
      disc_iArc E (closure e) a b hE heE hab hL hebd
    have hint₂E : discInt D₂ ⊆ E \ closure e := fun x hx =>
      ⟨subset_closure ⟨mem_univ x, fun h => disjoint_left.mp hDD h hx⟩, hint₂e x hx⟩
    have hDE : D₁ ∩ E ⊆ discBd D₁ := by
      rintro x ⟨hxD, hxE⟩
      by_contra hcon
      obtain ⟨y, hy, hyD⟩ := mem_closure_iff.mp hxE _ (hD₁.isOpen_discInt hman) ⟨hxD, hcon⟩
      exact hyD.2 hy.1
    -- The disc `K` away from `D₂`.
    have key : ∀ K A, IsClosedDisc K → K ⊆ E → discBd K = A ∪ closure e →
        A ∈ componentsIn (discBd E \ {a, b}) → Disjoint K (discInt D₂) → False := by
      intro K A hK hKE hbK hA hKD
      have hAsub := (isPreconnected_and_subset_of_mem_componentsIn hA).2
      obtain ⟨α, β, htwo, hα0, hα1, hr⟩ :=
        hD₁.isOArc_discBd.exists_arcs (hends haV) (hends hbV) hab
      have hc := componentsIn_twoArcs htwo
      rw [hr, hα0, hα1, ← hbE] at hc
      rw [hc] at hA
      have hgex : ∃ g : 𝕀 → T, IsArcMap g ∧ g 0 = a ∧ g 1 = b ∧ A = g '' Ioo 0 1 ∧
          range g ⊆ discBd D₁ := by
        rcases hA with h | h
        · exact ⟨α, htwo.arc_left, hα0, hα1, h, hr ▸ subset_union_left⟩
        · exact ⟨β, htwo.arc_right, htwo.zero.trans hα0, htwo.one.trans hα1, h,
            hr ▸ subset_union_right⟩
      obtain ⟨g, hg, hg0, hg1, hAg, hgD⟩ := hgex
      have hrg : range g = A ∪ {a, b} := by
        ext x
        constructor
        · rintro ⟨t, rfl⟩
          by_cases h0 : t = 0
          · exact Or.inr (Or.inl (h0 ▸ hg0))
          by_cases h1 : t = 1
          · exact Or.inr (Or.inr (h1 ▸ hg1))
          refine Or.inl (hAg ▸ ⟨t, ⟨?_, ?_⟩, rfl⟩)
          · exact lt_of_le_of_ne t.2.1 fun h => h0 h.symm
          · exact lt_of_le_of_ne t.2.2 fun h => h1 h
        · rintro (hx | rfl | rfl)
          · rw [hAg] at hx
            obtain ⟨t, -, rfl⟩ := hx
            exact mem_range_self t
          · exact ⟨0, hg0⟩
          · exact ⟨1, hg1⟩
      have hAK : A ⊆ discBd K := fun x hx => hbK ▸ Or.inl hx
      have heK : closure e ⊆ discBd K := fun x hx => hbK ▸ Or.inr hx
      have hAe : ∀ x ∈ A, x ∉ closure e := fun x hx hxe =>
        (hAsub hx).2 (hebd ▸ ⟨hxe, (hAsub hx).1⟩)
      have hgK : range g ⊆ discBd K := by
        rw [hrg]
        rintro x (hx | rfl | rfl)
        · exact hAK hx
        · exact heK haV.1
        · exact heK hbV.1
      have hDK : D₁ ∩ K = range g := by
        refine Subset.antisymm (fun x ⟨hxD, hxK⟩ => ?_) fun x hx =>
          ⟨discBd_subset _ (hgD hx), discBd_subset _ (hgK hx)⟩
        have hxb : x ∈ discBd D₁ := hDE ⟨hxD, hKE hxK⟩
        have hxbK : x ∈ discBd K := by
          by_contra hcon
          have := subset_discInt_of_isOpen hT hE (hK.isOpen_discInt hman)
            (fun y hy => hKE hy.1) ⟨hxK, hcon⟩
          exact this.2 (hbE ▸ hxb)
        rw [hbK] at hxbK
        rw [hrg]
        rcases hxbK with h | h
        · exact Or.inl h
        · exact Or.inr (hebd ▸ ⟨h, hbE ▸ hxb⟩)
      have hgL : IsLineWithEnds (range g) a b := hg0 ▸ hg1 ▸ hg.isLineWithEnds
      obtain ⟨hP, hbP⟩ := disc_union D₁ K (range g) a b hD₁ hK hgL hDK hgD hgK
      refine false_of_edge_on_discBd hT Γ hD₁ hD₂.isClosed hpush he heD hP
        subset_union_left ?_ ?_ ?_
      · refine disjoint_left.mpr fun x hx hxi => ?_
        rcases hx with hx | hx
        · exact disjoint_left.mp hDD hx hxi
        · exact disjoint_left.mp hKD hx hxi
      · intro x hx
        rw [hbP]
        refine ⟨Or.inr (heK hx), fun h => h.2 ?_⟩
        rw [hrg] at h
        rcases h.1 with h' | h'
        · exact absurd hx (hAe x h')
        · exact h'
      · rintro x ⟨hx, hxe⟩
        rw [hbP] at hx
        rcases hx.1 with h | h
        · exact discBd_subset _ h
        · rw [hbK] at h
          rcases h with h | h
          · exact discBd_subset _ (hgD (hrg ▸ Or.inl h))
          · exact discBd_subset _ (hends (hclV x h hxe))
    have hK₁E : K₁ ⊆ E := subset_union_left.trans hcup.le
    have hK₂E : K₂ ⊆ E := subset_union_right.trans hcup.le
    rcases subset_or_subset_of_componentsIn_eq_pair hcompK hpre₂ hint₂ hint₂E with h | h
    · refine key K₂ A₂ hK₂ hK₂E hbK₂ (by rw [hcomp]; exact Or.inr rfl) ?_
      refine disjoint_left.mpr fun x hx hxi => (h hxi).2 ?_
      exact hcap' ▸ ⟨(h hxi).1, hx⟩
    · refine key K₁ A₁ hK₁ hK₁E hbK₁ (by rw [hcomp]; exact Or.inl rfl) ?_
      refine disjoint_left.mpr fun x hx hxi => (h hxi).2 ?_
      exact hcap' ▸ ⟨hx, (h hxi).1⟩
  · -- A loop.
    obtain ⟨Δ₁, Δ₂, -, hΔ₁, hΔ₂, hb₁, hb₂, hcup, hcap', hcomp, -⟩ := sphere_disc T hsph _ hO
    have hint₁ : discInt D₁ ⊆ univ \ closure e := fun x hx =>
      ⟨mem_univ x, fun hxe => hx.2 (hends (hclD x hxe (Or.inl hx.1)))⟩
    have hint₂' : discInt D₂ ⊆ univ \ closure e := fun x hx => ⟨mem_univ x, hint₂e x hx⟩
    have loopkey : ∀ Δ Δ' : Set T, IsClosedDisc Δ → IsClosedDisc Δ' → discBd Δ = closure e →
        discBd Δ' = closure e → Δ ∩ Δ' = closure e → discInt D₁ ⊆ Δ \ closure e →
        (discInt D₂ ⊆ Δ \ closure e ∨ discInt D₂ ⊆ Δ' \ closure e) →
        ∃ De : Set T, IsClosedDisc De ∧ discBd De = closure e ∧
          De ∩ (D₁ ∪ D₂) ⊆ closure e ∩ Γ.V := by
      intro Δ Δ' hΔ hΔ' hb hb' hcapΔ h₁ h₂
      have hD₁Δ : D₁ ⊆ Δ := hP₁cl hΔ.isClosed fun x hx => (h₁ hx).1
      rcases h₂ with h₂ | h₂
      · refine ⟨Δ', hΔ', hb', ?_⟩
        have hD₂Δ : D₂ ⊆ Δ := hP₂cl hΔ.isClosed fun x hx => (h₂ hx).1
        rintro x ⟨hx, hxD⟩
        have hxΔ : x ∈ Δ := by
          rcases hxD with h | h
          · exact hD₁Δ h
          · exact hD₂Δ h
        exact hclD x (hcapΔ ▸ ⟨hxΔ, hx⟩) hxD
      · exfalso
        refine false_of_edge_on_discBd hT Γ hD₁ hD₂.isClosed hpush he heD hΔ hD₁Δ ?_ hb.ge ?_
        · refine disjoint_left.mpr fun x hx hxi => (h₂ hxi).2 ?_
          exact hcapΔ ▸ ⟨hx, (h₂ hxi).1⟩
        · rintro x ⟨hx, hxe⟩
          rw [hb] at hx
          exact discBd_subset _ (hends (hclV x hx hxe))
    have hcap'' : Δ₂ ∩ Δ₁ = closure e := inter_comm Δ₂ Δ₁ ▸ hcap'
    rcases subset_or_subset_of_componentsIn_eq_pair hcomp hD₁.isPreconnected_discInt
      hD₁.nonempty_discInt hint₁ with h₁ | h₁
    · rcases subset_or_subset_of_componentsIn_eq_pair hcomp hpre₂ hint₂ hint₂' with h₂ | h₂
      · exact loopkey Δ₁ Δ₂ hΔ₁ hΔ₂ hb₁ hb₂ hcap' h₁ (Or.inl h₂)
      · exact loopkey Δ₁ Δ₂ hΔ₁ hΔ₂ hb₁ hb₂ hcap' h₁ (Or.inr h₂)
    · rcases subset_or_subset_of_componentsIn_eq_pair hcomp hpre₂ hint₂ hint₂' with h₂ | h₂
      · exact loopkey Δ₂ Δ₁ hΔ₂ hΔ₁ hb₂ hb₁ hcap'' h₁ (Or.inr h₂)
      · exact loopkey Δ₂ Δ₁ hΔ₂ hΔ₁ hb₂ hb₁ hcap'' h₁ (Or.inl h₂)

/-- **An edge that touches a face lies in its closure.** Let `f` be a component of an open set `Q`
that holds every point off the drawing and off a closed set `Zc`, and misses the drawing. An edge
outside `Zc` with a point in the closure of `f` lies in the closure of `f`. Near a point of the
edge, the two sides of the edge (`GM11.exists_edge_sides_off`) lie in `Q`; one of them meets `f`,
so it lies in `f`, and the edge near the point is in its closure. So the part of the edge in the
closure of `f` is open in the edge; it is also closed, and the edge is connected. -/
theorem edge_subset_closure_of_component {T : Type} [TopologicalSpace T]
    (hT : IsClosedSurface T) (Γ : Drawing T) {Q Zc : Set T} (hZc : IsClosed Zc)
    (hQ : ∀ x, x ∉ Zc → x ∉ Γ.U → x ∈ Q) (hQU : Disjoint Q Γ.U) {p : T} {e : Set T}
    (he : e ∈ Γ.E) (heZ : Disjoint e Zc)
    (hinc : (e ∩ closure (connectedComponentIn Q p)).Nonempty) :
    e ⊆ closure (connectedComponentIn Q p) := by
  have : T2Space T := hT.2.1
  set f := connectedComponentIn Q p with hfdef
  have hfU : Disjoint f Γ.U := hQU.mono_left (connectedComponentIn_subset _ _)
  have hstep : ∀ z ∈ e ∩ closure f, ∃ W : Set T, IsOpen W ∧ z ∈ W ∧ e ∩ W ⊆ closure f := by
    rintro z ⟨hze, hzf⟩
    obtain ⟨W, A₁, A₂, -, -, hW, hzW, -, hsub, hA₁, hA₂, hU₁, hU₂, c₁, c₂, -, -, -, -, -, -,
      hZ₁, hZ₂⟩ := GM11.exists_edge_sides_off hT Γ he hze hZc
        (fun h => disjoint_left.mp heZ hze h)
    refine ⟨W, hW, hzW, ?_⟩
    obtain ⟨w, hwW, hwf⟩ := mem_closure_iff.mp hzf W hW hzW
    have hwU : w ∉ Γ.U := disjoint_left.mp hfU hwf
    have hside : ∀ A : Set T, IsPreconnected A → Disjoint A Γ.U → Disjoint A Zc → w ∈ A →
        A ⊆ f := fun A hA hAU hAZ hwA => by
      have hAQ : A ⊆ Q := fun x hx =>
        hQ x (disjoint_left.mp hAZ hx) (disjoint_left.mp hAU hx)
      rw [hfdef, connectedComponentIn_eq hwf]
      exact hA.subset_connectedComponentIn hwA hAQ
    rcases hsub ⟨hwW, hwU⟩ with hw | hw
    · exact c₁.trans (closure_mono (hside A₁ hA₁ hU₁ hZ₁ hw))
    · exact c₂.trans (closure_mono (hside A₂ hA₂ hU₂ hZ₂ hw))
  choose! W hWo hpW hWs using hstep
  let O : Set T := ⋃ z ∈ e ∩ closure f, W z
  have hO : IsOpen O := isOpen_biUnion fun z hz => hWo z hz
  by_contra hcon
  obtain ⟨z, hze, hzr⟩ := not_subset.mp hcon
  have hconn : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
  have hcov : e ⊆ O ∪ (closure f)ᶜ := by
    intro y hy
    by_cases hyr : y ∈ closure f
    · exact Or.inl (mem_iUnion₂.mpr ⟨y, ⟨hy, hyr⟩, hpW y ⟨hy, hyr⟩⟩)
    · exact Or.inr hyr
  obtain ⟨q, hq⟩ := hinc
  obtain ⟨y, hye, hyO, hyr⟩ := hconn O (closure f)ᶜ hO isClosed_closure.isOpen_compl hcov
    ⟨q, hq.1, mem_iUnion₂.mpr ⟨q, hq, hpW q hq⟩⟩ ⟨z, hze, hzr⟩
  obtain ⟨q', hq', hyq⟩ := mem_iUnion₂.mp hyO
  exact hyr (hWs q' hq' ⟨hye, hyq⟩)

/-- A point of an open set in the closure of one of its components lies in that component. -/
theorem mem_of_mem_closure_connectedComponentIn {T : Type*} [TopologicalSpace T]
    [LocallyConnectedSpace T] {O : Set T} (hO : IsOpen O) {w y : T}
    (hy : y ∈ closure (connectedComponentIn O w)) (hyO : y ∈ O) :
    y ∈ connectedComponentIn O w := by
  obtain ⟨z, hz, hzw⟩ := mem_closure_iff.mp hy _ (hO.connectedComponentIn (x := y))
    (mem_connectedComponentIn hyO)
  rw [connectedComponentIn_eq hzw, ← connectedComponentIn_eq hz]
  exact mem_connectedComponentIn hyO

/-- In a sphere, a closed disc meets the closed disc outside a closed disc `D₂` only on `bd D₂`. -/
theorem inter_closure_compl_subset_discBd {T : Type} [TopologicalSpace T]
    (hT : IsClosedSurface T) {D : Set T} (hD : IsClosedDisc D) :
    D ∩ closure (univ \ D) ⊆ discBd D := by
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  rintro x ⟨hxD, hxE⟩
  by_contra hcon
  obtain ⟨y, hy, hyD⟩ := mem_closure_iff.mp hxE _ (hD.isOpen_discInt hman) ⟨hxD, hcon⟩
  exact hyD.2 hy.1

/-- **Claim C, the start of part (iv).** In a sphere, let `D₁`, `D₂` be closed discs with `D₁`
outside the inside of `D₂`, and let `x ∈ bd D₂ \ D₁`. Some connected set `Ω` outside `D₁ ∪ D₂`
has `x` in its closure, and also a point `p` of `bd D₁` that lies neither on the drawing nor in
`D₂`.

A path from `x` into the inside of the disc outside `D₂` (`GM11.exists_path_into_disc`) lies in
one component `Ω` of the complement of `D₁ ∪ D₂`. If its closure held no such `p`, then `Ω` would be
open and closed in the inside of the disc outside `D₂` minus the finitely many vertices on
`bd D₁`. This set is connected (`GM11.isPreconnected_sdiff_finite`), so `Ω` would hold the inside
of `D₁`. -/
theorem exists_free_point {T : Type} [TopologicalSpace T] (hT : IsClosedSurface T)
    (hsph : IsSphere T) (Γ : Drawing T) {D₁ D₂ : Set T} (hD₁ : IsClosedDisc D₁)
    (hD₂ : IsClosedDisc D₂) (hDD : Disjoint D₁ (discInt D₂))
    (hU₁ : Γ.U ∩ discBd D₁ ⊆ Γ.V) {x : T} (hxD₂ : x ∈ discBd D₂) (hxD₁ : x ∉ D₁) :
    ∃ Ω : Set T, IsPreconnected Ω ∧ Ω ⊆ (D₁ ∪ D₂)ᶜ ∧ x ∈ closure Ω ∧
      ∃ p ∈ closure Ω, p ∈ discBd D₁ ∧ p ∉ Γ.U ∧ p ∉ D₂ := by
  classical
  have ht2 : T2Space T := hT.2.1
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  have hlc : LocallyConnectedSpace T := GM11.IsClosedSurface.locallyConnectedSpace hT
  obtain ⟨hE₂, hbE₂⟩ := GM12.isClosedDisc_closure_compl_of_sphere hT hsph hD₂
  set E₂ := closure (univ \ D₂) with hE₂def
  have hintE : ∀ y ∈ discInt E₂, y ∉ D₂ := fun y hy hyD =>
    hy.2 (hbE₂ ▸ inter_closure_compl_subset_discBd hT hD₂ ⟨hyD, hy.1⟩)
  obtain ⟨g, hgc, -, hg0, hg⟩ := GM11.exists_path_into_disc hE₂ (hbE₂ ▸ hxD₂ : x ∈ discBd E₂)
    hD₁.isClosed.isOpen_compl hxD₁
  set Ω₀ : Set T := (D₁ ∪ D₂)ᶜ with hΩ₀def
  have hΩ₀ : IsOpen Ω₀ := (hD₁.isClosed.union hD₂.isClosed).isOpen_compl
  have hgΩ : ∀ t : 𝕀, 0 < t → g t ∈ Ω₀ := fun t ht => by
    obtain ⟨h1, h2, h3⟩ := hg t ht
    rintro (h | h)
    · exact h1 h
    · exact hintE (g t) ⟨h2, h3⟩ h
  set h : 𝕀 := ⟨1 / 2, by norm_num, by norm_num⟩ with hhdef
  have hh : (0 : 𝕀) < h := by change (0 : ℝ) < 1 / 2; norm_num
  have hh1 : h < 1 := by change (1 / 2 : ℝ) < 1; norm_num
  set Ω := connectedComponentIn Ω₀ (g h) with hΩdef
  have hΩo : IsOpen Ω := hΩ₀.connectedComponentIn
  have hΩsub : Ω ⊆ Ω₀ := connectedComponentIn_subset _ _
  have hG : g '' Ioo 0 1 ⊆ Ω := by
    refine (ordConnected_Ioo.isPreconnected.image g hgc.continuousOn).subset_connectedComponentIn
      ⟨h, ⟨hh, hh1⟩, rfl⟩ ?_
    rintro _ ⟨t, ht, rfl⟩
    exact hgΩ t ht.1
  have hxcl : x ∈ closure Ω := by
    have h0 : (0 : 𝕀) ∈ closure (Ioo (0 : 𝕀) 1) := by
      rw [closure_Ioo zero_ne_one]; exact ⟨le_rfl, zero_le_one⟩
    have := mem_closure_image hgc.continuousAt h0
    rw [hg0] at this
    exact closure_mono hG this
  refine ⟨Ω, isPreconnected_connectedComponentIn, hΩsub, hxcl, ?_⟩
  by_contra hcon
  push Not at hcon
  set F' := Γ.V ∩ discBd D₁ with hF'def
  have hF' : F'.Finite := Γ.finite_V.subset inter_subset_left
  set X := discInt E₂ \ F' with hXdef
  have hX : IsPreconnected X :=
    GM11.isPreconnected_sdiff_finite hT (hE₂.isOpen_discInt hman) hE₂.isPreconnected_discInt hF'
  have hghX : g h ∈ X := by
    obtain ⟨h1, h2, h3⟩ := hg h hh
    exact ⟨⟨h2, h3⟩, fun h' => h1 (discBd_subset _ h'.2)⟩
  have hXΩ : X ⊆ Ω := by
    refine hX.subset_left_of_subset_union hΩo isClosed_closure.isOpen_compl
      (disjoint_left.mpr fun y hy hy' => hy' (subset_closure hy)) (fun y hy => ?_)
      ⟨g h, hghX, mem_connectedComponentIn (hgΩ h hh)⟩
    by_cases hycl : y ∈ closure Ω
    · refine Or.inl ?_
      by_cases hyΩ₀ : y ∈ Ω₀
      · exact mem_of_mem_closure_connectedComponentIn hΩ₀ hycl hyΩ₀
      · exfalso
        have hyD₂ : y ∉ D₂ := hintE y hy.1
        have hyD₁ : y ∈ D₁ := by
          by_contra h'
          exact hyΩ₀ (by rintro (h'' | h''); exacts [h' h'', hyD₂ h''])
        have hyb : y ∈ discBd D₁ := by
          by_contra h'
          obtain ⟨z, hz, hzΩ⟩ := mem_closure_iff.mp hycl _ (hD₁.isOpen_discInt hman) ⟨hyD₁, h'⟩
          exact hΩsub hzΩ (Or.inl hz.1)
        have hyU : y ∉ Γ.U := fun hyU => hy.2 ⟨hU₁ ⟨hyU, hyb⟩, hyb⟩
        exact hyD₂ (hcon y hycl hyb hyU)
    · exact Or.inr hycl
  obtain ⟨z, hz⟩ := hD₁.nonempty_discInt
  have hzD₂ : z ∉ D₂ := by
    intro hzD₂
    by_cases hzb : z ∈ discBd D₂
    · obtain ⟨w, hw, hw'⟩ := mem_closure_iff.mp (hD₂.subset_closure_discInt (discBd_subset _ hzb))
        _ (hD₁.isOpen_discInt hman) hz
      exact disjoint_left.mp hDD hw.1 hw'
    · exact disjoint_left.mp hDD hz.1 ⟨hzD₂, hzb⟩
  have hzX : z ∈ X := ⟨⟨subset_closure ⟨mem_univ z, hzD₂⟩, fun h' => hzD₂
    (discBd_subset _ (hbE₂ ▸ h'))⟩, fun h' => hz.2 h'.2⟩
  exact hΩsub (hXΩ hzX) (Or.inl hz.1)

/-- **Claim C.** In a sphere, let `D₁`, `D₂` be closed discs, with `D₁` outside the inside of
`D₂`, and the drawing outside the inside of `D₂`, meeting `bd D₁` and `bd D₂` only in vertices.
Suppose that the pushing property `hpush` holds (`Tube.image_inter_discInt_subset_of_maximal`),
and that a vertex `x` lies on `bd D₂` but not in `D₁`. Then a connected set `f` that misses the
drawing and `bd D₂` and meets the inside of `D₁` has in its closure a vertex outside `D₁`.

This gives the vertex `v` of Lemma 4. Take `Ω` and the free point `p` of
`exists_free_point`, a connected neighbourhood `O_p` of `p` off the drawing and `D₂`, and the
component `f` of `((D₁ ∪ D₂)ᶜ ∪ O_p) \ U` that holds `O_p`. Suppose that no vertex outside `D₁` is in
the closure of `f`. Every edge outside `D₁ ∪ D₂` in the closure of `f` then has its ends on
`bd D₁`, so it is a loop with a disc `De` (`exists_loopDisc`). The union `N` of `f` and these discs
without their ends is open and closed in `(D₁ ∪ D₂)ᶜ ∪ O_p`: near a point of such a loop, one side
of the loop lies in `f` and the other inside `De`, and a point of the drawing in the closure of
`f` lies on an edge in the closure of `f` (`edge_subset_closure_of_component`). So `N` holds the
connected set `Ω ∪ O_p`, and `x` lies in the closure of `f` or in some `De`. Both are false. -/
theorem exists_exposed_region {T : Type} [TopologicalSpace T] (hT : IsClosedSurface T)
    (hsph : IsSphere T) (Γ : Drawing T) {D₁ D₂ : Set T} (hD₁ : IsClosedDisc D₁)
    (hD₂ : IsClosedDisc D₂) (hDD : Disjoint D₁ (discInt D₂)) (hUD : Disjoint Γ.U (discInt D₂))
    (hU₁ : Γ.U ∩ discBd D₁ ⊆ Γ.V) (hU₂ : Γ.U ∩ discBd D₂ ⊆ Γ.V)
    (hpush : ∀ Δ : Set T, IsClosedDisc Δ → D₁ ⊆ Δ → Disjoint Δ (discInt D₂) →
      discBd Δ ∩ Γ.U ⊆ discBd D₁ → Γ.U ∩ discInt Δ ⊆ D₁)
    {x : T} (hxV : x ∈ Γ.V) (hxD₂ : x ∈ discBd D₂) (hxD₁ : x ∉ D₁) :
    ∃ W : Set T, IsPreconnected W ∧ Disjoint W (Γ.U ∪ D₂) ∧ (W ∩ discInt D₁).Nonempty ∧
      ∃ v ∈ Γ.V, v ∉ D₁ ∧ v ∈ closure W := by
  classical
  have ht2 : T2Space T := hT.2.1
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  have hlc : LocallyConnectedSpace T := GM11.IsClosedSurface.locallyConnectedSpace hT
  obtain ⟨Ω, hΩc, hΩsub, hxcl, p, hpcl, hpb, hpU, hpD₂⟩ :=
    exists_free_point hT hsph Γ hD₁ hD₂ hDD hU₁ hxD₂ hxD₁
  have hZc : IsClosed (D₁ ∪ D₂) := hD₁.isClosed.union hD₂.isClosed
  set Op := connectedComponentIn (Γ.U ∪ D₂)ᶜ p with hOpdef
  have hpOp' : p ∈ (Γ.U ∪ D₂)ᶜ := by rintro (h | h); exacts [hpU h, hpD₂ h]
  have hOpo : IsOpen Op := (Γ.isClosed_U.union hD₂.isClosed).isOpen_compl.connectedComponentIn
  have hOpc : IsPreconnected Op := isPreconnected_connectedComponentIn
  have hpOp : p ∈ Op := mem_connectedComponentIn hpOp'
  have hOpsub : Op ⊆ (Γ.U ∪ D₂)ᶜ := connectedComponentIn_subset _ _
  set Ωs : Set T := (D₁ ∪ D₂)ᶜ ∪ Op with hΩsdef
  set Q : Set T := Ωs \ Γ.U with hQdef
  have hQo : IsOpen Q := (hZc.isOpen_compl.union hOpo).sdiff Γ.isClosed_U
  have hQ : ∀ y, y ∉ D₁ ∪ D₂ → y ∉ Γ.U → y ∈ Q := fun y h1 h2 => ⟨Or.inl h1, h2⟩
  have hQU : Disjoint Q Γ.U := disjoint_left.mpr fun y hy => hy.2
  have hpQ : p ∈ Q := ⟨Or.inr hpOp, hpU⟩
  set f := connectedComponentIn Q p with hfdef
  have hfo : IsOpen f := hQo.connectedComponentIn
  have hfc : IsPreconnected f := isPreconnected_connectedComponentIn
  have hfQ : f ⊆ Q := connectedComponentIn_subset _ _
  have hOpf : Op ⊆ f := hOpc.subset_connectedComponentIn hpOp
    fun y hy => ⟨Or.inr hy, fun h => hOpsub hy (Or.inl h)⟩
  have hfU : ∀ y ∈ f, y ∉ Γ.U := fun y hy => (hfQ hy).2
  have hfD₂ : ∀ y ∈ f, y ∉ D₂ := by
    intro y hy hyD
    rcases (hfQ hy).1 with h | h
    · exact h (Or.inr hyD)
    · exact hOpsub h (Or.inr hyD)
  obtain ⟨z₁, hz₁Op, hz₁⟩ := mem_closure_iff.mp
    (hD₁.subset_closure_discInt (discBd_subset _ hpb)) Op hOpo hpOp
  have hfint : (f ∩ discInt D₁).Nonempty := ⟨z₁, hOpf hz₁Op, hz₁⟩
  refine ⟨f, hfc, disjoint_left.mpr fun y hy h => ?_, hfint, ?_⟩
  · rcases h with h | h
    · exact hfU y hy h
    · exact hfD₂ y hy h
  by_contra hno
  push Not at hno
  -- The loops in the closure of `f`.
  set 𝓛 : Set (Set T) := {e | e ∈ Γ.E ∧ e ⊆ closure f ∧ Disjoint e (D₁ ∪ D₂)} with h𝓛def
  have h𝓛 : 𝓛.Finite := Γ.finite_edges.subset fun e he => he.1
  have hends : ∀ e ∈ 𝓛, closure e ∩ Γ.V ⊆ discBd D₁ := by
    rintro e ⟨-, hef, heD⟩ v ⟨hvcl, hvV⟩
    have hvf : v ∈ closure f := closure_minimal hef isClosed_closure hvcl
    have hvD₁ : v ∈ D₁ := by
      by_contra h
      exact hno v hvV h hvf
    by_contra hb
    obtain ⟨w, hw, hwe⟩ := mem_closure_iff.mp hvcl _ (hD₁.isOpen_discInt hman) ⟨hvD₁, hb⟩
    exact disjoint_left.mp heD hwe (Or.inl hw.1)
  have hDe : ∀ e ∈ 𝓛, ∃ De : Set T, IsClosedDisc De ∧ discBd De = closure e ∧
      De ∩ (D₁ ∪ D₂) ⊆ closure e ∩ Γ.V := fun e he =>
    exists_loopDisc hT hsph Γ hD₁ hD₂ hDD hUD hpush he.1 he.2.2 (hends e he)
  choose! De hDe using hDe
  set N : Set T := f ∪ ⋃ e ∈ 𝓛, (De e \ (closure e ∩ Γ.V)) with hNdef
  have hfN : f ⊆ N := subset_union_left
  have hDeN : ∀ e ∈ 𝓛, De e \ (closure e ∩ Γ.V) ⊆ N := fun e he y hy =>
    Or.inr (mem_iUnion₂.mpr ⟨e, he, hy⟩)
  have hfDe : ∀ e ∈ 𝓛, Disjoint f (De e) := by
    intro e he
    obtain ⟨hDd, hbD, -⟩ := hDe e he
    rcases hDd.side hman hfc (disjoint_left.mpr fun y hy hyb =>
        hfU y hy (Γ.closure_subset_U he.1 (hbD ▸ hyb))) with h | h
    · exfalso
      obtain ⟨z, hzf, hzi⟩ := hfint
      have := (hDe e he).2.2 ⟨(h hzf).1, Or.inl hzi.1⟩
      exact hfU z hzf (Γ.V_subset_U this.2)
    · exact h
  -- `N` is open at its points in `Ωs`.
  have hopen : ∀ y ∈ N, y ∈ Ωs → y ∈ interior N := by
    intro y hy hyΩ
    rcases hy with hy | hy
    · exact interior_maximal hfN hfo hy
    obtain ⟨e, he, hy⟩ := mem_iUnion₂.mp hy
    obtain ⟨hDd, hbD, hDD'⟩ := hDe e he
    by_cases hyb : y ∈ discBd (De e)
    · have hye : y ∈ e := by
        rw [← Γ.closure_diff_V he.1]
        exact ⟨hbD ▸ hyb, fun h => hy.2 ⟨hbD ▸ hyb, h⟩⟩
      obtain ⟨W, A₁, A₂, -, -, hW, hyW, hWU, hsub, hA₁, hA₂, hU₁', hU₂', -, -, -, -, -, -, -, -,
        hZ₁, hZ₂⟩ := GM11.exists_edge_sides_off hT Γ he.1 hye hZc
          (fun h => disjoint_left.mp he.2.2 hye h)
      refine mem_interior.mpr ⟨W, fun z hz => ?_, hW, hyW⟩
      -- A point of the inside of `De` near `y`, and a point of `f` near `y`.
      obtain ⟨w, hwW, hwi⟩ := mem_closure_iff.mp
        (hDd.subset_closure_discInt (discBd_subset _ hyb)) W hW hyW
      have hwU : w ∉ Γ.U := fun h => hwi.2 (hbD ▸ subset_closure (hWU ⟨hwW, h⟩))
      obtain ⟨w', hw'W, hw'f⟩ := mem_closure_iff.mp (he.2.1 hye) W hW hyW
      have hw'U : w' ∉ Γ.U := hfU w' hw'f
      have hgood : ∀ A : Set T, IsPreconnected A → Disjoint A Γ.U → Disjoint A (D₁ ∪ D₂) →
          (w ∈ A → A ⊆ N) ∧ (w' ∈ A → A ⊆ N) ∧ ¬ (w ∈ A ∧ w' ∈ A) := by
        intro A hA hAU hAZ
        have hAs := hDd.side hman hA (disjoint_left.mpr fun a ha hab =>
          disjoint_left.mp hAU ha (Γ.closure_subset_U he.1 (hbD ▸ hab)))
        have hAQ : A ⊆ Q := fun a ha =>
          hQ a (disjoint_left.mp hAZ ha) (disjoint_left.mp hAU ha)
        refine ⟨fun hwA => ?_, fun hw'A => ?_, fun ⟨hwA, hw'A⟩ => ?_⟩
        · rcases hAs with h | h
          · exact fun a ha => hDeN e he ⟨(h ha).1, fun h' => (h ha).2 (hbD ▸ h'.1)⟩
          · exact absurd hwi.1 (disjoint_left.mp h hwA)
        · have hAf : A ⊆ f := by
            rw [hfdef, connectedComponentIn_eq hw'f]
            exact hA.subset_connectedComponentIn hw'A hAQ
          exact hAf.trans hfN
        · rcases hAs with h | h
          · exact disjoint_left.mp (hfDe e he) hw'f (h hw'A).1
          · exact disjoint_left.mp h hwA hwi.1
      obtain ⟨g₁w, g₁w', g₁n⟩ := hgood A₁ hA₁ hU₁' hZ₁
      obtain ⟨g₂w, g₂w', g₂n⟩ := hgood A₂ hA₂ hU₂' hZ₂
      by_cases hzU : z ∈ Γ.U
      · have hze : z ∈ e := hWU ⟨hz, hzU⟩
        exact hDeN e he ⟨discBd_subset _ (hbD ▸ subset_closure hze),
          fun h => (he.1.2.1 hze).2 h.2⟩
      · have hw12 : w ∈ A₁ ∪ A₂ := hsub ⟨hwW, hwU⟩
        have hw'12 : w' ∈ A₁ ∪ A₂ := hsub ⟨hw'W, hw'U⟩
        rcases hsub ⟨hz, hzU⟩ with hzA | hzA
        · rcases hw12 with h | h
          · exact g₁w h hzA
          · rcases hw'12 with h' | h'
            · exact g₁w' h' hzA
            · exact absurd ⟨h, h'⟩ g₂n
        · rcases hw12 with h | h
          · rcases hw'12 with h' | h'
            · exact absurd ⟨h, h'⟩ g₁n
            · exact g₂w' h' hzA
          · exact g₂w h hzA
    · refine mem_interior.mpr ⟨discInt (De e), fun z hz => hDeN e he ⟨hz.1,
        fun h => hz.2 (hbD ▸ h.1)⟩, hDd.isOpen_discInt hman, ⟨hy.1, hyb⟩⟩
  -- `N` is closed in `Ωs`.
  have hclN : closure N ⊆ closure f ∪ ⋃ e ∈ 𝓛, De e := by
    rw [hNdef, closure_union, h𝓛.closure_biUnion]
    refine union_subset_union_right _ (iUnion₂_mono fun e he => ?_)
    exact closure_minimal sdiff_subset (hDe e he).1.isClosed
  have hclosed : ∀ y ∈ closure N, y ∈ Ωs → y ∈ N := by
    intro y hy hyΩ
    have hyV : y ∈ Γ.V → y ∉ D₁ := by
      intro hyV hyD
      rcases hyΩ with h | h
      · exact h (Or.inl hyD)
      · exact hOpsub h (Or.inl (Γ.V_subset_U hyV))
    rcases hclN hy with hy | hy
    · by_cases hyQ : y ∈ Q
      · exact hfN (mem_of_mem_closure_connectedComponentIn hQo hy hyQ)
      · have hyU : y ∈ Γ.U := by
          by_contra h
          exact hyQ ⟨hyΩ, h⟩
        have hyZ : y ∉ D₁ ∪ D₂ := by
          rcases hyΩ with h | h
          · exact h
          · exact absurd (Or.inl hyU) (hOpsub h)
        by_cases hyV' : y ∈ Γ.V
        · exact absurd hy (hno y hyV' fun h => hyZ (Or.inl h))
        · obtain ⟨e, he, hye⟩ := Γ.exists_edge_of_mem hyU hyV'
          have heV : ∀ z ∈ e, z ∉ Γ.V := fun z hz => (he.2.1 hz).2
          have heU : e ⊆ Γ.U := fun z hz => (he.2.1 hz).1
          have heD₁ : Disjoint e D₁ := by
            rcases hD₁.side hman he.2.2.1.isConnected.isPreconnected
                (disjoint_left.mpr fun z hz hzb => heV z hz (hU₁ ⟨heU hz, hzb⟩)) with h | h
            · exact absurd (h hye).1 fun h' => hyZ (Or.inl h')
            · exact h
          have heD : Disjoint e (D₁ ∪ D₂) := by
            refine disjoint_left.mpr fun z hz h => ?_
            rcases h with h | h
            · exact disjoint_left.mp heD₁ hz h
            · by_cases hzb : z ∈ discBd D₂
              · exact heV z hz (hU₂ ⟨heU hz, hzb⟩)
              · exact disjoint_left.mp hUD (heU hz) ⟨h, hzb⟩
          have hef : e ⊆ closure f :=
            edge_subset_closure_of_component hT Γ hZc hQ hQU he heD ⟨y, hye, hy⟩
          exact hDeN e ⟨he, hef, heD⟩ ⟨discBd_subset _ ((hDe e ⟨he, hef, heD⟩).2.1 ▸
            subset_closure hye), fun h => heV y hye h.2⟩
    · obtain ⟨e, he, hy⟩ := mem_iUnion₂.mp hy
      refine hDeN e he ⟨hy, fun h => ?_⟩
      have hb := hends e he h
      rcases hyΩ with h' | h'
      · exact h' (Or.inl (discBd_subset _ hb))
      · exact hOpsub h' (Or.inl (Γ.V_subset_U h.2))
  -- `N` holds `Ω ∪ O_p`.
  obtain ⟨z, hzOp, hzΩ⟩ := mem_closure_iff.mp hpcl Op hOpo hpOp
  have hC : IsPreconnected (Ω ∪ Op) := hΩc.union z hzΩ hzOp hOpc
  have hCN : Ω ∪ Op ⊆ interior N := by
    refine hC.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl
      (disjoint_left.mpr fun y hy hy' => hy' (subset_closure (interior_subset hy)))
      (fun y hy => ?_) ⟨p, Or.inr hpOp, interior_maximal hfN hfo (hOpf hpOp)⟩
    have hyΩ : y ∈ Ωs := by
      rcases hy with h | h
      · exact Or.inl (hΩsub h)
      · exact Or.inr h
    by_cases hyN : y ∈ closure N
    · exact Or.inl (hopen y (hclosed y hyN hyΩ) hyΩ)
    · exact Or.inr hyN
  have hxN : x ∈ closure N :=
    closure_mono ((subset_union_left.trans hCN).trans interior_subset) hxcl
  rcases hclN hxN with h | h
  · exact hno x hxV hxD₁ h
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp h
    have := (hDe e he).2.2 ⟨hxe, Or.inr (discBd_subset _ hxD₂)⟩
    exact hxD₁ (discBd_subset _ (hends e he this))

end GraphMinor.GM08
