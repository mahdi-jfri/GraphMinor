module

public import GraphMinor.Surface.ArcErase
public import GraphMinor.Surface.Defs
import GraphMinor.Surface.CutLift

/-!
# Taming normal rings while keeping their points in the old rings

The foundation step of VIII (9.1), page 269, uses minimum-ring uniqueness.
To handle rings with infinitely many crossings, we need a finite-crossing
replacement that stays normal to the drawing. This file strengthens the
arc erasure construction of `Surface.exists_tame_pair` by recording that
each new arc stays in its old arc together with the fixed finite arc family.
Normality is then preserved whenever these sets are normal.
-/

public section

namespace GraphMinor.GM08

open Set Topology Metric Surface

local notation "𝕀" => unitInterval

universe u

/-- Two arcs can be made to meet a finite arc family in finitely many pieces,
while each replacement stays in its old arc together with that family.
The construction cuts the fixed arcs into small pieces and erases loops,
as in `Surface.exists_tame_pair`. The range inclusions preserve normality
when this construction is used for rings in VIII (9.1). -/
theorem exists_tame_pair_in_union {Y : Type u} [MetricSpace Y] (G : List (𝕀 → Y)) (hG : ∀ g ∈ G, IsArcMap g)
    {a b : 𝕀 → Y} (ha : IsArcMap a) (hb : IsArcMap b) (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hm : ∀ s t, a s = b t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hp : ∀ g ∈ G, a 0 ∉ range g) (hq : ∀ g ∈ G, a 1 ∉ range g) {ε : ℝ} (hε : 0 < ε) :
    ∃ a' b' : 𝕀 → Y, IsArcMap a' ∧ IsArcMap b' ∧ a' 0 = a 0 ∧ a' 1 = a 1 ∧ b' 0 = a 0 ∧ b' 1 = a 1 ∧
      (∀ s t, a' s = b' t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) ∧
      range a' ⊆ thickening ε (range a) ∧ range b' ⊆ thickening ε (range b) ∧
      FinConn ((range a' ∪ range b') \ ⋃ g ∈ G, range g) ∧
      range a' ⊆ range a ∪ ⋃ g ∈ G, range g ∧
      range b' ⊆ range b ∪ ⋃ g ∈ G, range g := by
  classical
  set G₀ : Set Y := ⋃ g ∈ G, range g with hG₀
  have hG₀c : IsClosed G₀ := by
    have : IsCompact G₀ := G.finite_toSet.isCompact_biUnion fun g hg =>
      isCompact_range (hG g hg).1
    exact this.isClosed
  have hAc : IsCompact (range a) := isCompact_range ha.1
  have hBc : IsCompact (range b) := isCompact_range hb.1
  have hdisj : Disjoint (range a ∩ G₀) (range b ∩ G₀) := by
    rw [Set.disjoint_left]
    rintro _ ⟨⟨s, rfl⟩, hs⟩ ⟨⟨t, ht⟩, -⟩
    obtain ⟨g, hg, hsg⟩ := mem_iUnion₂.mp hs
    rcases hm s t ht.symm with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hp g hg hsg
    · exact hq g hg hsg
  obtain ⟨δ₀, hδ₀, hthick⟩ := hdisj.exists_thickenings (hAc.inter_right hG₀c)
    (hBc.isClosed.inter hG₀c)
  have hfar : ∀ x ∈ range a ∩ G₀, ∀ y ∈ range b ∩ G₀, δ₀ ≤ dist x y := by
    intro x hx y hy
    by_contra hlt
    refine Set.disjoint_left.mp hthick (self_subset_thickening hδ₀ _ hx) ?_
    exact mem_thickening_iff.mpr ⟨y, hy, not_le.mp hlt⟩
  set δ : ℝ := min ε (δ₀ / 3) with hδdef
  have hδ : 0 < δ := lt_min hε (by positivity)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ3 : δ ≤ δ₀ / 3 := min_le_right _ _
  -- cut `G` into small arcs
  have hcut : ∃ L : List (𝕀 → Y), (∀ g ∈ L, IsArcMap g) ∧ (⋃ g ∈ L, range g) = G₀ ∧
      ∀ g ∈ L, ∀ x ∈ range g, ∀ y ∈ range g, dist x y < δ := by
    clear_value G₀
    subst hG₀
    clear hG₀c hdisj hthick hfar
    induction G with
    | nil =>
      exact ⟨[], by simp, by simp, by simp⟩
    | cons g G ih =>
      obtain ⟨L₁, h1', h2', h3'⟩ := (hG g (.head _)).exists_small hδ
      obtain ⟨L₂, h1'', h2'', h3''⟩ := ih (fun g' hg' => hG g' (.tail _ hg'))
        (fun g' hg' => hp g' (.tail _ hg')) (fun g' hg' => hq g' (.tail _ hg'))
      refine ⟨L₁ ++ L₂, ?_, ?_, ?_⟩
      · intro g' hg'
        rcases List.mem_append.mp hg' with h | h
        · exact h1' g' h
        · exact h1'' g' h
      · ext x
        simp only [mem_iUnion, List.mem_append, exists_prop, List.mem_cons]
        have e1 := Set.ext_iff.mp h2' x
        have e2 := Set.ext_iff.mp h2'' x
        simp only [mem_iUnion, exists_prop] at e1 e2
        constructor
        · rintro ⟨g', hg' | hg', hx⟩
          · exact ⟨g, .inl rfl, e1.mp ⟨g', hg', hx⟩⟩
          · obtain ⟨g'', h5, h6⟩ := e2.mp ⟨g', hg', hx⟩
            exact ⟨g'', .inr h5, h6⟩
        · rintro ⟨g', rfl | hg', hx⟩
          · obtain ⟨g'', h5, h6⟩ := e1.mpr hx
            exact ⟨g'', .inl h5, h6⟩
          · obtain ⟨g'', h5, h6⟩ := e2.mpr ⟨g', hg', hx⟩
            exact ⟨g'', .inr h5, h6⟩
      · intro g' hg'
        rcases List.mem_append.mp hg' with h | h
        · exact h3' g' h
        · exact h3'' g' h
  obtain ⟨L, hL1, hL2, hL3⟩ := hcut
  have hLG : ∀ g ∈ L, range g ⊆ G₀ := fun g hg => by
    rw [← hL2]
    exact subset_biUnion_of_mem (u := fun g : 𝕀 → Y => range g) hg
  let La := L.filter fun g => (range g ∩ range a).Nonempty
  let Lb := L.filter fun g => (range g ∩ range b).Nonempty
  have hLa : ∀ g ∈ La, g ∈ L ∧ (range g ∩ range a).Nonempty := fun g hg => by
    simpa [La] using hg
  have hLb : ∀ g ∈ Lb, g ∈ L ∧ (range g ∩ range b).Nonempty := fun g hg => by
    simpa [Lb] using hg
  have hmissG : ∀ g ∈ L, a 0 ∉ range g ∧ a 1 ∉ range g := fun g hg => by
    constructor
    · intro hx
      obtain ⟨g', h5, h6⟩ := mem_iUnion₂.mp (hLG g hg hx)
      exact hp g' h5 h6
    · intro hx
      obtain ⟨g', h5, h6⟩ := mem_iUnion₂.mp (hLG g hg hx)
      exact hq g' h5 h6
  obtain ⟨a', ha', ha0, ha1, ha2, ha3⟩ := exists_erase La (fun g hg => hL1 g (hLa g hg).1) ha
    (fun g hg => (hmissG g (hLa g hg).1).1) (fun g hg => (hmissG g (hLa g hg).1).2)
  obtain ⟨b', hb', hb0, hb1, hb2, hb3⟩ := exists_erase Lb (fun g hg => hL1 g (hLb g hg).1) hb
    (fun g hg => h0 ▸ (hmissG g (hLb g hg).1).1) (fun g hg => h1 ▸ (hmissG g (hLb g hg).1).2)
  -- a point of the new arc off the old one is near the old one
  have hnear : ∀ {c : 𝕀 → Y} {L' : List (𝕀 → Y)}, (∀ g ∈ L', g ∈ L ∧ (range g ∩ range c).Nonempty) →
      ∀ x ∈ ⋃ g ∈ L', range g, ∃ y ∈ range c ∩ G₀, dist x y < δ := by
    intro c L' hL' x hx
    obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp hx
    obtain ⟨y, hyg, hyc⟩ := (hL' g hg).2
    exact ⟨y, ⟨hyc, hLG g (hL' g hg).1 hyg⟩, hL3 g (hL' g hg).1 x hxg y hyg⟩
  have hsep : ∀ x y, x ∈ range a ∪ ⋃ g ∈ La, range g → y ∈ range b ∪ ⋃ g ∈ Lb, range g → x = y →
      x ∈ range a ∧ x ∈ range b := by
    intro x y hx hy hxy
    subst hxy
    have hxG : ∀ {L' : List (𝕀 → Y)}, (∀ g ∈ L', g ∈ L) → x ∈ (⋃ g ∈ L', range g) → x ∈ G₀ := by
      intro L' h1 h2
      obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h2
      exact hLG g (h1 g hg) hxg
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact ⟨hx, hy⟩
    · exfalso
      obtain ⟨w, hw, hd⟩ := hnear hLb x hy
      have h3 := hfar x ⟨hx, hxG (fun g hg => (hLb g hg).1) hy⟩ w hw
      linarith
    · exfalso
      obtain ⟨w, hw, hd⟩ := hnear hLa x hx
      have h3 := hfar w hw x ⟨hy, hxG (fun g hg => (hLa g hg).1) hx⟩
      rw [dist_comm] at h3
      linarith
    · exfalso
      obtain ⟨w, hw, hd⟩ := hnear hLa x hx
      obtain ⟨w', hw', hd'⟩ := hnear hLb x hy
      have h3 := hfar w hw w' hw'
      have h4 := dist_triangle_left w w' x
      linarith
  have hsdiff : ∀ {c : 𝕀 → Y} {c' : 𝕀 → Y} {L' : List (𝕀 → Y)},
      (∀ g ∈ L, (range g ∩ range c).Nonempty → g ∈ L') → (∀ g ∈ L', g ∈ L) →
      range c' ⊆ range c ∪ ⋃ g ∈ L', range g → range c' \ G₀ = range c' \ ⋃ g ∈ L', range g := by
    intro c c' L' h1 h2 h3
    ext x
    constructor
    · rintro ⟨h4, h5⟩
      refine ⟨h4, fun h6 => h5 ?_⟩
      obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h6
      exact hLG g (h2 g hg) hxg
    · rintro ⟨h4, h5⟩
      refine ⟨h4, fun h6 => ?_⟩
      rw [← hL2] at h6
      obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h6
      rcases h3 h4 with h7 | h7
      · exact h5 (mem_iUnion₂.mpr ⟨g, h1 g hg ⟨x, hxg, h7⟩, hxg⟩)
      · exact h5 h7
  have hthickA : ∀ {c c' : 𝕀 → Y} {L' : List (𝕀 → Y)},
      (∀ g ∈ L', g ∈ L ∧ (range g ∩ range c).Nonempty) → range c' ⊆ range c ∪ ⋃ g ∈ L', range g →
      range c' ⊆ thickening ε (range c) := by
    intro c c' L' h1 h2 x hx
    rcases h2 hx with h3 | h3
    · exact self_subset_thickening hε _ h3
    · obtain ⟨y, hy, hd⟩ := hnear h1 x h3
      exact mem_thickening_iff.mpr ⟨y, hy.1, hd.trans_le hδε⟩
  refine ⟨a', b', ha', hb', ha0, ha1, hb0.trans h0, hb1.trans h1, ?_, hthickA hLa ha2,
    hthickA hLb hb2, ?_, ?_, ?_⟩
  · intro s t he
    obtain ⟨⟨s', hs'⟩, ⟨t', ht'⟩⟩ := hsep _ _ (ha2 ⟨s, rfl⟩) (hb2 ⟨t, rfl⟩) he
    rcases hm s' t' (hs'.trans ht'.symm) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left
      have e1 : a' s = a' 0 := by rw [← hs', ha0]
      have e2 : b' t = b' 0 := by rw [← he, ← hs', hb0, h0]
      exact ⟨ha'.2 e1, hb'.2 e2⟩
    · right
      have e1 : a' s = a' 1 := by rw [← hs', ha1]
      have e2 : b' t = b' 1 := by rw [← he, ← hs', hb1, h1]
      exact ⟨ha'.2 e1, hb'.2 e2⟩
  · have e1 := hsdiff (c := a) (c' := a') (L' := La) (fun g hg h => by simp [La, hg, h])
      (fun g hg => (hLa g hg).1) ha2
    have e2 := hsdiff (c := b) (c' := b') (L' := Lb) (fun g hg h => by simp [Lb, hg, h])
      (fun g hg => (hLb g hg).1) hb2
    rw [union_sdiff_distrib, e1, e2]
    exact ha3.union hb3

  · intro x hx
    rcases ha2 hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp hx
      exact Or.inr (hLG g (hLa g hg).1 hxg)
  · intro x hx
    rcases hb2 hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp hx
      exact Or.inr (hLG g (hLb g hg).1 hxg)

/-- A compact curve has a neighbourhood containing no drawing vertices
other than the vertices already on the curve. -/
theorem exists_thickening_avoiding_new_vertices {Y : Type u} [MetricSpace Y]
    (D : Drawing Y) {F : Set Y} (hF : IsCompact F) :
    ∃ ε : ℝ, 0 < ε ∧ D.V ∩ thickening ε F ⊆ D.V ∩ F := by
  have hbad : IsClosed (D.V \ F) := (D.finite_V.subset sdiff_subset).isClosed
  have hdis : Disjoint F (D.V \ F) := Set.disjoint_left.mpr fun _ hx hy => hy.2 hx
  obtain ⟨ε, hε, hsep⟩ := hdis.exists_thickenings hF hbad
  refine ⟨ε, hε, fun x hx => ⟨hx.1, ?_⟩⟩
  by_contra hxF
  exact Set.disjoint_left.mp hsep hx.2 (self_subset_thickening hε _ ⟨hx.1, hxF⟩)

/-- A normal circle presented as two arcs has a normal finite-crossing
replacement in the union with the fixed normal arc family. The replacement
uses no new drawing vertices. This supplies the normality and size parts
of the ring replacement needed in the foundation step of VIII (9.1). -/
theorem exists_normal_tame_circle {Y : Type u} [MetricSpace Y] (D : Drawing Y)
    (G : List (𝕀 → Y)) (hG : ∀ g ∈ G, IsArcMap g)
    {a b : 𝕀 → Y} (ha : IsArcMap a) (hb : IsArcMap b)
    (h0 : b 0 = a 0) (h1 : b 1 = a 1)
    (hm : ∀ s t, a s = b t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hp : ∀ g ∈ G, a 0 ∉ range g) (hq : ∀ g ∈ G, a 1 ∉ range g)
    (hN : D.IsNormal (range a ∪ range b)) (hNG : D.IsNormal (⋃ g ∈ G, range g)) :
    ∃ F : Set Y, IsOArc F ∧ D.IsNormal F ∧
      D.V ∩ F ⊆ D.V ∩ (range a ∪ range b) ∧
      FinConn (F \ ⋃ g ∈ G, range g) ∧ F ⊆ (range a ∪ range b) ∪ ⋃ g ∈ G, range g := by
  obtain ⟨ε, hε, hvertices⟩ := exists_thickening_avoiding_new_vertices D
    ((isCompact_range ha.1).union (isCompact_range hb.1))
  obtain ⟨a', b', ha', hb', ha0, ha1, hb0, hb1, hm', hnearA, hnearB,
      htame, hsubA, hsubB⟩ := exists_tame_pair_in_union G hG ha hb h0 h1 hm hp hq hε
  have hcircle : IsOArc (range a' ∪ range b') := oArc_of_two_arcs ha' hb'
    (ha0.trans hb0.symm) (ha1.trans hb1.symm) hm'
  have hsub : range a' ∪ range b' ⊆ (range a ∪ range b) ∪ ⋃ g ∈ G, range g := by
    rintro x (hx | hx)
    · rcases hsubA hx with hx | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inr hx
    · rcases hsubB hx with hx | hx
      · exact Or.inl (Or.inr hx)
      · exact Or.inr hx
  have hnear : range a' ∪ range b' ⊆ thickening ε (range a ∪ range b) := union_subset
    (hnearA.trans (thickening_subset_of_subset ε subset_union_left))
    (hnearB.trans (thickening_subset_of_subset ε subset_union_right))
  refine ⟨range a' ∪ range b', hcircle, ?_, ?_, htame, hsub⟩
  · intro x hx
    rcases hsub hx.1 with hxF | hxG
    · exact hN ⟨hxF, hx.2⟩
    · exact hNG ⟨hxG, hx.2⟩
  · intro x hx
    exact hvertices ⟨hx.1, hnear hx.2⟩

end GraphMinor.GM08
