module

public import GraphMinor.GM11.Corners
import GraphMinor.GM11.RadialCorners
import GraphMinor.GM11.RadialChord
import GraphMinor.GM11.SphereRegion

/-!
# Distinct corners at a vertex that does not separate the drawing

For the boundary argument of VI (5.1), page 129, deleting an initial
vertex from the drawing with cuffs leaves a connected set. In a
sphere, two corners of the same region would give a circle through
that vertex and otherwise in the region. One of its discs misses
the punctured drawing. A small half-disc on that side would then
join the two distinct local sectors without crossing the drawing,
which their sector boundaries forbid.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

universe u

/-- In a sphere, corners at a vertex of a drawing belong to distinct
regions when removing that vertex leaves a preconnected point set.
This is the local planar separation step used in VI (5.1). -/
theorem corners_injective_of_punctured_drawing_connected
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S) {Γ : Drawing S}
    {γ : Set S → I → S} {c : S} (hc : c ∈ Γ.V)
    {next : halfEdges Γ γ c → halfEdges Γ γ c}
    {ρ P Q : halfEdges Γ γ c → Set S} {W : Set S}
    {τ : halfEdges Γ γ c → I}
    (hsec : IsSectors Γ γ c next ρ P W Q τ)
    (hpun : IsPreconnected (Γ.U \ {c})) : Function.Injective ρ := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  intro k k' hρ
  by_contra hkk
  have hcor := IsSectors.corners hsec
  have hpR : ρ k ∈ Γ.R := hcor.region k
  have hcp : c ∉ ρ k := fun h => region_subset hpR h (Γ.V_subset_U hc)
  have hppath : IsPathConnected (ρ k) := isPathConnected_of_isOpen hS
    (region_isOpen hpR) (region_isPreconnected hpR) (region_nonempty hpR)
  obtain ⟨g₁, hg₁, hi₁, h₁0, h₁⟩ := exists_path_into_disc (IsSectors.disc hsec k)
    (IsSectors.bd hsec k) (IsSectors.isOpen hsec) (IsSectors.mem hsec)
  obtain ⟨g₂, hg₂, hi₂, h₂0, h₂⟩ := exists_path_into_disc (IsSectors.disc hsec k')
    (IsSectors.bd hsec k') (IsSectors.isOpen hsec) (IsSectors.mem hsec)
  have hg₁p : ∀ t, 0 < t → g₁ t ∈ ρ k := fun t ht => by
    obtain ⟨a, b, d⟩ := h₁ t ht
    exact IsSectors.sub hsec k (IsSectors.inside hsec k ⟨⟨a, b⟩, d⟩)
  have hg₂p : ∀ t, 0 < t → g₂ t ∈ ρ k := fun t ht => by
    obtain ⟨a, b, d⟩ := h₂ t ht
    rw [hρ]
    exact IsSectors.sub hsec k' (IsSectors.inside hsec k' ⟨⟨a, b⟩, d⟩)
  obtain ⟨e, he, hei, he0, he1, hep, O, hO, hcO, hOr⟩ :=
    exists_chord_to_point hppath hcp (hg₂p 1 one_pos) hg₁ h₁0 hg₁p
  -- The first time after `0` at which `e` meets `g₂`.
  have hsame : ∀ t, t ≠ 0 → e t ∈ O → e t ∉ range g₂ := by
    rintro t ht htO ⟨b, hb⟩
    obtain ⟨a, ha⟩ := hOr t htO
    have hne : e t ≠ c := fun h => hcp (h ▸ hep t ht)
    have ha0 : 0 < a := unitInterval.pos_iff_ne_zero.mpr fun h => hne (by rw [← ha, h, h₁0])
    have hb0 : 0 < b := unitInterval.pos_iff_ne_zero.mpr fun h => hne (by rw [← hb, h, h₂0])
    have hmem : e t ∈ Q k ∩ Q k' := ⟨ha ▸ (h₁ a ha0).2.1, hb ▸ (h₂ b hb0).2.1⟩
    exact region_subset hpR (hep t ht) (IsSectors.inter hsec k k' hkk hmem)
  obtain ⟨δ, hδ, hδa, hδO⟩ := exists_pos_le he hO (he0 ▸ hcO) (a := 1) one_pos
  let Z : Set I := Icc δ 1 ∩ e ⁻¹' range g₂
  have hZc : IsCompact Z := isCompact_Icc.inter_right
    ((isCompact_range hg₂).isClosed.preimage he)
  have hZne : Z.Nonempty := ⟨1, ⟨hδa, le_rfl⟩, ⟨1, he1.symm⟩⟩
  obtain ⟨t₀, ⟨ht₀I, s₀, hs₀⟩, ht₀min⟩ := hZc.exists_isLeast hZne
  have ht₀ : 0 < t₀ := hδ.trans_le ht₀I.1
  have hne₀ : e t₀ ≠ c := fun h => ht₀.ne' (hei (h.trans he0.symm))
  have hs₀0 : 0 < s₀ := unitInterval.pos_iff_ne_zero.mpr fun h => hne₀ (by rw [← hs₀, h, h₂0])
  have hl₁ : IsLineWithEnds (e '' Icc 0 t₀) c (e t₀) := he0 ▸ isLine_piece he hei ht₀
  have hl₂ : IsLineWithEnds (g₂ '' Icc 0 s₀) c (e t₀) := by
    have := isLine_piece hg₂ hi₂ hs₀0
    rwa [h₂0, hs₀] at this
  have hmeet : e '' Icc 0 t₀ ∩ g₂ '' Icc 0 s₀ ⊆ {c, e t₀} := by
    rintro y ⟨⟨a, ha, rfl⟩, b, -, hb⟩
    by_cases ha0 : a = 0
    · exact Or.inl (by rw [ha0, he0])
    · refine Or.inr ?_
      have hle : t₀ ≤ a := by
        by_cases hδa' : δ ≤ a
        · exact ht₀min ⟨⟨hδa', unitInterval.le_one _⟩, ⟨b, hb⟩⟩
        · have hal : a ≤ δ := (not_le.mp hδa').le
          exact (hsame a ha0 (hδO a hal) ⟨b, hb⟩).elim
      have : a = t₀ := le_antisymm ha.2 hle
      show e a = e t₀
      rw [this]
  have hJ : IsOArc (e '' Icc 0 t₀ ∪ g₂ '' Icc 0 s₀) := isOArc_union hl₁ hl₂ hmeet
  have hJp : ∀ y ∈ e '' Icc 0 t₀ ∪ g₂ '' Icc 0 s₀, y = c ∨ y ∈ ρ k := by
    rintro _ (⟨a, -, rfl⟩ | ⟨a, -, rfl⟩)
    · by_cases ha : a = 0
      · exact Or.inl (by rw [ha, he0])
      · exact Or.inr (hep a ha)
    · by_cases ha : a = 0
      · exact Or.inl (by rw [ha, h₂0])
      · exact Or.inr (hg₂p a (unitInterval.pos_iff_ne_zero.mpr ha))
  have hTF : Disjoint (Γ.U \ {c})
      (e '' Icc 0 t₀ ∪ g₂ '' Icc 0 s₀) := by
    apply disjoint_left.mpr
    intro y hy hyF
    rcases hJp y hyF with he | he
    · exact hy.2 he
    · exact region_subset hpR he hy.1
  obtain ⟨Δ, hΔ, hb, hmiss⟩ := exists_disc_missing hS hsph hJ hpun hTF
  have hcb : c ∈ discBd Δ := hb ▸ Or.inl ⟨0, ⟨le_rfl, ht₀.le⟩, he0⟩
  have hfree : Disjoint (Δ \ discBd Δ) Γ.U := by
    apply disjoint_left.mpr
    intro y hy hyU
    by_cases hyc : y = c
    · exact hy.2 (hyc.symm ▸ hcb)
    · exact disjoint_left.mp hmiss hy.1 ⟨hyU, hyc⟩
  obtain ⟨A, W₀, hW₀, hcW₀, hAc, hAΔ, hAb, hAX, -, hclA⟩ :=
    exists_half_nbhd hΔ (IsSectors.isOpen hsec).isClosed_compl hcb
      (fun h' => h' (IsSectors.mem hsec))
  have hAW : ∀ y ∈ A, y ∈ W := fun y hy => by
    by_contra hn
    exact disjoint_left.mp hAX hy hn
  have hAU : ∀ y ∈ A, y ∉ Γ.U := fun y hy hyU =>
    disjoint_left.mp hfree ⟨hAΔ hy, disjoint_left.mp hAb hy⟩ hyU
  -- A connected set off `H` near `c`, with a point of a sector interior in its closure, lies in the
  -- closed disc of that sector.
  have hinQ : ∀ j, ∀ z, z ∈ closure A → z ∈ Q j → z ∉ discBd (Q j) → A ⊆ Q j := by
    intro j z hzA hzQ hzb
    have hQd := IsSectors.disc hsec j
    have hAfr : Disjoint A (frontier (Q j)) := by
      rw [IsClosedDisc.frontier_eq_discBd hS hQd]
      exact disjoint_left.mpr fun y hy hyb => hAU y hy (IsSectors.bdU hsec j ⟨hAW y hy, hyb⟩)
    have hzint : z ∈ interior (Q j) := by
      have hnf : z ∉ frontier (Q j) := by
        rwa [IsClosedDisc.frontier_eq_discBd hS hQd]
      by_contra hni
      exact hnf ⟨subset_closure hzQ, hni⟩
    rcases subset_or_disjoint_of_frontier hQd.isClosed hAc hAfr with h' | h'
    · exact h'
    · obtain ⟨y, hyI, hyA⟩ := mem_closure_iff.mp hzA _ isOpen_interior hzint
      exact (disjoint_left.mp h' hyA (interior_subset hyI)).elim
  obtain ⟨t, ht, htt₀, htN⟩ := exists_pos_le he (hW₀.inter hO) (by rw [he0]; exact ⟨hcW₀, hcO⟩) ht₀
  obtain ⟨s, hs, hss₀, hsN⟩ := exists_pos_le hg₂ hW₀ (by rw [h₂0]; exact hcW₀) hs₀0
  have hzt : e t ∈ closure A := hclA ⟨(htN t le_rfl).1, hb ▸ Or.inl ⟨t, ⟨ht.le, htt₀⟩, rfl⟩⟩
  have hzs : g₂ s ∈ closure A := hclA ⟨hsN s le_rfl, hb ▸ Or.inr ⟨s, ⟨hs.le, hss₀⟩, rfl⟩⟩
  obtain ⟨a, ha⟩ := hOr t (htN t le_rfl).2
  have ha0 : 0 < a := unitInterval.pos_iff_ne_zero.mpr fun h =>
    ht.ne' (hei ((ha.symm.trans (by rw [h, h₁0])).trans he0.symm))
  have hA₁ : A ⊆ Q k := hinQ k _ hzt (ha ▸ (h₁ a ha0).2.1) (ha ▸ (h₁ a ha0).2.2)
  have hA₂ : A ⊆ Q k' := hinQ k' _ hzs (h₂ s hs).2.1 (h₂ s hs).2.2
  obtain ⟨y, -, hyA⟩ := mem_closure_iff.mp hzs _ isOpen_univ (mem_univ _)
  exact hAU y hyA (IsSectors.inter hsec k k' hkk ⟨hA₁ hyA, hA₂ hyA⟩)

/-- When distinct corners have distinct regions, the half-edges
incident with one corner region are exactly its two bounding ones. -/
theorem incident_halfEdges_eq_corner_pair
    {S : Type u} [TopologicalSpace S] {Γ : Drawing S}
    {γ : Set S → I → S} {c : S}
    {next : halfEdges Γ γ c → halfEdges Γ γ c}
    {ρ : halfEdges Γ γ c → Set S}
    (hcor : IsCorners Γ γ c next ρ) (hinj : Function.Injective ρ)
    (k : halfEdges Γ γ c) :
    {j : halfEdges Γ γ c | j.1.1 ⊆ closure (ρ k)} = {k, next k} := by
  have : Finite (halfEdges Γ γ c) := (finite_halfEdges Γ γ c).to_subtype
  have hsurj : Function.Surjective next := Finite.surjective_of_injective hcor.inj
  ext j
  constructor
  · intro hj
    obtain ⟨a, ha⟩ := hsurj j
    have hja : (next a).1.1 ⊆ closure (ρ k) := by rwa [ha]
    rcases hcor.sides a (ρ k) (hcor.region k) hja with he | he
    · have hak : a = k := hinj he.symm
      subst a
      exact Or.inr (mem_singleton_iff.mpr ha.symm)
    · have hjk : j = k := hinj (by rw [ha] at he; exact he.symm)
      exact Or.inl hjk
  · intro hj
    rcases mem_insert_iff.mp hj with hj | hj
    · subst j
      obtain ⟨a, ha⟩ := hsurj k
      have hh := hcor.right a
      rwa [ha] at hh
    · have hj' := mem_singleton_iff.mp hj
      subst j
      exact hcor.left k

end GraphMinor.GM06
