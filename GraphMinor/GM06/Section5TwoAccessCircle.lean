module

public import GraphMinor.Surface.CrossCut
import GraphMinor.GM11.RadialChord
import GraphMinor.GM11.RadialCorners

/-!
# A circle following two accesses to an attachment

The corner argument in VI (5.5), page 130, joins two disjoint
access curves through their common region. Start an arc along the
first access and stop it at its first meeting with the second.
The two resulting line pieces form a circle. Keep their local
traces so that a half-disc bounded by this circle sees both accesses.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- Two access curves disjoint away from their common initial
point yield a circle in the region with that point added, retaining
positive initial pieces of both accesses. -/
theorem exists_circle_following_two_accesses
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {r : Set S} (hr : IsPathConnected r) {s : S} (hs : s ∉ r)
    (g₁ g₂ : C(I, S)) (hg₂ : Function.Injective g₂)
    (h₁0 : g₁ 0 = s) (h₂0 : g₂ 0 = s)
    (h₁ : ∀ t, 0 < t → g₁ t ∈ r) (h₂ : ∀ t, 0 < t → g₂ t ∈ r)
    (hdis : ∀ a b, g₁ a = g₂ b → g₁ a = s) :
    ∃ (F : Set S) (e : C(I, S)) (t₀ s₀ : I) (O : Set S),
      IsOArc F ∧ F ⊆ r ∪ {s} ∧ 0 < t₀ ∧ 0 < s₀ ∧
      e 0 = s ∧ (∀ t, 0 < t → e t ∈ r) ∧
      e '' Icc 0 t₀ ⊆ F ∧ g₂ '' Icc 0 s₀ ⊆ F ∧
      IsOpen O ∧ s ∈ O ∧ ∀ t, e t ∈ O → e t ∈ range g₁ := by
  obtain ⟨e, he, hei, he0, he1, hep, O, hO, hsO, hOr⟩ :=
    exists_chord_to_point hr hs (h₂ 1 one_pos) g₁.continuous h₁0 h₁
  have hsame : ∀ t, t ≠ 0 → e t ∈ O → e t ∉ range g₂ := by
    rintro t ht htO ⟨b, hb⟩
    obtain ⟨a, ha⟩ := hOr t htO
    have heq : e t = s := ha ▸ hdis a b (ha.trans hb.symm)
    exact ht (hei (heq.trans he0.symm))
  obtain ⟨δ, hδ, hδa, hδO⟩ := exists_pos_le he hO (he0 ▸ hsO) (a := 1) one_pos
  let Z : Set I := Icc δ 1 ∩ e ⁻¹' range g₂
  have hZc : IsCompact Z := isCompact_Icc.inter_right
    ((isCompact_range g₂.continuous).isClosed.preimage he)
  have hZne : Z.Nonempty := ⟨1, ⟨hδa, le_rfl⟩, ⟨1, he1.symm⟩⟩
  obtain ⟨t₀, ⟨ht₀I, s₀, hs₀⟩, ht₀min⟩ := hZc.exists_isLeast hZne
  have ht₀ : 0 < t₀ := hδ.trans_le ht₀I.1
  have hne₀ : e t₀ ≠ s := fun h => ht₀.ne' (hei (h.trans he0.symm))
  have hs₀0 : 0 < s₀ := pos_iff_ne_zero.mpr fun h => hne₀ (by rw [← hs₀, h, h₂0])
  have hl₁ : IsLineWithEnds (e '' Icc 0 t₀) s (e t₀) := he0 ▸ isLine_piece he hei ht₀
  have hl₂ : IsLineWithEnds (g₂ '' Icc 0 s₀) s (e t₀) := by
    have hh := isLine_piece g₂.continuous hg₂ hs₀0
    rwa [h₂0, hs₀] at hh
  have hmeet : e '' Icc 0 t₀ ∩ g₂ '' Icc 0 s₀ ⊆ {s, e t₀} := by
    rintro y ⟨⟨a, ha, rfl⟩, b, -, hb⟩
    by_cases ha0 : a = 0
    · exact Or.inl (by rw [ha0, he0])
    · refine Or.inr ?_
      have hle : t₀ ≤ a := by
        by_cases hδa' : δ ≤ a
        · exact ht₀min ⟨⟨hδa', le_top⟩, ⟨b, hb⟩⟩
        · have hal : a ≤ δ := (not_le.mp hδa').le
          exact (hsame a ha0 (hδO a hal) ⟨b, hb⟩).elim
      have heq : a = t₀ := le_antisymm ha.2 hle
      exact mem_singleton_iff.mpr (congrArg e heq)
  let F := e '' Icc 0 t₀ ∪ g₂ '' Icc 0 s₀
  have hF : IsOArc F := isOArc_union hl₁ hl₂ hmeet
  have hFr : F ⊆ r ∪ {s} := by
    rintro y (⟨t, _, rfl⟩ | ⟨t, _, rfl⟩)
    · by_cases ht : t = 0
      · exact Or.inr (by rw [ht, he0]; rfl)
      · exact Or.inl (hep t ht)
    · by_cases ht : t = 0
      · exact Or.inr (by rw [ht, h₂0]; rfl)
      · exact Or.inl (h₂ t (pos_iff_ne_zero.mpr ht))
  exact ⟨F, ⟨e, he⟩, t₀, s₀, O, hF, hFr, ht₀, hs₀0, he0,
    fun t ht => hep t ht.ne', subset_union_left, subset_union_right, hO, hsO, hOr⟩

end GraphMinor.GM06
