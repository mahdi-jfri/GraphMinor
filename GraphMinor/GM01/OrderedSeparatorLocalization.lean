module

public import GraphMinor.GM01.MinimalSeparators
public import GraphMinor.GM01.PathInteriorAttachments
import Lean.Elab.Tactic.Omega

/-!
# Localizing minimal separators in an ordered block family

The proof of Graph Minors I, (4.3), page 56, uses an essential witness
path through each separator vertex. A vertex in a block cannot lie
beyond the two boundary blocks, since crossing a boundary would give a
second vertex in an endpoint set. A vertex outside the blocks can be
joined along the witness path to an interior block. The subpath end
check and first visited block then put it in that block's attachment
region. The late endpoint set includes the final boundary block, as
required by the correction recorded for (4.2).
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- The ordered-block argument in GM01 (4.3), page 56. This lemma uses
the separator property of each block; the numbered result supplies it
by (4.1). Its late endpoint union includes the right boundary block. -/
theorem minimal_separator_ordered_localization {α β : Type*} {n : ℕ}
    {G : Graph α β} (S : Fin n → Set α)
    (hSG : ∀ i, S i ⊆ V(G)) (hdis : Pairwise (fun i j ↦ Disjoint (S i) (S j)))
    (hsep : ∀ j, GraphSeparates G (S j)
      (⋃ i, ⋃ (_ : i < j), S i) (⋃ i, ⋃ (_ : j < i), S i))
    (l r : Fin n) (hlr : l.val + 2 ≤ r.val) {X : Set α}
    (hX : IsMinimalGraphSeparator G X
      (⋃ i, ⋃ (_ : i ≤ l), S i) (⋃ i, ⋃ (_ : r ≤ i), S i)) :
    X ⊆ S l ∪ (⋃ i, ⋃ (_ : l < i ∧ i < r),
      blockAttachmentRegion G (⋃ j, S j) (S i)) ∪ S r := by
  classical
  let A := ⋃ i, ⋃ (_ : i ≤ l), S i
  let B := ⋃ i, ⋃ (_ : r ≤ i), S i
  let D := ⋃ i, ⋃ (_ : l < i ∧ i < r), S i
  let U := ⋃ i, S i
  have hAU : A ⊆ U := by
    intro y hy
    obtain ⟨i, hi, hy⟩ := Set.mem_iUnion₂.mp hy
    exact Set.mem_iUnion.mpr ⟨i, hy⟩
  have hBU : B ⊆ U := by
    intro y hy
    obtain ⟨i, hi, hy⟩ := Set.mem_iUnion₂.mp hy
    exact Set.mem_iUnion.mpr ⟨i, hy⟩
  have hcover : U ⊆ A ∪ D ∪ B := by
    intro y hy
    obtain ⟨i, hy⟩ := Set.mem_iUnion.mp hy
    by_cases hil : i ≤ l
    · exact Or.inl (Or.inl (Set.mem_iUnion₂.mpr ⟨i, hil, hy⟩))
    by_cases hri : r ≤ i
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, hri, hy⟩)
    exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨i,
      ⟨lt_of_not_ge hil, lt_of_not_ge hri⟩, hy⟩))
  have hD : Disjoint D (A ∪ B) := by
    apply Set.disjoint_left.mpr
    intro y hyD hyAB
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hyD
    rcases hyAB with hyA | hyB
    · obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hyA
      exact Set.disjoint_left.mp (hdis (by intro h; subst j; exact (not_lt_of_ge hj) hi.1)) hyi hyj
    · obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hyB
      exact Set.disjoint_left.mp (hdis (by intro h; subst j; exact (not_lt_of_ge hj) hi.2)) hyi hyj
  intro x hx
  obtain ⟨a, ha, b, hb, P, hP, _, hxP⟩ := hX.exists_witness_path hx
  obtain ⟨ia, hia, haS⟩ := Set.mem_iUnion₂.mp ha
  obtain ⟨ib, hib, hbS⟩ := Set.mem_iUnion₂.mp hb
  have hltr : l < r := by change l.val < r.val; omega
  by_cases hxU : x ∈ U
  · obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxU
    have hlk : l ≤ k := by
      by_contra hnot
      have hkl : k < l := lt_of_not_ge hnot
      have hxa : x = a := mem_singleton_iff.mp
        (hP.2.1 ▸ ⟨hxP, Set.mem_iUnion₂.mpr ⟨k, hkl.le, hxk⟩⟩)
      have haNot : a ∉ S l := by
        intro hal
        exact Set.disjoint_left.mp (hdis hkl.ne) (hxa ▸ hxk) hal
      have hAvoid : Disjoint V(P) (S l) := by
        apply Set.disjoint_left.mpr
        intro y hy hyl
        have hya : y = a := mem_singleton_iff.mp
          (hP.2.1 ▸ ⟨hy, Set.mem_iUnion₂.mpr ⟨l, le_rfl, hyl⟩⟩)
        exact haNot (hya ▸ hyl)
      apply (not_graphSeparates_iff.mpr ?_) (hsep l)
      exact ⟨a, Set.mem_iUnion₂.mpr ⟨k, hkl, hxa ▸ hxk⟩,
         b, Set.mem_iUnion₂.mpr ⟨ib, hltr.trans_le hib, hbS⟩, P, hP.1, hAvoid⟩
    have hkr : k ≤ r := by
      by_contra hnot
      have hrk : r < k := lt_of_not_ge hnot
      have hxb : x = b := mem_singleton_iff.mp
        (hP.2.2 ▸ ⟨hxP, Set.mem_iUnion₂.mpr ⟨k, hrk.le, hxk⟩⟩)
      have hbNot : b ∉ S r := by
        intro hbr
        exact Set.disjoint_left.mp (hdis hrk.ne.symm) (hxb ▸ hxk) hbr
      have hAvoid : Disjoint V(P) (S r) := by
        apply Set.disjoint_left.mpr
        intro y hy hyr
        have hyb : y = b := mem_singleton_iff.mp
          (hP.2.2 ▸ ⟨hy, Set.mem_iUnion₂.mpr ⟨r, le_rfl, hyr⟩⟩)
        exact hbNot (hyb ▸ hyr)
      apply (not_graphSeparates_iff.mpr ?_) (hsep r)
      exact ⟨a, Set.mem_iUnion₂.mpr ⟨ia, lt_of_le_of_lt hia hltr, haS⟩,
         b, Set.mem_iUnion₂.mpr ⟨k, hrk, hxb ▸ hxk⟩, P, hP.1, hAvoid⟩
    by_cases hkl : k = l
    · exact Or.inl (Or.inl (hkl ▸ hxk))
    by_cases hkr' : k = r
    · exact Or.inr (hkr' ▸ hxk)
    exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨k,
      ⟨lt_of_le_of_ne hlk (Ne.symm hkl), lt_of_le_of_ne hkr hkr'⟩,
      subset_blockAttachmentRegion (hSG k) hxk⟩))
  · let m : Fin n := ⟨l.val + 1, by omega⟩
    have hlm : l < m := by change l.val < l.val + 1; omega
    have hmr : m < r := by change l.val + 1 < r.val; omega
    have hMeet : ¬ Disjoint V(P) (S m) := by
      intro hAvoid
      apply (not_graphSeparates_iff.mpr ?_) (hsep m)
      exact ⟨a, Set.mem_iUnion₂.mpr ⟨ia, lt_of_le_of_lt hia hlm, haS⟩,
         b, Set.mem_iUnion₂.mpr ⟨ib, hmr.trans_le hib, hbS⟩,
         P, hP.1, hAvoid⟩
    obtain ⟨u, huP, huS⟩ := Set.not_disjoint_iff.mp hMeet
    have huD : u ∈ D := Set.mem_iUnion₂.mpr ⟨m, ⟨hlm, hmr⟩, huS⟩
    have hxD := mem_blockAttachmentRegion_of_witness_subpath
      hP hxP huP hxU hAU hBU huD hD hcover
    let T := {i : Fin n // l < i ∧ i < r}
    have hDeq : D = ⋃ i : T, S i.val := by
      ext y
      dsimp only [D]
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi, hy⟩
        exact ⟨⟨i, hi⟩, hy⟩
      · rintro ⟨i, hy⟩
        exact ⟨i.val, i.property, hy⟩
    rw [hDeq] at hxD
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (blockAttachmentRegion_iUnion_subset (fun i : T ↦ S i.val) hxD)
    exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨i.val, i.property, hi⟩))

end GraphMinor.GM01
