module

public import GraphMinor.Crossing.BridgeDefs

/-!
# Lemma 3: Candidate endpoint pairs detect every crossing between two bridges (Section 5.1)

This file formalizes Lemma 3 of Section 5.1 of the crossing-extractor note
(`docs/crossing/crossing_extractor.tex`):

> "**Lemma 3** (These candidates detect every crossing between two bridges). Let \(A\) and \(B\)
> be the attachment sets of two distinct bridges. Suppose that \(A\) contains \(a_1,a_2\) and
> \(B\) contains \(b_1,b_2\) such that the pairs \(\{a_1,a_2\}\) and \(\{b_1,b_2\}\) alternate
> around \(D\). Then some candidate of the first bridge alternates with some candidate of the
> second.
>
> *Proof.* There are \(A\)-attachments in both open arcs of \(D\) determined by \(b_1\) and
> \(b_2\). Around \(b_2\), choose the nearest \(A\)-attachment strictly before it and the nearest
> one strictly after it. These two attachments lie in the two different open arcs, so they
> alternate with \(b_1,b_2\). In the cyclic \(A\)-attachment list they are consecutive, unless
> \(b_2\in A\), in which case exactly one attachment, namely \(b_2\), lies between them. Hence they
> form an \(A\)-candidate that alternates with \(b_1,b_2\).
>
> Applying the same argument to \(B\), relative to this \(A\)-candidate, gives a \(B\)-candidate
> that alternates with it."

We also translate Lemma 3 into cycle-index intervals `(l, r, γ)` in `candidatesOfIndices`, showing
that alternating attachment pairs yield two candidates with `l' < l < r' < r` (in one of the two
orders).
-/

@[expose] public section

namespace GraphMinor.Crossing

open SimpleGraph GraphMinor.HP25

variable {V : Type*} {α : Type*} {β : Type*}

/-! ### 1. First and last matching elements in an open arc -/

/-- If `L` contains an element satisfying `p`, it splits at the first such element. -/
theorem exists_first_filter (p : α → Bool) {L : List α} {x : α} (hx : x ∈ L) (hpx : p x = true) :
    ∃ L₁ a L₂, L = L₁ ++ a :: L₂ ∧ p a = true ∧ L₁.filter p = [] := by
  induction L with
  | nil => cases hx
  | cons hd tl ih =>
    by_cases hphd : p hd = true
    · exact ⟨[], hd, tl, rfl, hphd, rfl⟩
    · have hphd_f : p hd = false := Bool.eq_false_iff.mpr hphd
      rcases List.mem_cons.mp hx with rfl | hxtl
      · exact absurd hpx hphd
      · obtain ⟨L₁, a, L₂, htl, hpa, hfilt⟩ := ih hxtl
        refine ⟨hd :: L₁, a, L₂, by simp [htl], hpa, ?_⟩
        simp [hphd_f, hfilt]

/-- If `L` contains an element satisfying `p`, it splits at the last such element. -/
theorem exists_last_filter (p : α → Bool) {L : List α} {x : α} (hx : x ∈ L) (hpx : p x = true) :
    ∃ L₁ a L₂, L = L₁ ++ a :: L₂ ∧ p a = true ∧ L₂.filter p = [] := by
  induction L generalizing x with
  | nil => cases hx
  | cons hd tl ih =>
    by_cases htl_any : ∃ y ∈ tl, p y = true
    · obtain ⟨y, hytl, hpy⟩ := htl_any
      obtain ⟨L₁, a, L₂, htl, hpa, hfilt⟩ := ih hytl hpy
      exact ⟨hd :: L₁, a, L₂, by simp [htl], hpa, hfilt⟩
    · push Not at htl_any
      rcases List.mem_cons.mp hx with rfl | hxtl
      · refine ⟨[], x, tl, rfl, hpx, ?_⟩
        rw [List.filter_eq_nil_iff]
        intro y hy
        exact htl_any y hy
      · exact absurd hpx (htl_any x hxtl)

/-! ### 2. Rotations of filtered lists and cyclic distance-1 / distance-2 pairs -/

/-- Filtering a rotated list is a rotation of the filtered list. -/
theorem filter_rotate_exists_rotate (p : α → Bool) (D : List α) (k : ℕ) :
    ∃ r : ℕ, (D.rotate k).filter p = (D.filter p).rotate r := by
  by_cases hD : D = []
  · subst hD; exact ⟨0, by simp⟩
  have hpos : 0 < D.length := List.length_pos_iff.mpr hD
  set k' := k % D.length
  have hk' : k' ≤ D.length := le_of_lt (Nat.mod_lt _ hpos)
  have hrot : D.rotate k = D.drop k' ++ D.take k' := by
    rw [← List.rotate_mod, List.rotate_eq_drop_append_take hk']
  have hsplit : D = D.take k' ++ D.drop k' := (List.take_append_drop k' D).symm
  set U := (D.take k').filter p
  set W := (D.drop k').filter p
  have hfilterD : D.filter p = U ++ W := by
    conv_lhs => rw [hsplit, List.filter_append]
  refine ⟨U.length, ?_⟩
  rw [hrot, List.filter_append, hfilterD]
  rw [List.rotate_eq_drop_append_take (by simp)]
  simp [U, W]

/-- Two consecutive elements in a rotation of a nodup list `t` form a cyclic distance-1 candidate
of `t`. -/
theorem mem_stepCandidates_one_of_rotate [DecidableEq α] {t : List α} (hnd : t.Nodup)
    {r : ℕ} {X Y : List α} {a b : α} (hrot : t.rotate r = X ++ a :: b :: Y) :
    (a, b) ∈ stepCandidates 1 t := by
  have hlen_rot : (t.rotate r).length = X.length + 2 + Y.length := by
    rw [hrot]; simp; omega
  rw [List.length_rotate] at hlen_rot
  have hpos : 0 < t.length := by omega
  set i := (X.length + r) % t.length
  have hi : i < t.length := Nat.mod_lt _ hpos
  have hX_lt : X.length < (t.rotate r).length := by rw [List.length_rotate]; omega
  have hX1_lt : X.length + 1 < (t.rotate r).length := by rw [List.length_rotate]; omega
  have ha_get : (t.rotate r)[X.length]'hX_lt = a := by
    simp only [hrot]
    rw [List.getElem_append_right (le_refl _)]
    simp
  have hb_get : (t.rotate r)[X.length + 1]'hX1_lt = b := by
    simp only [hrot]
    rw [List.getElem_append_right (by omega)]
    simp
  have ha_t : t[i]'hi = a := by
    rw [← ha_get, List.getElem_rotate]
  have hb_t : t[(i + 1) % t.length]'(Nat.mod_lt _ hpos) = b := by
    have hmod : (X.length + 1 + r) % t.length = (i + 1) % t.length := by
      simp only [i, Nat.mod_add_mod, show X.length + r + 1 = X.length + 1 + r by omega]
    rw [← hb_get, List.getElem_rotate]
    simp only [hmod]
  have hab : a ≠ b := by
    have hnd_rot : (t.rotate r).Nodup := List.nodup_rotate.mpr hnd
    rw [hrot, List.nodup_append, List.nodup_cons] at hnd_rot
    intro heq
    exact hnd_rot.2.1.1 (heq ▸ List.mem_cons_self)
  rw [mem_stepCandidates_iff]
  exact ⟨hpos, i, hi, by rw [ha_t, hb_t]; exact hab, by rw [ha_t, hb_t]⟩

/-- Two elements separated by one element in a rotation of a nodup list `t` form a cyclic
distance-2 candidate of `t`. -/
theorem mem_stepCandidates_two_of_rotate [DecidableEq α] {t : List α} (hnd : t.Nodup)
    {r : ℕ} {X Y : List α} {a m b : α} (hrot : t.rotate r = X ++ a :: m :: b :: Y) :
    (a, b) ∈ stepCandidates 2 t := by
  have hlen_rot : (t.rotate r).length = X.length + 3 + Y.length := by
    rw [hrot]; simp; omega
  rw [List.length_rotate] at hlen_rot
  have hpos : 0 < t.length := by omega
  set i := (X.length + r) % t.length
  have hi : i < t.length := Nat.mod_lt _ hpos
  have hX_lt : X.length < (t.rotate r).length := by rw [List.length_rotate]; omega
  have hX2_lt : X.length + 2 < (t.rotate r).length := by rw [List.length_rotate]; omega
  have ha_get : (t.rotate r)[X.length]'hX_lt = a := by
    simp only [hrot]
    rw [List.getElem_append_right (le_refl _)]
    simp
  have hb_get : (t.rotate r)[X.length + 2]'hX2_lt = b := by
    simp only [hrot]
    rw [List.getElem_append_right (by omega)]
    simp
  have ha_t : t[i]'hi = a := by
    rw [← ha_get, List.getElem_rotate]
  have hb_t : t[(i + 2) % t.length]'(Nat.mod_lt _ hpos) = b := by
    have hmod : (X.length + 2 + r) % t.length = (i + 2) % t.length := by
      simp only [i, Nat.mod_add_mod, show X.length + r + 2 = X.length + 2 + r by omega]
    rw [← hb_get, List.getElem_rotate]
    simp only [hmod]
  have hab : a ≠ b := by
    have hnd_rot : (t.rotate r).Nodup := List.nodup_rotate.mpr hnd
    rw [hrot, List.nodup_append, List.nodup_cons] at hnd_rot
    intro heq
    exact hnd_rot.2.1.1 (List.mem_cons_of_mem _ (heq ▸ List.mem_cons_self))
  rw [mem_stepCandidates_iff]
  exact ⟨hpos, i, hi, by rw [ha_t, hb_t]; exact hab, by rw [ha_t, hb_t]⟩

/-! ### 3. Proof of Lemma 3 (Section 5.1) -/

/-- **Single-bridge step of Lemma 3 (Section 5.1 of the note):**
"There are \(A\)-attachments in both open arcs of \(D\) determined by \(b_1\) and \(b_2\). Around
\(b_2\), choose the nearest \(A\)-attachment strictly before it and the nearest one strictly after
it. These two attachments lie in the two different open arcs, so they alternate with \(b_1,b_2\).
In the cyclic \(A\)-attachment list they are consecutive, unless \(b_2\in A\), in which case
exactly one attachment, namely \(b_2\), lies between them. Hence they form an \(A\)-candidate that
alternates with \(b_1,b_2\)." -/
theorem lemma_3_single_step [DecidableEq V] {D : List V} (hnd : D.Nodup) (pA : V → Bool)
    {a₁ a₂ b₁ b₂ : V} (ha₁ : pA a₁ = true) (ha₂ : pA a₂ = true)
    (halt : Alternate D b₁ b₂ a₁ a₂) :
    ∃ a₁' a₂' : V, (a₁', a₂') ∈ attachmentCandidates (D.filter pA) ∧
      Alternate D b₁ b₂ a₁' a₂' := by
  obtain ⟨k, L₁, L₂, hrot, ha₁_L₁, ha₂_L₂⟩ := halt
  -- Choose the nearest A-attachment strictly before b₂ (last in L₁)
  obtain ⟨L₁₁, a₁', L₁₂, hL₁, ha₁', hL₁₂_nil⟩ := exists_last_filter pA ha₁_L₁ ha₁
  -- Choose the nearest A-attachment strictly after b₂ (first in L₂)
  obtain ⟨L₂₁, a₂', L₂₂, hL₂, ha₂', hL₂₁_nil⟩ := exists_first_filter pA ha₂_L₂ ha₂
  have ha₁'_L₁ : a₁' ∈ L₁ := by rw [hL₁]; simp
  have ha₂'_L₂ : a₂' ∈ L₂ := by rw [hL₂]; simp
  have halt' : Alternate D b₁ b₂ a₁' a₂' := ⟨k, L₁, L₂, hrot, ha₁'_L₁, ha₂'_L₂⟩
  obtain ⟨r, hfilt_rot⟩ := filter_rotate_exists_rotate pA D k
  have hnd_filt : (D.filter pA).Nodup := hnd.filter pA
  refine ⟨a₁', a₂', ?_, halt'⟩
  rw [mem_attachmentCandidates_iff]
  have hrot_exp : D.rotate k =
      (b₁ :: L₁₁) ++ a₁' :: (L₁₂ ++ b₂ :: L₂₁ ++ a₂' :: L₂₂) := by
    rw [hrot, hL₁, hL₂]
    simp
  cases hb₂ : pA b₂
  · left
    have hfilt_eq₁ : (D.filter pA).rotate r =
        (b₁ :: L₁₁).filter pA ++ a₁' :: a₂' :: L₂₂.filter pA := by
      rw [← hfilt_rot, hrot_exp]
      cases hb₁ : pA b₁ <;>
        simp [List.filter_append, ha₁', ha₂', hL₁₂_nil, hL₂₁_nil, hb₁, hb₂]
    exact mem_stepCandidates_one_of_rotate hnd_filt hfilt_eq₁
  · right
    have hfilt_eq₂ : (D.filter pA).rotate r =
        (b₁ :: L₁₁).filter pA ++ a₁' :: b₂ :: a₂' :: L₂₂.filter pA := by
      rw [← hfilt_rot, hrot_exp]
      cases hb₁ : pA b₁ <;>
        simp [List.filter_append, ha₁', ha₂', hL₁₂_nil, hL₂₁_nil, hb₁, hb₂]
    exact mem_stepCandidates_two_of_rotate hnd_filt hfilt_eq₂

/-- **Lemma 3 (Section 5.1 of the note):**
if the attachment sets \(A\) and \(B\) of two distinct bridges contain pairs \(\{a_1,a_2\}\) and
\(\{b_1,b_2\}\) that alternate around \(D\), "then some candidate of the first bridge alternates
with some candidate of the second." -/
theorem lemma_3 [DecidableEq V] {D : List V} (hnd : D.Nodup) (pA pB : V → Bool)
    {a₁ a₂ b₁ b₂ : V} (ha₁ : pA a₁ = true) (ha₂ : pA a₂ = true)
    (hb₁ : pB b₁ = true) (hb₂ : pB b₂ = true)
    (halt : Alternate D a₁ a₂ b₁ b₂) :
    ∃ a₁' a₂' b₁' b₂' : V,
      (a₁', a₂') ∈ attachmentCandidates (D.filter pA) ∧
      (b₁', b₂') ∈ attachmentCandidates (D.filter pB) ∧
      Alternate D a₁' a₂' b₁' b₂' := by
  have halt_ba : Alternate D b₁ b₂ a₂ a₁ := halt.comm
  obtain ⟨a₁', a₂', hcA, halt_ba'⟩ := lemma_3_single_step hnd pA ha₂ ha₁ halt_ba
  have halt_a'b : Alternate D a₁' a₂' b₂ b₁ := halt_ba'.comm
  obtain ⟨b₁', b₂', hcB, halt_a'b'⟩ := lemma_3_single_step hnd pB hb₂ hb₁ halt_a'b
  exact ⟨a₁', a₂', b₁', b₂', hcA, hcB, halt_a'b'⟩

/-! ### 4. Alternating pairs and cycle-index intervals -/

/-- Two pairs `(l₁, r₁)` (with `l₁ < r₁ < D.length`) and `(l₂, r₂)` (with `l₂ < r₂ < D.length`)
satisfy `l₁ < l₂ < r₁ < r₂` or `l₂ < l₁ < r₂ < r₁` if and only if `(D[l₁], D[r₁])` and
`(D[l₂], D[r₂])` alternate on `D`. -/
theorem alternate_getElem_of_lt_lt_lt {D : List V} {l₁ r₁ l₂ r₂ : ℕ}
    (hl₁ : l₁ < l₂) (hl₂ : l₂ < r₁) (hr₁ : r₁ < r₂) (hr₂ : r₂ < D.length) :
    Alternate D D[l₁] D[r₁] D[l₂] D[r₂] := by
  refine ⟨l₁, (D.drop (l₁ + 1)).take (r₁ - l₁ - 1), D.drop (r₁ + 1) ++ D.take l₁, ?_, ?_, ?_⟩
  · have e1 : D.drop l₁ = D[l₁] :: D.drop (l₁ + 1) := List.drop_eq_getElem_cons (by omega)
    have e2 : D.drop (l₁ + 1) = (D.drop (l₁ + 1)).take (r₁ - l₁ - 1) ++ D[r₁] :: D.drop (r₁ + 1) := by
      conv_lhs => rw [← List.take_append_drop (r₁ - l₁ - 1) (D.drop (l₁ + 1))]
      congr 1
      rw [List.drop_drop, List.drop_eq_getElem_cons (by omega)]
      congr 2 <;> omega
    conv_lhs => rw [List.rotate_eq_drop_append_take (by omega), e1, e2]
    simp only [List.cons_append, List.append_assoc]
  · rw [List.mem_iff_getElem]
    exact ⟨l₂ - l₁ - 1, by simp; omega, by simp; congr 1; omega⟩
  · refine List.mem_append_left _ (List.mem_iff_getElem.mpr ⟨r₂ - r₁ - 1, by simp; omega, ?_⟩)
    simp
    congr 1
    omega

/-- In a nodup list `D`, if `Alternate D a b c d`, then their cycle indices `(min, max)` interleave:
either `l₁ < l₂ < r₁ < r₂` or `l₂ < l₁ < r₂ < r₁`. -/
theorem idxOf_interleave_of_alternate [DecidableEq V] {D : List V} (hnd : D.Nodup)
    {a b c d : V} (halt : Alternate D a b c d) :
    let l₁ := min (D.idxOf a) (D.idxOf b)
    let r₁ := max (D.idxOf a) (D.idxOf b)
    let l₂ := min (D.idxOf c) (D.idxOf d)
    let r₂ := max (D.idxOf c) (D.idxOf d)
    (l₁ < l₂ ∧ l₂ < r₁ ∧ r₁ < r₂) ∨ (l₂ < l₁ ∧ l₁ < r₂ ∧ r₂ < r₁) := by
  dsimp only
  have halt₀ := halt
  obtain ⟨k, L₁, L₂, hrot, hc_L₁, hd_L₂⟩ := halt
  have ha_D : a ∈ D := List.mem_rotate.mp (by rw [hrot]; simp)
  have hb_D : b ∈ D := List.mem_rotate.mp (by rw [hrot]; simp)
  have hc_D : c ∈ D := List.mem_rotate.mp (by rw [hrot]; simp [hc_L₁])
  have hd_D : d ∈ D := List.mem_rotate.mp (by rw [hrot]; simp [hd_L₂])
  set ia := D.idxOf a
  set ib := D.idxOf b
  set ic := D.idxOf c
  set id := D.idxOf d
  have hia : ia < D.length := List.idxOf_lt_length_of_mem ha_D
  have hib : ib < D.length := List.idxOf_lt_length_of_mem hb_D
  have hic : ic < D.length := List.idxOf_lt_length_of_mem hc_D
  have hid : id < D.length := List.idxOf_lt_length_of_mem hd_D
  set l₁ := min ia ib
  set r₁ := max ia ib
  set l₂ := min ic id
  set r₂ := max ic id
  have hab_ne : a ≠ b := (halt₀.comm.ne hnd).symm
  have hcd_ne : c ≠ d := halt₀.ne hnd
  have hl₁r₁ : l₁ < r₁ := by
    have : ia ≠ ib := fun h => hab_ne ((List.idxOf_inj ha_D).mp h)
    omega
  have hl₂r₂ : l₂ < r₂ := by
    have : ic ≠ id := fun h => hcd_ne ((List.idxOf_inj hc_D).mp h)
    omega
  have hr₁_lt : r₁ < D.length := by omega
  have hr₂_lt : r₂ < D.length := by omega
  -- Consider the rotation of D starting at `l₁`
  set A_arc := (D.drop (l₁ + 1)).take (r₁ - l₁ - 1)
  set B_arc := D.drop (r₁ + 1) ++ D.take l₁
  have hrot_l₁ : D.rotate l₁ = D[l₁] :: A_arc ++ D[r₁] :: B_arc := by
    have e1 : D.drop l₁ = D[l₁] :: D.drop (l₁ + 1) := List.drop_eq_getElem_cons (by omega)
    have e2 : D.drop (l₁ + 1) = A_arc ++ D[r₁] :: D.drop (r₁ + 1) := by
      dsimp only [A_arc]
      conv_lhs => rw [← List.take_append_drop (r₁ - l₁ - 1) (D.drop (l₁ + 1))]
      congr 1
      rw [List.drop_drop, List.drop_eq_getElem_cons (by omega)]
      congr 2 <;> omega
    conv_lhs => rw [List.rotate_eq_drop_append_take (by omega), e1, e2]
    simp only [B_arc, List.cons_append, List.append_assoc]
  -- Every vertex in A_arc has idxOf strictly between l₁ and r₁
  have hmem_A : ∀ v ∈ A_arc, l₁ < D.idxOf v ∧ D.idxOf v < r₁ := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
    have hj_lt : j < r₁ - l₁ - 1 := by
      simp only [A_arc, List.length_take, List.length_drop, lt_inf_iff] at hj
      exact hj.1
    have hget : A_arc[j] = D[l₁ + 1 + j]'(by omega) := by simp [A_arc]
    rw [hget, hnd.idxOf_getElem]
    omega
  -- Every vertex in B_arc has idxOf < l₁ or r₁ < idxOf
  have hmem_B : ∀ v ∈ B_arc, D.idxOf v < l₁ ∨ r₁ < D.idxOf v := by
    intro v hv
    rcases List.mem_append.mp hv with hv₁ | hv₂
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv₁
      have hj_lt : j < D.length - (r₁ + 1) := by simpa using hj
      have hget : (D.drop (r₁ + 1))[j] = D[r₁ + 1 + j]'(by omega) := by simp
      rw [hget, hnd.idxOf_getElem]
      right; omega
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv₂
      have hj_lt : j < l₁ := by
        simp only [List.length_take, lt_inf_iff] at hj
        exact hj.1
      have hget : (D.take l₁)[j] = D[j]'(by omega) := by simp
      rw [hget, hnd.idxOf_getElem]
      left; omega
  -- Now either `(D[l₁], D[r₁]) = (a, b)` or `(D[l₁], D[r₁]) = (b, a)`
  have halt_l₁r₁ : Alternate D D[l₁] D[r₁] c d ∨ Alternate D D[l₁] D[r₁] d c := by
    rcases le_total ia ib with hle | hle
    · left
      have hl₁_eq : D[l₁] = a := by
        simp only [l₁, Nat.min_eq_left hle, ia, List.getElem_idxOf hia]
      have hr₁_eq : D[r₁] = b := by
        simp only [r₁, Nat.max_eq_right hle, ib, List.getElem_idxOf hib]
      rw [hl₁_eq, hr₁_eq]
      exact halt₀
    · right
      have hl₁_eq : D[l₁] = b := by
        simp only [l₁, Nat.min_eq_right hle, ib, List.getElem_idxOf hib]
      have hr₁_eq : D[r₁] = a := by
        simp only [r₁, Nat.max_eq_left hle, ia, List.getElem_idxOf hia]
      rw [hl₁_eq, hr₁_eq]
      exact halt₀.swap
  have h_one_in_each : (c ∈ A_arc ∧ d ∈ B_arc) ∨ (d ∈ A_arc ∧ c ∈ B_arc) := by
    rcases halt_l₁r₁ with h1 | h2
    · exact Or.inl (h1.mem_of_rotate hnd hrot_l₁)
    · have := h2.mem_of_rotate hnd hrot_l₁
      exact Or.inr ⟨this.1, this.2⟩
  rcases h_one_in_each with ⟨hcA, hdB⟩ | ⟨hdA, hcB⟩
  · have hc_in := hmem_A c hcA
    rcases hmem_B d hdB with hd_lt | hd_gt
    · right; omega
    · left; omega
  · have hd_in := hmem_A d hdA
    rcases hmem_B c hcB with hc_lt | hc_gt
    · right; omega
    · left; omega

/-- Mapping an attachment list by a function injective on its elements commutes with
`stepCandidates`. -/
theorem stepCandidates_map_of_injOn [DecidableEq α] [DecidableEq β] {t : List α} {f : α → β}
    (hinj : ∀ x ∈ t, ∀ y ∈ t, f x = f y → x = y) (d : ℕ) :
    stepCandidates d (t.map f) = (stepCandidates d t).map (fun q => (f q.1, f q.2)) := by
  unfold stepCandidates
  rw [List.map_filterMap]
  refine congrArg₂ List.filterMap ?_ (by simp)
  ext i
  by_cases hpos : 0 < t.length
  · simp only [hpos, ↓reduceDIte, List.length_map, List.getElem_map]
    have h1 : t[i % t.length]'(Nat.mod_lt _ hpos) ∈ t := List.getElem_mem _
    have h2 : t[(i + d) % t.length]'(Nat.mod_lt _ hpos) ∈ t := List.getElem_mem _
    by_cases heq : t[i % t.length]'(Nat.mod_lt _ hpos) = t[(i + d) % t.length]'(Nat.mod_lt _ hpos)
    · simp [heq]
    · have hfne : f (t[i % t.length]'(Nat.mod_lt _ hpos)) ≠
          f (t[(i + d) % t.length]'(Nat.mod_lt _ hpos)) := mt (hinj _ h1 _ h2) heq
      simp [heq, hfne]
  · simp [hpos]

theorem attachmentCandidates_map_of_injOn [DecidableEq α] [DecidableEq β] {t : List α} {f : α → β}
    (hinj : ∀ x ∈ t, ∀ y ∈ t, f x = f y → x = y) :
    attachmentCandidates (t.map f) = (attachmentCandidates t).map (fun q => (f q.1, f q.2)) := by
  unfold attachmentCandidates
  rw [List.map_append, stepCandidates_map_of_injOn hinj 1, stepCandidates_map_of_injOn hinj 2]

/-- Mapping `D.filter p` by `D.idxOf` gives the filtered index range `(List.range D.length).filter`. -/
theorem map_idxOf_filter_eq_filter_range [DecidableEq V] {D : List V} (hnd : D.Nodup)
    (p : V → Bool) :
    (D.filter p).map D.idxOf =
      (List.range D.length).filter (fun i => match D[i]? with | some v => p v | none => false) := by
  induction D with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx_not_mem, hnd_xs⟩ := List.nodup_cons.mp hnd
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_cons]
    have hmap_xs : ((xs.filter p).map (x :: xs).idxOf) =
        ((xs.filter p).map xs.idxOf).map (· + 1) := by
      rw [List.map_map]
      refine List.map_congr_left fun y hy => ?_
      have hy_xs : y ∈ xs := List.mem_of_mem_filter hy
      have hyx : y ≠ x := fun h => hx_not_mem (h ▸ hy_xs)
      exact List.idxOf_cons_ne xs hyx.symm
    have hfilt_map : ((List.range xs.length).map (· + 1)).filter
        (fun i => match (x :: xs)[i]? with | some v => p v | none => false) =
        ((List.range xs.length).filter
          (fun i => match xs[i]? with | some v => p v | none => false)).map (· + 1) := by
      rw [List.filter_map]
      rfl
    rw [hfilt_map, ← ih hnd_xs]
    cases hpx : p x <;> simp [hpx, hmap_xs]

/-- **Lemma 3 for `candidatesOfIndices` (Sections 5.1 and 5.2):**
If bridges `γA` and `γB` have alternating attachment pairs `(a₁, a₂)` and `(b₁, b₂)` on `D`, then
their candidate lists `candidatesOfIndices γA tA` and `candidatesOfIndices γB tB` contain candidates
`I₁` and `I₂` whose intervals interleave (`I₁.l < I₂.l < I₁.r < I₂.r` or
`I₂.l < I₁.l < I₂.r < I₁.r`). -/
theorem lemma_3_candidatesOfIndices [DecidableEq V] {D : List V} (hnd : D.Nodup)
    (pA pB : V → Bool) (γA γB : ℕ)
    {a₁ a₂ b₁ b₂ : V} (ha₁ : pA a₁ = true) (ha₂ : pA a₂ = true)
    (hb₁ : pB b₁ = true) (hb₂ : pB b₂ = true)
    (halt : Alternate D a₁ a₂ b₁ b₂) :
    let tA := (D.filter pA).map D.idxOf
    let tB := (D.filter pB).map D.idxOf
    ∃ I₁ ∈ candidatesOfIndices γA tA, ∃ I₂ ∈ candidatesOfIndices γB tB,
      (I₁.l < I₂.l ∧ I₂.l < I₁.r ∧ I₁.r < I₂.r) ∨
      (I₂.l < I₁.l ∧ I₁.l < I₂.r ∧ I₂.r < I₁.r) := by
  dsimp only
  obtain ⟨a₁', a₂', b₁', b₂', hcA, hcB, halt'⟩ := lemma_3 hnd pA pB ha₁ ha₂ hb₁ hb₂ halt
  have hinjA : ∀ x ∈ D.filter pA, ∀ y ∈ D.filter pA, D.idxOf x = D.idxOf y → x = y :=
    fun x hx y _ h => (List.idxOf_inj (List.mem_of_mem_filter hx)).mp h
  have hinjB : ∀ x ∈ D.filter pB, ∀ y ∈ D.filter pB, D.idxOf x = D.idxOf y → x = y :=
    fun x hx y _ h => (List.idxOf_inj (List.mem_of_mem_filter hx)).mp h
  set I₁ : Candidate := ⟨min (D.idxOf a₁') (D.idxOf a₂'), max (D.idxOf a₁') (D.idxOf a₂'), γA⟩
  set I₂ : Candidate := ⟨min (D.idxOf b₁') (D.idxOf b₂'), max (D.idxOf b₁') (D.idxOf b₂'), γB⟩
  have hI₁ : I₁ ∈ candidatesOfIndices γA ((D.filter pA).map D.idxOf) := by
    unfold candidatesOfIndices
    rw [attachmentCandidates_map_of_injOn hinjA, List.mem_map]
    exact ⟨(D.idxOf a₁', D.idxOf a₂'), List.mem_map.mpr ⟨(a₁', a₂'), hcA, rfl⟩, rfl⟩
  have hI₂ : I₂ ∈ candidatesOfIndices γB ((D.filter pB).map D.idxOf) := by
    unfold candidatesOfIndices
    rw [attachmentCandidates_map_of_injOn hinjB, List.mem_map]
    exact ⟨(D.idxOf b₁', D.idxOf b₂'), List.mem_map.mpr ⟨(b₁', b₂'), hcB, rfl⟩, rfl⟩
  exact ⟨I₁, hI₁, I₂, hI₂, idxOf_interleave_of_alternate hnd halt'⟩

end GraphMinor.Crossing
