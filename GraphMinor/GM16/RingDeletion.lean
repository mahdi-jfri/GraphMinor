module

public import GraphMinor.GM16.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Card

/-!
# Vertex deletion in an `r`-ring

This file proves the single-ring case of `IsOutgrowthByRings.deleteVertices`:
given an `r`-ring `R` with perimeter `t` (`IsRRing R r t`) and a finite vertex set `Z` with
`Z.ncard ≤ n`, let `t' = t.filter (fun x => decide (x ∉ Z))`.
- If `t'` is nonempty (`IsRRing.deleteVertices_of_filter_ne_nil`), `R \ Z` is an `((n + 1) * r)`-ring
  with perimeter `t'`, obtained by merging each kept bag `X i \ Z` with the run of deleted bags
  immediately following it (and merging the initial run of deleted bags into the first kept bag).
- If `t'` is empty (`IsRRing.deleteVertices_singleton_of_filter_eq_nil`), every vertex of `t` lies in
  `Z`, so `t.length ≤ n`, `V(R \ Z).ncard ≤ n * r ≤ (n + 1) * r`, and for any `y ∈ V(R \ Z)`,
  `R \ Z` is an `((n + 1) * r)`-ring with singleton perimeter `[y]` and single bag `V(R \ Z)`.
-/

public section

namespace GraphMinor.GM16

open Set Function Graph

universe u v

variable {α : Type u} {β : Type v}

/-- Deleting a finite set `Z` from any set `A` (finite or infinite) does not increase `ncard`. -/
theorem ncard_sdiff_le_of_finite_right {A Z : Set α} (hZ : Z.Finite) :
    (A \ Z).ncard ≤ A.ncard := by
  by_cases hA : A.Finite
  · exact Set.ncard_le_ncard sdiff_subset hA
  · have hAZ_inf : (A \ Z).Infinite := by
      intro hAZ_fin
      apply hA
      refine (hAZ_fin.union hZ).subset ?_
      intro x hx
      by_cases hxZ : x ∈ Z
      · exact Or.inr hxZ
      · exact Or.inl ⟨hx, hxZ⟩
    rw [hAZ_inf.ncard]
    exact Nat.zero_le _

/-- Bound on the `ncard` of a union indexed by a `Finset` when each piece has `ncard ≤ r`. -/
theorem ncard_biUnion_finset_le {ι : Type*} (s : Finset ι) (f : ι → Set α) (r : ℕ)
    (hf : ∀ i ∈ s, (f i).ncard ≤ r) :
    (⋃ i ∈ s, f i).ncard ≤ s.card * r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.card_insert_of_notMem ha, Nat.add_one_mul, Nat.add_comm]
    exact (Set.ncard_union_le _ _).trans
      (Nat.add_le_add (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Bound on the `ncard` of a union indexed by `Fin m` when each piece has `ncard ≤ r`. -/
theorem ncard_iUnion_fin_le {m r : ℕ} (f : Fin m → Set α) (hf : ∀ i : Fin m, (f i).ncard ≤ r) :
    (⋃ i : Fin m, f i).ncard ≤ m * r := by
  have h := ncard_biUnion_finset_le (Finset.univ : Finset (Fin m)) f r (fun i _ => hf i)
  simpa using h

/-- Number of elements satisfying `p` in the prefix `t.take k`. -/
def filterPrefixLen (t : List α) (p : α → Bool) (k : ℕ) : ℕ :=
  ((t.take k).filter p).length

@[simp]
theorem filterPrefixLen_zero (t : List α) (p : α → Bool) :
    filterPrefixLen t p 0 = 0 := by
  simp [filterPrefixLen]

@[simp]
theorem filterPrefixLen_nil (p : α → Bool) (k : ℕ) :
    filterPrefixLen ([] : List α) p k = 0 := by
  simp [filterPrefixLen]

theorem filterPrefixLen_cons_succ (x : α) (xs : List α) (p : α → Bool) (k : ℕ) :
    filterPrefixLen (x :: xs) p (k + 1) =
      (if p x then 1 else 0) + filterPrefixLen xs p k := by
  dsimp [filterPrefixLen]
  cases hpx : p x <;> simp [List.filter, hpx, Nat.add_comm]

theorem filterPrefixLen_length (t : List α) (p : α → Bool) :
    filterPrefixLen t p t.length = (t.filter p).length := by
  simp [filterPrefixLen]

theorem filterPrefixLen_mono (t : List α) (p : α → Bool) {k₁ k₂ : ℕ} (hle : k₁ ≤ k₂) :
    filterPrefixLen t p k₁ ≤ filterPrefixLen t p k₂ := by
  induction t generalizing k₁ k₂ with
  | nil => simp
  | cons x xs ih =>
    cases k₁ with
    | zero => exact Nat.zero_le _
    | succ k₁ =>
      cases k₂ with
      | zero => omega
      | succ k₂ =>
        rw [filterPrefixLen_cons_succ, filterPrefixLen_cons_succ]
        exact Nat.add_le_add_left (ih (by omega)) _

theorem filterPrefixLen_le_length (t : List α) (p : α → Bool) (k : ℕ) :
    filterPrefixLen t p k ≤ (t.filter p).length := by
  rw [← filterPrefixLen_length]
  by_cases hk : k ≤ t.length
  · exact filterPrefixLen_mono t p hk
  · have htake : t.take k = t := List.take_of_length_le (by omega)
    simp [filterPrefixLen, htake]

theorem filterPrefixLen_succ (t : List α) (p : α → Bool) {k : ℕ} (hk : k < t.length) :
    filterPrefixLen t p (k + 1) =
      (if p (t[k]'hk) then 1 else 0) + filterPrefixLen t p k := by
  induction t generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero =>
      rw [filterPrefixLen_cons_succ, filterPrefixLen_zero]
      simp
    | succ k =>
      have hk' : k < xs.length := by simpa using hk
      rw [filterPrefixLen_cons_succ, filterPrefixLen_cons_succ, ih hk']
      simp [Nat.add_left_comm]

theorem exists_kept_index_of_lt_filter_length (t : List α) (p : α → Bool)
    {a : ℕ} (ha : a < (t.filter p).length) :
    ∃ (k : ℕ) (hk : k < t.length),
      p (t[k]'hk) = true ∧ filterPrefixLen t p k = a ∧ (t.filter p)[a]'ha = t[k]'hk := by
  induction t generalizing a with
  | nil => simp at ha
  | cons x xs ih =>
    cases hpx : p x
    · have ha' : a < (xs.filter p).length := by simpa [List.filter, hpx] using ha
      obtain ⟨k, hk, hpk, hlen, hget⟩ := ih ha'
      refine ⟨k + 1, Nat.succ_lt_succ hk, hpk, ?_, ?_⟩
      · rw [filterPrefixLen_cons_succ, hpx]
        simp [hlen]
      · simpa [List.filter, hpx] using hget
    · cases a with
      | zero =>
        refine ⟨0, Nat.zero_lt_succ _, by simpa using hpx, by simp, ?_⟩
        simp [List.filter, hpx]
      | succ a =>
        have ha' : a < (xs.filter p).length := by
          simpa [List.filter, hpx, Nat.add_comm] using ha
        obtain ⟨k, hk, hpk, hlen, hget⟩ := ih ha'
        refine ⟨k + 1, Nat.succ_lt_succ hk, hpk, ?_, ?_⟩
        · rw [filterPrefixLen_cons_succ, hpx]
          simp [hlen, Nat.add_comm]
        · simpa [List.filter, hpx] using hget

theorem card_deleted_indices_le {t : List α} (hnodup : t.Nodup) {Z : Set α}
    (hfin : Z.Finite) {n : ℕ} (hZ : Z.ncard ≤ n) (p : α → Bool)
    (hp : ∀ x, p x = false → x ∈ Z) :
    (Finset.univ.filter (fun j : Fin t.length => p (t[j.1]) = false)).card ≤ n := by
  classical
  let s_del : Finset (Fin t.length) :=
    Finset.univ.filter (fun j : Fin t.length => p (t[j.1]) = false)
  let g : Fin t.length → α := fun j => t[j.1]
  have hg_inj : Function.Injective g := by
    intro i j hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnodup).mp hij)
  have himg_sub : ((s_del.image g : Finset α) : Set α) ⊆ Z := by
    rintro x hx
    rw [Finset.mem_coe, Finset.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [Finset.mem_filter] at hj
    exact hp (g j) hj.2
  have hcard_eq : (s_del.image g).card = s_del.card :=
    Finset.card_image_of_injective s_del hg_inj
  have hncard_eq : ((s_del.image g : Finset α) : Set α).ncard = (s_del.image g).card :=
    Set.ncard_coe_finset (s_del.image g)
  have hle_Z : ((s_del.image g : Finset α) : Set α).ncard ≤ Z.ncard :=
    Set.ncard_le_ncard himg_sub hfin
  calc s_del.card
    _ = (s_del.image g).card := hcard_eq.symm
    _ = ((s_del.image g : Finset α) : Set α).ncard := hncard_eq.symm
    _ ≤ Z.ncard := hle_Z
    _ ≤ n := hZ

/-- If `R` is an `r`-ring with perimeter `t`, `Z` is a finite set of at most `n` vertices, and
`t' = t.filter (fun x => decide (x ∉ Z))` is nonempty, then `R \ Z` is an `((n + 1) * r)`-ring
with perimeter `t'`. -/
theorem IsRRing.deleteVertices_of_filter_ne_nil
    {R : Graph α β} {r n : ℕ} {t : List α}
    (hR : IsRRing R r t) {Z : Set α} [DecidablePred (· ∈ Z)] (hZ : Z.ncard ≤ n) (hfin : Z.Finite)
    (hne : t.filter (fun x => decide (x ∉ Z)) ≠ []) :
    IsRRing (GM09.deleteVertices R Z) ((n + 1) * r) (t.filter (fun x => decide (x ∉ Z))) := by
  let p : α → Bool := fun x => decide (x ∉ Z)
  let t' : List α := t.filter p
  have hm'_pos : 0 < t'.length := List.length_pos_of_ne_nil hne
  rcases hR with ⟨ht_nodup, ht_mem, X, hX_sub, hX_union, hX_edge, hX_perim, hX_interp, hX_card⟩
  have ht'_nodup : t'.Nodup := ht_nodup.sublist (List.filter_sublist)
  have ht'_mem : ∀ x ∈ t', x ∈ V(GM09.deleteVertices R Z) := by
    intro x hx
    rw [List.mem_filter] at hx
    exact ⟨ht_mem x hx.1, of_decide_eq_true hx.2⟩
  let bucket (j : Fin t.length) : Fin t'.length :=
    ⟨filterPrefixLen t p (j.1 + 1) - 1, by
      have hle : filterPrefixLen t p (j.1 + 1) ≤ t'.length :=
        filterPrefixLen_le_length t p (j.1 + 1)
      omega⟩
  have hbucket_mono : ∀ {j₁ j₂ : Fin t.length}, j₁ ≤ j₂ → bucket j₁ ≤ bucket j₂ := by
    intro j₁ j₂ hle
    change filterPrefixLen t p (j₁.1 + 1) - 1 ≤ filterPrefixLen t p (j₂.1 + 1) - 1
    have hmono := filterPrefixLen_mono t p (show j₁.1 + 1 ≤ j₂.1 + 1 by omega)
    omega
  have hbucket_kept : ∀ a : Fin t'.length, ∃ j : Fin t.length,
      p (t[j.1]) = true ∧ filterPrefixLen t p j.1 = a.1 ∧ bucket j = a ∧ t'[a.1] = t[j.1] := by
    intro a
    obtain ⟨k, hk, hpk, hlen, hget⟩ := exists_kept_index_of_lt_filter_length t p a.2
    refine ⟨⟨k, hk⟩, hpk, hlen, ?_, hget⟩
    apply Fin.ext
    change filterPrefixLen t p (k + 1) - 1 = a.1
    rw [filterPrefixLen_succ t p hk, hpk]
    simp [hlen]
  let X' (a : Fin t'.length) : Set α :=
    ⋃ (j : Fin t.length) (_ : bucket j = a), (X j \ Z)
  refine ⟨ht'_nodup, ht'_mem, X', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    refine iUnion₂_subset fun j _ v hv => ⟨hX_sub j hv.1, hv.2⟩
  · ext v
    constructor
    · rintro hv
      rcases mem_iUnion.mp hv with ⟨a, hv⟩
      rcases mem_iUnion₂.mp hv with ⟨j, _, hv⟩
      exact ⟨hX_sub j hv.1, hv.2⟩
    · rintro ⟨hvR, hvZ⟩
      rw [← hX_union, mem_iUnion] at hvR
      rcases hvR with ⟨j, hvj⟩
      exact mem_iUnion.mpr ⟨bucket j, mem_iUnion₂.mpr ⟨j, rfl, hvj, hvZ⟩⟩
  · intro e he
    have heR : e ∈ E(R) := (R.induce_le sdiff_subset).edgeSet_mono he
    obtain ⟨j, hj⟩ := hX_edge e heR
    refine ⟨bucket j, fun v hinc => ?_⟩
    rcases hinc with ⟨w, hlink⟩
    have hlinkR : R.IsLink e v w := hlink.mono (R.induce_le sdiff_subset)
    exact mem_iUnion₂.mpr ⟨j, rfl, hj v ⟨w, hlinkR⟩, hlink.left_mem.2⟩
  · intro a
    obtain ⟨j, hpk, _, hbj, hget⟩ := hbucket_kept a
    rw [hget]
    exact mem_iUnion₂.mpr ⟨j, hbj, hX_perim j, of_decide_eq_true hpk⟩
  · intro a₁ a₂ a₃ h12 h23
    rcases eq_or_lt_of_le h12 with rfl | hlt12
    · exact inter_subset_left
    · rcases eq_or_lt_of_le h23 with rfl | hlt23
      · exact inter_subset_right
      · rintro x ⟨hx₁, hx₃⟩
        obtain ⟨j₁, hj₁_eq, hxj₁⟩ := mem_iUnion₂.mp hx₁
        obtain ⟨j₃, hj₃_eq, hxj₃⟩ := mem_iUnion₂.mp hx₃
        obtain ⟨j₂, _, _, hj₂_eq, _⟩ := hbucket_kept a₂
        have hj12 : j₁ ≤ j₂ := by
          by_contra hgt
          have hle : bucket j₂ ≤ bucket j₁ := hbucket_mono (le_of_not_ge hgt)
          rw [hj₁_eq, hj₂_eq] at hle
          exact not_lt_of_ge hle hlt12
        have hj23 : j₂ ≤ j₃ := by
          by_contra hgt
          have hle : bucket j₃ ≤ bucket j₂ := hbucket_mono (le_of_not_ge hgt)
          rw [hj₂_eq, hj₃_eq] at hle
          exact not_lt_of_ge hle hlt23
        have hxj₂ : x ∈ X j₂ \ Z :=
          ⟨hX_interp j₁ j₂ j₃ hj12 hj23 ⟨hxj₁.1, hxj₃.1⟩, hxj₁.2⟩
        exact mem_iUnion₂.mpr ⟨j₂, hj₂_eq, hxj₂⟩
  · intro a
    obtain ⟨j₀, hpj₀, hlen_j₀, hbj₀, _⟩ := hbucket_kept a
    let s_del : Finset (Fin t.length) :=
      Finset.univ.filter (fun j : Fin t.length => p (t[j.1]) = false)
    let s_fib : Finset (Fin t.length) :=
      Finset.univ.filter (fun j : Fin t.length => bucket j = a)
    have hfib_sub : s_fib ⊆ insert j₀ s_del := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_insert, Finset.mem_filter]
      cases hpj : p (t[j.1])
      · exact Or.inr ⟨Finset.mem_univ j, rfl⟩
      · left
        have hsucc_j : filterPrefixLen t p (j.1 + 1) = filterPrefixLen t p j.1 + 1 := by
          rw [filterPrefixLen_succ t p j.2, hpj]
          simp [Nat.add_comm]
        have hlen_j : filterPrefixLen t p j.1 = a.1 := by
          have hb_val : (bucket j).1 = a.1 := congrArg Fin.val hj.2
          change filterPrefixLen t p (j.1 + 1) - 1 = a.1 at hb_val
          omega
        rcases lt_trichotomy j.1 j₀.1 with hlt | heq | hgt
        · have hmono := filterPrefixLen_mono t p (show j.1 + 1 ≤ j₀.1 by omega)
          omega
        · exact Fin.ext heq
        · have hmono := filterPrefixLen_mono t p (show j₀.1 + 1 ≤ j.1 by omega)
          have hsucc_j₀ : filterPrefixLen t p (j₀.1 + 1) = filterPrefixLen t p j₀.1 + 1 := by
            rw [filterPrefixLen_succ t p j₀.2, hpj₀]
            simp [Nat.add_comm]
          omega
    have hcard_del : s_del.card ≤ n := by
      refine card_deleted_indices_le ht_nodup hfin hZ p ?_
      intro x hx
      by_contra hxZ
      have : p x = true := decide_eq_true hxZ
      rw [this] at hx
      cases hx
    have hcard_fib : s_fib.card ≤ n + 1 := by
      calc s_fib.card
        _ ≤ (insert j₀ s_del).card := Finset.card_le_card hfib_sub
        _ ≤ s_del.card + 1 := Finset.card_insert_le j₀ s_del
        _ ≤ n + 1 := by omega
    have hX'_eq : X' a = ⋃ j ∈ s_fib, (X j \ Z) := by
      ext v
      simp [X', s_fib]
    rw [hX'_eq]
    have h : ∀ j ∈ s_fib, (X j \ Z).ncard ≤ r :=
      fun j _ => (ncard_sdiff_le_of_finite_right hfin).trans (hX_card j)
    calc (⋃ j ∈ s_fib, (X j \ Z)).ncard
      _ ≤ s_fib.card * r := ncard_biUnion_finset_le s_fib (fun j => X j \ Z) r h
      _ ≤ (n + 1) * r := Nat.mul_le_mul_right r hcard_fib

/-- If `R` is an `r`-ring with perimeter `t`, `Z` is a finite set of at most `n` vertices, and
`t.filter (fun x => decide (x ∉ Z)) = []`, then for any `y ∈ V(R \ Z)`, `R \ Z` is an
`((n + 1) * r)`-ring with singleton perimeter `[y]`. -/
theorem IsRRing.deleteVertices_singleton_of_filter_eq_nil
    {R : Graph α β} {r n : ℕ} {t : List α}
    (hR : IsRRing R r t) {Z : Set α} [DecidablePred (· ∈ Z)] (hZ : Z.ncard ≤ n) (hfin : Z.Finite)
    (heq : t.filter (fun x => decide (x ∉ Z)) = [])
    {y : α} (hy : y ∈ V(GM09.deleteVertices R Z)) :
    t ≠ [] ∧ IsRRing (GM09.deleteVertices R Z) ((n + 1) * r) [y] := by
  let p : α → Bool := fun x => decide (x ∉ Z)
  rcases hR with ⟨ht_nodup, _, X, _, hX_union, _, _, _, hX_card⟩
  have ht_ne_nil : t ≠ [] := by
    rintro rfl
    have hV_empty : V(R) = ∅ := by
      rw [← hX_union]
      simp
    have hyR : y ∈ V(R) := hy.1
    rw [hV_empty] at hyR
    exact hyR
  refine ⟨ht_ne_nil, List.nodup_singleton y, ?_, fun _ => V(GM09.deleteVertices R Z),
    fun _ => subset_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [List.mem_singleton] at hx
    rwa [hx]
  · ext v
    simp
  · intro e _
    exact ⟨⟨0, Nat.zero_lt_one⟩, fun v ⟨_, hlink⟩ => hlink.left_mem⟩
  · intro i
    simp [hy]
  · intro _ _ _ _ _
    exact inter_subset_left
  · intro _
    have hV_eq : V(GM09.deleteVertices R Z) = ⋃ j : Fin t.length, (X j \ Z) := by
      change V(R) \ Z = ⋃ j : Fin t.length, (X j \ Z)
      rw [← hX_union, Set.iUnion_sdiff]
    have hdel_all : ∀ j : Fin t.length, p (t[j.1]) = false := by
      intro j
      cases hpj : p (t[j.1])
      · rfl
      · exfalso
        have hmem : t[j.1] ∈ t.filter (fun x => decide (x ∉ Z)) :=
          List.mem_filter.mpr ⟨List.getElem_mem j.2, hpj⟩
        rw [heq] at hmem
        cases hmem
    have hs_del_eq :
        Finset.univ.filter (fun j : Fin t.length => p (t[j.1]) = false) = Finset.univ := by
      ext j
      simp [hdel_all j]
    have hlen_le_n : t.length ≤ n := by
      have hcard := card_deleted_indices_le ht_nodup hfin hZ p (fun x hx => by
        by_contra hxZ
        have : p x = true := decide_eq_true hxZ
        rw [this] at hx
        cases hx)
      simpa [hs_del_eq] using hcard
    rw [hV_eq]
    calc (⋃ j : Fin t.length, (X j \ Z)).ncard
      _ ≤ t.length * r :=
        ncard_iUnion_fin_le (fun j => X j \ Z)
          (fun j => (ncard_sdiff_le_of_finite_right hfin).trans (hX_card j))
      _ ≤ n * r := Nat.mul_le_mul_right r hlen_le_n
      _ ≤ (n + 1) * r := Nat.mul_le_mul_right r (Nat.le_succ n)

end GraphMinor.GM16
