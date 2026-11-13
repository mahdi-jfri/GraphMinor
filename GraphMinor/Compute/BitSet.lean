module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import GraphMinor.Compute.Logic

/-!
# Vertex Subsets as Bit Arrays in the Word RAM Model

This file provides a general library for representing subsets `X : Finset (Fin n)` as `0`/`1`
indicator arrays of length `n` in the Word RAM model:
- `bitSetList X`: canonical `0`/`1` list of length `n` encoding `X : Finset (Fin n)`.
- `finsetOfBitList n l`: decodes any `List ℕ` into `Finset (Fin n)` by filtering indices `< n`
  with non-zero entries.
- `IsBitSet X a s`: predicate stating that `s.arrs a` has length `n`, entries in `{0, 1}`, and
  non-zero entry at `u.1` if and only if `u ∈ X` (equivalently `s.arrs a = bitSetList X`).
- Word RAM operations for initializing empty/full bit sets, inserting/removing elements, copying a
  slice from an input array into a bit-set array (`readSliceProg`), and counting the cardinality of
  a bit set (`cardBitSetProg`).
-/

@[expose] public section

namespace GraphMinor.Compute

/-! ### Section 1: Pure Bit-List Encoding and Decoding of `Finset (Fin n)` -/

/-- Canonical `0`/`1` indicator list of length `n` for a subset `X : Finset (Fin n)`. -/
def bitSetList {n : ℕ} (X : Finset (Fin n)) : List ℕ :=
  List.ofFn (fun u : Fin n => if u ∈ X then 1 else 0)

@[simp]
theorem length_bitSetList {n : ℕ} (X : Finset (Fin n)) :
    (bitSetList X).length = n := by
  simp [bitSetList]

@[simp]
theorem getElem_bitSetList {n : ℕ} (X : Finset (Fin n)) (i : ℕ) (hi : i < n) :
    (bitSetList X)[i]'(by rw [length_bitSetList]; exact hi) =
      if (⟨i, hi⟩ : Fin n) ∈ X then 1 else 0 := by
  simp [bitSetList]

theorem getElem_bitSetList_le_one {n : ℕ} (X : Finset (Fin n)) (i : ℕ)
    (hi : i < (bitSetList X).length) :
    (bitSetList X)[i]'hi ≤ 1 := by
  have hi' : i < n := by simpa [length_bitSetList] using hi
  rw [getElem_bitSetList X i hi']
  split_ifs <;> omega

theorem getElem_bitSetList_ne_zero_iff {n : ℕ} (X : Finset (Fin n)) (u : Fin n) :
    (bitSetList X)[u.1]'(by rw [length_bitSetList]; exact u.2) ≠ 0 ↔ u ∈ X := by
  rw [getElem_bitSetList X u.1 u.2]
  split_ifs with h <;> simp [h]

/-- Decode a list `l : List ℕ` into a subset of `Fin n` by selecting all `u : Fin n` with
`l.getD u.1 0 ≠ 0`. -/
def finsetOfBitList (n : ℕ) (l : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun u : Fin n => l.getD u.1 0 ≠ 0)

@[simp]
theorem mem_finsetOfBitList {n : ℕ} {l : List ℕ} (u : Fin n) :
    u ∈ finsetOfBitList n l ↔ l.getD u.1 0 ≠ 0 := by
  simp [finsetOfBitList]

theorem take_add_one_eq_append_getElem {α : Type*} (l : List α) (k : ℕ) (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l[k]'hk] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  rfl

theorem mem_finsetOfBitList_of_lt {n : ℕ} {l : List ℕ} (u : Fin n) (hu : u.1 < l.length) :
    u ∈ finsetOfBitList n l ↔ l[u.1]'hu ≠ 0 := by
  rw [mem_finsetOfBitList]
  change (l[u.1]?.getD 0 ≠ 0) ↔ l[u.1]'hu ≠ 0
  rw [List.getElem?_eq_getElem hu]
  rfl

@[simp]
theorem finsetOfBitList_bitSetList {n : ℕ} (X : Finset (Fin n)) :
    finsetOfBitList n (bitSetList X) = X := by
  ext u
  rw [mem_finsetOfBitList_of_lt u (by simp [u.2])]
  exact getElem_bitSetList_ne_zero_iff X u

/-! ### Section 2: `IsBitSet` State Predicate -/

/-- `IsBitSet X a s` holds when array `a` in state `s` is a `0`/`1` indicator array of length `n`
for `X : Finset (Fin n)`. -/
def IsBitSet {n : ℕ} (X : Finset (Fin n)) (a : Arr) (s : State) : Prop :=
  ∃ (hlen : (s.arrs a).length = n),
    (∀ u : Fin n, (s.arrs a)[u.1]'(by rw [hlen]; exact u.2) ≤ 1) ∧
    (∀ u : Fin n, (s.arrs a)[u.1]'(by rw [hlen]; exact u.2) ≠ 0 ↔ u ∈ X)

theorem IsBitSet.of_arr_eq {n : ℕ} {X : Finset (Fin n)} {a : Arr} {s s' : State}
    (h : IsBitSet X a s) (heq : s'.arrs a = s.arrs a) :
    IsBitSet X a s' := by
  rcases h with ⟨hlen, hle, hmem⟩
  exact ⟨by rw [heq, hlen],
    fun u => by simp only [heq]; exact hle u,
    fun u => by simp only [heq]; exact hmem u⟩

theorem IsBitSet.of_bitSetList {n : ℕ} (X : Finset (Fin n)) (a : Arr) (s : State)
    (harr : s.arrs a = bitSetList X) :
    IsBitSet X a s := by
  refine ⟨by rw [harr, length_bitSetList], fun u => ?_, fun u => ?_⟩
  · simp only [harr]
    exact getElem_bitSetList_le_one X u.1 (by rw [length_bitSetList]; exact u.2)
  · simp only [harr]
    exact getElem_bitSetList_ne_zero_iff X u

theorem IsBitSet.getElem_eq_ite {n : ℕ} {X : Finset (Fin n)} {a : Arr} {s : State}
    (h : IsBitSet X a s) (u : Fin n) :
    (s.arrs a)[u.1]'(by rw [h.1]; exact u.2) = if u ∈ X then 1 else 0 := by
  rcases h with ⟨hlen, hle, hmem⟩
  have hle_u := hle u
  have hmem_u := hmem u
  split_ifs with hu
  · have hne : (s.arrs a)[u.1]'(by rw [hlen]; exact u.2) ≠ 0 := hmem_u.mpr hu
    omega
  · by_contra hne
    exact hu (hmem_u.mp hne)

theorem IsBitSet.arr_eq_bitSetList {n : ℕ} {X : Finset (Fin n)} {a : Arr} {s : State}
    (h : IsBitSet X a s) :
    s.arrs a = bitSetList X := by
  apply List.ext_getElem
  · rw [h.1, length_bitSetList]
  · intro i hi₁ hi₂
    have hi : i < n := by simpa [length_bitSetList] using hi₂
    rw [getElem_bitSetList X i hi]
    exact h.getElem_eq_ite ⟨i, hi⟩

theorem IsBitSet.finsetOfBitList_eq {n : ℕ} {X : Finset (Fin n)} {a : Arr} {s : State}
    (h : IsBitSet X a s) :
    finsetOfBitList n (s.arrs a) = X := by
  rw [h.arr_eq_bitSetList, finsetOfBitList_bitSetList]

theorem IsBitSet.empty_of_replicate {n : ℕ} {a : Arr} {s : State}
    (harr : s.arrs a = List.replicate n 0) :
    IsBitSet (∅ : Finset (Fin n)) a s := by
  refine ⟨by simp [harr], fun u => by simp [harr], fun u => ?_⟩
  simp [harr]

theorem IsBitSet.univ_of_replicate {n : ℕ} {a : Arr} {s : State}
    (harr : s.arrs a = List.replicate n 1) :
    IsBitSet (Finset.univ : Finset (Fin n)) a s := by
  refine ⟨by simp [harr], fun u => by simp [harr], fun u => ?_⟩
  simp [harr]

theorem IsBitSet.write_one {n : ℕ} {X : Finset (Fin n)} {a : Arr} {s : State}
    (h : IsBitSet X a s) (u : Fin n) :
    IsBitSet (insert u X) a (s.writeArr a u.1 1) := by
  rcases h with ⟨hlen, hle, hmem⟩
  refine ⟨by simp [hlen], fun v => ?_, fun v => ?_⟩
  · simp only [State.writeArr_arrs_self]
    by_cases hvu : v.1 = u.1
    · simp only [hvu]
      rw [List.getElem_set_self (by simp [hlen, u.2])]
    · rw [List.getElem_set_ne (Ne.symm hvu)]
      exact hle v
  · simp only [State.writeArr_arrs_self, Finset.mem_insert]
    by_cases hvu : v.1 = u.1
    · have hvu_eq : v = u := Fin.ext hvu
      simp only [hvu]
      rw [List.getElem_set_self (by simp [hlen, u.2])]
      simp [hvu_eq]
    · have hvu_ne : v ≠ u := fun heq => hvu (congrArg Fin.val heq)
      rw [List.getElem_set_ne (Ne.symm hvu)]
      simp [hvu_ne, hmem v]

theorem IsBitSet.write_zero {n : ℕ} {X : Finset (Fin n)} {a : Arr} {s : State}
    (h : IsBitSet X a s) (u : Fin n) :
    IsBitSet (X.erase u) a (s.writeArr a u.1 0) := by
  rcases h with ⟨hlen, hle, hmem⟩
  refine ⟨by simp [hlen], fun v => ?_, fun v => ?_⟩
  · simp only [State.writeArr_arrs_self]
    by_cases hvu : v.1 = u.1
    · simp only [hvu]
      rw [List.getElem_set_self (by simp [hlen, u.2])]
      decide
    · rw [List.getElem_set_ne (Ne.symm hvu)]
      exact hle v
  · simp only [State.writeArr_arrs_self, Finset.mem_erase]
    by_cases hvu : v.1 = u.1
    · have hvu_eq : v = u := Fin.ext hvu
      simp only [hvu]
      rw [List.getElem_set_self (by simp [hlen, u.2])]
      simp [hvu_eq]
    · have hvu_ne : v ≠ u := fun heq => hvu (congrArg Fin.val heq)
      rw [List.getElem_set_ne (Ne.symm hvu)]
      simp [hvu_ne, hmem v]

/-! ### Section 3: Copying an Array Slice (`readSliceProg`) -/

/-- Copy `n` words starting at offset `e_off` in `a_src` into a newly allocated array `a_dst` of
length `e_n`, using registers `r_base` (offset), `r_base + 1` (loop index `i`), and `r_base + 2`
(temporary value). -/
def readSliceBody (a_src a_dst : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 2) (.read a_src (.op .add (.reg r_base) (.reg (r_base + 1)))))
    (.write a_dst (.reg (r_base + 1)) (.reg (r_base + 2)))

def readSliceProg (a_src : Arr) (e_off : Expr) (a_dst : Arr) (e_n : Expr) (r_base : Reg) : Cmd :=
  .seq (.assign r_base e_off)
    (.seq (.alloc a_dst e_n)
      (.seq (.assign (r_base + 1) (.const 0))
        (forUp (r_base + 1) e_n (readSliceBody a_src a_dst r_base))))

theorem readSliceLoop_exec {w n off : ℕ} (a_src a_dst : ℕ) (r_n r_base : ℕ)
    (hne_arr : a_src ≠ a_dst)
    (hr_n : r_n < r_base)
    (pre mid suf : List ℕ)
    (hpre : pre.length = off) (hmid : mid.length = n)
    (hmid_w : ∀ x ∈ mid, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hoff_n_w : off + n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hsrc : s.arrs a_src = pre ++ mid ++ suf)
    (hdst : s.arrs a_dst = mid.take k ++ List.replicate (n - k) 0)
    (hrn_val : s.regs r_n = n)
    (hroff : s.regs r_base = off)
    (hrk : s.regs (r_base + 1) = k) :
    ∃ s' t,
      Exec w (forUp (r_base + 1) (.reg r_n) (readSliceBody a_src a_dst r_base)) s s' t ∧
      t ≤ 3 + 15 * rem ∧
      s'.arrs a_dst = mid ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg (r_base + 1)) (.reg r_n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrn_val, hn_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    have htake : mid.take k = mid := List.take_of_length_le (by omega)
    simpa [htake] using hdst
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    have hoff_w : off < 2 ^ w := by omega
    have hoff_k_w : off + k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 1)) (.reg r_n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrn_val, hk_w, hn_w, hk_lt, hw]
    have hk_mid : k < mid.length := by omega
    let val := mid[k]'hk_mid
    have hval_w : val < 2 ^ w := hmid_w val (List.getElem_mem hk_mid)
    have hsrc_len : off + k < (s.arrs a_src).length := by
      simp [hsrc, hpre, hmid]; omega
    have hsrc_get : (s.arrs a_src)[off + k]'hsrc_len = val := by
      simp only [hsrc, List.append_assoc]
      rw [List.getElem_append_right (by omega)]
      rw [List.getElem_append_left (by omega)]
      congr 1
      omega
    have heval_rd :
        (Expr.read a_src (.op .add (.reg r_base) (.reg (r_base + 1)))).eval w s = some val := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hroff, hrk, hoff_w, hk_w, hoff_k_w,
        hsrc_len, hsrc_get, hval_w]
    let s₁ := s.setReg (r_base + 2) val
    have hex₁ :
        Exec w (.assign (r_base + 2) (.read a_src (.op .add (.reg r_base) (.reg (r_base + 1)))))
          s s₁ 5 := .assign heval_rd
    have hdst_len : k < (s₁.arrs a_dst).length := by
      have : (s.arrs a_dst).length = n := by
        rw [hdst, List.length_append, List.length_take, List.length_replicate, hmid]
        omega
      simp [s₁, this, hk_lt]
    let s₂ := s₁.writeArr a_dst k val
    have hex₂ : Exec w (.write a_dst (.reg (r_base + 1)) (.reg (r_base + 2))) s₁ s₂ 3 :=
      .write (by simp [s₁, State.setReg, Expr.eval, checkWord, hrk, hk_w])
        (by simp [s₁, State.setReg, Expr.eval, checkWord, hval_w])
        hdst_len
    have hex_body : Exec w (readSliceBody a_src a_dst r_base) s s₂ (5 + 3) :=
      .seq hex₁ hex₂
    have hrk₂ : s₂.regs (r_base + 1) = k := by
      simp [s₂, s₁, State.setReg, hrk]
    have hinc : (Expr.op .add (.reg (r_base + 1)) (.const 1)).eval w s₂ = some (k + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk₂, hk_w, hw,
        show k + 1 < 2 ^ w by omega]
    let s₃ := s₂.setReg (r_base + 1) (k + 1)
    have hex_inc : Exec w (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
        s₂ s₃ 4 := .assign hinc
    have hdst₃ : s₃.arrs a_dst = mid.take (k + 1) ++ List.replicate (n - (k + 1)) 0 := by
      simp only [s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, hdst]
      have hlen_take : (mid.take k).length = k := by rw [List.length_take]; omega
      rw [List.set_append_right _ _ (by omega)]
      have hsub0 : k - (mid.take k).length = 0 := by omega
      have hrep : n - k = (n - (k + 1)) + 1 := by omega
      rw [hsub0, hrep, List.replicate_succ, List.set_cons_zero]
      rw [take_add_one_eq_append_getElem mid k hk_mid, List.append_assoc, List.singleton_append]
    have hsrc₃ : s₃.arrs a_src = pre ++ mid ++ suf := by
      simp [s₃, s₂, s₁, show (a_src : Arr) ≠ a_dst from hne_arr, hsrc]
    rcases ih (k + 1) (by omega) (s := s₃) hsrc₃ hdst₃
        (by simp [s₃, s₂, s₁, State.setReg, show (r_n : Reg) ≠ r_base + 1 by omega,
          show (r_n : Reg) ≠ r_base + 2 by omega, hrn_val])
        (by simp [s₃, s₂, s₁, State.setReg, hroff])
        (by simp [s₃]) with
      ⟨s₄, t₄, hex₄, ht₄, hdst₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((5 + 3) + 4) + t₄,
      .while_true hcond (by omega) (.seq hex_body hex_inc) hex₄,
      by omega, hdst₄,
      fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁, show (a : Arr) ≠ a_dst from ha],
      fun r hr => by
        rw [hreg₄ r hr]
        simp [s₃, s₂, s₁, State.setReg,
          show (r : Reg) ≠ r_base + 1 by omega,
          show (r : Reg) ≠ r_base + 2 by omega]⟩

/-- Specification of `readSliceProg`: copies a slice `mid` of length `n` starting at offset `off`
from `a_src` into `a_dst` in `O(n)` time (`16 * n + 8 + e_off.cost`), preserving all other arrays
and all registers `< r_base`. -/
theorem readSliceProg_exec {w n off : ℕ} (a_src a_dst : ℕ) (e_off : Expr) (r_n r_base : ℕ)
    (hne_arr : a_src ≠ a_dst)
    (hr_n : r_n < r_base)
    (pre mid suf : List ℕ)
    (hpre : pre.length = off) (hmid : mid.length = n)
    (hmid_w : ∀ x ∈ mid, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hoff_n_w : off + n < 2 ^ w)
    {s : State}
    (he_off : e_off.eval w s = some off)
    (hsrc : s.arrs a_src = pre ++ mid ++ suf)
    (hrn_val : s.regs r_n = n) :
    ∃ s' t,
      Exec w (readSliceProg a_src e_off a_dst (.reg r_n) r_base) s s' t ∧
      t ≤ 16 * n + 8 + e_off.cost ∧
      s'.arrs a_dst = mid ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  let s₁ := s.setReg r_base off
  have hex₁ : Exec w (.assign r_base e_off) s s₁ (e_off.cost + 1) :=
    .assign he_off
  have hrn₁ : s₁.regs r_n = n := by
    simp [s₁, State.setReg, show (r_n : Reg) ≠ r_base by omega, hrn_val]
  let s₂ := s₁.setArr a_dst (List.replicate n 0)
  have heval_n : (Expr.reg r_n).eval w s₁ = some n := by
    simp [Expr.eval, checkWord, hrn₁, hn_w]
  have hex₂ : Exec w (.alloc a_dst (.reg r_n)) s₁ s₂ (1 + n) :=
    .alloc heval_n
  let s₃ := s₂.setReg (r_base + 1) 0
  have hex₃ : Exec w (.assign (r_base + 1) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases readSliceLoop_exec a_src a_dst r_n r_base hne_arr hr_n pre mid suf hpre hmid hmid_w
      hw hoff_n_w n 0 (by omega) (s := s₃)
      (by simp [s₃, s₂, s₁, show (a_src : Arr) ≠ a_dst from hne_arr, hsrc])
      (by simp [s₃, s₂])
      (by simp [s₃, s₂, State.setReg, show (r_n : Reg) ≠ r_base + 1 by omega, hrn₁])
      (by simp [s₃, s₂, s₁, State.setReg])
      (by simp [s₃]) with
    ⟨s₄, t₄, hex₄, ht₄, hdst₄, harr₄, hreg₄⟩
  refine ⟨s₄, (e_off.cost + 1) + ((1 + n) + (2 + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hdst₄,
    fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁, show (a : Arr) ≠ a_dst from ha],
    fun r hr => by
      rw [hreg₄ r hr]
      simp [s₃, s₂, s₁, State.setReg,
        show (r : Reg) ≠ r_base + 1 by omega,
        show (r : Reg) ≠ r_base by omega]⟩

/-! ### Section 4: Counting the Cardinality of a Bit Set (`cardBitSetProg`) -/

/-- Sum of `bitSetList X` is `X.card`. -/
theorem sum_take_bitSetList {n : ℕ} (X : Finset (Fin n)) (k : ℕ) (hk : k ≤ n) :
    ((bitSetList X).take k).sum = (X.filter (fun u : Fin n => u.1 < k)).card := by
  induction k with
  | zero =>
    have hfilt : X.filter (fun u : Fin n => u.1 < 0) = ∅ := by
      ext u
      simp
    rw [hfilt]
    simp
  | succ k ih =>
    have hk_len : k < (bitSetList X).length := by rw [length_bitSetList]; omega
    rw [take_add_one_eq_append_getElem (bitSetList X) k hk_len, List.sum_append,
      List.sum_singleton, ih (by omega), getElem_bitSetList X k (by omega)]
    let uk : Fin n := ⟨k, by omega⟩
    by_cases huk : uk ∈ X
    · have hfilt : X.filter (fun u : Fin n => u.1 < k + 1) =
          insert uk (X.filter (fun u : Fin n => u.1 < k)) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨huX, hlt⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
          · exact Or.inr ⟨huX, hlt'⟩
          · exact Or.inl (Fin.ext heq)
        · rintro (rfl | ⟨huX, hlt⟩)
          · exact ⟨huk, by simp [uk]⟩
          · exact ⟨huX, by omega⟩
      have hnot_mem : uk ∉ X.filter (fun u : Fin n => u.1 < k) := by
        simp [uk]
      simp [uk, huk, hfilt, Finset.card_insert_of_notMem hnot_mem]
    · have hfilt : X.filter (fun u : Fin n => u.1 < k + 1) =
          X.filter (fun u : Fin n => u.1 < k) := by
        ext u
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨huX, hlt⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
          · exact ⟨huX, hlt'⟩
          · exfalso
            have : u = uk := Fin.ext heq
            subst this
            exact huk huX
        · rintro ⟨huX, hlt⟩
          exact ⟨huX, by omega⟩
      simp [uk, huk, hfilt]

@[simp]
theorem sum_bitSetList {n : ℕ} (X : Finset (Fin n)) :
    (bitSetList X).sum = X.card := by
  have h := sum_take_bitSetList X n (le_rfl)
  have htake : (bitSetList X).take n = bitSetList X :=
    List.take_of_length_le (by simp)
  have hfilt : X.filter (fun u : Fin n => u.1 < n) = X := by
    ext u
    simp
  rw [htake, hfilt] at h
  exact h

/-- Count the cardinality of a bit-set array `a_set` of length `e_n` into `r_card`, using loop
register `r_i`. -/
def cardBitSetProg (a_set : Arr) (e_n : Expr) (r_card r_i : Reg) : Cmd :=
  .seq (.assign r_card (.const 0))
    (.seq (.assign r_i (.const 0))
      (forUp r_i e_n
        (.assign r_card (.op .add (.reg r_card) (.read a_set (.reg r_i))))))

theorem cardBitSetLoop_exec {w n : ℕ} (X : Finset (Fin n)) (a_set : ℕ) (r_n r_card r_i : ℕ)
    (hne_ci : r_card ≠ r_i) (hne_cn : r_card ≠ r_n) (hne_in : r_i ≠ r_n)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hset : IsBitSet X a_set s)
    (hrn : s.regs r_n = n)
    (hrcard : s.regs r_card = ((bitSetList X).take k).sum)
    (hri : s.regs r_i = k) :
    ∃ s' t,
      Exec w (forUp r_i (.reg r_n)
        (.assign r_card (.op .add (.reg r_card) (.read a_set (.reg r_i))))) s s' t ∧
      t ≤ 3 + 12 * rem ∧
      s'.regs r_card = X.card ∧
      (∀ a : Arr, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_card → r ≠ r_i → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg r_i) (.reg r_n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hn_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, ?_, fun _ => rfl, fun _ _ _ => rfl⟩
    have htake : (bitSetList X).take k = bitSetList X :=
      List.take_of_length_le (by simp)
    rw [htake, sum_bitSetList] at hrcard
    exact hrcard
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_i) (.reg r_n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hk_w, hn_w, hk_lt, hw]
    have harr_eq : s.arrs a_set = bitSetList X := hset.arr_eq_bitSetList
    have hk_len : k < (s.arrs a_set).length := by rw [hset.1]; exact hk_lt
    let val := (s.arrs a_set)[k]'hk_len
    have hval_le : val ≤ 1 := hset.2.1 ⟨k, hk_lt⟩
    have hval_w : val < 2 ^ w := by omega
    have hk_bl : k < (bitSetList X).length := by rw [length_bitSetList]; exact hk_lt
    have hsum_step : ((bitSetList X).take k).sum + val = ((bitSetList X).take (k + 1)).sum := by
      rw [take_add_one_eq_append_getElem (bitSetList X) k hk_bl, List.sum_append,
        List.sum_singleton]
      simp [val, harr_eq]
    have hnext_le : ((bitSetList X).take (k + 1)).sum ≤ n := by
      rw [sum_take_bitSetList X (k + 1) (by omega)]
      have hle := Finset.card_le_univ (X.filter (fun u : Fin n => u.1 < k + 1))
      simpa using hle
    have hcur_w : ((bitSetList X).take k).sum < 2 ^ w := by omega
    have hnext_w : ((bitSetList X).take (k + 1)).sum < 2 ^ w := by omega
    have heval_add :
        (Expr.op .add (.reg r_card) (.read a_set (.reg r_i))).eval w s =
          some (((bitSetList X).take (k + 1)).sum) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrcard, hcur_w, hri, hk_w,
        hk_len, val, hval_w, hsum_step, hnext_w]
    let s₁ := s.setReg r_card (((bitSetList X).take (k + 1)).sum)
    have hex₁ : Exec w (.assign r_card (.op .add (.reg r_card) (.read a_set (.reg r_i))))
        s s₁ 5 := .assign heval_add
    have hri₁ : s₁.regs r_i = k := by
      simp [s₁, State.setReg, show (r_i : Reg) ≠ r_card from hne_ci.symm, hri]
    have hinc : (Expr.op .add (.reg r_i) (.const 1)).eval w s₁ = some (k + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri₁, hk_w, hw,
        show k + 1 < 2 ^ w by omega]
    let s₂ := s₁.setReg r_i (k + 1)
    have hex₂ : Exec w (.assign r_i (.op .add (.reg r_i) (.const 1))) s₁ s₂ 4 :=
      .assign hinc
    rcases ih (k + 1) (by omega) (s := s₂)
        (hset.of_arr_eq rfl)
        (by simp [s₂, s₁, State.setReg,
          show (r_n : Reg) ≠ r_i from hne_in.symm,
          show (r_n : Reg) ≠ r_card from hne_cn.symm, hrn])
        (by simp [s₂, s₁, State.setReg, show (r_card : Reg) ≠ r_i from hne_ci])
        (by simp [s₂]) with
      ⟨s₃, t₃, hex₃, ht₃, hrcard₃, harr₃, hreg₃⟩
    refine ⟨s₃, 3 + (5 + 4) + t₃,
      .while_true hcond (by omega) (.seq hex₁ hex₂) hex₃,
      by omega, hrcard₃, harr₃,
      fun r hrc hri_ne => by
        rw [hreg₃ r hrc hri_ne]
        simp [s₂, s₁, State.setReg,
          show (r : Reg) ≠ r_i from hri_ne,
          show (r : Reg) ≠ r_card from hrc]⟩

theorem cardBitSetProg_exec {w n : ℕ} (X : Finset (Fin n)) (a_set : ℕ) (r_n r_card r_i : ℕ)
    (hne_ci : r_card ≠ r_i) (hne_cn : r_card ≠ r_n) (hne_in : r_i ≠ r_n)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hset : IsBitSet X a_set s)
    (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (cardBitSetProg a_set (.reg r_n) r_card r_i) s s' t ∧
      t ≤ 12 * n + 7 ∧
      s'.regs r_card = X.card ∧
      (∀ a : Arr, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_card → r ≠ r_i → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg r_card 0
  have hex₁ : Exec w (.assign r_card (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₁.setReg r_i 0
  have hex₂ : Exec w (.assign r_i (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases cardBitSetLoop_exec X a_set r_n r_card r_i hne_ci hne_cn hne_in hw hn_w n 0 (by omega)
      (s := s₂)
      (hset.of_arr_eq rfl)
      (by simp [s₂, s₁, State.setReg,
        show (r_n : Reg) ≠ r_i from hne_in.symm,
        show (r_n : Reg) ≠ r_card from hne_cn.symm, hrn])
      (by simp [s₂, s₁, State.setReg, show (r_card : Reg) ≠ r_i from hne_ci])
      (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hrcard₃, harr₃, hreg₃⟩
  refine ⟨s₃, 2 + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hrcard₃, harr₃,
    fun r hrc hri_ne => by
      rw [hreg₃ r hrc hri_ne]
      simp [s₂, s₁, State.setReg,
        show (r : Reg) ≠ r_i from hri_ne,
        show (r : Reg) ≠ r_card from hrc]⟩

end GraphMinor.Compute
