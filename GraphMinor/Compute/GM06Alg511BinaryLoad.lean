module

public import GraphMinor.Compute.GM06Alg511BinaryDigits
public import GraphMinor.Compute.GM06Alg511BinaryRows
public import GraphMinor.Compute.GM06Alg511SelectField
import Mathlib.Tactic

/-!
# Loading the supplied binary decision input

The nine input fields are the vertex count, ordinary edge ends,
rotation code, two cuff orders, path count, binary numerator,
binary denominator and binary turn-table code. Select those exact
fields into retained arrays. Read the path count as one ordinary
graph word and load only the magnitude digits of the two target
integers into the verified integrality interface.

No large input integer is decoded into a word. Its sign and each
binary digit remain separate words. The exact loading theorem has
linear cost in the supplied code length and retains the whole input.
This is the input-loading step of VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Destination arrays for the nine supplied binary input fields. -/
def gm06Alg511BinaryFieldTargets : List ℕ := [1500, 1230, 1231, 1210, 1211, 1501, 2702, 2703, 2900]

/-- The destination of a supplied field. Only indices below nine
are used by the loader. -/
def gm06Alg511BinaryFieldTarget (i : ℕ) : ℕ := gm06Alg511BinaryFieldTargets.getD i 0

private theorem target_mem (i : ℕ) (hi : i < 9) :
    gm06Alg511BinaryFieldTarget i ∈ gm06Alg511BinaryFieldTargets := by
  interval_cases i <;> decide

private theorem target_ne_zero (i : ℕ) (hi : i < 9) : gm06Alg511BinaryFieldTarget i ≠ 0 := by
  have h := target_mem i hi
  intro he
  rw [he] at h
  exact (by decide : 0 ∉ gm06Alg511BinaryFieldTargets) h

private theorem target_injective {i j : ℕ} (hi : i < 9) (hj : j < 9)
    (he : gm06Alg511BinaryFieldTarget i = gm06Alg511BinaryFieldTarget j) : i = j := by
  have hinj : Function.Injective (fun i : Fin 9 => gm06Alg511BinaryFieldTarget i.val) := by decide
  exact congrArg Fin.val (hinj (show gm06Alg511BinaryFieldTarget (⟨i, hi⟩ : Fin 9).val =
    gm06Alg511BinaryFieldTarget (⟨j, hj⟩ : Fin 9).val from he))

/-- Select the first n supplied fields into their fixed retained
arrays. The complete input remains in array zero. -/
def gm06Alg511BinaryLoadFieldsProg : ℕ → Cmd
  | 0 => .skip
  | n + 1 => .seq (gm06Alg511BinaryLoadFieldsProg n)
      (gm06Alg511SelectFieldProg 0 (gm06Alg511BinaryFieldTarget n) n)

/-- The exact selected rows and unchanged other arrays after any
prefix of the fixed nine-field loader. -/
theorem gm06Alg511BinaryLoadFieldsProg_exec {w : ℕ} (x : GM06Alg511BinaryInput) (n : ℕ) (hn : n ≤ 9)
    (s : State) (hw : 1 < 2 ^ w) (hA : s.arrs 0 = x.words)
    (hfit : x.words.length < 2 ^ w) (hwords : ∀ word ∈ x.words, word < 2 ^ w) :
    ∃ t u, Exec w (gm06Alg511BinaryLoadFieldsProg n) s t u ∧
      u ≤ 1 + n * (180 + 22 * x.words.length) ∧
      (∀ i (hi : i < n), t.arrs (gm06Alg511BinaryFieldTarget i) = x.rows[i]'(by
        change i < 9; omega)) ∧
      ∀ a ∉ gm06Alg511BinaryFieldTargets, t.arrs a = s.arrs a := by
  induction n with
  | zero => exact ⟨s, 1, .skip s, by simp, fun i hi => (Nat.not_lt_zero _ hi).elim, fun _ _ => rfl⟩
  | succ n ih =>
    have hn9 : n < 9 := by omega
    obtain ⟨st, u₁, he₁, ht₁, hrows, hkeep₁⟩ := ih (by omega)
    have hinput : st.arrs 0 = x.words := (hkeep₁ 0 (by decide)).trans hA
    have hnRows : n < x.rows.length := hn9
    obtain ⟨t, u₂, he₂, ht₂, hrow, hkeep₂⟩ := gm06Alg511SelectFieldProg_exec 0 (gm06Alg511BinaryFieldTarget n)
      (target_ne_zero n hn9).symm x.rows n hnRows st hw hinput hfit hwords
    have hlen : x.rows[n].length ≤ x.words.length := gm06Alg511_encoded_row_length_le (List.getElem_mem hnRows)
    have htcol : u₂ ≤ 180 + 22 * x.words.length := by omega
    refine ⟨t, u₁ + u₂, .seq he₁ he₂, ?_, ?_, ?_⟩
    · calc
        u₁ + u₂ ≤ (1 + n * (180 + 22 * x.words.length)) + (180 + 22 * x.words.length) := Nat.add_le_add ht₁ htcol
        _ = 1 + (n + 1) * (180 + 22 * x.words.length) := by ring
    · intro i hi
      by_cases hin : i < n
      · exact (hkeep₂ _ (fun he => (Nat.ne_of_lt hin) (target_injective (by omega) hn9 he))).trans (hrows i hin)
      · have heq : i = n := by omega
        subst i
        exact hrow
    · intro a ha
      exact (hkeep₂ a (fun he => ha (he ▸ target_mem n hn9))).trans (hkeep₁ a ha)

/-- Read the graph path count, then expose the two target signs
and magnitude rows without interpreting their integer magnitudes. -/
def gm06Alg511BinaryLoadTargetsProg : Cmd :=
  .seq (.assign 52 (.read 1501 (.const 0)))
    (.seq (gm06Alg511LoadBinaryRowProg 2702 2700 2704)
      (gm06Alg511LoadBinaryRowProg 2703 2701 2705))

/-- Load all drawing and binary integer fields from the complete
supplied input, then prepare the binary integrality operands. -/
def gm06Alg511BinaryLoadProg : Cmd :=
  .seq (gm06Alg511BinaryLoadFieldsProg 9) gm06Alg511BinaryLoadTargetsProg

/-- Every binary input integer row consists exactly of its sign
bit followed by its supplied binary magnitude digits. -/
theorem GM06Alg511BinaryInteger.words_eq (z : GM06Alg511BinaryInteger) :
    z.words = z.negative.toNat :: z.digits.map Bool.toNat := by rfl

/-- All nine selected fields remain after reading the graph count
and the target sign/digit operands. The complete supplied code is
retained, and the cost is linear in its word (hence bit) length. -/
theorem gm06Alg511BinaryLoadProg_exec {w : ℕ} (x : GM06Alg511BinaryInput) (s : State)
    (hw : 3 < 2 ^ w) (hA : s.arrs 0 = x.words)
    (hfit : x.words.length + 2 < 2 ^ w) (hcount : x.pathCount < 2 ^ w)
    (hwords : ∀ word ∈ x.words, word < 2 ^ w) :
    ∃ t u, Exec w gm06Alg511BinaryLoadProg s t u ∧ u ≤ 2000 + 300 * x.words.length ∧
      (∀ i : Fin 9, t.arrs (gm06Alg511BinaryFieldTarget i.val) = x.rows[i.val]'i.isLt) ∧
      t.regs 52 = x.pathCount ∧ t.regs 2704 = x.numerator.negative.toNat ∧ t.regs 2705 = x.denominator.negative.toNat ∧
      t.arrs 2700 = x.numerator.digits.map Bool.toNat ∧ t.arrs 2701 = x.denominator.digits.map Bool.toNat ∧
      t.arrs 0 = x.words ∧
      ∀ a ∉ gm06Alg511BinaryFieldTargets ++ [2700, 2701], t.arrs a = s.arrs a := by
  obtain ⟨s₁, u₁, he₁, ht₁, hfields₁, hkeep₁⟩ := gm06Alg511BinaryLoadFieldsProg_exec x 9 (by rfl) s (by omega) hA (by omega) hwords
  have hk₁ : s₁.arrs 1501 = [x.pathCount] := hfields₁ 5 (by decide)
  have hnum₁ : s₁.arrs 2702 = x.numerator.words := hfields₁ 6 (by decide)
  have hden₁ : s₁.arrs 2703 = x.denominator.words := hfields₁ 7 (by decide)
  let s₂ := s₁.setReg 52 x.pathCount
  have he₂ : Exec w (.assign 52 (.read 1501 (.const 0))) s₁ s₂ 3 :=
    .assign ((Crossing.eval_read (a := 1501) (Crossing.eval_const (Nat.two_pow_pos w))
      (by rw [hk₁]; simp) (by simpa only [hk₁, List.getElem_cons_zero] using hcount)).trans (by simp [hk₁]))
  have hnumLen : (x.numerator.digits.map Bool.toNat).length + 2 < 2 ^ w := by
    have hh := gm06Alg511_encoded_row_length_le (rows := x.rows) (row := x.numerator.words) (by simp [GM06Alg511BinaryInput.rows])
    change _ ≤ x.words.length at hh
    rw [GM06Alg511BinaryInteger.words_eq, List.length_cons] at hh
    exact (Nat.add_le_add_right (by omega : (x.numerator.digits.map Bool.toNat).length ≤ x.words.length) 2).trans_lt hfit
  have hdenLen : (x.denominator.digits.map Bool.toNat).length + 2 < 2 ^ w := by
    have hh := gm06Alg511_encoded_row_length_le (rows := x.rows) (row := x.denominator.words) (by simp [GM06Alg511BinaryInput.rows])
    change _ ≤ x.words.length at hh
    rw [GM06Alg511BinaryInteger.words_eq, List.length_cons] at hh
    exact (Nat.add_le_add_right (by omega : (x.denominator.digits.map Bool.toNat).length ≤ x.words.length) 2).trans_lt hfit
  have hbool (v : Bool) : v.toNat < 2 := by cases v <;> decide
  have hdigits (digits : List Bool) : ∀ d ∈ digits.map Bool.toNat, d < 2 := by
    intro d hd
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hd
    exact hbool v
  obtain ⟨s₃, u₃, he₃, ht₃, hk₃, hsign₃, ha₃⟩ := gm06Alg511LoadBinaryRowProg_exec (w := w) 2702 2700 2704 (by decide) (by decide)
    x.numerator.negative.toNat (x.numerator.digits.map Bool.toNat) s₂ (by omega) (by omega) (hbool _) (hdigits _)
      (by simpa only [s₂, State.setReg_arrs, GM06Alg511BinaryInteger.words_eq] using hnum₁)
  obtain ⟨t, u₄, he₄, ht₄, hk₄, hsign₄, ha₄⟩ := gm06Alg511LoadBinaryRowProg_exec (w := w) 2703 2701 2705 (by decide) (by decide)
    x.denominator.negative.toNat (x.denominator.digits.map Bool.toNat) s₃ (by omega) (by omega) (hbool _) (hdigits _)
      (by rw [hk₃.2 2703 (by decide)]; simpa only [s₂, State.setReg_arrs, GM06Alg511BinaryInteger.words_eq] using hden₁)
  have hkeep : Keeps [2704, 2705, 313] [2700, 2701] s₂ t :=
    (hk₃.mono (by simp) (by simp)).trans hk₄ (by simp) (by simp)
  refine ⟨t, u₁ + (3 + (u₃ + u₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)), ?_, ?_,
    (hkeep.1 52 (by decide)).trans (by simp [s₂]), (hk₄.1 2704 (by decide)).trans hsign₃, hsign₄,
    (hk₄.2 2700 (by decide)).trans ha₃, ha₄, ?_, ?_⟩
  · have hnum := gm06Alg511_encoded_row_length_le (rows := x.rows) (row := x.numerator.words) (by simp [GM06Alg511BinaryInput.rows])
    have hden := gm06Alg511_encoded_row_length_le (rows := x.rows) (row := x.denominator.words) (by simp [GM06Alg511BinaryInput.rows])
    change x.numerator.words.length ≤ x.words.length at hnum
    change x.denominator.words.length ≤ x.words.length at hden
    rw [GM06Alg511BinaryInteger.words_eq, List.length_cons] at hnum hden
    omega
  · intro i
    rw [hkeep.2 _ (by
      have hmem := target_mem i.val i.isLt
      simp only [gm06Alg511BinaryFieldTargets, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide)]
    exact hfields₁ i.val i.isLt
  · exact (hkeep.2 0 (by decide)).trans ((hkeep₁ 0 (by decide)).trans hA)
  · intro a ha
    exact (hkeep.2 a (fun hm => ha (List.mem_append.mpr (Or.inr hm)))).trans
      (hkeep₁ a (fun hm => ha (List.mem_append.mpr (Or.inl hm))))

end GraphMinor.Compute
