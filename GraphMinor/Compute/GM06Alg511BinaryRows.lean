module

public import GraphMinor.Compute.GM06Alg511BinarySigned
public import GraphMinor.Compute.GM06SpliceRotations
import Mathlib.Tactic

/-!
# Loading and storing signed binary rows

The supplied integer rows contain a sign followed by their actual
binary digits. Arithmetic programs use a sign register and a digit
array. Load these fields by reading the first word and copying the
remaining slice. Store an arithmetic result by allocating its row,
writing the sign, and copying all magnitude digits. Both operations
have linear cost in digit count and retain all other arrays.
The row value below is only a mathematical interpretation. No
program converts a target or edge-turn magnitude to a machine word.
These adapters are used in VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Mathematical interpretation of a sign followed by binary digits. -/
def gm06Alg511BinaryRowValue (row : List ℕ) : ℤ :=
  gm06Alg511BinarySignedValue (row.headD 0) row.tail

/-- A supplied integer row has exactly its supplied integer value. -/
theorem gm06Alg511BinaryRowValue_integer (z : GM06Alg511BinaryInteger) :
    gm06Alg511BinaryRowValue z.words = z.value := gm06Alg511BinarySignedValue_integer z

/-- Load a sign register and a separate digit array from the plain
integer row, using only its first word and its remaining slice. -/
def gm06Alg511LoadBinaryRowProg (src dst signReg : ℕ) : Cmd :=
  .seq (.assign signReg (.read src (.const 0)))
    (.seq (.alloc dst (.op .sub (.len src) (.const 1)))
      (gm06RotationSliceProg src dst (.op .sub (.len src) (.const 1)) (.const 1) (.const 0)))

/-- Loading the actual signed row is exact and linear in its digit
count. Source rows and all other arrays are preserved. -/
theorem gm06Alg511LoadBinaryRowProg_exec {w : ℕ} (src dst signReg : ℕ)
    (hne : src ≠ dst) (hr : signReg ≠ 313) (sign : ℕ) (digits : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hsize : digits.length + 1 < 2 ^ w)
    (hsign : sign < 2) (hbits : ∀ d ∈ digits, d < 2) (ha : s.arrs src = sign :: digits) :
    ∃ t u, Exec w (gm06Alg511LoadBinaryRowProg src dst signReg) s t u ∧
      u ≤ 30 + 25 * digits.length ∧ Keeps [signReg, 313] [dst] s t ∧
      t.regs signReg = sign ∧ t.arrs dst = digits := by
  have hd : digits.length < 2 ^ w := by omega
  have hs : sign < 2 ^ w := hsign.trans_le (by omega)
  have hwords : ∀ d ∈ sign :: digits, d < 2 ^ w := by
    intro d hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hs
    · exact (hbits d hm).trans_le (by omega)
  have hread : (Expr.read src (.const 0)).eval w s = some sign := by
    exact (Crossing.eval_read (a := src) (Crossing.eval_const (Nat.two_pow_pos w))
      (by rw [ha]; exact Nat.zero_lt_succ _) (by simpa only [ha, List.getElem_cons_zero] using hs)).trans (by simp [ha])
  let s₁ := s.setReg signReg sign
  let s₂ := s₁.setArr dst (List.replicate digits.length 0)
  have he₁ : Exec w (.assign signReg (.read src (.const 0))) s s₁ 3 := .assign hread
  have hlen : (Expr.len src).eval w s₁ = some (digits.length + 1) := Crossing.eval_len ha hsize
  have he₂ : Exec w (.alloc dst (.op .sub (.len src) (.const 1))) s₁ s₂ (3 + digits.length) := by
    simpa only [Nat.add_sub_cancel, Expr.cost, Nat.reduceAdd] using Exec.alloc (a := dst)
      (Crossing.eval_sub hlen (Crossing.eval_const hw))
  have ha₂ : s₂.arrs src = sign :: digits := by
    simpa only [s₂, s₁, State.setArr_arrs_ne _ _ hne, State.setReg_arrs] using ha
  obtain ⟨t, u, he₃, ht₃, hk₃, hout⟩ := gm06RotationSliceProg_exec (w := w) src dst hne
    (.op .sub (.len src) (.const 1)) (.const 1) (.const 0) (sign :: digits) [] 1 digits.length digits.length s₂
    hw (by simpa only [List.length_cons] using hsize) (by simp only [List.length_cons]; omega) hwords le_rfl (by simpa using hd) ha₂ (by simp [s₂])
    (fun st hk => by
      have hh := Crossing.eval_sub (Crossing.eval_len ((hk.2 src (by simpa only [List.mem_singleton] using hne)).trans ha₂) hsize)
        (Crossing.eval_const hw)
      simpa only [List.length_cons, Nat.add_sub_cancel] using hh)
    (fun st hk => Crossing.eval_const hw)
    (fun st hk => Crossing.eval_const (Nat.two_pow_pos w))
  have hk₂ : Keeps [signReg, 313] [dst] s s₂ :=
    ((Keeps.refl _ _ s).setReg (by simp) sign).setArr (by simp) _
  refine ⟨t, 3 + (3 + digits.length + u), .seq he₁ (.seq he₂ he₃), ?_,
    hk₂.trans hk₃ (by simp) (by simp), ?_, ?_⟩
  · simp only [Expr.cost] at ht₃
    omega
  · exact (hk₃.1 signReg (by simpa only [List.mem_singleton] using hr)).trans (by simp [s₂, s₁])
  · simpa only [List.drop_succ_cons, List.drop_zero, List.take_length, Nat.sub_self,
      List.replicate_zero, List.nil_append, List.append_nil] using hout

/-- Store a computed sign and magnitude as one plain binary row. -/
def gm06Alg511StoreBinaryRowProg (src dst signReg : ℕ) : Cmd :=
  .seq (.alloc dst (.op .add (.len src) (.const 1)))
    (.seq (.write dst (.const 0) (.reg signReg))
      (gm06RotationSliceProg src dst (.len src) (.const 0) (.const 1)))

/-- Storing an arithmetic result writes exactly its sign and every
binary magnitude digit, in linear time, retaining all other arrays. -/
theorem gm06Alg511StoreBinaryRowProg_exec {w : ℕ} (src dst signReg : ℕ) (hne : src ≠ dst)
    (sign : ℕ) (digits : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hsize : digits.length + 1 < 2 ^ w)
    (hsign : sign < 2) (hbits : ∀ d ∈ digits, d < 2)
    (ha : s.arrs src = digits) (hs : s.regs signReg = sign) :
    ∃ t u, Exec w (gm06Alg511StoreBinaryRowProg src dst signReg) s t u ∧
      u ≤ 30 + 25 * digits.length ∧ Keeps [313] [dst] s t ∧ t.arrs dst = sign :: digits := by
  have hd : digits.length < 2 ^ w := by omega
  let s₁ := s.setArr dst (List.replicate (digits.length + 1) 0)
  let s₂ := s₁.writeArr dst 0 sign
  have he₁ : Exec w (.alloc dst (.op .add (.len src) (.const 1))) s s₁ (digits.length + 4) := by
    simpa only [Expr.cost, Nat.reduceAdd, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Exec.alloc (a := dst) (Crossing.eval_add (Crossing.eval_len ha hd) (Crossing.eval_const hw) hsize)
  have he₂ : Exec w (.write dst (.const 0) (.reg signReg)) s₁ s₂ 3 :=
    .write (Crossing.eval_const (Nat.two_pow_pos w)) (Crossing.eval_reg hs (hsign.trans_le (by omega)))
      (by simp [s₁])
  have ha₂ : s₂.arrs src = digits := by
    simpa only [s₂, s₁, State.writeArr_arrs_ne _ _ _ hne, State.setArr_arrs_ne _ _ hne] using ha
  have hdst : s₂.arrs dst = [sign] ++ List.replicate digits.length 0 := by
    simp [s₂, s₁, List.replicate_succ]
  obtain ⟨t, u, he₃, ht₃, hk₃, hout⟩ := gm06RotationSliceProg_exec (w := w) src dst hne
    (.len src) (.const 0) (.const 1) digits [sign] 0 digits.length digits.length s₂ hw hd (by simp)
    (fun d hm => (hbits d hm).trans_le (by omega)) le_rfl (by simpa only [List.length_singleton, Nat.add_comm] using hsize) ha₂ hdst
    (fun st hk => Crossing.eval_len ((hk.2 src (by simpa only [List.mem_singleton] using hne)).trans ha₂) hd)
    (fun st hk => Crossing.eval_const (Nat.two_pow_pos w))
    (fun st hk => by simpa only [List.length_singleton] using Crossing.eval_const (w := w) (s := st) hw)
  have hk₂ : Keeps [313] [dst] s s₂ := ((Keeps.refl _ _ s).setArr (by simp) _).writeArr (by simp) _ _
  refine ⟨t, digits.length + 4 + (3 + u), .seq he₁ (.seq he₂ he₃), ?_, hk₂.trans hk₃ (by simp) (by simp), ?_⟩
  · simp only [Expr.cost] at ht₃
    omega
  · simpa only [List.drop_zero, List.take_length, Nat.sub_self, List.replicate_zero,
      List.append_nil, List.singleton_append] using hout

end GraphMinor.Compute
