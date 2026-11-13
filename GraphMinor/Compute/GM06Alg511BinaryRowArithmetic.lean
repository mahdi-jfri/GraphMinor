module

public import GraphMinor.Compute.GM06Alg511BinaryRows
public import GraphMinor.Compute.GM06Alg511BinaryCompare
import Mathlib.Tactic

/-!
# Arithmetic on retained signed binary rows

The winding loop retains its large values as complete sign/digit
rows. Load two supplied rows into the verified arithmetic interface.
For addition, store the exact result back as a complete row. For
comparison, retain the returned Boolean. All operand rows outside
the arithmetic workspace remain available throughout the call.
These concrete commands provide the comparison and increment of
VI (5.11), page 134, without one-word magnitude assumptions.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Add two retained signed rows and store their signed binary sum. -/
def gm06Alg511BinaryRowAddProg (left right dst : ℕ) : Cmd :=
  .seq (gm06Alg511LoadBinaryRowProg left 2000 2400)
    (.seq (gm06Alg511LoadBinaryRowProg right 2001 2401)
      (.seq gm06Alg511BinarySignedAddProg (gm06Alg511StoreBinaryRowProg 2002 dst 2402)))

/-- The actual retained-row addition returns the exact signed sum,
with binary output and linear digit-count cost. The destination may
be either source row. Other rows outside the workspace are retained. -/
theorem gm06Alg511BinaryRowAddProg_exec {w : ℕ} (left right dst : ℕ)
    (hleft : left ∉ [2000, 2001, 2002, 2003, 2004, 2005])
    (hright : right ∉ [2000, 2001, 2002, 2003, 2004, 2005]) (hdst : 2002 ≠ dst)
    (a b : List ℕ) (sa sb : ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : max a.length b.length + 2 < 2 ^ w)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2) (hsa : sa < 2) (hsb : sb < 2)
    (hA : s.arrs left = sa :: a) (hB : s.arrs right = sb :: b) :
    ∃ t u out sign, Exec w (gm06Alg511BinaryRowAddProg left right dst) s t u ∧
      u ≤ 400 + 350 * (a.length + b.length + 1) ∧
      Keeps [0, 20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2400, 2401, 2402, 2404]
        [2000, 2001, 2002, 2003, 2004, 2005, dst] s t ∧
      t.arrs dst = sign :: out ∧ sign < 2 ∧ out.length ≤ max a.length b.length + 1 ∧
      (∀ d ∈ out, d < 2) ∧
      gm06Alg511BinaryRowValue (sign :: out) = gm06Alg511BinaryRowValue (sa :: a) + gm06Alg511BinaryRowValue (sb :: b) := by
  have hleft0 : left ≠ 2000 := fun hh => hleft (by simp [hh])
  have hright0 : right ≠ 2000 := fun hh => hright (by simp [hh])
  have hright1 : right ≠ 2001 := fun hh => hright (by simp [hh])
  obtain ⟨s₁, u₁, he₁, ht₁, hk₁, hsa₁, ha₁⟩ := gm06Alg511LoadBinaryRowProg_exec (w := w) left 2000 2400
    hleft0 (by decide) sa a s (by omega) (by omega) hsa habits hA
  obtain ⟨s₂, u₂, he₂, ht₂, hk₂, hsb₂, hb₂⟩ := gm06Alg511LoadBinaryRowProg_exec (w := w) right 2001 2401
    hright1 (by decide) sb b s₁ (by omega) (by omega) hsb hbbits ((hk₁.2 right (by simpa using hright0)).trans hB)
  obtain ⟨s₃, u₃, out, sign, he₃, ht₃, hk₃, hout, hsign, hsignBit, hlen, hbits, hval⟩ :=
    gm06Alg511BinarySignedAddProg_exec a b sa sb s₂ hw (by omega) habits hbbits hsa hsb
      ((hk₂.2 2000 (by decide)).trans ha₁) hb₂ ((hk₂.1 2400 (by decide)).trans hsa₁) hsb₂
  obtain ⟨t, u₄, he₄, ht₄, hk₄, hstored⟩ := gm06Alg511StoreBinaryRowProg_exec (w := w) 2002 dst 2402 hdst sign out s₃
    (by omega) (by omega) hsignBit hbits hout hsign
  let R := [0, 20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2400, 2401, 2402, 2404]
  let A := [2000, 2001, 2002, 2003, 2004, 2005, dst]
  have hk : Keeps R A s t := (((hk₁.mono (by simp [R]) (by simp [A])).trans hk₂ (by simp [R]) (by simp [A])).trans hk₃
    (by simp [R]) (by simp [A])).trans hk₄ (by simp [R]) (by simp [A])
  refine ⟨t, u₁ + (u₂ + (u₃ + u₄)), out, sign, .seq he₁ (.seq he₂ (.seq he₃ he₄)), ?_, hk,
    hstored, hsignBit, hlen, hbits, hval⟩
  have hm : max a.length b.length ≤ a.length + b.length := by omega
  omega

/-- Compare two retained signed binary rows using the exact signed
subtraction and zero scan, retaining both supplied source rows. -/
def gm06Alg511BinaryRowLessProg (left right : ℕ) : Cmd :=
  .seq (gm06Alg511LoadBinaryRowProg left 2000 2400)
    (.seq (gm06Alg511LoadBinaryRowProg right 2001 2401) gm06Alg511BinarySignedLessProg)

/-- Retained-row comparison has linear digit-count cost and returns
one exactly for strict integer comparison, including signed zeros. -/
theorem gm06Alg511BinaryRowLessProg_exec {w : ℕ} (left right : ℕ)
    (hleft : left ∉ [2000, 2001, 2002, 2003, 2004, 2005])
    (hright : right ∉ [2000, 2001, 2002, 2003, 2004, 2005])
    (a b : List ℕ) (sa sb : ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : max a.length b.length + 2 < 2 ^ w)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2) (hsa : sa < 2) (hsb : sb < 2)
    (hA : s.arrs left = sa :: a) (hB : s.arrs right = sb :: b) :
    ∃ t u flag, Exec w (gm06Alg511BinaryRowLessProg left right) s t u ∧
      u ≤ 400 + 350 * (a.length + b.length + 1) ∧
      Keeps [0, 20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2400, 2401, 2402, 2404, 2410, 2411]
        [2000, 2001, 2002, 2003, 2004, 2005] s t ∧ t.regs 0 = flag ∧ flag < 2 ∧
      (flag = 1 ↔ gm06Alg511BinaryRowValue (sa :: a) < gm06Alg511BinaryRowValue (sb :: b)) := by
  have hleft0 : left ≠ 2000 := fun hh => hleft (by simp [hh])
  have hright0 : right ≠ 2000 := fun hh => hright (by simp [hh])
  have hright1 : right ≠ 2001 := fun hh => hright (by simp [hh])
  obtain ⟨s₁, u₁, he₁, ht₁, hk₁, hsa₁, ha₁⟩ := gm06Alg511LoadBinaryRowProg_exec (w := w) left 2000 2400
    hleft0 (by decide) sa a s (by omega) (by omega) hsa habits hA
  obtain ⟨s₂, u₂, he₂, ht₂, hk₂, hsb₂, hb₂⟩ := gm06Alg511LoadBinaryRowProg_exec (w := w) right 2001 2401
    hright1 (by decide) sb b s₁ (by omega) (by omega) hsb hbbits ((hk₁.2 right (by simpa using hright0)).trans hB)
  obtain ⟨t, u₃, flag, he₃, ht₃, hk₃, hflag, hbit, hiff⟩ :=
    gm06Alg511BinarySignedLessProg_exec a b sa sb s₂ hw (by omega) habits hbbits hsa hsb
      ((hk₂.2 2000 (by decide)).trans ha₁) hb₂ ((hk₂.1 2400 (by decide)).trans hsa₁) hsb₂
  let R := [0, 20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2400, 2401, 2402, 2404, 2410, 2411]
  let A := [2000, 2001, 2002, 2003, 2004, 2005]
  have hk : Keeps R A s t := ((hk₁.mono (by simp [R]) (by simp [A])).trans hk₂ (by simp [R]) (by simp [A])).trans hk₃
    (by simp [R]) (by simp [A])
  refine ⟨t, u₁ + (u₂ + u₃), flag, .seq he₁ (.seq he₂ he₃), ?_, hk, hflag, hbit, hiff⟩
  have hm : max a.length b.length ≤ a.length + b.length := by omega
  omega

/-- Multiply retained signed rows and store their exact signed
binary product. The destination may be either supplied source. -/
def gm06Alg511BinaryRowMultiplyProg (left right dst : ℕ) : Cmd :=
  .seq (gm06Alg511LoadBinaryRowProg left 2000 2400)
    (.seq (gm06Alg511LoadBinaryRowProg right 2001 2401)
      (.seq gm06Alg511BinarySignedMultiplyProg (gm06Alg511StoreBinaryRowProg 2002 dst 2402)))

/-- Retained-row multiplication computes the exact product with
binary output, additive width and quadratic digit-count time. -/
theorem gm06Alg511BinaryRowMultiplyProg_exec {w : ℕ} (left right dst : ℕ)
    (hleft : left ∉ [2000, 2001, 2002, 2300, 2301, 2302])
    (hright : right ∉ [2000, 2001, 2002, 2300, 2301, 2302]) (hdst : 2002 ≠ dst)
    (a b : List ℕ) (sa sb : ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsize : a.length + b.length + 2 < 2 ^ w)
    (habits : ∀ d ∈ a, d < 2) (hbbits : ∀ d ∈ b, d < 2) (hsa : sa < 2) (hsb : sb < 2)
    (hA : s.arrs left = sa :: a) (hB : s.arrs right = sb :: b) :
    ∃ t u out sign, Exec w (gm06Alg511BinaryRowMultiplyProg left right dst) s t u ∧
      u ≤ 700 * (a.length + b.length + 1) ^ 2 ∧
      Keeps [20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2233, 2235, 2400, 2401, 2402]
        [2000, 2001, 2002, 2300, 2301, 2302, dst] s t ∧
      t.arrs dst = sign :: out ∧ sign < 2 ∧ out.length ≤ a.length + b.length ∧
      (∀ d ∈ out, d < 2) ∧
      gm06Alg511BinaryRowValue (sign :: out) = gm06Alg511BinaryRowValue (sa :: a) * gm06Alg511BinaryRowValue (sb :: b) := by
  have hleft0 : left ≠ 2000 := fun hh => hleft (by simp [hh])
  have hright0 : right ≠ 2000 := fun hh => hright (by simp [hh])
  have hright1 : right ≠ 2001 := fun hh => hright (by simp [hh])
  obtain ⟨s₁, u₁, he₁, ht₁, hk₁, hsa₁, ha₁⟩ := gm06Alg511LoadBinaryRowProg_exec (w := w) left 2000 2400
    hleft0 (by decide) sa a s (by omega) (by omega) hsa habits hA
  obtain ⟨s₂, u₂, he₂, ht₂, hk₂, hsb₂, hb₂⟩ := gm06Alg511LoadBinaryRowProg_exec (w := w) right 2001 2401
    hright1 (by decide) sb b s₁ (by omega) (by omega) hsb hbbits ((hk₁.2 right (by simpa using hright0)).trans hB)
  obtain ⟨s₃, u₃, out, sign, he₃, ht₃, hk₃, hout, hsign, hsignBit, hlen, hbits, hval⟩ :=
    gm06Alg511BinarySignedMultiplyProg_exec a b sa sb s₂ hw (by omega) habits hbbits hsa hsb
      ((hk₂.2 2000 (by decide)).trans ha₁) hb₂ ((hk₂.1 2400 (by decide)).trans hsa₁) hsb₂
  obtain ⟨t, u₄, he₄, ht₄, hk₄, hstored⟩ := gm06Alg511StoreBinaryRowProg_exec (w := w) 2002 dst 2402 hdst sign out s₃
    (by omega) (by omega) hsignBit hbits hout hsign
  let R := [20, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2233, 2235, 2400, 2401, 2402]
  let A := [2000, 2001, 2002, 2300, 2301, 2302, dst]
  have hk : Keeps R A s t := (((hk₁.mono (by simp [R]) (by simp [A])).trans hk₂ (by simp [R]) (by simp [A])).trans hk₃
    (by simp [R]) (by simp [A])).trans hk₄ (by simp [R]) (by simp [A])
  refine ⟨t, u₁ + (u₂ + (u₃ + u₄)), out, sign, .seq he₁ (.seq he₂ (.seq he₃ he₄)), ?_, hk,
    hstored, hsignBit, hlen, hbits, hval⟩
  have hp : 1 ≤ a.length + b.length + 1 := by omega
  nlinarith only [ht₁, ht₂, ht₃, ht₄, hlen, hp]

end GraphMinor.Compute
