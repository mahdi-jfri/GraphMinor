module

public import GraphMinor.Compute.GM06Alg511SuccTrace
public import GraphMinor.Compute.Algorithm77Prog
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# RAM traversal of an initial linkage path

For the winding phase of VI (5.11), page 134, follow the successor
words of a successful maximum-flow output. Store visited vertex
labels in a buffer of capacity equal to the vertex count. A source
of a valid path system reaches the sentinel within that many steps.
The proof follows the finite successor trace and uses the verified
buffer append operation. All arrays other than the path buffer are
preserved, including the full drawing data.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Append the current vertex and read its successor from the raw
Menger output in array 1. Registers 40 and 41 hold the vertex and `n`. -/
def gm06Alg511TraceBody : Cmd :=
  .seq (pushBufCmd 12 42 (.reg 40))
    (.assign 40 (.read outArr
      (.op .add (.op .add (.const 1) (.op .mul (.const 2) (.reg 41))) (.reg 40))))

/-- Stop at the sentinel `n`, appending each real path vertex once. -/
def gm06Alg511TraceLoop : Cmd :=
  .while (.op .lt (.reg 40) (.reg 41)) gm06Alg511TraceBody

/-- Allocate the path buffer, then traverse from the supplied source
in register 40. Register 41 supplies the vertex count. -/
def gm06Alg511TraceProg : Cmd :=
  .seq (initBufCmd 12 42 (.reg 41)) gm06Alg511TraceLoop

private theorem trace_loop_exec {w n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} (out : List ℕ)
    (hsys : IsValidPathSystem G A B (decUsed n out) (decPred n out) (decSucc n out))
    (hw : 1 < 2 ^ w) (hword : 1 + 3 * n < 2 ^ w) (hlen : out.length = 1 + 3 * n)
    (fuel : ℕ) : ∀ (u : Fin n), succAt (decSucc n out) fuel u = none →
      ∀ (pre : List ℕ) (s : State), s.arrs outArr = out → s.regs 40 = u.val → s.regs 41 = n →
      IsBufPrefix s 12 42 n pre →
      pre.length + (gm06Alg511SuccVertices n out fuel u.val).length ≤ n →
      ∃ s' t, Exec w gm06Alg511TraceLoop s s' t ∧
        t ≤ 19 * (gm06Alg511SuccVertices n out fuel u.val).length + 3 ∧
        IsBufPrefix s' 12 42 n (pre ++ gm06Alg511SuccVertices n out fuel u.val) ∧
        s'.regs 40 = n ∧ s'.regs 41 = n ∧
        ∀ a ≠ 12, s'.arrs a = s.arrs a := by
  induction fuel with
  | zero => intro u h; simp [succAt] at h
  | succ fuel ih =>
    intro u hterm pre s hout hcur hN hbuf hspace
    have hnfit : n < 2 ^ w := by omega
    have hufit : u.val < 2 ^ w := u.isLt.trans hnfit
    have hcond : (Expr.op .lt (.reg 40) (.reg 41)).eval w s = some 1 := by
      simpa only [u.isLt, ite_true] using GraphMinor.Compute.Crossing.eval_lt
        (GraphMinor.Compute.Crossing.eval_reg hcur hufit)
        (GraphMinor.Compute.Crossing.eval_reg hN hnfit) hw
    have hnonempty : 0 < (gm06Alg511SuccVertices n out (fuel + 1) u.val).length := by
      unfold gm06Alg511SuccVertices
      split <;> simp
    obtain ⟨s₁, t₁, he₁, ht₁, hbuf₁, hregs₁, harr₁⟩ := pushBufCmd_exec
      12 42 (.reg 40) n pre u.val hw hnfit hbuf (by omega)
      (GraphMinor.Compute.Crossing.eval_reg hcur hufit)
    have hcur₁ : s₁.regs 40 = u.val := (hregs₁ 40 (by decide)).trans hcur
    have hN₁ : s₁.regs 41 = n := (hregs₁ 41 (by decide)).trans hN
    have hout₁ : s₁.arrs outArr = out := (harr₁ outArr (by decide)).trans hout
    have hoff : 1 + 2 * n + u.val < out.length := by rw [hlen]; omega
    have hnext : decSucc n out u ≤ n := hsys.succ_le u
    have hnextfit : decSucc n out u < 2 ^ w := hnext.trans_lt hnfit
    have hidx : (Expr.op .add (.op .add (.const 1)
        (.op .mul (.const 2) (.reg 41))) (.reg 40)).eval w s₁ =
        some (1 + 2 * n + u.val) :=
      GraphMinor.Compute.Crossing.eval_add
        (GraphMinor.Compute.Crossing.eval_add
          (GraphMinor.Compute.Crossing.eval_const hw)
          (GraphMinor.Compute.Crossing.eval_mul
            (GraphMinor.Compute.Crossing.eval_const (by omega : 2 < 2 ^ w))
            (GraphMinor.Compute.Crossing.eval_reg hN₁ hnfit) (by omega)) (by omega))
        (GraphMinor.Compute.Crossing.eval_reg hcur₁ hufit) (hoff.trans (by omega))
    have heRead : (Expr.read outArr (.op .add (.op .add (.const 1)
        (.op .mul (.const 2) (.reg 41))) (.reg 40))).eval w s₁ = some (decSucc n out u) := by
      have hbound : 1 + 2 * n + u.val < (s₁.arrs outArr).length := by rw [hout₁]; exact hoff
      have hget : (s₁.arrs outArr)[1 + 2 * n + u.val]'hbound = decSucc n out u := by
        change _ = out.getD (1 + 2 * n + u.val) n
        simp only [hout₁, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hoff, Option.getD_some]
      have he := GraphMinor.Compute.Crossing.eval_read hidx hbound
        (show (s₁.arrs outArr)[1 + 2 * n + u.val]'hbound < 2 ^ w by rw [hget]; exact hnextfit)
      simpa only [hget] using he
    let s₂ := s₁.setReg 40 (decSucc n out u)
    have he₂ : Exec w (.assign 40 (.read outArr (.op .add (.op .add (.const 1)
        (.op .mul (.const 2) (.reg 41))) (.reg 40)))) s₁ s₂ 9 := .assign heRead
    have hbuf₂ : IsBufPrefix s₂ 12 42 n (pre ++ [u.val]) :=
      hbuf₁.of_preserve rfl (by simp [s₂])
    have hN₂ : s₂.regs 41 = n := by simpa [s₂] using hN₁
    have hout₂ : s₂.arrs outArr = out := hout₁
    have harr₂ : ∀ a ≠ 12, s₂.arrs a = s.arrs a := by
      intro a ha
      exact harr₁ a ha
    by_cases hlt : decSucc n out u < n
    · have hterm' : succAt (decSucc n out) fuel ⟨decSucc n out u, hlt⟩ = none := by
        simpa only [succAt, hlt, ↓reduceDIte] using hterm
      have htrace : gm06Alg511SuccVertices n out (fuel + 1) u.val =
          u.val :: gm06Alg511SuccVertices n out fuel (decSucc n out u) := by
        change (if out.getD (1 + 2 * n + u.val) n < n then
          u.val :: gm06Alg511SuccVertices n out fuel (out.getD (1 + 2 * n + u.val) n)
          else [u.val]) = _
        rw [ite_eq_left (show out.getD (1 + 2 * n + u.val) n < n from hlt)]
        rfl
      have hspace' : (pre ++ [u.val]).length +
          (gm06Alg511SuccVertices n out fuel (decSucc n out u)).length ≤ n := by
        rw [htrace] at hspace
        simp only [List.length_append, List.length_cons, List.length_nil] at hspace ⊢
        omega
      obtain ⟨s₃, t₃, he₃, ht₃, hbuf₃, hcur₃, hN₃, harr₃⟩ :=
        ih ⟨decSucc n out u, hlt⟩ hterm' (pre ++ [u.val]) s₂ hout₂
          (by simp [s₂]) hN₂ hbuf₂ hspace'
      refine ⟨s₃, 3 + (t₁ + 9) + t₃,
        .while_true hcond (by decide) (.seq he₁ he₂) he₃, ?_, ?_, hcur₃, hN₃, ?_⟩
      · rw [htrace]
        simp only [List.length_cons]
        change t₃ ≤ 19 * (gm06Alg511SuccVertices n out fuel (decSucc n out u)).length + 3 at ht₃
        simp only [Expr.cost] at ht₁
        omega
      · simpa only [htrace, List.append_assoc, List.singleton_append] using hbuf₃
      · intro a ha
        exact (harr₃ a ha).trans (harr₂ a ha)
    · have hsnext : decSucc n out u = n := by omega
      have htrace : gm06Alg511SuccVertices n out (fuel + 1) u.val = [u.val] := by
        unfold gm06Alg511SuccVertices
        exact ite_eq_right (show ¬ out.getD (1 + 2 * n + u.val) n < n from hlt)
      have hcond₂ : (Expr.op .lt (.reg 40) (.reg 41)).eval w s₂ = some 0 := by
        have hcur₂ : s₂.regs 40 = n := by simp [s₂, hsnext]
        simpa only [lt_self_iff_false, ite_false] using GraphMinor.Compute.Crossing.eval_lt
          (GraphMinor.Compute.Crossing.eval_reg hcur₂ hnfit)
          (GraphMinor.Compute.Crossing.eval_reg hN₂ hnfit) hw
      refine ⟨s₂, 3 + (t₁ + 9) + 3,
        .while_true hcond (by decide) (.seq he₁ he₂) (.while_false hcond₂), ?_, ?_, ?_, hN₂, harr₂⟩
      · rw [htrace]
        simp only [List.length_singleton]
        simp only [Expr.cost] at ht₁
        omega
      · simpa only [htrace] using hbuf₂
      · simp [s₂, hsnext]

/-- The actual RAM traversal writes exactly the source's successor
trace to its buffer, in linear time, preserving all other arrays. -/
theorem gm06Alg511TraceProg_exec {w n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} (out : List ℕ)
    (hsys : IsValidPathSystem G A B (decUsed n out) (decPred n out) (decSucc n out))
    (u : Fin n) (hu : u ∈ pathStarts (decUsed n out) (decPred n out))
    (s : State) (hw : 1 < 2 ^ w) (hword : 1 + 3 * n < 2 ^ w)
    (hlen : out.length = 1 + 3 * n) (hout : s.arrs outArr = out)
    (hcur : s.regs 40 = u.val) (hN : s.regs 41 = n) :
    ∃ s' t, Exec w gm06Alg511TraceProg s s' t ∧ t ≤ 20 * n + 6 ∧
      IsBufPrefix s' 12 42 n (gm06Alg511SuccVertices n out n u.val) ∧
      s'.regs 40 = n ∧ ∀ a ≠ 12, s'.arrs a = s.arrs a := by
  have hnfit : n < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hbuf, hregs, harr⟩ := initBufCmd_exec 12 42 (.reg 41) n
    (s := s) (Nat.two_pow_pos w) (GraphMinor.Compute.Crossing.eval_reg hN hnfit)
  have hterminate := succAt_self_eq_none hsys hu
  have hlength := (gm06Alg511SuccVertices_nodup_length out hsys u hu).2
  obtain ⟨s₂, t₂, he₂, ht₂, hbuf₂, hcur₂, _, harr₂⟩ := trace_loop_exec out hsys hw hword hlen n
    u hterminate [] s₁ ((harr outArr (by decide)).trans hout)
    ((hregs 40 (by decide)).trans hcur) ((hregs 41 (by decide)).trans hN) hbuf
    (by simpa using hlength)
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_, ?_, hcur₂, ?_⟩
  · simp only [Expr.cost] at ht₁
    omega
  · simpa only [List.nil_append] using hbuf₂
  · intro a ha
    exact (harr₂ a ha).trans (harr a ha)

end GraphMinor.Compute
