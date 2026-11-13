module

public import GraphMinor.Compute.TwoPathsRotate
import GraphMinor.Compute.Join13Adapter72Defs

/-!
# Writing a part of a model certificate

The (7.2) adapter writes mapped edge endpoints and branch-set bits into a buffer.
This loop fills one part of that buffer. Its value expression may read input
arrays, while the loop changes only its counter and destination array.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Fill a consecutive part of a buffer from a word expression. -/
def fillModelPart72Prog (r_i : Reg) (count offset value : Expr) (dst : Arr) : Cmd :=
  .seq (.assign r_i (.const 0))
    (forUp r_i count (.write dst (.op .add offset (.reg r_i)) value))

private theorem set_modelPart72 (pre words : List ℕ) (rem i : ℕ)
    (hi : i < words.length) (hrem : words.length ≤ rem) :
    (pre ++ words.take i ++ List.replicate (rem - i) 0).set (pre.length + i) words[i] =
      pre ++ words.take (i + 1) ++ List.replicate (rem - (i + 1)) 0 := by
  have hlen : (pre ++ words.take i).length = pre.length + i := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  rw [← hlen, list_set_append_replicate_zero_step _ _ _ (by omega),
    List.take_succ_eq_append_getElem hi]
  simp only [List.append_assoc, Nat.sub_sub]

/-- The buffer-filling loop writes exactly the supplied words and preserves all
registers except its counter and all arrays except its destination. -/
theorem fillModelPart72Prog_exec {w : ℕ} (r_i : Reg) (count offset value : Expr)
    (dst : Arr) (words pre : List ℕ) (rem : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hrem : words.length ≤ rem)
    (hcap : pre.length + rem < 2 ^ w)
    (hcount : ∀ st, Keeps [r_i] [dst] s st → count.eval w st = some words.length)
    (hoff : ∀ st, Keeps [r_i] [dst] s st → offset.eval w st = some pre.length)
    (hvalue : ∀ st i (hi : i < words.length), Keeps [r_i] [dst] s st →
      st.regs r_i = i → value.eval w st = some words[i])
    (hdst : s.arrs dst = pre ++ List.replicate rem 0) :
    ∃ s' t, Exec w (fillModelPart72Prog r_i count offset value dst) s s' t ∧
      t ≤ 4 + count.cost + words.length * (count.cost + offset.cost + value.cost + 9) ∧
      Keeps [r_i] [dst] s s' ∧
      s'.arrs dst = pre ++ words ++ List.replicate (rem - words.length) 0 ∧
      s'.regs r_i = words.length := by
  let s₁ := s.setReg r_i 0
  have hex₁ : Exec w (.assign r_i (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord])
  let I : ℕ → State → Prop := fun i st =>
    Keeps [r_i] [dst] s st ∧ st.regs r_i = i ∧
      st.arrs dst = pre ++ words.take i ++ List.replicate (rem - i) 0
  have hinit : I 0 s₁ := by
    refine ⟨(Keeps.refl _ _ s).setReg (by simp) _, by simp [s₁], ?_⟩
    simp [s₁, hdst]
  obtain ⟨s', t, hex, ht, hk, hr, hd⟩ := forUp_pot I (fun _ => 0)
    words.length (offset.cost + value.cost + 3) (r_i := r_i) (hi := count)
    (body := .write dst (.op .add offset (.reg r_i)) value) hw (by omega)
    (fun i _ st hst => ⟨hst.2.1, hcount st hst.1⟩)
    (fun i hi st hst => by
      obtain ⟨hk, hr, hd⟩ := hst
      have hidx : (.op .add offset (.reg r_i) : Expr).eval w st = some (pre.length + i) := by
        simp [Expr.eval, hoff st hk, hr, BinOp.eval, BinOp.raw, checkWord,
          show i < 2 ^ w by omega,
          show pre.length + i < 2 ^ w by omega]
      refine ⟨st.writeArr dst (pre.length + i) words[i], _,
        .write hidx (hvalue st i hi hk hr) (by rw [hd]; simp; omega), ?_,
        ⟨?_, by simp, ?_⟩, by simp [hr]⟩
      · simp only [Expr.cost]; omega
      · exact (hk.writeArr (by simp) _ _).setReg (by simp) _
      · simp only [State.setReg_arrs, State.writeArr_arrs_self, hd]
        exact set_modelPart72 pre words rem i hi hrem)
    0 (Nat.zero_le _) s₁ hinit
  refine ⟨s', 2 + t, .seq hex₁ hex, ?_, hk, ?_, hr⟩
  · simp only [Nat.sub_zero] at ht
    have heq : count.cost + 6 + (offset.cost + value.cost + 3) =
        count.cost + offset.cost + value.cost + 9 := by omega
    rw [heq] at ht
    omega
  · simpa using hd

end GraphMinor.Compute
