module

public import GraphMinor.Compute.TwoPathsCyc
import GraphMinor.Compute.TwoPathsRotate
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Filling scratch arrays with computed words

The winding computation of VI (5.11), page 134, needs endpoint-pair
keys and flattened signed edge words. This loop fills each position
with the value of a RAM expression. Its invariant preserves the
input outside the counter and destination array.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Allocate a scratch array and fill it with an expression evaluated
at each counter value. -/
def gm06Alg511MapValuesProg (r : Reg) (hi : Expr) (dst : Arr) (value : Expr) : Cmd :=
  .seq (.alloc dst hi) (.seq (.assign r (.const 0))
    (forUp r hi (.write dst (.reg r) value)))

/-- The value-filling loop writes the specified finite list, with a
linear time bound in its length and preservation of other storage. -/
theorem gm06Alg511MapValuesProg_exec {w : ℕ} (r : Reg) (hi : Expr)
    (dst : Arr) (value : Expr) (k : ℕ) (f : ℕ → ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hk : k < 2 ^ w)
    (hhi : ∀ st, Keeps [r] [dst] s st → hi.eval w st = some k)
    (hvalue : ∀ st i, Keeps [r] [dst] s st → st.regs r = i → i < k →
      value.eval w st = some (f i)) :
    ∃ s' t, Exec w (gm06Alg511MapValuesProg r hi dst value) s s' t ∧
      t ≤ 2 * hi.cost + 4 + k * (hi.cost + value.cost + 9) ∧
      Keeps [r] [dst] s s' ∧ s'.arrs dst = (List.range k).map f := by
  let s₁ := s.setArr dst (List.replicate k 0)
  let s₂ := s₁.setReg r 0
  have he₁ : Exec w (.alloc dst hi) s s₁ (hi.cost + k) :=
    .alloc (hhi s (Keeps.refl _ _ s))
  have he₂ : Exec w (.assign r (.const 0)) s₁ s₂ 2 :=
    .assign (Crossing.eval_const (Nat.two_pow_pos w))
  let I : ℕ → State → Prop := fun i st => Keeps [r] [dst] s st ∧
    st.regs r = i ∧ st.arrs dst = (List.range i).map f ++ List.replicate (k - i) 0
  have hI : I 0 s₂ := ⟨((Keeps.refl _ _ s).setArr (by simp) _).setReg (by simp) _,
    by simp [s₂], by simp [s₂, s₁]⟩
  obtain ⟨s', t, he, ht, hI'⟩ := Crossing.forUp_exec' I k (value.cost + 2) hw hk
    (fun i _ st h => ⟨h.2.1, hhi st h.1⟩)
    (fun i hi' st h => by
      have hlen : i < (st.arrs dst).length := by rw [h.2.2]; simp; omega
      refine ⟨st.writeArr dst i (f i), _,
        .write (Crossing.eval_reg h.2.1 (hi'.trans hk))
          (hvalue st i h.1 h.2.1 hi') hlen, by simp only [Expr.cost]; omega, ?_, ?_⟩
      · refine ⟨(h.1.writeArr (by simp) _ _).setReg (by simp) _, by simp, ?_⟩
        simp only [State.setReg_arrs, State.writeArr, State.setArr_arrs, ite_true, h.2.2]
        exact set_range_map f hi'
      · simpa using h.2.1)
    s₂ hI
  refine ⟨s', hi.cost + k + (2 + t), .seq he₁ (.seq he₂ he), ?_, hI'.1, ?_⟩
  · have hdist : k * (hi.cost + value.cost + 9) =
        k * (hi.cost + 6 + (value.cost + 2)) + k := by ring
    omega
  · simpa [I] using hI'.2.2

end GraphMinor.Compute
