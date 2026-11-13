module

public import GraphMinor.Compute.Join13Write72
public import GraphMinor.Compute.MultiDigraph

/-!
# Expanding a multiplicity in the (7.2) input

The graph input lists one triple for each active endpoint pair. The core input
uses one index per individual edge. This loop writes an endpoint pair once for
each copy of that edge, in the order used by the decomposition code.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Repeat the endpoint pair in registers `r + 1` and `r + 2`. The position is
in register `r`, and the remaining multiplicity is in register `r + 3`. -/
def repeatEndpoints72Prog (a_buf r : ℕ) : Cmd :=
  .while (.reg (r + 3))
    (.seq (bufPush2 a_buf r (r + 1) (r + 2))
      (.assign (r + 3) (.op .sub (.reg (r + 3)) (.const 1))))

/-- Expanding one multiplicity takes linear time and changes only the position,
remaining count, and destination buffer. -/
theorem repeatEndpoints72Prog_exec {w : ℕ} (a_buf r u v k rem : ℕ)
    (pre : List ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hu : u < 2 ^ w) (hv : v < 2 ^ w)
    (hcap : pre.length + 2 * k + rem < 2 ^ w)
    (hbuf : s.arrs a_buf = pre ++ List.replicate (2 * k + rem) 0)
    (hr_pos : s.regs r = pre.length) (hr_u : s.regs (r + 1) = u)
    (hr_v : s.regs (r + 2) = v) (hr_count : s.regs (r + 3) = k) :
    let words := (List.replicate k [u, v]).flatten
    ∃ s' t, Exec w (repeatEndpoints72Prog a_buf r) s s' t ∧ t ≤ 20 * k + 1 ∧
      s'.arrs a_buf = pre ++ words ++ List.replicate rem 0 ∧
      s'.regs r = (pre ++ words).length ∧ s'.regs (r + 3) = 0 ∧
      Keeps [r, r + 3] [a_buf] s s' := by
  induction k generalizing pre s with
  | zero =>
    refine ⟨s, 1, .while_false (by simp [Expr.eval, checkWord, hr_count]), by omega,
      ?_, ?_, hr_count, Keeps.refl _ _ s⟩
    · simpa using hbuf
    · simpa using hr_pos
  | succ k ih =>
    have hk_w : k + 1 < 2 ^ w := by omega
    obtain ⟨s₁, t₁, hex₁, ht₁, hd₁, hp₁, ha₁, hreg₁⟩ :=
      bufPush2_exec a_buf r (r + 1) (r + 2) pre (2 * k + rem) u v hw (by omega) hu hv
        (by simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbuf)
        hr_pos hr_u hr_v
    let s₂ := s₁.setReg (r + 3) k
    have hc₁ : s₁.regs (r + 3) = k + 1 := (hreg₁ _ (by omega)).trans hr_count
    have hex₂ : Exec w (.assign (r + 3) (.op .sub (.reg (r + 3)) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc₁, hk_w,
        show k < 2 ^ w by omega, show 1 < 2 ^ w by omega])
    obtain ⟨s', t', hex', ht', hd', hp', hc', hk'⟩ := ih (pre ++ [u, v]) s₂
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      hd₁
      (by rw [State.setReg_regs_ne _ _ (show (r : ℕ) ≠ r + 3 by omega)]; exact hp₁)
      (by simp [s₂, hreg₁ (r + 1) (by omega), hr_u])
      (by simp [s₂, hreg₁ (r + 2) (by omega), hr_v])
      (by simp [s₂])
    have hcond : (.reg (r + 3) : Expr).eval w s = some (k + 1) := by
      simp [Expr.eval, checkWord, hr_count, hk_w]
    refine ⟨s', 1 + (t₁ + 4) + t', .while_true hcond (by omega) (.seq hex₁ hex₂) hex',
      by omega, ?_, ?_, hc', ?_⟩
    · simpa [List.replicate_succ, List.append_assoc] using hd'
    · simpa [List.replicate_succ, List.append_assoc] using hp'
    · refine ⟨fun j hj => ?_, fun a ha => ?_⟩
      · rw [hk'.1 j hj]
        have hj0 : j ≠ r := by simp only [List.mem_cons, not_or] at hj; exact hj.1
        have hj3 : j ≠ r + 3 := by simp only [List.mem_cons, not_or] at hj; exact hj.2.1
        rw [State.setReg_regs_ne _ _ hj3]
        exact hreg₁ j hj0
      · rw [hk'.2 a ha]
        exact ha₁ a (by simpa using ha)

end GraphMinor.Compute
