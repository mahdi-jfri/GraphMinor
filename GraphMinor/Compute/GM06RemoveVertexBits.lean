module

public import GraphMinor.Compute.GM13SocietyTabulate
public import GraphMinor.Compute.GM02CopyLabelBits

/-!
# Removing a computed component from the live vertex mask

For Reduction 2 in VI (5.7), page 133, a searched component's
membership bits identify the vertices to remove. Multiply each
live bit by the complement of its component bit and write a fresh
mask. This computes set difference in linear time and keeps the
source masks for the edge-deletion pass and the reduction record.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- Write live vertices outside the computed component into a fresh array. -/
def gm06RemoveVertexBitsProg (live removed dst : Arr) : Cmd :=
  gm13TabulateProg 180 (.len live)
    (.op .mul (.read live (.reg 180)) (.op .sub (.const 1) (.read removed (.reg 180)))) dst

/-- The vertex update computes exact set difference, with linear time
and unchanged source masks. -/
theorem gm06RemoveVertexBitsProg_exec {n w : ℕ} (A R : Finset (Fin n))
    (live removed dst : Arr) (hld : live ≠ dst) (hrd : removed ≠ dst) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w)
    (hlive : s.arrs live = gm02VertexBits A) (hremoved : s.arrs removed = gm02VertexBits R) :
    ∃ s' t, Exec w (gm06RemoveVertexBitsProg live removed dst) s s' t ∧
      t ≤ 6 + 19 * n ∧ Keeps [180] [dst] s s' ∧ s'.arrs dst = gm02VertexBits (A \ R) := by
  classical
  obtain ⟨s', t, hex, ht, hk, hout⟩ := gm13TabulateProg_exec 180 (.len live)
    (.op .mul (.read live (.reg 180)) (.op .sub (.const 1) (.read removed (.reg 180))))
    dst (gm02VertexBits (A \ R)) s hw
    (by simpa only [gm02VertexBits, List.length_ofFn] using hn)
    (fun st hk => by
      simp only [gm02VertexBits, List.length_ofFn]
      simpa only [gm02VertexBits, List.length_ofFn] using
        (eval_len ((hk.2 live (by simpa using hld)).trans hlive)
          (by simpa only [gm02VertexBits, List.length_ofFn] using hn)))
    (fun st i hi hk hidx => by
      have hin : i < n := by simpa only [gm02VertexBits, List.length_ofFn] using hi
      let v : Fin n := ⟨i, hin⟩
      have hlive' : st.arrs live = gm02VertexBits A :=
        (hk.2 live (by simpa using hld)).trans hlive
      have hremoved' : st.arrs removed = gm02VertexBits R :=
        (hk.2 removed (by simpa using hrd)).trans hremoved
      have hA := gm02ReadVertexBits_eval A v live 180 st hw hn hidx hlive'
      have hR := gm02ReadVertexBits_eval R v removed 180 st hw hn hidx hremoved'
      have hsub := eval_sub (eval_const hw) hR
      have hfit : (if v ∈ A then 1 else 0) * (1 - (if v ∈ R then 1 else 0)) < 2 ^ w := by
        by_cases ha : v ∈ A <;> by_cases hr : v ∈ R <;> simp [ha, hr, hw, Nat.zero_lt_of_lt hw]
      have he := eval_mul hA hsub hfit
      by_cases ha : v ∈ A <;> by_cases hr : v ∈ R <;>
        simpa only [gm02VertexBits, List.getElem_ofFn, Finset.mem_sdiff, ha, hr, ite_true,
          ite_false, and_true, and_false, true_and, false_and, not_true_eq_false,
          not_false_eq_true, Nat.sub_self, Nat.sub_zero, Nat.mul_one, Nat.mul_zero,
          Nat.zero_mul, Nat.one_mul, v] using he)
  refine ⟨s', t, hex, ?_, hk, hout⟩
  simpa only [Expr.cost, gm02VertexBits, List.length_ofFn, Nat.mul_comm] using ht

end GraphMinor.Compute
