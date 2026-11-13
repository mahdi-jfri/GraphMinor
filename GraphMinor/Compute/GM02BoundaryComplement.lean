module

public import GraphMinor.Compute.GM13SocietyTabulate
public import GraphMinor.Compute.BitSet

/-!
# Selecting the bounded scheme boundary

The boundary is the union of the original terminal support with the
separator, which is the intersection of the two vertex sides. From their
three membership arrays, compute the complement of this union. The
compact-rank routine uses these deletion bits to number exactly the
boundary vertices.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.Compute.Crossing TwoPaths

/-- Complement bits of support union separator, using counter 300 and
vertex count 40. -/
def gm02BoundaryComplementProg (support left right dst : Arr) : Cmd :=
  gm13TabulateProg 300 (.reg 40)
    (.op .mul (.op .sub (.const 1) (.read support (.reg 300)))
      (.op .sub (.const 1) (.op .mul (.read left (.reg 300)) (.read right (.reg 300))))) dst

/-- The computed deletion set is precisely the complement of the terminal
support union the separator, in linear time. -/
theorem gm02BoundaryComplementProg_exec {n w : ℕ} (Q L R : Finset (Fin n))
    (support left right dst : Arr) (hqd : support ≠ dst) (hld : left ≠ dst) (hrd : right ≠ dst)
    (s : State) (hq : s.arrs support = bitSetList Q) (hl : s.arrs left = bitSetList L)
    (hr : s.arrs right = bitSetList R) (hn : s.regs 40 = n) (hnw : n < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t, Exec w (gm02BoundaryComplementProg support left right dst) s s' t ∧
      t ≤ 6 + 25 * n ∧ Keeps [300] [dst] s s' ∧
      s'.arrs dst = bitSetList (Q ∪ (L ∩ R))ᶜ := by
  obtain ⟨s', t, he, ht, hk, hout⟩ := gm13TabulateProg_exec (w := w) 300 (.reg 40)
    (.op .mul (.op .sub (.const 1) (.read support (.reg 300)))
      (.op .sub (.const 1) (.op .mul (.read left (.reg 300)) (.read right (.reg 300))))) dst
    (bitSetList (Q ∪ (L ∩ R))ᶜ) s hw (by simpa only [length_bitSetList] using hnw)
    (fun st hk => by
      rw [length_bitSetList]
      exact eval_reg ((hk.1 _ (by decide)).trans hn) hnw)
    (fun st i hi hk hri => by
      have hin : i < n := by simpa only [length_bitSetList] using hi
      let v : Fin n := ⟨i, hin⟩
      have hqa : st.arrs support = bitSetList Q :=
        (hk.2 _ (by simpa only [List.mem_singleton] using hqd)).trans hq
      have hla : st.arrs left = bitSetList L :=
        (hk.2 _ (by simpa only [List.mem_singleton] using hld)).trans hl
      have hra : st.arrs right = bitSetList R :=
        (hk.2 _ (by simpa only [List.mem_singleton] using hrd)).trans hr
      by_cases hvq : v ∈ Q <;> by_cases hvl : v ∈ L <;> by_cases hvr : v ∈ R <;>
        simp [Expr.eval, BinOp.eval, BinOp.raw, hqa, hla, hra, bitSetList, hri,
          hin, v, hvq, hvl, hvr, checkWord_of_lt (hin.trans hnw),
          checkWord_of_lt hw, checkWord_of_lt (by omega : 0 < 2 ^ w)])
  refine ⟨s', t, he, ?_, hk, hout⟩
  simp only [Expr.cost_op, Expr.cost_const, Expr.cost_reg, Expr.cost_read, length_bitSetList] at ht
  omega

end GraphMinor.Compute
