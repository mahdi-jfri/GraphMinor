module

public import GraphMinor.Compute.GM13SocietyTabulate
public import GraphMinor.Compute.TwoPathsNorm

/-!
# Removing one word from the current linkage encoding

Contracting the first edge of a given path in VI (5.7), page 133,
removes its first directed-edge word. Copy all other words to a
scratch array, shifting those at or after the removed position by
one, then copy the result back. The row-header adjustment is a
separate write. The deletion preserves every other instance array
and lowers the encoded word count by exactly one.
-/

public section
namespace GraphMinor.Compute
open TwoPaths

/-- Delete the linkage-array word at position 310 using scratch
array 27. The position register is retained for the row-header update. -/
@[expose] def gm06EraseLinkageWordProg : Cmd :=
  .seq (gm13TabulateProg 308 (.op .sub (.len 8) (.const 1))
    (.read 8 (.op .add (.reg 308) (.op .le (.reg 310) (.reg 308)))) 27)
    (copyProg 8 27)

/-- Deleting one valid word computes precisely list erasure, with
linear time and an exact one-word decrease in the linkage array. -/
theorem gm06EraseLinkageWordProg_exec {w : ℕ} (xs : List ℕ) (d : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : xs.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w)
    (hd : d < xs.length) (h8 : s.arrs 8 = xs) (h310 : s.regs 310 = d) :
    ∃ s' t, Exec w gm06EraseLinkageWordProg s s' t ∧ t ≤ 16 + 32 * xs.length ∧
      Keeps [308, 98] [8, 27] s s' ∧ s'.arrs 8 = xs.eraseIdx d ∧
      s'.arrs 27 = xs.eraseIdx d ∧ (s'.arrs 8).length + 1 = xs.length := by
  have hlen : (xs.eraseIdx d).length = xs.length - 1 := List.length_eraseIdx_of_lt hd
  have hlen_le : (xs.eraseIdx d).length ≤ xs.length := List.length_eraseIdx_le _ _
  have hlenw : (xs.eraseIdx d).length < 2 ^ w := hlen_le.trans_lt hn
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hout⟩ := gm13TabulateProg_exec
    308 (.op .sub (.len 8) (.const 1))
    (.read 8 (.op .add (.reg 308) (.op .le (.reg 310) (.reg 308)))) 27
    (xs.eraseIdx d) s hw hlenw
    (fun st hk => by
      have hs : st.arrs 8 = xs := (hk.2 8 (by decide)).trans h8
      simpa only [hlen] using GraphMinor.Compute.Crossing.eval_sub
        (GraphMinor.Compute.Crossing.eval_len hs hn) (GraphMinor.Compute.Crossing.eval_const hw))
    (fun st i hi hk hri => by
      have hs : st.arrs 8 = xs := (hk.2 8 (by decide)).trans h8
      have hr : st.regs 310 = d := (hk.1 310 (by decide)).trans h310
      have hiOld : i < xs.length := hi.trans_le hlen_le
      have hiw := hiOld.trans hn
      have hle : (Expr.op .le (.reg 310) (.reg 308)).eval w st =
          some (if d ≤ i then 1 else 0) := by
        by_cases hh : d ≤ i <;>
          simp [Expr.eval, hr, hri, checkWord, hd.trans hn, hiw, BinOp.eval, BinOp.raw,
            hh, hw, Nat.zero_lt_of_lt hw]
      let p := i + (if d ≤ i then 1 else 0)
      have hp : p < xs.length := by dsimp only [p]; split <;> rw [hlen] at hi <;> omega
      have hidx := GraphMinor.Compute.Crossing.eval_add
        (GraphMinor.Compute.Crossing.eval_reg hri hiw) hle (hp.trans hn)
      have hread := GraphMinor.Compute.Crossing.eval_read (a := 8) hidx
        (by simpa only [hs] using hp) (by simpa only [hs] using hx _ (List.getElem_mem hp))
      have hget : xs[p] = (xs.eraseIdx d)[i] := by
        by_cases hh : d ≤ i
        · simpa only [p, hh, ite_true] using (List.getElem_eraseIdx_of_ge hi hh).symm
        · have hh' : i < d := Nat.lt_of_not_ge hh
          simpa only [p, hh, ite_false, Nat.add_zero] using (List.getElem_eraseIdx_of_lt hi hh').symm
      simp only [hs] at hread
      exact hread.trans (congrArg some hget))
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hcopy⟩ := copyProg_exec
    (dst := 8) (src := 27) (by decide) (xs.eraseIdx d) s₁ hw hlenw
    (fun x hx' => hx x (List.mem_of_mem_eraseIdx hx')) hout
  have hk₁' : Keeps [308, 98] [8, 27] s s₁ := hk₁.mono (by simp) (by simp)
  have hk : Keeps [308, 98] [8, 27] s s₂ := hk₁'.trans hk₂ (by simp [rI3]) (by simp)
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_, hk, hcopy,
    (hk₂.2 27 (by decide)).trans hout, ?_⟩
  · simp only [Expr.cost] at ht₁
    omega
  · rw [hcopy, hlen]
    omega

end GraphMinor.Compute
