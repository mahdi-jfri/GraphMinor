module

public import GraphMinor.Compute.GM02TemplateMembership
public import GraphMinor.Compute.BitSet

/-!
# Writing expanded boundary-template bits

A fixed catalogue template gives a list of boundary indices. Scan the
parent vertices and use the old-name membership expression to mark its
image. This computes the reserved and terminal-support sets needed to
build recursive child inputs, in time linear in parent size for a fixed
template.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.Compute.Crossing TwoPaths

/-- Mark the parent names of a fixed list of boundary indices. -/
def gm02TemplateBitsProg (orig dst : Arr) (indices : List ℕ) : Cmd :=
  gm13TabulateProg 340 (.reg 40)
    (.op .sub (.const 1) (gm02TemplateFreeExpr orig (.reg 340) indices)) dst

/-- The loop writes exactly the image of the fixed template under old-name lookup. -/
theorem gm02TemplateBitsProg_exec {n b w : ℕ} (f : Fin b → Fin n)
    (indices : List (Fin b)) (orig dst : Arr) (hod : orig ≠ dst) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hb : b < 2 ^ w)
    (horig : s.arrs orig = List.ofFn (fun i => (f i).val)) (hcount : s.regs 40 = n) :
    ∃ s' t, Exec w (gm02TemplateBitsProg orig dst (indices.map Fin.val)) s s' t ∧
      t ≤ 6 + n * (15 + 7 * indices.length) ∧ Keeps [340] [dst] s s' ∧
      s'.arrs dst = bitSetList (indices.toFinset.image f) := by
  obtain ⟨s', t, he, ht, hk, hout⟩ := gm13TabulateProg_exec (w := w) 340 (.reg 40)
    (.op .sub (.const 1) (gm02TemplateFreeExpr orig (.reg 340) (indices.map Fin.val))) dst
    (bitSetList (indices.toFinset.image f)) s hw
    (by simpa only [length_bitSetList] using hn)
    (fun st hk => by
      rw [length_bitSetList]
      exact eval_reg ((hk.1 _ (by decide)).trans hcount) hn)
    (fun st i hi hk hri => by
      have hin : i < n := by simpa only [length_bitSetList] using hi
      let v : Fin n := ⟨i, hin⟩
      have hra : st.arrs orig = List.ofFn (fun i => (f i).val) :=
        (hk.2 _ (by simpa only [List.mem_singleton] using hod)).trans horig
      have hfree := gm02TemplateFreeExpr_eval_names f indices orig (.reg 340) v st hw hn hb
        hra (eval_reg hri (hin.trans hn))
      have hs := eval_sub (eval_const hw) hfree
      simpa only [bitSetList, List.getElem_ofFn, v, apply_ite, Nat.sub_zero,
        Nat.sub_self] using hs)
  refine ⟨s', t, he, ?_, hk, hout⟩
  simp only [Expr.cost, gm02TemplateFreeExpr_cost, List.length_map, length_bitSetList] at ht
  have hc : 1 + (1 + (1 + indices.length * (1 + 6)) + 1) + 11 =
      15 + 7 * indices.length := by omega
  rw [hc] at ht
  exact ht

end GraphMinor.Compute
