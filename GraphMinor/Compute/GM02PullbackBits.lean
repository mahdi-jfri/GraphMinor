module

public import GraphMinor.Compute.GM13SocietyTabulate
public import GraphMinor.Compute.BitSet

/-!
# Restricting side bits to numbered boundary vertices

The inverse boundary-numbering array gives the old name of each numbered
boundary vertex. Look up its side-membership bit in the parent array.
The result is exactly the pullback subset on the numbered boundary, in
linear boundary size and without changing either source array.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.Compute.Crossing TwoPaths

/-- The numbered vertices whose old names belong to the given subset. -/
def gm02PullbackVertexSet {n b : ℕ} (f : Fin b → Fin n) (S : Finset (Fin n)) : Finset (Fin b) :=
  Finset.univ.filter (fun i => f i ∈ S)

/-- Pull side bits back through an old-name array, using counter 320. -/
def gm02PullbackBitsProg (side orig dst : Arr) : Cmd :=
  gm13TabulateProg 320 (.len orig) (.read side (.read orig (.reg 320))) dst

/-- Looking up the old side bits writes exactly the numbered side subset. -/
theorem gm02PullbackBitsProg_exec {n b w : ℕ} (f : Fin b → Fin n) (S : Finset (Fin n))
    (side orig dst : Arr) (hsd : side ≠ dst) (hod : orig ≠ dst) (s : State)
    (hside : s.arrs side = bitSetList S) (horig : s.arrs orig = List.ofFn (fun i => (f i).val))
    (hn : n < 2 ^ w) (hb : b < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t, Exec w (gm02PullbackBitsProg side orig dst) s s' t ∧
      t ≤ 6 + 15 * b ∧ Keeps [320] [dst] s s' ∧
      s'.arrs dst = bitSetList (gm02PullbackVertexSet f S) := by
  obtain ⟨s', t, he, ht, hk, hout⟩ := gm13TabulateProg_exec (w := w) 320 (.len orig)
    (.read side (.read orig (.reg 320))) dst (bitSetList (gm02PullbackVertexSet f S)) s hw
    (by simpa only [length_bitSetList] using hb)
    (fun st hk => by
      rw [length_bitSetList]
      simpa only [List.length_ofFn] using eval_len ((hk.2 _ (by simpa only [List.mem_singleton] using hod)).trans horig)
        (by simpa only [List.length_ofFn] using hb))
    (fun st i hi hk hri => by
      have hib : i < b := by simpa only [length_bitSetList] using hi
      let v : Fin b := ⟨i, hib⟩
      have hoa : st.arrs orig = List.ofFn (fun i => (f i).val) :=
        (hk.2 _ (by simpa only [List.mem_singleton] using hod)).trans horig
      have hsa : st.arrs side = bitSetList S :=
        (hk.2 _ (by simpa only [List.mem_singleton] using hsd)).trans hside
      have hio : i < (st.arrs orig).length := by simpa only [hoa, List.length_ofFn] using hib
      have hget : (st.arrs orig)[i] = (f v).val := by simp only [hoa, List.getElem_ofFn, v]
      have heorig := eval_read (a := orig) (eval_reg hri (hib.trans hb)) hio (by
        rw [hget]
        exact (f v).isLt.trans hn)
      rw [hget] at heorig
      have his : (f v).val < (st.arrs side).length := by simpa only [hsa, length_bitSetList] using (f v).isLt
      have heword : (st.arrs side)[(f v).val] = if f v ∈ S then 1 else 0 := by
        simp only [hsa, bitSetList, List.getElem_ofFn]
      have heside := eval_read (a := side) heorig his (by
        rw [heword]
        split_ifs <;> omega)
      simpa only [heword, bitSetList, List.getElem_ofFn, gm02PullbackVertexSet,
        Finset.mem_filter, Finset.mem_univ, true_and] using heside)
  refine ⟨s', t, he, ?_, hk, hout⟩
  simp only [Expr.cost_len, Expr.cost_read, Expr.cost_reg, length_bitSetList] at ht
  omega

end GraphMinor.Compute
