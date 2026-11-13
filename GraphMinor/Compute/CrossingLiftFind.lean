module

public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Locating the merged vertex on a returned path

The contraction lifts in Section 11 first test whether the retained vertex occurs on a
returned path, and use its position when it does. This file implements that scan on a
path array. A path has no repeated vertices, so the position stored by the scan is its
list index. The array length is the sentinel when the vertex is absent.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Find the vertex in `r_v` in the path array. Return its position in `r_pos`, or the array
length when absent. Only `r_pos` and loop counter `r_i` change. -/
def liftFindVertexProg (src r_v r_pos r_i : ℕ) : Cmd :=
  .seq (.assign r_pos (.len src))
    (.seq (.assign r_i (.const 0))
      (forUp r_i (.len src)
        (.ite (.op .eq (.read src (.reg r_i)) (.reg r_v))
          (.assign r_pos (.reg r_i)) .skip)))

/-- The Section 11 position scan on a duplicate-free path is linear and preserves all arrays.
Its only assumptions concern the stored list, register separation, and word bounds. -/
theorem liftFindVertexProg_exec {w : ℕ} (src r_v r_pos r_i : ℕ)
    (hvp : r_v ≠ r_pos) (hvi : r_v ≠ r_i) (hpi : r_pos ≠ r_i)
    (L : List ℕ) (v : ℕ) (s : State) (hsrc : s.arrs src = L)
    (hv : s.regs r_v = v) (hnd : L.Nodup)
    (hwords : ∀ x ∈ L, x < 2 ^ w) (hvw : v < 2 ^ w) (hw : L.length + 1 < 2 ^ w) :
    ∃ s' t, Exec w (liftFindVertexProg src r_v r_pos r_i) s s' t ∧
      t ≤ 16 * (L.length + 1) ∧ s'.regs r_pos = L.idxOf v ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_pos → r ≠ r_i → s'.regs r = s.regs r) := by
  have hlen : L.length < 2 ^ w := by omega
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  let s1 := s.setReg r_pos L.length
  let s2 := s1.setReg r_i 0
  let I : ℕ → State → Prop := fun j st =>
    st.regs r_i = j ∧ st.regs r_pos = (if L.idxOf v < j then L.idxOf v else L.length) ∧
    (∀ a, st.arrs a = s.arrs a) ∧
    (∀ r, r ≠ r_pos → r ≠ r_i → st.regs r = s.regs r)
  have hinit : I 0 s2 := by
    refine ⟨by simp [s2], ?_, fun _ => rfl, ?_⟩
    · simp [s2, s1, hpi]
    · intro r hp hi; simp [s2, s1, hp, hi]
  obtain ⟨s3, t3, he3, ht3, hI⟩ := forUp_exec' I L.length 6 hw1 hlen
    (r_i := r_i) (hi := .len src)
    (body := .ite (.op .eq (.read src (.reg r_i)) (.reg r_v))
      (.assign r_pos (.reg r_i)) .skip)
    (fun j _ st hI => ⟨hI.1, eval_len ((hI.2.2.1 src).trans hsrc) hlen⟩)
    (fun j hj st hI => by
      obtain ⟨hri, hp, ha, hr⟩ := hI
      have hs : st.arrs src = L := (ha src).trans hsrc
      have hvst : st.regs r_v = v := (hr r_v hvp hvi).trans hv
      have hidx : j < (st.arrs src).length := by rw [hs]; exact hj
      have hval : (st.arrs src)[j]'hidx = L[j] := by simp only [hs]
      have hread : (Expr.read src (.reg r_i)).eval w st = some L[j] := by
        rw [← hval]
        exact eval_read (eval_reg hri (by omega)) hidx
          (by rw [hval]; exact hwords _ (List.getElem_mem hj))
      have hcond := eval_eq hread (eval_reg hvst hvw) hw1
      by_cases heq : L[j] = v
      · have hpos : L.idxOf v = j := by
          rw [← heq]
          exact hnd.idxOf_getElem j hj
        have hc : (Expr.op .eq (.read src (.reg r_i)) (.reg r_v)).eval w st = some 1 := by
          simpa only [heq, ↓reduceIte] using hcond
        refine ⟨st.setReg r_pos j, 6, .ite_true hc (by omega)
          (.assign (eval_reg hri (by omega))), by omega, ?_, ?_⟩
        · refine ⟨by simp, ?_, ha, ?_⟩
          · simp [hpi, hpos]
          · intro r hpr hir
            simp [hpr, hir, hr r hpr hir]
        · simp [hpi.symm, hri]
      · have hpos : L.idxOf v ≠ j := by
          intro h
          have hget : L[L.idxOf v]'(by omega) = v := List.getElem_idxOf (by omega)
          exact heq (by simpa only [h] using hget)
        have hc : (Expr.op .eq (.read src (.reg r_i)) (.reg r_v)).eval w st = some 0 := by
          simpa only [heq, ↓reduceIte] using hcond
        refine ⟨st, 5, .ite_false hc (.skip st), by omega, ?_, hri⟩
        refine ⟨by simp, ?_, ha, ?_⟩
        · simp only [State.setReg_regs_ne _ _ hpi, hp]
          split_ifs <;> omega
        · intro r hpr hir; simp [hir, hr r hpr hir])
    s2 hinit
  refine ⟨s3, 2 + (2 + t3),
    .seq (.assign (eval_len hsrc hlen)) (.seq (.assign (eval_const hw0)) he3),
    ?_, ?_, hI.2.2.1, hI.2.2.2⟩
  · simp only [Expr.cost] at ht3
    omega
  · have hle : L.idxOf v ≤ L.length := List.idxOf_le_length
    rw [hI.2.1]
    split_ifs <;> omega

end GraphMinor.Compute.Crossing
