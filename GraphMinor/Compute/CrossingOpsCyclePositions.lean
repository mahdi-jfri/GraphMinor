module

public import GraphMinor.Compute.CrossingOpsReplLists
import GraphMinor.Compute.TwoPathsCyc

/-!
# Storing cycle positions

Each cycle vertex receives its list index plus one, while other vertices receive zero.
The program writes these positions in one pass over the cycle. The prefix-update proof
uses the cycle-position lemma from the disjoint-path library.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Cycle-position words after processing the first `i` cycle vertices. -/
def cyclePositions {N : ℕ} (D : List (Fin N)) (i : ℕ) : List ℕ :=
  List.ofFn (fun u : Fin N => if u ∈ D.take i then D.idxOf u + 1 else 0)

/-- Writing the next cycle vertex's position extends the processed prefix. -/
theorem cyclePositions_set {N : ℕ} (D : List (Fin N)) (hD : D.Nodup)
    {i : ℕ} (hi : i < D.length) :
    (cyclePositions D i).set D[i].val (i + 1) = cyclePositions D (i + 1) := by
  unfold cyclePositions
  rw [TwoPaths.ofFn_set]
  congr 1
  have hh := TwoPaths.update_fn_succ hD hi (fun u => D.idxOf u + 1)
    (fun L u => if u ∈ L then D.idxOf u + 1 else 0) (fun _ _ => rfl)
  beta_reduce at hh
  rw [hD.idxOf_getElem i hi] at hh
  exact hh

/-- Allocate the position array and write cycle indices. Register `R+8` holds `N`. -/
def cyclePositionsProg (a_D a_pos R : ℕ) : Cmd :=
  .seq (.alloc a_pos (.reg (R + 8)))
    (forArrProg a_D (R + 5) (R + 6) (R + 7)
      (.write a_pos (.reg (R + 7)) (.op .add (.reg (R + 5)) (.const 1))))

/-- The position program takes one pass over the cycle and preserves every other array. -/
theorem cyclePositionsProg_exec {w N : ℕ} (a_D a_pos R : ℕ)
    {D : List (Fin N)} {s : State} (hne : a_D ≠ a_pos) (hD : D.Nodup)
    (hsrc : s.arrs a_D = D.map Fin.val) (hN : s.regs (R + 8) = N)
    (hNword : N < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t, Exec w (cyclePositionsProg a_D a_pos R) s s' t ∧
      t ≤ N + 8 + 15 * D.length ∧ s'.arrs a_pos = cyclePositions D D.length ∧
      (∀ a, a ≠ a_pos → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 5 → r ≠ R + 6 → r ≠ R + 7 → s'.regs r = s.regs r) := by
  have hDlen : D.length ≤ N := by simpa using hD.length_le_card
  let s0 := s.setArr a_pos (List.replicate N 0)
  let Q : ℕ → State → Prop := fun i z => z.arrs a_pos = cyclePositions D i ∧
    ∀ a, a ≠ a_pos → z.arrs a = s.arrs a
  have h0 : Q 0 s0 := by
    refine ⟨?_, fun a ha => by simp [s0, State.setArr_arrs_ne, ha]⟩
    simp [s0, cyclePositions, List.ofFn_const]
  have hsrc0 : s0.arrs a_D = D.map Fin.val := by simp [s0, State.setArr_arrs_ne, hne, hsrc]
  obtain ⟨s1, t1, he1, ht1, hQ1⟩ := forArr_exec (w := w)
    a_D (R + 5) (R + 6) (R + 7)
    (.write a_pos (.reg (R + 7)) (.op .add (.reg (R + 5)) (.const 1))) Q 5
    (by omega) (by omega) (by omega) hw (s := s0)
    (by simp [hsrc0]; omega)
    (fun y hy => by rw [hsrc0] at hy; obtain ⟨v, -, rfl⟩ := List.mem_map.mp hy; exact v.isLt.trans hNword)
    h0
    (fun i z z' h ha _ => ⟨(congrFun ha _).trans h.1,
      fun a hh => (congrFun ha a).trans (h.2 a hh)⟩)
    (fun _ _ h => (h.2 a_D hne).trans (by simp [s0, State.setArr_arrs_ne, hne]))
    (fun i hi z h hri hrn hry => by
      have hi' : i < D.length := by simpa only [hsrc0, List.length_map] using hi
      have hry' : z.regs (R + 7) = D[i].val := by simpa only [hsrc0, List.getElem_map] using hry
      let z' := z.writeArr a_pos D[i].val (i + 1)
      have he' : Exec w (.write a_pos (.reg (R + 7)) (.op .add (.reg (R + 5)) (.const 1))) z z' 5 :=
        .write (eval_reg hry' (D[i].isLt.trans hNword))
          (eval_add (eval_reg hri (by omega)) (eval_const hw) (by omega))
          (by simp [h.1, cyclePositions])
      refine ⟨z', 5, he', le_rfl, ⟨?_, ?_⟩, by simpa [z'] using hri, by simpa [z'] using hrn⟩
      · simpa only [z', State.writeArr_arrs_self, h.1] using cyclePositions_set D hD hi'
      · intro a hh
        exact (State.writeArr_arrs_ne _ _ _ hh).trans (h.2 a hh))
  have hex := Exec.seq (Exec.alloc (eval_reg hN hNword)) he1
  refine ⟨s1, (1 + N) + t1, hex, ?_, ?_, hQ1.2, ?_⟩
  · simpa only [hsrc0, List.length_map] using (show (1 + N) + t1 ≤ N + 8 + 15 * D.length by
      rw [hsrc0, List.length_map] at ht1; omega)
  · simpa only [hsrc0, List.length_map] using hQ1.1
  · intro r h5 h6 h7
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [cyclePositionsProg, forArrProg, forUp, Cmd.writtenRegs, h5, h6, h7])

end GraphMinor.Compute.Crossing
