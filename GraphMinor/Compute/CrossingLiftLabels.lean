module

public import GraphMinor.Compute.CrossingLiftLabelFill
public import GraphMinor.Compute.TwoPathsBfs
public import GraphMinor.Compute.TwoPathsSep

/-!
# Labels for the reverse replacement search

The component vertices and the start are free. The end is the target, even if it also
belongs to the component or equals the start. All remaining vertices are forbidden.
The program fills the labels once and marks the component once.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Allocate forbidden labels, free the component and start, then mark the target. -/
def liftSearchLabelsProg (component labels r_n r_u r_v R : ℕ) : Cmd :=
  .seq (.alloc labels (.reg r_n))
    (.seq (liftFillConstProg labels R 2)
      (.seq (TwoPaths.markProg R (.const 0) (.len component) labels component 0)
        (.seq (.write labels (.reg r_u) (.const 0))
          (.write labels (.reg r_v) (.const 3)))))

/-- The label preparation computes the existing BFS labels in linear time. Its hypotheses
specify the component list, endpoints in lower registers, the stored vertex count, distinct input
and output arrays, and the word bound. -/
theorem liftSearchLabelsProg_exec {w N : ℕ} (component labels r_n r_u r_v R : ℕ)
    (hcl : labels ≠ component) (huR : r_u < R) (hvR : r_v < R)
    (C : List (Fin N)) (u v : Fin N) (s : State)
    (hC : s.arrs component = C.map Fin.val) (hn : s.regs r_n = N)
    (hu : s.regs r_u = u.val) (hv : s.regs r_v = v.val)
    (hw : N + C.length + 4 < 2 ^ w) :
    ∃ s' t, Exec w (liftSearchLabelsProg component labels r_n r_u r_v R) s s' t ∧
      t ≤ 20 * (N + C.length + 1) + 30 ∧
      s'.arrs labels = List.ofFn (TwoPaths.bfsLabel C u v) ∧
      (∀ a, a ≠ labels → s'.arrs a = s.arrs a) ∧
      (∀ q < R, s'.regs q = s.regs q) := by
  let s0 := s.setArr labels (List.replicate N 0)
  have hc0 : s0.arrs component = C.map Fin.val := by simp [s0, Ne.symm hcl, hC]
  obtain ⟨s1, t1, he1, ht1, ho1, ha1, hr1⟩ := liftFillConstProg_exec (w := w) (N := N)
    labels R 2 (s := s0) (by simp [s0]) (by omega) (by omega) (by omega)
  have hc1 : s1.arrs component = C.map Fin.val := (ha1 _ (Ne.symm hcl)).trans hc0
  have ho1' : s1.arrs labels = List.ofFn (fun _ : Fin N => 2) := by
    simpa only [List.ofFn_const] using ho1
  obtain ⟨s2, t2, he2, ht2, hk2, ho2⟩ := TwoPaths.markProg_exec (w := w) R (.const 0) (.len component)
    labels component 0 hcl C (fun _ => 2) 0 C.length s1
    (by omega) (by omega) (by omega) (by omega) le_rfl (eval_const (by omega))
    (fun st hk => by
      have hs := (hk.2 component (by simpa using Ne.symm hcl)).trans hc1
      simpa only [List.length_map] using eval_len (w := w) hs (by simp only [List.length_map]; omega))
    hc1 ho1'
  have hu2 : s2.regs r_u = u.val := by
    rw [hk2.1 r_u (by simp; omega), hr1 _ (by omega)]; exact hu
  have hv2 : s2.regs r_v = v.val := by
    rw [hk2.1 r_v (by simp; omega), hr1 _ (by omega)]; exact hv
  have ho2' : s2.arrs labels = List.ofFn (fun x : Fin N => if x ∈ C then 0 else 2) := by
    simpa only [List.take_length, List.drop_zero] using ho2
  let s3 := s2.writeArr labels u.val 0
  have he3 : Exec w (.write labels (.reg r_u) (.const 0)) s2 s3 3 :=
    .write (eval_reg hu2 (u.isLt.trans (by omega))) (eval_const (by omega))
      (by rw [ho2']; simp)
  have hv3 : s3.regs r_v = v.val := hv2
  have he4 : Exec w (.write labels (.reg r_v) (.const 3)) s3
      (s3.writeArr labels v.val 3) 3 :=
    .write (eval_reg hv3 (v.isLt.trans (by omega))) (eval_const (by omega))
      (by simp only [s3, State.writeArr_arrs_self, List.length_set, ho2', List.length_ofFn]; exact v.isLt)
  refine ⟨s3.writeArr labels v.val 3, (1 + N) + (t1 + (t2 + (3 + 3))),
    .seq (.alloc (eval_reg hn (by omega))) (.seq he1 (.seq he2 (.seq he3 he4))), ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost] at ht2; omega
  · simp only [State.writeArr_arrs_self, s3, ho2', TwoPaths.ofFn_set]
    apply congrArg List.ofFn
    funext x
    simp only [Function.update_apply, TwoPaths.bfsLabel]
    by_cases hxv : x = v <;> by_cases hxu : x = u <;> by_cases hxC : x ∈ C <;>
      simp [hxv, hxu, hxC]
  · intro a ha
    rw [State.writeArr_arrs_ne _ _ _ ha, State.writeArr_arrs_ne _ _ _ ha,
      hk2.2 a (by simpa using ha), ha1 a ha]
    exact State.setArr_arrs_ne _ _ ha
  · intro q hq
    exact (hk2.1 q (by simp; omega)).trans (hr1 q (by omega))

end GraphMinor.Compute.Crossing
