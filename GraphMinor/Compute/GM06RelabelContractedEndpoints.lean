module

public import GraphMinor.Compute.TwoPathsCyc
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Relabelling the endpoints of a contracted initial edge

Reduction 3 in VI (5.7), page 133, moves the neighbour of an
initial leaf to that initial vertex. In the endpoint array this
replaces every occurrence of the neighbour label by the initial
label. Process the array in place. A mapped-prefix invariant proves
that each unread position still holds its original value, while
all earlier positions have exactly the required new labels.
-/

public section
namespace GraphMinor.Compute
open TwoPaths

private theorem relabel_prefix_length (xs : List ℕ) (f : ℕ → ℕ) (i : ℕ) :
    ((xs.take i).map f ++ xs.drop i).length = xs.length := by
  simp only [List.length_append, List.length_map, List.length_take, List.length_drop]
  omega

private theorem relabel_prefix_get (xs : List ℕ) (f : ℕ → ℕ) (i : ℕ) (hi : i < xs.length) :
    ((xs.take i).map f ++ xs.drop i)[i]? = some xs[i] := by
  have hlen : ((xs.take i).map f).length = i := by
    rw [List.length_map, List.length_take_of_le hi.le]
  rw [List.getElem?_append_right (by omega)]
  simp only [hlen, Nat.sub_self, List.getElem?_drop, Nat.add_zero,
    List.getElem?_eq_getElem hi]

private theorem relabel_prefix_set (xs : List ℕ) (f : ℕ → ℕ) (i : ℕ) (hi : i < xs.length) :
    ((xs.take i).map f ++ xs.drop i).set i (f xs[i]) =
      (xs.take (i + 1)).map f ++ xs.drop (i + 1) := by
  have hlen : ((xs.take i).map f).length = i := by
    rw [List.length_map, List.length_take_of_le hi.le]
  rw [List.drop_eq_getElem_cons hi, List.take_add_one,
    List.getElem?_eq_getElem hi, Option.toList_some]
  rw [List.set_append_right i (f xs[i]) (by omega)]
  simp only [hlen, Nat.sub_self, List.set_cons_zero, List.map_append, List.map_cons,
    List.map_nil, List.append_assoc, List.singleton_append]

/-- Replace neighbour label 301 by initial label 22 in endpoint
array 3. The original edge indices and array length stay fixed. -/
@[expose] def gm06RelabelContractedEndpointsProg : Cmd :=
  .seq (.assign 307 (.const 0))
    (forUp 307 (.len 3) (.ite (.op .eq (.read 3 (.reg 307)) (.reg 301))
      (.write 3 (.reg 307) (.reg 22)) .skip))

/-- The endpoint update computes the exact label substitution in
place, in linear time, with no change to any other array. -/
theorem gm06RelabelContractedEndpointsProg_exec {w : ℕ} (xs : List ℕ) (a b : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : xs.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h3 : s.arrs 3 = xs) (h22 : s.regs 22 = a) (h301 : s.regs 301 = b) :
    ∃ s' t, Exec w gm06RelabelContractedEndpointsProg s s' t ∧
      t ≤ 5 + 14 * xs.length ∧ Keeps [307] [3] s s' ∧
      s'.arrs 3 = xs.map (fun v => if v = b then a else v) := by
  let f := fun v => if v = b then a else v
  let Inv := fun i st => st.regs 307 = i ∧ Keeps [307] [3] s st ∧
    st.arrs 3 = (xs.take i).map f ++ xs.drop i
  let s₀ := s.setReg 307 0
  have he₀ : Exec w (.assign 307 (.const 0)) s s₀ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hInv₀ : Inv 0 s₀ := by
    refine ⟨by simp [s₀], (Keeps.refl [307] [3] s).setReg (by simp) _, ?_⟩
    simpa [s₀] using h3
  obtain ⟨s', t, hex, ht, hInv⟩ := GraphMinor.Compute.Crossing.forUp_exec'
    (r_i := 307) (hi := .len 3)
    (body := .ite (.op .eq (.read 3 (.reg 307)) (.reg 301)) (.write 3 (.reg 307) (.reg 22)) .skip)
    Inv xs.length 7 hw hn
    (fun i _ st h => by
      have hlen : (st.arrs 3).length = xs.length := h.2.2 ▸ relabel_prefix_length xs f i
      refine ⟨h.1, ?_⟩
      simpa only [hlen] using GraphMinor.Compute.Crossing.eval_len (a := 3) (s := st) rfl (hlen ▸ hn))
    (fun i hi st h => by
      obtain ⟨hidx, hframe, harr⟩ := h
      have hlen : (st.arrs 3).length = xs.length := harr ▸ relabel_prefix_length xs f i
      have hiSt : i < (st.arrs 3).length := hlen ▸ hi
      have hget : (st.arrs 3)[i] = xs[i] := by
        have hh := relabel_prefix_get xs f i hi
        rw [← harr] at hh
        simpa only [List.getElem?_eq_getElem hiSt, Option.some.injEq] using hh
      have hread := GraphMinor.Compute.Crossing.eval_read (a := 3) (s := st)
        (GraphMinor.Compute.Crossing.eval_reg hidx (hi.trans hn)) hiSt
        (by rw [hget]; exact hx _ (List.getElem_mem hi))
      have hcmp := GraphMinor.Compute.Crossing.eval_eq hread
        (GraphMinor.Compute.Crossing.eval_reg ((hframe.1 301 (by decide)).trans h301) hb) hw
      simp only [hget] at hcmp
      by_cases heq : xs[i] = b
      · let st₁ := st.writeArr 3 i a
        have hwrite : Exec w (.write 3 (.reg 307) (.reg 22)) st st₁ 3 :=
          .write (GraphMinor.Compute.Crossing.eval_reg hidx (hi.trans hn))
            (GraphMinor.Compute.Crossing.eval_reg ((hframe.1 22 (by decide)).trans h22) ha) hiSt
        have hf : f xs[i] = a := by simp only [f, heq, ite_true]
        have hnext : st₁.arrs 3 = (xs.take (i + 1)).map f ++ xs.drop (i + 1) := by
          change (st.arrs 3).set i a = _
          rw [harr, ← hf]
          exact relabel_prefix_set xs f i hi
        refine ⟨st₁, 7, .ite_true (by simpa only [heq, ite_true] using hcmp) (by decide) hwrite,
          le_rfl, ⟨by simp, (hframe.setArr (by simp) _).setReg (by simp) _, ?_⟩, ?_⟩
        · simpa using hnext
        · simpa [st₁] using hidx
      · have hf : f xs[i] = xs[i] := by simp only [f, heq, ite_false]
        have hnext : st.arrs 3 = (xs.take (i + 1)).map f ++ xs.drop (i + 1) := by
          have hh := relabel_prefix_set xs f i hi
          rw [hf, ← harr, ← hget, List.set_getElem_self hiSt] at hh
          exact hh
        refine ⟨st, 5, .ite_false (by simpa only [heq, ite_false] using hcmp) (.skip st),
          by decide, ⟨by simp, hframe.setReg (by simp) _, ?_⟩, hidx⟩
        simpa using hnext) s₀ hInv₀
  refine ⟨s', 2 + t, .seq he₀ hex, ?_, hInv.2.1, ?_⟩
  · simp only [Expr.cost] at ht
    omega
  · simpa only [List.take_length, List.drop_length, List.append_nil] using hInv.2.2

end GraphMinor.Compute
