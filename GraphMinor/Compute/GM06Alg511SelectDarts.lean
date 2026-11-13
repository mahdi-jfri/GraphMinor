module

public import GraphMinor.Compute.GM06Alg511DartBody
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Selecting all directed edges of a returned path

For VI (5.11), page 134, traverse the stored vertex trace in order.
At each consecutive pair, use the verified edge scan and append its
dart to a fresh buffer. The loop invariant records the endpoints of
every appended dart. Neither a dart list nor an edge choice is part
of the input to this phase.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Convert vertex buffer 12, with length 42, to dart buffer 13,
with length 49. Register 41 holds the allocated capacity. -/
def gm06Alg511SelectDartsProg : Cmd :=
  .seq (initBufCmd 13 49 (.reg 41))
    (.seq (.assign 51 (.const 0))
      (forUp 51 (.op .sub (.reg 42) (.const 1)) gm06Alg511DartBody))

/-- The path-to-edge loop produces one valid directed edge per pair
of consecutive input vertices. Its time is at most quadratic in
vertex count plus endpoint-array length. -/
theorem gm06Alg511SelectDartsProg_exec {w : ℕ} (x : GM06Alg511Input)
    {α β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G)
    (vs : List (Fin x.vertexCount))
    (hadj : ∀ i (hi : i + 1 < vs.length),
      x.flowGraph.Adj vs[i] vs[i + 1])
    (s : State) (hw : 1 < 2 ^ w) (hn : x.vertexCount < 2 ^ w)
    (hsquare : x.vertexCount * x.vertexCount < 2 ^ w)
    (hends : x.endpoints.length < 2 ^ w)
    (hkeys : s.arrs 1100 = gm06Alg511DartKeys x)
    (hN : s.regs 41 = x.vertexCount)
    (hvertices : IsBufPrefix s 12 42 x.vertexCount (vs.map Fin.val)) :
    ∃ s' t, Exec w gm06Alg511SelectDartsProg s s' t ∧
      t ≤ 10 + x.vertexCount * (38 + 13 * x.endpoints.length) ∧
      Keeps [43, 44, 48, 20, 47, 49, 51] [13] s s' ∧
      ∃ darts, darts.length = vs.length - 1 ∧
        IsBufPrefix s' 13 49 x.vertexCount darts ∧
        ∀ j (hj : j < darts.length), darts[j] < x.endpoints.length ∧
          x.endpoints.getD darts[j] 0 = (vs.map Fin.val).getD j 0 ∧
          x.endpoints.getD (gm06DartMate darts[j]) 0 = (vs.map Fin.val).getD (j + 1) 0 := by
  let R := [43, 44, 48, 20, 47, 49, 51]
  let P : List ℕ → Prop := fun darts => ∀ j (hj : j < darts.length),
    darts[j] < x.endpoints.length ∧
      x.endpoints.getD darts[j] 0 = (vs.map Fin.val).getD j 0 ∧
      x.endpoints.getD (gm06DartMate darts[j]) 0 = (vs.map Fin.val).getD (j + 1) 0
  have hvlen : vs.length ≤ x.vertexCount := by simpa using hvertices.2.2.1
  let N := vs.length - 1
  have hNle : N ≤ x.vertexCount := (Nat.sub_le _ _).trans hvlen
  have hNfit : N < 2 ^ w := hNle.trans_lt hn
  let I : ℕ → State → Prop := fun i st => i ≤ N ∧ Keeps R [13] s st ∧
    st.regs 51 = i ∧ ∃ darts, darts.length = i ∧
      IsBufPrefix st 13 49 x.vertexCount darts ∧ P darts
  obtain ⟨s₁, t₁, he₁, ht₁, hbuf₁, hreg₁, harr₁⟩ :=
    initBufCmd_exec 13 49 (.reg 41) x.vertexCount (by omega)
      (Crossing.eval_reg hN hn)
  let s₂ := s₁.setReg 51 0
  have he₂ : Exec w (.assign 51 (.const 0)) s₁ s₂ 2 :=
    .assign (Crossing.eval_const (Nat.two_pow_pos w))
  have hk₁ : Keeps R [13] s s₁ :=
    ⟨fun r hr => hreg₁ r (by simp only [R, List.mem_cons] at hr; tauto),
      fun a ha => harr₁ a (by simpa using ha)⟩
  have hI₀ : I 0 s₂ := by
    refine ⟨Nat.zero_le _, hk₁.setReg (by simp [R]) _, by simp [s₂], [], rfl,
      hbuf₁.of_preserve rfl (by simp [s₂]), ?_⟩
    intro j hj
    simp at hj
  obtain ⟨s', t, he, ht, hI'⟩ := Crossing.forUp_exec' I N
    (28 + 13 * x.endpoints.length) hw hNfit
    (fun i _ st h => by
      refine ⟨h.2.2.1, ?_⟩
      have hcount : st.regs 42 = vs.length :=
        (h.2.1.1 42 (by decide)).trans (by simpa using hvertices.2.1)
      exact Crossing.eval_sub (Crossing.eval_reg hcount (hvlen.trans_lt hn))
        (Crossing.eval_const hw))
    (fun i hi st h => by
      obtain ⟨darts, hdlen, hbuf, hp⟩ := h.2.2.2
      have hi' : i + 1 < vs.length := by change i < vs.length - 1 at hi; omega
      have hi₀ : i < vs.length := by omega
      have hvst : IsBufPrefix st 12 42 x.vertexCount (vs.map Fin.val) :=
        hvertices.of_preserve (h.2.1.2 12 (by decide)) (h.2.1.1 42 (by decide))
      have hiarr : i < (st.arrs 12).length := by rw [hvst.1]; omega
      have hinext : i + 1 < (st.arrs 12).length := by rw [hvst.1]; omega
      have hleft : (st.arrs 12)[i] = (vs[i]).val := by
        have hh := hvst.2.2.2 i (by simpa using hi₀)
        simpa only [List.getElem?_eq_getElem hiarr, List.getElem_map, Option.some.injEq] using hh
      have hright : (st.arrs 12)[i + 1] = (vs[i + 1]).val := by
        have hh := hvst.2.2.2 (i + 1) (by simpa using hi')
        simpa only [List.getElem?_eq_getElem hinext, List.getElem_map, Option.some.injEq] using hh
      obtain ⟨st', tb, heb, htb, hkb, d, hd, hbuf', _, hda, hdb⟩ :=
        gm06Alg511DartBody_exec x rep vs[i] vs[i + 1] (hadj i hi') i darts st
          hw hn hsquare hends ((h.2.1.2 1100 (by decide)).trans hkeys)
          ((h.2.1.1 41 (by decide)).trans hN) h.2.2.1 hvst.1 (by omega)
          hleft hright hbuf (by omega)
      have hkeep : Keeps R [13] s st' := h.2.1.trans hkb (by simp [R]) (by simp)
      have hprop : P (darts ++ [d]) := by
        intro j hj
        by_cases hjold : j < darts.length
        · simpa only [List.getElem_append_left hjold] using hp j hjold
        · have hji : j = i := by simp only [List.length_append, List.length_singleton] at hj; omega
          subst j
          have hget : (darts ++ [d])[i] = d := by simp [← hdlen]
          rw [hget]
          refine ⟨hd, ?_, ?_⟩
          · simpa [hi₀] using hda
          · simpa [hi'] using hdb
      refine ⟨st', tb, heb, htb, ?_, (hkb.1 51 (by decide)).trans h.2.2.1⟩
      refine ⟨by omega, hkeep.setReg (by simp [R]) _, by simp,
        darts ++ [d], by simp [hdlen],
        hbuf'.of_preserve rfl (by simp), hprop⟩)
    s₂ hI₀
  refine ⟨s', t₁ + (2 + t), .seq he₁ (.seq he₂ he), ?_, hI'.2.1, ?_⟩
  · simp only [Expr.cost] at ht ht₁
    have hmul := Nat.mul_le_mul_right (37 + 13 * x.endpoints.length) hNle
    nlinarith [ht, ht₁]
  · exact hI'.2.2.2

end GraphMinor.Compute
