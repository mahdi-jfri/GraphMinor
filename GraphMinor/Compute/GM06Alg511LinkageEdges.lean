module

public import GraphMinor.Compute.GM06Alg511LinkageEdgeBody
import Mathlib.Tactic

/-!
# Materializing every edge choice of the initial flow linkage

For VI (5.11), page 134, enumerate all finite vertex labels. Select
an actual directed edge for every successor pair returned by maximum
flow. Store a sentinel otherwise. The resulting array, together with
the raw predecessor/successor output, retains all linkage edge labels.
Its construction uses neither a supplied linkage nor geometric choice.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Select one directed edge per actual successor and store it at
its source vertex in array 1300. -/
def gm06Alg511LinkageEdgesProg : Cmd :=
  .seq (.alloc 1300 (.reg 41)) (.seq (.assign 80 (.const 0))
    (forUp 80 (.reg 41) gm06Alg511LinkageEdgeBody))

private theorem set_prefix_append (cs : List ℕ) (i n d : ℕ)
    (hcs : cs.length = i) (hi : i < n) :
    (cs ++ List.replicate (n - i) 0).set i d =
      (cs ++ [d]) ++ List.replicate (n - (i + 1)) 0 := by
  rw [List.set_append_right _ _ (by omega), hcs, Nat.sub_self,
    show n - i = (n - (i + 1)) + 1 by omega, List.replicate_succ, List.set_cons_zero]
  simp only [List.append_assoc, List.singleton_append]

/-- Every edge of the raw flow paths is selected by the RAM scans,
with a quadratic time bound and exact directed endpoint correctness. -/
theorem gm06Alg511LinkageEdgesProg_exec {w : ℕ} (x : GM06Alg511Input)
    {α β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G) (out : List ℕ)
    (hsys : IsValidPathSystem x.flowGraph x.flowInput.A x.flowInput.B
      (decUsed x.vertexCount out) (decPred x.vertexCount out) (decSucc x.vertexCount out))
    (s : State) (hw : 1 < 2 ^ w) (hword : 1 + 3 * x.vertexCount < 2 ^ w)
    (hsquare : x.vertexCount * x.vertexCount < 2 ^ w) (hends : x.endpoints.length < 2 ^ w)
    (hlen : out.length = 1 + 3 * x.vertexCount) (hout : s.arrs outArr = out)
    (hkeys : s.arrs 1100 = gm06Alg511DartKeys x) (hN : s.regs 41 = x.vertexCount) :
    ∃ s' t, Exec w gm06Alg511LinkageEdgesProg s s' t ∧
      t ≤ 6 + x.vertexCount * (38 + 13 * x.endpoints.length) ∧
      Keeps [80, 43, 44, 48, 20, 47] [1300] s s' ∧
      (s'.arrs 1300).length = x.vertexCount ∧
      ∀ u : Fin x.vertexCount,
        let d := (s'.arrs 1300).getD u.val x.endpoints.length
        if decSucc x.vertexCount out u < x.vertexCount then
          d < x.endpoints.length ∧ x.endpoints.getD d 0 = u.val ∧
            x.endpoints.getD (gm06DartMate d) 0 = decSucc x.vertexCount out u
        else d = x.endpoints.length := by
  have hn : x.vertexCount < 2 ^ w := by omega
  let P : List ℕ → Prop := fun cs => ∀ j (hj : j < cs.length) (hjn : j < x.vertexCount),
    if decSucc x.vertexCount out ⟨j, hjn⟩ < x.vertexCount then
      cs[j] < x.endpoints.length ∧ x.endpoints.getD cs[j] 0 = j ∧
        x.endpoints.getD (gm06DartMate cs[j]) 0 = decSucc x.vertexCount out ⟨j, hjn⟩
    else cs[j] = x.endpoints.length
  let I : ℕ → State → Prop := fun i st =>
    Keeps [80, 43, 44, 48, 20, 47] [1300] s st ∧ st.regs 80 = i ∧
      ∃ cs : List ℕ, cs.length = i ∧
        st.arrs 1300 = cs ++ List.replicate (x.vertexCount - i) 0 ∧ P cs
  let s₁ := s.setArr 1300 (List.replicate x.vertexCount 0)
  let s₂ := s₁.setReg 80 0
  have he₁ : Exec w (.alloc 1300 (.reg 41)) s s₁ (1 + x.vertexCount) :=
    .alloc (Crossing.eval_reg hN hn)
  have he₂ : Exec w (.assign 80 (.const 0)) s₁ s₂ 2 :=
    .assign (Crossing.eval_const (Nat.two_pow_pos w))
  have hI₀ : I 0 s₂ := by
    refine ⟨((Keeps.refl _ _ s).setArr (by simp) _).setReg (by simp) _, by simp [s₂],
      [], rfl, by simp [s₂, s₁], ?_⟩
    intro j hj
    simp at hj
  obtain ⟨s', t, he, ht, hI'⟩ := Crossing.forUp_exec' I x.vertexCount
    (30 + 13 * x.endpoints.length) hw hn
    (fun i _ st h => ⟨h.2.1, Crossing.eval_reg ((h.1.1 41 (by decide)).trans hN) hn⟩)
    (fun i hilt st h => by
      obtain ⟨cs, hcs, harr, hp⟩ := h.2.2
      have hcap : (st.arrs 1300).length = x.vertexCount := by
        rw [harr, List.length_append, List.length_replicate, hcs]
        omega
      obtain ⟨st', tb, heb, htb, hk, d, hset, hd⟩ := gm06Alg511LinkageEdgeBody_exec
        x rep out hsys ⟨i, hilt⟩ st hw hword hsquare hends hlen
        ((h.1.2 outArr (by decide)).trans hout) ((h.1.2 1100 (by decide)).trans hkeys)
        ((h.1.1 41 (by decide)).trans hN) h.2.1 hcap
      have hprop : P (cs ++ [d]) := by
        intro j hj hjn
        by_cases hjold : j < cs.length
        · simpa only [List.getElem_append_left hjold] using hp j hjold hjn
        · have hji : j = i := by simp only [List.length_append, List.length_singleton] at hj; omega
          subst j
          have hget : (cs ++ [d])[i] = d := by simp [← hcs]
          simpa only [hget] using hd
      refine ⟨st', tb, heb, htb, ?_, (hk.1 80 (by decide)).trans h.2.1⟩
      refine ⟨(h.1.trans hk (by simp) (by simp)).setReg (by simp) _, by simp,
        cs ++ [d], by simp [hcs], ?_, hprop⟩
      simp only [State.setReg_arrs, hset, harr]
      exact set_prefix_append cs i x.vertexCount d hcs hilt)
    s₂ hI₀
  obtain ⟨cs, hcs, harr, hp⟩ := hI'.2.2
  have hfinal : s'.arrs 1300 = cs := by simpa only [Nat.sub_self, List.replicate_zero, List.append_nil] using harr
  refine ⟨s', 1 + x.vertexCount + (2 + t), .seq he₁ (.seq he₂ he), ?_, hI'.1,
    by rw [hfinal, hcs], ?_⟩
  · simp only [Expr.cost] at ht
    nlinarith only [ht]
  · intro u
    have hu : u.val < cs.length := by rw [hcs]; exact u.isLt
    have hget : (s'.arrs 1300).getD u.val x.endpoints.length = cs[u.val] := by simp [hfinal, hu]
    simp only [hget]
    exact hp u.val hu u.isLt

end GraphMinor.Compute
