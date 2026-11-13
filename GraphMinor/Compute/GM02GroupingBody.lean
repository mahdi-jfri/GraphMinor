module

public import GraphMinor.Compute.GM02GroupingSearchProg

/-!
# One complete greedy grouping iteration

Leave a completed grouping unchanged. Otherwise skip vertices already
in the separator or the selected side, and search and add the component
of any new eligible vertex. The RAM iteration implements the same state
transition as the grouping proof for II (3.1), page 316.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set TwoPaths GraphMinor.Compute.Crossing Classical

/-- One complete iteration of the successful-output component grouping. -/
def gm02GroupingBody (k : ℕ) : Cmd :=
  .ite (.reg 188) .skip (.ite (gm02GroupingGuardExpr k) (gm02GroupingSearchProg k) .skip)

/-- The grouping iteration computes the exact next side, count, and ready
bit. Its only mathematical precondition is closure of the current side,
which the grouping invariant proves at every iteration. -/
theorem gm02GroupingBody_exec {n k w : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (Q X : Finset (Fin n)) (st : Finset (Fin n) × Bool)
    (f : Fin k → ℕ) (hf : ∀ i, f i ≤ n) (hX : X = gm02SlotVertices f)
    (a : Fin n) (hclosed : ∀ v ∈ st.1, gm02FiniteComponent G X v ⊆ st.1)
    (s : State) (hw : 4 < 2 ^ w) (hn : 3 * n < 2 ^ w)
    (hadj : IsAdjList G 10 11 12 lists s) (hent : (s.arrs 12).length < 2 ^ w)
    (hrn : s.regs 40 = n) (hra : s.regs 181 = a.val)
    (hq : s.arrs 5 = gm02VertexBits Q) (hslots : ∀ i, s.regs (200 + i.val) = f i)
    (hY : s.arrs 70 = gm02VertexBits st.1) (hcountY : s.regs 187 = (st.1 ∩ Q).card)
    (hready : s.regs 188 = if st.2 then 1 else 0) (hN : s.regs 185 = (Q \ X).card) :
    ∃ s' t, Exec w (gm02GroupingBody k) s s' t ∧
      t ≤ 107 + 6 * k + n * (k * 6 + 94) + 29 * totalAdjEntries lists ∧
      Keeps gm02GroupingRegs gm02GroupingArrays s s' ∧
      let out := gm02GroupingStep G Q X a st
      s'.arrs 70 = gm02VertexBits out.1 ∧ s'.regs 187 = (out.1 ∩ Q).card ∧
        s'.regs 188 = if out.2 then 1 else 0 := by
  have hn' : n < 2 ^ w := (show n ≤ 3 * n by omega).trans_lt hn
  cases hr : st.2 with
  | true =>
    have hflag : s.regs 188 = 1 := by simpa only [hr, Bool.false_eq_true, ↓reduceIte] using hready
    have hstep : gm02GroupingStep G Q X a st = st := by simp only [gm02GroupingStep, hr, ↓reduceIte]
    refine ⟨s, 2, .ite_true (eval_reg hflag (by omega)) (by decide) (.skip s), by omega,
      Keeps.refl _ _ _, ?_⟩
    rw [hstep]
    exact ⟨hY, hcountY, hready⟩
  | false =>
    have hflag : s.regs 188 = 0 := by simpa only [hr, Bool.false_eq_true, ↓reduceIte] using hready
    have heguard := gm02GroupingGuardExpr_eval f hf st.1 a s (by omega) hn' hra hY hslots
    have hcost := gm02GroupingGuardExpr_cost k
    by_cases helig : a ∉ X ∧ a ∉ st.1
    · have heguard' : (gm02GroupingGuardExpr k).eval w s = some 1 := by
        have h := helig
        rw [hX] at h
        simpa only [ite_eq_left h] using heguard
      obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hout⟩ := gm02GroupingSearchProg_exec G lists Q X st.1
        f hf hX a helig.1 helig.2 hclosed s hw hn hadj hent hrn hra hq hslots hY hcountY hN
      refine ⟨s₁, 1 + ((gm02GroupingGuardExpr k).cost + t₁), .ite_false
        (eval_reg hflag (Nat.two_pow_pos w)) (.ite_true heguard' (by decide) he₁), ?_, hk₁, ?_⟩
      · rw [hcost]
        omega
      · have hst : st = (st.1, false) := Prod.ext rfl hr
        have hstep := congrArg (gm02GroupingStep G Q X a) hst
        rw [hstep]
        exact hout
    · have hskip : a ∈ X ∨ a ∈ st.1 := by
        by_cases hx : a ∈ X
        · exact Or.inl hx
        · exact Or.inr (Classical.byContradiction (fun hy => helig ⟨hx, hy⟩))
      have heguard' : (gm02GroupingGuardExpr k).eval w s = some 0 := by
        have h : ¬(a ∉ gm02SlotVertices (n := n) f ∧ a ∉ st.1) := by
          simpa only [← hX] using helig
        simpa only [ite_eq_right h] using heguard
      have hstep : gm02GroupingStep G Q X a st = st := by
        simp only [gm02GroupingStep, hr, Bool.false_eq_true, ↓reduceIte, ite_eq_left hskip]
      refine ⟨s, 1 + ((gm02GroupingGuardExpr k).cost + 1), .ite_false
        (eval_reg hflag (Nat.two_pow_pos w)) (.ite_false heguard' (.skip s)), ?_, Keeps.refl _ _ _, ?_⟩
      · rw [hcost]
        omega
      · rw [hstep]
        exact ⟨hY, hcountY, hready⟩

end GraphMinor.Compute
