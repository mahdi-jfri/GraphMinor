module

public import GraphMinor.Compute.GM02ComponentRun

/-!
# Testing one vertex's component

For a vertex outside a proposed separator, run the component operation
and compare three times its terminal count with twice the remaining
terminal count. Multiply the accumulated success flag by this comparison
bit. Vertices in the proposed separator require no search. This is one
iteration of the component test in II (3.1), page 316.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set TwoPaths GraphMinor.Compute.Crossing Classical

/-- Update the success bit using the component and remaining-terminal counts. -/
def gm02ComponentFlagExpr : Expr := .op .mul (.reg 184)
  (.op .le (.op .mul (.const 3) (.reg 183)) (.op .mul (.const 2) (.reg 185)))

/-- One component-test iteration, with the vertex number in register 181. -/
def gm02ComponentTestBody (k : ℕ) : Cmd :=
  .ite (gm02TupleFreeExpr 200 (.reg 181) k)
    (.seq (gm02ComponentRunProg k) (.assign 184 gm02ComponentFlagExpr)) .skip

/-- Any vertex subset of a numbered graph has cardinality at most the vertex count. -/
theorem gm02VertexSet_ncard_le {n : ℕ} (S : Set (Fin n)) : S.ncard ≤ n := by
  simpa only [Set.ncard_univ, Nat.card_fin] using
    Set.ncard_le_ncard S.subset_univ Set.finite_univ

private theorem le_expr_eval {w a b : ℕ} {s : State} {A B : Expr}
    (hA : A.eval w s = some a) (hB : B.eval w s = some b) (hw : 1 < 2 ^ w) :
    (.op .le A B : Expr).eval w s = some (if a ≤ b then 1 else 0) := by
  by_cases h : a ≤ b <;>
    simp [Expr.eval, hA, hB, BinOp.eval, BinOp.raw, checkWord, h, hw]

/-- The flag update computes conjunction with the two-thirds component test. -/
theorem gm02ComponentFlagExpr_eval {w n c N : ℕ} (s : State) (P : Prop)
    (hw : 4 < 2 ^ w) (hn : 3 * n < 2 ^ w) (hc : c ≤ n) (hN : N ≤ n)
    (hcount : s.regs 183 = c) (htotal : s.regs 185 = N)
    (hflag : s.regs 184 = if P then 1 else 0) :
    gm02ComponentFlagExpr.eval w s = some (if P ∧ 3 * c ≤ 2 * N then 1 else 0) := by
  have hcw : c < 2 ^ w := (show c ≤ 3 * n by omega).trans_lt hn
  have hNw : N < 2 ^ w := (show N ≤ 3 * n by omega).trans_lt hn
  have hleft := eval_mul (eval_const (show 3 < 2 ^ w by omega)) (eval_reg hcount hcw)
    (show 3 * c < 2 ^ w from (Nat.mul_le_mul_left 3 hc).trans_lt hn)
  have hright := eval_mul (eval_const (show 2 < 2 ^ w by omega)) (eval_reg htotal hNw)
    (show 2 * N < 2 ^ w from (show 2 * N ≤ 3 * n by omega).trans_lt hn)
  have htest := le_expr_eval hleft hright (by omega)
  have hfw : (if P then 1 else 0) < 2 ^ w := by split_ifs <;> omega
  have hprod : (if P then 1 else 0) * (if 3 * c ≤ 2 * N then 1 else 0) < 2 ^ w := by
    split_ifs <;> omega
  have he := eval_mul (eval_reg hflag hfw) htest hprod
  by_cases hp : P <;> by_cases ht : 3 * c ≤ 2 * N <;>
    simpa only [gm02ComponentFlagExpr, hp, ht, ↓reduceIte, true_and, false_and,
      Nat.zero_mul, Nat.one_mul] using he

/-- One iteration conjoins the accumulated flag with the component bound,
and preserves every location outside its declared scratch registers and arrays. -/
theorem gm02ComponentTestBody_exec {n k w : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (Q : Finset (Fin n)) (f : Fin k → ℕ)
    (hf : ∀ i, f i ≤ n) (a : Fin n) (s : State) (P : Prop)
    (hw : 4 < 2 ^ w) (hn : 3 * n < 2 ^ w)
    (hadj : IsAdjList G 10 11 12 lists s) (hent : (s.arrs 12).length < 2 ^ w)
    (hrn : s.regs 40 = n) (hra : s.regs 181 = a.val)
    (hq : s.arrs 5 = gm02VertexBits Q) (hslots : ∀ i, s.regs (200 + i.val) = f i)
    (hflag : s.regs 184 = if P then 1 else 0)
    (htotal : s.regs 185 = (Q \ gm02SlotVertices f).card) :
    ∃ s' t, Exec w (gm02ComponentTestBody k) s s' t ∧
      t ≤ 84 + k * 6 + n * (k * 6 + 57) + 29 * totalAdjEntries lists ∧
      Keeps (184 :: gm02ComponentRegs) gm02ComponentArrays s s' ∧
      s'.regs 184 = if P ∧ (a ∉ gm02SlotVertices f →
        3 * (GM02.deletedComponent (Graph.ofSimpleGraph G)
          (gm02SlotVertices (n := n) f : Set (Fin n)) a ∩ (Q : Set (Fin n))).ncard ≤
          2 * (Q \ gm02SlotVertices f).card) then 1 else 0 := by
  have hn' : n < 2 ^ w := (show n ≤ 3 * n by omega).trans_lt hn
  have hcond := gm02TupleFreeExpr_eval_slots 200 181 f a s (by omega) hra hn' hf hslots
  have hcost := gm02TupleFreeExpr_cost 200 (.reg 181) k
  simp only [Expr.cost] at hcost
  by_cases ha : a ∉ gm02SlotVertices (n := n) f
  · simp only [ite_eq_left ha] at hcond
    obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hc₁, _⟩ := gm02ComponentRunProg_exec G lists Q f hf a ha
      s hw hn' hadj hent hrn hra hq hslots
    let c := (GM02.deletedComponent (Graph.ofSimpleGraph G)
      (gm02SlotVertices (n := n) f : Set (Fin n)) a ∩ (Q : Set (Fin n))).ncard
    have hc : c ≤ n := gm02VertexSet_ncard_le _
    have hN : (Q \ gm02SlotVertices f).card ≤ n :=
      (Finset.card_le_card (Finset.sdiff_subset)).trans (by simpa using Finset.card_le_univ Q)
    have hflag₁ : s₁.regs 184 = if P then 1 else 0 := (hk₁.1 _ (by decide)).trans hflag
    have htotal₁ : s₁.regs 185 = (Q \ gm02SlotVertices f).card := (hk₁.1 _ (by decide)).trans htotal
    have he := gm02ComponentFlagExpr_eval s₁ P hw hn hc hN hc₁ htotal₁ hflag₁
    let v := if P ∧ 3 * c ≤ 2 * (Q \ gm02SlotVertices f).card then 1 else 0
    let s₂ := s₁.setReg 184 v
    have hex₂ : Exec w (.assign 184 gm02ComponentFlagExpr) s₁ s₂ 10 := by
      simpa only [gm02ComponentFlagExpr, Expr.cost] using (Exec.assign (r := 184) he)
    have hk₁' : Keeps (184 :: gm02ComponentRegs) gm02ComponentArrays s s₁ :=
      hk₁.mono (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h)
    refine ⟨s₂, (gm02TupleFreeExpr 200 (.reg 181) k).cost + (t₁ + 10),
      .ite_true hcond (by decide) (.seq hex₁ hex₂), ?_, hk₁'.setReg (by simp) _, ?_⟩
    · rw [hcost]
      omega
    · simp [s₂, v, c, ha]
  · simp only [ite_eq_right ha] at hcond
    refine ⟨s, (gm02TupleFreeExpr 200 (.reg 181) k).cost + 1,
      .ite_false hcond (.skip s), ?_, Keeps.refl _ _ _, ?_⟩
    · rw [hcost]
      omega
    · simpa only [ha, false_implies, and_true] using hflag

end GraphMinor.Compute
