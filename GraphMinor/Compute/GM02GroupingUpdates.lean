module

public import GraphMinor.Compute.GM02UnionLabelBits

/-!
# Updating the selected side and its terminal count

The grouping in II (3.1) either chooses a component alone or adds a new
small component to the old side. These RAM routines update the side bits,
the stored terminal count, and the threshold flag. Disjointness of the
old side and a new component justifies adding their counts.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing TwoPaths Classical

/-- Test whether the selected terminal count has reached one third. -/
def gm02GroupingThresholdExpr (count : Reg := 187) : Expr :=
  .op .le (.reg 185) (.op .mul (.const 3) (.reg count))

/-- Choose a whole component and mark the grouping complete. -/
def gm02TakeComponentProg : Cmd := .seq (gm02CopyLabelBitsProg 60 70)
  (.seq (.assign 187 (.reg 183)) (.assign 188 (.const 1)))

/-- Add a component, update the terminal count, and test the threshold. -/
def gm02AddComponentProg : Cmd := .seq (gm02UnionLabelBitsProg 60)
  (.seq (.assign 187 (.op .add (.reg 187) (.reg 183))) (.assign 188 gm02GroupingThresholdExpr))

/-- The threshold comparison uses bounded words and returns the exact bit. -/
theorem gm02GroupingThresholdExpr_eval {n w N c : ℕ} (s : State) (count : Reg)
    (hw : 4 < 2 ^ w) (hn : 3 * n < 2 ^ w) (hN : N ≤ n) (hc : c ≤ n)
    (h185 : s.regs 185 = N) (h187 : s.regs count = c) :
    (gm02GroupingThresholdExpr count).eval w s = some (if N ≤ 3 * c then 1 else 0) := by
  have heN := eval_reg h185 ((show N ≤ 3 * n by omega).trans_lt hn)
  have hec := eval_reg h187 ((show c ≤ 3 * n by omega).trans_lt hn)
  have hemul := eval_mul (eval_const (show 3 < 2 ^ w by omega)) hec
    ((Nat.mul_le_mul_left 3 hc).trans_lt hn)
  change (match (Expr.reg 185).eval w s, (.op .mul (.const 3) (.reg count) : Expr).eval w s with
    | some x, some y => BinOp.le.eval w x y
    | _, _ => none) = _
  rw [heN, hemul]
  by_cases h : N ≤ 3 * c <;> simp [BinOp.eval, BinOp.raw, checkWord, h, show 1 < 2 ^ w by omega]

/-- Taking a whole component writes its bits and count and sets the ready flag. -/
theorem gm02TakeComponentProg_exec {n w : ℕ} (Q C : Finset (Fin n))
    (mask : Fin n → ℕ) (hm : ∀ v, mask v ≤ 2) (hC : ∀ v, mask v = 1 ↔ v ∈ C)
    (s : State) (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hrn : s.regs 40 = n)
    (hmask : s.arrs 60 = List.ofFn mask) (hcount : s.regs 183 = (C ∩ Q).card) :
    ∃ s' t, Exec w gm02TakeComponentProg s s' t ∧ t ≤ 10 + n * 16 ∧
      Keeps [180, 187, 188] [70] s s' ∧ s'.arrs 70 = gm02VertexBits C ∧
      s'.regs 187 = (C ∩ Q).card ∧ s'.regs 188 = 1 := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hout⟩ := gm02CopyLabelBitsProg_exec C mask hm hC 60 70
    (by decide) s hw hn hrn hmask
  have hc : (C ∩ Q).card < 2 ^ w :=
    (show (C ∩ Q).card ≤ n from (Finset.card_le_card Finset.inter_subset_left).trans
      (by simpa using Finset.card_le_univ C)).trans_lt hn
  let s₂ := s₁.setReg 187 (C ∩ Q).card
  let s₃ := s₂.setReg 188 1
  have he₂ : Exec w (.assign 187 (.reg 183)) s₁ s₂ 2 :=
    .assign (eval_reg ((hk₁.1 _ (by decide)).trans hcount) hc)
  have he₃ : Exec w (.assign 188 (.const 1)) s₂ s₃ 2 := .assign (eval_const (by omega))
  have hk₁' : Keeps [180, 187, 188] [70] s s₁ :=
    hk₁.mono (by intro r hr; obtain rfl := List.mem_singleton.1 hr; simp) (fun _ h => h)
  refine ⟨s₃, t₁ + (2 + 2), .seq he₁ (.seq he₂ he₃), by omega,
    (hk₁'.setReg (by simp) _).setReg (by simp) _, ?_, ?_, ?_⟩
  · exact hout
  · simp [s₃, s₂]
  · simp [s₃]

/-- Adding a new disjoint component updates the side, exact terminal count,
and ready flag in linear time. -/
theorem gm02AddComponentProg_exec {n w N : ℕ} (Q Y C : Finset (Fin n)) (hdis : Disjoint Y C)
    (mask : Fin n → ℕ) (hm : ∀ v, mask v ≤ 2) (hC : ∀ v, mask v = 1 ↔ v ∈ C)
    (s : State) (hw : 4 < 2 ^ w) (hn : 3 * n < 2 ^ w) (hN : N ≤ n)
    (hrn : s.regs 40 = n) (hmask : s.arrs 60 = List.ofFn mask)
    (hY : s.arrs 70 = gm02VertexBits Y) (hcount : s.regs 183 = (C ∩ Q).card)
    (hcountY : s.regs 187 = (Y ∩ Q).card) (h185 : s.regs 185 = N) :
    ∃ s' t, Exec w gm02AddComponentProg s s' t ∧ t ≤ 22 + n * 37 ∧
      Keeps [180, 187, 188] [70, 71] s s' ∧ s'.arrs 70 = gm02VertexBits (Y ∪ C) ∧
      s'.regs 187 = ((Y ∪ C) ∩ Q).card ∧
      s'.regs 188 = if N ≤ 3 * ((Y ∪ C) ∩ Q).card then 1 else 0 := by
  have hn' : n < 2 ^ w := (show n ≤ 3 * n by omega).trans_lt hn
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hout⟩ := gm02UnionLabelBitsProg_exec Y C mask hm hC 60
    (by decide) (by decide) s (by omega) hn' hrn hY hmask
  have hsum : ((Y ∪ C) ∩ Q).card = (Y ∩ Q).card + (C ∩ Q).card := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_of_disjoint (hdis.mono Finset.inter_subset_left Finset.inter_subset_left)
  have hbound : ((Y ∪ C) ∩ Q).card ≤ n :=
    (Finset.card_le_card Finset.inter_subset_right).trans (by simpa using Finset.card_le_univ Q)
  have heval := eval_add (eval_reg ((hk₁.1 _ (by decide)).trans hcountY)
    ((show (Y ∩ Q).card ≤ n from (Finset.card_le_card Finset.inter_subset_right).trans
      (by simpa using Finset.card_le_univ Q)).trans_lt hn'))
    (eval_reg ((hk₁.1 _ (by decide)).trans hcount)
    ((show (C ∩ Q).card ≤ n from (Finset.card_le_card Finset.inter_subset_right).trans
      (by simpa using Finset.card_le_univ Q)).trans_lt hn'))
    (by rw [← hsum]; exact hbound.trans_lt hn')
  let s₂ := s₁.setReg 187 ((Y ∪ C) ∩ Q).card
  have he₂ : Exec w (.assign 187 (.op .add (.reg 187) (.reg 183))) s₁ s₂ 4 := by
    simpa only [← hsum, Expr.cost] using (Exec.assign (r := 187) heval)
  have heflag := gm02GroupingThresholdExpr_eval s₂ 187 hw hn hN hbound
    (by simpa only [s₂, State.setReg_regs_ne _ _ (show (185 : Reg) ≠ 187 by decide)] using
      (hk₁.1 _ (by decide)).trans h185) (by simp [s₂])
  let v := if N ≤ 3 * ((Y ∪ C) ∩ Q).card then 1 else 0
  let s₃ := s₂.setReg 188 v
  have he₃ : Exec w (.assign 188 gm02GroupingThresholdExpr) s₂ s₃ 6 := by
    simpa only [gm02GroupingThresholdExpr, Expr.cost] using (Exec.assign (r := 188) heflag)
  have hk₁' : Keeps [180, 187, 188] [70, 71] s s₁ :=
    hk₁.mono (by intro r hr; obtain rfl := List.mem_singleton.1 hr; simp) (fun _ h => h)
  refine ⟨s₃, t₁ + (4 + 6), .seq he₁ (.seq he₂ he₃), by omega,
    (hk₁'.setReg (by simp) _).setReg (by simp) _, hout, ?_, ?_⟩
  · simp [s₃, s₂]
  · simp [s₃, v]

end GraphMinor.Compute
