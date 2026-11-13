module

public import GraphMinor.Compute.GM02GroupingBody
public import GraphMinor.Compute.GM02GroupingComplete

/-!
# Constructing the balanced side on the RAM

Start with an empty selected side and scan all vertices using the greedy
grouping iteration. The loop follows the data-only grouping state exactly.
The proved grouping invariants supply component closure at each step,
and the completed-state theorem gives balance at the end. This is the
successful-output construction of II (3.1), page 316.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set TwoPaths GraphMinor.Compute.Crossing Classical

/-- Initialize the selected side and run the greedy component-grouping scan. -/
def gm02GroupingLoop (k : ℕ) : Cmd :=
  .seq (.alloc 70 (.reg 40)) (.seq (.assign 187 (.const 0))
    (.seq (.assign 188 (.op .eq (.reg 185) (.const 0)))
      (.seq (.assign 181 (.const 0)) (forUp 181 (.reg 40) (gm02GroupingBody k)))))

/-- The RAM grouping loop writes the exact balanced side proved by the
component-grouping argument, with a polynomial time bound. -/
theorem gm02GroupingLoop_exec {n k w : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (Q X : Finset (Fin n))
    (f : Fin k → ℕ) (hf : ∀ i, f i ≤ n) (hX : X = gm02SlotVertices f)
    (hcomp : ∀ a ∉ X, 3 * (gm02FiniteComponent G X a ∩ Q).card ≤ 2 * (Q \ X).card)
    (s : State) (hw : 4 < 2 ^ w) (hn : 3 * n < 2 ^ w)
    (hadj : IsAdjList G 10 11 12 lists s) (hent : (s.arrs 12).length < 2 ^ w)
    (hrn : s.regs 40 = n) (hq : s.arrs 5 = gm02VertexBits Q)
    (hslots : ∀ i, s.regs (200 + i.val) = f i) (hN : s.regs 185 = (Q \ X).card) :
    ∃ s' t, Exec w (gm02GroupingLoop k) s s' t ∧
      t ≤ 12 + n + n * (114 + 6 * k + n * (k * 6 + 94) + 29 * totalAdjEntries lists) ∧
      Keeps (181 :: gm02GroupingRegs) gm02GroupingArrays s s' ∧
      s'.arrs 70 = gm02VertexBits (gm02GroupingState G Q X n).1 ∧
      s'.regs 187 = ((gm02GroupingState G Q X n).1 ∩ Q).card ∧ s'.regs 188 = 1 := by
  classical
  have hn' : n < 2 ^ w := (show n ≤ 3 * n by omega).trans_lt hn
  have hNw : (Q \ X).card < 2 ^ w :=
    ((Finset.card_le_card Finset.sdiff_subset).trans (by simpa using Finset.card_le_univ Q)).trans_lt hn'
  let R := 181 :: gm02GroupingRegs
  let s₁ := s.setArr 70 (List.replicate n 0)
  let s₂ := s₁.setReg 187 0
  let s₃ := s₂.setReg 188 (if (Q \ X).card = 0 then 1 else 0)
  let s₄ := s₃.setReg 181 0
  have hk₁ : Keeps R gm02GroupingArrays s s₁ := (Keeps.refl _ _ s).setArr (by decide) _
  have hk₂ : Keeps R gm02GroupingArrays s s₂ := hk₁.setReg (by simp [R, gm02GroupingRegs]) _
  have hk₃ : Keeps R gm02GroupingArrays s s₃ := hk₂.setReg (by simp [R, gm02GroupingRegs]) _
  have hk₄ : Keeps R gm02GroupingArrays s s₄ := hk₃.setReg (by simp [R]) _
  let I : ℕ → State → Prop := fun i st => st.regs 181 = i ∧
    Keeps R gm02GroupingArrays s st ∧
    st.arrs 70 = gm02VertexBits (gm02GroupingState G Q X i).1 ∧
    st.regs 187 = ((gm02GroupingState G Q X i).1 ∩ Q).card ∧
    st.regs 188 = if (gm02GroupingState G Q X i).2 then 1 else 0
  have hI₀ : I 0 s₄ := by
    refine ⟨by simp [s₄], hk₄, ?_, ?_, ?_⟩
    · simp [s₄, s₃, s₂, s₁, gm02GroupingState, gm02VertexBits]
    · simp [s₄, s₃, s₂, gm02GroupingState]
    · simp only [s₄, s₃, State.setReg_regs_ne _ _ (show (188 : Reg) ≠ 181 by decide),
        State.setReg_regs_self, gm02GroupingState, decide_eq_true_eq]
  let B := 107 + 6 * k + n * (k * 6 + 94) + 29 * totalAdjEntries lists
  obtain ⟨s', t, hex, ht, hI⟩ := forUp_exec' I n B (by omega) hn'
    (fun i hi st hI => ⟨hI.1, eval_reg ((hI.2.1.1 _ (by decide)).trans hrn) hn'⟩)
    (fun i hi st hI => by
      let a : Fin n := ⟨i, hi⟩
      have hclosed := (gm02GroupingState_invariants G Q X hcomp i (Nat.le_of_lt hi)).2.1
      have hadjst := hadj.of_arrs_eq (hI.2.1.2 _ (by decide))
        (hI.2.1.2 _ (by decide)) (hI.2.1.2 _ (by decide))
      have hslotst : ∀ j, st.regs (200 + j.val) = f j := by
        intro j
        apply (hI.2.1.1 _ ?_).trans (hslots j)
        dsimp only [Reg]
        simp [R, gm02GroupingRegs, gm02ComponentRegs]
        omega
      obtain ⟨st', t', he', ht', hk', hout⟩ := gm02GroupingBody_exec G lists Q X
        (gm02GroupingState G Q X i) f hf hX a hclosed st hw hn hadjst
        (by simpa only [hI.2.1.2 12 (by decide)] using hent)
        ((hI.2.1.1 _ (by decide)).trans hrn) hI.1 ((hI.2.1.2 _ (by decide)).trans hq)
        hslotst hI.2.2.1 hI.2.2.2.1 hI.2.2.2.2 ((hI.2.1.1 _ (by decide)).trans hN)
      have hstate : gm02GroupingState G Q X (i + 1) =
          gm02GroupingStep G Q X a (gm02GroupingState G Q X i) := by
        rw [gm02GroupingState, dite_eq_left hi]
      rw [← hstate] at hout
      have hk'R : Keeps R gm02GroupingArrays st st' :=
        hk'.mono (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h)
      have hframe := (hI.2.1.trans hk'R (fun _ h => h) (fun _ h => h)).setReg
        (show 181 ∈ R by simp [R]) (i + 1)
      refine ⟨st', t', he', ht', ⟨by simp, hframe, ?_, ?_, ?_⟩,
        (hk'.1 _ (by decide)).trans hI.1⟩
      · exact hout.1
      · simpa only [State.setReg_regs_ne _ _ (show (187 : Reg) ≠ 181 by decide)] using hout.2.1
      · simpa only [State.setReg_regs_ne _ _ (show (188 : Reg) ≠ 181 by decide)] using hout.2.2)
    s₄ hI₀
  have he₁ : Exec w (.alloc 70 (.reg 40)) s s₁ (1 + n) := .alloc (eval_reg hrn hn')
  have he₂ : Exec w (.assign 187 (.const 0)) s₁ s₂ 2 := .assign (eval_const (Nat.two_pow_pos w))
  have h185₂ : s₂.regs 185 = (Q \ X).card := (hk₂.1 _ (by decide)).trans hN
  have he₃ : Exec w (.assign 188 (.op .eq (.reg 185) (.const 0))) s₂ s₃ 4 :=
    .assign (eval_eq (eval_reg h185₂ hNw) (eval_const (Nat.two_pow_pos w)) (by omega))
  have he₄ : Exec w (.assign 181 (.const 0)) s₃ s₄ 2 := .assign (eval_const (Nat.two_pow_pos w))
  refine ⟨s', (1 + n) + (2 + (4 + (2 + t))), .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ hex))),
    ?_, hI.2.1, hI.2.2.1, hI.2.2.2.1, ?_⟩
  · simp only [Expr.cost] at ht
    have hc : 1 + 6 + B = 114 + 6 * k + n * (k * 6 + 94) + 29 * totalAdjEntries lists := by dsimp [B]; omega
    rw [hc] at ht
    omega
  · have hr := (gm02GroupingState_complete G Q X hcomp).1
    simpa only [hr, ↓reduceIte] using hI.2.2.2.2

end GraphMinor.Compute
