module

public import GraphMinor.Compute.GM02ComponentTestBody

/-!
# Testing all remaining components

Scan the numbered vertices and test the component of each vertex outside
the candidate separator. Repeated visits to a component do no harm and
keep the running time polynomial. The accumulated flag at the end is one
exactly when every component passes the test in II (3.1), page 316.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set TwoPaths GraphMinor.Compute.Crossing Classical

/-- Check the component of each vertex, accumulating success in register 184. -/
def gm02ComponentTestLoop (k : ℕ) : Cmd :=
  .seq (.assign 184 (.const 1)) (.seq (.assign 181 (.const 0))
    (forUp 181 (.reg 40) (gm02ComponentTestBody k)))

/-- The complete component loop returns exactly the truth value of the
component test, preserving the candidate slots and input arrays. -/
theorem gm02ComponentTestLoop_exec {n k w : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (Q : Finset (Fin n)) (f : Fin k → ℕ)
    (hf : ∀ i, f i ≤ n) (s : State) (hw : 4 < 2 ^ w) (hn : 3 * n < 2 ^ w)
    (hadj : IsAdjList G 10 11 12 lists s) (hent : (s.arrs 12).length < 2 ^ w)
    (hrn : s.regs 40 = n) (hq : s.arrs 5 = gm02VertexBits Q)
    (hslots : ∀ i, s.regs (200 + i.val) = f i)
    (htotal : s.regs 185 = (Q \ gm02SlotVertices f).card) :
    ∃ s' t, Exec w (gm02ComponentTestLoop k) s s' t ∧
      t ≤ 7 + n * (91 + k * 6 + n * (k * 6 + 57) + 29 * totalAdjEntries lists) ∧
      Keeps (181 :: 184 :: gm02ComponentRegs) gm02ComponentArrays s s' ∧
      s'.regs 184 = if ∀ a : Fin n, a ∉ gm02SlotVertices f →
        3 * (GM02.deletedComponent (Graph.ofSimpleGraph G)
          (gm02SlotVertices (n := n) f : Set (Fin n)) a ∩ (Q : Set (Fin n))).ncard ≤
          2 * (Q \ gm02SlotVertices f).card then 1 else 0 := by
  classical
  let good : Fin n → Prop := fun a => a ∉ gm02SlotVertices f →
    3 * (GM02.deletedComponent (Graph.ofSimpleGraph G)
      (gm02SlotVertices (n := n) f : Set (Fin n)) a ∩ (Q : Set (Fin n))).ncard ≤
      2 * (Q \ gm02SlotVertices f).card
  let R := 181 :: 184 :: gm02ComponentRegs
  let I : ℕ → State → Prop := fun i st => st.regs 181 = i ∧
    Keeps R gm02ComponentArrays s st ∧
    st.regs 184 = if ∀ a : Fin n, a.val < i → good a then 1 else 0
  let s₁ := s.setReg 184 1
  let s₂ := s₁.setReg 181 0
  have hk₁ : Keeps R gm02ComponentArrays s s₁ := (Keeps.refl _ _ s).setReg (by simp [R]) _
  have hk₂ : Keeps R gm02ComponentArrays s s₂ := hk₁.setReg (by simp [R]) _
  have hI₀ : I 0 s₂ := by
    refine ⟨by simp [s₂], hk₂, ?_⟩
    simp [s₂, s₁]
  have hn' : n < 2 ^ w := (show n ≤ 3 * n by omega).trans_lt hn
  let B := 84 + k * 6 + n * (k * 6 + 57) + 29 * totalAdjEntries lists
  obtain ⟨s', t, hex, ht, hI⟩ := forUp_exec' I n B (by omega) hn'
    (fun i hi st hI => ⟨hI.1, eval_reg ((hI.2.1.1 _ (by decide)).trans hrn) hn'⟩)
    (fun i hi st hI => by
      let a : Fin n := ⟨i, hi⟩
      have hadjst := hadj.of_arrs_eq (hI.2.1.2 _ (by decide))
        (hI.2.1.2 _ (by decide)) (hI.2.1.2 _ (by decide))
      have hslotst : ∀ j, st.regs (200 + j.val) = f j := by
        intro j
        apply (hI.2.1.1 _ ?_).trans (hslots j)
        dsimp only [Reg]
        simp [R, gm02ComponentRegs]
        omega
      obtain ⟨st', t', hex', ht', hk', hflag'⟩ := gm02ComponentTestBody_exec G lists Q f hf a st
        (∀ v : Fin n, v.val < i → good v) hw hn hadjst
        (by simpa only [hI.2.1.2 12 (by decide)] using hent)
        ((hI.2.1.1 _ (by decide)).trans hrn) hI.1
        ((hI.2.1.2 _ (by decide)).trans hq) hslotst (by
          by_cases hp : ∀ v : Fin n, v.val < i → good v
          · simpa only [ite_eq_left hp] using hI.2.2
          · simpa only [ite_eq_right hp] using hI.2.2)
        ((hI.2.1.1 _ (by decide)).trans htotal)
      have hprop : ((∀ v : Fin n, v.val < i → good v) ∧ good a) ↔
          ∀ v : Fin n, v.val < i + 1 → good v := by
        constructor
        · rintro ⟨hprev, hlast⟩ v hv
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hv) with hlt | heq
          · exact hprev v hlt
          · exact (show v = a from Fin.ext heq) ▸ hlast
        · intro h
          exact ⟨fun v hv => h v (Nat.lt_succ_of_lt hv), h a (Nat.lt_succ_self i)⟩
      have hk'R : Keeps R gm02ComponentArrays st st' :=
        hk'.mono (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h)
      have hframe := hI.2.1.trans hk'R (fun _ h => h) (fun _ h => h)
      refine ⟨st', t', hex', ht', ?_, ?_⟩
      · refine ⟨by simp, hframe.setReg (by simp [R]) _, ?_⟩
        simp only [State.setReg_regs_ne _ _ (show (184 : Reg) ≠ 181 by decide)]
        change st'.regs 184 = if ∀ v : Fin n, v.val < i + 1 → good v then 1 else 0
        by_cases hp : ∀ v : Fin n, v.val < i + 1 → good v
        · have hh := hprop.mpr hp
          dsimp only [good] at hh hflag'
          simpa only [ite_eq_left hp] using
            (show st'.regs 184 = 1 by simpa only [ite_eq_left hh] using hflag')
        · have hh : ¬((∀ v : Fin n, v.val < i → good v) ∧ good a) := fun h => hp (hprop.mp h)
          dsimp only [good] at hh hflag'
          simpa only [ite_eq_right hp] using
            (show st'.regs 184 = 0 by simpa only [ite_eq_right hh] using hflag')
      · exact (hk'.1 _ (by decide)).trans hI.1)
    s₂ hI₀
  have he₁ : Exec w (.assign 184 (.const 1)) s s₁ 2 := .assign (eval_const (by omega))
  have he₂ : Exec w (.assign 181 (.const 0)) s₁ s₂ 2 := .assign (eval_const (Nat.two_pow_pos w))
  refine ⟨s', 2 + (2 + t), .seq he₁ (.seq he₂ hex), ?_, hI.2.1, ?_⟩
  · have hc : 1 + 6 + B = 91 + k * 6 + n * (k * 6 + 57) + 29 * totalAdjEntries lists := by
      dsimp [B]
      omega
    simp only [Expr.cost] at ht
    rw [hc] at ht
    omega
  · have hp : (∀ a : Fin n, a.val < n → good a) ↔ ∀ a : Fin n, good a :=
      ⟨fun h a => h a a.isLt, fun h a _ => h a⟩
    simpa only [hp] using hI.2.2

end GraphMinor.Compute
