module

public import GraphMinor.Compute.GM02CodeSearchBody

/-!
# Exhaustive search for a successful separator code

Scan all codes of the fixed length in base one plus the vertex count.
Each successful component test updates the stored code. The invariant
says either all earlier codes failed, or the stored earlier code passed.
At termination this supplies a successful separator code or a valid
rejection of every candidate in II (3.1), page 316.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set TwoPaths GraphMinor.Compute.Crossing Classical

/-- Enumerate all codes, keeping a found bit and a successful code. -/
def gm02CodeSearchLoop (k : ℕ) : Cmd :=
  .seq (.assign 186 (.const 0)) (.seq (.assign 190 (.const 0))
    (forUp 190 (gm02PowerExpr gm02CodeBaseExpr k) (gm02CodeSearchBody k)))

/-- The exhaustive code loop either rejects every candidate or stores a
code whose deleted components satisfy the required terminal bound. -/
theorem gm02CodeSearchLoop_exec {n k w : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (Q : Finset (Fin n)) (s : State)
    (hw : 4 < 2 ^ w) (hn : 3 * n < 2 ^ w) (hb : n + 1 < 2 ^ w)
    (hp : (n + 1) ^ k < 2 ^ w)
    (hadj : IsAdjList G 10 11 12 lists s) (hent : (s.arrs 12).length < 2 ^ w)
    (hrn : s.regs 40 = n) (hq : s.arrs 5 = gm02VertexBits Q) :
    ∃ s' t, Exec w (gm02CodeSearchLoop k) s s' t ∧
      t ≤ 7 + 4 * k + (n + 1) ^ k *
        (35 + 4 * k + k * (8 + 4 * k) + n * (k * 6 + 36) +
          n * (91 + k * 6 + n * (k * 6 + 57) + 29 * totalAdjEntries lists)) ∧
      Keeps (190 :: gm02CodeSearchRegs k) gm02ComponentArrays s s' ∧
      let good := fun code => ∀ a : Fin n,
        a ∉ gm02SlotVertices (fun i : Fin k => gm02SeparatorDigit n code i.val) →
        3 * (GM02.deletedComponent (Graph.ofSimpleGraph G)
          (gm02SlotVertices (n := n) (fun i : Fin k => gm02SeparatorDigit n code i.val) : Set (Fin n)) a ∩
            (Q : Set (Fin n))).ncard ≤
          2 * (Q \ gm02SlotVertices (fun i : Fin k => gm02SeparatorDigit n code i.val)).card
      (s'.regs 186 = 0 ∧ ∀ code < (n + 1) ^ k, ¬good code) ∨
      (s'.regs 186 = 1 ∧ s'.regs 191 < (n + 1) ^ k ∧ good (s'.regs 191)) := by
  classical
  let good := fun code => ∀ a : Fin n,
    a ∉ gm02SlotVertices (fun i : Fin k => gm02SeparatorDigit n code i.val) →
    3 * (GM02.deletedComponent (Graph.ofSimpleGraph G)
      (gm02SlotVertices (n := n) (fun i : Fin k => gm02SeparatorDigit n code i.val) : Set (Fin n)) a ∩
        (Q : Set (Fin n))).ncard ≤
      2 * (Q \ gm02SlotVertices (fun i : Fin k => gm02SeparatorDigit n code i.val)).card
  let R := 190 :: gm02CodeSearchRegs k
  let I : ℕ → State → Prop := fun i st => st.regs 190 = i ∧
    Keeps R gm02ComponentArrays s st ∧
    ((st.regs 186 = 0 ∧ ∀ code < i, ¬good code) ∨
      (st.regs 186 = 1 ∧ st.regs 191 < i ∧ good (st.regs 191)))
  let s₁ := s.setReg 186 0
  let s₂ := s₁.setReg 190 0
  have hk₁ : Keeps R gm02ComponentArrays s s₁ := (Keeps.refl _ _ s).setReg (by simp [R, gm02CodeSearchRegs]) _
  have hk₂ : Keeps R gm02ComponentArrays s s₂ := hk₁.setReg (by simp [R]) _
  have hI₀ : I 0 s₂ := by
    refine ⟨by simp [s₂], hk₂, Or.inl ⟨?_, ?_⟩⟩
    · simp [s₂, s₁]
    · intro code hc
      omega
  have h40 : 40 ∉ R := by
    simp only [R, gm02CodeSearchRegs, List.mem_cons, List.mem_append, not_or]
    exact ⟨by decide, by decide, by decide, not_mem_gm02SlotRegs (by decide), by decide⟩
  have hn' : n < 2 ^ w := (Nat.lt_succ_self n).trans hb
  have hlim (st : State) (hk : Keeps R gm02ComponentArrays s st) :
      (gm02PowerExpr gm02CodeBaseExpr k).eval w st = some ((n + 1) ^ k) :=
    gm02PowerExpr_eval _ _ _ (Nat.succ_le_succ (Nat.zero_le n))
      (eval_add (eval_reg ((hk.1 _ h40).trans hrn) hn') (eval_const (by omega)) hb) hp
  let B := 28 + k * (8 + 4 * k) + n * (k * 6 + 36) +
    n * (91 + k * 6 + n * (k * 6 + 57) + 29 * totalAdjEntries lists)
  obtain ⟨s', t, hex, ht, hI⟩ := forUp_exec' I ((n + 1) ^ k) B (by omega) hp
    (fun i hi st hI => ⟨hI.1, hlim st hI.2.1⟩)
    (fun i hi st hI => by
      have hadjst := hadj.of_arrs_eq (hI.2.1.2 _ (by decide))
        (hI.2.1.2 _ (by decide)) (hI.2.1.2 _ (by decide))
      obtain ⟨st', t', he', ht', hk', hu⟩ := gm02CodeSearchBody_exec G lists Q st hw hn hb
        (hi.trans hp) hp hadjst (by simpa only [hI.2.1.2 12 (by decide)] using hent)
        ((hI.2.1.1 _ h40).trans hrn) ((hI.2.1.2 _ (by decide)).trans hq) hI.1
      have hk'R : Keeps R gm02ComponentArrays st st' :=
        hk'.mono (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h)
      have hknew := (hI.2.1.trans hk'R (fun _ h => h) (fun _ h => h)).setReg
        (show 190 ∈ R by simp [R]) (i + 1)
      have h190 : 190 ∉ gm02CodeSearchRegs k := by
        simp only [gm02CodeSearchRegs, List.mem_cons, List.mem_append, not_or]
        exact ⟨by decide, by decide, not_mem_gm02SlotRegs (by decide), by decide⟩
      refine ⟨st', t', he', ht', ⟨by simp, hknew, ?_⟩, (hk'.1 _ h190).trans hI.1⟩
      simp only [State.setReg_regs_ne _ _ (show (186 : Reg) ≠ 190 by decide),
        State.setReg_regs_ne _ _ (show (191 : Reg) ≠ 190 by decide)]
      by_cases hg : good i
      · have hgr := hg
        dsimp only [good] at hgr
        simp only [ite_eq_left hgr] at hu
        exact Or.inr ⟨hu.1, by rw [hu.2]; omega, by simpa only [hu.2] using hg⟩
      · have hgr := hg
        dsimp only [good] at hgr
        simp only [ite_eq_right hgr] at hu
        rcases hI.2.2 with ⟨hzero, hprev⟩ | ⟨hone, hlt, hold⟩
        · refine Or.inl ⟨hu.1.trans hzero, ?_⟩
          intro code hcode
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hcode) with hlt | rfl
          · exact hprev code hlt
          · exact hg
        · exact Or.inr ⟨hu.1.trans hone, by rw [hu.2]; omega, by simpa only [hu.2] using hold⟩)
    s₂ hI₀
  have he₁ : Exec w (.assign 186 (.const 0)) s s₁ 2 := .assign (eval_const (Nat.two_pow_pos w))
  have he₂ : Exec w (.assign 190 (.const 0)) s₁ s₂ 2 := .assign (eval_const (Nat.two_pow_pos w))
  refine ⟨s', 2 + (2 + t), .seq he₁ (.seq he₂ hex), ?_, hI.2.1, hI.2.2⟩
  have hc : (gm02PowerExpr gm02CodeBaseExpr k).cost = 1 + 4 * k := by
    rw [gm02PowerExpr_cost]
    simp only [gm02CodeBaseExpr, Expr.cost]
    omega
  rw [hc] at ht
  have heq : (1 + 4 * k + 6 + B) =
      35 + 4 * k + k * (8 + 4 * k) + n * (k * 6 + 36) +
        n * (91 + k * 6 + n * (k * 6 + 57) + 29 * totalAdjEntries lists) := by dsimp [B]; omega
  rw [heq] at ht
  omega

end GraphMinor.Compute
