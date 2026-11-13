module

public import GraphMinor.Compute.GM13SocietyRecordScan
public import GraphMinor.Compute.GM13SocietyLoopOwners

/-!
# Finding a loop owner by scanning the division records

For one vertex, read its bit in each member record. Whenever the bit is
one, store that member's index. This gives the last containing member,
including for isolated boundary vertices. Edge lists are skipped by their
stored lengths, so each member costs constant time for this query.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Read a vertex bit in the member at the current record address. -/
def gm13MemberBit : Expr := .read 65 (.op .add (.reg 20) (.reg 24))

/-- The membership bit is the vertex bit of the serialized member. -/
theorem gm13MemberBit_eval {w n : ℕ} (A : Finset (Fin n) × List (Fin n × Fin n))
    (pre suf : List ℕ) (v : Fin n)
    (hw : (pre ++ encAlg86Subgraph A.1 A.2).length < 2 ^ w)
    {s : State} (hin : s.arrs 65 = pre ++ encAlg86Subgraph A.1 A.2 ++ suf)
    (hoff : s.regs 20 = pre.length) (hv : s.regs 24 = v.1) :
    gm13MemberBit.eval w s = some (if v ∈ A.1 then 1 else 0) := by
  have hlen := length_encAlg86Subgraph A.1 A.2
  have hpre : pre.length + v.1 < 2 ^ w := by
    simp only [List.length_append, hlen] at hw
    omega
  have hw1 : 1 < 2 ^ w := by
    simp only [List.length_append, hlen] at hw
    omega
  apply gm13_read_eval (eval_add (eval_reg hoff (by omega)) (eval_reg hv (by omega)) hpre)
  · rw [hin, List.append_assoc, List.getElem?_append_right (by omega),
      Nat.add_sub_cancel_left]
    simp only [encAlg86Subgraph, List.append_assoc]
    rw [List.getElem?_append_left (by simpa only [length_bitSetList] using v.2),
      List.getElem?_eq_getElem (by simpa only [length_bitSetList] using v.2),
      getElem_bitSetList]
  · split <;> omega

/-- Update the one-based owner index if the current member contains the vertex. -/
def gm13OwnerUpdateProg : Cmd :=
  .ite gm13MemberBit (.assign 25 (.op .add (.reg 22) (.const 1))) .skip

/-- The update changes only the owner register. -/
theorem gm13OwnerUpdateProg_exec {w n : ℕ}
    (A : Finset (Fin n) × List (Fin n × Fin n)) (pre suf : List ℕ) (v : Fin n)
    (k owner : ℕ) (hkw : k + 1 < 2 ^ w)
    (hw : (pre ++ encAlg86Subgraph A.1 A.2).length < 2 ^ w)
    {s : State} (hin : s.arrs 65 = pre ++ encAlg86Subgraph A.1 A.2 ++ suf)
    (hoff : s.regs 20 = pre.length) (hv : s.regs 24 = v.1)
    (hk : s.regs 22 = k) (ho : s.regs 25 = owner) :
    ∃ s' t, Exec w gm13OwnerUpdateProg s s' t ∧ t ≤ 8 ∧
      s'.regs 25 = (if v ∈ A.1 then k + 1 else owner) ∧ s'.arrs = s.arrs ∧
      (∀ r : ℕ, r ≠ 25 → s'.regs r = s.regs r) := by
  have hb := gm13MemberBit_eval A pre suf v hw hin hoff hv
  have h1 : 1 < 2 ^ w := by omega
  by_cases hmem : v ∈ A.1
  · simp only [hmem, ↓reduceIte] at hb ⊢
    let s' := s.setReg 25 (k + 1)
    have he : Exec w (.assign 25 (.op .add (.reg 22) (.const 1))) s s' 4 :=
      .assign (eval_add (eval_reg hk (by omega)) (eval_const h1) hkw)
    exact ⟨s', 8, .ite_true hb (by decide) he, le_rfl, by simp [s'], rfl,
      fun r hr => by simp [s', hr]⟩
  · simp only [hmem, ↓reduceIte] at hb ⊢
    exact ⟨s, 5, .ite_false hb (.skip s), by decide, ho, rfl, fun _ _ => rfl⟩

/-- Query every remaining record for one vertex. -/
def gm13OwnerQueryLoop : Cmd :=
  forUp 22 (.reg 21) (.seq gm13OwnerUpdateProg gm13SkipRecordProg)

/-- One query costs constant time per member and returns exactly the last
containing-member index after the supplied initial owner. -/
theorem gm13OwnerQueryLoop_exec {w n : ℕ}
    (L : List (Finset (Fin n) × List (Fin n × Fin n))) (pre suf : List ℕ)
    (v : Fin n) (k N owner : ℕ) (hN : k + L.length = N) (hNw : N < 2 ^ w)
    (hw : (pre ++ L.flatMap (fun A => encAlg86Subgraph A.1 A.2)).length < 2 ^ w)
    {s : State} (hin : s.arrs 65 = pre ++ L.flatMap (fun A => encAlg86Subgraph A.1 A.2) ++ suf)
    (hoff : s.regs 20 = pre.length) (hn : s.regs 0 = n)
    (hcount : s.regs 21 = N) (hk : s.regs 22 = k)
    (hv : s.regs 24 = v.1) (ho : s.regs 25 = owner) (hw1 : 1 < 2 ^ w) :
    ∃ s' t, Exec w gm13OwnerQueryLoop s s' t ∧ t ≤ 32 * L.length + 3 ∧
      s'.regs 25 = gm13OwnerFrom L k owner v ∧ s'.arrs = s.arrs ∧
      (∀ r : ℕ, r ≠ 20 → r ≠ 22 → r ≠ 23 → r ≠ 25 → s'.regs r = s.regs r) := by
  induction L generalizing pre k owner s with
  | nil =>
    have hkn : k = N := by simpa using hN
    have htest : (Expr.op .lt (.reg 22) (.reg 21)).eval w s = some 0 := by
      simpa [hkn] using eval_lt (eval_reg hk (by omega)) (eval_reg hcount hNw) hw1
    exact ⟨s, 3, .while_false htest, by simp, ho, rfl, fun _ _ _ _ _ => rfl⟩
  | cons A rest ih =>
    have hkN : k < N := by simp only [List.length_cons] at hN; omega
    have htest : (Expr.op .lt (.reg 22) (.reg 21)).eval w s = some 1 := by
      simpa [hkN] using eval_lt (eval_reg hk (by omega)) (eval_reg hcount hNw) hw1
    have hrec : (pre ++ encAlg86Subgraph A.1 A.2).length < 2 ^ w := by
      simp only [List.flatMap_cons, List.length_append] at hw ⊢
      omega
    let suf' := rest.flatMap (fun A => encAlg86Subgraph A.1 A.2) ++ suf
    have hinput : s.arrs 65 = pre ++ encAlg86Subgraph A.1 A.2 ++ suf' := by
      simpa only [suf', List.flatMap_cons, List.append_assoc] using hin
    obtain ⟨s₁, t₁, he₁, ht₁, ho₁, ha₁, hr₁⟩ :=
      gm13OwnerUpdateProg_exec (w := w) A pre suf' v k owner (by omega)
        hrec hinput hoff hv hk ho
    obtain ⟨s₂, he₂, hoff₂, ha₂, hr₂⟩ :=
      gm13SkipRecordProg_exec (w := w) A pre suf' hrec (by rw [ha₁]; exact hinput)
        ((hr₁ 20 (by decide)).trans hoff) ((hr₁ 0 (by decide)).trans hn)
    let s₃ := s₂.setReg 22 (k + 1)
    have he₃ : Exec w (.assign 22 (.op .add (.reg 22) (.const 1))) s₂ s₃ 4 :=
      .assign (eval_add (eval_reg (((hr₂ 22 (by decide) (by decide)).trans
        (hr₁ 22 (by decide))).trans hk) (by omega)) (eval_const hw1) (by omega))
    have hkeep : ∀ r : ℕ, r ≠ 20 → r ≠ 22 → r ≠ 23 → r ≠ 25 →
        s₃.regs r = s.regs r := by
      intro r hr20 hr22 hr23 hr25
      simpa [s₃, hr22] using (hr₂ r hr20 hr23).trans (hr₁ r hr25)
    have ha₃ : s₃.arrs = s.arrs := ha₂.trans ha₁
    obtain ⟨s₄, t₄, he₄, ht₄, ho₄, ha₄, hr₄⟩ := ih
      (pre ++ encAlg86Subgraph A.1 A.2) (k + 1)
      (if v ∈ A.1 then k + 1 else owner)
      (by simp only [List.length_cons] at hN; omega)
      (by simpa only [List.flatMap_cons, List.append_assoc] using hw)
      (s := s₃) (by simpa only [ha₃, List.flatMap_cons, List.append_assoc] using hin)
      (by simpa [s₃] using hoff₂)
      ((hkeep 0 (by decide) (by decide) (by decide) (by decide)).trans hn)
      ((hkeep 21 (by decide) (by decide) (by decide) (by decide)).trans hcount)
      (by simp [s₃])
      ((hkeep 24 (by decide) (by decide) (by decide) (by decide)).trans hv)
      (by simpa [s₃] using (hr₂ 25 (by decide) (by decide)).trans ho₁)
    refine ⟨s₄, 3 + (t₁ + 17 + 4) + t₄,
      .while_true htest (by decide) (.seq (.seq he₁ he₂) he₃) he₄,
      by simp only [List.length_cons]; omega, ho₄, ha₄.trans ha₃, ?_⟩
    intro r h20 h22 h23 h25
    exact (hr₄ r h20 h22 h23 h25).trans (hkeep r h20 h22 h23 h25)

end GraphMinor.Compute
