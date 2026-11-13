module

public import GraphMinor.Compute.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Total-correctness Hoare logic with step bounds

This file defines a quantitative Hoare triple `Triple w P c Q t` (written `⦃P⦄[w] c ⦃Q⦄ ≤ t`) for
the word RAM language of `GraphMinor.Compute.Basic`, stating that from every state `s` satisfying
`P s`, executing `c` at word size `w` terminates within `t s` steps in a state `s'` satisfying
`Q s'`.

## Main definitions and theorems

* `GraphMinor.Compute.Triple`: total-correctness triple `⦃P⦄[w] c ⦃Q⦄ ≤ t`.
* `GraphMinor.Compute.Triple.assign`, `Triple.write`, `Triple.alloc`, `Triple.seq`, `Triple.ite`:
  structural rules for primitive commands, sequencing, and conditionals.
* `GraphMinor.Compute.whileCost` and `GraphMinor.Compute.Triple.while`: loop rule parameterized by
  an invariant `I`, a decreasing measure `m : State → ℕ`, and a round-cost function
  `stepCost : ℕ → ℕ`, bounding total steps by the sum of the costs of the rounds.
* `GraphMinor.Compute.FrameFor` and `GraphMinor.Compute.Triple.frame`: frame rule for assertions
  that depend only on registers and arrays untouched by `c`.
* `GraphMinor.Compute.forUp` and `GraphMinor.Compute.Triple.forUp_const` / `Triple.forUp_sum`:
  derived counting-loop combinator and verification rules.
-/

@[expose] public section

namespace GraphMinor.Compute

open scoped BigOperators

/-- Total-correctness Hoare triple with time bound: from every state `s` satisfying `P s`,
executing command `c` with word size `w` terminates in some state `s'` satisfying `Q s'` within
`t s` steps. -/
def Triple (w : ℕ) (P : State → Prop) (c : Cmd) (Q : State → Prop) (t : State → ℕ) : Prop :=
  ∀ s, P s → ∃ s' k, Exec w c s s' k ∧ k ≤ t s ∧ Q s'

/-- Notation `⦃P⦄[w] c ⦃Q⦄ ≤ t` for `Triple w P c Q t`. -/
notation:50 "⦃" P "⦄" "[" w "] " c " ⦃" Q "⦄" " ≤ " t:50 => Triple w P c Q t

/-- Rule of consequence for `Triple`. -/
theorem Triple.conseq {w : ℕ} {P P' Q Q' : State → Prop} {c : Cmd} {t t' : State → ℕ}
    (h : ⦃P⦄[w] c ⦃Q⦄ ≤ t)
    (hP : ∀ s, P' s → P s)
    (hQ : ∀ s', Q s' → Q' s')
    (ht : ∀ s, P' s → t s ≤ t' s) :
    ⦃P'⦄[w] c ⦃Q'⦄ ≤ t' := by
  intro s hs'
  rcases h s (hP s hs') with ⟨s', k, hexec, hk, hQs'⟩
  exact ⟨s', k, hexec, hk.trans (ht s hs'), hQ s' hQs'⟩

theorem Triple.mono_cost {w : ℕ} {P Q : State → Prop} {c : Cmd} {t t' : State → ℕ}
    (h : ⦃P⦄[w] c ⦃Q⦄ ≤ t) (ht : ∀ s, P s → t s ≤ t' s) :
    ⦃P⦄[w] c ⦃Q⦄ ≤ t' :=
  h.conseq (fun _ h => h) (fun _ h => h) ht

theorem Triple.mono_post {w : ℕ} {P Q Q' : State → Prop} {c : Cmd} {t : State → ℕ}
    (h : ⦃P⦄[w] c ⦃Q⦄ ≤ t) (hQ : ∀ s', Q s' → Q' s') :
    ⦃P⦄[w] c ⦃Q'⦄ ≤ t :=
  h.conseq (fun _ h => h) hQ (fun _ _ => le_rfl)

theorem Triple.weaken_pre {w : ℕ} {P P' Q : State → Prop} {c : Cmd} {t : State → ℕ}
    (h : ⦃P⦄[w] c ⦃Q⦄ ≤ t) (hP : ∀ s, P' s → P s) :
    ⦃P'⦄[w] c ⦃Q⦄ ≤ t :=
  h.conseq hP (fun _ h => h) (fun _ _ => le_rfl)

/-- Rule for `Cmd.skip`. -/
theorem Triple.skip {w : ℕ} {P Q : State → Prop} {t : State → ℕ}
    (h : ∀ s, P s → Q s ∧ 1 ≤ t s) :
    ⦃P⦄[w] .skip ⦃Q⦄ ≤ t := by
  intro s hs
  rcases h s hs with ⟨hQ, ht⟩
  exact ⟨s, 1, .skip s, ht, hQ⟩

theorem Triple.skip_wp {w : ℕ} (Q : State → Prop) :
    ⦃Q⦄[w] .skip ⦃Q⦄ ≤ fun _ => 1 :=
  Triple.skip fun _ hQ => ⟨hQ, le_rfl⟩

/-- Rule for `Cmd.assign`. -/
theorem Triple.assign {w : ℕ} {P Q : State → Prop} {r : Reg} {e : Expr} {t : State → ℕ}
    (h : ∀ s, P s → ∃ v, e.eval w s = some v ∧ Q (s.setReg r v) ∧ e.cost + 1 ≤ t s) :
    ⦃P⦄[w] .assign r e ⦃Q⦄ ≤ t := by
  intro s hs
  rcases h s hs with ⟨v, he, hQ, ht⟩
  exact ⟨s.setReg r v, e.cost + 1, .assign he, ht, hQ⟩

/-- Weakest-precondition rule for `Cmd.assign`. -/
theorem Triple.assign_wp {w : ℕ} (r : Reg) (e : Expr) (Q : State → Prop) :
    ⦃fun s => ∃ v, e.eval w s = some v ∧ Q (s.setReg r v)⦄[w]
      .assign r e ⦃Q⦄ ≤ fun _ => e.cost + 1 :=
  Triple.assign fun _ ⟨v, he, hQ⟩ => ⟨v, he, hQ, le_rfl⟩

/-- Rule for `Cmd.write`. -/
theorem Triple.write {w : ℕ} {P Q : State → Prop} {a : Arr} {idx val : Expr} {t : State → ℕ}
    (h : ∀ s, P s → ∃ i v, idx.eval w s = some i ∧ val.eval w s = some v ∧
      i < (s.arrs a).length ∧ Q (s.writeArr a i v) ∧ idx.cost + val.cost + 1 ≤ t s) :
    ⦃P⦄[w] .write a idx val ⦃Q⦄ ≤ t := by
  intro s hs
  rcases h s hs with ⟨i, v, hi, hv, hlen, hQ, ht⟩
  exact ⟨s.writeArr a i v, idx.cost + val.cost + 1, .write hi hv hlen, ht, hQ⟩

/-- Weakest-precondition rule for `Cmd.write`. -/
theorem Triple.write_wp {w : ℕ} (a : Arr) (idx val : Expr) (Q : State → Prop) :
    ⦃fun s => ∃ i v, idx.eval w s = some i ∧ val.eval w s = some v ∧
      i < (s.arrs a).length ∧ Q (s.writeArr a i v)⦄[w]
      .write a idx val ⦃Q⦄ ≤ fun _ => idx.cost + val.cost + 1 :=
  Triple.write fun _ ⟨i, v, hi, hv, hlen, hQ⟩ => ⟨i, v, hi, hv, hlen, hQ, le_rfl⟩

/-- Rule for `Cmd.alloc`. -/
theorem Triple.alloc {w : ℕ} {P Q : State → Prop} {a : Arr} {len : Expr} {t : State → ℕ}
    (h : ∀ s, P s → ∃ m, len.eval w s = some m ∧
      Q (s.setArr a (List.replicate m 0)) ∧ len.cost + m ≤ t s) :
    ⦃P⦄[w] .alloc a len ⦃Q⦄ ≤ t := by
  intro s hs
  rcases h s hs with ⟨m, hm, hQ, ht⟩
  exact ⟨s.setArr a (List.replicate m 0), len.cost + m, .alloc hm, ht, hQ⟩

/-- Rule for `Cmd.seq`. -/
theorem Triple.seq {w : ℕ} {P R Q : State → Prop} {c₁ c₂ : Cmd} {t₁ t₂ t : State → ℕ}
    (h₁ : ⦃P⦄[w] c₁ ⦃R⦄ ≤ t₁)
    (h₂ : ⦃R⦄[w] c₂ ⦃Q⦄ ≤ t₂)
    (ht : ∀ s s₁, P s → R s₁ → t₁ s + t₂ s₁ ≤ t s) :
    ⦃P⦄[w] .seq c₁ c₂ ⦃Q⦄ ≤ t := by
  intro s hs
  rcases h₁ s hs with ⟨s₁, k₁, hex₁, hk₁, hR⟩
  rcases h₂ s₁ hR with ⟨s₂, k₂, hex₂, hk₂, hQ⟩
  exact ⟨s₂, k₁ + k₂, .seq hex₁ hex₂, (Nat.add_le_add hk₁ hk₂).trans (ht s s₁ hs hR), hQ⟩

/-- Rule for `Cmd.seq` when the second command has a state-independent cost bound `T₂`. -/
theorem Triple.seq_const {w : ℕ} {P R Q : State → Prop} {c₁ c₂ : Cmd} {t₁ : State → ℕ} {T₂ : ℕ}
    (h₁ : ⦃P⦄[w] c₁ ⦃R⦄ ≤ t₁)
    (h₂ : ⦃R⦄[w] c₂ ⦃Q⦄ ≤ fun _ => T₂) :
    ⦃P⦄[w] .seq c₁ c₂ ⦃Q⦄ ≤ fun s => t₁ s + T₂ :=
  h₁.seq h₂ fun _ _ _ _ => le_rfl

/-- Rule for `Cmd.seq` when both commands have constant cost bounds `T₁` and `T₂`. -/
theorem Triple.seq_const₂ {w : ℕ} {P R Q : State → Prop} {c₁ c₂ : Cmd} {T₁ T₂ : ℕ}
    (h₁ : ⦃P⦄[w] c₁ ⦃R⦄ ≤ fun _ => T₁)
    (h₂ : ⦃R⦄[w] c₂ ⦃Q⦄ ≤ fun _ => T₂) :
    ⦃P⦄[w] .seq c₁ c₂ ⦃Q⦄ ≤ fun _ => T₁ + T₂ :=
  h₁.seq h₂ fun _ _ _ _ => le_rfl

/-- Rule for `Cmd.ite` (`if`). -/
theorem Triple.ite {w : ℕ} {P Q : State → Prop} {cond : Expr} {c₁ c₂ : Cmd}
    {t₁ t₂ t : State → ℕ}
    (hcond : ∀ s, P s → ∃ v, cond.eval w s = some v)
    (h₁ : ⦃fun s => P s ∧ ∃ v, cond.eval w s = some v ∧ v ≠ 0⦄[w] c₁ ⦃Q⦄ ≤ t₁)
    (h₂ : ⦃fun s => P s ∧ cond.eval w s = some 0⦄[w] c₂ ⦃Q⦄ ≤ t₂)
    (ht₁ : ∀ s, P s → (∃ v, cond.eval w s = some v ∧ v ≠ 0) → cond.cost + t₁ s ≤ t s)
    (ht₂ : ∀ s, P s → cond.eval w s = some 0 → cond.cost + t₂ s ≤ t s) :
    ⦃P⦄[w] .ite cond c₁ c₂ ⦃Q⦄ ≤ t := by
  intro s hs
  rcases hcond s hs with ⟨v, hv⟩
  by_cases hv0 : v = 0
  · subst hv0
    rcases h₂ s ⟨hs, hv⟩ with ⟨s', k, hex, hk, hQ⟩
    refine ⟨s', cond.cost + k, .ite_false hv hex, ?_, hQ⟩
    exact (Nat.add_le_add_left hk _).trans (ht₂ s hs hv)
  · rcases h₁ s ⟨hs, v, hv, hv0⟩ with ⟨s', k, hex, hk, hQ⟩
    refine ⟨s', cond.cost + k, .ite_true hv hv0 hex, ?_, hQ⟩
    exact (Nat.add_le_add_left hk _).trans (ht₁ s hs ⟨v, hv, hv0⟩)

/-- Rule for `Cmd.ite` with a common cost bound `tb` on both branches. -/
theorem Triple.ite_const {w : ℕ} {P Q : State → Prop} {cond : Expr} {c₁ c₂ : Cmd} {tb : ℕ}
    (hcond : ∀ s, P s → ∃ v, cond.eval w s = some v)
    (h₁ : ⦃fun s => P s ∧ ∃ v, cond.eval w s = some v ∧ v ≠ 0⦄[w] c₁ ⦃Q⦄ ≤ fun _ => tb)
    (h₂ : ⦃fun s => P s ∧ cond.eval w s = some 0⦄[w] c₂ ⦃Q⦄ ≤ fun _ => tb) :
    ⦃P⦄[w] .ite cond c₁ c₂ ⦃Q⦄ ≤ fun _ => cond.cost + tb :=
  Triple.ite hcond h₁ h₂ (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl)

/-- Total cost of a `while` loop with condition cost `condCost`, round cost `stepCost` (indexed by
the value `k ≥ 1` of the decreasing measure at the start of the round), and initial measure `n`. -/
def whileCost (condCost : ℕ) (stepCost : ℕ → ℕ) (n : ℕ) : ℕ :=
  condCost + ∑ i ∈ Finset.range n, (condCost + stepCost (i + 1))

@[simp]
theorem whileCost_zero (condCost : ℕ) (stepCost : ℕ → ℕ) :
    whileCost condCost stepCost 0 = condCost := by
  simp [whileCost]

theorem whileCost_succ (condCost : ℕ) (stepCost : ℕ → ℕ) (n : ℕ) :
    whileCost condCost stepCost (n + 1) =
      whileCost condCost stepCost n + (condCost + stepCost (n + 1)) := by
  simp only [whileCost, Finset.sum_range_succ]
  omega

theorem whileCost_mono (condCost : ℕ) (stepCost : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) :
    whileCost condCost stepCost m ≤ whileCost condCost stepCost n := by
  unfold whileCost
  apply Nat.add_le_add_left
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

theorem whileCost_const (condCost B n : ℕ) :
    whileCost condCost (fun _ => B) n = condCost + n * (condCost + B) := by
  simp [whileCost, Finset.sum_const, Finset.card_range]

/-- Rule for `Cmd.while` using an invariant `I`, a decreasing measure `m : State → ℕ`, and a
round-cost function `stepCost : ℕ → ℕ`. -/
theorem Triple.while {w : ℕ} (I : State → Prop) (m : State → ℕ) (stepCost : ℕ → ℕ)
    {cond : Expr} {body : Cmd}
    (hcond : ∀ s, I s → ∃ v, cond.eval w s = some v ∧ (v ≠ 0 → 0 < m s))
    (hbody : ∀ k > 0,
      ⦃fun s => I s ∧ m s = k ∧ ∃ v, cond.eval w s = some v ∧ v ≠ 0⦄[w]
        body
      ⦃fun s' => I s' ∧ m s' < k⦄ ≤ fun _ => stepCost k) :
    ⦃I⦄[w] .while cond body ⦃fun s' => I s' ∧ cond.eval w s' = some 0⦄ ≤
      fun s => whileCost cond.cost stepCost (m s) := by
  intro s hs
  generalize hk : m s = k
  induction k using Nat.strong_induction_on generalizing s with
  | _ k ih =>
    rcases hcond s hs with ⟨v, hv, hpos⟩
    by_cases hv0 : v = 0
    · subst hv0
      refine ⟨s, cond.cost, .while_false hv, ?_, hs, hv⟩
      dsimp only
      rw [hk]
      have : whileCost cond.cost stepCost 0 ≤ whileCost cond.cost stepCost k :=
        whileCost_mono cond.cost stepCost (Nat.zero_le k)
      simpa using this
    · have hkpos : 0 < k := hk ▸ hpos hv0
      rcases hbody k hkpos s ⟨hs, hk, v, hv, hv0⟩ with ⟨s₁, t₁, hex₁, ht₁, hI₁, hm₁⟩
      rcases ih (m s₁) hm₁ s₁ hI₁ rfl with ⟨s₂, t₂, hex₂, ht₂, hI₂, hcond₂⟩
      refine ⟨s₂, cond.cost + t₁ + t₂, .while_true hv hv0 hex₁ hex₂, ?_, hI₂, hcond₂⟩
      dsimp only at ht₁ ht₂ ⊢
      rw [hk]
      have hle : m s₁ ≤ k - 1 := by omega
      have hmono := whileCost_mono cond.cost stepCost hle
      have hsucc := whileCost_succ cond.cost stepCost (k - 1)
      rw [Nat.sub_add_cancel hkpos] at hsucc
      omega

/-- Rule for `Cmd.while` when every round of `body` has constant cost bound `B`. -/
theorem Triple.while_const {w : ℕ} (I : State → Prop) (m : State → ℕ) (B : ℕ)
    {cond : Expr} {body : Cmd}
    (hcond : ∀ s, I s → ∃ v, cond.eval w s = some v ∧ (v ≠ 0 → 0 < m s))
    (hbody : ⦃fun s => I s ∧ ∃ v, cond.eval w s = some v ∧ v ≠ 0⦄[w]
        body
      ⦃fun s' => I s'⦄ ≤ fun _ => B)
    (hdec : ∀ s, I s → (∃ v, cond.eval w s = some v ∧ v ≠ 0) →
      ∀ s' k, Exec w body s s' k → m s' < m s) :
    ⦃I⦄[w] .while cond body ⦃fun s' => I s' ∧ cond.eval w s' = some 0⦄ ≤
      fun s => cond.cost + m s * (cond.cost + B) := by
  have h := Triple.while I m (fun _ => B) hcond fun k _ s ⟨hI, hms, htrue⟩ => by
    rcases hbody s ⟨hI, htrue⟩ with ⟨s', t, hex, ht, hI'⟩
    exact ⟨s', t, hex, ht, hI', hms ▸ hdec s hI htrue s' t hex⟩
  refine h.mono_cost fun s _ => ?_
  rw [whileCost_const]

/-- An assertion `F : State → Prop` is a valid frame for command `c` if it is preserved whenever
all registers outside `c.writtenRegs` and all arrays outside `c.writtenArrs` are preserved. -/
def FrameFor (c : Cmd) (F : State → Prop) : Prop :=
  ∀ s s', (∀ r ∉ c.writtenRegs, s'.regs r = s.regs r) →
    (∀ a ∉ c.writtenArrs, s'.arrs a = s.arrs a) →
    F s → F s'

/-- The frame rule: any assertion `F` untouched by `c` (`FrameFor c F`) is preserved across `c`
with no additional step cost. -/
theorem Triple.frame {w : ℕ} {P Q F : State → Prop} {c : Cmd} {t : State → ℕ}
    (h : ⦃P⦄[w] c ⦃Q⦄ ≤ t) (hF : FrameFor c F) :
    ⦃fun s => P s ∧ F s⦄[w] c ⦃fun s' => Q s' ∧ F s'⦄ ≤ t := by
  intro s ⟨hP, hFs⟩
  rcases h s hP with ⟨s', k, hex, hk, hQ⟩
  refine ⟨s', k, hex, hk, hQ, ?_⟩
  exact hF s s' (fun r hr => hex.regs_eq_of_not_mem_writtenRegs hr)
    (fun a ha => hex.arrs_eq_of_not_mem_writtenArrs ha) hFs

theorem FrameFor.reg_eq {c : Cmd} {r : Reg} (hr : r ∉ c.writtenRegs) (v : ℕ) :
    FrameFor c (fun s => s.regs r = v) := by
  intro s s' hregs _ hs
  rw [hregs r hr, hs]

theorem FrameFor.arr_eq {c : Cmd} {a : Arr} (ha : a ∉ c.writtenArrs) (l : List ℕ) :
    FrameFor c (fun s => s.arrs a = l) := by
  intro s s' _ harrs hs
  rw [harrs a ha, hs]

theorem FrameFor.and {c : Cmd} {F₁ F₂ : State → Prop}
    (h₁ : FrameFor c F₁) (h₂ : FrameFor c F₂) :
    FrameFor c (fun s => F₁ s ∧ F₂ s) := by
  intro s s' hr ha ⟨hf₁, hf₂⟩
  exact ⟨h₁ s s' hr ha hf₁, h₂ s s' hr ha hf₂⟩

theorem FrameFor.forall {α : Type*} {c : Cmd} {F : α → State → Prop}
    (h : ∀ x, FrameFor c (F x)) :
    FrameFor c (fun s => ∀ x, F x s) := by
  intro s s' hr ha hf x
  exact h x s s' hr ha (hf x)

theorem FrameFor.below {c : Cmd} (base : Reg) (aBase : Arr)
    (hr : ∀ r ∈ c.writtenRegs, base ≤ r)
    (ha : ∀ a ∈ c.writtenArrs, aBase ≤ a)
    {F : State → Prop}
    (hdep : ∀ s s', (∀ r < base, s'.regs r = s.regs r) →
      (∀ a < aBase, s'.arrs a = s.arrs a) → F s → F s') :
    FrameFor c F := by
  intro s s' hregs harrs hFs
  apply hdep s s'
  · intro r hlt
    exact hregs r fun hmem => Nat.not_le.mpr hlt (hr r hmem)
  · intro a hlt
    exact harrs a fun hmem => Nat.not_le.mpr hlt (ha a hmem)
  · exact hFs

/-- Counting loop macro: while `s.regs r_i < hi`, execute `body` and increment `r_i` by `1`. -/
def forUp (r_i : Reg) (hi : Expr) (body : Cmd) : Cmd :=
  .while (.op .lt (.reg r_i) hi) (.seq body (.assign r_i (.op .add (.reg r_i) (.const 1))))

/-- Verification rule for `forUp r_i hi body` with indexed invariant `I : ℕ → State → Prop` and
per-iteration cost `stepCost : ℕ → ℕ` (where `stepCost i` is the cost of `body` at index `i`). -/
theorem Triple.forUp_sum_from {w : ℕ} (I : ℕ → State → Prop) (N : ℕ) (stepCost : ℕ → ℕ)
    {r_i : Reg} {hi : Expr} {body : Cmd}
    (hw : 1 < 2 ^ w)
    (hN : N < 2 ^ w)
    (hhi : ∀ i ≤ N, ∀ s, I i s → s.regs r_i = i ∧ hi.eval w s = some N)
    (hbody : ∀ i < N,
      ⦃I i⦄[w] body ⦃fun s' => I (i + 1) (s'.setReg r_i (i + 1)) ∧ s'.regs r_i = i⦄ ≤
        fun _ => stepCost i) :
    ∀ i₀ ≤ N,
      ⦃I i₀⦄[w] forUp r_i hi body ⦃I N⦄ ≤
        fun _ => (hi.cost + 2) + ∑ j ∈ Finset.range (N - i₀), (hi.cost + 6 + stepCost (i₀ + j)) := by
  intro i₀ hi₀
  induction hdiff : N - i₀ generalizing i₀ with
  | zero =>
    have hi₀_eq : i₀ = N := by omega
    subst hi₀_eq
    intro s hs
    obtain ⟨hreg, hhi_eval⟩ := hhi i₀ le_rfl s hs
    have hcond : (Expr.op .lt (.reg r_i) hi).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hreg, hhi_eval, hN,
        show (0 : ℕ) < 2 ^ w by omega]
    refine ⟨s, (Expr.op .lt (.reg r_i) hi).cost, .while_false hcond, ?_, hs⟩
    simp [Expr.cost]; omega
  | succ d ih =>
    have hi₀_lt : i₀ < N := by omega
    intro s hs
    obtain ⟨hreg, hhi_eval⟩ := hhi i₀ hi₀ s hs
    have h_i₀_lt_w : i₀ < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_i) hi).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hreg, hhi_eval, h_i₀_lt_w, hi₀_lt, hw]
    rcases hbody i₀ hi₀_lt s hs with ⟨s₁, t₁, hex₁, ht₁, hI₁, hreg₁⟩
    have hinc_eval : (Expr.op .add (.reg r_i) (.const 1)).eval w s₁ = some (i₀ + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hreg₁, h_i₀_lt_w, hw,
        show i₀ + 1 < 2 ^ w by omega]
    have hex_step : Exec w (.seq body (.assign r_i (.op .add (.reg r_i) (.const 1))))
        s (s₁.setReg r_i (i₀ + 1)) (t₁ + 4) :=
      .seq hex₁ (.assign hinc_eval)
    rcases ih (i₀ + 1) (by omega) (by omega) (s₁.setReg r_i (i₀ + 1)) hI₁ with
      ⟨s₂, t₂, hex₂, ht₂, hI_N⟩
    refine ⟨s₂, (Expr.op .lt (.reg r_i) hi).cost + (t₁ + 4) + t₂,
      .while_true hcond (by omega) hex_step hex₂, ?_, hI_N⟩
    dsimp only at ht₁ ht₂ ⊢
    rw [Finset.sum_range_succ']
    have hshift : ∑ k ∈ Finset.range d, (hi.cost + 6 + stepCost (i₀ + (k + 1))) =
        ∑ k ∈ Finset.range d, (hi.cost + 6 + stepCost (i₀ + 1 + k)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Nat.add_assoc, Nat.add_right_comm i₀ k 1]
    rw [hshift, Nat.add_zero i₀]
    simp only [Expr.cost]
    omega

/-- Verification rule for `forUp r_i hi body` starting at `0` with per-iteration cost `stepCost i`. -/
theorem Triple.forUp_sum {w : ℕ} (I : ℕ → State → Prop) (N : ℕ) (stepCost : ℕ → ℕ)
    {r_i : Reg} {hi : Expr} {body : Cmd}
    (hw : 1 < 2 ^ w)
    (hN : N < 2 ^ w)
    (hhi : ∀ i ≤ N, ∀ s, I i s → s.regs r_i = i ∧ hi.eval w s = some N)
    (hbody : ∀ i < N,
      ⦃I i⦄[w] body ⦃fun s' => I (i + 1) (s'.setReg r_i (i + 1)) ∧ s'.regs r_i = i⦄ ≤
        fun _ => stepCost i) :
    ⦃I 0⦄[w] forUp r_i hi body ⦃I N⦄ ≤
      fun _ => (hi.cost + 2) + ∑ j ∈ Finset.range N, (hi.cost + 6 + stepCost j) := by
  have h := Triple.forUp_sum_from I N stepCost hw hN hhi hbody 0 (Nat.zero_le N)
  refine h.mono_cost fun _ _ => ?_
  simp

/-- Verification rule for `forUp r_i hi body` starting at `0` with constant body cost `B`. -/
theorem Triple.forUp_const {w : ℕ} (I : ℕ → State → Prop) (N B : ℕ)
    {r_i : Reg} {hi : Expr} {body : Cmd}
    (hw : 1 < 2 ^ w)
    (hN : N < 2 ^ w)
    (hhi : ∀ i ≤ N, ∀ s, I i s → s.regs r_i = i ∧ hi.eval w s = some N)
    (hbody : ∀ i < N,
      ⦃I i⦄[w] body ⦃fun s' => I (i + 1) (s'.setReg r_i (i + 1)) ∧ s'.regs r_i = i⦄ ≤
        fun _ => B) :
    ⦃I 0⦄[w] forUp r_i hi body ⦃I N⦄ ≤
      fun _ => (hi.cost + 2) + N * (hi.cost + 6 + B) := by
  have h := Triple.forUp_sum I N (fun _ => B) hw hN hhi hbody
  refine h.mono_cost fun _ _ => ?_
  simp [Finset.sum_const]

/-- Simp lemmas for expression evaluation and written-set queries. -/
@[simp] theorem Expr.eval_const (w n : ℕ) (s : State) :
    (Expr.const n).eval w s = checkWord w n := rfl

@[simp] theorem Expr.eval_reg (w : ℕ) (r : Reg) (s : State) :
    (Expr.reg r).eval w s = checkWord w (s.regs r) := rfl

@[simp] theorem Expr.eval_len (w : ℕ) (a : Arr) (s : State) :
    (Expr.len a).eval w s = checkWord w (s.arrs a).length := rfl

@[simp] theorem Cmd.writtenRegs_skip : Cmd.skip.writtenRegs = ∅ := rfl
@[simp] theorem Cmd.writtenRegs_assign (r : Reg) (e : Expr) :
    (Cmd.assign r e).writtenRegs = {r} := rfl
@[simp] theorem Cmd.writtenRegs_write (a : Arr) (idx val : Expr) :
    (Cmd.write a idx val).writtenRegs = ∅ := rfl
@[simp] theorem Cmd.writtenRegs_alloc (a : Arr) (len : Expr) :
    (Cmd.alloc a len).writtenRegs = ∅ := rfl
@[simp] theorem Cmd.writtenRegs_seq (c₁ c₂ : Cmd) :
    (Cmd.seq c₁ c₂).writtenRegs = c₁.writtenRegs ∪ c₂.writtenRegs := rfl
@[simp] theorem Cmd.writtenRegs_ite (cond : Expr) (c₁ c₂ : Cmd) :
    (Cmd.ite cond c₁ c₂).writtenRegs = c₁.writtenRegs ∪ c₂.writtenRegs := rfl
@[simp] theorem Cmd.writtenRegs_while (cond : Expr) (body : Cmd) :
    (Cmd.while cond body).writtenRegs = body.writtenRegs := rfl

@[simp] theorem Cmd.writtenArrs_skip : Cmd.skip.writtenArrs = ∅ := rfl
@[simp] theorem Cmd.writtenArrs_assign (r : Reg) (e : Expr) :
    (Cmd.assign r e).writtenArrs = ∅ := rfl
@[simp] theorem Cmd.writtenArrs_write (a : Arr) (idx val : Expr) :
    (Cmd.write a idx val).writtenArrs = {a} := rfl
@[simp] theorem Cmd.writtenArrs_alloc (a : Arr) (len : Expr) :
    (Cmd.alloc a len).writtenArrs = {a} := rfl
@[simp] theorem Cmd.writtenArrs_seq (c₁ c₂ : Cmd) :
    (Cmd.seq c₁ c₂).writtenArrs = c₁.writtenArrs ∪ c₂.writtenArrs := rfl
@[simp] theorem Cmd.writtenArrs_ite (cond : Expr) (c₁ c₂ : Cmd) :
    (Cmd.ite cond c₁ c₂).writtenArrs = c₁.writtenArrs ∪ c₂.writtenArrs := rfl
@[simp] theorem Cmd.writtenArrs_while (cond : Expr) (body : Cmd) :
    (Cmd.while cond body).writtenArrs = body.writtenArrs := rfl

/-- Evaluate a `Triple` for a single primitive command (`assign`, `write`, `alloc`, `skip`). -/
macro "vcg_prim" : tactic =>
  `(tactic|
    first
    | apply Triple.assign; intro s hs
    | apply Triple.write; intro s hs
    | apply Triple.alloc; intro s hs
    | apply Triple.skip; intro s hs)

end GraphMinor.Compute
