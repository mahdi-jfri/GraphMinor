module

public import GraphMinor.Compute.GM06Alg511Loop
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Preserving the feasibility-loop words across a successor call

The successor procedure uses its own scalar workspace. VI (5.11)
retains the current and target numerators, their denominators and
the continuing flag between calls. Save these seven words in fresh
registers above every register written by the supplied command.
Restore them after the call. All arrays and the returned Boolean
are left as returned by that command. The wrapper adds a fixed
number of instructions, independently of the command's workspace.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Copy a fixed list of destination/source register pairs. -/
def gm06Alg511CopyRegisters : List (Reg × Reg) → Cmd
  | [] => .skip
  | p :: ps => .seq (.assign p.1 (.reg p.2)) (gm06Alg511CopyRegisters ps)

private theorem copy_registers_exec {w : ℕ} (pairs : List (Reg × Reg)) (s : State)
    (hnd : (pairs.map Prod.fst).Nodup)
    (hdis : ∀ p ∈ pairs, ∀ q ∈ pairs, p.1 ≠ q.2)
    (hwords : ∀ p ∈ pairs, s.regs p.2 < 2 ^ w) :
    ∃ t, Exec w (gm06Alg511CopyRegisters pairs) s t (2 * pairs.length + 1) ∧
      (∀ p ∈ pairs, t.regs p.1 = s.regs p.2) ∧ Keeps (pairs.map Prod.fst) [] s t := by
  induction pairs generalizing s with
  | nil => exact ⟨s, .skip s, by simp, Keeps.refl _ _ s⟩
  | cons p pairs ih =>
    have hnd' := List.nodup_cons.mp hnd
    let s₁ := s.setReg p.1 (s.regs p.2)
    have htail : ∀ q ∈ pairs, s₁.regs q.2 = s.regs q.2 := by
      intro q hq
      exact State.setReg_regs_ne s _ (hdis p (by simp) q (by simp [hq])).symm
    obtain ⟨t, he, hv, hkeep⟩ := ih s₁ hnd'.2
      (fun q hq r hr => hdis q (by simp [hq]) r (by simp [hr]))
      (fun q hq => (htail q hq).symm ▸ hwords q (by simp [hq]))
    have he₀ : Exec w (.assign p.1 (.reg p.2)) s s₁ 2 :=
      .assign (Crossing.eval_reg rfl (hwords p (by simp)))
    have hcost : 2 + (2 * pairs.length + 1) = 2 * (p :: pairs).length + 1 := by simp; omega
    refine ⟨t, hcost ▸ Exec.seq he₀ he, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with heq | hq
      · subst q
        have hnot : p.1 ∉ pairs.map Prod.fst := hnd'.1
        exact (hkeep.1 p.1 hnot).trans (State.setReg_regs_self _ _ _)
      · exact (hv q hq).trans (htail q hq)
    · have hfirst : Keeps ((p :: pairs).map Prod.fst) [] s s₁ :=
        (Keeps.refl _ _ s).setReg (by simp) _
      exact hfirst.trans hkeep (by
        intro r hr
        exact List.mem_cons_of_mem p.1 hr) (by simp)

/-- The saved registers lie above the callee's entire written
register set and above the loop's fixed register addresses. -/
def gm06Alg511CallRegisterBase (callee : Cmd) : Reg :=
  callee.writtenRegs.sup id + 6001

/-- Fresh destination registers for the seven retained loop words. -/
def gm06Alg511CallSavePairs (callee : Cmd) : List (Reg × Reg) :=
  let b := gm06Alg511CallRegisterBase callee
  [(b, 54), (b + 1, 55), (b + 2, 62), (b + 3, 63),
    (b + 4, 52), (b + 5, 66), (b + 6, 6000)]

/-- Save the loop words, run the supplied successor, and restore
the words without changing its returned paths or decision bit. -/
def gm06Alg511PreserveCallRegisters (callee : Cmd) : Cmd :=
  .seq (gm06Alg511CopyRegisters (gm06Alg511CallSavePairs callee))
    (.seq callee (gm06Alg511CopyRegisters ((gm06Alg511CallSavePairs callee).map Prod.swap)))

private theorem save_pair_bounds (callee : Cmd) (p : Reg × Reg)
    (hp : p ∈ gm06Alg511CallSavePairs callee) :
    gm06Alg511CallRegisterBase callee ≤ p.1 ∧ p.2 ≤ 6000 := by
  simp only [gm06Alg511CallSavePairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [Prod.fst, Prod.snd, Reg] <;> omega

private theorem base_large (callee : Cmd) : 6001 ≤ gm06Alg511CallRegisterBase callee := by
  unfold gm06Alg511CallRegisterBase
  dsimp only [Reg] at *
  omega

private theorem save_pair_fresh (callee : Cmd) (p : Reg × Reg)
    (hp : p ∈ gm06Alg511CallSavePairs callee) : p.1 ∉ callee.writtenRegs := by
  intro hm
  have hh := Finset.le_sup (f := id) hm
  have hb := (save_pair_bounds callee p hp).1
  dsimp only [id, gm06Alg511CallRegisterBase, Reg] at *
  omega

private theorem save_pairs_nodup (callee : Cmd) :
    ((gm06Alg511CallSavePairs callee).map Prod.fst).Nodup := by
  change (List.ofFn (fun i : Fin 7 => gm06Alg511CallRegisterBase callee + i.val)).Nodup
  apply List.nodup_ofFn_ofInjective
  intro i j h
  exact Fin.ext (Nat.add_left_cancel h)

private theorem restore_pairs_nodup (callee : Cmd) :
    (((gm06Alg511CallSavePairs callee).map Prod.swap).map Prod.fst).Nodup := by
  change ([54, 55, 62, 63, 52, 66, 6000] : List ℕ).Nodup
  decide

private theorem save_pairs_disjoint (callee : Cmd) :
    ∀ p ∈ gm06Alg511CallSavePairs callee, ∀ q ∈ gm06Alg511CallSavePairs callee, p.1 ≠ q.2 := by
  intro p hp q hq
  have hp' := save_pair_bounds callee p hp
  have hq' := save_pair_bounds callee q hq
  have hb := base_large callee
  dsimp only [Reg] at *
  omega

/-- The register wrapper preserves all seven scalar loop words and
leaves the callee's output bit and every array unchanged. The callee
execution is invoked from the actual saved state; it may overwrite
any of the original seven registers. The total overhead is 30 steps. -/
theorem gm06Alg511PreserveCallRegisters_exec {w B : ℕ} (callee : Cmd) (s : State)
    (hwords : ∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], s.regs j < 2 ^ w)
    (post : State → Prop)
    (hcall : ∀ s₁, s₁.arrs = s.arrs →
      (∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], s₁.regs j = s.regs j) →
      ∃ t u, Exec w callee s₁ t u ∧ u ≤ B ∧ post t) :
    ∃ t raw u, Exec w (gm06Alg511PreserveCallRegisters callee) s t u ∧
      u ≤ B + 30 ∧ post raw ∧ t.arrs = raw.arrs ∧ t.regs 0 = raw.regs 0 ∧
      ∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], t.regs j = s.regs j := by
  let pairs := gm06Alg511CallSavePairs callee
  have hswords : ∀ p ∈ pairs, s.regs p.2 < 2 ^ w := by
    intro p hp
    have hsrc : p.2 ∈ [54, 55, 62, 63, 52, 66, 6000] := by
      simp only [pairs, gm06Alg511CallSavePairs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    exact hwords p.2 hsrc
  obtain ⟨s₁, he₁, hsave, hk₁⟩ := copy_registers_exec pairs s
    (save_pairs_nodup callee) (save_pairs_disjoint callee) hswords
  have harr₁ : s₁.arrs = s.arrs := funext (fun a => hk₁.2 a (by simp))
  have hregs₁ : ∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], s₁.regs j = s.regs j := by
    intro j hj
    apply hk₁.1 j
    intro hj'
    obtain ⟨p, hp, hpj⟩ := List.mem_map.mp hj'
    have hb := save_pair_bounds callee p hp
    have hlarge := base_large callee
    have hjle : j ≤ 6000 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    dsimp only [Reg] at *
    omega
  obtain ⟨raw, uraw, heraw, huraw, hpost⟩ := hcall s₁ harr₁ hregs₁
  have hsaved : ∀ p ∈ pairs, raw.regs p.1 = s.regs p.2 := by
    intro p hp
    exact (heraw.regs_eq_of_not_mem_writtenRegs (save_pair_fresh callee p hp)).trans (hsave p hp)
  have hrwords : ∀ p ∈ pairs.map Prod.swap, raw.regs p.2 < 2 ^ w := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [show (q.swap).2 = q.1 from rfl, hsaved q hq]
    exact hswords q hq
  have hrdis : ∀ p ∈ pairs.map Prod.swap, ∀ q ∈ pairs.map Prod.swap, p.1 ≠ q.2 := by
    intro p hp q hq
    obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact (save_pairs_disjoint callee q' hq' p' hp').symm
  obtain ⟨t, he₂, hrestore, hk₂⟩ := copy_registers_exec (pairs.map Prod.swap) raw
    (restore_pairs_nodup callee) hrdis hrwords
  have hlen : pairs.length = 7 := rfl
  refine ⟨t, raw, (2 * pairs.length + 1) + (uraw + (2 * (pairs.map Prod.swap).length + 1)),
    .seq he₁ (.seq heraw he₂), by simp only [hlen, List.length_map]; omega, hpost,
    funext (fun a => hk₂.2 a (by simp)), ?_, ?_⟩
  · apply hk₂.1 0
    simp [pairs, gm06Alg511CallSavePairs]
  · intro j hj
    have hex : ∃ p ∈ pairs, p.2 = j := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [pairs, gm06Alg511CallSavePairs]
    obtain ⟨p, hp, hpj⟩ := hex
    have hh := hrestore p.swap (List.mem_map.mpr ⟨p, hp, rfl⟩)
    change t.regs p.2 = raw.regs p.1 at hh
    rw [hpj, hsaved p hp, hpj] at hh
    exact hh

end GraphMinor.Compute
