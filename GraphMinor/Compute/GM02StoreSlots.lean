module

public import GraphMinor.Compute.GM02DecodeSlots
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Storing decoded candidate slots in an array

The existing fixed-slot decoder writes the digits to consecutive
registers. Copy those registers into an allocated array with fixed
index writes. Induction on the written prefix proves the exact output
list, preserves every register and unrelated array, and gives linear
copying time in the fixed slot count.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Copy the first `k` decoded slot registers into the same positions of an allocated array. -/
@[expose] def gm02StoreSlotsProg (dst : Arr) : ℕ → Cmd
  | 0 => .skip
  | k + 1 => .seq (gm02StoreSlotsProg dst k) (.write dst (.const k) (.reg (200 + k)))

private def slotPrefix {N : ℕ} (f : Fin N → ℕ) (j : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin N => if i.val < j then f i else 0)

private theorem slotPrefix_zero {N : ℕ} (f : Fin N → ℕ) : slotPrefix f 0 = List.replicate N 0 := by
  simp [slotPrefix, List.ofFn_const]

private theorem slotPrefix_full {N : ℕ} (f : Fin N → ℕ) : slotPrefix f N = List.ofFn f := by
  unfold slotPrefix
  apply congrArg List.ofFn
  funext i
  exact ite_eq_left i.isLt

private theorem slotPrefix_set_next {N : ℕ} (f : Fin N → ℕ) (j : Fin N) :
    (slotPrefix f j.val).set j.val (f j) = slotPrefix f (j.val + 1) := by
  apply List.ext_getElem
  · simp [slotPrefix]
  · intro i hi hj
    by_cases hij : i = j.val
    · subst i
      simp only [slotPrefix, List.getElem_set_self, List.getElem_ofFn, Fin.eta,
        Nat.lt_succ_self, ite_true]
    · have hlt : i < j.val + 1 ↔ i < j.val := by omega
      simp only [slotPrefix, List.getElem_set, List.getElem_ofFn, Ne.symm hij, ite_false, hlt]

private theorem storeSlots_prefix_exec {w N : ℕ} (dst : Arr) (f : Fin N → ℕ) (s : State)
    (harr : s.arrs dst = List.replicate N 0)
    (hslots : ∀ i : Fin N, s.regs (200 + i.val) = f i)
    (hN : N < 2 ^ w) (hwords : ∀ i, f i < 2 ^ w)
    (j : ℕ) (hj : j ≤ N) :
    ∃ s' t, Exec w (gm02StoreSlotsProg dst j) s s' t ∧ t ≤ 1 + 3 * j ∧
      s'.arrs dst = slotPrefix f j ∧ s'.regs = s.regs ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) := by
  revert hj
  induction j with
  | zero =>
    intro _
    exact ⟨s, 1, .skip s, le_rfl, harr.trans (slotPrefix_zero f).symm, rfl, fun _ _ => rfl⟩
  | succ j ih =>
    intro hj
    have hjN : j < N := Nat.lt_of_succ_le hj
    obtain ⟨s₁, t₁, he₁, ht₁, harr₁, hr₁, ha₁⟩ := ih (Nat.le_of_succ_le hj)
    let i : Fin N := ⟨j, hjN⟩
    let s₂ := s₁.writeArr dst j (f i)
    have hreg : s₁.regs (200 + j) = f i := (congrFun hr₁ _).trans (hslots i)
    have he₂ : Exec w (.write dst (.const j) (.reg (200 + j))) s₁ s₂ 3 :=
      .write (eval_const (hjN.trans hN)) (eval_reg hreg (hwords i))
        (by simpa only [harr₁, slotPrefix, List.length_ofFn] using hjN)
    refine ⟨s₂, t₁ + 3, .seq he₁ he₂, by omega, ?_, hr₁, ?_⟩
    · rw [show s₂.arrs dst = (s₁.arrs dst).set j (f i) from State.writeArr_arrs_self .., harr₁]
      exact slotPrefix_set_next f i
    · intro a had
      exact (State.writeArr_arrs_ne s₁ j (f i) had).trans (ha₁ a had)

/-- The fixed register-to-array copy computes exactly the supplied slot list in at most `3k + 1` steps. -/
theorem gm02StoreSlotsProg_exec {w k : ℕ} (dst : Arr) (f : Fin k → ℕ) (s : State)
    (harr : s.arrs dst = List.replicate k 0)
    (hslots : ∀ i : Fin k, s.regs (200 + i.val) = f i)
    (hk : k < 2 ^ w) (hwords : ∀ i, f i < 2 ^ w) :
    ∃ s' t, Exec w (gm02StoreSlotsProg dst k) s s' t ∧ t ≤ 1 + 3 * k ∧
      s'.arrs dst = List.ofFn f ∧ s'.regs = s.regs ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) := by
  obtain ⟨s', t, he, ht, hout, hr, ha⟩ := storeSlots_prefix_exec dst f s harr hslots hk hwords k le_rfl
  exact ⟨s', t, he, ht, hout.trans (slotPrefix_full f), hr, ha⟩

end GraphMinor.Compute
