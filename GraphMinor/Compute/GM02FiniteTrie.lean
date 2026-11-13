module

public import GraphMinor.Compute.Basic
import GraphMinor.Compute.Algorithm101Defs

/-!
# Finite exhaustion for the bounded cases of II (3.2)

A finite prefix tree reads words until a complete input is reached. Its
leaves contain fixed answers. The execution proof bounds time and shows
that only the output and scratch registers change. The tree has fixed
depth and branching bounds for each fixed width parameter.
-/

public section
namespace GraphMinor.Compute
open Classical

/-- A bounded prefix tree for the exhaustive base cases on page 316. -/
noncomputable def gm02FiniteTrieProg (arr : Arr) (r_out r_tmp : Reg) (maxWord : ℕ) (stop : List ℕ → Prop) (f : List ℕ → ℕ) :
    ℕ → List ℕ → Cmd
  | 0, pref => .assign r_out (.const (f pref))
  | rem + 1, pref =>
    if stop pref then
      .assign r_out (.const (f pref))
    else
      .seq (.assign r_tmp (.read arr (.const pref.length)))
        (branchValProg r_tmp
          (fun v => gm02FiniteTrieProg arr r_out r_tmp maxWord stop f rem (pref ++ [v]))
          maxWord)

/-- Execution of the finite prefix tree on a self-delimiting word list. -/
theorem gm02FiniteTrieProg_exec {w : ℕ} (arr : Arr) (r_out r_tmp : Reg) (maxWord : ℕ)
    (stop : List ℕ → Prop) (f : List ℕ → ℕ) (hf_lt : ∀ pref, f pref < 2 ^ w)
    (words rest : List ℕ)
    (hstop : ∀ m ≤ words.length, stop (words.take m) ↔ m = words.length)
    (hwords : ∀ x ∈ words, x ≤ maxWord)
    (hw_max : maxWord + 1 < 2 ^ w)
    (hlen_w : (words).length < 2 ^ w) :
    ∀ (rem : ℕ) (m : ℕ),
      m ≤ (words).length →
      (words).length - m ≤ rem →
      rem < 2 ^ w →
      ∀ (s : State),
        s.arrs arr = words ++ rest →
        ∃ (s' : State) (t : ℕ),
          Exec w (gm02FiniteTrieProg arr r_out r_tmp maxWord stop f rem ((words).take m))
            s s' t ∧
          t ≤ (rem + 1) * (4 * maxWord + 10) ∧
          s'.regs r_out = f (words) ∧
          (∀ r, r ≠ r_out → r ≠ r_tmp → s'.regs r = s.regs r) ∧
          s'.arrs = s.arrs
  | 0, m, hm_le, hrem, _, s, harr => by
    have hm_eq : m = (words).length := by omega
    subst hm_eq
    rw [List.take_length]
    refine ⟨s.setReg r_out (f (words)), 2, ?_,
      by rw [Nat.one_mul]; omega, by simp, fun r hr₁ _ => by simp [hr₁], rfl⟩
    exact .assign (checkWord_of_lt (hf_lt _))
  | rem + 1, m, hm_le, hrem, hrem_w, s, harr => by
    unfold gm02FiniteTrieProg
    by_cases hm_eq : m = (words).length
    · subst hm_eq
      have hs : stop words := by
        simpa only [List.take_length] using (hstop words.length (Nat.le_refl _)).2 rfl
      simp only [List.take_length, ite_eq_left hs]
      refine ⟨s.setReg r_out (f (words)), 2, ?_,
        by rw [Nat.succ_mul]; omega, by simp, fun r hr₁ _ => by simp [hr₁], rfl⟩
      exact .assign (checkWord_of_lt (hf_lt _))
    · have hm_lt : m < (words).length := by omega
      have hm_w : m < 2 ^ w := by omega
      have hs : ¬stop (words.take m) := fun hs => hm_eq ((hstop m hm_le).1 hs)
      simp only [ite_eq_right hs]
      let v := (words)[m]'hm_lt
      have hv_mem : v ∈ words := List.getElem_mem hm_lt
      have hv_le : v ≤ maxWord := hwords v hv_mem
      have hv_w : v < 2 ^ w := by omega
      have hlen_take : ((words).take m).length = m := List.length_take_of_le hm_le
      have hidx_arr : m < (s.arrs arr).length := by
        rw [harr, List.length_append]
        omega
      have hget_arr : (s.arrs arr)[m]'hidx_arr = v := by
        simp [harr, List.getElem_append_left hm_lt, v]
      have hex_read :
          Exec w (.assign r_tmp (.read arr (.const ((words).take m).length)))
            s (s.setReg r_tmp v) 3 := by
        rw [hlen_take]
        refine .assign ?_
        simp [Expr.eval, checkWord_of_lt hm_w, hidx_arr, hget_arr, checkWord_of_lt hv_w]
      have htake_succ : (words).take m ++ [v] = (words).take (m + 1) := by
        simp [v]
      let s₁ := s.setReg r_tmp v
      have hs₁_arr : s₁.arrs arr = words ++ rest := harr
      rcases gm02FiniteTrieProg_exec arr r_out r_tmp maxWord stop f hf_lt words rest hstop hwords hw_max hlen_w
          rem (m + 1) (by omega) (by omega) (by omega) s₁ hs₁_arr with
        ⟨s', t_rec, hex_rec, ht_rec, hrout, hregs, harrs⟩
      rw [← htake_succ] at hex_rec
      have hs₁_r_tmp : s₁.regs r_tmp = v := by simp [s₁]
      rcases branchValProg_exec r_tmp
          (fun val => gm02FiniteTrieProg arr r_out r_tmp maxWord stop f rem
            ((words).take m ++ [val]))
          maxWord (s := s₁) (by rw [hs₁_r_tmp]; exact hv_le) hw_max
          (by rw [hs₁_r_tmp]; exact hex_rec) with
        ⟨t_br, hex_br, ht_br⟩
      refine ⟨s', 3 + t_br, .seq hex_read hex_br, ?_, hrout, ?_, harrs⟩
      · rw [Nat.succ_mul (rem + 1)]
        omega
      · intro r hr₁ hr₂
        rw [hregs r hr₁ hr₂]
        simp [s₁, hr₂]


end GraphMinor.Compute
