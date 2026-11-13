module

public import GraphMinor.Compute.F92Trace
public import GraphMinor.Compute.TwoPathsRename

/-!
# Moving the subwall search to scratch space

Exchange the first hundred addresses with a block above the caller's arrays and registers.
Renaming the search and trace by this exchange preserves the execution time and moves every
written address into that block. Thus no caller data needs to be saved or restored.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

open TwoPaths

/-- Exchange the first hundred addresses with a disjoint block starting at `base`. -/
def f92Swap (base x : ℕ) : ℕ :=
  if x < 100 then base + x
  else if base ≤ x ∧ x < base + 100 then x - base else x

theorem f92Swap_involutive {base : ℕ} (hb : 100 ≤ base) :
    Function.Involutive (f92Swap base) := by
  intro x
  unfold f92Swap
  split_ifs <;> omega

/-- The search and full parent trace, moved to the caller's scratch block. -/
def f92SearchHiProg (base : ℕ) : Cmd := renameCmd (f92Swap base) f92SearchTraceProg

/-- Renaming the canonical search preserves its cost and result and leaves every array
and register below `base` untouched. Inputs occupy offsets 40–42, 60 and 63, and the
path is written at offset 64. -/
theorem f92SearchHiProg_exec {w l m p h k r : ℕ}
    (x : Alg92Input l m p h k r) (a : Fin k) (lists : Fin x.n → List ℕ)
    (base : ℕ) (hb : 100 ≤ base)
    (src : List ℕ) (hsrc : ∀ v : Fin x.n, v.val ∈ src ↔ v ∈ (x.W_sub a).insideFinset)
    (hsrcLt : ∀ v ∈ src, v < x.n) (s : State)
    (hadj : IsAdjList x.G.toSimpleGraph (base + 40) (base + 41) (base + 42) lists s)
    (hent : (s.arrs (base + 42)).length < 2 ^ w) (hrn : s.regs (base + 40) = x.n)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hlen : src.length < 2 ^ w)
    (hlab : s.arrs (base + 60) = List.ofFn (f92SearchLabel x.W (x.W_sub a)))
    (hsrcArr : s.arrs (base + 63) = src) :
    ∃ s' t, ∃ P : List (Fin x.n), Exec w (f92SearchHiProg base) s s' t ∧
      t ≤ 35 + 45 * x.n + 29 * src.length + 29 * totalAdjEntries lists ∧
      IsSubwallHPath x.W (x.W_sub a) P ∧ s'.arrs (base + 64) = P.map Fin.val ∧
      (∀ q : ℕ, q < base + 60 ∨ base + 74 ≤ q → s'.regs q = s.regs q) ∧
      (∀ b : ℕ, b ≠ base + 60 → b ≠ base + 61 → b ≠ base + 62 →
        b ≠ base + 64 → s'.arrs b = s.arrs b) := by
  let s₀ := renameState (f92Swap base) s
  have hadj₀ : IsAdjList x.G.toSimpleGraph 40 41 42 lists s₀ :=
    hadj.of_arrs_eq rfl rfl rfl
  obtain ⟨s₁, t, P, hex, ht, hP, hout, hreg, harr⟩ :=
    f92SearchTraceProg_exec x a lists src hsrc hsrcLt s₀ hadj₀
      (by simpa [s₀, renameState, f92Swap] using hent)
      (by simpa [s₀, renameState, f92Swap] using hrn) hw hn hlen
      (by simpa [s₀, renameState, aLab, f92Swap] using hlab)
      (by simpa [s₀, renameState, aSrc, f92Swap] using hsrcArr)
  have hinv : renameState (f92Swap base) s₀ = s := by
    ext z <;> simp [s₀, renameState, f92Swap_involutive hb z]
  refine ⟨renameState (f92Swap base) s₁, t, P, ?_, ht, hP, ?_, ?_, ?_⟩
  · rw [← hinv]
    exact exec_renameCmd (f92Swap_involutive hb) hex
  · have hswap : f92Swap base (base + 64) = 64 := by simp [f92Swap]; omega
    simpa only [renameState_arrs, hswap] using hout
  · intro q hq
    change s₁.regs (f92Swap base q) = s.regs q
    have hframe : f92Swap base q < 60 ∨ 74 ≤ f92Swap base q := by
      unfold f92Swap
      split_ifs <;> omega
    rw [hreg _ hframe]
    exact congrArg s.regs (f92Swap_involutive hb q)
  · intro b hb60 hb61 hb62 hb64
    change s₁.arrs (f92Swap base b) = s.arrs b
    have hne : f92Swap base b ≠ 60 ∧ f92Swap base b ≠ 61 ∧
        f92Swap base b ≠ 62 ∧ f92Swap base b ≠ 64 := by
      unfold f92Swap
      split_ifs <;> omega
    rw [harr _ hne.1 hne.2.1 hne.2.2.1 hne.2.2.2]
    exact congrArg s.arrs (f92Swap_involutive hb b)

end GraphMinor.Compute.Alg92
