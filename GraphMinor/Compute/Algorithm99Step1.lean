module

public import GraphMinor.Compute.Specs9
import GraphMinor.Compute.Algorithm77Prog75Full

/-!
# Step (1) of Algorithm (9.9): one call of (7.2)

Step (1) of the proof of (9.8) in Graph Minors XIII (page 104) reads: "(1) We apply (7.2) to
$G$. (This is possible by (7.1).) If we obtain a branch-decomposition of $G$ of width
$\le \omega$ we stop. Otherwise we obtain a wall $H$ in $G$ of height $h'$."

The program `alg99Step1Prog P72 B R` saves the input `G.enc` in array `B` (the call of `P72`
may overwrite the input array), runs `P72`, and reads the tag of its output into register `R`.
The caller puts all its own arrays at `B` or above and all its own registers at `R` or above,
with `B` and `R` above the arrays and registers that `P72` writes. Then the call changes none of
them. The execution theorem is `alg99Step1Prog_exec`.

The two lemmas `isAlg99Output_of_alg72_tag_zero` and `exists_wall_of_alg72_tag_ne_zero` say what
the tag means: tag `0` means the output of `P72` is already an output (i) of (9.9), and any other
tag gives a valid wall of height `h'` in `G`, with the output equal to `1 :: W.encList`.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- `omega` after unfolding `Reg` and `Arr`, which `omega` does not see as `ℕ`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr, inArr, outArr] at *); omega))

/-- What `ComputesArrRelInTime.subroutine_exec` says about a program `P` with constants `C, c`:
from any state with the input `encIn x` in `inArr`, at any word size `w ≥ wordSize c (size x)`,
`P` writes an output satisfying `Spec x` in time `≤ C * T (size x)`, and keeps the registers at
`folioCallerRegBase P` and above and the arrays at `folioCallerArrBase P` and above. -/
def RunsAsSubroutine {X : Type*} (size : X → ℕ) (encIn : X → List ℕ) (Spec : X → List ℕ → Prop)
    (P : Cmd) (T : ℕ → ℕ) (C c : ℕ) : Prop :=
  ∀ (x : X) (w : ℕ), wordSize c (size x) ≤ w →
    ∀ (s : State), s.arrs inArr = encIn x →
      ∃ (s' : State) (t : ℕ),
        Exec w P s s' t ∧
        t ≤ C * T (size x) ∧
        Spec x (s'.arrs outArr) ∧
        (∀ r : Reg, folioCallerRegBase P ≤ r → s'.regs r = s.regs r) ∧
        (∀ a : Arr, folioCallerArrBase P ≤ a → s'.arrs a = s.arrs a)

/-- `ComputesArrRelInTime.subroutine_exec` in the form `RunsAsSubroutine`. -/
theorem ComputesArrRelInTime.runsAsSubroutine {X : Type*} {size : X → ℕ} {encIn : X → List ℕ}
    {Spec : X → List ℕ → Prop} {P : Cmd} {T : ℕ → ℕ}
    (hP : ComputesArrRelInTime size encIn Spec P T) :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ RunsAsSubroutine size encIn Spec P T C c :=
  hP.subroutine_exec

/-- Step (1) of (9.9): save `G.enc` from `inArr` in array `B`, run `P72`, and read the tag of its
output into register `R` (register `R + 1` is a loop counter). -/
def alg99Step1Prog (P72 : Cmd) (B R : ℕ) : Cmd :=
  .seq (copyArrLoopProg inArr B R (R + 1))
    (.seq P72 (.assign R (.read outArr (.const 0))))

/-- The first word of an output of (7.2) is `0` or `1`. -/
theorem headD_lt_two_of_isAlgorithm72Output {ω h : ℕ} {x : Algorithm72Input} {out : List ℕ}
    (hout : IsAlgorithm72Output ω h x out) : 0 < out.length ∧ out.headD 0 < 2 := by
  rcases hout with ⟨code, rfl, _⟩ | ⟨W, _, rfl⟩ <;> simp

private theorem getElem_zero_eq_headD (l : List ℕ) (h : 0 < l.length) : l[0] = l.headD 0 := by
  cases l with
  | nil => simp at h
  | cons a l => rfl

/-- **Step (1) of Algorithm (9.9)** (Graph Minors XIII, page 104), on the Word RAM. -/
theorem alg99Step1Prog_exec {ω h' C c : ℕ} {P72 : Cmd}
    (hP : RunsAsSubroutine algorithm72Size encAlgorithm72In (IsAlgorithm72Output ω h') P72
      (fun s => s) C c)
    {B R : ℕ} (hB : folioCallerArrBase P72 ≤ B) (hR : folioCallerRegBase P72 ≤ R)
    {w n : ℕ} (G : MultiDigraph n) (hw : wordSize c (algorithm72Size ⟨n, G⟩) ≤ w)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hm_w : G.numEdges < 2 ^ w)
    (hlen_w : G.enc.length < 2 ^ w)
    (s : State) (hs : s.arrs inArr = G.enc) :
    ∃ s' t, Exec w (alg99Step1Prog P72 B R) s s' t ∧
      t ≤ C * algorithm72Size ⟨n, G⟩ + 15 * G.enc.length + 12 ∧
      s'.arrs B = G.enc ∧
      IsAlgorithm72Output ω h' ⟨n, G⟩ (s'.arrs outArr) ∧
      s'.regs R = (s'.arrs outArr).headD 0 ∧
      (∀ a : ℕ, B < a → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, R + 1 < r → s'.regs r = s.regs r) := by
  have hB2 : 2 ≤ B := le_trans (le_max_left _ _) hB
  obtain ⟨s₁, t₁, hex₁, ht₁, hB₁, harr₁, hreg₁⟩ :=
    copyArrLoopProg_exec inArr B R (R + 1) (by romega) (by romega) hw1 s
      (by rw [hs]; exact hlen_w) (by rw [hs]; exact mem_enc_lt_two_pow G hn_w hm_w)
  have hin₁ : s₁.arrs inArr = encAlgorithm72In ⟨n, G⟩ := by
    rw [harr₁ inArr (by romega), hs]; rfl
  obtain ⟨s₂, t₂, hex₂, ht₂, hout₂, hreg₂, harr₂⟩ := hP ⟨n, G⟩ w hw s₁ hin₁
  obtain ⟨hpos, htag⟩ := headD_lt_two_of_isAlgorithm72Output hout₂
  have hread : (Expr.read outArr (.const 0)).eval w s₂ = some ((s₂.arrs outArr).headD 0) := by
    have h0 : checkWord w 0 = some 0 := checkWord_of_lt (by omega)
    have hhd : (s₂.arrs outArr)[0]'hpos = (s₂.arrs outArr).headD 0 :=
      getElem_zero_eq_headD _ hpos
    simp only [Expr.eval, h0, hpos, ↓reduceDIte, hhd]
    exact checkWord_of_lt (by omega)
  refine ⟨s₂.setReg R ((s₂.arrs outArr).headD 0), t₁ + (t₂ + ((Expr.read outArr (.const 0)).cost + 1)),
    .seq hex₁ (.seq hex₂ (.assign hread)), ?_, ?_, hout₂, by simp, ?_, ?_⟩
  · rw [hs] at ht₁; dsimp only at ht₂; simp only [Expr.cost]; omega
  · rw [State.setReg_arrs, harr₂ B hB, hB₁, hs]
  · intro a ha
    rw [State.setReg_arrs, harr₂ a (by romega), harr₁ a (by romega)]
  · intro r hr
    rw [State.setReg_regs_ne _ _ (by romega), hreg₂ r (by romega),
      hreg₁ r (by romega) (by romega)]

/-- **Step (1) of Algorithm (9.9)**, the case "If we obtain a branch-decomposition of $G$ of width
$\le \omega$ we stop" (page 104): if the output of
(7.2) starts with `0`, it is an output (i) of (9.9) for the same `ω`. -/
theorem isAlg99Output_of_alg72_tag_zero (dec : Case3BlockDecoder) (p h : ℕ) {ω h' n : ℕ}
    {G : MultiDigraph n} {out : List ℕ} (hout : IsAlgorithm72Output ω h' ⟨n, G⟩ out)
    (htag : out.headD 0 = 0) :
    IsAlg99Output dec p h ω ⟨n, G⟩ out := by
  rcases hout with ⟨code, rfl, hcode⟩ | ⟨W, _, rfl⟩
  · exact Or.inl ⟨code, rfl, hcode⟩
  · simp at htag

/-- **Step (1) of Algorithm (9.9)** (page 104), the case
"Otherwise we obtain a wall $H$ in $G$ of height $h'$": if the output of (7.2) does not start with `0`, it is `1 :: W.encList` for a valid wall `W` of
height `h'` in `G`. -/
theorem exists_wall_of_alg72_tag_ne_zero {ω h' n : ℕ} {G : MultiDigraph n} {out : List ℕ}
    (hout : IsAlgorithm72Output ω h' ⟨n, G⟩ out) (htag : out.headD 0 ≠ 0) :
    ∃ W : WallOfHeight h' G, W.IsValid ∧ out = 1 :: W.encList := by
  rcases hout with ⟨code, rfl, _⟩ | hW
  · simp at htag
  · exact hW

end GraphMinor.Compute
