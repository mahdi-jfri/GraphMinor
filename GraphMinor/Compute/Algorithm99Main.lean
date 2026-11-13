module

public import GraphMinor.Compute.Algorithm99Loop
public import GraphMinor.Compute.Algorithm99Step1
import GraphMinor.Compute.Algorithm91Parse
import GraphMinor.Compute.Join13WordSize72

/-!
# Algorithm (9.9) on its own: step (1), the first state, and the loop

The program `alg99MainProg` is Algorithm (9.9) of Graph Minors XIII (page 104) for an input
graph `G` in `inArr`. It runs step (1) (one call of (7.2)); on a branch-decomposition it stops
(its output is already output (i)); otherwise it stores the first state `G_1 = G`, `Z_1 = ∅`,
`H_1 = H` (`alg99InitProg`), sets the loop flag, and runs the loop (`alg99LoopProg`).

* `isAlg99Output_of_loopOut`: what the loop writes is an output (ii) or (iii) of (9.9).
* `alg99MainProg_exec`: the run, in time at most `K (n + 1) (|E(G)| + n + 1)`.
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph

/-- `omega` after unfolding `Reg` and `Arr`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr, inArr, outArr] at *); omega))

/-- What the loop writes, read as an output of (9.9): the model is mapped to `G` by `orig`
(`IsCliqueModel.map_orig`), and output (iii) is `isAlg99Output_of_case3StepsOutputA`. -/
theorem isAlg99Output_of_loopOut {pp h ω h' n C_blk w B : ℕ} {h2 : 2 ≤ h} {he : Even h}
    {G : MultiDigraph n} {Inv : Alg99Iter h' G → Prop} {out : List ℕ}
    (hout : Alg99LoopOut pp h ω h2 he C_blk w B Inv out) :
    IsAlg99Output case3Decoder pp h ω ⟨n, G⟩ out := by
  obtain ⟨st, hst, -, ⟨K, hK, rfl⟩ | ⟨X, hXc, W, hW, hZ, hKc, s_m, p, hA, hparse, rfl⟩⟩ := hout
  · exact Or.inr (Or.inl ⟨_, rfl, IsCliqueModel.map_orig hst hK⟩)
  · obtain ⟨p', hparse', hout'⟩ := isAlg99Output_of_case3StepsOutputA (pp := pp) hst hXc hZ hKc hA
    rw [hparse] at hparse'
    cases Option.some.inj hparse'
    exact hout'

/-- Algorithm (9.9) on its own: step (1) at array `B` and register `Q`; on a wall, the first
state, `n` in register `Q + 6`, the flag `Q + 5 := 1`, and the loop. -/
def alg99MainProg (P72 P97 P : Cmd) (pp h : ℕ) (h2 : 2 ≤ h) (h' : ℕ) (h2' : 2 ≤ h')
    (B Q : ℕ) : Cmd :=
  .seq (alg99Step1Prog P72 B Q)
    (.ite (.reg Q)
      (.seq (alg99InitProg B (Q + 10))
        (.seq (.assign (Q + 6) (.read B (.const 0)))
          (.seq (.assign (Q + 5) (.const 1)) (alg99LoopProg P97 P pp h h2 h' h2' B Q))))
      .skip)

/-- The time constant of `alg99MainProg`. -/
def alg99MainConst (pp h' C72 C97 K4 C C_blk : ℕ) : ℕ :=
  4 * C72 + 2 * (alg99IterConst pp h' C97 K4 C C_blk + 1) + 20 * elemWallNumVerts h' +
    20 * (elemWallEdges h').length + 300

/-- **Graph Minors XIII, Algorithm (9.9)** (page 104), on the Word RAM, for the programs of
(7.2), (9.7) and of steps (5) to (7). From `G.enc` in `inArr`, the program writes an output of
(9.9) in `outArr`, in time at most `alg99MainConst … * (n + 1) * (|E(G)| + n + 1)`. -/
theorem alg99MainProg_exec {pp h h' ω C72 c72 C97 c97 C C_blk c K4 : ℕ} {h2 : 2 ≤ h}
    {he : Even h} {h2' : 2 ≤ h'} {he' : Even h'} {P72 P97 P : Cmd} {B Q : ℕ}
    (hP72 : RunsAsSubroutine algorithm72Size encAlgorithm72In (IsAlgorithm72Output ω h') P72
      (fun s => s) C72 c72)
    (hP97 : RunsAsSubroutine (alg97Size (h' := h')) (encAlg97In (h' := h'))
      (IsAlg97Output pp (pp.choose 2 + 5) h h') P97 (fun m => m) C97 c97)
    (hP : Case3StepsRuns h h' ω h2 he h2' he' C C_blk c 23 16 (B + 5) 33 (B - 1) (B - 2) (B - 3)
      (B - 4) (B + 6) (Q + 7) (Q + 10) P)
    (hK4 : ∀ n m, alg99Step4Cost (pp.choose 2 + 5) h h' B n m ≤ K4 * (n + m + 1))
    (hB : 40 ≤ B) (hB72 : folioCallerArrBase P72 ≤ B) (hB97 : folioCallerArrBase P97 ≤ B)
    (hQ : 15 ≤ Q) (hQ72 : folioCallerRegBase P72 ≤ Q) (hQ97 : folioCallerRegBase P97 ≤ Q)
    {n : ℕ} (G : MultiDigraph n) {w : ℕ}
    (hw : wordSize (5 * c72 + alg99WordConst pp h h' c97 c C_blk)
      ((n + 1) * (G.numEdges + n + 1)) ≤ w)
    {s : State} (hs : s.arrs inArr = G.enc) :
    ∃ s' t, Exec w (alg99MainProg P72 P97 P pp h h2 h' h2' B Q) s s' t ∧
      t ≤ alg99MainConst pp h' C72 C97 K4 C C_blk * ((n + 1) * (G.numEdges + n + 1)) ∧
      IsAlg99Output case3Decoder pp h ω ⟨n, G⟩ (s'.arrs outArr) := by
  set N := (n + 1) * (G.numEdges + n + 1) with hN
  set cW := alg99WordConst pp h h' c97 c C_blk with hcW
  have hcW' : 20 + h' + 4 * elemWallNumVerts h' + (elemWallEdges h').length ≤ cW := by
    rw [hcW]; unfold alg99WordConst; omega
  have hN1 : G.numEdges + n + 1 ≤ N := Nat.le_mul_of_pos_left _ (by omega)
  have hn1 : n + 1 ≤ N := Nat.le_mul_of_pos_right _ (by omega)
  have wl : ∀ {D q : ℕ}, 1 ≤ D → D ≤ 5 * c72 + cW → q ≤ D * (N + 1) → q < 2 ^ w :=
    fun hD1 hD hq => hq.trans_lt (linear_lt_wordSize72 (by omega) hD hw)
  have wN : ∀ {q : ℕ}, q ≤ N + 1 → q < 2 ^ w := fun hq => wl (D := 1) le_rfl (by omega)
    (by omega)
  have hw1 : 1 < 2 ^ w := wN (by omega)
  have hAP : G.numActivePairs ≤ G.numEdges := MultiDigraph.numActivePairs_le_numEdges _
  have h72 : algorithm72Size ⟨n, G⟩ ≤ 2 * (N + 1) := by
    change (n + 1) ^ 2 + G.numEdges + n + 1 ≤ 2 * ((n + 1) * (G.numEdges + n + 1) + 1)
    have := Nat.mul_le_mul_left (n + 1) (show n + 1 ≤ G.numEdges + n + 1 by omega)
    rw [Nat.pow_two]; omega
  have hw72 : wordSize c72 (algorithm72Size ⟨n, G⟩) ≤ w :=
    ((wordSize_le_of_le_mul h72).trans (wordSize_mono_left (by omega) N)).trans hw
  -- Step (1).
  obtain ⟨s₁, t₁, hex₁, ht₁, hB₁, hout₁, hR₁, harr₁, hreg₁⟩ :=
    alg99Step1Prog_exec hP72 hB72 hQ72 G hw72 (wN (by omega)) (wN (by omega)) (wN (by omega))
      (wl (D := 3) (by omega) (by omega) (by rw [MultiDigraph.length_enc]; omega)) s hs
  have ht1 : t₁ ≤ 4 * (C72 * N) + 92 * N := by
    have h1 := Nat.mul_le_mul_left C72 h72
    have h2 : C72 * (2 * (N + 1)) = 2 * (C72 * N) + 2 * C72 := by ring
    have h3 : C72 ≤ C72 * N := Nat.le_mul_of_pos_right _ (by omega)
    rw [MultiDigraph.length_enc] at ht₁
    omega
  have hMC : alg99MainConst pp h' C72 C97 K4 C C_blk * N = 4 * (C72 * N) +
      2 * ((alg99IterConst pp h' C97 K4 C C_blk + 1) * N) +
      20 * (elemWallNumVerts h' * N) + 20 * ((elemWallEdges h').length * N) + 300 * N := by
    unfold alg99MainConst; ring
  by_cases htag : (s₁.arrs outArr).headD 0 = 0
  · -- Output (i): a branch-decomposition of `G`.
    have hcond : (Expr.reg Q).eval w s₁ = some 0 := by
      simp only [Expr.eval, hR₁, htag]; exact checkWord_of_lt (by omega)
    refine ⟨s₁, t₁ + (1 + 1), .seq hex₁ (.ite_false hcond (.skip _)), ?_,
      isAlg99Output_of_alg72_tag_zero case3Decoder pp h hout₁ htag⟩
    rw [hMC]
    omega
  · -- A wall `H`: the first state and the loop.
    obtain ⟨W, hW, hWout⟩ := exists_wall_of_alg72_tag_ne_zero hout₁ htag
    have hcond : (Expr.reg Q).eval w s₁ = some 1 := by
      simp only [Expr.eval, hR₁, hWout, List.headD_cons]; exact checkWord_of_lt hw1
    have hWl := Alg91.length_encList_le_of_isValid hW
    have hD : ∀ {D q : ℕ}, 1 ≤ D → D ≤ 5 * c72 + cW → q ≤ D + N → q < 2 ^ w :=
      fun {D q} h1 hD hq => wl h1 hD (hq.trans (by
        have := Nat.le_mul_of_pos_left N (show 0 < D by omega)
        rw [Nat.mul_succ]; omega))
    obtain ⟨s₂, t₂, hex₂, ht₂, hS₂, harr₂, hreg₂⟩ :=
      alg99InitProg_exec W hW B (Q + 10) (by omega) (wN (by omega)) (wN (by omega))
        (wN (by omega)) (wl (D := 3) (by omega) (by omega) (by rw [MultiDigraph.length_enc]; omega))
        (hD (D := h' + 1) (by omega) (by omega) (by omega))
        (hD (D := 3 + 2 * elemWallNumVerts h') (by omega) (by omega) (by omega))
        (hD (D := 4 + elemWallNumVerts h' + (elemWallEdges h').length) (by omega) (by omega) (by omega)) hB₁ hWout
    have hB₂ : s₂.arrs B = G.enc := by rw [harr₂ B (Or.inl (by omega)), hB₁]
    have hpos : 0 < (s₂.arrs B).length := by rw [hB₂]; simp
    have h0 : (s₂.arrs B)[0]'hpos = n := by simp [hB₂, MultiDigraph.enc]
    have hex₃ : Exec w (.assign (Q + 6) (.read B (.const 0))) s₂ (s₂.setReg (Q + 6) n) 3 :=
      .assign (by simp only [Expr.eval, checkWord_of_lt (show 0 < 2 ^ w by omega), hpos,
        ↓reduceDIte, h0, checkWord_of_lt (wN (show n ≤ N + 1 by omega))])
    have hex₄ : Exec w (.assign (Q + 5) (.const 1)) (s₂.setReg (Q + 6) n)
        ((s₂.setReg (Q + 6) n).setReg (Q + 5) 1) 2 :=
      .assign (by simp [Expr.eval, checkWord, show (1 : ℕ) < 2 ^ w by omega])
    obtain ⟨s₅, t₅, hex₅, ht₅, -, hout₅⟩ :=
      alg99LoopProg_exec (ω := ω) hP97 hP hK4 hB hB97 hQ hQ97 (fun _ => True)
        (fun _ _ _ _ _ _ _ => trivial) (Alg99Iter.init W) (Alg99Iter.init_isValid hW _) trivial
        ((wordSize_mono_left (by omega) _).trans hw) (s := (s₂.setReg (Q + 6) n).setReg (Q + 5) 1)
        hS₂ (by simp [State.setReg_regs_ne _ _ (show Q + 6 ≠ Q + 5 by omega)])
        (by simp)
    refine ⟨s₅, t₁ + (1 + (t₂ + (3 + (2 + t₅)))),
      .seq hex₁ (.ite_true hcond one_ne_zero (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))), ?_,
      isAlg99Output_of_loopOut hout₅⟩
    change t₅ ≤ 2 * (alg99IterConst pp h' C97 K4 C C_blk + 1) * N at ht₅
    have e5 : 2 * (alg99IterConst pp h' C97 K4 C C_blk + 1) * N =
        2 * ((alg99IterConst pp h' C97 K4 C C_blk + 1) * N) := by ring
    have h1 := Nat.le_mul_of_pos_right (elemWallNumVerts h') (show 0 < N by omega)
    have h2 := Nat.le_mul_of_pos_right (elemWallEdges h').length (show 0 < N by omega)
    rw [MultiDigraph.length_enc] at ht₂
    rw [hMC]
    omega

end GraphMinor.Compute

namespace GraphMinor.Compute

/-- **Graph Minors XIII, (9.8) and Algorithm (9.9)** (page 104), the program on its own, from
(7.2), (9.7) and the programs of steps (5) to (7): for the `ω` of (7.2) at the height `h'` of
(9.7), `alg99MainProg` computes an output of (9.9) in time `O(vε)`. -/
theorem alg99MainProg_computes {pp h h' ω C72 c72 C97 c97 C C_blk c K4 : ℕ} {h2 : 2 ≤ h}
    {he : Even h} {h2' : 2 ≤ h'} {he' : Even h'} {P72 P97 P : Cmd} {B Q : ℕ}
    (hP72 : RunsAsSubroutine algorithm72Size encAlgorithm72In (IsAlgorithm72Output ω h') P72
      (fun s => s) C72 c72)
    (hP97 : RunsAsSubroutine (alg97Size (h' := h')) (encAlg97In (h' := h'))
      (IsAlg97Output pp (pp.choose 2 + 5) h h') P97 (fun m => m) C97 c97)
    (hP : Case3StepsRuns h h' ω h2 he h2' he' C C_blk c 23 16 (B + 5) 33 (B - 1) (B - 2) (B - 3)
      (B - 4) (B + 6) (Q + 7) (Q + 10) P)
    (hK4 : ∀ n m, alg99Step4Cost (pp.choose 2 + 5) h h' B n m ≤ K4 * (n + m + 1))
    (hB : 40 ≤ B) (hB72 : folioCallerArrBase P72 ≤ B) (hB97 : folioCallerArrBase P97 ≤ B)
    (hQ : 15 ≤ Q) (hQ72 : folioCallerRegBase P72 ≤ Q) (hQ97 : folioCallerRegBase P97 ≤ Q) :
    ComputesArrRelInTime alg99Size encAlg99In (IsAlg99Output case3Decoder pp h ω)
      (alg99MainProg P72 P97 P pp h h2 h' h2' B Q) (fun m => m) := by
  refine ⟨alg99MainConst pp h' C72 C97 K4 C C_blk + 1, 5 * c72 + alg99WordConst pp h h' c97 c C_blk,
    by omega, by unfold alg99WordConst; omega, fun x s hs => ?_⟩
  obtain ⟨s', t, hex, ht, hout⟩ := alg99MainProg_exec (ω := ω) hP72 hP97 hP hK4 hB hB72 hB97 hQ
    hQ72 hQ97 x.G le_rfl hs
  exact ⟨s', t, hex, ht.trans (Nat.mul_le_mul_right _ (by omega)), hout⟩

end GraphMinor.Compute
