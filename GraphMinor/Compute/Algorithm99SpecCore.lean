module

public import GraphMinor.Compute.Algorithm99Main
public import GraphMinor.Compute.Algorithm99SpecState
import GraphMinor.Compute.Algorithm91Parse
import GraphMinor.Compute.Join13WordSize72
import GraphMinor.Compute.Algorithm105Step2
import GraphMinor.Compute.Algorithm77Prog75Full

/-!
# Algorithm (9.9) on `G_i \ Z_i`, as (10.5) calls it

Algorithm (10.5) of Graph Minors XIII (page 108) calls (9.9) on `G_i \ Z_i`. It gives the
multigraph `D = G_i.deleteVertices Z_i` on `Fin m` (the vertices of `Z_i` stay, with no edges)
and the set `Z_i` (`Alg99Spec`). The program `alg99SpecCoreProg` runs (9.9) on `D` with the
vertices outside `Z_i` renumbered (`Algorithm99SpecState.lean`):

1. it writes `G_c = D.deleteVerticesCompact Z_i` and the list of `compactEmb Z_i`
   (`deleteVerticesCompactProg`, `compactOrigProg`), and saves `D.enc` in array `B + 8`;
2. it runs step (1) on `G_c`; on a branch-decomposition of `G_c` it stops;
3. otherwise it stores the first state `Alg99Iter.initCompact G_i Z_i H` and runs the loop, with
   the property "`orig` misses `Z_i`".

`alg99SpecCoreProg_exec` is the result. The input `D.enc` is in array `0` and `bitSetList Z_i`
in array `1`; the caller shifts the program so that these are the arrays of `Alg99Spec`.
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph

/-- `omega` after unfolding `Reg` and `Arr`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr, inArr, outArr] at *); omega))

/-- Algorithm (9.9) on `D = G_i \ Z_i` (array `0`) with `bitSetList Z_i` in array `1`. -/
def alg99SpecCoreProg (P72 P97 P : Cmd) (pp h : ℕ) (h2 : 2 ≤ h) (h' : ℕ) (h2' : 2 ≤ h')
    (B Q : ℕ) : Cmd :=
  .seq (deleteVerticesCompactProg inArr outArr (B + 7) (B + 6) (B + 5) (Q + 10))
  (.seq (.assign (Q + 6) (.read inArr (.const 0)))
  (.seq (.assign (Q + 8) (.read (B + 5) (.const 0)))
  (.seq (compactOrigProg outArr (B + 6) (B + 9) (Q + 6) (Q + 8) (Q + 9))
  (.seq (copyArrLoopProg inArr (B + 8) (Q + 10) (Q + 11))
  (.seq (copyArrLoopProg (B + 5) inArr (Q + 10) (Q + 11))
  (.seq (alg99Step1Prog P72 B Q)
    (.ite (.reg Q)
      (.seq (alg99InitProg B (Q + 10))
        (.seq (copyArrLoopProg (B + 9) (B + 2) (Q + 10) (Q + 11))
          (.seq (.assign (Q + 6) (.read (B + 8) (.const 0)))
            (.seq (.assign (Q + 5) (.const 1)) (alg99LoopProg P97 P pp h h2 h' h2' B Q)))))
      .skip)))))))

/-- The time constant of `alg99SpecCoreProg`. -/
def alg99SpecCoreConst (pp h' C72 C97 K4 C C_blk : ℕ) : ℕ :=
  4 * C72 + 2 * (alg99IterConst pp h' C97 K4 C C_blk + 1) + 20 * elemWallNumVerts h' +
    20 * (elemWallEdges h').length + 1000

/-- **Algorithm (9.9) on `G_i \ Z_i`** (Graph Minors XIII, page 104, as called in (10.5), page
108), on the Word RAM. From `D.enc` in array `0` and `bitSetList Z_i` in array `1`
(`D = G_i \ Z_i` on `Fin m`), the program ends with either
* `0 :: code` in `outArr`, a branch-decomposition of width `≤ ω` of the renumbered graph
  `G_c = D.deleteVerticesCompact Z_i`, and `D.enc` in array `B + 8`; or
* an output of the loop (`Alg99LoopOut`) for `D`, for a state whose map `orig` misses `Z_i`,
  and `m` in register `Q + 6`.

The time is at most `alg99SpecCoreConst … * ((m + 1) * (|E(D)| + m + 1))`. -/
theorem alg99SpecCoreProg_exec {pp h h' ω C72 c72 C97 c97 C C_blk c K4 : ℕ} {h2 : 2 ≤ h}
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
    {m : ℕ} (Gi : MultiDigraph m) (Zs : Finset (Fin m)) {w : ℕ}
    (hw : wordSize (5 * c72 + alg99WordConst pp h h' c97 c C_blk)
      ((m + 1) * ((Gi.deleteVertices Zs).numEdges + m + 1)) ≤ w)
    {s : State} (hs : s.arrs inArr = (Gi.deleteVertices Zs).enc)
    (hZ : s.arrs outArr = bitSetList Zs) :
    ∃ s' t, Exec w (alg99SpecCoreProg P72 P97 P pp h h2 h' h2' B Q) s s' t ∧
      t ≤ alg99SpecCoreConst pp h' C72 C97 K4 C C_blk *
        ((m + 1) * ((Gi.deleteVertices Zs).numEdges + m + 1)) ∧
      ((∃ code : List ℕ, s'.arrs outArr = 0 :: code ∧
          IsValidBranchDecompCode ω ((Gi.deleteVertices Zs).deleteVerticesCompact Zs) code ∧
          s'.arrs (B + 8) = (Gi.deleteVertices Zs).enc) ∨
        (s'.regs (Q + 6) = m ∧
          Alg99LoopOut pp h ω h2 he C_blk w B (h' := h') (G := Gi.deleteVertices Zs)
            (fun st => ∀ u, st.orig u ∉ Zs) (s'.arrs outArr))) := by
  set D := Gi.deleteVertices Zs with hDdef
  set Gc := D.deleteVerticesCompact Zs with hGc
  set N := (m + 1) * (D.numEdges + m + 1) with hN
  set cW := alg99WordConst pp h h' c97 c C_blk with hcW
  have hcW' : 20 + h' + 4 * elemWallNumVerts h' + (elemWallEdges h').length ≤ cW := by
    rw [hcW]; unfold alg99WordConst; omega
  have hN1 : D.numEdges + m + 1 ≤ N := Nat.le_mul_of_pos_left _ (by omega)
  have hn1 : m + 1 ≤ N := Nat.le_mul_of_pos_right _ (by omega)
  have wl : ∀ {D q : ℕ}, 1 ≤ D → D ≤ 5 * c72 + cW → q ≤ D * (N + 1) → q < 2 ^ w :=
    fun hD1 hD hq => hq.trans_lt (linear_lt_wordSize72 (by omega) hD hw)
  have wN : ∀ {q : ℕ}, q ≤ N + 1 → q < 2 ^ w := fun hq => wl (D := 1) le_rfl (by omega)
    (by omega)
  have hw1 : 1 < 2 ^ w := wN (by omega)
  have hw3 : 3 < 2 ^ w := wl (D := 3) (by omega) (by omega) (by omega)
  have hAP : D.numActivePairs ≤ D.numEdges := MultiDigraph.numActivePairs_le_numEdges _
  have hvm : Zsᶜ.card ≤ m := by
    simpa using Finset.card_le_univ Zsᶜ
  have hEc : Gc.numEdges ≤ D.numEdges := numEdges_deleteVerticesCompact_le D Zs
  have hAPc : Gc.numActivePairs ≤ D.numActivePairs :=
    (MultiDigraph.numActivePairs_deleteVerticesCompact D Zs).trans_le
      (MultiDigraph.numActivePairs_deleteVertices_le D Zs)
  have hlenD : D.enc.length ≤ 3 * (N + 1) := by rw [MultiDigraph.length_enc]; omega
  have hlenC : Gc.enc.length ≤ 3 * (N + 1) := by rw [MultiDigraph.length_enc]; omega
  -- 1. The renumbered graph and the ranks.
  obtain ⟨s₁, t₁, hex₁, ht₁, hGc₁, hrank₁, harr₁, hreg₁⟩ :=
    deleteVerticesCompactProg_exec D Zs inArr outArr (B + 7) (B + 6) (B + 5) (Q + 10)
      (by romega) (by romega) (by romega) (by romega) (by romega) (by romega) hw3
      (wN (by omega)) (wl (D := 3) (by omega) (by omega) (by omega)) (wN (by omega)) hs hZ
  have hD₁ : s₁.arrs inArr = D.enc := by rw [harr₁ _ (by romega) (by romega) (by romega), hs]
  have hZ₁ : s₁.arrs outArr = bitSetList Zs := by
    rw [harr₁ _ (by romega) (by romega) (by romega), hZ]
  -- 2. `m` and `|Z_iᶜ|`.
  have hposD : 0 < (s₁.arrs inArr).length := by rw [hD₁]; simp
  have h0D : (s₁.arrs inArr)[0]'hposD = m := by simp [hD₁, MultiDigraph.enc]
  have c0 := checkWord_of_lt (w := w) (v := 0) (by omega)
  let s₂ := s₁.setReg (Q + 6) m
  have hex₂ : Exec w (.assign (Q + 6) (.read inArr (.const 0))) s₁ s₂ 3 :=
    .assign (by simp only [Expr.eval, c0, hposD, ↓reduceDIte, h0D,
      checkWord_of_lt (wN (show m ≤ N + 1 by omega))])
  have hposC : 0 < (s₂.arrs (B + 5)).length := by simp [s₂, hGc₁]
  have h0C : (s₂.arrs (B + 5))[0]'hposC = Zsᶜ.card := by
    simp [s₂, hGc₁, Gc, MultiDigraph.enc]
  let s₃ := s₂.setReg (Q + 8) Zsᶜ.card
  have hex₃ : Exec w (.assign (Q + 8) (.read (B + 5) (.const 0))) s₂ s₃ 3 :=
    .assign (by simp only [Expr.eval, c0, hposC, ↓reduceDIte, h0C,
      checkWord_of_lt (wN (show Zsᶜ.card ≤ N + 1 by omega))])
  -- 3. The list of `compactEmb Z_i`.
  obtain ⟨s₄, t₄, hex₄, ht₄, horig₄, harr₄, hreg₄⟩ :=
    compactOrigProg_exec Zs outArr (B + 6) (B + 9) (Q + 6) (Q + 8) (Q + 9) (by romega)
      (by romega) (by romega) (by omega) (wN (by omega)) (s := s₃) (by simpa [s₃, s₂] using hZ₁)
      (by simpa [s₃, s₂] using hrank₁) (by simp [s₃, s₂]) (by simp [s₃])
  -- 4. Save `D.enc` and put `G_c.enc` in `inArr`.
  have hD₄ : s₄.arrs inArr = D.enc := by
    rw [harr₄ _ (by romega)]; simpa [s₃, s₂] using hD₁
  obtain ⟨s₅, t₅, hex₅, ht₅, h8₅, harr₅, hreg₅⟩ :=
    copyArrLoopProg_exec inArr (B + 8) (Q + 10) (Q + 11) (by romega) (by romega) hw1 s₄
      (by rw [hD₄]; exact wl (D := 3) (by omega) (by omega) hlenD)
      (by rw [hD₄]; exact mem_enc_lt_two_pow D (wN (by omega)) (wN (by omega)))
  rw [hD₄] at ht₅ h8₅
  have hC₅ : s₅.arrs (B + 5) = Gc.enc := by
    rw [harr₅ _ (by romega), harr₄ _ (by romega)]; simpa [s₃, s₂] using hGc₁
  obtain ⟨s₆, t₆, hex₆, ht₆, h0₆, harr₆, hreg₆⟩ :=
    copyArrLoopProg_exec (B + 5) inArr (Q + 10) (Q + 11) (by romega) (by romega) hw1 s₅
      (by rw [hC₅]; exact wl (D := 3) (by omega) (by omega) hlenC)
      (by rw [hC₅]; exact mem_enc_lt_two_pow Gc (wN (by omega)) (wN (by omega)))
  rw [hC₅] at ht₆ h0₆
  -- 5. Step (1) on `G_c`.
  have h72s : algorithm72Size ⟨_, Gc⟩ ≤ 2 * (N + 1) := by
    change (Zsᶜ.card + 1) ^ 2 + Gc.numEdges + Zsᶜ.card + 1 ≤ 2 * ((m + 1) * (D.numEdges + m + 1) + 1)
    have := Nat.mul_le_mul (show Zsᶜ.card + 1 ≤ m + 1 by omega)
      (show Zsᶜ.card + 1 ≤ D.numEdges + m + 1 by omega)
    rw [Nat.pow_two]; omega
  have hw72 : wordSize c72 (algorithm72Size ⟨_, Gc⟩) ≤ w :=
    ((wordSize_le_of_le_mul h72s).trans (wordSize_mono_left (by omega) N)).trans hw
  obtain ⟨s₇, t₇, hex₇, ht₇, hB₇, hout₇, hR₇, harr₇, hreg₇⟩ :=
    alg99Step1Prog_exec hP72 hB72 hQ72 Gc hw72 hw1 (wN (by omega)) (wN (by omega))
      (wl (D := 3) (by omega) (by omega) hlenC) s₆ h0₆
  have ht7 : t₇ ≤ 4 * (C72 * N) + 110 * N := by
    have h1 := Nat.mul_le_mul_left C72 h72s
    have h2 : C72 * (2 * (N + 1)) = 2 * (C72 * N) + 2 * C72 := by ring
    have h3 : C72 ≤ C72 * N := Nat.le_mul_of_pos_right _ (by omega)
    have := hlenC
    omega
  have h8₇ : s₇.arrs (B + 8) = D.enc := by
    rw [harr₇ _ (by omega), harr₆ _ (by romega), h8₅]
  have h9₇ : s₇.arrs (B + 9) = List.ofFn (fun j : Fin Zsᶜ.card => (compactEmb Zs j).1) := by
    rw [harr₇ _ (by omega), harr₆ _ (by romega), harr₅ _ (by romega), horig₄]
  have hMC : alg99SpecCoreConst pp h' C72 C97 K4 C C_blk * N = 4 * (C72 * N) +
      2 * ((alg99IterConst pp h' C97 K4 C C_blk + 1) * N) +
      20 * (elemWallNumVerts h' * N) + 20 * ((elemWallEdges h').length * N) + 1000 * N := by
    unfold alg99SpecCoreConst; ring
  have ht16 : t₁ + 3 + 3 + t₄ + t₅ + t₆ ≤ 400 * N := by
    have := hlenC
    have := hlenD
    omega
  by_cases htag : (s₇.arrs outArr).headD 0 = 0
  · -- A branch-decomposition of `G_c`: stop.
    have hcond : (Expr.reg Q).eval w s₇ = some 0 := by
      simp only [Expr.eval, hR₇, htag]; exact checkWord_of_lt (by omega)
    obtain ⟨code, hcode, hval⟩ | ⟨W, -, hWout⟩ := hout₇
    · refine ⟨s₇, t₁ + (3 + (3 + (t₄ + (t₅ + (t₆ + (t₇ + (1 + 1))))))),
        .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
          (.seq hex₇ (.ite_false hcond (.skip _)))))))), ?_,
        Or.inl ⟨code, hcode, hval, h8₇⟩⟩
      rw [hMC]
      omega
    · simp [hWout] at htag
  · -- A wall `H` of `G_c`: the first state and the loop.
    obtain ⟨W, hW, hWout⟩ := exists_wall_of_alg72_tag_ne_zero hout₇ htag
    have hcond : (Expr.reg Q).eval w s₇ = some 1 := by
      simp only [Expr.eval, hR₇, hWout, List.headD_cons]; exact checkWord_of_lt hw1
    have hWl := Alg91.length_encList_le_of_isValid hW
    have hD : ∀ {D q : ℕ}, 1 ≤ D → D ≤ 5 * c72 + cW → q ≤ D + N → q < 2 ^ w :=
      fun {D q} h1 hD hq => wl h1 hD (hq.trans (by
        have := Nat.le_mul_of_pos_left N (show 0 < D by omega)
        rw [Nat.mul_succ]; omega))
    obtain ⟨s₈, t₈, hex₈, ht₈, hS₈, harr₈, hreg₈⟩ :=
      alg99InitProg_exec W hW B (Q + 10) (by omega) hw1 (wN (by omega))
        (wN (by omega)) (wl (D := 3) (by omega) (by omega) hlenC)
        (hD (D := h' + 1) (by omega) (by omega) (by omega))
        (hD (D := 3 + 2 * elemWallNumVerts h') (by omega) (by omega) (by omega))
        (hD (D := 4 + elemWallNumVerts h' + (elemWallEdges h').length) (by omega) (by omega)
          (by omega)) hB₇ hWout
    have h9₈ : s₈.arrs (B + 9) = List.ofFn (fun j : Fin Zsᶜ.card => (compactEmb Zs j).1) := by
      rw [harr₈ _ (Or.inr (by omega)), h9₇]
    have h8₈ : s₈.arrs (B + 8) = D.enc := by rw [harr₈ _ (Or.inr (by omega)), h8₇]
    obtain ⟨s₉, t₉, hex₉, ht₉, h2₉, harr₉, hreg₉⟩ :=
      copyArrLoopProg_exec (B + 9) (B + 2) (Q + 10) (Q + 11) (by romega) (by romega) hw1 s₈
        (by rw [h9₈]; simpa using wN (show Zsᶜ.card ≤ N + 1 by omega))
        (by
          rw [h9₈]
          intro x hx
          obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
          exact wN (show (compactEmb Zs j).1 ≤ N + 1 by have := (compactEmb Zs j).2; omega))
    rw [h9₈] at ht₉ h2₉
    simp only [List.length_ofFn] at ht₉
    have hS₉ : (Alg99Iter.initCompact Gi Zs W).StoredIn B s₉ := by
      obtain ⟨h1, -, h3, h4⟩ := hS₈
      refine ⟨?_, h2₉, ?_, ?_⟩
      · rw [harr₉ _ (by romega)]; exact h1
      · rw [harr₉ _ (by romega)]; exact h3
      · rw [harr₉ _ (by romega)]; exact h4
    have h8₉ : s₉.arrs (B + 8) = D.enc := by rw [harr₉ _ (by romega), h8₈]
    have hpos8 : 0 < (s₉.arrs (B + 8)).length := by rw [h8₉]; simp
    have h08 : (s₉.arrs (B + 8))[0]'hpos8 = m := by simp [h8₉, MultiDigraph.enc]
    have hex₁₀ : Exec w (.assign (Q + 6) (.read (B + 8) (.const 0))) s₉ (s₉.setReg (Q + 6) m) 3 :=
      .assign (by simp only [Expr.eval, c0, hpos8, ↓reduceDIte, h08,
        checkWord_of_lt (wN (show m ≤ N + 1 by omega))])
    have hex₁₁ : Exec w (.assign (Q + 5) (.const 1)) (s₉.setReg (Q + 6) m)
        ((s₉.setReg (Q + 6) m).setReg (Q + 5) 1) 2 :=
      .assign (by simp [Expr.eval, checkWord, show (1 : ℕ) < 2 ^ w by omega])
    have hsz : (m + 1) * ((Alg99Iter.initCompact Gi Zs W).Gi.numEdges +
        (Alg99Iter.initCompact Gi Zs W).v + 1) ≤ N :=
      Nat.mul_le_mul_left _ (show Gc.numEdges + Zsᶜ.card + 1 ≤ D.numEdges + m + 1 by omega)
    obtain ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, hn₁₂, hout₁₂⟩ :=
      alg99LoopProg_exec (ω := ω) hP97 hP hK4 hB hB97 hQ hQ97 (G := D)
        (fun st => ∀ u, st.orig u ∉ Zs)
        (fun _ X V_A Bd _ W_A hI => Alg99Iter.step8_orig_not_mem hI X V_A Bd W_A)
        (Alg99Iter.initCompact Gi Zs W) (Alg99Iter.initCompact_isValid Gi Zs hW _)
        (Alg99Iter.initCompact_orig_not_mem Gi Zs W)
        (((wordSize_mono_right _ hsz).trans (wordSize_mono_left (by omega) _)).trans hw)
        (s := (s₉.setReg (Q + 6) m).setReg (Q + 5) 1)
        hS₉ (by simp [State.setReg_regs_ne _ _ (show Q + 6 ≠ Q + 5 by omega)]) (by simp)
    refine ⟨s₁₂, t₁ + (3 + (3 + (t₄ + (t₅ + (t₆ + (t₇ + (1 + (t₈ + (t₉ + (3 + (2 + t₁₂))))))))))),
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇
        (.ite_true hcond one_ne_zero (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁
          hex₁₂))))))))))),
      ?_, Or.inr ⟨hn₁₂, hout₁₂⟩⟩
    have hL := Nat.mul_le_mul_left (2 * (alg99IterConst pp h' C97 K4 C C_blk + 1)) hsz
    have e5 : 2 * (alg99IterConst pp h' C97 K4 C C_blk + 1) * N =
        2 * ((alg99IterConst pp h' C97 K4 C C_blk + 1) * N) := by ring
    have h1 := Nat.le_mul_of_pos_right (elemWallNumVerts h') (show 0 < N by omega)
    have h2 := Nat.le_mul_of_pos_right (elemWallEdges h').length (show 0 < N by omega)
    have := hlenC
    rw [hMC]
    omega

end GraphMinor.Compute
