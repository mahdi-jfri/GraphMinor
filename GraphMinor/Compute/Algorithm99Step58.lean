module

public import GraphMinor.Compute.Algorithm99Case3Claim
public import GraphMinor.Compute.Algorithm99Step8Prog
public import GraphMinor.Compute.Algorithm99OutIIIProg
public import GraphMinor.Compute.Algorithm99Length
public import GraphMinor.Compute.Algorithm99Step4Prog
import GraphMinor.Compute.Algorithm91Parse

/-!
# Steps (5) to (8) of Algorithm (9.9), in one program

After step (4) of Algorithm (9.9) (Graph Minors XIII, pages 104–105) the program has a flat wall
`H^1` of height `h` in `G' \ X` (`G' = (G_i \ X) ∪ H_i`) and its compass. Steps (5) to (7) are the
program `P` of `Case3StepsClaim`. It ends with a tag: on tag `0` "we stop" with output (iii), and
on tag `1` step (8) builds the next state.

`alg99Step58Prog` runs `P` and branches on its tag. On tag `0` it writes the output (iii) in the
labels of `G` (`alg99OutAProg`) and clears the loop flag. On tag `1` it writes the next state
`st.step8 X V_A Bd W_A` (`alg99Step8Prog`), which is valid and at most half as large
(`Alg99Iter.step8_of_outputB`). The result is `alg99Step58_exec`.

The arrays are fixed as follows, for a base `B ≥ 40` of the stored state and a base `Q` of the
registers of the loop: `P` reads arrays `23, 16, B + 5, 33` (what step (4) writes) and writes
`B - 1, B - 2, B - 3, B - 4`; the loop flag is register `Q + 5`, `n` is in register `Q + 6`, the
tag of `P` in register `Q + 7`, and the programs called after `P` use registers from `Q + 10`.

`Case3StepsRuns` is the property that `Case3StepsClaim` gives for one choice of array indices
(`case3StepsRuns_of_claim`).
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph

/-- `omega` after unfolding `Reg` and `Arr`, which `omega` does not see as `ℕ`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr, inArr, outArr] at *); omega))

/-- What `Case3StepsClaim` says of the program `P` for fixed array indices and constants. -/
def Case3StepsRuns (h h' ω : ℕ) (h2 : 2 ≤ h) (he : Even h) (h2' : 2 ≤ h') (he' : Even h')
    (C C_blk c a_G' a_X a_W a_VK a_out a_bd a_wall a_A_enc a_base r_tag r_base : ℕ)
    (P : Cmd) : Prop :=
  ∀ (w n : ℕ) (G' : MultiDigraph n) (X : Finset (Fin n))
    (W : WallOfHeight h (G'.deleteVertices X)) (hW : W.IsValid),
    Disjoint W.vertexFinset X →
    W.IsFlatWall h2 →
    Disjoint W.compassFinset X →
    W.compassFinset.toNatSet =
      V(GM13.wallCompass (delGraph G' X) (W.toGMWall h2 he hW)) →
    wordSize c ((n + 1) * (G'.numEdges + n + 1)) ≤ w →
    ∀ s : State,
      s.arrs a_G' = G'.enc →
      s.arrs a_X = bitSetList X →
      s.arrs a_W = W.encList →
      s.arrs a_VK = bitSetList W.compassFinset →
      ∃ s' t, Exec w P s s' t ∧
        t ≤ C * (n + 1) * (G'.numEdges + n + 1) ∧
        (∀ a, a < a_base → a ≠ a_out → a ≠ a_bd → a ≠ a_wall → a ≠ a_A_enc →
          s'.arrs a = s.arrs a) ∧
        (∀ r, r < r_base → r ≠ r_tag → s'.regs r = s.regs r) ∧
        ((s'.regs r_tag = 0 ∧
            IsCase3StepsOutputA h ω G' X W h2 he hW C_blk w a_out a_wall s') ∨
          (s'.regs r_tag = 1 ∧
            IsCase3StepsOutputB h h' G' X W h2 he hW h2' he' a_out a_bd a_wall a_A_enc s'))

/-- `Case3StepsClaim` for one choice of array indices. -/
theorem case3StepsRuns_of_claim (hC3 : Case3StepsClaim) (h h' ω : ℕ) (h2 : 2 ≤ h)
    (he : Even h) (h2' : 2 ≤ h') (he' : Even h') (shiloachProg : Cmd)
    (h86 : ComputesArrRelInTime alg81Size encAlg81In
      (fun x out => IsValidAlg86Output x (decAlg86Out x out)) (alg86Prog shiloachProg)
      (fun s => s))
    (P72 : Cmd)
    (h72 : ComputesArrRelInTime algorithm72Size encAlgorithm72In (IsAlgorithm72Output ω h') P72
      (fun s => s)) :
    ∃ C C_blk c : ℕ, ∀ (a_G' a_X a_W a_VK a_out a_bd a_wall a_A_enc a_base r_tag r_base : ℕ),
      (∀ a ∈ [a_G', a_X, a_W, a_VK, a_out, a_bd, a_wall, a_A_enc], a < a_base) →
      [a_out, a_bd, a_wall, a_A_enc].Nodup →
      List.Disjoint [a_out, a_bd, a_wall, a_A_enc] [a_G', a_X, a_W, a_VK] →
      r_tag < r_base →
      ∃ P : Cmd, Case3StepsRuns h h' ω h2 he h2' he' C C_blk c a_G' a_X a_W a_VK a_out a_bd
        a_wall a_A_enc a_base r_tag r_base P := by
  obtain ⟨C, C_blk, c, hC⟩ := hC3 h h' ω h2 he h2' he' shiloachProg h86 P72 h72
  exact ⟨C, C_blk, c, fun a_G' a_X a_W a_VK a_out a_bd a_wall a_A_enc a_base r_tag r_base hlt hnd
    hdj hr => hC a_G' a_X a_W a_VK a_out a_bd a_wall a_A_enc a_base r_tag r_base hlt hnd hdj hr⟩

/-- The program of steps (5) to (8): `P`, then the output (iii) on tag `0` or the next state on
tag `1`. -/
def alg99Step58Prog (P : Cmd) (B Q : ℕ) : Cmd :=
  .seq P
    (.ite (.reg (Q + 7))
      (alg99Step8Prog B (B + 10) 16 (B - 1) (B - 2) (B - 3) (Q + 10))
      (.seq (alg99OutAProg (B - 3) (B + 2) 16 (B + 6) (B + 7) outArr (Q + 6) (Q + 10))
        (.assign (Q + 5) (.const 0))))

/-- **Steps (5) to (8) of Algorithm (9.9)** (Graph Minors XIII, pages 104–105), on the Word RAM.
Let `st` be a valid state stored at `B`, and let step (4) have left `G' = (G_i \ X) ∪ H_i`, `X`,
a wall `W` of height `h` in `G' \ X` and its compass in arrays `23, 16, B + 5, 33`, with the
facts that `alg99Step4Prog_exec` gives. Then `alg99Step58Prog` ends in one of two ways:
* the flag `Q + 5` is `0` and `outArr` holds `2 :: (bitSetList (orig(X)) ++ p.movedBlock)`, where
  `p` is the parse of the block of an output (a) of steps (5) to (7);
* the flag is unchanged and the next state `st.step8 X V_A Bd W_A` is stored at `B`; it is valid
  and at most half as large. -/
theorem alg99Step58_exec {n h' s₀ pp h ω C C_blk c : ℕ} {h2 : 2 ≤ h} {he : Even h}
    {h2' : 2 ≤ h'} {he' : Even h'} {P : Cmd} {B Q : ℕ}
    (hP : Case3StepsRuns h h' ω h2 he h2' he' C C_blk c 23 16 (B + 5) 33 (B - 1) (B - 2) (B - 3)
      (B - 4) (B + 6) (Q + 7) (Q + 10) P)
    (hB : 40 ≤ B) {G : MultiDigraph n} {st : Alg99Iter h' G} (hst : st.IsValid s₀)
    (hs₀ : s₀ = pp.choose 2 + 5) {X : Finset (Fin st.v)} (hXc : X.card < pp.choose 2)
    {G' : MultiDigraph st.v} (hG' : G' = WallOfHeight.wallUnionMultiDigraph st.Gi X st.H)
    {W : WallOfHeight h (G'.deleteVertices X)} {hW : W.IsValid}
    (hWX : Disjoint W.vertexFinset X) (hflat : W.IsFlatWall h2)
    (hcX : Disjoint W.compassFinset X)
    (hK : W.compassFinset.toNatSet = V(GM13.wallCompass (delGraph G' X) (W.toGMWall h2 he hW)))
    (hKZ : Disjoint W.compassFinset st.Z)
    (h4 : 2 * (GM13.graphSize (GM13.wallCompass (delGraph G' X) (W.toGMWall h2 he hW)) +
        (GM13.crossEdgesToSet st.Gi.toGMDigraph.toGraph
          V(GM13.wallCompass (delGraph G' X) (W.toGMWall h2 he hW)) X.toNatSet).ncard +
        X.toNatSet.ncard) ≤ GM13.graphSize st.Gi.toGMDigraph.toGraph)
    {w : ℕ} (hws : wordSize c ((st.v + 1) * (G'.numEdges + st.v + 1)) ≤ w)
    (hw4 : 4 < 2 ^ w) (hv_w : st.v + 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hm3_w : 2 + 3 * st.Gi.numActivePairs < 2 ^ w) (hE_w : st.Gi.numEdges < 2 ^ w)
    (hh'_w : h' < 2 ^ w) (hc'_w : 3 + 2 * elemWallNumVerts h' < 2 ^ w)
    (hL_w : 3 + elemWallNumVerts h' + (elemWallEdges h').length + st.v < 2 ^ w)
    (hblk_w : n + 1 + C_blk * (st.v + G'.numEdges + 1) < 2 ^ w)
    {s : State} (hS : st.StoredIn B s) (h23 : s.arrs 23 = G'.enc)
    (h16 : s.arrs 16 = bitSetList X) (hB5 : s.arrs (B + 5) = W.encList)
    (h33 : s.arrs 33 = bitSetList W.compassFinset) (hn : s.regs (Q + 6) = n) :
    ∃ s' t, Exec w (alg99Step58Prog P B Q) s s' t ∧
      t ≤ C * (st.v + 1) * (G'.numEdges + st.v + 1) + 131 * (C_blk * (st.v + G'.numEdges + 1)) +
        300 * st.Gi.numActivePairs + 200 * st.v + 16 * n +
        50 * (3 + elemWallNumVerts h' + (elemWallEdges h').length) + 800 ∧
      s'.regs (Q + 6) = n ∧
      ((s'.regs (Q + 5) = 0 ∧ ∃ (s_m : State) (p : ParsedCase3Block (G'.deleteVertices X) X),
          IsCase3StepsOutputA h ω G' X W h2 he hW C_blk w (B - 1) (B - 3) s_m ∧
          parseCase3Block _ X (s_m.arrs (B - 3)) = some p ∧
          s'.arrs outArr = 2 :: (bitSetList (X.image st.orig) ++
            p.movedBlock hst.orig_injective (hG' ▸ hst.edgeMult_wallUnion X))) ∨
        (s'.regs (Q + 5) = s.regs (Q + 5) ∧
          ∃ (V_A Bd : Finset (Fin st.v)) (A_sub : MultiDigraph st.v)
            (W_A : WallOfHeight h' (A_sub.deleteVerticesCompact V_Aᶜ)),
            (st.step8 X V_A Bd W_A).StoredIn B s' ∧ (st.step8 X V_A Bd W_A).IsValid s₀ ∧
            2 * ((st.step8 X V_A Bd W_A).Gi.numEdges + (st.step8 X V_A Bd W_A).v + 1) ≤
              st.Gi.numEdges + st.v + 1)) := by
  subst hG'
  obtain ⟨hS1, hS2, hS3, hS4⟩ := hS
  obtain ⟨s₁, t₁, hex₁, ht₁, harr₁, hreg₁, hcase⟩ :=
    hP w st.v _ X W hW hWX hflat hcX hK hws s h23 h16 hB5 h33
  have hkeep : ∀ a, a < B + 6 → a ≠ B - 1 → a ≠ B - 2 → a ≠ B - 3 → a ≠ B - 4 →
      s₁.arrs a = s.arrs a := harr₁
  have hS₁ : st.StoredIn B s₁ := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (rw [hkeep _ (by romega) (by romega) (by romega) (by romega) (by romega)]; assumption)
  have h16₁ : s₁.arrs 16 = bitSetList X := by
    rw [hkeep _ (by romega) (by romega) (by romega) (by romega) (by romega)]; exact h16
  have hn₁ : s₁.regs (Q + 6) = n := by rw [hreg₁ _ (by romega) (by romega)]; exact hn
  rcases hcase with ⟨htag, hA⟩ | ⟨htag, hBo⟩
  · -- Output (a): write the output (iii) in the labels of `G`.
    obtain ⟨p, hparse, -⟩ := isAlg99Output_of_case3StepsOutputA hst hXc hKZ hK hA
    have hA' := hA
    obtain ⟨K_vList, K_eList, corners, members, -, hwall, hlen, hval, -⟩ := hA'
    have hE' := MultiDigraph.numEdges_deleteVertices_le
      (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X
    have hlenC : (s₁.arrs (B - 3)).length ≤
        C_blk * (st.v + (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).numEdges + 1) := by
      rw [hwall]
      exact hlen.trans (Nat.mul_le_mul_left _ (by omega))
    obtain ⟨s₂, t₂, hex₂, ht₂, hout₂, -, -, hreg₂⟩ :=
      alg99OutAProg_exec hst.orig_injective (hst.edgeMult_wallUnion X) hparse
        (a := B - 3) (o := B + 2) (a_X := 16) (a_mv := B + 6) (a_hd := B + 7) (a_dst := outArr)
        (by romega) (by romega) (by romega) (by romega) (by romega) (by romega) (by romega)
        (by romega) (by romega) (by romega) (r_n := Q + 6) (r := Q + 10) (by romega)
        (s := s₁) rfl hS₁.2.1 h16₁ hn₁ (by rw [hwall]; exact hval) hw4 (by omega)
    let s₃ := s₂.setReg (Q + 5) 0
    have hex₃ : Exec w (.assign (Q + 5) (.const 0)) s₂ s₃ 2 :=
      .assign (by simp [Expr.eval, checkWord, show (0 : ℕ) < 2 ^ w by omega])
    have hcond : (Expr.reg (Q + 7)).eval w s₁ = some 0 := by
      simp [Expr.eval, checkWord, htag, show (0 : ℕ) < 2 ^ w by omega]
    refine ⟨s₃, t₁ + (1 + (t₂ + 2)), .seq hex₁ (.ite_false hcond (.seq hex₂ hex₃)), ?_, ?_,
      Or.inl ⟨by simp [s₃], s₁, p, hA, hparse, by simpa [s₃] using hout₂⟩⟩
    · have := Nat.mul_le_mul_left 131 hlenC
      omega
    · simp only [s₃, State.setReg_regs_ne _ _ (show Q + 6 ≠ Q + 5 by omega)]
      rw [hreg₂ _ (by romega), hn₁]
  · -- Output (b): step (8).
    obtain ⟨V_A, Bd, A_sub, W_A, hVo, hBdo, hWo, -, hval8, hsize⟩ :=
      Alg99Iter.step8_of_outputB hst hs₀ hXc hWX hKZ hK h4 hBo
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hWn, _, _, hw', _⟩ := hBo
    obtain ⟨hWnv, -⟩ := hWn
    have heq := hWo.symm.trans hw'
    have hLlen := Alg91.length_encList_le_of_isValid hWnv
    rw [← heq] at hLlen
    have hLval := all_lt_encList_of_isValid _ hWnv le_rfl hh'_w hc'_w (by omega)
    rw [← heq] at hLval
    obtain ⟨s₂, t₂, hex₂, ht₂, hS₂, -, hreg₂⟩ :=
      alg99Step8Prog_exec X V_A Bd W_A (B := B) (T := B + 10) (a_X := 16) (a_V := B - 1)
        (a_bd := B - 2) (a_wall := B - 3) (R := Q + 10) (by romega) (by romega) (by romega)
        (by romega) (by romega) (by omega) hv_w hn_w hm3_w hE_w (by omega) hLval hS₁ h16₁ hVo
        hBdo hWo
    have hcond : (Expr.reg (Q + 7)).eval w s₁ = some 1 := by
      simp [Expr.eval, checkWord, htag, show (1 : ℕ) < 2 ^ w by omega]
    refine ⟨s₂, t₁ + (1 + t₂), .seq hex₁ (.ite_true hcond (by omega) hex₂), ?_, ?_,
      Or.inr ⟨?_, V_A, Bd, A_sub, W_A, hS₂, hval8, hsize⟩⟩
    · omega
    · rw [hreg₂ _ (by romega), hn₁]
    · rw [hreg₂ _ (by romega), hreg₁ _ (by romega) (by romega)]

/-- The cost of step (4) is linear in `|V(G_i)| + |E(G_i)|`, for fixed `s, h, h', B`. -/
theorem alg99Step4Cost_le (s h h' B : ℕ) : ∃ K, ∀ n m,
    alg99Step4Cost s h h' B n m ≤ K * (n + m + 1) := by
  set a := elemWallNumVerts h
  set b := elemWallNumVerts h'
  set e := (isWallUnionEdgeExpr h' (B + 10) 16 (3 + 6) (3 + 7)).cost
  refine ⟨(s + 1) * (500 + 300 * a + 300 * b + e), fun n m => ?_⟩
  unfold alg99Step4Cost alg99Step4SetupCost alg99Step4CheckCost parseWallCost maxWallEncLen
  nlinarith [Nat.zero_le (a * n), Nat.zero_le (b * n), Nat.zero_le (s * n), Nat.zero_le (s * m),
    Nat.zero_le (s * a * n), Nat.zero_le (e * m), Nat.zero_le (s * e), Nat.zero_le (s * a),
    Nat.zero_le (s * b), Nat.zero_le (s * b * n), Nat.zero_le (s * e * n),
    Nat.zero_le (s * e * m), Nat.zero_le (a * m), Nat.zero_le (b * m), Nat.zero_le (s * a * m),
    Nat.zero_le (s * b * m), Nat.zero_le (e * n)]

end GraphMinor.Compute
