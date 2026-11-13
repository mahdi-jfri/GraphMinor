module

public import GraphMinor.Compute.Algorithm99Step4Loop
public import GraphMinor.Compute.Algorithm99State
public import GraphMinor.Compute.Algorithm33Multigraph
import GraphMinor.Compute.Algorithm77Prog75Full

/-!
# Step (4) of Algorithm (9.9): the program

Step (4) of Algorithm (9.9) (Graph Minors XIII, pages 104–105) reads: "Since $|Z_i| \le s - 3$,
we may choose three of the $H^j$'s, say $H^1$, $H^2$, and $H^3$, such that
$V(K^j) \cap Z_i = \emptyset$ ($1 \le j \le 3$)." After a count it ends: "Choose one of them,
$K^1$ say, so that $\varepsilon(K^1) + d_1 + |X| \le \frac{1}{2}\varepsilon(G_i)$."

The program has two parts.
* The set-up (`alg99Step4Setup`) copies `G_i.enc` and the bit sets of `X` and `Z_i` into the low
  arrays that the programs of (9.4) and (9.7) read, reads `H_i`, writes
  `G' = (G_i \ X) ∪ H_i` (`G'.enc` in array `23`, adjacency lists in arrays `20`–`22`), and
  computes `|E(G_i)|` and `|X|` (`alg99Step4Setup_exec`).
* The scan of `Algorithm99Step4Loop` tests the subwalls in turn.

The test of the program is the inequality of the paper written with the counts of
`Algorithm99Step4Count` (`alg99Step4Pass_iff`). By `alg99_step4_exists` some subwall passes, so
the scan ends with the flag set, the code of a subwall `H^a` that passes in array `B + 5`, and
its compass in array `33` (`alg99Step4Prog_exec`). These arrays, with `G'.enc` in array `23` and
the bit set of `X` in array `16`, are the inputs of `Case3StepsClaim`.
-/

@[expose] public section

namespace GraphMinor.Compute

open WallOfHeight Graph

/-- `omega` after unfolding `Reg` and `Arr`, which `omega` does not see as `ℕ`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr, inArr, outArr] at *); omega))

variable {n h h' s : ℕ}

/-! ### The test is the inequality of the paper -/

/-- The compass of a wall that misses `X` has the same edges in `G'` and in `G_i`. -/
theorem restrictMult_wallUnionMultiDigraph {Gi : MultiDigraph n} {X : Finset (Fin n)}
    (Hi : WallOfHeight h' Gi) (V : Finset (Fin n)) (hVX : Disjoint V X) :
    (wallUnionMultiDigraph Gi X Hi).restrictMult (fun u w => u ∈ V ∧ w ∈ V) =
      Gi.restrictMult (fun u w => u ∈ V ∧ w ∈ V) := by
  ext u w
  simp only [MultiDigraph.restrictMult, wallUnionMultiDigraph_edgeMult]
  by_cases hP : u ∈ V ∧ w ∈ V
  · have hu : u ∉ X := Finset.disjoint_left.mp hVX hP.1
    have hw : w ∉ X := Finset.disjoint_left.mp hVX hP.2
    simp [hP, hu, hw]
  · simp [hP]

/-- **The test of the program is the inequality of step (4)** (Graph Minors XIII, page 105).
For a subwall `H^a` of `H_i` that misses `X` and is dividing in `G'`, the compass `V` of `H^a`
in `G'` passes `Alg99Step4Pass` exactly when `V` misses `Z_i` and
`2 (ε(K^a) + d_a + |X|) ≤ ε(G_i)`, where `K^a` is the compass of `H^a` in `G_i \ X`. -/
theorem alg99Step4Pass_iff {Gi : MultiDigraph n} {Hi : WallOfHeight h' Gi} (hHi : Hi.IsValid)
    (h2' : 2 ≤ h') (he' : Even h') {W₀ : WallOfHeight h Gi} (hW₀ : W₀.IsValid) (h2 : 2 ≤ h)
    (he : Even h) {X Z : Finset (Fin n)} (hdisj : Disjoint W₀.vertexFinset X)
    (hdiv : (Hi.castGraph (wallUnionMultiDigraph Gi X Hi)).IsDividingSubwall
      (W₀.castGraph (wallUnionMultiDigraph Gi X Hi)))
    (hWD : (W₀.castGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).IsValid) :
    Alg99Step4Pass Gi X Z (W₀.castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset ↔
      Disjoint (W₀.castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset Z ∧
      2 * (GM13.graphSize (GM13.wallCompass (delGraph (wallUnionMultiDigraph Gi X Hi) X)
          ((W₀.castGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).toGMWall h2 he hWD)) +
        (GM13.crossEdgesToSet Gi.toGMDigraph.toGraph
          V(GM13.wallCompass (delGraph (wallUnionMultiDigraph Gi X Hi) X)
            ((W₀.castGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).toGMWall
              h2 he hWD))
          X.toNatSet).ncard + X.toNatSet.ncard) ≤
        GM13.graphSize Gi.toGMDigraph.toGraph := by
  set G' := wallUnionMultiDigraph Gi X Hi with hG'
  set V := (W₀.castGraph G').compassFinset with hV
  have hVX : Disjoint V X := disjoint_compassFinset_wallUnion hHi h2' he' hW₀ h2 hdisj hdiv
  have hVK : V.toNatSet = V(GM13.wallCompass (delGraph G' X)
      ((W₀.castGraph (G'.deleteVertices X)).toGMWall h2 he hWD)) := by
    rw [hV, ← compassFinset_castGraph_deleteVertices_wallUnion hHi h2' he' hW₀ h2 hdisj hdiv]
    exact toNatSet_compassFinset_eq_wallCompass_delGraph _ h2 he hWD
      (by rw [castGraph_vertexFinset]; exact hdisj)
  rw [graphSize_wallCompass_delGraph G' X V _ hVK hVX, ← hVK, ncard_crossEdgesToSet Gi X V,
    ncard_toNatSet, graphSize_toGMDigraph, hG', restrictMult_wallUnionMultiDigraph Hi V hVX]
  rfl

/-! ### The set-up -/

private theorem bitSetList_lt {w n : ℕ} (Z : Finset (Fin n)) (hw : 1 < 2 ^ w) :
    ∀ x ∈ bitSetList Z, x < 2 ^ w := by
  intro x hx
  rcases List.mem_iff_getElem.mp hx with ⟨idx, hidx, rfl⟩
  have hle1 := getElem_bitSetList_le_one Z idx hidx
  omega

/-- The set-up of step (4). The state of (9.9) is in arrays `B + 1` (`G_i.enc`), `B + 3`
(`bitSetList Z_i`) and `B + 4` (`H_i.encList`), the output (ii) of (9.7) in `outArr`. The
successor arrays of `H_i` go to arrays `B + 10, B + 11, …`. -/
def alg99Step4Setup (h' : ℕ) (h2' : 2 ≤ h') (B R : ℕ) : Cmd :=
  .seq (copyArrLoopProg (B + 1) 9 (R + 40) (R + 41))
  (.seq (.assign 1 (.read 9 (.const 0)))
  (.seq (readSliceProg outArr (.const 1) 16 (.reg 1) (R + 30))
  (.seq (copyArrLoopProg (B + 3) 17 (R + 40) (R + 41))
  (.seq (.assign (R + 3) (.const 0))
  (.seq (parseFixedWallProg h' h2' true (B + 10) (B + 4) 11 28 (R + 3))
  (.seq (buildWallUnionCsrProg h' (B + 10))
  (.seq (.assign 2 (.len 22))
  (.seq (sumEdgeMultProg 9 (R + 5))
  (.seq (.assign (R + 2) (.reg (R + 7)))
  (.seq (cardBitSetProg 16 (.reg 1) (R + 1) (R + 6))
  (.seq (.assign (R + 3) (.op .add (.const 1) (.reg 1)))
  (.seq (.assign (R + 4) (.const 0))
    (.assign R (.const 0))))))))))))))

/-- The cost of the set-up. -/
def alg99Step4SetupCost (h' B n m' : ℕ) : ℕ :=
  parseWallCost h' n + (358 + (isWallUnionEdgeExpr h' (B + 10) 16 (3 + 6) (3 + 7)).cost) * m' +
    66 * n + 281

/-- **The set-up of step (4) of (9.9)**. From the stored `G_i`, `Z_i`, `H_i` and the output (ii)
of (9.7), the program writes what the scan reads (`Alg99Step4Ctx`), `G'.enc` in array `23`, and
starts the scan: index `0` in register `R`, the start of the code of `H^0` in register `R + 3`,
the flag `0` in register `R + 4`. -/
theorem alg99Step4Setup_exec {w : ℕ} {Gi : MultiDigraph n} {Hi : WallOfHeight h' Gi}
    (hHi : Hi.IsValid) (h2' : 2 ≤ h') {X Z : Finset (Fin n)} {W_flat : Fin s → WallOfHeight h Gi}
    (B R : ℕ) (hB : 40 ≤ B) (hR : 14 < R)
    (hw3 : 3 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w) (hm3_w : 2 + 3 * Gi.numActivePairs < 2 ^ w)
    (hbig : 4 * (Gi.numEdges + n + 1) < 2 ^ w)
    (hc3'_w : 3 + 3 * elemWallNumVerts h' + n < 2 ^ w)
    {st : State} (hG : st.arrs (B + 1) = Gi.enc) (hZ : st.arrs (B + 3) = bitSetList Z)
    (hH : st.arrs (B + 4) = Hi.encList)
    (hout : st.arrs outArr =
      1 :: (bitSetList X ++ (List.finRange s).flatMap (fun b => (W_flat b).encList))) :
    ∃ st' t, Exec w (alg99Step4Setup h' h2' B R) st st' t ∧
      t ≤ alg99Step4SetupCost h' B n Gi.numActivePairs ∧
      Alg99Step4Ctx Gi Hi X Z W_flat R st' ∧
      st'.arrs 23 = (wallUnionMultiDigraph Gi X Hi).enc ∧
      st'.regs R = 0 ∧ st'.regs (R + 3) = (alg97OutPrefix X W_flat 0).length ∧
      st'.regs (R + 4) = 0 ∧
      (st'.arrs 22).length ≤ 2 * Gi.numEdges ∧
      (∀ x : ℕ, x ≠ 0 → x ≠ 9 → x ≠ 11 → x ≠ 16 → x ≠ 17 → x ≠ 20 → x ≠ 21 → x ≠ 22 →
        x ≠ 23 → x ≠ 28 → x ≠ 34 → x ≠ 35 → x < B + 10 → st'.arrs x = st.arrs x) ∧
      (∀ q : ℕ, 14 < q → q < R → st'.regs q = st.regs q) := by
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hm_w : Gi.numEdges < 2 ^ w := by omega
  -- 1. `G_i.enc` into array `9`.
  obtain ⟨s₁, t₁, hex₁, ht₁, h9₁, harr₁, hreg₁⟩ :=
    copyArrLoopProg_exec (B + 1) 9 (R + 40) (R + 41) (by romega) (by romega) hw1 st
      (by rw [hG, MultiDigraph.length_enc]; omega)
      (by rw [hG]; exact mem_enc_lt_two_pow Gi hn_w hm_w)
  rw [hG] at h9₁ ht₁
  -- 2. `n` into register `1`.
  have hsrc9 : s₁.arrs 9 = Gi.enc ++ [] := by rw [h9₁]; simp
  obtain ⟨h0_len, h0_val⟩ := enc_getElem_zero Gi [] hsrc9
  let s₂ := s₁.setReg 1 n
  have hex₂ : Exec w (.assign 1 (.read 9 (.const 0))) s₁ s₂ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w])
  -- 3. The bit set of `X` into array `16`.
  have hout₂ : s₂.arrs outArr = [1] ++ bitSetList X ++
      (List.finRange s).flatMap (fun b => (W_flat b).encList) := by
    change s₁.arrs 1 = _
    rw [harr₁ 1 (by romega), show (1 : ℕ) = outArr from rfl, hout]; simp
  obtain ⟨s₃, t₃, hex₃, ht₃, h16₃, harr₃, hreg₃⟩ :=
    readSliceProg_exec outArr 16 (.const 1) 1 (R + 30) (by romega) (by omega) [1] (bitSetList X)
      _ rfl (length_bitSetList X) (bitSetList_lt X hw1) hw1 (by simp; omega)
      (by simp [Expr.eval, checkWord, hw1]) hout₂ (by simp [s₂])
  -- 4. The bit set of `Z_i` into array `17`.
  have hZ₃ : s₃.arrs (B + 3) = bitSetList Z := by
    rw [harr₃ _ (by omega)]; change s₁.arrs (B + 3) = _; rw [harr₁ _ (by romega)]; exact hZ
  obtain ⟨s₄, t₄, hex₄, ht₄, h17₄, harr₄, hreg₄⟩ :=
    copyArrLoopProg_exec (B + 3) 17 (R + 40) (R + 41) (by romega) (by romega) hw1 s₃
      (by rw [hZ₃, length_bitSetList]; exact hn_w) (by rw [hZ₃]; exact bitSetList_lt Z hw1)
  rw [hZ₃, length_bitSetList] at ht₄
  rw [hZ₃] at h17₄
  -- 5. Read `H_i` and its successor arrays.
  let s₅ := s₄.setReg (R + 3) 0
  have hex₅ : Exec w (.assign (R + 3) (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hH₅ : s₅.arrs (B + 4) = [] ++ Hi.encList ++ [] := by
    change s₄.arrs (B + 4) = _
    rw [harr₄ _ (by romega), harr₃ _ (by omega)]; change s₁.arrs (B + 4) = _
    rw [harr₁ _ (by romega), hH]; simp
  have hr1_5 : s₅.regs 1 = n := by
    simp only [s₅, State.setReg_regs_ne _ _ (show (1 : Reg) ≠ R + 3 by romega)]
    rw [hreg₄ 1 (by romega) (by romega), hreg₃ 1 (by omega)]; simp [s₂]
  have hlenH := Alg91.length_encList_le_of_isValid hHi
  have hE_le : (elemWallEdges h').length ≤ 2 * elemWallNumVerts h' := length_elemWallEdges_le h'
  obtain ⟨s₆, t₆, hex₆, ht₆, -, -, hV₆, -, hsucc₆, harr₆, hreg₆⟩ :=
    parseFixedWallProg_exec h2' le_rfl Hi hHi true (B + 10) (B + 4) 11 28 (R + 3) (by omega)
      (by omega) (by omega) (fun _ k => ⟨by omega, by omega, by omega⟩) (by omega) [] []
      hw1 hn1_w (by omega) (by simp; omega) hH₅ hr1_5 (by simp [s₅])
  have hsucc₆' := hsucc₆ rfl
  have harr₆' : ∀ x : ℕ, x ≠ 11 → x ≠ 28 → x < B + 10 → s₆.arrs x = s₄.arrs x := by
    intro x h11 h28 hx
    rw [harr₆ x h11 h28 (fun _ k => by omega)]; rfl
  -- 6. `G'`.
  have h9₄ : s₄.arrs 9 = Gi.enc := by
    rw [harr₄ _ (by romega), harr₃ _ (by omega)]; change s₁.arrs 9 = _; exact h9₁
  have h16₄ : s₄.arrs 16 = bitSetList X := by rw [harr₄ _ (by romega)]; exact h16₃
  obtain ⟨s₇, t₇, hex₇, ht₇, h23₇, hadj₇, hlen22₇, htot₇, harr₇, hreg₇⟩ :=
    buildWallUnionCsrProg_exec Gi X Hi hHi (B + 10) (by omega) hw3 hn1_w hm3_w hm_w
      ((harr₆' 9 (by omega) (by omega) (by omega)).trans h9₄)
      (IsBitSet.of_bitSetList _ _ _ ((harr₆' 16 (by omega) (by omega) (by omega)).trans h16₄))
      hsucc₆'
  -- 7. The length of array `22` into register `2`.
  have hlen22_w : (s₇.arrs 22).length < 2 ^ w := by
    have h1 := card_edgeFinset_toSimpleGraph_le_numEdges (wallUnionMultiDigraph Gi X Hi)
    have h2 := wallUnionMultiDigraph_numEdges_le Gi X Hi
    rw [length_edgeListOf_eq_card_edgeFinset] at h1
    omega
  let s₈ := s₇.setReg 2 (s₇.arrs 22).length
  have hex₈ : Exec w (.assign 2 (.len 22)) s₇ s₈ 2 :=
    .assign (by simp [checkWord, hlen22_w])
  -- 8. `|E(G_i)|` into register `R + 2`.
  have harr₇' : ∀ x : ℕ, x ≠ 0 → x ≠ 20 → x ≠ 21 → x ≠ 22 → x ≠ 23 → x ≠ 34 → x ≠ 35 →
      x ≠ 11 → x ≠ 28 → x < B + 10 → s₈.arrs x = s₄.arrs x := by
    intro x h0 h20 h21 h22 h23 h34 h35 h11 h28 hx
    change s₇.arrs x = _
    rw [harr₇ x h0 h20 h21 h22 h23 h34 h35, harr₆' x h11 h28 hx]
  obtain ⟨s₉, t₉, hex₉, ht₉, -, -, hm₉, harr₉, hreg₉⟩ :=
    sumEdgeMultProg_exec Gi 9 (R + 5) hw3 hn_w hm3_w hm_w (s := s₈)
      (by rw [harr₇' 9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)]; exact h9₄)
  let s₁₀ := s₉.setReg (R + 2) Gi.numEdges
  have hex₁₀ : Exec w (.assign (R + 2) (.reg (R + 7))) s₉ s₁₀ 2 :=
    .assign (by simp [checkWord, hm₉, hm_w])
  -- 9. `|X|` into register `R + 1`.
  have h16₁₀ : s₁₀.arrs 16 = bitSetList X := by
    change s₉.arrs 16 = _
    rw [harr₉, harr₇' 16 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)]; exact h16₄
  have hr1_8 : s₈.regs 1 = n := by
    simp only [s₈, State.setReg_regs_ne _ _ (show (1 : Reg) ≠ 2 by romega)]
    rw [hreg₇ 1 (by omega), hreg₆ 1 (by omega) (by omega) (by romega)]; exact hr1_5
  have hr1_10 : s₁₀.regs 1 = n := by
    simp only [s₁₀, State.setReg_regs_ne _ _ (show (1 : Reg) ≠ R + 2 by romega)]
    rw [hreg₉ 1 (by omega)]; exact hr1_8
  obtain ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hX₁₁, harr₁₁, hreg₁₁⟩ :=
    cardBitSetProg_exec X 16 1 (R + 1) (R + 6) (by omega) (by omega) (by omega) hw1 hn_w
      (IsBitSet.of_bitSetList _ _ _ h16₁₀) hr1_10
  -- 10. Start the scan.
  have hr1_11 : s₁₁.regs 1 = n := by rw [hreg₁₁ 1 (by omega) (by omega)]; exact hr1_10
  let s₁₂ := s₁₁.setReg (R + 3) (1 + n)
  have hex₁₂ : Exec w (.assign (R + 3) (.op .add (.const 1) (.reg 1))) s₁₁ s₁₂ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1_11, hw1, hn_w,
      show 1 + n < 2 ^ w by omega])
  let s₁₃ := s₁₂.setReg (R + 4) 0
  have hex₁₃ : Exec w (.assign (R + 4) (.const 0)) s₁₂ s₁₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₁₄ := s₁₃.setReg R 0
  have hex₁₄ : Exec w (.assign R (.const 0)) s₁₃ s₁₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- The arrays at the end.
  have harr_end : ∀ x : ℕ, s₁₄.arrs x = s₇.arrs x := fun x => by
    change s₁₁.arrs x = _
    rw [harr₁₁ x]; change s₉.arrs x = _; rw [harr₉ x]; rfl
  have harr_end₄ : ∀ x : ℕ, x ≠ 0 → x ≠ 20 → x ≠ 21 → x ≠ 22 → x ≠ 23 → x ≠ 34 → x ≠ 35 →
      x ≠ 11 → x ≠ 28 → x < B + 10 → s₁₄.arrs x = s₄.arrs x := by
    intro x h0 h20 h21 h22 h23 h34 h35 h11 h28 hx
    rw [harr_end x, harr₇ x h0 h20 h21 h22 h23 h34 h35, harr₆' x h11 h28 hx]
  have harr₄st : ∀ x : ℕ, x ≠ 9 → x ≠ 16 → x ≠ 17 → s₄.arrs x = st.arrs x := by
    intro x h9 h16 h17
    rw [harr₄ x (by romega), harr₃ x h16]; change s₁.arrs x = _; rw [harr₁ x (by romega)]
  have h11_end : s₁₄.arrs 11 = bitSetList Hi.vertexFinset := by
    rw [harr_end, harr₇ 11 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]
    exact hV₆.arr_eq_bitSetList
  have hlen22 : (s₁₄.arrs 22).length =
      2 * (wallUnionMultiDigraph Gi X Hi).toSimpleGraph.edgeFinset.card := by
    rw [harr_end]; exact hlen22₇
  -- The registers at the end.
  have hreg_end : ∀ q : ℕ, q ≠ R → q ≠ R + 1 → q ≠ R + 3 → q ≠ R + 4 → q ≠ R + 6 →
      s₁₄.regs q = s₁₀.regs q := by
    intro q h0 h1 h3 h4 h6
    simp only [s₁₄, s₁₃, s₁₂, State.setReg_regs_ne _ _ (show (q : Reg) ≠ R from h0),
      State.setReg_regs_ne _ _ (show (q : Reg) ≠ R + 4 from h4),
      State.setReg_regs_ne _ _ (show (q : Reg) ≠ R + 3 from h3)]
    exact hreg₁₁ q h1 h6
  have hreg₈₄ : ∀ q : ℕ, 14 < q → q < R + 5 → q ≠ R + 3 → s₈.regs q = s₄.regs q := by
    intro q hq hqR h3
    simp only [s₈, State.setReg_regs_ne _ _ (show (q : Reg) ≠ 2 by romega)]
    rw [hreg₇ q (by omega), hreg₆ q (by omega) (by omega) h3]
    simp only [s₅, State.setReg_regs_ne _ _ (show (q : Reg) ≠ R + 3 from h3)]
  have hreg₄st : ∀ q : ℕ, 14 < q → q < R + 30 → q ≠ R + 40 → q ≠ R + 41 →
      s₄.regs q = st.regs q := by
    intro q hq hqR h40 h41
    rw [hreg₄ q (by romega) (by romega), hreg₃ q hqR]
    simp only [s₂, State.setReg_regs_ne _ _ (show (q : Reg) ≠ 1 by romega)]
    exact hreg₁ q (by romega) (by romega)
  have hr2_end : s₁₄.regs 2 = (s₁₄.arrs 22).length := by
    rw [hreg_end 2 (by omega) (by omega) (by omega) (by omega) (by omega), harr_end]
    simp only [s₁₀, State.setReg_regs_ne _ _ (show (2 : Reg) ≠ R + 2 by romega)]
    rw [hreg₉ 2 (by omega)]; simp [s₈]
  have hc_end : Alg99Step4Ctx Gi Hi X Z W_flat R s₁₄ := by
    refine ⟨?_, ?_, ?_, ?_, h11_end, ?_, ?_, ?_, hr2_end, ?_, ?_⟩
    · rw [show outArr = (1 : ℕ) from rfl, harr_end₄ 1 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        harr₄st 1 (by omega) (by omega) (by omega)]
      exact hout
    · rw [harr_end₄ 9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)]; exact h9₄
    · rw [harr_end₄ 16 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)]; exact h16₄
    · rw [harr_end₄ 17 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)]; exact h17₄
    · exact hadj₇.of_arrs_eq (harr_end 20) (harr_end 21) (harr_end 22)
    · rw [hlen22, htot₇]
    · rw [hreg_end 1 (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp only [s₁₀, State.setReg_regs_ne _ _ (show (1 : Reg) ≠ R + 2 by romega)]
      rw [hreg₉ 1 (by omega)]; exact hr1_8
    · simp only [s₁₄, s₁₃, s₁₂, State.setReg_regs_ne _ _ (show (R + 1 : Reg) ≠ R by romega),
        State.setReg_regs_ne _ _ (show (R + 1 : Reg) ≠ R + 4 by romega),
        State.setReg_regs_ne _ _ (show (R + 1 : Reg) ≠ R + 3 by romega)]
      exact hX₁₁
    · rw [hreg_end (R + 2) (by omega) (by omega) (by omega) (by omega) (by omega)]; simp [s₁₀]
  refine ⟨s₁₄, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇
    (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂ (.seq hex₁₃ hex₁₄)))))))))))),
    ?_, hc_end, ?_, by simp [s₁₄], ?_, ?_, ?_, ?_, ?_⟩
  · rw [MultiDigraph.length_enc] at ht₁
    simp only [Expr.cost] at ht₃
    have hring : (358 + (isWallUnionEdgeExpr h' (B + 10) 16 (3 + 6) (3 + 7)).cost) *
        Gi.numActivePairs = (291 + (isWallUnionEdgeExpr h' (B + 10) 16 (3 + 6) (3 + 7)).cost) *
        Gi.numActivePairs + 67 * Gi.numActivePairs := by ring
    unfold alg99Step4SetupCost
    omega
  · rw [harr_end]; exact h23₇
  · simp only [s₁₄, s₁₃, State.setReg_regs_ne _ _ (show (R + 3 : Reg) ≠ R by romega),
      State.setReg_regs_ne _ _ (show (R + 3 : Reg) ≠ R + 4 by romega)]
    rw [length_alg97OutPrefix_zero]; simp [s₁₂]
  · simp [s₁₄, s₁₃]
  · rw [hlen22]
    have h1 := card_edgeFinset_toSimpleGraph_le_numEdges (wallUnionMultiDigraph Gi X Hi)
    have h2 := wallUnionMultiDigraph_numEdges_le Gi X Hi
    rw [length_edgeListOf_eq_card_edgeFinset] at h1
    omega
  · intro x h0 h9 h11 h16 h17 h20 h21 h22 h23 h28 h34 h35 hx
    rw [harr_end₄ x h0 h20 h21 h22 h23 h34 h35 h11 h28 hx, harr₄st x h9 h16 h17]
  · intro q hq hqR
    rw [hreg_end q (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp only [s₁₀, State.setReg_regs_ne _ _ (show (q : Reg) ≠ R + 2 by romega)]
    rw [hreg₉ q (by omega), hreg₈₄ q hq (by omega) (by omega),
      hreg₄st q hq (by omega) (by omega) (by omega)]

/-! ### The program of step (4) -/

/-- The program of step (4) of (9.9): the set-up, then the scan of the `s` subwalls. The code of
the chosen subwall goes to array `B + 5`. -/
def alg99Step4Prog (h : ℕ) (h2 : 2 ≤ h) (h' : ℕ) (h2' : 2 ≤ h') (B R s : ℕ) : Cmd :=
  .seq (alg99Step4Setup h' h2' B R) (alg99Step4Loop h h2 (B + 5) R s)

/-- The cost of step (4) for `G_i` with `n` vertices and `m` edges. -/
def alg99Step4Cost (s h h' B n m : ℕ) : ℕ :=
  alg99Step4SetupCost h' B n m + 3 +
    s * (parseWallCost h n + alg99Step4CheckCost h' n (2 * m) m + 17)

/-- **Step (4) of Algorithm (9.9)** (Graph Minors XIII, pages 104–105), the program. Let the
state of (9.9) be stored in arrays `B + 1`, `B + 3`, `B + 4` (`G_i`, `Z_i`, `H_i`), and let
`outArr` hold the output (ii) of (9.7): `X` with `|X| < C(p, 2)` and the subwalls
`H^1, …, H^s` (`s = C(p, 2) + 5`), pairwise disjoint, missing `X`, flat and dividing in
`G' = (G_i \ X) ∪ H_i`. Let `|Z_i| ≤ C(p, 2) + 2`. Then the program chooses `a` such that the
compass `K^a` of `H^a` misses `Z_i` and `2 (ε(K^a) + d_a + |X|) ≤ ε(G_i)`, and ends with the
inputs of `Case3StepsClaim` for the wall `H^a` of `G' \ X`: `G'.enc` in array `23`, the bit set
of `X` in array `16`, the code of `H^a` in array `B + 5`, the bit set of its compass in array
`33`. The wall meets every hypothesis of `Case3StepsClaim` on its wall. -/
theorem alg99Step4Prog_exec {w p : ℕ} {Gi : MultiDigraph n} {Hi : WallOfHeight h' Gi}
    (hHi : Hi.IsValid) (h2' : 2 ≤ h') (he' : Even h') (h2 : 2 ≤ h) (he : Even h)
    {X Z : Finset (Fin n)} (hX : X.card < p.choose 2) (hZ : Z.card ≤ p.choose 2 + 2)
    (W_flat : Fin (p.choose 2 + 5) → WallOfHeight h Gi) (hsub : ∀ a, (W_flat a).IsSubwallOf Hi)
    (hpair : Pairwise fun a b => Disjoint (W_flat a).vertexFinset (W_flat b).vertexFinset)
    (hdisj : ∀ a, Disjoint (W_flat a).vertexFinset X)
    (hflat : ∀ a, ((W_flat a).castGraph (wallUnionMultiDigraph Gi X Hi)).IsFlatWall h2)
    (hdiv : ∀ a, (Hi.castGraph (wallUnionMultiDigraph Gi X Hi)).IsDividingSubwall
      ((W_flat a).castGraph (wallUnionMultiDigraph Gi X Hi)))
    (B R : ℕ) (hB : 40 ≤ B) (hR : 14 < R)
    (hw3 : 3 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w) (hm3_w : 2 + 3 * Gi.numActivePairs < 2 ^ w)
    (hbig : 4 * (Gi.numEdges + n + 1) < 2 ^ w) (hs_w : p.choose 2 + 5 < 2 ^ w)
    (hh_w : h < 2 ^ w) (hc2_w : 3 + 2 * elemWallNumVerts h < 2 ^ w)
    (hc3'_w : 3 + 3 * elemWallNumVerts h' + n < 2 ^ w)
    {st : State} (hG : st.arrs (B + 1) = Gi.enc) (hZst : st.arrs (B + 3) = bitSetList Z)
    (hH : st.arrs (B + 4) = Hi.encList)
    (hout : st.arrs outArr = 1 :: (bitSetList X ++
      (List.finRange (p.choose 2 + 5)).flatMap (fun b => (W_flat b).encList)))
    (hout_w : (st.arrs outArr).length < 2 ^ w) :
    ∃ st' t, Exec w (alg99Step4Prog h h2 h' h2' B R (p.choose 2 + 5)) st st' t ∧
      t ≤ alg99Step4Cost (p.choose 2 + 5) h h' B n Gi.numEdges ∧
      st'.arrs 23 = (wallUnionMultiDigraph Gi X Hi).enc ∧ st'.arrs 16 = bitSetList X ∧
      (∃ a, ∃ hW : ((W_flat a).castGraph
          ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).IsValid,
        st'.arrs (B + 5) =
          ((W_flat a).castGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).encList ∧
        st'.arrs 33 = bitSetList
          ((W_flat a).castGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).compassFinset ∧
        Disjoint ((W_flat a).castGraph
          ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).vertexFinset X ∧
        ((W_flat a).castGraph ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).IsFlatWall h2 ∧
        Disjoint ((W_flat a).castGraph
          ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).compassFinset X ∧
        ((W_flat a).castGraph
            ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).compassFinset.toNatSet =
          V(GM13.wallCompass (delGraph (wallUnionMultiDigraph Gi X Hi) X)
            (((W_flat a).castGraph
              ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).toGMWall h2 he hW)) ∧
        Disjoint ((W_flat a).castGraph
          ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).compassFinset Z ∧
        2 * (GM13.graphSize (GM13.wallCompass (delGraph (wallUnionMultiDigraph Gi X Hi) X)
            (((W_flat a).castGraph
              ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).toGMWall h2 he hW)) +
          (GM13.crossEdgesToSet Gi.toGMDigraph.toGraph
            V(GM13.wallCompass (delGraph (wallUnionMultiDigraph Gi X Hi) X)
              (((W_flat a).castGraph
                ((wallUnionMultiDigraph Gi X Hi).deleteVertices X)).toGMWall h2 he hW))
            X.toNatSet).ncard + X.toNatSet.ncard) ≤
          GM13.graphSize Gi.toGMDigraph.toGraph) ∧
      (∀ x : ℕ, x ≠ 0 → x ≠ 9 → x ≠ 11 → x ≠ 16 → x ≠ 17 → (x < 20 ∨ 38 < x) → x ≠ B + 5 →
        x < B + 10 → st'.arrs x = st.arrs x) ∧
      (∀ q : ℕ, 14 < q → q < R → st'.regs q = st.regs q) := by
  set G' := wallUnionMultiDigraph Gi X Hi with hG'
  have hW : ∀ a, (W_flat a).IsValid := fun a => Hi.isValid_of_isSubwallOf hHi (hsub a)
  have hVX : ∀ a, Disjoint ((W_flat a).castGraph G').compassFinset X := fun a =>
    disjoint_compassFinset_wallUnion hHi h2' he' (hW a) h2 (hdisj a) (hdiv a)
  -- The set-up.
  obtain ⟨s₁, t₁, hex₁, ht₁, hc₁, h23₁, hR₁, hpos₁, hflag₁, hlen22₁, harr₁, hreg₁⟩ :=
    alg99Step4Setup_exec (W_flat := W_flat) hHi h2' B R hB hR hw3 hn1_w hm3_w hbig hc3'_w hG hZst
      hH hout
  have hout₁ : s₁.arrs outArr = st.arrs outArr :=
    harr₁ 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  -- The scan.
  obtain ⟨s₂, t₂, hex₂, ht₂, hc₂, hfound, harr₂, hreg₂⟩ :=
    alg99Step4Loop_exec hHi h2' he' h2 hsub hVX (B + 5) R (by omega) hR hw3 hn1_w hm3_w hbig hs_w
      hh_w hc2_w hc₁ (by omega) (by rw [hout₁]; exact hout_w) hR₁ hpos₁ hflag₁
  -- A subwall passed.
  have hpass_of : ∀ a, ∀ hWD : ((W_flat a).castGraph (G'.deleteVertices X)).IsValid,
      Alg99Step4Pass Gi X Z ((W_flat a).castGraph G').compassFinset ↔ _ := fun a hWD =>
    alg99Step4Pass_iff (Z := Z) hHi h2' he' (hW a) h2 he (hdisj a) (hdiv a) hWD
  obtain ⟨b, hb_pass, hb_W, hb_33⟩ : ∃ b : Fin (p.choose 2 + 5),
      Alg99Step4Pass Gi X Z ((W_flat b).castGraph G').compassFinset ∧
      s₂.arrs (B + 5) = (W_flat b).encList ∧
      s₂.arrs 33 = bitSetList ((W_flat b).castGraph G').compassFinset := by
    rcases hfound with ⟨-, hnone⟩ | ⟨-, b, -, hpass, hWb, h33⟩
    · exfalso
      obtain ⟨a, hWa, hZa, -, hineq⟩ :=
        alg99_step4_exists hHi h2' he' h2 he hX hZ W_flat hsub hpair hdisj hdiv
      exact hnone a a.2 ((hpass_of a hWa).2 ⟨hZa, hineq⟩)
    · exact ⟨b, hpass, hWb, h33⟩
  obtain ⟨hWD, hd1, hfl, hd2, hnat, hcomp_eq⟩ :=
    handoff_case3StepsClaim_input hHi h2' he' (hW b) h2 he (hdisj b) (hdiv b) (hflat b)
  obtain ⟨hbZ, hb_ineq⟩ := (hpass_of b hWD).1 hb_pass
  have hm' : Gi.numActivePairs ≤ Gi.numEdges := Alg91.numActivePairs_le_numEdges Gi
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, ?_, ?_,
    ⟨b, hWD, by rw [castGraph_encList]; exact hb_W, by rw [hcomp_eq]; exact hb_33, hd1, hfl, hd2,
      hnat, by rw [hcomp_eq]; exact hbZ, hb_ineq⟩, ?_, ?_⟩
  · have hset : alg99Step4SetupCost h' B n Gi.numActivePairs ≤
        alg99Step4SetupCost h' B n Gi.numEdges := by
      unfold alg99Step4SetupCost
      have := Nat.mul_le_mul_left
        (358 + (isWallUnionEdgeExpr h' (B + 10) 16 (3 + 6) (3 + 7)).cost) hm'
      omega
    have hloop : (p.choose 2 + 5) * (parseWallCost h n +
        alg99Step4CheckCost h' n (s₁.arrs 22).length Gi.numActivePairs + 17) ≤
        (p.choose 2 + 5) * (parseWallCost h n +
        alg99Step4CheckCost h' n (2 * Gi.numEdges) Gi.numEdges + 17) := by
      apply Nat.mul_le_mul_left
      unfold alg99Step4CheckCost
      omega
    unfold alg99Step4Cost
    omega
  · rw [harr₂ 23 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)]
    exact h23₁
  · rw [harr₂ 16 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)]
    exact hc₁.2.2.1
  · intro x h0 h9 h11 h16 h17 hx hB5 hxB
    rw [harr₂ x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hB5]
    exact harr₁ x h0 h9 h11 h16 h17 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hxB
  · intro q hq hqR
    rw [hreg₂ q (by omega) hqR, hreg₁ q hq hqR]

end GraphMinor.Compute
