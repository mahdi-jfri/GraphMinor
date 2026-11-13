module

public import GraphMinor.Compute.Algorithm99Step4Scan
public import GraphMinor.Compute.Algorithm99Step3Read
public import GraphMinor.Compute.Algorithm94Aux
public import GraphMinor.Compute.Algorithm94Scan
public import GraphMinor.Compute.Algorithm97ScanAux

/-!
# Step (4) of Algorithm (9.9): testing one subwall

Step (4) of Algorithm (9.9) (Graph Minors XIII, pages 104–105) chooses a subwall `H^a` whose
compass `K^a` misses `Z_i` and satisfies `ε(K^a) + d_a + |X| ≤ ε(G_i) / 2`. The program tests
the subwalls `H^0, H^1, …` in turn and keeps the first one that passes. This file gives one test.

The test of `H^a` reads its code from the output of (9.7) (`alg99ReadSubwall_exec`), computes
its compass in `G' = (G_i \ X) ∪ H_i` (`testDividingAndCompassWall_exec`, bit set in array `33`),
counts the edges of `G_i` inside the compass and between the compass and `X`
(`step4CountProg_exec`), counts the compass, and tests that the compass misses `Z_i`
(`testDisjointInstProg_exec`, on a copy in array `27`). If the numbers pass, it sets the flag
in register `R + 4` and copies the code of `H^a` into `a_W`. Once the flag is set, a test only
reads the code of the next subwall, so the compass in array `33` and the code in `a_W` stay
those of the first subwall that passed (`alg99Step4Iter_exec`).

The arrays and registers that the tests read are listed in `Alg99Step4Ctx`.
-/

@[expose] public section

namespace GraphMinor.Compute

open WallOfHeight

/-- `omega` after unfolding `Reg` and `Arr`, which `omega` does not see as `ℕ`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr, inArr, outArr] at *); omega))

variable {n h h' s : ℕ}

/-- The test of step (4) of (9.9) for a compass with vertex set `V`: `V` misses `Z_i`, and
`2 (ε(K) + d + |X|) ≤ ε(G_i)` with `ε(K) = |E(K)| + |V| + 1`, `|E(K)|` the number of edges of
`G_i` with both ends in `V` and `d` the number of edges of `G_i` with one end in `V` and the other
in `X`. -/
def Alg99Step4Pass (Gi : MultiDigraph n) (X Z V : Finset (Fin n)) : Prop :=
  Disjoint V Z ∧
  2 * ((Gi.restrictMult (fun u w => u ∈ V ∧ w ∈ V)).numEdges + V.card + 1 +
      (Gi.restrictMult (fun u w => (u ∈ V ∧ w ∈ X) ∨ (u ∈ X ∧ w ∈ V))).numEdges + X.card) ≤
    Gi.numEdges + n + 1

/-- What the tests of step (4) read: the output (ii) of (9.7) in `outArr`, `G_i.enc` in array
`9`, the bit sets of `X`, `Z_i` and `V(H_i)` in arrays `16`, `17`, `11`, the adjacency lists of
`G' = (G_i \ X) ∪ H_i` in arrays `20`–`22`, `n` and the length of array `22` in registers `1`
and `2`, `|X|` and `|E(G_i)|` in registers `R + 1` and `R + 2`. -/
def Alg99Step4Ctx (Gi : MultiDigraph n) (Hi : WallOfHeight h' Gi) (X Z : Finset (Fin n))
    (W_flat : Fin s → WallOfHeight h Gi) (R : ℕ) (st : State) : Prop :=
  st.arrs outArr =
      1 :: (bitSetList X ++ (List.finRange s).flatMap (fun b => (W_flat b).encList)) ∧
    st.arrs 9 = Gi.enc ∧ st.arrs 16 = bitSetList X ∧ st.arrs 17 = bitSetList Z ∧
    st.arrs 11 = bitSetList Hi.vertexFinset ∧
    IsAdjList (wallUnionMultiDigraph Gi X Hi).toSimpleGraph 20 21 22
      (edgeNeighbors (edgeListOf (wallUnionMultiDigraph Gi X Hi).toSimpleGraph)) st ∧
    (st.arrs 22).length =
      totalAdjEntries (edgeNeighbors (edgeListOf (wallUnionMultiDigraph Gi X Hi).toSimpleGraph)) ∧
    st.regs 1 = n ∧ st.regs 2 = (st.arrs 22).length ∧ st.regs (R + 1) = X.card ∧
    st.regs (R + 2) = Gi.numEdges

theorem Alg99Step4Ctx.of_eq {Gi : MultiDigraph n} {Hi : WallOfHeight h' Gi}
    {X Z : Finset (Fin n)} {W_flat : Fin s → WallOfHeight h Gi} {R : ℕ} {st st' : State}
    (hc : Alg99Step4Ctx Gi Hi X Z W_flat R st)
    (harr : ∀ a : ℕ, a = 1 ∨ a = 9 ∨ a = 11 ∨ a = 16 ∨ a = 17 ∨ a = 20 ∨ a = 21 ∨ a = 22 →
      st'.arrs a = st.arrs a)
    (hreg : ∀ q : ℕ, q = 1 ∨ q = 2 ∨ q = R + 1 ∨ q = R + 2 → st'.regs q = st.regs q) :
    Alg99Step4Ctx Gi Hi X Z W_flat R st' := by
  obtain ⟨h1, h9, h16, h17, h11, hadj, hlen, hr1, hr2, hrX, hrE⟩ := hc
  refine ⟨?_, ?_, ?_, ?_, ?_, hadj.of_arrs_eq (harr 20 (by omega)) (harr 21 (by omega))
    (harr 22 (by omega)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [show outArr = (1 : ℕ) from rfl, harr 1 (by omega)]; exact h1
  · rw [harr 9 (by omega)]; exact h9
  · rw [harr 16 (by omega)]; exact h16
  · rw [harr 17 (by omega)]; exact h17
  · rw [harr 11 (by omega)]; exact h11
  · rw [harr 22 (by omega)]; exact hlen
  · rw [hreg 1 (by omega)]; exact hr1
  · rw [hreg 2 (by omega), harr 22 (by omega)]; exact hr2
  · rw [hreg (R + 1) (by omega)]; exact hrX
  · rw [hreg (R + 2) (by omega)]; exact hrE

/-- The test expression: register `10` holds the disjointness bit, and the counts are in
registers `R + 18` (edges inside), `R + 6` (vertices), `R + 19` (edges to `X`), `R + 1` (`|X|`),
`R + 2` (`|E(G_i)|`) and `1` (`n`). -/
def alg99Step4Test (R : ℕ) : Expr :=
  .op .mul (.reg 10) (.op .le
    (.op .mul (.const 2) (.op .add (.op .add (.op .add (.op .add (.reg (R + 18)) (.reg (R + 6)))
      (.const 1)) (.reg (R + 19))) (.reg (R + 1))))
    (.op .add (.op .add (.reg (R + 2)) (.reg 1)) (.const 1)))

/-- A subwall passed: set the flag and copy its code, which lies in `outArr` from the position in
register `R + 5` to the position in register `R + 3`, into `a_W`. -/
def alg99Step4Found (a_W : Arr) (R : ℕ) : Cmd :=
  .seq (.assign (R + 4) (.const 1))
    (.seq (.assign (R + 8) (.op .sub (.reg (R + 3)) (.reg (R + 5))))
      (readSliceProg outArr (.reg (R + 5)) a_W (.reg (R + 8)) (R + 30)))

/-- The test of one subwall whose vertex set, perimeter and seed are in arrays `27`, `28` and
register `14`. -/
def alg99Step4Check (a_W : Arr) (R : ℕ) : Cmd :=
  .seq testDividingAndCompassProg
    (.seq (step4CountProg 9 33 16 (R + 10))
      (.seq (cardBitSetProg 33 (.reg 1) (R + 6) (R + 7))
        (.seq (copyArrLoopProg 33 27 (R + 40) (R + 41))
          (.seq testDisjointInstProg
            (.ite (alg99Step4Test R) (alg99Step4Found a_W R) .skip)))))

/-- One step of the scan of step (4): read the code of the next subwall, and test it if no
subwall has passed yet (flag in register `R + 4`). -/
def alg99Step4Iter (h : ℕ) (h2 : 2 ≤ h) (a_W : Arr) (R : ℕ) : Cmd :=
  .seq (.assign (R + 5) (.reg (R + 3)))
    (.seq (parseFixedWallProg h h2 false 0 outArr 27 28 (R + 3))
      (.ite (.op .eq (.reg (R + 4)) (.const 0)) (alg99Step4Check a_W R) .skip))

/-- The cost of one test. `E₂` is the length of array `22` (twice the number of edges of the
simple graph of `G'`) and `m'` the number of triples of `G_i`. -/
def alg99Step4CheckCost (h n E₂ m' : ℕ) : ℕ :=
  52 * E₂ + 60 * m' + 16 * maxWallEncLen h n + 200 * n + 200

/-- **The test of one subwall in step (4) of (9.9)** (Graph Minors XIII, page 105). With the
vertex set and the perimeter of `H^a` in arrays `27`, `28`, its seed in register `14`, and its
code between the positions in registers `R + 5` and `R + 3` of `outArr`, the program computes
the compass `V` of `H^a` in `G'` into array `33`. If `V` passes the test of step (4), it sets
the flag in register `R + 4` and copies the code of `H^a` into `a_W`; otherwise the flag stays
`0`. -/
theorem alg99Step4Check_exec {w : ℕ} {Gi : MultiDigraph n} {Hi : WallOfHeight h' Gi}
    (hHi : Hi.IsValid) (h2' : 2 ≤ h') (he' : Even h') (h2 : 2 ≤ h)
    {X Z : Finset (Fin n)} {W_flat : Fin s → WallOfHeight h Gi}
    (hsub : ∀ a, (W_flat a).IsSubwallOf Hi) (a : Fin s)
    (hVX : Disjoint ((W_flat a).castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset X)
    (a_W R : ℕ) (ha_W : 38 < a_W) (hR : 14 < R)
    (hw3 : 3 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w) (hm3_w : 2 + 3 * Gi.numActivePairs < 2 ^ w)
    (hbig : 4 * (Gi.numEdges + n + 1) < 2 ^ w)
    (hh_w : h < 2 ^ w) (hc2_w : 3 + 2 * elemWallNumVerts h < 2 ^ w)
    {st : State} (hc : Alg99Step4Ctx Gi Hi X Z W_flat R st)
    (hcap_w : (st.arrs 22).length < 2 ^ w) (hout_w : (st.arrs outArr).length < 2 ^ w)
    (h27 : IsBitSet (W_flat a).vertexFinset 27 st)
    (h28 : IsBitSet (W_flat a).perimeterFinset 28 st)
    (h14 : st.regs 14 = ((W_flat a).seedVert h2).1)
    (hpos : st.regs (R + 5) = (alg97OutPrefix X W_flat a.1).length)
    (hpos' : st.regs (R + 3) = (alg97OutPrefix X W_flat (a.1 + 1)).length)
    (hflag : st.regs (R + 4) = 0) :
    ∃ st' t, Exec w (alg99Step4Check a_W R) st st' t ∧
      t ≤ alg99Step4CheckCost h' n (st.arrs 22).length Gi.numActivePairs ∧
      Alg99Step4Ctx Gi Hi X Z W_flat R st' ∧
      (Alg99Step4Pass Gi X Z ((W_flat a).castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset →
        st'.regs (R + 4) = 1 ∧ st'.arrs a_W = (W_flat a).encList ∧
        st'.arrs 33 =
          bitSetList ((W_flat a).castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset) ∧
      (¬ Alg99Step4Pass Gi X Z
          ((W_flat a).castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset →
        st'.regs (R + 4) = 0) ∧
      (∀ x : ℕ, x ≠ 27 → x ≠ 29 → x ≠ 31 → x ≠ 32 → x ≠ 33 → x ≠ 36 → x ≠ 37 → x ≠ 38 →
        x ≠ a_W → st'.arrs x = st.arrs x) ∧
      (∀ q : ℕ, (q < 3 ∨ 10 < q) → q < R + 4 → st'.regs q = st.regs q) := by
  set G' := wallUnionMultiDigraph Gi X Hi with hG'
  set V := ((W_flat a).castGraph G').compassFinset with hV
  obtain ⟨h1, h9, h16, h17, h11, hadj, hlen22, hr1, hr2, hrX, hrE⟩ := hc
  have hc : Alg99Step4Ctx Gi Hi X Z W_flat R st :=
    ⟨h1, h9, h16, h17, h11, hadj, hlen22, hr1, hr2, hrX, hrE⟩
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hm_w : Gi.numEdges < 2 ^ w := by omega
  have hHi' : (Hi.castGraph G').IsValid := isValid_castGraph_wallUnionMultiDigraph X hHi
  have hsub' : ((W_flat a).castGraph G').IsSubwallOf (Hi.castGraph G') :=
    isSubwallOf_castGraph (hsub a)
  -- 1. The compass of `H^a` in `G'`.
  have hHV : IsBitSet (Hi.castGraph G').vertexFinset 11 st := by
    rw [castGraph_vertexFinset]; exact IsBitSet.of_bitSetList _ _ _ h11
  have hHjV : IsBitSet ((W_flat a).castGraph G').vertexFinset 27 st := by
    rw [castGraph_vertexFinset]; exact h27
  have hperim : IsBitSet ((W_flat a).castGraph G').perimeterFinset 28 st := by
    rw [castGraph_perimeterFinset]; exact h28
  obtain ⟨s₁, t₁, hex₁, ht₁, hV₁, -, harr₁, hreg₁⟩ :=
    testDividingAndCompassWall_exec G' _ (Hi.castGraph G') ((W_flat a).castGraph G') h2' he' hHi'
      hsub' (st.arrs 22).length hw2 hn_w hcap_w (le_of_eq hlen22.symm) hadj hcap_w hHV hHjV hperim
      hr1 hr2 h14
  have harr₁' : ∀ x : ℕ, x ≠ 29 → x ≠ 31 → x ≠ 32 → x ≠ 33 → x ≠ 36 → x ≠ 37 → x ≠ 38 →
      s₁.arrs x = st.arrs x := fun x a b c d e f g => harr₁ x a b c d e f g
  -- 2. The two counts.
  obtain ⟨s₂, t₂, hex₂, ht₂, hin₂, hcr₂, harr₂, hreg₂⟩ :=
    step4CountProg_exec Gi V X hVX 9 33 16 (R + 10) hw3 hn_w hm3_w hm_w
      (by rw [harr₁' 9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)]; exact h9) hV₁
      (IsBitSet.of_bitSetList _ _ _ (by rw [harr₁' 16 (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)]; exact h16))
  -- 3. `|V|`.
  have hr1_2 : s₂.regs 1 = n := by
    rw [hreg₂ 1 (by omega), hreg₁ 1 (by omega)]; exact hr1
  obtain ⟨s₃, t₃, hex₃, ht₃, hcard₃, harr₃, hreg₃⟩ :=
    cardBitSetProg_exec V 33 1 (R + 6) (R + 7) (by omega) (by omega) (by omega) hw1 hn_w
      (hV₁.of_arr_eq (harr₂ 33)) hr1_2
  -- 4. A copy of `V` in array `27`.
  have hV₃ : IsBitSet V 33 s₃ := (hV₁.of_arr_eq (harr₂ 33)).of_arr_eq (harr₃ 33)
  have hlen33 : (s₃.arrs 33).length < 2 ^ w := by rw [hV₃.1]; exact hn_w
  have hvals33 : ∀ x ∈ s₃.arrs 33, x < 2 ^ w := by
    rw [hV₃.arr_eq_bitSetList]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := getElem_bitSetList_le_one V i hi
    omega
  obtain ⟨s₄, t₄, hex₄, ht₄, h27₄, harr₄, hreg₄⟩ :=
    copyArrLoopProg_exec 33 27 (R + 40) (R + 41) (by decide) (by romega) hw1 s₃ hlen33 hvals33
  have hV₄ : IsBitSet V 27 s₄ := hV₃.of_arr_eq' h27₄
  -- 5. The test `V ∩ Z_i = ∅`.
  have hZ₄ : IsBitSet Z 17 s₄ := by
    refine IsBitSet.of_bitSetList _ _ _ ?_
    rw [harr₄ 17 (by decide), harr₃ 17, harr₂ 17,
      harr₁' 17 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact h17
  have hr1_4 : s₄.regs 1 = n := by
    rw [hreg₄ 1 (by romega) (by romega), hreg₃ 1 (by omega) (by omega)]; exact hr1_2
  obtain ⟨s₅, t₅, hex₅, ht₅, hr10₅, harr₅, hreg₅⟩ :=
    testDisjointInstProg_exec V Z hw1 hn_w hV₄ hZ₄ hr1_4
  -- The registers at the test.
  have hreg_st : ∀ q : ℕ, (q < 3 ∨ 10 < q) → q < R + 6 → s₅.regs q = st.regs q := by
    intro q hq hqR
    rw [hreg₅ q (by omega) (by omega), hreg₄ q (by romega) (by romega),
      hreg₃ q (by omega) (by omega), hreg₂ q (by omega), hreg₁ q hq]
  have hreg_s₂ : ∀ q : ℕ, R + 10 ≤ q → q ≤ R + 20 → s₅.regs q = s₂.regs q := by
    intro q hq hq'
    rw [hreg₅ q (by omega) (by omega), hreg₄ q (by romega) (by romega),
      hreg₃ q (by omega) (by omega)]
  have hr18 : s₅.regs (R + 18) = (Gi.restrictMult (fun u w => u ∈ V ∧ w ∈ V)).numEdges := by
    rw [hreg_s₂ (R + 18) (by omega) (by omega)]; exact hin₂
  have hr19 : s₅.regs (R + 19) =
      (Gi.restrictMult (fun u w => (u ∈ V ∧ w ∈ X) ∨ (u ∈ X ∧ w ∈ V))).numEdges := by
    rw [hreg_s₂ (R + 19) (by omega) (by omega)]; exact hcr₂
  have hr6 : s₅.regs (R + 6) = V.card := by
    rw [hreg₅ _ (by omega) (by omega), hreg₄ _ (by romega) (by romega)]; exact hcard₃
  have hr1_5 : s₅.regs 1 = n := by rw [hreg_st 1 (by omega) (by omega)]; exact hr1
  have hrX_5 : s₅.regs (R + 1) = X.card := by rw [hreg_st _ (by omega) (by omega)]; exact hrX
  have hrE_5 : s₅.regs (R + 2) = Gi.numEdges := by
    rw [hreg_st _ (by omega) (by omega)]; exact hrE
  -- The value of the test.
  have hinC := Gi.numEdges_restrictMult_le (fun u w => u ∈ V ∧ w ∈ V)
  have hcrC := Gi.numEdges_restrictMult_le (fun u w => (u ∈ V ∧ w ∈ X) ∨ (u ∈ X ∧ w ∈ V))
  have hVc : V.card ≤ n := by simpa using V.card_le_univ
  have hXc : X.card ≤ n := by simpa using X.card_le_univ
  set inC := (Gi.restrictMult (fun u w => u ∈ V ∧ w ∈ V)).numEdges with hinC_def
  set crC := (Gi.restrictMult (fun u w => (u ∈ V ∧ w ∈ X) ∨ (u ∈ X ∧ w ∈ V))).numEdges
    with hcrC_def
  have ev_const : ∀ c : ℕ, c < 2 ^ w → (Expr.const c).eval w s₅ = some c := fun c hc => by
    simp [Expr.eval, checkWord, hc]
  have ev_le : ∀ {e₁ e₂ : Expr} {v₁ v₂ : ℕ}, e₁.eval w s₅ = some v₁ → e₂.eval w s₅ = some v₂ →
      (Expr.op .le e₁ e₂).eval w s₅ = some (if v₁ ≤ v₂ then 1 else 0) := by
    intro e₁ e₂ v₁ v₂ h₁ h₂
    have : (if v₁ ≤ v₂ then 1 else 0 : ℕ) < 2 ^ w := by split_ifs <;> omega
    simp [Expr.eval, h₁, h₂, BinOp.eval, BinOp.raw, checkWord, this]
  have hbit : ∀ (P : Prop) [Decidable P], (if P then 1 else 0 : ℕ) ≤ 1 := by
    intro P _; split_ifs <;> omega
  have htest : (alg99Step4Test R).eval w s₅ = some ((if Disjoint V Z then 1 else 0) *
      (if 2 * (inC + V.card + 1 + crC + X.card) ≤ Gi.numEdges + n + 1 then 1 else 0)) := by
    have hd := hbit (Disjoint V Z)
    have hl := hbit (2 * (inC + V.card + 1 + crC + X.card) ≤ Gi.numEdges + n + 1)
    have hprod : (if Disjoint V Z then 1 else 0 : ℕ) *
        (if 2 * (inC + V.card + 1 + crC + X.card) ≤ Gi.numEdges + n + 1 then 1 else 0) ≤ 1 := by
      calc _ ≤ 1 * 1 := Nat.mul_le_mul hd hl
        _ = 1 := rfl
    unfold alg99Step4Test
    exact step4_eval_mul (step4_eval_reg hr10₅ (by omega)) (ev_le
      (step4_eval_mul (ev_const 2 hw2) (step4_eval_add (step4_eval_add (step4_eval_add
        (step4_eval_add (step4_eval_reg hr18 (by omega)) (step4_eval_reg hr6 (by omega))
          (by omega)) (ev_const 1 hw1) (by omega)) (step4_eval_reg hr19 (by omega)) (by omega))
        (step4_eval_reg hrX_5 (by omega)) (by omega)) (by omega))
      (step4_eval_add (step4_eval_add (step4_eval_reg hrE_5 (by omega))
        (step4_eval_reg hr1_5 (by omega)) (by omega)) (ev_const 1 hw1) (by omega))) (by omega)
  -- The time before the branch.
  have ht₄' : t₄ ≤ 8 + 15 * n := by rw [hV₃.1] at ht₄; exact ht₄
  have hcost_test : (alg99Step4Test R).cost = 19 := by simp [alg99Step4Test, Expr.cost]
  have hWa : (W_flat a).IsValid := Hi.isValid_of_isSubwallOf hHi (hsub a)
  have hlenW : (W_flat a).encList.length ≤ maxWallEncLen h' n :=
    length_encList_le_maxWallEncLen hHi (hsub a)
  rw [← hlen22] at ht₁
  have ht_pre : t₁ + (t₂ + (t₃ + (t₄ + t₅))) ≤
      52 * (st.arrs 22).length + 60 * Gi.numActivePairs + 162 * n + 100 := by omega
  have harr_st : ∀ x : ℕ, x ≠ 27 → x ≠ 29 → x ≠ 31 → x ≠ 32 → x ≠ 33 → x ≠ 36 → x ≠ 37 →
      x ≠ 38 → s₅.arrs x = st.arrs x := by
    intro x h27 h29 h31 h32 h33 h36 h37 h38
    rw [harr₅ x, harr₄ x (by romega), harr₃ x, harr₂ x, harr₁' x h29 h31 h32 h33 h36 h37 h38]
  have hctx_of : ∀ st' : State, (∀ x : ℕ, x ≠ 27 → x ≠ 29 → x ≠ 31 → x ≠ 32 → x ≠ 33 →
      x ≠ 36 → x ≠ 37 → x ≠ 38 → x ≠ a_W → st'.arrs x = st.arrs x) →
      (∀ q : ℕ, (q < 3 ∨ 10 < q) → q < R + 4 → st'.regs q = st.regs q) →
      Alg99Step4Ctx Gi Hi X Z W_flat R st' := by
    intro st' ha hq
    refine hc.of_eq (fun x hx => ha x ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (fun q hq' => hq q ?_ ?_) <;>
      omega
  by_cases hP : Alg99Step4Pass Gi X Z V
  · -- The subwall passes: set the flag and copy its code.
    have hval : (if Disjoint V Z then 1 else 0 : ℕ) *
        (if 2 * (inC + V.card + 1 + crC + X.card) ≤ Gi.numEdges + n + 1 then 1 else 0) = 1 := by
      obtain ⟨hd, hl⟩ := hP
      have hl' : 2 * (inC + V.card + 1 + crC + X.card) ≤ Gi.numEdges + n + 1 := hl
      simp [hd, hl']
    rw [hval] at htest
    let s₆ := s₅.setReg (R + 4) 1
    have hex₆ : Exec w (.assign (R + 4) (.const 1)) s₅ s₆ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw1])
    have hsplit := alg97Out_eq_prefix_append X W_flat a
    have hsucc := alg97OutPrefix_succ X W_flat a
    have hlen_out : (alg97OutPrefix X W_flat a.1).length + (W_flat a).encList.length ≤
        (st.arrs outArr).length := by
      rw [h1, hsplit]; simp only [List.length_append]; omega
    have hlen_succ : (alg97OutPrefix X W_flat (a.1 + 1)).length =
        (alg97OutPrefix X W_flat a.1).length + (W_flat a).encList.length := by
      rw [hsucc, List.length_append]
    have hp3 : s₆.regs (R + 3) = (alg97OutPrefix X W_flat (a.1 + 1)).length := by
      simp only [s₆, State.setReg_regs_ne _ _ (show (R + 3 : Reg) ≠ R + 4 by romega)]
      rw [hreg_st _ (by omega) (by omega)]; exact hpos'
    have hp5 : s₆.regs (R + 5) = (alg97OutPrefix X W_flat a.1).length := by
      simp only [s₆, State.setReg_regs_ne _ _ (show (R + 5 : Reg) ≠ R + 4 by romega)]
      rw [hreg_st _ (by omega) (by omega)]; exact hpos
    let s₇ := s₆.setReg (R + 8) (W_flat a).encList.length
    have hex₇ : Exec w (.assign (R + 8) (.op .sub (.reg (R + 3)) (.reg (R + 5)))) s₆ s₇ 4 := by
      refine .assign ?_
      have h3w : (alg97OutPrefix X W_flat (a.1 + 1)).length < 2 ^ w := by omega
      have h5w : (alg97OutPrefix X W_flat a.1).length < 2 ^ w := by omega
      have hlw : (W_flat a).encList.length < 2 ^ w := by omega
      have hsub_eq : (alg97OutPrefix X W_flat (a.1 + 1)).length -
          (alg97OutPrefix X W_flat a.1).length = (W_flat a).encList.length := by omega
      simp only [Expr.eval, checkWord, hp3, hp5, h3w, h5w, ↓reduceIte, BinOp.eval, BinOp.raw,
        hsub_eq, hlw]
    have hsrc₇ : s₇.arrs outArr = alg97OutPrefix X W_flat a.1 ++ (W_flat a).encList ++
        ((List.finRange s).drop (a.1 + 1)).flatMap (fun b => (W_flat b).encList) := by
      change s₅.arrs 1 = _
      rw [harr_st 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)]
      exact h1.trans hsplit
    have he_off : (Expr.reg (R + 5)).eval w s₇ = some (alg97OutPrefix X W_flat a.1).length := by
      have : s₇.regs (R + 5) = (alg97OutPrefix X W_flat a.1).length := by
        simp only [s₇, State.setReg_regs_ne _ _ (show (R + 5 : Reg) ≠ R + 8 by romega)]
        exact hp5
      simp [Expr.eval, checkWord, this]; omega
    obtain ⟨s₈, t₈, hex₈, ht₈, hW₈, harr₈, hreg₈⟩ :=
      readSliceProg_exec outArr a_W (.reg (R + 5)) (R + 8) (R + 30) (by romega) (by omega)
        (alg97OutPrefix X W_flat a.1) (W_flat a).encList _ rfl rfl
        (all_lt_encList_of_isValid (W_flat a) hWa le_rfl hh_w hc2_w hn_w) hw1 (by omega)
        he_off hsrc₇ (by simp [s₇])
    have hreg₈' : ∀ q : ℕ, (q < 3 ∨ 10 < q) → q < R + 4 → s₈.regs q = st.regs q := by
      intro q hq hqR
      rw [hreg₈ q (by omega)]
      simp only [s₇, s₆, State.setReg_regs_ne _ _ (show (q : Reg) ≠ R + 8 by romega),
        State.setReg_regs_ne _ _ (show (q : Reg) ≠ R + 4 by romega)]
      exact hreg_st q hq (by omega)
    have harr₈' : ∀ x : ℕ, x ≠ 27 → x ≠ 29 → x ≠ 31 → x ≠ 32 → x ≠ 33 → x ≠ 36 → x ≠ 37 →
        x ≠ 38 → x ≠ a_W → s₈.arrs x = st.arrs x := by
      intro x h27 h29 h31 h32 h33 h36 h37 h38 hW
      rw [harr₈ x hW]
      exact harr_st x h27 h29 h31 h32 h33 h36 h37 h38
    refine ⟨s₈, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
      (.ite_true htest one_ne_zero (.seq hex₆ (.seq hex₇ hex₈))))))), ?_,
      hctx_of s₈ harr₈' hreg₈', fun _ => ⟨?_, hW₈, ?_⟩, fun h => absurd hP h, harr₈', hreg₈'⟩
    · simp only [Expr.cost] at ht₈
      rw [hcost_test]
      unfold alg99Step4CheckCost
      omega
    · rw [hreg₈ (R + 4) (by omega)]
      simp [s₇, s₆]
    · rw [harr₈ 33 (by omega)]
      change s₅.arrs 33 = _
      rw [harr₅ 33, harr₄ 33 (by romega)]
      exact hV₃.arr_eq_bitSetList
  · -- The subwall fails: nothing more is done.
    have hval : (if Disjoint V Z then 1 else 0 : ℕ) *
        (if 2 * (inC + V.card + 1 + crC + X.card) ≤ Gi.numEdges + n + 1 then 1 else 0) = 0 := by
      by_cases hd : Disjoint V Z
      · have hl : ¬ 2 * (inC + V.card + 1 + crC + X.card) ≤ Gi.numEdges + n + 1 :=
          fun hl => hP ⟨hd, hl⟩
        simp [hd, hl]
      · simp [hd]
    rw [hval] at htest
    have harr₅' : ∀ x : ℕ, x ≠ 27 → x ≠ 29 → x ≠ 31 → x ≠ 32 → x ≠ 33 → x ≠ 36 → x ≠ 37 →
        x ≠ 38 → x ≠ a_W → s₅.arrs x = st.arrs x :=
      fun x h27 h29 h31 h32 h33 h36 h37 h38 _ => harr_st x h27 h29 h31 h32 h33 h36 h37 h38
    have hreg₅' : ∀ q : ℕ, (q < 3 ∨ 10 < q) → q < R + 4 → s₅.regs q = st.regs q :=
      fun q hq hqR => hreg_st q hq (by omega)
    refine ⟨s₅, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
      (.ite_false htest (.skip _)))))), ?_, hctx_of s₅ harr₅' hreg₅', fun h => absurd h hP,
      fun _ => ?_, harr₅', hreg₅'⟩
    · rw [hcost_test]
      unfold alg99Step4CheckCost
      omega
    · rw [hreg_st _ (by omega) (by omega)]; exact hflag

/-- **One step of the scan of step (4) of (9.9)** (Graph Minors XIII, page 105). Started at the
start of the code of `H^a` in `outArr` (register `R + 3`), the program reads `H^a` and stops at
the start of the code of `H^{a+1}`. If the flag in register `R + 4` was `1`, it keeps the flag,
the code in `a_W` and the compass in array `33`. If it was `0`, the flag becomes `1` exactly when
the compass of `H^a` passes the test, and then `a_W` and array `33` hold the code and the compass
of `H^a`. -/
theorem alg99Step4Iter_exec {w : ℕ} {Gi : MultiDigraph n} {Hi : WallOfHeight h' Gi}
    (hHi : Hi.IsValid) (h2' : 2 ≤ h') (he' : Even h') (h2 : 2 ≤ h)
    {X Z : Finset (Fin n)} {W_flat : Fin s → WallOfHeight h Gi}
    (hsub : ∀ a, (W_flat a).IsSubwallOf Hi) (a : Fin s)
    (hVX : Disjoint ((W_flat a).castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset X)
    (a_W R : ℕ) (ha_W : 38 < a_W) (hR : 14 < R)
    (hw3 : 3 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w) (hm3_w : 2 + 3 * Gi.numActivePairs < 2 ^ w)
    (hbig : 4 * (Gi.numEdges + n + 1) < 2 ^ w)
    (hh_w : h < 2 ^ w) (hc2_w : 3 + 2 * elemWallNumVerts h < 2 ^ w)
    {st : State} (hc : Alg99Step4Ctx Gi Hi X Z W_flat R st)
    (hcap_w : (st.arrs 22).length < 2 ^ w) (hout_w : (st.arrs outArr).length < 2 ^ w)
    (hpos : st.regs (R + 3) = (alg97OutPrefix X W_flat a.1).length)
    (hflag : st.regs (R + 4) = 0 ∨ st.regs (R + 4) = 1) :
    ∃ st' t, Exec w (alg99Step4Iter h h2 a_W R) st st' t ∧
      t ≤ parseWallCost h n + alg99Step4CheckCost h' n (st.arrs 22).length Gi.numActivePairs + 10 ∧
      Alg99Step4Ctx Gi Hi X Z W_flat R st' ∧
      st'.regs (R + 3) = (alg97OutPrefix X W_flat (a.1 + 1)).length ∧
      (st.regs (R + 4) = 1 →
        st'.regs (R + 4) = 1 ∧ st'.arrs a_W = st.arrs a_W ∧ st'.arrs 33 = st.arrs 33) ∧
      (st.regs (R + 4) = 0 →
        (Alg99Step4Pass Gi X Z
            ((W_flat a).castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset →
          st'.regs (R + 4) = 1 ∧ st'.arrs a_W = (W_flat a).encList ∧
          st'.arrs 33 =
            bitSetList ((W_flat a).castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset) ∧
        (¬ Alg99Step4Pass Gi X Z
            ((W_flat a).castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset →
          st'.regs (R + 4) = 0)) ∧
      (∀ x : ℕ, x ≠ 27 → x ≠ 28 → x ≠ 29 → x ≠ 31 → x ≠ 32 → x ≠ 33 → x ≠ 36 → x ≠ 37 →
        x ≠ 38 → x ≠ a_W → st'.arrs x = st.arrs x) ∧
      (∀ q : ℕ, (q < 3 ∨ 14 < q) → q < R + 3 → st'.regs q = st.regs q) := by
  have h1 := hc.1
  have hr1 := hc.2.2.2.2.2.2.2.1
  have hw1 : 1 < 2 ^ w := by omega
  have hWa : (W_flat a).IsValid := Hi.isValid_of_isSubwallOf hHi (hsub a)
  -- 1. Save the start of the code of `H^a`.
  let s₁ := st.setReg (R + 5) (alg97OutPrefix X W_flat a.1).length
  have hsplit := alg97Out_eq_prefix_append X W_flat a
  have hlen_out : (alg97OutPrefix X W_flat (a.1 + 1)).length ≤ (st.arrs outArr).length := by
    rw [h1, hsplit, alg97OutPrefix_succ]; simp only [List.length_append]; omega
  have hex₁ : Exec w (.assign (R + 5) (.reg (R + 3))) st s₁ 2 :=
    .assign (by
      have : (alg97OutPrefix X W_flat a.1).length < 2 ^ w := by
        rw [alg97OutPrefix_succ, List.length_append] at hlen_out; omega
      simp [Expr.eval, checkWord, hpos, this])
  -- 2. Read `H^a`.
  obtain ⟨s₂, t₂, hex₂, ht₂, hpos₂, h14₂, hV₂, hP₂, harr₂, hreg₂⟩ :=
    alg99ReadSubwall_exec (st := s₁) h2 X W_flat a hWa outArr 27 28 (R + 3) (by decide)
      (by decide) (by decide) (by omega) hw1 hn1_w (by omega) (by omega) (by exact h1)
      (by simp [s₁, hr1])
      (by simp [s₁, hpos])
  have hreg₂' : ∀ q : ℕ, (q < 3 ∨ 14 < q) → q ≠ R + 3 → q ≠ R + 5 → s₂.regs q = st.regs q := by
    intro q hq h3 h5
    rw [hreg₂ q (by omega) (by omega) h3]
    simp [s₁, State.setReg_regs_ne _ _ (show (q : Reg) ≠ R + 5 from h5)]
  have harr₂' : ∀ x : ℕ, x ≠ 27 → x ≠ 28 → s₂.arrs x = st.arrs x := fun x h27 h28 => by
    rw [harr₂ x h27 h28]; rfl
  have hc₂ : Alg99Step4Ctx Gi Hi X Z W_flat R s₂ :=
    hc.of_eq (fun x hx => harr₂' x (by omega) (by omega))
      (fun q hq => hreg₂' q (by omega) (by omega) (by omega))
  have h22₂ : s₂.arrs 22 = st.arrs 22 := harr₂' 22 (by omega) (by omega)
  have hout₂ : s₂.arrs outArr = st.arrs outArr := harr₂' 1 (by omega) (by omega)
  have hflag₂ : s₂.regs (R + 4) = st.regs (R + 4) := hreg₂' _ (by omega) (by omega) (by omega)
  have hp5₂ : s₂.regs (R + 5) = (alg97OutPrefix X W_flat a.1).length := by
    rw [hreg₂ _ (by omega) (by omega) (by omega)]; simp [s₁]
  have hcost_eq : (Expr.op .eq (.reg (R + 4)) (.const 0)).cost = 3 := rfl
  rcases hflag with hf | hf
  · -- No subwall has passed yet: test `H^a`.
    have hcond : (Expr.op .eq (.reg (R + 4)) (.const 0)).eval w s₂ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hflag₂, hf, hw1]
    obtain ⟨s₃, t₃, hex₃, ht₃, hc₃, hpass, hfail, harr₃, hreg₃⟩ :=
      alg99Step4Check_exec hHi h2' he' h2 hsub a hVX a_W R ha_W hR hw3 hn1_w hm3_w hbig hh_w hc2_w
        hc₂ (by rw [h22₂]; exact hcap_w) (by rw [hout₂]; exact hout_w) hV₂ hP₂ h14₂ hp5₂ hpos₂
        (by rw [hflag₂, hf])
    refine ⟨s₃, _, .seq hex₁ (.seq hex₂ (.ite_true hcond one_ne_zero hex₃)), ?_, hc₃, ?_,
      fun h => by omega, fun _ => ⟨hpass, hfail⟩, ?_, ?_⟩
    · rw [hcost_eq, h22₂] at *
      omega
    · rw [hreg₃ _ (by omega) (by omega)]; exact hpos₂
    · intro x h27 h28 h29 h31 h32 h33 h36 h37 h38 hW
      rw [harr₃ x h27 h29 h31 h32 h33 h36 h37 h38 hW, harr₂' x h27 h28]
    · intro q hq hqR
      rw [hreg₃ q (by omega) (by omega), hreg₂' q hq (by omega) (by omega)]
  · -- A subwall has passed: only read `H^a`.
    have hcond : (Expr.op .eq (.reg (R + 4)) (.const 0)).eval w s₂ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hflag₂, hf, hw1]
    refine ⟨s₂, _, .seq hex₁ (.seq hex₂ (.ite_false hcond (.skip _))), ?_, hc₂, hpos₂,
      fun _ => ⟨by rw [hflag₂, hf], harr₂' _ (by omega) (by omega),
        harr₂' _ (by omega) (by omega)⟩, fun h => by omega, ?_, ?_⟩
    · rw [hcost_eq]
      omega
    · intro x h27 h28 _ _ _ _ _ _ _ _
      exact harr₂' x h27 h28
    · intro q hq hqR
      exact hreg₂' q hq (by omega) (by omega)

end GraphMinor.Compute
