module

public import GraphMinor.Compute.Algorithm91
public import GraphMinor.Compute.Algorithm97Init

/-!
# Graph Minors XIII, Algorithm (9.7): Flat Subwalls or $K_p$ Minor in $O(v\varepsilon)$ Time

This module formalizes **Algorithm (9.7)** (and proves **(9.6)**, `Algorithm97Statement`) from
Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*, page 103,
on the shared `MultiDigraph` and `WallOfHeight` formats:

> *(9.6) For any $p, s \ge 0$ and $h \ge 2$, even, there exists $h' \ge p^2 + 2$, even, such that
> there is an algorithm as in (9.7), with running time $O(v\varepsilon)$ for fixed $p, s, h$.*
>
> *(9.7) Algorithm.*
> *Input:* A graph $G$ and a wall $H \subseteq G$ of height $h'$.
> *Output:* Either
> (i) a model of $K_p$ in $G$, or
> (ii) a subset $X \subseteq V(G)$ with $|X| < \binom{p}{2}$ and $s$ mutually disjoint subwalls
> $H_1, \dots, H_s$ of $H$ of height $h$, each disjoint from $X$, and each flat and dividing in
> $(G \setminus X) \cup H$.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical

/-! ### Section 1: Cost Factor Helpers for $O(v\varepsilon)$ Time Bound -/

theorem maxCrossedBlockLen_le_mul (h n sz : ℕ) (hsz1 : 1 ≤ sz) (hn : n ≤ sz) :
    maxCrossedBlockLen h n ≤ (8 + 3 * elemWallNumVerts h) * sz := by
  have hmw := maxWallEncLen_le_mul h n sz hsz1 hn
  unfold maxCrossedBlockLen
  have h1 : 2 * 1 ≤ 2 * sz := Nat.mul_le_mul_left 2 hsz1
  have h2 : 2 * n ≤ 2 * sz := Nat.mul_le_mul_left 2 hn
  have h3 : (8 + 3 * elemWallNumVerts h) * sz =
      (4 + 3 * elemWallNumVerts h) * sz + 2 * sz + 2 * sz := by ring
  omega

/-- Constant factor for `alg97ScanStepCost` relative to `sz = alg97Size x`. -/
def alg97ScanFactor (h k₂ s_goal C_sh : ℕ) : ℕ :=
  1043 + 214 * elemWallNumVerts h + 190 * (4 + 3 * elemWallNumVerts h) + C_sh +
    170 * k₂ * (8 + 3 * elemWallNumVerts h) + 34 * s_goal * (4 + 3 * elemWallNumVerts h)

theorem alg97ScanStepCost_le_mul (h n e_card k₂ s_goal C_sh sz : ℕ)
    (hsz1 : 1 ≤ sz) (hn : n ≤ sz) (he : e_card ≤ sz)
    (hve : (n + 1) * (e_card + n + 1) ≤ sz) :
    alg97ScanStepCost h n k₂ s_goal (2 * e_card) (2 * e_card) e_card C_sh ≤
      alg97ScanFactor h k₂ s_goal C_sh * sz := by
  unfold alg97ScanStepCost alg97ScanFactor
  have h1 : 600 * 1 ≤ 600 * sz := Nat.mul_le_mul_left 600 hsz1
  have h2 : 270 * n ≤ 270 * sz := Nat.mul_le_mul_left 270 hn
  have h3 := parseWallCost_le_mul h n sz hsz1 hn
  have h4 : 190 * maxWallEncLen h n ≤ 190 * (4 + 3 * elemWallNumVerts h) * sz := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left 190 (maxWallEncLen_le_mul h n sz hsz1 hn)
  have h5 : 2 * (2 * e_card) + 76 * (2 * e_card) ≤ 156 * sz := by omega
  have h6 : C_sh * (n + 1) * (e_card + n + 1) ≤ C_sh * sz := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left C_sh hve
  have h7 : 170 * (k₂ * maxCrossedBlockLen h n) ≤
      170 * k₂ * (8 + 3 * elemWallNumVerts h) * sz := by
    have hm := maxCrossedBlockLen_le_mul h n sz hsz1 hn
    have hmul := Nat.mul_le_mul_left (170 * k₂) hm
    calc 170 * (k₂ * maxCrossedBlockLen h n)
        = (170 * k₂) * maxCrossedBlockLen h n := by ring
      _ ≤ (170 * k₂) * ((8 + 3 * elemWallNumVerts h) * sz) := hmul
      _ = 170 * k₂ * (8 + 3 * elemWallNumVerts h) * sz := by ring
  have h8 : 34 * (s_goal * maxWallEncLen h n) ≤
      34 * s_goal * (4 + 3 * elemWallNumVerts h) * sz := by
    have hm := maxWallEncLen_le_mul h n sz hsz1 hn
    have hmul := Nat.mul_le_mul_left (34 * s_goal) hm
    calc 34 * (s_goal * maxWallEncLen h n)
        = (34 * s_goal) * maxWallEncLen h n := by ring
      _ ≤ (34 * s_goal) * ((4 + 3 * elemWallNumVerts h) * sz) := hmul
      _ = 34 * s_goal * (4 + 3 * elemWallNumVerts h) * sz := by ring
  simp only [Nat.add_mul, Nat.mul_one] at h1 h3 ⊢
  omega

/-- Constant factor for `alg97InitCost` relative to `sz = alg97Size x`. -/
def alg97InitFactor (p t r h : ℕ) : ℕ :=
  let h' := alg97WallHeight p t r h
  537 + 84 * (4 + 3 * elemWallNumVerts h') + 214 * elemWallNumVerts h' +
    26 * (elemWallEdges h').length +
    t * (55 + 7 * elemWallNumVerts h +
      (elemWallEdges h).length * (40 + 34 * (4 + 3 * elemWallNumVerts h)) +
      34 * (t * (4 + 3 * elemWallNumVerts h))) +
    18 * (t * (4 + 3 * elemWallNumVerts h))

theorem alg97InitCost_le_mul {p t r h : ℕ} (x : Alg97Input (alg97WallHeight p t r h)) :
    alg97InitCost p t r h x.n x.G.numActivePairs ≤ alg97InitFactor p t r h * alg97Size x := by
  let h' := alg97WallHeight p t r h
  let sz := alg97Size x
  have hsz1 : 1 ≤ sz := by
    dsimp [sz, alg97Size]
    have : 1 * 1 ≤ (x.n + 1) * (x.G.numEdges + x.n + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hn : x.n ≤ sz := by
    dsimp [sz, alg97Size]
    have : (x.n + 1) * 1 ≤ (x.n + 1) * (x.G.numEdges + x.n + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hm : x.G.numActivePairs ≤ sz := by
    have h1 := Alg91.numActivePairs_le_numEdges x.G
    have h2 : 1 * (x.G.numEdges + x.n + 1) ≤ (x.n + 1) * (x.G.numEdges + x.n + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    dsimp [sz, alg97Size]
    omega
  have hmw' := maxWallEncLen_le_mul h' x.n sz hsz1 hn
  have hpw' := parseWallCost_le_mul h' x.n sz hsz1 hn
  have hmw := maxWallEncLen_le_mul h x.n sz hsz1 hn
  have h1 : (100 + 26 * (elemWallEdges h').length) * 1 ≤
      (100 + 26 * (elemWallEdges h').length) * sz :=
    Nat.mul_le_mul_left _ hsz1
  have h2 : 84 * (2 + 3 * x.G.numActivePairs) ≤ 420 * sz := by omega
  have h3 : 84 * maxWallEncLen h' x.n ≤ 84 * (4 + 3 * elemWallNumVerts h') * sz := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left 84 hmw'
  have h4 :
      t * (55 + 7 * elemWallNumVerts h +
        (elemWallEdges h).length * (40 + 34 * maxWallEncLen h x.n) +
        34 * (t * maxWallEncLen h x.n)) ≤
      t * (55 + 7 * elemWallNumVerts h +
        (elemWallEdges h).length * (40 + 34 * (4 + 3 * elemWallNumVerts h)) +
        34 * (t * (4 + 3 * elemWallNumVerts h))) * sz := by
    have hc1 : (55 + 7 * elemWallNumVerts h) * 1 ≤ (55 + 7 * elemWallNumVerts h) * sz :=
      Nat.mul_le_mul_left _ hsz1
    have hc2 :
        (elemWallEdges h).length * (40 + 34 * maxWallEncLen h x.n) ≤
          (elemWallEdges h).length * (40 + 34 * (4 + 3 * elemWallNumVerts h)) * sz := by
      have ha : 40 * 1 ≤ 40 * sz := Nat.mul_le_mul_left 40 hsz1
      have hb : 34 * maxWallEncLen h x.n ≤ 34 * (4 + 3 * elemWallNumVerts h) * sz := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 34 hmw
      have hab : 40 + 34 * maxWallEncLen h x.n ≤
          (40 + 34 * (4 + 3 * elemWallNumVerts h)) * sz := by
        rw [Nat.add_mul]
        omega
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left (elemWallEdges h).length hab
    have hc3 :
        34 * (t * maxWallEncLen h x.n) ≤
          34 * (t * (4 + 3 * elemWallNumVerts h)) * sz := by
      have hmul := Nat.mul_le_mul_left (34 * t) hmw
      calc 34 * (t * maxWallEncLen h x.n)
          = (34 * t) * maxWallEncLen h x.n := by ring
        _ ≤ (34 * t) * ((4 + 3 * elemWallNumVerts h) * sz) := hmul
        _ = 34 * (t * (4 + 3 * elemWallNumVerts h)) * sz := by ring
    have hsum :
        55 + 7 * elemWallNumVerts h +
          (elemWallEdges h).length * (40 + 34 * maxWallEncLen h x.n) +
          34 * (t * maxWallEncLen h x.n) ≤
        (55 + 7 * elemWallNumVerts h +
          (elemWallEdges h).length * (40 + 34 * (4 + 3 * elemWallNumVerts h)) +
          34 * (t * (4 + 3 * elemWallNumVerts h))) * sz := by
      simp only [Nat.add_mul, Nat.mul_one] at hc1 ⊢
      omega
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left t hsum
  have h5 : 18 * (t * maxWallEncLen h x.n) ≤ 18 * (t * (4 + 3 * elemWallNumVerts h)) * sz := by
    have hmul := Nat.mul_le_mul_left (18 * t) hmw
    calc 18 * (t * maxWallEncLen h x.n)
        = (18 * t) * maxWallEncLen h x.n := by ring
      _ ≤ (18 * t) * ((4 + 3 * elemWallNumVerts h) * sz) := hmul
      _ = 18 * (t * (4 + 3 * elemWallNumVerts h)) * sz := by ring
  unfold alg97InitCost alg97InitFactor
  dsimp only [h', sz] at hpw' h1 h2 h3 h4 h5 ⊢
  simp only [Nat.add_mul, Nat.mul_one] at hpw' h1 ⊢
  omega

/-! ### Section 2: Flat and Crossed Outcome Branches (`alg97FlatBranchProg`, `alg97CrossedBranchProg`) -/

/-- Branch of Algorithm (9.7) when `reg 11 < k₂` (`reg 12 = s_goal` flat dividing subwalls disjoint
from `X` have been collected in `arr 25`):
copies `arr 17` (`bitSetList X`) to `arr 26`, appends `arr 25` to `arr 26`, and prepends tag `1`
into `outArr`. -/
def alg97FlatBranchProg : Cmd :=
  .seq (copyArrLoopProg 17 26 14 15)
    (.seq (.assign 14 (.reg 1))
      (.seq (.assign 15 (.len 25))
        (.seq (appendArrProg 26 25 30 14 15 20)
          (prependWordProg (.const 1) 26 outArr 14 20))))

theorem alg97FlatBranchProg_exec {w p s_goal t r h : ℕ} (h2 : 2 ≤ h) (he : Even h)
    (x : Alg97Input (alg97WallHeight p t r h))
    (X : Finset (Fin x.n)) (hX_card : X.card < p.choose 2)
    (I : Finset (Fin t))
    (hI_div : ∀ idx ∈ I,
      (x.W.castGraph (WallOfHeight.wallUnionMultiDigraph x.G X x.W)).IsDividingSubwall
        ((alg97Subwall h2 he x.W idx).castGraph (WallOfHeight.wallUnionMultiDigraph x.G X x.W)))
    (idx_f : Fin s_goal → Fin t)
    (hmf : StrictMono idx_f)
    (hval_f : ∀ a : Fin s_goal,
      idx_f a ∈ I ∧
      ((alg97Subwall h2 he x.W (idx_f a)).castGraph
        (WallOfHeight.wallUnionMultiDigraph x.G X x.W)).IsFlatWall h2 ∧
      Disjoint ((alg97Subwall h2 he x.W (idx_f a)).castGraph
        (WallOfHeight.wallUnionMultiDigraph x.G X x.W)).vertexFinset X)
    (hw1 : 1 < 2 ^ w) (hn_w : x.n < 2 ^ w) (hh_w : h < 2 ^ w)
    (hc2_w : 3 + 2 * elemWallNumVerts h < 2 ^ w)
    (htot_out_w : 1 + (x.n + s_goal * maxWallEncLen h x.n) < 2 ^ w)
    {s : State}
    (harr17 : s.arrs 17 = bitSetList X)
    (harr25 : s.arrs 25 =
      (List.finRange s_goal).flatMap (fun a =>
        ((alg97Subwall h2 he x.W (idx_f a)).castGraph
          (WallOfHeight.wallUnionMultiDigraph x.G X x.W)).encList))
    (hr1 : s.regs 1 = x.n) :
    ∃ s' time,
      Exec w alg97FlatBranchProg s s' time ∧
      time ≤ 100 + 68 * x.n + 36 * (s_goal * maxWallEncLen h x.n) ∧
      IsAlg97Output p s_goal h (alg97WallHeight p t r h) x (s'.arrs outArr) := by
  let G' := WallOfHeight.wallUnionMultiDigraph x.G X x.W
  let W_sub' : Fin t → WallOfHeight h G' := fun idx => (alg97Subwall h2 he x.W idx).castGraph G'
  let flat_flat := (List.finRange s_goal).flatMap (fun a => (W_sub' (idx_f a)).encList)
  have hsub_valid' : ∀ idx : Fin t, (W_sub' idx).IsValid := by
    intro idx
    have hW' := WallOfHeight.isValid_castGraph_wallUnionMultiDigraph X x.hW_valid.2.2
    dsimp [W_sub']
    rw [alg97Subwall_castGraph h2 he G' x.W idx]
    exact alg97Subwall_isValid h2 he hW' idx
  obtain ⟨hf_len, hf_all_w⟩ :=
    flatEntries_len_and_bounds hsub_valid' idx_f hh_w hc2_w hn_w
  change flat_flat.length ≤ s_goal * maxWallEncLen h x.n at hf_len
  change ∀ v ∈ flat_flat, v < 2 ^ w at hf_all_w
  have hX_all_w : ∀ v ∈ bitSetList X, v < 2 ^ w := all_lt_bitSetList X hw1
  have hX_len_w : (s.arrs 17).length < 2 ^ w := by rw [harr17, length_bitSetList]; exact hn_w
  have hX_s_w : ∀ v ∈ s.arrs 17, v < 2 ^ w := by rw [harr17]; exact hX_all_w
  -- 1. copyArrLoopProg 17 26 14 15
  rcases copyArrLoopProg_exec 17 26 14 15
      (by decide) (by decide) hw1 s hX_len_w hX_s_w with
    ⟨s₁, t₁, hex₁, ht₁, harr26_1, harr₁, hreg₁⟩
  rw [harr17, length_bitSetList] at ht₁
  rw [harr17] at harr26_1
  -- 2. reg 14 := reg 1
  have hr1_1 : s₁.regs 1 = x.n := by
    rw [hreg₁ 1 (by decide) (by decide)]; exact hr1
  let s₂ := s₁.setReg 14 x.n
  have hex₂ : Exec w (.assign 14 (.reg 1)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr1_1, hn_w])
  -- 3. reg 15 := len 25
  have harr25_2 : s₂.arrs 25 = flat_flat := by
    simp only [s₂, State.setReg_arrs]
    rw [harr₁ 25 (by decide)]; exact harr25
  have hf_len_w : flat_flat.length < 2 ^ w := by omega
  let s₃ := s₂.setReg 15 flat_flat.length
  have hex₃ : Exec w (.assign 15 (.len 25)) s₂ s₃ 2 :=
    .assign (by simp only [Expr.eval, checkWord, harr25_2, hf_len_w, ↓reduceIte])
  -- 4. appendArrProg 26 25 30 14 15 20
  have htot_app_w : (bitSetList X).length + flat_flat.length < 2 ^ w := by
    rw [length_bitSetList]; omega
  rcases appendArrProg_exec 26 25 30 14 15 20
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (bitSetList X) flat_flat hX_all_w hf_all_w hw1 htot_app_w (s := s₃)
      (by simp [s₃, s₂, harr26_1])
      (by simp [s₃, harr25_2])
      (by simp [s₃, s₂, length_bitSetList])
      rfl with
    ⟨s₄, t₄, hex₄, ht₄, harr26_4, hr14_4, _, _⟩
  rw [length_bitSetList] at ht₄ hr14_4
  -- 5. prependWordProg (.const 1) 26 outArr 14 20
  have hcomb_all_w : ∀ v ∈ bitSetList X ++ flat_flat, v < 2 ^ w := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hX_all_w v hv
    · exact hf_all_w v hv
  have h1_comb_w : 1 + (bitSetList X ++ flat_flat).length < 2 ^ w := by
    rw [List.length_append, length_bitSetList]; omega
  rcases prependWordProg_exec (tag := 1) (.const 1) 26 outArr 14 20
      (by decide) (by decide)
      (bitSetList X ++ flat_flat) hcomb_all_w hw1 h1_comb_w
      (fun _ => by simp [Expr.eval, checkWord, hw1])
      harr26_4
      (by rw [List.length_append, length_bitSetList]; exact hr14_4) with
    ⟨s₅, t₅, hex₅, ht₅, hout₅, _, _⟩
  dsimp [Expr.cost] at ht₅
  rw [List.length_append, length_bitSetList] at ht₅
  have h36_f : 36 * flat_flat.length ≤ 36 * (s_goal * maxWallEncLen h x.n) :=
    Nat.mul_le_mul_left 36 hf_len
  refine ⟨s₅, t₁ + (2 + (2 + (t₄ + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega,
    isAlg97Output_of_flat_outcome h2 he x X hX_card I hI_div idx_f hmf hval_f hout₅⟩

/-- Branch of Algorithm (9.7) when `¬ reg 11 < k₂` (`reg 11 = k₂` crossed dividing subwalls have
been collected in `arr 24`):
assembles `encAlg91In x91 = x.G.enc ++ x.W.encList ++ arr 24` in `inArr` from `arr 9`, `arr 10`,
and `arr 24`, executes `P91`, copies `outArr` (`encBitSetsUpTo K p`) to `arr 26`, and prepends tag
`0` into `outArr`. -/
def alg97CrossedBranchProg (P91 : Cmd) : Cmd :=
  .seq (copyArrLoopProg 9 inArr 14 15)
    (.seq (.assign 14 (.len inArr))
      (.seq (.assign 15 (.len 10))
        (.seq (appendArrProg inArr 10 30 14 15 20)
          (.seq (.assign 15 (.len 24))
            (.seq (appendArrProg inArr 24 30 14 15 20)
              (.seq P91
                (.seq (copyArrLoopProg outArr 26 14 15)
                  (.seq (.assign 14 (.len 26))
                    (prependWordProg (.const 0) 26 outArr 14 20)))))))))

/-- Cost bound for `alg97CrossedBranchProg`. -/
def alg97CrossedBranchCost (p t r h k₂ n m_act e_edges C₉₁ : ℕ) : ℕ :=
  let h' := alg97WallHeight p t r h
  150 + 83 * (2 + 3 * m_act) + 52 * maxWallEncLen h' n +
    18 * (k₂ * maxCrossedBlockLen h n) +
    C₉₁ * (e_edges + n + 1) + 33 * (p * n)

theorem alg97CrossedBranchProg_exec {w p s_goal t r h k₂ r₂ C₉₁ : ℕ}
    {P91 : Cmd}
    (h2 : 2 ≤ h) (he : Even h) (hr₂ : r₂ ≤ r)
    (x : Alg97Input (alg97WallHeight p t r h))
    (X : Finset (Fin x.n)) (I : Finset (Fin t))
    (hI_div : ∀ idx ∈ I,
      (x.W.castGraph (WallOfHeight.wallUnionMultiDigraph x.G X x.W)).IsDividingSubwall
        ((alg97Subwall h2 he x.W idx).castGraph (WallOfHeight.wallUnionMultiDigraph x.G X x.W)))
    (entries_c : Fin k₂ → CrossedSubwallEntry h2
      (fun idx => (alg97Subwall h2 he x.W idx).castGraph
        (WallOfHeight.wallUnionMultiDigraph x.G X x.W)))
    (hmc : StrictMono (fun a => (entries_c a).idx))
    (hmem_c : ∀ a : Fin k₂, (entries_c a).idx ∈ I)
    (hexec91 : ∀ (x91 : Alg91Input p (alg97WallHeight p t r h) k₂ r₂),
      x91.n = x.n → x91.G.numEdges = x.G.numEdges →
      ∀ (s : State), s.arrs inArr = encAlg91In x91 →
      ∃ s' time,
        Exec w P91 s s' time ∧
        time ≤ C₉₁ * alg91Size x91 ∧
        IsAlg91Output p x91 (s'.arrs outArr))
    (hw1 : 1 < 2 ^ w) (hn1_w : x.n + 1 < 2 ^ w)
    (hh'_w : alg97WallHeight p t r h < 2 ^ w)
    (hc2'_w : 3 + 2 * elemWallNumVerts (alg97WallHeight p t r h) < 2 ^ w)
    (hm_w : x.G.numActivePairs < 2 ^ w) (he_w : x.G.numEdges < 2 ^ w)
    (hin91_w :
      (2 + 3 * x.G.numActivePairs) +
        maxWallEncLen (alg97WallHeight p t r h) x.n +
        k₂ * maxCrossedBlockLen h x.n < 2 ^ w)
    (hmod_w : 1 + p * x.n < 2 ^ w)
    {s : State}
    (harr9 : s.arrs 9 = x.G.enc)
    (harr10 : s.arrs 10 = x.W.encList)
    (harr24 : s.arrs 24 = (List.finRange k₂).flatMap (fun a => (entries_c a).encBlock)) :
    ∃ s' time,
      Exec w (alg97CrossedBranchProg P91) s s' time ∧
      time ≤ alg97CrossedBranchCost p t r h k₂ x.n x.G.numActivePairs x.G.numEdges C₉₁ ∧
      IsAlg97Output p s_goal h (alg97WallHeight p t r h) x (s'.arrs outArr) := by
  let h' := alg97WallHeight p t r h
  let G' := WallOfHeight.wallUnionMultiDigraph x.G X x.W
  let W_sub' : Fin t → WallOfHeight h G' := fun idx => (alg97Subwall h2 he x.W idx).castGraph G'
  let crossed_flat := (List.finRange k₂).flatMap (fun a => (entries_c a).encBlock)
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have hh_w : h < 2 ^ w := by have := le_alg97WallHeight p t r h; omega
  have hc2_w : 3 + 2 * elemWallNumVerts h < 2 ^ w := by
    have hle := le_alg97WallHeight p t r h
    have : elemWallNumVerts h ≤ elemWallNumVerts h' := by
      rw [elemWallNumVerts_eq, elemWallNumVerts_eq]
      exact Nat.sub_le_sub_right
        (Nat.mul_le_mul (show h + 1 ≤ h' + 1 by omega) (show 2 * h + 2 ≤ 2 * h' + 2 by omega)) 2
    dsimp [h'] at this; omega
  have hG_len : x.G.enc.length = 2 + 3 * x.G.numActivePairs := MultiDigraph.length_enc x.G
  have hW_len_le : x.W.encList.length ≤ maxWallEncLen h' x.n := by
    have ha := Alg91.length_encList_le_of_isValid x.hW_valid.2.2
    have hb := length_elemWallEdges_le h'
    unfold maxWallEncLen; dsimp [h'] at hb ⊢; omega
  have hsub_valid' : ∀ idx : Fin t, (W_sub' idx).IsValid := by
    intro idx
    have hW' := WallOfHeight.isValid_castGraph_wallUnionMultiDigraph X x.hW_valid.2.2
    dsimp [W_sub']
    rw [alg97Subwall_castGraph h2 he G' x.W idx]
    exact alg97Subwall_isValid h2 he hW' idx
  obtain ⟨hc_len, hc_all_w⟩ :=
    crossedEntries_len_and_bounds hsub_valid' entries_c hh_w hc2_w hn1_w
  change crossed_flat.length ≤ k₂ * maxCrossedBlockLen h x.n at hc_len
  change ∀ v ∈ crossed_flat, v < 2 ^ w at hc_all_w
  have hG_all_w : ∀ v ∈ x.G.enc, v < 2 ^ w := all_lt_enc_multiDigraph x.G hn_w hm_w he_w
  have hW_all_w : ∀ v ∈ x.W.encList, v < 2 ^ w :=
    all_lt_encList_of_isValid x.W x.hW_valid.2.2 le_rfl hh'_w hc2'_w hn_w
  have hG_len_w : x.G.enc.length < 2 ^ w := by omega
  have hW_len_w : x.W.encList.length < 2 ^ w := by dsimp [h'] at hW_len_le; omega
  have hGW_len_w : x.G.enc.length + x.W.encList.length < 2 ^ w := by dsimp [h'] at hW_len_le; omega
  have hc_len_w : crossed_flat.length < 2 ^ w := by omega
  -- 1. copyArrLoopProg 9 inArr 14 15
  rcases copyArrLoopProg_exec 9 inArr 14 15
      (by decide) (by decide) hw1 s
      (by rw [harr9]; exact hG_len_w)
      (by rw [harr9]; exact hG_all_w) with
    ⟨s₁, t₁, hex₁, ht₁, hin₁, harr₁, _⟩
  rw [harr9] at ht₁ hin₁
  -- 2. reg 14 := len inArr
  let s₂ := s₁.setReg 14 x.G.enc.length
  have hex₂ : Exec w (.assign 14 (.len inArr)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hin₁, hG_len_w, ↓reduceIte])
  -- 3. reg 15 := len 10
  have harr10_2 : s₂.arrs 10 = x.W.encList := by
    simp only [s₂, State.setReg_arrs]
    rw [harr₁ 10 (by decide)]; exact harr10
  let s₃ := s₂.setReg 15 x.W.encList.length
  have hex₃ : Exec w (.assign 15 (.len 10)) s₂ s₃ 2 :=
    .assign (by simp only [Expr.eval, checkWord, harr10_2, hW_len_w, ↓reduceIte])
  -- 4. appendArrProg inArr 10 30 14 15 20
  rcases appendArrProg_exec inArr 10 30 14 15 20
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      x.G.enc x.W.encList hG_all_w hW_all_w hw1 hGW_len_w (s := s₃)
      (by simp [s₃, s₂, hin₁])
      (by simp [s₃, harr10_2])
      rfl rfl with
    ⟨s₄, t₄, hex₄, ht₄, hin₄, hr14_4, harr₄, _⟩
  -- 5. reg 15 := len 24
  have harr24_4 : s₄.arrs 24 = crossed_flat := by
    rw [harr₄ 24 (by decide) (by decide)]
    simp only [s₃, s₂, State.setReg_arrs]
    rw [harr₁ 24 (by decide)]; exact harr24
  let s₅ := s₄.setReg 15 crossed_flat.length
  have hex₅ : Exec w (.assign 15 (.len 24)) s₄ s₅ 2 :=
    .assign (by simp only [Expr.eval, checkWord, harr24_4, hc_len_w, ↓reduceIte])
  -- 6. appendArrProg inArr 24 30 14 15 20
  have hGW_all_w : ∀ v ∈ x.G.enc ++ x.W.encList, v < 2 ^ w := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hG_all_w v hv
    · exact hW_all_w v hv
  have htot91_w : (x.G.enc ++ x.W.encList).length + crossed_flat.length < 2 ^ w := by
    dsimp [h'] at hW_len_le
    rw [List.length_append]; omega
  rcases appendArrProg_exec inArr 24 30 14 15 20
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (x.G.enc ++ x.W.encList) crossed_flat hGW_all_w hc_all_w hw1 htot91_w (s := s₅)
      (by simp [s₅, hin₄])
      (by simp [s₅, harr24_4])
      (by simp [s₅, List.length_append, hr14_4])
      rfl with
    ⟨s₆, t₆, hex₆, ht₆, hin₆, _, _, _⟩
  rw [List.length_append] at ht₆
  -- 7. P91
  let x91 := buildAlg91InputOfCrosses (p := p) h2 he hr₂ x X I hI_div entries_c hmc hmem_c
  have hin₆' : s₆.arrs inArr = encAlg91In x91 := by
    rw [hin₆, encAlg91In_buildAlg91InputOfCrosses]
  rcases hexec91 x91 rfl rfl s₆ hin₆' with
    ⟨s₇, t₇, hex₇, ht₇, K, hout₇, hK_mod⟩
  rw [alg91Size_buildAlg91InputOfCrosses] at ht₇
  -- 8. copyArrLoopProg outArr 26 14 15
  have hK_len : (encBitSetsUpTo K p).length = p * x.n := length_encBitSetsUpTo K p le_rfl
  have hK_len_w : (encBitSetsUpTo K p).length < 2 ^ w := by rw [hK_len]; omega
  have hK_all_w : ∀ v ∈ encBitSetsUpTo K p, v < 2 ^ w := all_lt_encBitSetsUpTo K hw1 p le_rfl
  rcases copyArrLoopProg_exec outArr 26 14 15
      (by decide) (by decide) hw1 s₇
      (by rw [hout₇]; exact hK_len_w)
      (by rw [hout₇]; exact hK_all_w) with
    ⟨s₈, t₈, hex₈, ht₈, harr26_8, _, _⟩
  rw [hout₇, hK_len] at ht₈
  rw [hout₇] at harr26_8
  -- 9. reg 14 := len 26
  let s₉ := s₈.setReg 14 (encBitSetsUpTo K p).length
  have hex₉ : Exec w (.assign 14 (.len 26)) s₈ s₉ 2 :=
    .assign (by simp only [Expr.eval, checkWord, harr26_8, hK_len_w, ↓reduceIte])
  -- 10. prependWordProg (.const 0) 26 outArr 14 20
  rcases prependWordProg_exec (tag := 0) (.const 0) 26 outArr 14 20
      (by decide) (by decide)
      (encBitSetsUpTo K p) hK_all_w hw1
      (by rw [hK_len]; exact hmod_w) (s := s₉)
      (fun _ => by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₉, harr26_8]) rfl with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hout₁₀, _, _⟩
  dsimp [Expr.cost] at ht₁₀
  rw [hK_len] at ht₁₀
  have h52_W : 52 * x.W.encList.length ≤ 52 * maxWallEncLen h' x.n :=
    Nat.mul_le_mul_left 52 hW_len_le
  have h18_c : 18 * crossed_flat.length ≤ 18 * (k₂ * maxCrossedBlockLen h x.n) :=
    Nat.mul_le_mul_left 18 hc_len
  refine ⟨s₁₀,
    t₁ + (2 + (2 + (t₄ + (2 + (t₆ + (t₇ + (t₈ + (2 + t₁₀)))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
      (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ hex₁₀)))))))),
    by dsimp [alg97CrossedBranchCost, h'] at *; rw [hG_len] at ht₁ ht₄ ht₆; omega,
    Or.inl ⟨K, hout₁₀, hK_mod⟩⟩

/-! ### Section 3: Dividing Subwall Branch (`alg97DividingBranchProg`) -/

/-- Branch of Algorithm (9.7) when `outArr[0] ≠ 0` after `P94`:
1. Unpacks `bitSetList X` into `arr 16` and `arr 17` and `indI` into `arr 18`,
2. Copies `a_G` to `arr 9`, `a_W` to `arr 10`, and `a_WV` to `arr 11`,
3. Runs `buildWallUnionCsrProg h' (B_arr + 4)`,
4. Copies `a_sub` to `arr 16`, sets `reg 1 := x.n` and `reg 2 := len 22`,
5. Runs `alg97ScanSubwallsProg t h h2 shiloachProg k₂ s_goal`,
6. Branches on `reg 11 < k₂` between `alg97FlatBranchProg` and `alg97CrossedBranchProg P91`. -/
def alg97DividingBranchProg (p t r h : ℕ) (h2 : 2 ≤ h)
    (shiloachProg P91 : Cmd) (k₂ s_goal B_arr B_reg : ℕ) : Cmd :=
  let h' := alg97WallHeight p t r h
  .seq (.assign 14 (.reg B_reg))
    (.seq (readSliceProg outArr (.const 1) 16 (.reg 14) 20)
      (.seq (copyArrLoopProg 16 17 14 15)
        (.seq (.assign 14 (.const t))
          (.seq (.assign 15 (.op .add (.const 1) (.reg B_reg)))
            (.seq (readSliceProg outArr (.reg 15) 18 (.reg 14) 20)
              (.seq (copyArrLoopProg B_arr 9 14 15)
                (.seq (copyArrLoopProg (B_arr + 1) 10 14 15)
                  (.seq (copyArrLoopProg (B_arr + 2) 11 14 15)
                    (.seq (buildWallUnionCsrProg h' (B_arr + 4))
                      (.seq (copyArrLoopProg (B_arr + 3) 16 14 15)
                        (.seq (.assign 1 (.reg B_reg))
                          (.seq (.assign 2 (.len 22))
                            (.seq (alg97ScanSubwallsProg t h h2 shiloachProg k₂ s_goal)
                              (.ite (.op .lt (.reg 11) (.const k₂))
                                alg97FlatBranchProg
                                (alg97CrossedBranchProg P91)))))))))))))))

/-- Cost bound for `alg97DividingBranchProg`. -/
def alg97DividingBranchCost (p t r h k₂ s_goal B_arr n m_act e_edges C_sh C₉₁ : ℕ) : ℕ :=
  let h' := alg97WallHeight p t r h
  let exprCost := (isWallUnionEdgeExpr h' (B_arr + 4) 16 (3 + 6) (3 + 7)).cost
  500 + 138 * n + 16 * t + 15 * (2 + 3 * m_act) + 15 * maxWallEncLen h' n +
    (291 + exprCost) * m_act + 15 * (t * maxWallEncLen h n) +
    t * alg97ScanStepCost h n k₂ s_goal (2 * e_edges) (2 * e_edges) e_edges C_sh +
    36 * (s_goal * maxWallEncLen h n) +
    alg97CrossedBranchCost p t r h k₂ n m_act e_edges C₉₁

private lemma alg97_div_total_bound
    {t₁ t₂ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₃ t₁₄ n t s_goal m_act mw' mw exprCost scanStep cbc : ℕ}
    (ht₁ : t₁ ≤ 16 * n + 8 + 1)
    (ht₂ : t₂ ≤ 8 + 15 * n)
    (ht₅ : t₅ ≤ 16 * t + 8 + 1)
    (ht₆ : t₆ ≤ 8 + 15 * (2 + 3 * m_act))
    (ht₇ : t₇ ≤ 8 + 15 * mw')
    (ht₈ : t₈ ≤ 8 + 15 * n)
    (ht₉ : t₉ ≤ 187 + 23 * n + (291 + exprCost) * m_act)
    (ht₁₀ : t₁₀ ≤ 8 + 15 * (t * mw))
    (ht₁₃ : t₁₃ ≤ 10 + t * scanStep)
    (ht₁₄ : t₁₄ ≤ (100 + 68 * n + 36 * (s_goal * mw)) + cbc) :
    2 + (t₁ + (t₂ + (2 + (4 + (t₅ + (t₆ + (t₇ + (t₈ + (t₉ + (t₁₀ +
      (2 + (2 + (t₁₃ + (3 + t₁₄)))))))))))))) ≤
      500 + 138 * n + 16 * t + 15 * (2 + 3 * m_act) + 15 * mw' +
        (291 + exprCost) * m_act + 15 * (t * mw) + t * scanStep +
        36 * (s_goal * mw) + cbc := by
  omega

theorem alg97ScanStepCost_mono {h n k₂ s_goal cap₁ cap₂ m₁ m₂ e₁ e₂ C_sh : ℕ}
    (hcap : cap₁ ≤ cap₂) (hm : m₁ ≤ m₂) (he : e₁ ≤ e₂) :
    alg97ScanStepCost h n k₂ s_goal cap₁ m₁ e₁ C_sh ≤
      alg97ScanStepCost h n k₂ s_goal cap₂ m₂ e₂ C_sh := by
  unfold alg97ScanStepCost
  have hsh : C_sh * (n + 1) * (e₁ + n + 1) ≤ C_sh * (n + 1) * (e₂ + n + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

set_option maxHeartbeats 800000 in
theorem alg97DividingBranchProg_exec {w p s_goal k₁ k₂ r₂ t r h B_arr B_reg C_sh c_sh C₉₁ : ℕ}
    {shiloachProg P91 : Cmd}
    (h2 : 2 ≤ h) (he : Even h) (hr₂ : r₂ ≤ r)
    (ht_eq : t = s_goal + k₁ + k₂ + p.choose 2)
    (hB_arr : 50 ≤ B_arr) (hB_reg : 30 ≤ B_reg)
    (hShiloachProg :
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
        (lists : Fin N → List ℕ) (s₁ t₁ s₂ t₂ : Fin N),
        s₁ ≠ t₁ → s₁ ≠ s₂ → s₁ ≠ t₂ → t₁ ≠ s₂ → t₁ ≠ t₂ → s₂ ≠ t₂ →
        ∀ (w : ℕ), wordSize c_sh ((N + 1) * (G.edgeFinset.card + N + 1)) ≤ w →
        ∀ (s : State),
          IsAdjList G 30 31 32 lists s →
          (s.arrs 32).length < 2 ^ w →
          s.regs 30 = N →
          s.regs 31 = s₁.1 →
          s.regs 32 = t₁.1 →
          s.regs 33 = s₂.1 →
          s.regs 34 = t₂.1 →
          ∃ (s' : State) (t : ℕ),
            Exec w shiloachProg s s' t ∧
            t ≤ C_sh * (N + 1) * (G.edgeFinset.card + N + 1) ∧
            (∀ r < 30, s'.regs r = s.regs r) ∧
            (∀ a < 33, s'.arrs a = s.arrs a) ∧
            ((s'.regs 35 = 1 ∧
                ∃ (P₁ : G.Walk s₁ t₁) (P₂ : G.Walk s₂ t₂),
                  P₁.IsPath ∧ P₂.IsPath ∧
                  List.Disjoint P₁.support P₂.support ∧
                  s'.arrs 33 = P₁.support.map Fin.val ∧
                  s'.arrs 34 = P₂.support.map Fin.val) ∨
              (s'.regs 35 = 0 ∧
                ∀ (P₁ : G.Walk s₁ t₁) (P₂ : G.Walk s₂ t₂),
                  P₁.IsPath → P₂.IsPath → ¬ List.Disjoint P₁.support P₂.support)))
    (x : Alg97Input (alg97WallHeight p t r h))
    (hexec91 : ∀ (x91 : Alg91Input p (alg97WallHeight p t r h) k₂ r₂),
      x91.n = x.n → x91.G.numEdges = x.G.numEdges →
      ∀ (s : State), s.arrs inArr = encAlg91In x91 →
      ∃ s' time,
        Exec w P91 s s' time ∧
        time ≤ C₉₁ * alg91Size x91 ∧
        IsAlg91Output p x91 (s'.arrs outArr))
    (X : Finset (Fin x.n)) (I : Finset (Fin t))
    (hX_card : X.card < p.choose 2) (hI_card : t - k₁ ≤ I.card)
    (hI_div : ∀ idx ∈ I,
      (x.W.castGraph (WallOfHeight.wallUnionMultiDigraph x.G X x.W)).IsDividingSubwall
        ((alg97Subwall h2 he x.W idx).castGraph (WallOfHeight.wallUnionMultiDigraph x.G X x.W)))
    (hw_sh : wordSize c_sh (alg97Size x) ≤ w)
    (hw_bound :
      (2 + 3 * x.G.numActivePairs) +
      maxWallEncLen (alg97WallHeight p t r h) x.n +
      (t + s_goal + k₂ + 2) * maxCrossedBlockLen h x.n +
      (1 + p * x.n) +
      3 + 2 * elemWallNumVerts (alg97WallHeight p t r h) +
      alg97WallHeight p t r h + x.n + 2 * x.G.numEdges < 2 ^ w)
    {s : State}
    (hout : s.arrs outArr =
      1 :: (bitSetList X ++ (List.finRange t).map (fun idx => if idx ∈ I then 1 else 0)))
    (hrB : s.regs B_reg = x.n)
    (harrG : s.arrs B_arr = x.G.enc)
    (harrW : s.arrs (B_arr + 1) = x.W.encList)
    (hWV : IsBitSet x.W.vertexFinset (B_arr + 2) s)
    (harrSub : s.arrs (B_arr + 3) =
      (List.finRange t).flatMap (fun a => (alg97Subwall h2 he x.W a).encList))
    (hsucc : IsWallSuccArrs x.W (B_arr + 4) s) :
    ∃ s' time,
      Exec w (alg97DividingBranchProg p t r h h2 shiloachProg P91 k₂ s_goal B_arr B_reg) s s' time ∧
      time ≤ alg97DividingBranchCost p t r h k₂ s_goal B_arr
        x.n x.G.numActivePairs x.G.numEdges C_sh C₉₁ ∧
      IsAlg97Output p s_goal h (alg97WallHeight p t r h) x (s'.arrs outArr) := by
  let h' := alg97WallHeight p t r h
  let h2' := two_le_alg97WallHeight p t r h
  let he' := even_alg97WallHeight p t r h
  let indI := (List.finRange t).map (fun idx => if idx ∈ I then 1 else 0)
  let sub_flat := (List.finRange t).flatMap (fun a => (alg97Subwall h2 he x.W a).encList)
  let G' := WallOfHeight.wallUnionMultiDigraph x.G X x.W
  let W' := x.W.castGraph G'
  let W_sub' : Fin t → WallOfHeight h G' := fun idx => (alg97Subwall h2 he x.W idx).castGraph G'
  have hmax_pos : 1 ≤ maxCrossedBlockLen h x.n := maxCrossedBlockLen_pos h x.n
  have hmaxW_le_C : maxWallEncLen h x.n ≤ maxCrossedBlockLen h x.n := by
    unfold maxCrossedBlockLen; omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have hn1_w : x.n + 1 < 2 ^ w := by omega
  have hh'_w : h' < 2 ^ w := by dsimp [h']; omega
  have hh_le_h' : h ≤ alg97WallHeight p t r h := le_alg97WallHeight p t r h
  have helem_le : elemWallNumVerts h ≤ elemWallNumVerts (alg97WallHeight p t r h) := by
    rw [elemWallNumVerts_eq, elemWallNumVerts_eq]
    exact Nat.sub_le_sub_right
      (Nat.mul_le_mul (show h + 1 ≤ alg97WallHeight p t r h + 1 by omega)
        (show 2 * h + 2 ≤ 2 * alg97WallHeight p t r h + 2 by omega)) 2
  have hh_w : h < 2 ^ w := by omega
  have hc2'_w : 3 + 2 * elemWallNumVerts h' < 2 ^ w := by dsimp [h']; omega
  have hc2_w : 3 + 2 * elemWallNumVerts h < 2 ^ w := by omega
  have hm_w : x.G.numActivePairs < 2 ^ w := by omega
  have hm3_w : 2 + 3 * x.G.numActivePairs < 2 ^ w := by omega
  have he_w : x.G.numEdges < 2 ^ w := by
    have := Alg91.numActivePairs_le_numEdges x.G; omega
  have ht2_le : t + 1 < (t + s_goal + k₂ + 2) * maxCrossedBlockLen h x.n := by
    calc t + 1 < t + s_goal + k₂ + 2 := by omega
      _ = (t + s_goal + k₂ + 2) * 1 := (Nat.mul_one _).symm
      _ ≤ (t + s_goal + k₂ + 2) * maxCrossedBlockLen h x.n := Nat.mul_le_mul_left _ hmax_pos
  have ht_w : t < 2 ^ w := by omega
  have h1nt_w : 1 + x.n + t < 2 ^ w := by omega
  have h1n_w : 1 + x.n < 2 ^ w := by omega
  have hG_len : x.G.enc.length = 2 + 3 * x.G.numActivePairs := MultiDigraph.length_enc x.G
  have hW_len_le : x.W.encList.length ≤ maxWallEncLen h' x.n := by
    have ha := Alg91.length_encList_le_of_isValid x.hW_valid.2.2
    have hb := length_elemWallEdges_le h'
    unfold maxWallEncLen; dsimp [h'] at hb ⊢; omega
  have hsub_len_le : sub_flat.length ≤ t * maxWallEncLen h x.n := by
    have hsub : ∀ xs : List (Fin t),
        (xs.flatMap (fun j => (alg97Subwall h2 he x.W j).encList)).length ≤
          xs.length * maxWallEncLen h x.n := by
      intro xs
      induction xs with
      | nil => simp
      | cons j xs ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        have hj : (alg97Subwall h2 he x.W j).encList.length ≤ maxWallEncLen h x.n := by
          have ha := Alg91.length_encList_le_of_isValid (alg97Subwall_isValid h2 he x.hW_valid.2.2 j)
          have hb := length_elemWallEdges_le h
          unfold maxWallEncLen; omega
        rw [Nat.add_one_mul]; omega
    simpa [sub_flat] using hsub (List.finRange t)
  have hX_all_w : ∀ v ∈ bitSetList X, v < 2 ^ w := all_lt_bitSetList X hw1
  have hindI_all_w : ∀ v ∈ indI, v < 2 ^ w := by
    intro v hv; dsimp [indI] at hv; rw [List.mem_map] at hv
    rcases hv with ⟨_, _, rfl⟩; split_ifs <;> omega
  -- 1. reg 14 := reg B_reg (x.n)
  let s₀ := s.setReg 14 x.n
  have hex₀ : Exec w (.assign 14 (.reg B_reg)) s s₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrB, hn_w])
  -- 2. readSliceProg outArr (.const 1) 16 (.reg 14) 20
  rcases readSliceProg_exec_full outArr 16 (.const 1) 14 20
      (by decide) (by decide) [1] (bitSetList X) indI
      rfl (length_bitSetList X) hX_all_w hw1 (by simp; exact h1n_w) (s := s₀)
      (by simp [Expr.eval, checkWord, hw1])
      (by dsimp [s₀, indI]; rw [hout])
      rfl with
    ⟨s₁, t₁, hex₁, ht₁, harr16_1, harr₁, hreg₁⟩
  dsimp [Expr.cost] at ht₁
  -- 3. copyArrLoopProg 16 17 14 15
  rcases copyArrLoopProg_exec 16 17 14 15
      (by decide) (by decide) hw1 s₁
      (by rw [harr16_1, length_bitSetList]; exact hn_w)
      (by rw [harr16_1]; exact hX_all_w) with
    ⟨s₂, t₂, hex₂, ht₂, harr17_2, harr₂, hreg₂⟩
  rw [harr16_1, length_bitSetList] at ht₂
  rw [harr16_1] at harr17_2
  -- 4. reg 14 := t
  let s₃ := s₂.setReg 14 t
  have hex₃ : Exec w (.assign 14 (.const t)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, ht_w])
  -- 5. reg 15 := 1 + reg B_reg
  have hrB_3 : s₃.regs B_reg = x.n := by
    simp only [s₃]
    rw [State.setReg_regs_ne _ _ (ne_reg_of_ne (by omega)),
      hreg₂ B_reg (ne_reg_of_ne (by omega)) (ne_reg_of_ne (by omega)),
      hreg₁ B_reg (Or.inr (by omega))]
    dsimp only [s₀]
    rw [State.setReg_regs_ne _ _ (ne_reg_of_ne (by omega))]
    exact hrB
  let s₄ := s₃.setReg 15 (1 + x.n)
  have hex₄ : Exec w (.assign 15 (.op .add (.const 1) (.reg B_reg))) s₃ s₄ 4 :=
    .assign (by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrB_3, hw1, hn_w, h1n_w])
  -- 6. readSliceProg outArr (.reg 15) 18 (.reg 14) 20
  have hout_4 : s₄.arrs outArr = (1 :: bitSetList X) ++ indI ++ [] := by
    simp only [s₄, s₃, State.setReg_arrs]
    rw [harr₂ outArr (by decide), harr₁ outArr (by decide)]
    dsimp [s₀, indI]; rw [hout]; simp
  rcases readSliceProg_exec_full outArr 18 (.reg 15) 14 20
      (by decide) (by decide) (1 :: bitSetList X) indI []
      (by simp [length_bitSetList, Nat.add_comm])
      (by simp [indI]) hindI_all_w hw1 h1nt_w (s := s₄)
      (by simp only [s₄, Expr.eval, checkWord, State.setReg_regs_self, h1n_w, ↓reduceIte])
      hout_4
      (by simp [s₄, s₃]) with
    ⟨s₅, t₅, hex₅, ht₅, harr18_5, harr₅, hreg₅⟩
  dsimp [Expr.cost] at ht₅
  -- Helper for array preservation at s₅ for a ∉ {16, 17, 18}
  have harr₅_ne : ∀ a : ℕ, a ≠ 16 → a ≠ 17 → a ≠ 18 → s₅.arrs a = s.arrs a := by
    intro a ha16 ha17 ha18
    rw [harr₅ a ha18]
    simp only [s₄, s₃, State.setReg_arrs]
    rw [harr₂ a (ne_arr_of_ne ha17), harr₁ a ha16]
    rfl
  -- 7. copyArrLoopProg B_arr 9 14 15
  have harrG_5 : s₅.arrs B_arr = x.G.enc := by
    rw [harr₅_ne B_arr (by omega) (by omega) (by omega)]; exact harrG
  have hG_all_w : ∀ v ∈ x.G.enc, v < 2 ^ w := all_lt_enc_multiDigraph x.G hn_w hm_w he_w
  rcases copyArrLoopProg_exec B_arr 9 14 15
      (ne_arr_of_ne (by omega)) (by decide) hw1 s₅
      (by rw [harrG_5, hG_len]; exact hm3_w)
      (by rw [harrG_5]; exact hG_all_w) with
    ⟨s₆, t₆, hex₆, ht₆, harr9_6, harr₆, hreg₆⟩
  rw [harrG_5, hG_len] at ht₆
  rw [harrG_5] at harr9_6
  -- 8. copyArrLoopProg (B_arr + 1) 10 14 15
  have harrW_6 : s₆.arrs (B_arr + 1) = x.W.encList := by
    rw [harr₆ (B_arr + 1) (ne_arr_of_ne (by omega)),
      harr₅_ne (B_arr + 1) (by omega) (by omega) (by omega)]
    exact harrW
  have hW_all_w : ∀ v ∈ x.W.encList, v < 2 ^ w :=
    all_lt_encList_of_isValid x.W x.hW_valid.2.2 le_rfl hh'_w hc2'_w hn_w
  have hW_len_w : x.W.encList.length < 2 ^ w := by dsimp [h'] at hW_len_le; omega
  rcases copyArrLoopProg_exec (B_arr + 1) 10 14 15
      (ne_arr_of_ne (by omega)) (by decide) hw1 s₆
      (by rw [harrW_6]; exact hW_len_w)
      (by rw [harrW_6]; exact hW_all_w) with
    ⟨s₇, t₇, hex₇, ht₇, harr10_7, harr₇, hreg₇⟩
  rw [harrW_6] at ht₇ harr10_7
  -- 9. copyArrLoopProg (B_arr + 2) 11 14 15
  have harrWV_7 : s₇.arrs (B_arr + 2) = s.arrs (B_arr + 2) := by
    rw [harr₇ (B_arr + 2) (ne_arr_of_ne (by omega)),
      harr₆ (B_arr + 2) (ne_arr_of_ne (by omega)),
      harr₅_ne (B_arr + 2) (by omega) (by omega) (by omega)]
  have hWV_7 : IsBitSet x.W.vertexFinset (B_arr + 2) s₇ := hWV.of_arr_eq harrWV_7
  rcases copyArrLoopProg_exec (B_arr + 2) 11 14 15
      (ne_arr_of_ne (by omega)) (by decide) hw1 s₇
      (by rw [hWV_7.1]; exact hn_w)
      (hWV_7.all_lt hw1) with
    ⟨s₈, t₈, hex₈, ht₈, harr11_8, harr₈, hreg₈⟩
  rw [hWV_7.1] at ht₈
  have hWV_8 : IsBitSet x.W.vertexFinset 11 s₈ := hWV_7.of_arr_eq' harr11_8
  -- Helper for array preservation at s₈ for a ∉ {9, 10, 11, 16, 17, 18}
  have harr₈_ne : ∀ a : ℕ,
      a ≠ 9 → a ≠ 10 → a ≠ 11 → a ≠ 16 → a ≠ 17 → a ≠ 18 → s₈.arrs a = s.arrs a := by
    intro a ha9 ha10 ha11 ha16 ha17 ha18
    rw [harr₈ a (ne_arr_of_ne ha11), harr₇ a (ne_arr_of_ne ha10), harr₆ a (ne_arr_of_ne ha9)]
    exact harr₅_ne a ha16 ha17 ha18
  -- 10. buildWallUnionCsrProg h' (B_arr + 4)
  have harr9_8 : s₈.arrs 9 = x.G.enc := by
    rw [harr₈ 9 (by decide), harr₇ 9 (by decide)]; exact harr9_6
  have harr16_8 : s₈.arrs 16 = bitSetList X := by
    rw [harr₈ 16 (by decide), harr₇ 16 (by decide), harr₆ 16 (by decide), harr₅ 16 (by decide)]
    simp only [s₄, s₃, State.setReg_arrs]
    rw [harr₂ 16 (by decide)]; exact harr16_1
  have hX_8 : IsBitSet X 16 s₈ := IsBitSet.of_bitSetList X 16 s₈ harr16_8
  have hsucc_8 : IsWallSuccArrs x.W (B_arr + 4) s₈ :=
    hsucc.of_arrs_eq (fun k =>
      harr₈_ne (B_arr + 4 + k.1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  rcases buildWallUnionCsrProg_exec x.G X x.W x.hW_valid.2.2 (B_arr + 4) (by omega)
      hw3 hn1_w hm3_w he_w harr9_8 hX_8 hsucc_8 with
    ⟨s₉, t₉, hex₉, ht₉, _, hadj₉, hent₉, htot₉, harr₉, hreg₉⟩
  -- 11. copyArrLoopProg (B_arr + 3) 16 14 15
  have harrSub_9 : s₉.arrs (B_arr + 3) = sub_flat := by
    rw [harr₉ (B_arr + 3) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      harr₈_ne (B_arr + 3) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact harrSub
  have hsub_all_w : ∀ v ∈ sub_flat, v < 2 ^ w := by
    intro v hv; dsimp [sub_flat] at hv; rw [List.mem_flatMap] at hv
    rcases hv with ⟨j, _, hvj⟩
    exact all_lt_encList_of_isValid (alg97Subwall h2 he x.W j)
      (alg97Subwall_isValid h2 he x.hW_valid.2.2 j)
      le_rfl hh_w hc2_w hn_w v hvj
  have hsub_len_w : sub_flat.length < 2 ^ w := by
    have : t * maxWallEncLen h x.n ≤ (t + s_goal + k₂ + 2) * maxCrossedBlockLen h x.n :=
      Nat.mul_le_mul (by omega) hmaxW_le_C
    omega
  rcases copyArrLoopProg_exec (B_arr + 3) 16 14 15
      (ne_arr_of_ne (by omega)) (by decide) hw1 s₉
      (by rw [harrSub_9]; exact hsub_len_w)
      (by rw [harrSub_9]; exact hsub_all_w) with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, harr16_10, harr₁₀, hreg₁₀⟩
  rw [harrSub_9] at ht₁₀ harr16_10
  -- 12. reg 1 := reg B_reg
  have hrB_10 : s₁₀.regs B_reg = x.n := by
    rw [hreg₁₀ B_reg (ne_reg_of_ne (by omega)) (ne_reg_of_ne (by omega)),
      hreg₉ B_reg (Or.inr (by omega)),
      hreg₈ B_reg (ne_reg_of_ne (by omega)) (ne_reg_of_ne (by omega)),
      hreg₇ B_reg (ne_reg_of_ne (by omega)) (ne_reg_of_ne (by omega)),
      hreg₆ B_reg (ne_reg_of_ne (by omega)) (ne_reg_of_ne (by omega)),
      hreg₅ B_reg (Or.inr (by omega))]
    dsimp only [s₄]
    rw [State.setReg_regs_ne _ _ (ne_reg_of_ne (by omega))]
    exact hrB_3
  let s₁₁ := s₁₀.setReg 1 x.n
  have hex₁₁ : Exec w (.assign 1 (.reg B_reg)) s₁₀ s₁₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrB_10, hn_w])
  -- 13. reg 2 := len 22
  let cap := 2 * G'.toSimpleGraph.edgeFinset.card
  have he_card_le : G'.toSimpleGraph.edgeFinset.card ≤ x.G.numEdges :=
    le_trans (edgeFinset_card_toSimpleGraph_le_numEdges G')
      (WallOfHeight.wallUnionMultiDigraph_numEdges_le x.G X x.W)
  have hcap_le : cap ≤ 2 * x.G.numEdges := Nat.mul_le_mul_left 2 he_card_le
  have hcap_w : cap < 2 ^ w := by omega
  have hent_11 : (s₁₁.arrs 22).length = cap := by
    simp only [s₁₁, State.setReg_arrs]
    rw [harr₁₀ 22 (by decide)]; exact hent₉
  let s₁₂ := s₁₁.setReg 2 cap
  have hex₁₂ : Exec w (.assign 2 (.len 22)) s₁₁ s₁₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hent_11, hcap_w, ↓reduceIte])
  -- 14. alg97ScanSubwallsProg t h h2 shiloachProg k₂ s_goal
  have hW'_valid : W'.IsValid :=
    WallOfHeight.isValid_castGraph_wallUnionMultiDigraph X x.hW_valid.2.2
  have hsub' : ∀ idx : Fin t, (W_sub' idx).IsSubwallOf W' := by
    intro idx
    dsimp [W_sub', W']
    rw [alg97Subwall_castGraph h2 he G' x.W idx]
    exact alg97Subwall_isSubwallOf h2 he W' idx
  have hw_sh' : wordSize c_sh ((x.n + 1) * (G'.toSimpleGraph.edgeFinset.card + x.n + 1)) ≤ w := by
    have hle_sz : (x.n + 1) * (G'.toSimpleGraph.edgeFinset.card + x.n + 1) ≤ alg97Size x :=
      Nat.mul_le_mul_left (x.n + 1) (by omega)
    exact le_trans (wordSize_mono_right c_sh hle_sz) hw_sh
  have hw_scan_bound :
      (t + s_goal + k₂ + 2) * maxCrossedBlockLen h x.n +
        3 + 2 * elemWallNumVerts h + h + x.n + cap < 2 ^ w := by
    omega
  have hadj₁₂ : IsAdjList G'.toSimpleGraph 20 21 22 (edgeNeighbors (edgeListOf G'.toSimpleGraph)) s₁₂ :=
    hadj₉.of_arrs_eq
      (by simp [s₁₂, s₁₁, harr₁₀ 20 (by decide)])
      (by simp [s₁₂, s₁₁, harr₁₀ 21 (by decide)])
      (by simp [s₁₂, s₁₁, harr₁₀ 22 (by decide)])
  have hWV₁₂ : IsBitSet W'.vertexFinset 11 s₁₂ :=
    hWV_8.of_arr_eq (by
      simp only [s₁₂, s₁₁, State.setReg_arrs]
      rw [harr₁₀ 11 (by decide),
        harr₉ 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
  have harr17_12 : s₁₂.arrs 17 = bitSetList X := by
    simp only [s₁₂, s₁₁, State.setReg_arrs]
    rw [harr₁₀ 17 (by decide),
      harr₉ 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      harr₈ 17 (by decide), harr₇ 17 (by decide), harr₆ 17 (by decide), harr₅ 17 (by decide)]
    simp [s₄, s₃, harr17_2]
  have hX₁₂ : IsBitSet X 17 s₁₂ := IsBitSet.of_bitSetList X 17 s₁₂ harr17_12
  have harr16_12 : s₁₂.arrs 16 = (List.finRange t).flatMap (fun idx => (W_sub' idx).encList) := by
    simp [s₁₂, s₁₁, harr16_10, sub_flat, W_sub']
  have harr18_12 : s₁₂.arrs 18 = indI := by
    simp only [s₁₂, s₁₁, State.setReg_arrs]
    rw [harr₁₀ 18 (by decide),
      harr₉ 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      harr₈ 18 (by decide), harr₇ 18 (by decide), harr₆ 18 (by decide)]
    exact harr18_5
  have harr9_12 : s₁₂.arrs 9 = x.G.enc := by
    simp only [s₁₂, s₁₁, State.setReg_arrs]
    rw [harr₁₀ 9 (by decide),
      harr₉ 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact harr9_8
  have harr10_12 : s₁₂.arrs 10 = x.W.encList := by
    simp only [s₁₂, s₁₁, State.setReg_arrs]
    rw [harr₁₀ 10 (by decide),
      harr₉ 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      harr₈ 10 (by decide)]
    exact harr10_7
  rcases alg97ScanSubwallsProg_exec hShiloachProg G' (edgeNeighbors (edgeListOf G'.toSimpleGraph))
      W' W_sub' X I h2 he h2' he' hW'_valid hsub' hw_sh' hw_scan_bound
      (le_of_eq htot₉) hadj₁₂ (by simp [s₁₂, hent_11, hcap_w])
      hWV₁₂ hX₁₂ harr16_12 harr18_12 (by simp [s₁₂, s₁₁]) rfl with
    ⟨s₁₃, t₁₃, hex₁₃, ht₁₃, hinv₁₃, harr₁₃, hr1_13, _⟩
  rw [htot₉] at ht₁₃
  have hstep_cost_le :
      alg97ScanStepCost h x.n k₂ s_goal cap (2 * G'.toSimpleGraph.edgeFinset.card)
        G'.toSimpleGraph.edgeFinset.card C_sh ≤
      alg97ScanStepCost h x.n k₂ s_goal (2 * x.G.numEdges) (2 * x.G.numEdges) x.G.numEdges C_sh :=
    alg97ScanStepCost_mono hcap_le hcap_le he_card_le
  have ht₁₃' :
      t₁₃ ≤ 10 + t * alg97ScanStepCost h x.n k₂ s_goal
        (2 * x.G.numEdges) (2 * x.G.numEdges) x.G.numEdges C_sh :=
    le_trans ht₁₃ (Nat.add_le_add_left (Nat.mul_le_mul_left t hstep_cost_le) 10)
  have h15_W : 15 * x.W.encList.length ≤ 15 * maxWallEncLen h' x.n :=
    Nat.mul_le_mul_left 15 hW_len_le
  have h15_sub : 15 * sub_flat.length ≤ 15 * (t * maxWallEncLen h x.n) :=
    Nat.mul_le_mul_left 15 hsub_len_le
  have ht₇' : t₇ ≤ 8 + 15 * maxWallEncLen h' x.n := by omega
  have ht₁₀' : t₁₀ ≤ 8 + 15 * (t * maxWallEncLen h x.n) := by omega
  -- 15. Outcome at j = t and branch on reg 11 < k₂
  have hdisj_sub' : ∀ j₁ j₂ : Fin t, j₁ ≠ j₂ →
      Disjoint (W_sub' j₁).vertexFinset (W_sub' j₂).vertexFinset := by
    intro j₁ j₂ hj
    dsimp [W_sub']
    exact alg97Subwall_disjoint_vertexFinset h2 he x.hW_valid.2.2 hj
  have hout_scan :=
    hinv₁₃.outcome_at_end ht_eq hI_card hX_card hdisj_sub'
  have hk₂_w : k₂ < 2 ^ w := by
    have : k₂ < (t + s_goal + k₂ + 2) * maxCrossedBlockLen h x.n := by
      calc k₂ < t + s_goal + k₂ + 2 := by omega
        _ = (t + s_goal + k₂ + 2) * 1 := (Nat.mul_one _).symm
        _ ≤ (t + s_goal + k₂ + 2) * maxCrossedBlockLen h x.n := Nat.mul_le_mul_left _ hmax_pos
    omega
  rcases hout_scan with ⟨hr11_13, entries_c, hmc, hmem_c, harr24_13⟩ |
      ⟨hr11_lt, _, idx_f, hmf, hval_f, harr25_13⟩
  · -- Crossed outcome (s₁₃.regs 11 = k₂, so reg 11 < k₂ is false)
    have heval_lt : (Expr.op .lt (.reg 11) (.const k₂)).eval w s₁₃ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11_13, hk₂_w, h0_w]
    have hin91_w :
        (2 + 3 * x.G.numActivePairs) + maxWallEncLen h' x.n + k₂ * maxCrossedBlockLen h x.n <
          2 ^ w := by
      have : k₂ * maxCrossedBlockLen h x.n ≤ (t + s_goal + k₂ + 2) * maxCrossedBlockLen h x.n :=
        Nat.mul_le_mul_right _ (by omega)
      dsimp [h'] at *; omega
    rcases alg97CrossedBranchProg_exec h2 he hr₂ x X I hI_div entries_c hmc hmem_c
        hexec91 hw1 hn1_w hh'_w hc2'_w hm_w he_w hin91_w (by omega)
        (by rw [harr₁₃ 9 (by decide)]; exact harr9_12)
        (by rw [harr₁₃ 10 (by decide)]; exact harr10_12)
        harr24_13 with
      ⟨s₁₄, t₁₄, hex₁₄, ht₁₄, hout₁₄⟩
    have hex_ite :
        Exec w (.ite (.op .lt (.reg 11) (.const k₂)) alg97FlatBranchProg (alg97CrossedBranchProg P91))
          s₁₃ s₁₄ (3 + t₁₄) :=
      .ite_false heval_lt hex₁₄
    refine ⟨s₁₄,
      2 + (t₁ + (t₂ + (2 + (4 + (t₅ + (t₆ + (t₇ + (t₈ + (t₉ + (t₁₀ +
        (2 + (2 + (t₁₃ + (3 + t₁₄)))))))))))))),
      .seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
        (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁
          (.seq hex₁₂ (.seq hex₁₃ hex_ite))))))))))))),
      alg97_div_total_bound ht₁ ht₂ ht₅ ht₆ ht₇' ht₈ ht₉ ht₁₀' ht₁₃'
        (Nat.le_add_left_of_le ht₁₄),
      hout₁₄⟩
  · -- Flat outcome (s₁₃.regs 11 < k₂, so reg 11 < k₂ is true)
    have hr11_w : s₁₃.regs 11 < 2 ^ w := by omega
    have heval_lt : (Expr.op .lt (.reg 11) (.const k₂)).eval w s₁₃ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11_w, hk₂_w, hr11_lt, hw1]
    have htot_out_w : 1 + (x.n + s_goal * maxWallEncLen h x.n) < 2 ^ w := by
      have : s_goal * maxWallEncLen h x.n ≤ (t + s_goal + k₂ + 2) * maxCrossedBlockLen h x.n :=
        Nat.mul_le_mul (by omega) hmaxW_le_C
      omega
    rcases alg97FlatBranchProg_exec h2 he x X hX_card I hI_div idx_f hmf hval_f
        hw1 hn_w hh_w hc2_w htot_out_w
        (by rw [harr₁₃ 17 (by decide)]; exact harr17_12)
        harr25_13 hr1_13 with
      ⟨s₁₄, t₁₄, hex₁₄, ht₁₄, hout₁₄⟩
    have hex_ite :
        Exec w (.ite (.op .lt (.reg 11) (.const k₂)) alg97FlatBranchProg (alg97CrossedBranchProg P91))
          s₁₃ s₁₄ (3 + t₁₄) :=
      .ite_true heval_lt (by omega) hex₁₄
    refine ⟨s₁₄,
      2 + (t₁ + (t₂ + (2 + (4 + (t₅ + (t₆ + (t₇ + (t₈ + (t₉ + (t₁₀ +
        (2 + (2 + (t₁₃ + (3 + t₁₄)))))))))))))),
      .seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
        (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁
           (.seq hex₁₂ (.seq hex₁₃ hex_ite))))))))))))),
      alg97_div_total_bound ht₁ ht₂ ht₅ ht₆ ht₇' ht₈ ht₉ ht₁₀' ht₁₃'
        (Nat.le_add_right_of_le ht₁₄),
      hout₁₄⟩

/-! ### Section 4: Complete Word RAM Program and Main Theorem (`gm13_algorithm_9_7`) -/

/-- Complete Word RAM program for **Algorithm (9.7)**:
1. Runs `alg97InitProg` to unpack `x.G.enc` and `x.W.encList`, extract the `t` canonical subwalls
   `alg97Subwall h2 he x.W`, and assemble `encAlg94In` in `inArr`,
2. Runs `P94`,
3. Reads `outArr[0]` into `reg 14`: if `reg 14 = 0`, returns `outArr` directly (`K_p` model);
   if `reg 14 ≠ 0`, runs `alg97DividingBranchProg`. -/
def alg97Prog (p t r h : ℕ) (h2 : 2 ≤ h)
    (shiloachProg P94 P91 : Cmd) (k₂ s_goal : ℕ) : Cmd :=
  let B_arr := alg97ArrBase P94
  let B_reg := alg97RegBase P94
  .seq (alg97InitProg p t r h h2 B_arr B_reg)
    (.seq P94
      (.seq (.assign 14 (.read outArr (.const 0)))
        (.ite (.reg 14)
          (alg97DividingBranchProg p t r h h2 shiloachProg P91 k₂ s_goal B_arr B_reg)
          .skip)))

/-- **Graph Minors XIII, (9.6) and Algorithm (9.7)** (Section 9, page 103):
For every `p, s ≥ 0` and even `h ≥ 2`, there exists an even height `h' ≥ p ^ 2 + 2` and a Word RAM
program `P` with running time `O(vε)` (`≤ C * alg97Size x`, where `C` depends only on `p, s, h`)
that computes an output satisfying `IsAlg97Output p s h h'`. -/
theorem gm13_algorithm_9_7
    (hShiloach : Shiloach80Statement)
    (h94 : Algorithm94Statement) :
    Algorithm97Statement := by
  intro p s_goal h h2 he
  obtain ⟨shiloachProg, C_sh, c_sh, _, _, hShiloachProg⟩ := hShiloach
  obtain ⟨k₁, r₁, h94_alg⟩ := h94 p
  obtain ⟨k₂, r₂, h91_alg⟩ := gm13_algorithm_9_1 p
  let r := max r₁ r₂
  have hr₁ : r₁ ≤ r := le_max_left r₁ r₂
  have hr₂ : r₂ ≤ r := le_max_right r₁ r₂
  let t := s_goal + k₁ + k₂ + p.choose 2
  let h' := alg97WallHeight p t r h
  have hp_sq : p ^ 2 + 2 ≤ h' := p_sq_add_two_le_alg97WallHeight p t r h
  have h2' : 2 ≤ h' := two_le_alg97WallHeight p t r h
  have he' : Even h' := even_alg97WallHeight p t r h
  obtain ⟨P94, hP94⟩ := h94_alg t h' h2' he'
  rcases hP94.subroutine_exec with ⟨C₉₄, c₉₄, _, _, hexec94⟩
  obtain ⟨P91, hP91⟩ := h91_alg h' h2' he'
  rcases hP91.subroutine_exec with ⟨C₉₁, c₉₁, _, _, hexec91⟩
  let B_arr := alg97ArrBase P94
  let B_reg := alg97RegBase P94
  have hB_arr : 50 ≤ B_arr := le_max_left 50 _
  have hB_arr94 : folioCallerArrBase P94 ≤ B_arr := le_max_right 50 _
  have hB_reg : 30 ≤ B_reg := le_max_left 30 _
  have hB_reg94 : folioCallerRegBase P94 ≤ B_reg := le_max_right 30 _
  let exprCost := (isWallUnionEdgeExpr h' (B_arr + 4) 16 (3 + 6) (3 + 7)).cost
  let C_init : ℕ := alg97InitFactor p t r h
  let C_cross : ℕ :=
    565 + 52 * (4 + 3 * elemWallNumVerts h') +
      18 * k₂ * (8 + 3 * elemWallNumVerts h) + C₉₁ + 33 * p
  let C_div : ℕ :=
    800 + 16 * t + 15 * (4 + 3 * elemWallNumVerts h') +
      (291 + exprCost) + 15 * t * (4 + 3 * elemWallNumVerts h) +
      t * alg97ScanFactor h k₂ s_goal C_sh +
      36 * s_goal * (4 + 3 * elemWallNumVerts h) + C_cross
  let C_total : ℕ := C_init + C₉₄ + C_div + 10
  let K_factor : ℕ :=
    5 + (4 + 3 * elemWallNumVerts h') +
      (t + s_goal + k₂ + 2) * (8 + 3 * elemWallNumVerts h) +
      (1 + p) + (3 + 2 * elemWallNumVerts h' + h') + 3
  let c_total : ℕ := c_sh + c₉₄ + c₉₁ + K_factor + 2
  refine ⟨alg97WallHeight p t r h, hp_sq, he', alg97Prog p t r h h2 shiloachProg P94 P91 k₂ s_goal,
    C_total, c_total, by omega, by omega, ?_⟩
  intro x s₀ hs₀
  let w := wordSize c_total (alg97Size x)
  have hmul_w : K_factor * (alg97Size x + 2) < 2 ^ w :=
    mul_lt_two_pow_wordSize_of_succ_le (A := K_factor) (c := c_total) (n := alg97Size x) (by omega)
  have hsz_pos : 1 ≤ alg97Size x := by
    unfold alg97Size
    have : 1 * 1 ≤ (x.n + 1) * (x.G.numEdges + x.n + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hn_le_sz : x.n ≤ alg97Size x := by
    unfold alg97Size
    have : (x.n + 1) * 1 ≤ (x.n + 1) * (x.G.numEdges + x.n + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hn1_le_sz : x.n + 1 ≤ alg97Size x := by
    unfold alg97Size
    have : (x.n + 1) * 1 ≤ (x.n + 1) * (x.G.numEdges + x.n + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have he1_le_sz : x.G.numEdges + x.n + 1 ≤ alg97Size x := by
    unfold alg97Size
    have : 1 * (x.G.numEdges + x.n + 1) ≤ (x.n + 1) * (x.G.numEdges + x.n + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have he_le_sz : x.G.numEdges ≤ alg97Size x := by omega
  have hm_le_sz : x.G.numActivePairs ≤ alg97Size x := by
    have := Alg91.numActivePairs_le_numEdges x.G; omega
  have hmw'_sz : maxWallEncLen h' x.n ≤ (4 + 3 * elemWallNumVerts h') * alg97Size x :=
    maxWallEncLen_le_mul h' x.n (alg97Size x) hsz_pos hn_le_sz
  have hmw_sz : maxWallEncLen h x.n ≤ (4 + 3 * elemWallNumVerts h) * alg97Size x :=
    maxWallEncLen_le_mul h x.n (alg97Size x) hsz_pos hn_le_sz
  have hmc_sz : maxCrossedBlockLen h x.n ≤ (8 + 3 * elemWallNumVerts h) * alg97Size x :=
    maxCrossedBlockLen_le_mul h x.n (alg97Size x) hsz_pos hn_le_sz
  have hw_bound :
      (2 + 3 * x.G.numActivePairs) +
      maxWallEncLen h' x.n +
      (t + s_goal + k₂ + 2) * maxCrossedBlockLen h x.n +
      (1 + p * x.n) +
      3 + 2 * elemWallNumVerts h' +
      h' + x.n + 2 * x.G.numEdges < 2 ^ w := by
    have h1 : 2 + 3 * x.G.numActivePairs ≤ 5 * alg97Size x := by omega
    have h2 :
        (t + s_goal + k₂ + 2) * maxCrossedBlockLen h x.n ≤
          (t + s_goal + k₂ + 2) * (8 + 3 * elemWallNumVerts h) * alg97Size x := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ hmc_sz
    have h3 : 1 + p * x.n ≤ (1 + p) * alg97Size x := by
      have ha : p * x.n ≤ p * alg97Size x := Nat.mul_le_mul_left p hn_le_sz
      rw [Nat.add_mul, Nat.one_mul]; omega
    have h4 : (3 + 2 * elemWallNumVerts h' + h') * 1 ≤
        (3 + 2 * elemWallNumVerts h' + h') * alg97Size x :=
      Nat.mul_le_mul_left _ hsz_pos
    have hK_exp : K_factor * alg97Size x =
        5 * alg97Size x +
        (4 + 3 * elemWallNumVerts h') * alg97Size x +
        (t + s_goal + k₂ + 2) * (8 + 3 * elemWallNumVerts h) * alg97Size x +
        (1 + p) * alg97Size x +
        (3 + 2 * elemWallNumVerts h' + h') * alg97Size x +
        3 * alg97Size x := by
      dsimp [K_factor]; ring
    have hle_mul : K_factor * alg97Size x ≤ K_factor * (alg97Size x + 2) :=
      Nat.mul_le_mul_left K_factor (by omega)
    omega
  have hmaxW_le_C : maxWallEncLen h x.n ≤ maxCrossedBlockLen h x.n := by
    unfold maxCrossedBlockLen; omega
  have ht_sub_le : t * maxWallEncLen h x.n ≤ (t + s_goal + k₂ + 2) * maxCrossedBlockLen h x.n :=
    Nat.mul_le_mul (by omega) hmaxW_le_C
  have ht_sub_w : t * maxWallEncLen h x.n < 2 ^ w := by omega
  have hin94_w : (encAlg94In (buildAlg94Input (k₁ := k₁) h2 he hr₁ x)).length < 2 ^ w := by
    have hin := length_encAlg94In_le (buildAlg94Input (k₁ := k₁) h2 he hr₁ x)
    dsimp [buildAlg94Input] at hin
    rw [Nat.add_mul, Nat.one_mul] at hin
    have hW_le : maxWallEncLen (alg97WallHeight p t r h) x.n = maxWallEncLen h' x.n := rfl
    have hsub_le : ∀ xs : List (Fin t),
        (xs.flatMap (fun j => (alg97Subwall h2 he x.W j).encList)).length ≤
          xs.length * maxWallEncLen h x.n := by
      intro xs
      induction xs with
      | nil => simp
      | cons j xs ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        have hj : (alg97Subwall h2 he x.W j).encList.length ≤ maxWallEncLen h x.n := by
          have ha := Alg91.length_encList_le_of_isValid (alg97Subwall_isValid h2 he x.hW_valid.2.2 j)
          have hb := length_elemWallEdges_le h
          unfold maxWallEncLen; omega
        rw [Nat.add_one_mul]; omega
    have htot94 : (encAlg94In (buildAlg94Input (k₁ := k₁) h2 he hr₁ x)).length ≤
        (2 + 3 * x.G.numActivePairs) + maxWallEncLen h' x.n + t * maxWallEncLen h x.n := by
      rw [encAlg94In_buildAlg94Input, List.length_append, List.length_append,
        MultiDigraph.length_enc]
      have hW : x.W.encList.length ≤ maxWallEncLen h' x.n := by
        have ha := Alg91.length_encList_le_of_isValid x.hW_valid.2.2
        have hb := length_elemWallEdges_le h'
        unfold maxWallEncLen; dsimp [h'] at hb ⊢; omega
      have hs := hsub_le (List.finRange t)
      rw [List.length_finRange] at hs
      omega
    omega
  -- 1. alg97InitProg
  rcases alg97InitProg_exec (w := w) (k₁ := k₁) h2 he hr₁ x B_arr B_reg hB_arr hB_reg
      (by omega) (by omega) (by dsimp [h'] at hw_bound; omega)
      (by dsimp [h'] at hw_bound; omega) (by omega) hin94_w ht_sub_w hs₀ with
    ⟨s₁, t₁, hex₁, ht₁, hin₁, hrB₁, harrG₁, harrW₁, hWV₁, harrSub₁, hsucc₁⟩
  -- 2. P94
  let x94 := buildAlg94Input (k₁ := k₁) h2 he hr₁ x
  have hw94 : wordSize c₉₄ (alg94Size x94) ≤ w :=
    le_trans (wordSize_mono_right c₉₄ (alg94Size_buildAlg94Input_le h2 he hr₁ x))
      (wordSize_mono_left (by omega) _)
  rcases hexec94 x94 w hw94 s₁ hin₁ with
    ⟨s₂, t₂, hex₂, ht₂, hout₂, hreg94, harr94⟩
  rw [alg94Size_buildAlg94Input] at ht₂
  have ht₁_sz : t₁ ≤ C_init * alg97Size x :=
    le_trans ht₁ (alg97InitCost_le_mul x)
  have ht₂_sz : t₂ ≤ C₉₄ * alg97Size x :=
    le_trans ht₂ (Nat.mul_le_mul_left C₉₄ he1_le_sz)
  have h0_w : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  -- 3. Branch on IsAlg94Output p t k₁ x94 (s₂.arrs outArr)
  dsimp only [IsAlg94Output, x94, buildAlg94Input] at hout₂
  rcases hout₂ with ⟨K, houtK, hK_mod⟩ | ⟨X, I, houtXI, hX_card, hI_card, hI_div⟩
  · -- Case (i) of (9.4): s₂.arrs outArr = 0 :: encBitSetsUpTo K p
    have hout_len : 0 < (s₂.arrs outArr).length := by rw [houtK]; simp
    have hout_get0 : (s₂.arrs outArr)[0]'hout_len = 0 := by simp [houtK]
    let s₃ := s₂.setReg 14 0
    have hex₃ : Exec w (.assign 14 (.read outArr (.const 0))) s₂ s₃ 3 :=
      .assign (by simp [Expr.eval, checkWord, h0_w, hout_len, hout_get0])
    have heval14 : (Expr.reg 14).eval w s₃ = some 0 := by
      simp [s₃, Expr.eval, checkWord, h0_w]
    have hex_ite :
        Exec w
          (.ite (.reg 14)
            (alg97DividingBranchProg p t r h h2 shiloachProg P91 k₂ s_goal B_arr B_reg)
            .skip)
          s₃ s₃ (1 + 1) :=
      .ite_false heval14 (.skip s₃)
    refine ⟨s₃, t₁ + (t₂ + (3 + (1 + 1))),
      .seq hex₁ (.seq hex₂ (.seq hex₃ hex_ite)),
      ?_,
      Or.inl ⟨K, by dsimp [s₃]; exact houtK, hK_mod⟩⟩
    dsimp [C_total]
    simp only [Nat.add_mul]
    omega
  · -- Case (ii) of (9.4): s₂.arrs outArr = 1 :: (bitSetList X ++ indI)
    have hout_len : 0 < (s₂.arrs outArr).length := by rw [houtXI]; simp
    have hout_get0 : (s₂.arrs outArr)[0]'hout_len = 1 := by simp [houtXI]
    let s₃ := s₂.setReg 14 1
    have hex₃ : Exec w (.assign 14 (.read outArr (.const 0))) s₂ s₃ 3 :=
      .assign (by simp [Expr.eval, checkWord, h0_w, hout_len, hout_get0, hw1])
    have heval14 : (Expr.reg 14).eval w s₃ = some 1 := by
      simp [s₃, Expr.eval, checkWord, hw1]
    have hrB₃ : s₃.regs B_reg = x.n := by
      simp only [s₃]
      rw [State.setReg_regs_ne _ _ (ne_reg_of_ne (by omega)),
        hreg94 B_reg hB_reg94]
      exact hrB₁
    have harrG₃ : s₃.arrs B_arr = x.G.enc := by
      simp only [s₃, State.setReg_arrs]
      rw [harr94 B_arr hB_arr94]; exact harrG₁
    have harrW₃ : s₃.arrs (B_arr + 1) = x.W.encList := by
      simp only [s₃, State.setReg_arrs]
      rw [harr94 (B_arr + 1) (Nat.le_trans hB_arr94 (Nat.le_add_right B_arr 1))]
      exact harrW₁
    have hWV₃ : IsBitSet x.W.vertexFinset (B_arr + 2) s₃ :=
      hWV₁.of_arr_eq (by
        dsimp [s₃]
        exact harr94 (B_arr + 2) (Nat.le_trans hB_arr94 (Nat.le_add_right B_arr 2)))
    have harrSub₃ : s₃.arrs (B_arr + 3) =
        (List.finRange t).flatMap (fun a => (alg97Subwall h2 he x.W a).encList) := by
      simp only [s₃, State.setReg_arrs]
      rw [harr94 (B_arr + 3) (Nat.le_trans hB_arr94 (Nat.le_add_right B_arr 3))]
      exact harrSub₁
    have hsucc₃ : IsWallSuccArrs x.W (B_arr + 4) s₃ :=
      hsucc₁.of_arrs_eq (fun k => by
        dsimp [s₃]
        exact harr94 (B_arr + 4 + k.1)
          (Nat.le_trans hB_arr94
            (Nat.le_trans (Nat.le_add_right B_arr 4) (Nat.le_add_right (B_arr + 4) k.1))))
    have hw_sh : wordSize c_sh (alg97Size x) ≤ w :=
      wordSize_mono_left (by omega) _
    have hexec91' : ∀ (x91 : Alg91Input p h' k₂ r₂),
        x91.n = x.n → x91.G.numEdges = x.G.numEdges →
        ∀ (s : State), s.arrs inArr = encAlg91In x91 →
        ∃ s' time,
          Exec w P91 s s' time ∧
          time ≤ C₉₁ * alg91Size x91 ∧
          IsAlg91Output p x91 (s'.arrs outArr) := by
      intro x91 hn_eq hm_eq s hs_in
      have hsz91 : alg91Size x91 ≤ alg97Size x := by
        dsimp [alg91Size]; omega
      have hw91 : wordSize c₉₁ (alg91Size x91) ≤ w :=
        le_trans (wordSize_mono_right c₉₁ hsz91) (wordSize_mono_left (by omega) _)
      rcases hexec91 x91 w hw91 s hs_in with ⟨s', time, hex, ht, hout, _, _⟩
      exact ⟨s', time, hex, ht, hout⟩
    rcases alg97DividingBranchProg_exec (t := t) h2 he hr₂ rfl hB_arr hB_reg
        hShiloachProg x hexec91' X I hX_card hI_card hI_div
        hw_sh hw_bound
        (by dsimp [s₃]; exact houtXI) hrB₃ harrG₃ harrW₃ hWV₃ harrSub₃ hsucc₃ with
      ⟨s₄, t₄, hex₄, ht₄, hout₄⟩
    have hex_ite :
        Exec w
          (.ite (.reg 14)
            (alg97DividingBranchProg p t r h h2 shiloachProg P91 k₂ s_goal B_arr B_reg)
            .skip)
          s₃ s₄ (1 + t₄) :=
      .ite_true heval14 (by omega) hex₄
    refine ⟨s₄, t₁ + (t₂ + (3 + (1 + t₄))),
      .seq hex₁ (.seq hex₂ (.seq hex₃ hex_ite)),
      ?_,
      hout₄⟩
    -- Bound t₄ ≤ C_div * alg97Size x
    have hcbc_sz :
        alg97CrossedBranchCost p t r h k₂ x.n x.G.numActivePairs x.G.numEdges C₉₁ ≤
          C_cross * alg97Size x := by
      unfold alg97CrossedBranchCost
      have hc1 : 150 * 1 ≤ 150 * alg97Size x := Nat.mul_le_mul_left 150 hsz_pos
      have hc2 : 83 * (2 + 3 * x.G.numActivePairs) ≤ 415 * alg97Size x := by omega
      have hc3 : 52 * maxWallEncLen h' x.n ≤ 52 * (4 + 3 * elemWallNumVerts h') * alg97Size x := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 52 hmw'_sz
      have hc4 : 18 * (k₂ * maxCrossedBlockLen h x.n) ≤
          18 * k₂ * (8 + 3 * elemWallNumVerts h) * alg97Size x := by
        have hmul := Nat.mul_le_mul_left (18 * k₂) hmc_sz
        calc 18 * (k₂ * maxCrossedBlockLen h x.n)
            = (18 * k₂) * maxCrossedBlockLen h x.n := by ring
          _ ≤ (18 * k₂) * ((8 + 3 * elemWallNumVerts h) * alg97Size x) := hmul
          _ = 18 * k₂ * (8 + 3 * elemWallNumVerts h) * alg97Size x := by ring
      have hc5 : C₉₁ * (x.G.numEdges + x.n + 1) ≤ C₉₁ * alg97Size x :=
        Nat.mul_le_mul_left C₉₁ he1_le_sz
      have hc6 : 33 * (p * x.n) ≤ 33 * p * alg97Size x := by
        rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_left (33 * p) hn_le_sz
      dsimp only [C_cross, h'] at hc3 ⊢
      simp only [Nat.add_mul, Nat.mul_one] at hc1 ⊢
      omega
    have ht₄_sz : t₄ ≤ C_div * alg97Size x := by
      have hd1 : (500 + 16 * t) * 1 ≤ (500 + 16 * t) * alg97Size x :=
        Nat.mul_le_mul_left _ hsz_pos
      have hd2 : 138 * x.n ≤ 138 * alg97Size x := Nat.mul_le_mul_left 138 hn_le_sz
      have hd3 : 15 * (2 + 3 * x.G.numActivePairs) ≤ 75 * alg97Size x := by omega
      have hd4 : 15 * maxWallEncLen h' x.n ≤ 15 * (4 + 3 * elemWallNumVerts h') * alg97Size x := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 15 hmw'_sz
      have hd5 : (291 + exprCost) * x.G.numActivePairs ≤ (291 + exprCost) * alg97Size x :=
        Nat.mul_le_mul_left _ hm_le_sz
      have hd6 : 15 * (t * maxWallEncLen h x.n) ≤
          15 * t * (4 + 3 * elemWallNumVerts h) * alg97Size x := by
        have hmul := Nat.mul_le_mul_left (15 * t) hmw_sz
        calc 15 * (t * maxWallEncLen h x.n)
            = (15 * t) * maxWallEncLen h x.n := by ring
          _ ≤ (15 * t) * ((4 + 3 * elemWallNumVerts h) * alg97Size x) := hmul
          _ = 15 * t * (4 + 3 * elemWallNumVerts h) * alg97Size x := by ring
      have hd7 :
          t * alg97ScanStepCost h x.n k₂ s_goal (2 * x.G.numEdges) (2 * x.G.numEdges)
            x.G.numEdges C_sh ≤
          t * alg97ScanFactor h k₂ s_goal C_sh * alg97Size x := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left t
          (alg97ScanStepCost_le_mul h x.n x.G.numEdges k₂ s_goal C_sh (alg97Size x)
            hsz_pos hn_le_sz he_le_sz le_rfl)
      have hd8 : 36 * (s_goal * maxWallEncLen h x.n) ≤
          36 * s_goal * (4 + 3 * elemWallNumVerts h) * alg97Size x := by
        have hmul := Nat.mul_le_mul_left (36 * s_goal) hmw_sz
        calc 36 * (s_goal * maxWallEncLen h x.n)
            = (36 * s_goal) * maxWallEncLen h x.n := by ring
          _ ≤ (36 * s_goal) * ((4 + 3 * elemWallNumVerts h) * alg97Size x) := hmul
          _ = 36 * s_goal * (4 + 3 * elemWallNumVerts h) * alg97Size x := by ring
      dsimp only [alg97DividingBranchCost, C_div, h', exprCost] at ht₄ hd4 hd5 ⊢
      simp only [Nat.add_mul, Nat.mul_one] at ht₄ hd1 hd5 ⊢
      omega
    dsimp [C_total]
    simp only [Nat.add_mul]
    omega

end GraphMinor.Compute

end
