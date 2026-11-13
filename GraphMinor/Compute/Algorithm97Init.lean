module

public import GraphMinor.Compute.Algorithm94Init
public import GraphMinor.Compute.Algorithm97Scan

/-!
# Graph Minors XIII, Algorithm (9.7): Bridges to (9.4) and (9.1) and Initialization

This module provides:
1. **`buildAlg94Input`:** packages `x : Alg97Input (alg97WallHeight p t r h)` together with its
   `t` canonical subwalls `alg97Subwall h2 he x.W` into an `Alg94Input`.
2. **`buildAlg91InputOfCrosses`:** lifts `k₂` crossed dividing subwalls of `(G \ X) ∪ H` found by
   `alg97ScanSubwallsProg` to an `Alg91Input` in `x.G` using GM XIII (9.5)
   (`WallOfHeight.disjoint_compassFinset_of_isDividingSubwall`).
3. **`isAlg97Output_of_flat_outcome`:** packages `s` flat dividing subwalls disjoint from `X` found
   by `alg97ScanSubwallsProg` into Case (ii) of `IsAlg97Output`.
4. **`alg97InitProg` and `alg97InitProg_exec`:** unpacks `x.G.enc` and `x.W.encList`, builds
   `IsBitSet x.W.vertexFinset` and `IsWallSuccArrs x.W`, extracts the `t` canonical subwall
   encodings via `unpackWallSegsProg` and `buildAllSubwallsEncProg`, and prepares `inArr = encAlg94In`
   for `P94`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical

/-! ### Section 1: Lifting Crosses and Packaging Inputs/Outputs for (9.4), (9.1), and (9.7) -/

/-- Lift a cross over `W_sub.castGraph (wallUnionMultiDigraph G X H)` in `(G \ X) ∪ H` to a cross
over `W_sub` in `G`. -/
theorem WallOfHeight.IsCrossOverWall.of_castGraph_wallUnionMultiDigraph
    {n h h' : ℕ} {G : MultiDigraph n} (X : Finset (Fin n)) (H : WallOfHeight h' G)
    (W_sub : WallOfHeight h G) {h2 h2' : 2 ≤ h} {P₁ P₂ : List (Fin n)}
    (hcr : (W_sub.castGraph (WallOfHeight.wallUnionMultiDigraph G X H)).IsCrossOverWall h2 P₁ P₂) :
    W_sub.IsCrossOverWall h2' P₁ P₂ where
  ne_nil₁ := hcr.ne_nil₁
  ne_nil₂ := hcr.ne_nil₂
  nodup₁ := hcr.nodup₁
  nodup₂ := hcr.nodup₂
  isWalk₁ := WallOfHeight.isSimpleWalkList_of_congr
    (fun _ _ _ huv => WallOfHeight.wallUnionMultiDigraph_toSimpleGraph_le G X H huv) hcr.isWalk₁
  isWalk₂ := WallOfHeight.isSimpleWalkList_of_congr
    (fun _ _ _ huv => WallOfHeight.wallUnionMultiDigraph_toSimpleGraph_le G X H huv) hcr.isWalk₂
  head₁ := hcr.head₁
  getLast₁ := hcr.getLast₁
  head₂ := hcr.head₂
  getLast₂ := hcr.getLast₂
  disjoint := hcr.disjoint

/-- Package `x : Alg97Input (alg97WallHeight p t r h)` together with its `t` canonical subwalls
`alg97Subwall h2 he x.W` into an `Alg94Input p t (alg97WallHeight p t r h) k₁ r₁` (`r₁ ≤ r`). -/
def buildAlg94Input {p t r h k₁ r₁ : ℕ} (h2 : 2 ≤ h) (he : Even h) (hr₁ : r₁ ≤ r)
    (x : Alg97Input (alg97WallHeight p t r h)) :
    Alg94Input p t (alg97WallHeight p t r h) k₁ r₁ where
  n := x.n
  G := x.G
  W := x.W
  h_sub := fun _ => h
  W_sub := alg97Subwall h2 he x.W
  hW_valid := x.hW_valid
  hsub := alg97Subwall_isSubwallOf h2 he x.W
  hdist := fun _ _ hab _ hu _ hv =>
    le_trans hr₁ (alg97Subwall_brickDist_ge h2 he x.hW_valid.2.2 hab hu hv)

theorem encAlg94In_buildAlg94Input {p t r h k₁ r₁ : ℕ} (h2 : 2 ≤ h) (he : Even h) (hr₁ : r₁ ≤ r)
    (x : Alg97Input (alg97WallHeight p t r h)) :
    encAlg94In (buildAlg94Input (k₁ := k₁) h2 he hr₁ x) =
      x.G.enc ++ x.W.encList ++
        (List.finRange t).flatMap (fun a => (alg97Subwall h2 he x.W a).encList) :=
  rfl

theorem alg94Size_buildAlg94Input {p t r h k₁ r₁ : ℕ} (h2 : 2 ≤ h) (he : Even h) (hr₁ : r₁ ≤ r)
    (x : Alg97Input (alg97WallHeight p t r h)) :
    alg94Size (buildAlg94Input (k₁ := k₁) h2 he hr₁ x) = x.G.numEdges + x.n + 1 :=
  rfl

theorem alg94Size_buildAlg94Input_le {p t r h k₁ r₁ : ℕ} (h2 : 2 ≤ h) (he : Even h) (hr₁ : r₁ ≤ r)
    (x : Alg97Input (alg97WallHeight p t r h)) :
    alg94Size (buildAlg94Input (k₁ := k₁) h2 he hr₁ x) ≤ alg97Size x := by
  dsimp [alg94Size, buildAlg94Input, alg97Size]
  have h1 : 1 * (x.G.numEdges + x.n + 1) ≤ (x.n + 1) * (x.G.numEdges + x.n + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- Construct an `Alg91Input p (alg97WallHeight p t r h) k₂ r₂` (`r₂ ≤ r`) from `k₂` crossed
dividing subwalls collected by `alg97ScanSubwallsProg`. -/
def buildAlg91InputOfCrosses {p t r h k₂ r₂ : ℕ} (h2 : 2 ≤ h) (he : Even h) (hr₂ : r₂ ≤ r)
    (x : Alg97Input (alg97WallHeight p t r h))
    (X : Finset (Fin x.n)) (I : Finset (Fin t))
    (hI_div : ∀ idx ∈ I,
      (x.W.castGraph (WallOfHeight.wallUnionMultiDigraph x.G X x.W)).IsDividingSubwall
        ((alg97Subwall h2 he x.W idx).castGraph (WallOfHeight.wallUnionMultiDigraph x.G X x.W)))
    (entries_c : Fin k₂ → CrossedSubwallEntry h2
      (fun idx => (alg97Subwall h2 he x.W idx).castGraph
        (WallOfHeight.wallUnionMultiDigraph x.G X x.W)))
    (hmc : StrictMono (fun a => (entries_c a).idx))
    (hmem_c : ∀ a : Fin k₂, (entries_c a).idx ∈ I) :
    Alg91Input p (alg97WallHeight p t r h) k₂ r₂ where
  n := x.n
  G := x.G
  W := x.W
  h_sub := fun _ => h
  W_sub := fun a => alg97Subwall h2 he x.W (entries_c a).idx
  P := fun a => (entries_c a).data.P₁
  Q := fun a => (entries_c a).data.P₂
  hW_valid := x.hW_valid
  hsub := fun a => alg97Subwall_isSubwallOf h2 he x.W (entries_c a).idx
  hdist := fun a b hab _ hu _ hv =>
    le_trans hr₂
      (alg97Subwall_brickDist_ge h2 he x.hW_valid.2.2 (hmc.injective.ne hab) hu hv)
  hcross := fun a =>
    WallOfHeight.IsCrossOverWall.of_castGraph_wallUnionMultiDigraph X x.W
      (alg97Subwall h2 he x.W (entries_c a).idx) (entries_c a).data.hcr
  hinter := by
    intro a v hv hvW
    let G' := WallOfHeight.wallUnionMultiDigraph x.G X x.W
    let W' := x.W.castGraph G'
    have hW' : W'.IsValid :=
      WallOfHeight.isValid_castGraph_wallUnionMultiDigraph X x.hW_valid.2.2
    have hv_comp : v ∈ ((alg97Subwall h2 he x.W (entries_c a).idx).castGraph G').compassFinset := by
      rcases hv with hv₁ | hv₂
      · exact (entries_c a).data.hmem₁ v hv₁
      · exact (entries_c a).data.hmem₂ v hv₂
    have hvW' : v ∈ W'.vertexFinset := hvW
    have hmem := W'.mem_vertexFinset_of_mem_compassFinset_of_isDividingSubwall
      x.hW_valid.1 x.hW_valid.2.1 hW' (hI_div (entries_c a).idx (hmem_c a)) hv_comp hvW'
    rwa [WallOfHeight.castGraph_vertexFinset] at hmem
  hdisj := by
    intro a b hab v ⟨hva, hvb⟩
    let G' := WallOfHeight.wallUnionMultiDigraph x.G X x.W
    let W' := x.W.castGraph G'
    have hW' : W'.IsValid :=
      WallOfHeight.isValid_castGraph_wallUnionMultiDigraph X x.hW_valid.2.2
    have hv_a : v ∈ ((alg97Subwall h2 he x.W (entries_c a).idx).castGraph G').compassFinset := by
      rcases hva with hv₁ | hv₂
      · exact (entries_c a).data.hmem₁ v hv₁
      · exact (entries_c a).data.hmem₂ v hv₂
    have hv_b : v ∈ ((alg97Subwall h2 he x.W (entries_c b).idx).castGraph G').compassFinset := by
      rcases hvb with hv₁ | hv₂
      · exact (entries_c b).data.hmem₁ v hv₁
      · exact (entries_c b).data.hmem₂ v hv₂
    have hdisj_V :
        Disjoint
          ((alg97Subwall h2 he x.W (entries_c a).idx).castGraph G').vertexFinset
          ((alg97Subwall h2 he x.W (entries_c b).idx).castGraph G').vertexFinset := by
      rw [WallOfHeight.castGraph_vertexFinset, WallOfHeight.castGraph_vertexFinset]
      exact alg97Subwall_disjoint_vertexFinset h2 he x.hW_valid.2.2 (hmc.injective.ne hab)
    have hdisj_C := W'.disjoint_compassFinset_of_isDividingSubwall
      x.hW_valid.1 x.hW_valid.2.1 hW'
      (hI_div (entries_c a).idx (hmem_c a))
      (hI_div (entries_c b).idx (hmem_c b))
      hdisj_V
    exact Finset.disjoint_left.mp hdisj_C hv_a hv_b

theorem encAlg91In_buildAlg91InputOfCrosses {p t r h k₂ r₂ : ℕ}
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
    (hmem_c : ∀ a : Fin k₂, (entries_c a).idx ∈ I) :
    encAlg91In (buildAlg91InputOfCrosses h2 he hr₂ x X I hI_div entries_c hmc hmem_c) =
      x.G.enc ++ x.W.encList ++
        (List.finRange k₂).flatMap (fun a => (entries_c a).encBlock) := by
  simp [encAlg91In, buildAlg91InputOfCrosses, CrossedSubwallEntry.encBlock,
    crossedSubwallBlock, WallOfHeight.castGraph_encList]

theorem alg91Size_buildAlg91InputOfCrosses {p t r h k₂ r₂ : ℕ}
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
    (hmem_c : ∀ a : Fin k₂, (entries_c a).idx ∈ I) :
    alg91Size (buildAlg91InputOfCrosses h2 he hr₂ x X I hI_div entries_c hmc hmem_c) =
      x.G.numEdges + x.n + 1 :=
  rfl

theorem alg91Size_buildAlg91InputOfCrosses_le {p t r h k₂ r₂ : ℕ}
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
    (hmem_c : ∀ a : Fin k₂, (entries_c a).idx ∈ I) :
    alg91Size (buildAlg91InputOfCrosses h2 he hr₂ x X I hI_div entries_c hmc hmem_c) ≤
      alg97Size x := by
  dsimp [alg91Size, buildAlg91InputOfCrosses, alg97Size]
  have h1 : 1 * (x.G.numEdges + x.n + 1) ≤ (x.n + 1) * (x.G.numEdges + x.n + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem WallOfHeight.IsFlatWall.congr_h2 {n h : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} {h2 h2' : 2 ≤ h} (hf : W.IsFlatWall h2) :
    W.IsFlatWall h2' :=
  hf

/-- Package `s_goal` flat dividing subwalls disjoint from `X` collected by `alg97ScanSubwallsProg`
into Case (ii) of `IsAlg97Output`. -/
theorem isAlg97Output_of_flat_outcome {p s_goal t r h : ℕ} (h2 : 2 ≤ h) (he : Even h)
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
    {out : List ℕ}
    (hout : out = 1 :: (bitSetList X ++
      (List.finRange s_goal).flatMap (fun a =>
        ((alg97Subwall h2 he x.W (idx_f a)).castGraph
          (WallOfHeight.wallUnionMultiDigraph x.G X x.W)).encList))) :
    IsAlg97Output p s_goal h (alg97WallHeight p t r h) x out := by
  right
  refine ⟨X, fun a => alg97Subwall h2 he x.W (idx_f a),
    fun a => alg97Subwall_isSubwallOf h2 he x.W (idx_f a),
    by simpa only [WallOfHeight.castGraph_encList] using hout,
    hX_card,
    fun a b hab => alg97Subwall_disjoint_vertexFinset h2 he x.hW_valid.2.2 (hmf.injective.ne hab),
    fun a => ⟨by simpa only [WallOfHeight.castGraph_vertexFinset] using (hval_f a).2.2,
      (hval_f a).2.1.congr_h2, hI_div (idx_f a) (hval_f a).1⟩⟩

/-! ### Section 2: Persistent Layout and Initialization (`alg97InitProg`) -/

/-- Caller-safe base array index above `50` and above `P94`. -/
def alg97ArrBase (P94 : Cmd) : ℕ :=
  max 50 (folioCallerArrBase P94)

/-- Caller-safe base register index above `30` and above `P94`. -/
def alg97RegBase (P94 : Cmd) : ℕ :=
  max 30 (folioCallerRegBase P94)

/-- Initialization program for Algorithm (9.7):
Given `inArr = encAlg97In x = x.G.enc ++ x.W.encList` (`h' = alg97WallHeight p t r h`):
1. Reads `x.n = inArr[0]` into `reg 1`,
2. Computes `x.G.enc.length = 2 + 3 * inArr[1]` into `reg 18` and saves it in `reg 19`,
3. Copies `x.G.enc` into `arr B_arr`,
4. Runs `parseFixedWallProg h' h2' true (B_arr + 4) inArr (B_arr + 2) 12 18` to populate
   `IsBitSet x.W.vertexFinset (B_arr + 2)` and `IsWallSuccArrs x.W (B_arr + 4)`, advancing `reg 18`
   to `(x.G.enc ++ x.W.encList).length`,
5. Copies `x.W.encList` into `arr (B_arr + 1)`,
6. Runs `unpackWallSegsProg h' (B_arr + 1) baseSegArr 14 15 16 20` and
   `buildAllSubwallsEncProg p t r h h2 (B_arr + 1) baseSegArr (B_arr + 3) 26 27 14 15 20` to build
   `sub_flat = (List.finRange t).flatMap (fun a => (alg97Subwall h2 he x.W a).encList)` in
   `arr (B_arr + 3)`,
7. Saves `x.n` (`reg 1`) in `reg B_reg`, and appends `arr (B_arr + 3)` to `inArr` so that
   `inArr = encAlg94In (buildAlg94Input h2 he hr₁ x)`. -/
def alg97InitProg (p t r h : ℕ) (h2 : 2 ≤ h) (B_arr B_reg : ℕ) : Cmd :=
  let h' := alg97WallHeight p t r h
  let h2' := two_le_alg97WallHeight p t r h
  let a_G : Arr := B_arr
  let a_W : Arr := B_arr + 1
  let a_WV : Arr := B_arr + 2
  let a_sub : Arr := B_arr + 3
  let baseSuccArr : ℕ := B_arr + 4
  let baseSegArr : ℕ := B_arr + 4 + (elemWallEdges h').length
  .seq (.assign 1 (.read inArr (.const 0)))
    (.seq (.assign 18 (.op .add (.const 2) (.op .mul (.const 3) (.read inArr (.const 1)))))
      (.seq (.assign 19 (.reg 18))
        (.seq (readSliceProg inArr (.const 0) a_G (.reg 18) 20)
          (.seq (parseFixedWallProg h' h2' true baseSuccArr inArr a_WV 12 18)
            (.seq (.assign 14 (.op .sub (.reg 18) (.reg 19)))
              (.seq (readSliceProg inArr (.reg 19) a_W (.reg 14) 20)
                (.seq (unpackWallSegsProg h' a_W baseSegArr 14 15 16 20)
                  (.seq (buildAllSubwallsEncProg p t r h h2
                      a_W baseSegArr a_sub 26 27 14 15 20)
                    (.seq (.assign B_reg (.reg 1))
                      (.seq (.assign 14 (.len inArr))
                        (.seq (.assign 15 (.len a_sub))
                          (appendArrProg inArr a_sub 30 14 15 20))))))))))))

/-- Time bound for `alg97InitProg`. -/
def alg97InitCost (p t r h n m_act : ℕ) : ℕ :=
  let h' := alg97WallHeight p t r h
  100 + 84 * (2 + 3 * m_act) + 84 * maxWallEncLen h' n +
    parseWallCost h' n + 26 * (elemWallEdges h').length +
    t * (55 + 7 * elemWallNumVerts h +
      (elemWallEdges h).length * (40 + 34 * maxWallEncLen h n) +
      34 * (t * maxWallEncLen h n)) +
    18 * (t * maxWallEncLen h n)

theorem alg97InitProg_exec {w p t r h k₁ r₁ : ℕ} (h2 : 2 ≤ h) (he : Even h) (hr₁ : r₁ ≤ r)
    (x : Alg97Input (alg97WallHeight p t r h))
    (B_arr B_reg : ℕ) (hB_arr : 50 ≤ B_arr) (hB_reg : 30 ≤ B_reg)
    (hw3 : 3 < 2 ^ w)
    (hn1_w : x.n + 1 < 2 ^ w)
    (hh'_w : alg97WallHeight p t r h < 2 ^ w)
    (hc2'_w : 3 + 2 * elemWallNumVerts (alg97WallHeight p t r h) < 2 ^ w)
    (he_w : x.G.numEdges < 2 ^ w)
    (hin94_w : (encAlg94In (buildAlg94Input (k₁ := k₁) h2 he hr₁ x)).length < 2 ^ w)
    (ht_sub_w : t * maxWallEncLen h x.n < 2 ^ w)
    {s₀ : State} (hs₀ : s₀.arrs inArr = encAlg97In x) :
    ∃ s' time,
      Exec w (alg97InitProg p t r h h2 B_arr B_reg) s₀ s' time ∧
      time ≤ alg97InitCost p t r h x.n x.G.numActivePairs ∧
      s'.arrs inArr = encAlg94In (buildAlg94Input (k₁ := k₁) h2 he hr₁ x) ∧
      s'.regs B_reg = x.n ∧
      s'.arrs B_arr = x.G.enc ∧
      s'.arrs (B_arr + 1) = x.W.encList ∧
      IsBitSet x.W.vertexFinset (B_arr + 2) s' ∧
      s'.arrs (B_arr + 3) =
        (List.finRange t).flatMap (fun a => (alg97Subwall h2 he x.W a).encList) ∧
      IsWallSuccArrs x.W (B_arr + 4) s' := by
  let h' := alg97WallHeight p t r h
  let h2' := two_le_alg97WallHeight p t r h
  let baseSuccArr : ℕ := B_arr + 4
  let baseSegArr : ℕ := B_arr + 4 + (elemWallEdges h').length
  let sub_flat := (List.finRange t).flatMap (fun a => (alg97Subwall h2 he x.W a).encList)
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have hc'_w : 3 + elemWallNumVerts h' < 2 ^ w := by dsimp [h']; omega
  have hh_le_h' : h ≤ h' := le_alg97WallHeight p t r h
  have hh_w : h < 2 ^ w := by dsimp [h'] at hh_le_h'; omega
  have hc2_w : 3 + 2 * elemWallNumVerts h < 2 ^ w := by
    have : elemWallNumVerts h ≤ elemWallNumVerts h' := by
      rw [elemWallNumVerts_eq, elemWallNumVerts_eq]
      exact Nat.sub_le_sub_right
        (Nat.mul_le_mul (show h + 1 ≤ h' + 1 by omega) (show 2 * h + 2 ≤ 2 * h' + 2 by omega)) 2
    dsimp [h'] at this; omega
  have hin94_eq :
      encAlg94In (buildAlg94Input (k₁ := k₁) h2 he hr₁ x) =
        x.G.enc ++ x.W.encList ++ sub_flat := rfl
  have hin97_eq : encAlg97In x = x.G.enc ++ x.W.encList := rfl
  have hG_len : x.G.enc.length = 2 + 3 * x.G.numActivePairs := MultiDigraph.length_enc x.G
  have hW_len_le : x.W.encList.length ≤ maxWallEncLen h' x.n := by
    have ha := Alg91.length_encList_le_of_isValid x.hW_valid.2.2
    have hb := length_elemWallEdges_le h'
    unfold maxWallEncLen; dsimp [h'] at hb ⊢; omega
  have hsub_len_le : sub_flat.length ≤ t * maxWallEncLen h x.n := by
    have h1 := length_encAlg94In_le (buildAlg94Input (k₁ := k₁) h2 he hr₁ x)
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
  have hGW_len_le : (x.G.enc ++ x.W.encList).length ≤
      (encAlg94In (buildAlg94Input (k₁ := k₁) h2 he hr₁ x)).length := by
    rw [hin94_eq]; simp [List.length_append]
  have hGW_w : (x.G.enc ++ x.W.encList).length < 2 ^ w := by omega
  have hG_len_w : x.G.enc.length < 2 ^ w := by
    simp [List.length_append] at hGW_w; omega
  have hW_len_w : x.W.encList.length < 2 ^ w := by
    simp [List.length_append] at hGW_w; omega
  have hm_w : x.G.numActivePairs < 2 ^ w := by omega
  have h3m_w : 3 * x.G.numActivePairs < 2 ^ w := by omega
  have hin_len0 : 0 < (s₀.arrs inArr).length := by
    rw [hs₀, hin97_eq]; simp [MultiDigraph.enc]
  have hin_len1 : 1 < (s₀.arrs inArr).length := by
    rw [hs₀, hin97_eq]; simp [MultiDigraph.enc]
  have hin_get0 : (s₀.arrs inArr)[0]'hin_len0 = x.n := by
    simp [hs₀, hin97_eq, MultiDigraph.enc]
  have hin_get1 : (s₀.arrs inArr)[1]'hin_len1 = x.G.numActivePairs := by
    simp [hs₀, hin97_eq, MultiDigraph.enc]
  -- 1. reg 1 := inArr[0]
  let s₁ := s₀.setReg 1 x.n
  have hex₁ : Exec w (.assign 1 (.read inArr (.const 0))) s₀ s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, hin_len0, hin_get0, hn_w])
  -- 2. reg 18 := 2 + 3 * inArr[1]
  let s₂ := s₁.setReg 18 x.G.enc.length
  have hex₂ :
      Exec w (.assign 18 (.op .add (.const 2) (.op .mul (.const 3) (.read inArr (.const 1)))))
        s₁ s₂ 7 :=
    .assign (by
      rw [hG_len]
      simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hw1, hw3, hin_len1, hin_get1, hm_w, h3m_w, show 2 < 2 ^ w by omega,
        show 2 + 3 * x.G.numActivePairs < 2 ^ w by omega])
  -- 3. reg 19 := reg 18
  let s₃ := s₂.setReg 19 x.G.enc.length
  have hex₃ : Exec w (.assign 19 (.reg 18)) s₂ s₃ 2 :=
    .assign (by simp only [s₂, Expr.eval, checkWord, State.setReg_regs_self, hG_len_w, ↓reduceIte])
  -- 4. readSliceProg inArr 0 B_arr (reg 18) 20
  have hG_enc_w : ∀ v ∈ x.G.enc, v < 2 ^ w :=
    all_lt_enc_multiDigraph x.G hn_w hm_w he_w
  rcases readSliceProg_exec_full inArr B_arr (.const 0) 18 20
      (by change 0 ≠ B_arr; omega) (by decide) [] x.G.enc x.W.encList
      rfl rfl hG_enc_w hw1 (by simpa using hG_len_w) (s := s₃)
      (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₃, s₂, s₁, hs₀, hin97_eq])
      rfl with
    ⟨s₄, t₄, hex₄, ht₄, harrG_4, harr₄, hreg₄⟩
  dsimp [Expr.cost] at ht₄
  -- 5. parseFixedWallProg h' h2' true baseSuccArr inArr (B_arr + 2) 12 18
  have hsucc_ne :
      (true = true) → ∀ idx : Fin (elemWallEdges h').length,
        baseSuccArr + idx.1 ≠ inArr ∧ baseSuccArr + idx.1 ≠ B_arr + 2 ∧ baseSuccArr + idx.1 ≠ 12 := by
    intro _ idx
    change B_arr + 4 + idx.1 ≠ 0 ∧ B_arr + 4 + idx.1 ≠ B_arr + 2 ∧ B_arr + 4 + idx.1 ≠ 12
    omega
  rcases parseFixedWallProg_exec h2' le_rfl x.W x.hW_valid.2.2 true baseSuccArr
      inArr (B_arr + 2) 12 18
      (by change 0 ≠ B_arr + 2; omega) (by decide) (by omega) hsucc_ne (by decide)
      x.G.enc [] hw1 hn1_w hc'_w hGW_w (s := s₄)
      (by rw [harr₄ inArr (by change 0 ≠ B_arr; omega), List.append_nil]; exact hs₀)
      (by rw [hreg₄ 1 (Or.inl (by decide))]; rfl)
      (by rw [hreg₄ 18 (Or.inl (by decide))]; rfl) with
    ⟨s₅, t₅, hex₅, ht₅, hr18_5, _, hWV_5, _, hsucc_5, harr₅, hreg₅⟩
  have hsucc_5' : IsWallSuccArrs x.W baseSuccArr s₅ := hsucc_5 rfl
  -- 6. reg 14 := reg 18 - reg 19
  have hr19_5 : s₅.regs 19 = x.G.enc.length := by
    rw [hreg₅ 19 (Or.inr (by decide)) (by decide) (by decide), hreg₄ 19 (Or.inl (by decide))]
    rfl
  have hr18_5' : s₅.regs 18 = x.G.enc.length + x.W.encList.length := by
    rw [hr18_5, List.length_append]
  let s₆ := s₅.setReg 14 x.W.encList.length
  have hex₆ : Exec w (.assign 14 (.op .sub (.reg 18) (.reg 19))) s₅ s₆ 4 :=
    .assign (by
      have htot_w : x.G.enc.length + x.W.encList.length < 2 ^ w := by
        simpa [List.length_append] using hGW_w
      simp only [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr18_5', hr19_5,
        hG_len_w, htot_w, hW_len_w, ↓reduceIte, Nat.add_sub_cancel_left])
  -- 7. readSliceProg inArr (reg 19) (B_arr + 1) (reg 14) 20
  have hW_enc_w : ∀ v ∈ x.W.encList, v < 2 ^ w :=
    all_lt_encList_of_isValid x.W x.hW_valid.2.2 le_rfl hh'_w hc2'_w hn_w
  have hin_6 : s₆.arrs inArr = x.G.enc ++ x.W.encList ++ [] := by
    simp only [s₆, State.setReg_arrs]
    rw [harr₅ inArr (by change 0 ≠ B_arr + 2; omega) (by decide)
      (fun _ k => by change 0 ≠ B_arr + 4 + k.1; omega),
      harr₄ inArr (by change 0 ≠ B_arr; omega), List.append_nil]
    exact hs₀
  rcases readSliceProg_exec_full inArr (B_arr + 1) (.reg 19) 14 20
      (by change 0 ≠ B_arr + 1; omega) (by decide) x.G.enc x.W.encList []
      rfl rfl hW_enc_w hw1 (by simpa [List.length_append] using hGW_w) (s := s₆)
      (by
        have hr19_6 : s₆.regs 19 = x.G.enc.length := by simp [s₆, hr19_5]
        simp only [Expr.eval, checkWord, hr19_6, hG_len_w, ↓reduceIte])
      hin_6 (by simp [s₆]) with
    ⟨s₇, t₇, hex₇, ht₇, harrW_7, harr₇, hreg₇⟩
  dsimp [Expr.cost] at ht₇
  -- 8. unpackWallSegsProg h' (B_arr + 1) baseSegArr 14 15 16 20
  rcases unpackWallSegsProg_exec x.W (B_arr + 1) baseSegArr 14 15 16 20
      (by dsimp [baseSegArr]; omega) (by decide) (by decide) (by decide)
      hw1 hn_w hW_len_w harrW_7 with
    ⟨s₈, t₈, hex₈, ht₈, hsegs₈, harr₈, hreg₈⟩
  -- 9. buildAllSubwallsEncProg p t r h h2 (B_arr + 1) baseSegArr (B_arr + 3) 26 27 14 15 20
  have harrW_8 : s₈.arrs (B_arr + 1) = x.W.encList := by
    rw [harr₈ (B_arr + 1) (by dsimp [baseSegArr]; omega)]
    exact harrW_7
  rcases buildAllSubwallsEncProg_exec h2 he x.W x.hW_valid.2.2
      (B_arr + 1) baseSegArr (B_arr + 3) 26 27 14 15 20
      (ne_arr_of_ne (by omega)) (ne_arr_of_ne (by omega)) (ne_arr_of_ne (by omega))
      (by dsimp [baseSegArr]; omega) (by dsimp [baseSegArr]; omega) (by dsimp [baseSegArr]; omega)
      (ne_arr_of_ne (by omega)) (ne_arr_of_ne (by omega)) (by decide)
      (by decide) (by decide) hw1 hn_w hc'_w ht_sub_w
      harrW_8 hsegs₈ with
    ⟨s₉, t₉, hex₉, ht₉, harrSub_9, harr₉, hreg₉⟩
  -- Preserve facts at s₉
  have hr1_9 : s₉.regs 1 = x.n := by
    rw [hreg₉ 1 (by decide), hreg₈ 1 (by decide), hreg₇ 1 (Or.inl (by decide))]
    simp only [s₆]
    rw [State.setReg_regs_ne _ _ (by decide : (1 : Reg) ≠ 14),
      hreg₅ 1 (Or.inl (by decide)) (by decide) (by decide),
      hreg₄ 1 (Or.inl (by decide))]
    rfl
  have hin_9 : s₉.arrs inArr = x.G.enc ++ x.W.encList := by
    rw [harr₉ inArr (ne_arr_of_ne (by change 0 ≠ B_arr + 3; omega)) (by decide) (by decide),
      harr₈ inArr (by change 0 < baseSegArr; dsimp [baseSegArr]; omega),
      harr₇ inArr (by change 0 ≠ B_arr + 1; omega)]
    simpa using hin_6
  -- 10. reg B_reg := reg 1
  let s₁₀ := s₉.setReg B_reg x.n
  have hex₁₀ : Exec w (.assign B_reg (.reg 1)) s₉ s₁₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr1_9, hn_w])
  -- 11. reg 14 := len inArr
  let s₁₁ := s₁₀.setReg 14 (x.G.enc ++ x.W.encList).length
  have hex₁₁ : Exec w (.assign 14 (.len inArr)) s₁₀ s₁₁ 2 :=
    .assign (by simp only [s₁₀, Expr.eval, checkWord, State.setReg_arrs, hin_9, hGW_w, ↓reduceIte])
  -- 12. reg 15 := len (B_arr + 3)
  have hsub_len_w : sub_flat.length < 2 ^ w := by
    rw [hin94_eq, List.length_append] at hin94_w; omega
  let s₁₂ := s₁₁.setReg 15 sub_flat.length
  have hex₁₂ : Exec w (.assign 15 (.len (B_arr + 3))) s₁₁ s₁₂ 2 :=
    .assign (by
      have h9 : s₉.arrs (B_arr + 3) = sub_flat := harrSub_9
      simp only [s₁₁, s₁₀, Expr.eval, checkWord, State.setReg_arrs, h9, hsub_len_w, ↓reduceIte])
  -- 13. appendArrProg inArr (B_arr + 3) 30 14 15 20
  have hGW_all_w : ∀ v ∈ x.G.enc ++ x.W.encList, v < 2 ^ w := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hG_enc_w v hv
    · exact hW_enc_w v hv
  have hsub_all_w : ∀ v ∈ sub_flat, v < 2 ^ w := by
    intro v hv
    dsimp [sub_flat] at hv
    rw [List.mem_flatMap] at hv
    rcases hv with ⟨j, _, hvj⟩
    exact all_lt_encList_of_isValid (alg97Subwall h2 he x.W j)
      (alg97Subwall_isValid h2 he x.hW_valid.2.2 j)
      le_rfl hh_w hc2_w hn_w v hvj
  have htot94_w : (x.G.enc ++ x.W.encList).length + sub_flat.length < 2 ^ w := by
    rw [hin94_eq, List.length_append] at hin94_w
    exact hin94_w
  rcases appendArrProg_exec inArr (B_arr + 3) 30 14 15 20
      (ne_arr_of_ne (by change 0 ≠ B_arr + 3; omega)) (by decide)
      (ne_arr_of_ne (by omega))
      (by decide) (by decide) (by decide)
      (x.G.enc ++ x.W.encList) sub_flat hGW_all_w hsub_all_w hw1 htot94_w (s := s₁₂)
      hin_9 harrSub_9 rfl rfl with
    ⟨s₁₃, t₁₃, hex₁₃, ht₁₃, hin_13, _, harr₁₃, hreg₁₃⟩
  have h16_G : 16 * x.G.enc.length ≤ 16 * (2 + 3 * x.G.numActivePairs) := by rw [hG_len]
  have h34_GW :
      34 * (x.G.enc ++ x.W.encList).length ≤
        34 * (2 + 3 * x.G.numActivePairs) + 34 * maxWallEncLen h' x.n := by
    rw [List.length_append, hG_len, Nat.mul_add]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left 34 hW_len_le) _
  have h32_W : 16 * x.W.encList.length ≤ 16 * maxWallEncLen h' x.n :=
    Nat.mul_le_mul_left 16 hW_len_le
  have h18_sub : 18 * sub_flat.length ≤ 18 * (t * maxWallEncLen h x.n) :=
    Nat.mul_le_mul_left 18 hsub_len_le
  refine ⟨s₁₃,
    3 + (7 + (2 + (t₄ + (t₅ + (4 + (t₇ + (t₈ + (t₉ + (2 + (2 + (2 + t₁₃))))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂ hex₁₃))))))))))),
    by dsimp [alg97InitCost, h'] at *; omega,
    hin_13,
    by
      rw [hreg₁₃ B_reg (Or.inr (by omega)) (by omega)]
      simp [s₁₂, s₁₁, s₁₀,
        State.setReg_regs_ne _ _ (by omega : (B_reg : Reg) ≠ 15),
        State.setReg_regs_ne _ _ (by omega : (B_reg : Reg) ≠ 14)],
    by
      rw [harr₁₃ B_arr (ne_arr_of_ne (by change B_arr ≠ 0; omega)) (ne_arr_of_ne (by omega))]
      simp only [s₁₂, s₁₁, s₁₀, State.setReg_arrs]
      rw [harr₉ B_arr (ne_arr_of_ne (by omega)) (ne_arr_of_ne (by omega)) (ne_arr_of_ne (by omega)),
        harr₈ B_arr (by dsimp [baseSegArr]; omega),
        harr₇ B_arr (by omega)]
      simp only [s₆, State.setReg_arrs]
      rw [harr₅ B_arr (by omega) (by omega) (fun _ k => by dsimp [baseSuccArr]; omega)]
      exact harrG_4,
    by
      rw [harr₁₃ (B_arr + 1) (ne_arr_of_ne (by change B_arr + 1 ≠ 0; omega)) (ne_arr_of_ne (by omega))]
      simp only [s₁₂, s₁₁, s₁₀, State.setReg_arrs]
      rw [harr₉ (B_arr + 1) (ne_arr_of_ne (by omega)) (ne_arr_of_ne (by omega)) (ne_arr_of_ne (by omega))]
      exact harrW_8,
    hWV_5.of_arr_eq (by
      rw [harr₁₃ (B_arr + 2) (ne_arr_of_ne (by change B_arr + 2 ≠ 0; omega)) (ne_arr_of_ne (by omega))]
      simp only [s₁₂, s₁₁, s₁₀, State.setReg_arrs]
      rw [harr₉ (B_arr + 2) (ne_arr_of_ne (by omega)) (ne_arr_of_ne (by omega)) (ne_arr_of_ne (by omega)),
        harr₈ (B_arr + 2) (by dsimp [baseSegArr]; omega),
        harr₇ (B_arr + 2) (by omega)]
      rfl),
    by
      rw [harr₁₃ (B_arr + 3) (ne_arr_of_ne (by change B_arr + 3 ≠ 0; omega)) (ne_arr_of_ne (by omega))]
      exact harrSub_9,
    hsucc_5'.of_arrs_eq (fun k => by
      have hk := k.2
      rw [harr₁₃ (baseSuccArr + k.1)
        (ne_arr_of_ne (by change B_arr + 4 + k.1 ≠ 0; omega))
        (ne_arr_of_ne (by dsimp [baseSuccArr]; omega))]
      simp only [s₁₂, s₁₁, s₁₀, State.setReg_arrs]
      rw [harr₉ (baseSuccArr + k.1)
          (ne_arr_of_ne (by dsimp [baseSuccArr]; omega))
          (ne_arr_of_ne (by dsimp [baseSuccArr]; omega))
          (ne_arr_of_ne (by dsimp [baseSuccArr]; omega)),
        harr₈ (baseSuccArr + k.1) (by dsimp [baseSuccArr, baseSegArr, h'] at hk ⊢; omega),
        harr₇ (baseSuccArr + k.1) (by dsimp [baseSuccArr]; omega)]
      rfl)⟩

end GraphMinor.Compute

end
