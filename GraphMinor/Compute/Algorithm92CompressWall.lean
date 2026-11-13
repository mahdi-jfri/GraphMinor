module

public import GraphMinor.Compute.Algorithm92Compress

/-!
# Graph Minors XIII, (9.2): the compressed wall (`Algorithm92CompressWall.lean`)

The search of (9.2) (page 101) takes place in `H ∪ F`, where `H` is the wall. When `H ∪ F` is
compressed (`Algorithm92Compress.lean`), the wall `H` is compressed with it: each subdivision path
of `H` is a path of the path system, and the compressed path keeps its nodes and the last vertex of
each of its runs (`cWall`). This file proves:

* `isValid_cWall`: the compressed wall is a wall of the compressed graph;
* `isWallBlobMap_cBlobMap`: the blob map respects the two walls (`BlobMap.IsWallBlobMap`), so a
  star found in the compressed graph lifts to a star of `H` (`Algorithm92Lift.lean`);
* `vertCell_cWall_node`, `vertCell_cWall_rep`: a vertex of the compressed wall lies in the same
  cell of the drawing of the wall as the vertices it stands for, so distances are kept.
-/

public section

namespace GraphMinor.Compute

namespace Alg92

open WallOfHeight

variable {n : ℕ} {S : Finset (Fin n)} {Ps : List (List (Fin n))} {G : MultiDigraph n}

section Local

variable (hP : IsPathSystem G S Ps)
include hP

/-- Two consecutive non-nodes of a path have the same blob. -/
theorem IsPathSystem.cBlob_eq_of_consec {P : List (Fin n)} (hPs : P ∈ Ps) {y z : Fin n}
    (hyz : Consec P y z) (hyS : y ∉ S) (hzS : z ∉ S) : cBlob S Ps y = cBlob S Ps z := by
  obtain ⟨A, a, R, c, B, hdec, ha, hc, -, hyR, hrun⟩ := hP.exists_run hPs hyz.mem_left hyS
  rcases hP.cEdge_mem_run hPs hdec hyR hyS ⟨P, hPs, Or.inl hyz⟩ with hzR | rfl | rfl
  · rw [(hrun y hyR).1, (hrun z hzR).1]
  · exact absurd ha hzS
  · exact absurd hc hzS

/-- A non-node followed by a node on a path is the last vertex of its run. -/
theorem IsPathSystem.cRep_eq_self_of_consec {P : List (Fin n)} (hPs : P ∈ Ps) {y z : Fin n}
    (hyz : Consec P y z) (hyS : y ∉ S) (hzS : z ∈ S) : cRep S Ps y = y := by
  obtain ⟨A, a, R, c, B, hdec, -, -, hR, hyR, hrun⟩ := hP.exists_run hPs hyz.mem_left hyS
  obtain ⟨R₁, R₂, rfl⟩ := List.append_of_mem hyR
  have hsplit : P = (A ++ a :: R₁) ++ y :: (R₂ ++ c :: B) := by rw [hdec]; simp
  have hnext := hyz.eq_of_split (hP.nodup P hPs) hsplit
  cases R₂ with
  | nil =>
    simp only [cRep, (hrun y hyR).1]
    simp
  | cons w R₂ =>
    simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hnext
    subst hnext
    exact absurd hzS (hR w (by simp))

theorem IsPathSystem.cRep_gap {P : List (Fin n)} (hPs : P ∈ Ps) :
    ∀ (M X Y : List (Fin n)) (u v : Fin n), P = X ++ u :: M ++ v :: Y →
      (∀ m ∈ M, cRep S Ps m ≠ m) → cRep S Ps v = v →
      M = [] ∨ (v ∉ S ∧ ∀ m ∈ M, cRep S Ps m = v)
  | [], _, _, _, _, _, _, _ => Or.inl rfl
  | m :: M', X, Y, u, v, hdec, hM, hv => by
    right
    have hdec' : P = (X ++ [u]) ++ m :: M' ++ v :: Y := by rw [hdec]; simp
    have hM' : ∀ m' ∈ M', cRep S Ps m' ≠ m' := fun m' hm' => hM m' (by simp [hm'])
    have hmS : m ∉ S := fun hmS => hM m (by simp) (cRep_of_mem_S hmS)
    cases M' with
    | nil =>
      have hcon : Consec P m v := ⟨X ++ [u], Y, by rw [hdec]; simp⟩
      have hvS : v ∉ S := fun hvS => hM m (by simp) (hP.cRep_eq_self_of_consec hPs hcon hmS hvS)
      refine ⟨hvS, fun m' hm' => ?_⟩
      rw [List.mem_singleton] at hm'
      subst hm'
      have := hP.cBlob_eq_of_consec hPs hcon hmS hvS
      rw [← hv]; simp only [cRep, this]
    | cons m' M'' =>
      obtain ⟨hvS, hall⟩ :=
        (IsPathSystem.cRep_gap hPs (m' :: M'') (X ++ [u]) Y m v hdec' hM' hv).resolve_left (by simp)
      have hcon : Consec P m m' := ⟨X ++ [u], M'' ++ v :: Y, by rw [hdec]; simp⟩
      have hm'S : m' ∉ S := fun hS => hM' m' (by simp) (cRep_of_mem_S hS)
      have hbl := hP.cBlob_eq_of_consec hPs hcon hmS hm'S
      refine ⟨hvS, fun w hw => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · rw [← hall m' (by simp)]; simp only [cRep, hbl]
      · exact hall w hw

/-- The last vertices of runs that follow each other on a path are adjacent in the compressed
graph. -/
theorem IsPathSystem.cAdj_of_consec_filter {P : List (Fin n)} (hPs : P ∈ Ps) {u v : Fin n}
    (huv : Consec (P.filter (fun y => decide (cRep S Ps y = y))) u v) : CAdj S Ps u v := by
  have hu : cRep S Ps u = u := by
    simpa using (List.mem_filter.mp huv.mem_left).2
  have hv : cRep S Ps v = v := by
    simpa using (List.mem_filter.mp huv.mem_right).2
  obtain ⟨X, M, Y, hdec, hM⟩ := exists_of_consec_filter huv
  have hM' : ∀ m ∈ M, cRep S Ps m ≠ m := fun m hm => by simpa using hM m hm
  have hne : u ≠ v := by
    intro huv'
    subst huv'
    have hnd := hP.nodup P hPs
    rw [hdec] at hnd
    simp [List.nodup_append] at hnd
  refine ⟨hne, ?_⟩
  rcases hP.cRep_gap hPs M X Y u v hdec hM' hv with rfl | ⟨-, hall⟩
  · exact ⟨u, v, ⟨P, hPs, Or.inl ⟨X, Y, by rw [hdec]; simp⟩⟩, hu, hv⟩
  · cases M with
    | nil => exact ⟨u, v, ⟨P, hPs, Or.inl ⟨X, Y, by rw [hdec]; simp⟩⟩, hu, hv⟩
    | cons m M' =>
      exact ⟨u, m, ⟨P, hPs, Or.inl ⟨X, M' ++ v :: Y, by rw [hdec]; simp⟩⟩, hu, hall m (by simp)⟩

/-- The representative of a vertex of a path is on the compressed path. -/
theorem IsPathSystem.cRep_mem_filter {P : List (Fin n)} (hPs : P ∈ Ps) {y : Fin n} (hyP : y ∈ P) :
    cRep S Ps y ∈ P.filter (fun y => decide (cRep S Ps y = y)) := by
  rw [List.mem_filter]
  by_cases hyS : y ∈ S
  · rw [cRep_of_mem_S hyS]; exact ⟨hyP, by simp [cRep_of_mem_S hyS]⟩
  · obtain ⟨A, a, R, c, B, hdec, -, -, -, hyR, hrun⟩ := hP.exists_run hPs hyP hyS
    have hRne : R ≠ [] := List.ne_nil_of_mem hyR
    have hrep : cRep S Ps y = R.getLast hRne := by simp only [cRep, (hrun y hyR).1]
    have hlast := List.getLast_mem hRne
    refine ⟨by rw [hrep, hdec]; simp [hlast], ?_⟩
    rw [hrep]
    simp only [cRep, (hrun _ hlast).1, decide_true]

end Local

/-! ### The compressed wall -/

variable (S Ps)

/-- The test "`y` stands for its own blob" (a node, or the last vertex of a run). -/
@[expose] abbrev isRepB (y : Fin n) : Bool := decide (cRep S Ps y = y)

variable {N : ℕ} (e : Fin N → Fin n) (ι : Fin n → Fin N)

/-- The compressed wall: the branch vertices are kept, and each subdivision path keeps its nodes
and the last vertex of each of its runs. -/
@[expose] def cWall {h : ℕ} (W : WallOfHeight h G) : WallOfHeight h (cGraph S Ps e) where
  branchVert u := ι (W.branchVert u)
  internalVerts k := ((W.internalVerts k).filter (isRepB S Ps)).map ι

/-- The conditions under which a wall `W` of `G` is compressed with a path system: the paths of
`W` are paths of the system, the branch vertices are nodes, and `e`, `ι` number the vertices of
the compressed graph. -/
structure IsCompression {h : ℕ} (W : WallOfHeight h G) : Prop where
  path : IsPathSystem G S Ps
  valid : W.IsValid
  branch_mem : ∀ u, W.branchVert u ∈ S
  wall_mem : ∀ k, W.subdivPathVerts k ∈ Ps
  inj : Function.Injective e
  mem_cVerts : ∀ i, e i ∈ cVerts S Ps
  e_ι : ∀ y ∈ cVerts S Ps, e (ι y) = y

variable {S Ps e ι}

section Compression

variable {h : ℕ} {W : WallOfHeight h G} (hC : IsCompression S Ps e ι W)
include hC

theorem IsCompression.ι_e (i : Fin N) : ι (e i) = i :=
  hC.inj (hC.e_ι _ (hC.mem_cVerts i))

theorem IsCompression.ι_inj {y z : Fin n} (hy : y ∈ cVerts S Ps) (hz : z ∈ cVerts S Ps)
    (h : ι y = ι z) : y = z := by
  rw [← hC.e_ι y hy, ← hC.e_ι z hz, h]

omit hC in
theorem IsCompression.mem_cVerts_of_S {y : Fin n} (hy : y ∈ S) : y ∈ cVerts S Ps :=
  mem_cVerts_iff.mpr (Or.inl hy)

omit hC in
theorem IsCompression.mem_cVerts_of_filter {P : List (Fin n)} (hPs : P ∈ Ps) {y : Fin n}
    (hy : y ∈ P.filter (isRepB S Ps)) : y ∈ cVerts S Ps := by
  rw [List.mem_filter] at hy
  exact mem_cVerts_iff.mpr (Or.inr ⟨⟨P, hPs, hy.1⟩, by simpa using hy.2⟩)

theorem IsCompression.subdivPathVerts_cWall (k : Fin (elemWallEdges h).length) :
    (cWall S Ps e ι W).subdivPathVerts k = ((W.subdivPathVerts k).filter (isRepB S Ps)).map ι := by
  have h1 := hC.branch_mem ((elemWallEdges h)[k.1]'k.2).1
  have h2 := hC.branch_mem ((elemWallEdges h)[k.1]'k.2).2
  simp only [subdivPathVerts, cWall, List.filter_append, List.map_append]
  simp [isRepB, cRep_of_mem_S h1, cRep_of_mem_S h2]

/-- **The compressed wall is a wall** of the compressed graph. -/
theorem IsCompression.isValid_cWall : (cWall S Ps e ι W).IsValid := by
  have hv := hC.valid
  refine ⟨?_, fun k => ⟨?_, ?_⟩, fun k u => ?_, fun k₁ k₂ hk => ?_⟩
  · intro u u' huu
    exact hv.1 (hC.ι_inj (IsCompression.mem_cVerts_of_S (hC.branch_mem u))
      (IsCompression.mem_cVerts_of_S (hC.branch_mem u')) huu)
  · rw [hC.subdivPathVerts_cWall]
    refine List.Nodup.map_on (fun y hy z hz hyz => ?_) ((hv.2.1 k).1.sublist List.filter_sublist)
    exact hC.ι_inj (IsCompression.mem_cVerts_of_filter (hC.wall_mem k) hy)
      (IsCompression.mem_cVerts_of_filter (hC.wall_mem k) hz) hyz
  · rw [hC.subdivPathVerts_cWall, isSimpleWalkList_iff_consec]
    intro i j hij
    obtain ⟨a, b, hab, rfl, rfl⟩ := exists_of_consec_map hij
    rw [cGraph_adj, hC.e_ι a (IsCompression.mem_cVerts_of_filter (hC.wall_mem k) hab.mem_left),
      hC.e_ι b (IsCompression.mem_cVerts_of_filter (hC.wall_mem k) hab.mem_right)]
    exact hC.path.cAdj_of_consec_filter (hC.wall_mem k) hab
  · intro hmem
    simp only [cWall, List.mem_map, List.mem_filter] at hmem
    obtain ⟨y, ⟨hy, hyr⟩, hyι⟩ := hmem
    have hyv : y ∈ cVerts S Ps := mem_cVerts_iff.mpr
      (Or.inr ⟨⟨_, hC.wall_mem k, (W.mem_subdivPathVerts_iff k y).mpr (Or.inr (Or.inl hy))⟩,
        by simpa using hyr⟩)
    have := hC.ι_inj hyv (IsCompression.mem_cVerts_of_S (hC.branch_mem u)) hyι
    exact hv.2.2.1 k u (this ▸ hy)
  · intro i hi₁ hi₂
    simp only [cWall, List.mem_map, List.mem_filter] at hi₁ hi₂
    obtain ⟨y, ⟨hy, hyr⟩, rfl⟩ := hi₁
    obtain ⟨z, ⟨hz, hzr⟩, hzy⟩ := hi₂
    have hyv : y ∈ cVerts S Ps := mem_cVerts_iff.mpr
      (Or.inr ⟨⟨_, hC.wall_mem k₁, (W.mem_subdivPathVerts_iff k₁ y).mpr (Or.inr (Or.inl hy))⟩,
        by simpa using hyr⟩)
    have hzv : z ∈ cVerts S Ps := mem_cVerts_iff.mpr
      (Or.inr ⟨⟨_, hC.wall_mem k₂, (W.mem_subdivPathVerts_iff k₂ z).mpr (Or.inr (Or.inl hz))⟩,
        by simpa using hzr⟩)
    have := hC.ι_inj hzv hyv hzy
    exact hv.2.2.2 k₁ k₂ hk hy (this ▸ hz)

omit hC in
/-- Two walls give the same cell to two vertices that are branch vertices for the same `u` and
inner vertices of the same paths. -/
theorem vertCell_eq_of_iff {N' : ℕ} {G' : MultiDigraph N'} {W' : WallOfHeight h G'}
    {i : Fin N'} {y : Fin n}
    (hb : ∀ u, W'.branchVert u = i ↔ W.branchVert u = y)
    (hi : ∀ k, i ∈ W'.internalVerts k ↔ y ∈ W.internalVerts k) :
    W'.vertCell i = W.vertCell y := by
  have e1 : (fun u => decide (W'.branchVert u = i)) = (fun u => decide (W.branchVert u = y)) :=
    funext fun u => by simp [hb u]
  have e2 : (fun k => decide (i ∈ W'.internalVerts k)) =
      (fun k => decide (y ∈ W.internalVerts k)) :=
    funext fun k => by simp [hi k]
  unfold vertCell
  rw [e1, e2]

/-- A node of the compressed wall lies in the same cell as the vertex it stands for. -/
theorem IsCompression.vertCell_cWall_node {y : Fin n} (hy : y ∈ S) :
    (cWall S Ps e ι W).vertCell (ι y) = W.vertCell y := by
  have hyv : y ∈ cVerts S Ps := IsCompression.mem_cVerts_of_S hy
  refine vertCell_eq_of_iff (fun u => ⟨fun h => ?_, fun h => ?_⟩) (fun k => ⟨fun h => ?_,
    fun h => ?_⟩)
  · exact hC.ι_inj (IsCompression.mem_cVerts_of_S (hC.branch_mem u)) hyv h
  · simp only [cWall, h]
  · simp only [cWall, List.mem_map, List.mem_filter] at h
    obtain ⟨z, ⟨hz, hzr⟩, hzy⟩ := h
    have hzv : z ∈ cVerts S Ps := mem_cVerts_iff.mpr
      (Or.inr ⟨⟨_, hC.wall_mem k, (W.mem_subdivPathVerts_iff k z).mpr (Or.inr (Or.inl hz))⟩,
        by simpa using hzr⟩)
    exact hC.ι_inj hzv hyv hzy ▸ hz
  · simp only [cWall, List.mem_map, List.mem_filter]
    exact ⟨y, ⟨h, by simp [cRep_of_mem_S hy]⟩, rfl⟩

/-- A vertex of `W` that is not a node lies in the same cell as its representative in the
compressed wall. -/
theorem IsCompression.vertCell_cWall_rep {y : Fin n} {k₀ : Fin (elemWallEdges h).length}
    (hyk : y ∈ W.internalVerts k₀) (hyS : y ∉ S) :
    (cWall S Ps e ι W).vertCell (ι (cRep S Ps y)) = W.vertCell y := by
  have hv := hC.valid
  have hyL : y ∈ W.subdivPathVerts k₀ :=
    (W.mem_subdivPathVerts_iff k₀ y).mpr (Or.inr (Or.inl hyk))
  have hon : OnPath Ps y := ⟨_, hC.wall_mem k₀, hyL⟩
  obtain ⟨hrS, -, hrr, -⟩ := hC.path.cRep_not_mem hon hyS
  have hrf := hC.path.cRep_mem_filter (hC.wall_mem k₀) hyL
  have hrv := IsCompression.mem_cVerts_of_filter (hC.wall_mem k₀) hrf
  -- the representative is an inner vertex of the path `k₀`
  have hrk : cRep S Ps y ∈ W.internalVerts k₀ := by
    rcases (W.mem_subdivPathVerts_iff k₀ _).mp (List.mem_filter.mp hrf).1 with h | h | h
    · exact absurd (h ▸ hC.branch_mem _) hrS
    · exact h
    · exact absurd (h ▸ hC.branch_mem _) hrS
  refine vertCell_eq_of_iff (fun u => ⟨fun h => ?_, fun h => ?_⟩) (fun k => ⟨fun h => ?_,
    fun h => ?_⟩)
  · have := hC.ι_inj (IsCompression.mem_cVerts_of_S (hC.branch_mem u)) hrv h
    exact absurd (this ▸ hC.branch_mem u) hrS
  · exact absurd (h ▸ hC.branch_mem u) hyS
  · simp only [cWall, List.mem_map, List.mem_filter] at h
    obtain ⟨z, ⟨hz, hzr⟩, hzy⟩ := h
    have hzv : z ∈ cVerts S Ps := mem_cVerts_iff.mpr
      (Or.inr ⟨⟨_, hC.wall_mem k, (W.mem_subdivPathVerts_iff k z).mpr (Or.inr (Or.inl hz))⟩,
        by simpa using hzr⟩)
    have hzr' := hC.ι_inj hzv hrv hzy
    subst hzr'
    by_contra hk
    exact hv.2.2.2 k k₀ (fun h => hk (h ▸ hyk)) hz hrk
  · simp only [cWall, List.mem_map, List.mem_filter]
    refine ⟨cRep S Ps y, ⟨?_, by simp [hrr]⟩, rfl⟩
    have hyL' : y ∈ W.subdivPathVerts k :=
      (W.mem_subdivPathVerts_iff k y).mpr (Or.inr (Or.inl h))
    have hrf' := hC.path.cRep_mem_filter (hC.wall_mem k) hyL'
    rcases (W.mem_subdivPathVerts_iff k _).mp (List.mem_filter.mp hrf').1 with h' | h' | h'
    · exact absurd (h' ▸ hC.branch_mem _) hrS
    · exact h'
    · exact absurd (h' ▸ hC.branch_mem _) hrS

/-- The compressed wall has the same distances as `W` between nodes. -/
theorem IsCompression.brickDist_cWall_node {y z : Fin n} (hy : y ∈ S) (hz : z ∈ S) :
    (cWall S Ps e ι W).brickDist (ι y) (ι z) = W.brickDist y z := by
  unfold brickDist
  rw [hC.vertCell_cWall_node hy, hC.vertCell_cWall_node hz]
  have : ι y = ι z ↔ y = z :=
    ⟨hC.ι_inj (IsCompression.mem_cVerts_of_S hy) (IsCompression.mem_cVerts_of_S hz), fun h => h ▸ rfl⟩
  simp only [this]

/-- **The blob map respects the walls.** -/
theorem IsCompression.isWallBlobMap_cBlobMap :
    (cBlobMap S Ps e ι).IsWallBlobMap (cWall S Ps e ι W) W := by
  have hB := isBlobMap_cBlobMap S Ps hC.path hC.inj hC.mem_cVerts hC.e_ι
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `blob_not_mem`
    intro v hv y hy hyW
    apply hv
    have hry := ((hC.path.mem_cBlob_iff (hC.mem_cVerts v)).mp hy).2
    rcases (W.mem_vertexFinset_iff y).mp hyW with ⟨u, rfl⟩ | ⟨k, hyk⟩
    · rw [cRep_of_mem_S (hC.branch_mem u)] at hry
      rw [mem_vertexFinset_iff]
      exact Or.inl ⟨u, by simp only [cWall, hry, hC.ι_e]⟩
    · have hyL : y ∈ W.subdivPathVerts k :=
        (W.mem_subdivPathVerts_iff k y).mpr (Or.inr (Or.inl hyk))
      apply mem_vertexFinset_of_mem_subdivPathVerts _ (k := k)
      rw [hC.subdivPathVerts_cWall, List.mem_map]
      exact ⟨_, hC.path.cRep_mem_filter (hC.wall_mem k) hyL, by rw [hry, hC.ι_e]⟩
  · -- `node_mem`
    intro v _ hv
    rw [mem_vertexFinset_iff] at hv ⊢
    rcases hv with ⟨u, hu⟩ | ⟨k, hk⟩
    · refine Or.inl ⟨u, ?_⟩
      simp only [cBlobMap, ← hu, cWall]
      exact (hC.e_ι _ (IsCompression.mem_cVerts_of_S (hC.branch_mem u))).symm
    · simp only [cWall, List.mem_map, List.mem_filter] at hk
      obtain ⟨y, ⟨hy, hyr⟩, rfl⟩ := hk
      refine Or.inr ⟨k, ?_⟩
      simp only [cBlobMap]
      rw [hC.e_ι y (mem_cVerts_iff.mpr (Or.inr ⟨⟨_, hC.wall_mem k,
        (W.mem_subdivPathVerts_iff k y).mpr (Or.inr (Or.inl hy))⟩, by simpa using hyr⟩))]
      exact hy
  · -- `isWallEdge`
    intro u v hu hv huv
    have huS : e u ∈ S := by simpa [cBlobMap] using hu
    have hvS : e v ∈ S := by simpa [cBlobMap] using hv
    obtain ⟨k, hk⟩ := huv
    refine ⟨k, ?_⟩
    simp only [cBlobMap] at hk
    rw [consec_iff_mem_zip, consec_iff_mem_zip] at hk ⊢
    rw [hC.subdivPathVerts_cWall]
    have hu' : isRepB S Ps (e u) = true := by simp [cRep_of_mem_S huS]
    have hv' : isRepB S Ps (e v) = true := by simp [cRep_of_mem_S hvS]
    rcases hk with hk | hk
    · left
      have := (hk.filter _ hu' hv').map ι
      rwa [hC.ι_e, hC.ι_e] at this
    · right
      have := (hk.filter _ hv' hu').map ι
      rwa [hC.ι_e, hC.ι_e] at this
  · -- `isWallEdge_mid`
    intro v w hv hvW hvw
    have hvS : e v ∉ S := by simpa [cBlobMap] using hv
    have hends := hB.adj_mid v w hv hvw
    -- `v` is the representative of a run of some path of `W`
    obtain ⟨k, hk⟩ : ∃ k, e v ∈ W.internalVerts k := by
      rcases (mem_vertexFinset_iff _ v).mp hvW with ⟨u, hu⟩ | ⟨k, hk⟩
      · exfalso; apply hvS
        rw [← hu]; simp only [cWall, hC.e_ι _ (IsCompression.mem_cVerts_of_S (hC.branch_mem u))]
        exact hC.branch_mem u
      · simp only [cWall, List.mem_map, List.mem_filter] at hk
        obtain ⟨y, ⟨hy, hyr⟩, rfl⟩ := hk
        refine ⟨k, ?_⟩
        rw [hC.e_ι y (mem_cVerts_iff.mpr (Or.inr ⟨⟨_, hC.wall_mem k,
          (W.mem_subdivPathVerts_iff k y).mpr (Or.inr (Or.inl hy))⟩, by simpa using hyr⟩))]
        exact hy
    have hvL : e v ∈ W.subdivPathVerts k :=
      (W.mem_subdivPathVerts_iff k _).mpr (Or.inr (Or.inl hk))
    obtain ⟨A, a, R, c, B, hdec, ha, hc, hR, hvR, hrun⟩ :=
      hC.path.exists_run (hC.wall_mem k) hvL hvS
    have hRne : R ≠ [] := List.ne_nil_of_mem hvR
    have hvlast : R.getLast hRne = e v := by
      have h1 : cRep S Ps (e v) = e v :=
        ((mem_cVerts_iff.mp (hC.mem_cVerts v)).resolve_left hvS).2
      rw [← h1]; simp only [cRep, (hrun _ hvR).1]
    -- the compressed path around `v` is `a, v, c`
    have hRf : R.filter (isRepB S Ps) = [e v] := by
      have hnd : R.Nodup := by
        have := (hC.valid.2.1 k).1
        rw [hdec] at this
        exact this.sublist (List.IsInfix.sublist ⟨A ++ [a], c :: B, by simp⟩)
      rw [← List.dropLast_append_getLast hRne, List.filter_append, hvlast]
      have hnot : ∀ z ∈ R.dropLast, isRepB S Ps z = false := by
        intro z hz
        have hzR : z ∈ R := List.mem_of_mem_dropLast hz
        have hz' : cRep S Ps z = e v := by
          rw [← hvlast]; simp only [cRep, (hrun z hzR).1]
        have hzne : z ≠ e v := by
          intro hzv
          rw [← List.dropLast_append_getLast hRne, hvlast] at hnd
          rw [List.nodup_append] at hnd
          exact hnd.2.2 z hz (e v) (by simp) hzv
        simp [isRepB, hz', Ne.symm hzne]
      rw [List.filter_eq_nil_iff.mpr (fun z hz => by simpa using hnot z hz)]
      simp [isRepB, show cRep S Ps (e v) = e v from by
        rw [← hvlast]; simp only [cRep, (hrun _ (List.getLast_mem hRne)).1]]
    have hfil : (W.subdivPathVerts k).filter (isRepB S Ps) =
        A.filter (isRepB S Ps) ++ a :: e v :: c :: B.filter (isRepB S Ps) := by
      rw [hdec]
      simp only [List.filter_append, List.filter_cons, hRf]
      simp [isRepB, cRep_of_mem_S ha, cRep_of_mem_S hc]
    refine ⟨k, ?_⟩
    rw [consec_iff_mem_zip, consec_iff_mem_zip, hC.subdivPathVerts_cWall, hfil]
    have hpr := (hrun _ hvR).2.1
    have hnx := (hrun _ hvR).2.2
    simp only [cBlobMap, hpr, hnx] at hends
    rcases hends with rfl | rfl
    · right
      refine ⟨(A.filter (isRepB S Ps)).map ι, (c :: B.filter (isRepB S Ps)).map ι, ?_⟩
      simp [hC.ι_e]
    · left
      refine ⟨(A.filter (isRepB S Ps)).map ι ++ [ι a], (B.filter (isRepB S Ps)).map ι, ?_⟩
      simp [hC.ι_e]
  · -- `brickDist_le`
    intro u v hu hv _ _
    have huS : e u ∈ S := by simpa [cBlobMap] using hu
    have hvS : e v ∈ S := by simpa [cBlobMap] using hv
    have := hC.brickDist_cWall_node huS hvS
    rw [hC.ι_e, hC.ι_e] at this
    simp only [cBlobMap]
    exact this.le

/-! ### Vertex sets and distances of the compressed wall -/

theorem IsCompression.mem_cVerts_of_mem_internalVerts {k : Fin (elemWallEdges h).length}
    {y : Fin n} (hy : y ∈ W.internalVerts k) (hyr : isRepB S Ps y = true) : y ∈ cVerts S Ps :=
  mem_cVerts_iff.mpr (Or.inr ⟨⟨_, hC.wall_mem k,
    (W.mem_subdivPathVerts_iff k y).mpr (Or.inr (Or.inl hy))⟩, by simpa using hyr⟩)

/-- A vertex of the compressed wall stands for a vertex of `W` in `cVerts`. -/
theorem IsCompression.exists_of_mem_vertexFinset_cWall {i : Fin N}
    (hi : i ∈ (cWall S Ps e ι W).vertexFinset) :
    ∃ y ∈ cVerts S Ps, i = ι y ∧ y ∈ W.vertexFinset := by
  rcases (mem_vertexFinset_iff _ i).mp hi with ⟨u, rfl⟩ | ⟨k, hk⟩
  · exact ⟨_, IsCompression.mem_cVerts_of_S (hC.branch_mem u), rfl,
      (W.mem_vertexFinset_iff _).mpr (Or.inl ⟨u, rfl⟩)⟩
  · simp only [cWall, List.mem_map, List.mem_filter] at hk
    obtain ⟨y, ⟨hy, hyr⟩, rfl⟩ := hk
    exact ⟨y, hC.mem_cVerts_of_mem_internalVerts hy hyr, rfl,
      (W.mem_vertexFinset_iff _).mpr (Or.inr ⟨k, hy⟩)⟩

/-- A vertex of `cVerts` is on the compressed wall exactly when it is on `W`. -/
theorem IsCompression.mem_vertexFinset_cWall_iff {y : Fin n} (hy : y ∈ cVerts S Ps) :
    ι y ∈ (cWall S Ps e ι W).vertexFinset ↔ y ∈ W.vertexFinset := by
  constructor
  · intro h
    obtain ⟨z, hz, hzy, hzW⟩ := hC.exists_of_mem_vertexFinset_cWall h
    rwa [hC.ι_inj hy hz hzy]
  · intro h
    rw [mem_vertexFinset_iff]
    rcases (W.mem_vertexFinset_iff y).mp h with ⟨u, rfl⟩ | ⟨k, hk⟩
    · exact Or.inl ⟨u, rfl⟩
    · refine Or.inr ⟨k, ?_⟩
      simp only [cWall, List.mem_map, List.mem_filter]
      refine ⟨y, ⟨hk, ?_⟩, rfl⟩
      rcases mem_cVerts_iff.mp hy with hyS | ⟨-, hyr⟩
      · simp [cRep_of_mem_S hyS]
      · simp [hyr]

/-- A node is on the perimeter of the compressed wall exactly when it is on the perimeter
of `W`. -/
theorem IsCompression.mem_perimeterFinset_cWall_iff {y : Fin n} (hy : y ∈ S) :
    ι y ∈ (cWall S Ps e ι W).perimeterFinset ↔ y ∈ W.perimeterFinset := by
  rw [mem_perimeterFinset_iff, mem_perimeterFinset_iff]
  refine exists_congr fun k => and_congr_right fun _ => ?_
  rw [hC.subdivPathVerts_cWall, List.mem_map]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hzv := IsCompression.mem_cVerts_of_filter (hC.wall_mem k) hz
    rw [← hC.ι_inj hzv (IsCompression.mem_cVerts_of_S hy) hzy]
    exact (List.mem_filter.mp hz).1
  · intro h
    exact ⟨y, List.mem_filter.mpr ⟨h, by simp [cRep_of_mem_S hy]⟩, rfl⟩

/-- A node is inside the compressed wall exactly when it is inside `W`. -/
theorem IsCompression.mem_insideFinset_cWall_iff {y : Fin n} (hy : y ∈ S) :
    ι y ∈ (cWall S Ps e ι W).insideFinset ↔ y ∈ W.insideFinset := by
  simp only [insideFinset, Finset.mem_sdiff,
    hC.mem_vertexFinset_cWall_iff (IsCompression.mem_cVerts_of_S hy),
    hC.mem_perimeterFinset_cWall_iff hy]

/-- A vertex of `W` in `cVerts` lies in the same cell as its copy in the compressed wall. -/
theorem IsCompression.vertCell_cWall {y : Fin n} (hy : y ∈ cVerts S Ps)
    (hyW : y ∈ W.vertexFinset) : (cWall S Ps e ι W).vertCell (ι y) = W.vertCell y := by
  by_cases hyS : y ∈ S
  · exact hC.vertCell_cWall_node hyS
  · obtain ⟨-, hyr⟩ := (mem_cVerts_iff.mp hy).resolve_left hyS
    rcases (W.mem_vertexFinset_iff y).mp hyW with ⟨u, rfl⟩ | ⟨k, hk⟩
    · exact absurd (hC.branch_mem u) hyS
    · have := hC.vertCell_cWall_rep hk hyS
      rwa [hyr] at this

/-- Distances in the compressed wall are the distances in `W`. -/
theorem IsCompression.brickDist_cWall {y z : Fin n} (hy : y ∈ cVerts S Ps) (hz : z ∈ cVerts S Ps)
    (hyW : y ∈ W.vertexFinset) (hzW : z ∈ W.vertexFinset) :
    (cWall S Ps e ι W).brickDist (ι y) (ι z) = W.brickDist y z := by
  unfold brickDist
  rw [hC.vertCell_cWall hy hyW, hC.vertCell_cWall hz hzW]
  have : ι y = ι z ↔ y = z := ⟨hC.ι_inj hy hz, fun h => h ▸ rfl⟩
  simp only [this]

omit hC in
/-- Compressing commutes with taking a subwall. -/
theorem cWall_subwallAt (i j h' : ℕ) (hh' : 1 ≤ h') (hle : h' ≤ h) (hi_even : Even i)
    (hj_even : Even j) (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') :
    cWall S Ps e ι (W.subwallAt i j h' hh' hle hi_even hj_even hi_le hj_le) =
      (cWall S Ps e ι W).subwallAt i j h' hh' hle hi_even hj_even hi_le hj_le := by
  unfold cWall subwallAt
  congr 1
  funext k
  split <;> simp_all

/-- A subwall of `W` is compressed with the same path system. -/
theorem IsCompression.subwallAt (i j h' : ℕ) (hh' : 1 ≤ h') (hle : h' ≤ h) (hi_even : Even i)
    (hj_even : Even j) (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') :
    IsCompression S Ps e ι (W.subwallAt i j h' hh' hle hi_even hj_even hi_le hj_le) where
  path := hC.path
  valid := isValid_subwallAt W hC.valid i j h' hh' hle hi_even hj_even hi_le hj_le
  branch_mem u := hC.branch_mem _
  wall_mem k := by
    obtain ⟨kW, -, -, -, hk⟩ :=
      W.exists_subdivPathVerts_subwallAt i j h' hh' hle hi_even hj_even hi_le hj_le k
    rw [hk]; exact hC.wall_mem kW
  inj := hC.inj
  mem_cVerts := hC.mem_cVerts
  e_ι := hC.e_ι

end Compression

end Alg92

end GraphMinor.Compute
