module

public import GraphMinor.Compute.Algorithm92Layout
public import GraphMinor.Compute.Algorithm92Ram
public import GraphMinor.Compute.Algorithm92FClaim

/-!
# Graph Minors XIII, (9.2): writing the paths of `H ∪ F` into one array (`Algorithm92Build.lean`)

The first program after `F` (page 101 of Graph Minors XIII) reads the arrays that the program that
finds `F` wrote: `x.W.encList` and `encSegs92 segs`. It writes the layout of the paths of `H ∪ F`
(`layout`, from `Algorithm92Layout.lean`) into one array: for each path of the wall, the separator,
the two branch vertices at its ends and its inner vertices; for each path of `F`, the separator and
its vertices. On the way it marks the nodes: the branch vertices and the two ends of each path of
`F`.

This file states where things are in the two encodings and in the layout:

* `wcur k` and `scur j`: the position in `x.W.encList` of the length of the `k`-th path of the
  wall, and in `encSegs92 segs` of the length of the `j`-th path of `F`.
* `lpos j`: the position in the layout of the block of the `j`-th path of `fPaths`.
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

open WallOfHeight

variable {l m p h k r : ℕ} (x : Alg92Input l m p h k r) (segs : List (List (Fin x.n)))

/-! ### Positions in the encodings -/

/-- The inner vertices of the paths of the wall, as numbers. -/
def ivl : List (List ℕ) :=
  (List.finRange (elemWallEdges h).length).map (fun k => (x.W.internalVerts k).map Fin.val)

/-- The paths of `F`, as numbers. -/
def sgl : List (List ℕ) := segs.map (fun P => P.map Fin.val)

/-- A list with its length in front. -/
def lenPre (c : List ℕ) : List ℕ := c.length :: c

/-- The blocks of the layout. -/
def blocks : List (List ℕ) := (fPaths x segs).map (layBlock x.n)

/-- The branch vertices, as numbers. -/
def bvl : List ℕ := (List.finRange (elemWallNumVerts h)).map (fun u => (x.W.branchVert u).val)

theorem encList_eq : x.W.encList = [h, elemWallNumVerts h, (elemWallEdges h).length] ++ bvl x ++
    ((ivl x).map lenPre).flatten := by
  simp [WallOfHeight.encList, bvl, ivl, List.flatMap_def, lenPre, Function.comp_def]

theorem encSegs92_eq : encSegs92 segs = segs.length :: ((sgl x segs).map lenPre).flatten := by
  simp [encSegs92, sgl, List.flatMap_def, lenPre, Function.comp_def]

theorem layout_eq : layout x segs = (blocks x segs).flatten := by
  simp [layout, blocks, List.flatMap_def]

/-- The position in `x.W.encList` of the length of the `k`-th path of the wall. -/
def wcur (k : ℕ) : ℕ := 3 + elemWallNumVerts h + ((((ivl x).map lenPre).take k).flatten).length

/-- The position in `encSegs92 segs` of the length of the `j`-th path of `F`. -/
def scur (j : ℕ) : ℕ := 1 + ((((sgl x segs).map lenPre).take j).flatten).length

/-- The position in the layout of the block of the `j`-th path of `fPaths`. -/
def lpos (j : ℕ) : ℕ := (((blocks x segs).take j).flatten).length

variable {x segs}

@[simp] theorem length_ivl : (ivl x).length = (elemWallEdges h).length := by simp [ivl]

@[simp] theorem length_sgl : (sgl x segs).length = segs.length := by simp [sgl]

@[simp] theorem length_blocks : (blocks x segs).length = (elemWallEdges h).length + segs.length := by
  simp [blocks, fPaths]

@[simp] theorem length_bvl : (bvl x).length = elemWallNumVerts h := by simp [bvl]

theorem getD_encList_bv (u : ℕ) (hu : u < elemWallNumVerts h) :
    x.W.encList.getD (3 + u) 0 = (x.W.branchVert ⟨u, hu⟩).val := by
  rw [encList_eq, List.append_assoc, List.getD_append_right _ _ _ _ (by simp),
    show 3 + u - [h, elemWallNumVerts h, (elemWallEdges h).length].length = u by simp,
    List.getD_append _ _ _ _ (by simpa using hu)]
  simp [bvl, List.getD_eq_getElem?_getD, hu]

theorem getD_lenPre_flatten (LL : List (List ℕ)) {j : ℕ} (hj : j < LL.length) :
    (LL.map lenPre).flatten.getD (((LL.map lenPre).take j).flatten.length) 0 = LL[j].length ∧
    ∀ t < LL[j].length,
      (LL.map lenPre).flatten.getD (((LL.map lenPre).take j).flatten.length + 1 + t) 0 =
        LL[j].getD t 0 := by
  have hj' : j < (LL.map lenPre).length := by simpa using hj
  refine ⟨?_, fun t ht => ?_⟩
  · have := getD_flatten_take (LL.map lenPre) hj' (t := 0) (by simp [lenPre])
    rw [Nat.add_zero] at this
    rw [this]
    simp [lenPre]
  · have := getD_flatten_take (LL.map lenPre) hj' (t := 1 + t) (by simp [lenPre]; omega)
    rw [← Nat.add_assoc] at this
    rw [this]
    simp [lenPre, Nat.add_comm 1 t]

theorem wcur_succ {k' : ℕ} (hk : k' < (elemWallEdges h).length) :
    wcur x (k' + 1) = wcur x k' + 1 + (x.W.internalVerts ⟨k', hk⟩).length := by
  unfold wcur
  rw [length_flatten_take_succ _ (by simpa using hk)]
  simp [ivl, lenPre]
  omega

theorem scur_succ {j : ℕ} (hj : j < segs.length) :
    scur x segs (j + 1) = scur x segs j + 1 + segs[j].length := by
  unfold scur
  rw [length_flatten_take_succ _ (by simpa using hj)]
  simp [sgl, lenPre]
  omega

theorem lpos_succ {j : ℕ} (hj : j < (elemWallEdges h).length + segs.length) :
    lpos x segs (j + 1) = lpos x segs j + ((blocks x segs)[j]'(by simpa using hj)).length := by
  unfold lpos
  rw [length_flatten_take_succ _ (by simpa using hj)]

theorem getD_encList_wall {k' : ℕ} (hk : k' < (elemWallEdges h).length) :
    x.W.encList.getD (wcur x k') 0 = (x.W.internalVerts ⟨k', hk⟩).length ∧
    ∀ t < (x.W.internalVerts ⟨k', hk⟩).length,
      x.W.encList.getD (wcur x k' + 1 + t) 0 = ((x.W.internalVerts ⟨k', hk⟩).map Fin.val).getD t 0 := by
  have hk' : k' < (ivl x).length := by simpa using hk
  obtain ⟨h1, h2⟩ := getD_lenPre_flatten (ivl x) hk'
  have hlen3 : ([h, elemWallNumVerts h, (elemWallEdges h).length] ++ bvl x).length =
      3 + elemWallNumVerts h := by simp; omega
  have e : ∀ q, x.W.encList.getD (3 + elemWallNumVerts h + q) 0 =
      ((ivl x).map lenPre).flatten.getD q 0 := by
    intro q
    rw [encList_eq, List.getD_append_right _ _ _ _ (by omega), hlen3, Nat.add_sub_cancel_left]
  have hiv : (ivl x)[k'] = (x.W.internalVerts ⟨k', hk⟩).map Fin.val := by simp [ivl]
  refine ⟨?_, fun t ht => ?_⟩
  · rw [wcur, e, h1, hiv, List.length_map]
  · have := h2 t (by rw [hiv]; simpa using ht)
    rw [wcur, Nat.add_assoc, Nat.add_assoc, e, ← Nat.add_assoc, this, hiv]

theorem getD_encSegs {j : ℕ} (hj : j < segs.length) :
    (encSegs92 segs).getD (scur x segs j) 0 = segs[j].length ∧
    ∀ t < segs[j].length,
      (encSegs92 segs).getD (scur x segs j + 1 + t) 0 = (segs[j].map Fin.val).getD t 0 := by
  have hj' : j < (sgl x segs).length := by simpa using hj
  obtain ⟨h1, h2⟩ := getD_lenPre_flatten (sgl x segs) hj'
  have e : ∀ q, (encSegs92 segs).getD (1 + q) 0 = ((sgl x segs).map lenPre).flatten.getD q 0 := by
    intro q
    rw [encSegs92_eq, Nat.add_comm, List.getD_cons_succ]
  have hsg : (sgl x segs)[j] = segs[j].map Fin.val := by simp [sgl]
  refine ⟨?_, fun t ht => ?_⟩
  · rw [scur, e, h1, hsg, List.length_map]
  · have := h2 t (by rw [hsg]; simpa using ht)
    rw [scur, Nat.add_assoc, Nat.add_assoc, e, ← Nat.add_assoc, this, hsg]

theorem blocks_wall {k' : ℕ} (hk : k' < (elemWallEdges h).length) :
    (blocks x segs)[k']'(by simp; omega) = x.n :: (x.W.branchVert ((elemWallEdges h)[k']).1).val ::
      ((x.W.internalVerts ⟨k', hk⟩).map Fin.val ++ [(x.W.branchVert ((elemWallEdges h)[k']).2).val]) := by
  simp only [blocks, fPaths, List.map_append]
  rw [List.getElem_append_left (by simpa using hk)]
  simp [layBlock, subdivPathVerts]

theorem blocks_seg {j : ℕ} (hj : j < segs.length) :
    (blocks x segs)[(elemWallEdges h).length + j]'(by simp; omega) = x.n :: segs[j].map Fin.val := by
  simp [blocks, fPaths, layBlock]

theorem length_layout :
    (layout x segs).length + (4 + elemWallNumVerts h) =
      x.W.encList.length + 2 * (elemWallEdges h).length + (encSegs92 segs).length := by
  have h1 : (layout x segs).length =
      ((List.finRange (elemWallEdges h).length).map
        (fun k => (x.W.internalVerts k).length + 3)).sum +
      (segs.map (fun P => P.length + 1)).sum := by
    simp [layout, fPaths, List.length_flatMap, layBlock, subdivPathVerts, Function.comp_def]
    omega
  have h2 : x.W.encList.length = 3 + elemWallNumVerts h +
      ((List.finRange (elemWallEdges h).length).map
        (fun k => (x.W.internalVerts k).length + 1)).sum := by
    simp [WallOfHeight.encList, List.length_flatMap, Function.comp_def]
    omega
  have h3 : (encSegs92 segs).length = 1 + (segs.map (fun P => P.length + 1)).sum := by
    simp [encSegs92, List.length_flatMap, Function.comp_def]
    omega
  have h4 : ((List.finRange (elemWallEdges h).length).map
        (fun k => (x.W.internalVerts k).length + 3)).sum =
      ((List.finRange (elemWallEdges h).length).map
        (fun k => (x.W.internalVerts k).length + 1)).sum + 2 * (elemWallEdges h).length := by
    rw [List.sum_map_add, List.sum_map_add]
    simp
    omega
  omega

end Alg92

end GraphMinor.Compute
