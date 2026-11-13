module

public import GraphMinor.Compute.Algorithm92Key

/-!
# Graph Minors XIII, (9.2): the paths of `H ∪ F` in one array (`Algorithm92Layout.lean`)

The program of (9.2) compresses `H ∪ F` (page 101: "Since the size of $F$ is bounded (exept for
divalent vertices) ..."). To do so it writes all paths of `H ∪ F` into one array, the *layout*:
each path is written after a separator, the number `n` of vertices of `G`. One pass over the
layout then finds the runs of non-nodes: the register that holds the start of the current run is
`rsIdx`, and the program stores for each non-node the start of its run, and for each run start the
position of its end. This file proves what these numbers mean.

* `layout x segs`: the layout, and `ndB x segs`: the node test on numbers (the separator counts as
  a node).
* `rsIdx nd L j`: the start of the run of position `j`, as computed by the pass.
* `sweep_spec`: if `rs` and `en` hold what the pass stores, then for every non-node `y` on a path,
  the run of `y` in the layout starts at `rs y`, ends at `en (rs y)`, its last vertex is `cRep y`,
  and the vertex before it is `cPrev y`.
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

open WallOfHeight

/-! ### The start of the run of a position -/

/-- The start of the run of position `j` of `L`: the position after the last node before `j` (or
`0`). This is the value of the register of the pass before it reads position `j`. -/
def rsIdx (nd : ℕ → Bool) (L : List ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if nd (L.getD j 0) then j + 1 else rsIdx nd L j

theorem rsIdx_le (nd : ℕ → Bool) (L : List ℕ) : ∀ j, rsIdx nd L j ≤ j
  | 0 => le_rfl
  | j + 1 => by
    unfold rsIdx
    split_ifs
    · exact le_rfl
    · exact (rsIdx_le nd L j).trans (Nat.le_succ j)

theorem rsIdx_mono (nd : ℕ → Bool) (L : List ℕ) {i : ℕ} : ∀ {j}, i ≤ j → rsIdx nd L i ≤ rsIdx nd L j
  | 0, h => by rw [Nat.le_zero.mp h]
  | j + 1, h => by
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · show rsIdx nd L i ≤ (if nd (L.getD j 0) then j + 1 else rsIdx nd L j)
      split_ifs
      · exact (rsIdx_le nd L i).trans (by omega)
      · exact rsIdx_mono nd L (by omega)
    · rw [Nat.le_antisymm h hge]

/-- After a node at position `j`, the run starts at `j + 1`. -/
theorem rsIdx_succ_of_nd {nd : ℕ → Bool} {L : List ℕ} {j : ℕ} (h : nd (L.getD j 0) = true) :
    rsIdx nd L (j + 1) = j + 1 := by
  show (if nd (L.getD j 0) then j + 1 else rsIdx nd L j) = j + 1
  rw [if_pos h]

/-- Inside a run `R` that follows a node `a`, the run starts just after `a`. -/
theorem rsIdx_run {nd : ℕ → Bool} {L X R Y : List ℕ} {a : ℕ} (hL : L = X ++ a :: R ++ Y)
    (ha : nd a = true) (hR : ∀ v ∈ R, nd v = false) :
    ∀ t ≤ R.length, rsIdx nd L (X.length + 1 + t) = X.length + 1
  | 0, _ => by
    apply rsIdx_succ_of_nd
    rw [hL, List.append_assoc, List.getD_append_right _ _ _ _ le_rfl]
    simpa using ha
  | t + 1, ht => by
    rw [show X.length + 1 + (t + 1) = (X.length + 1 + t) + 1 by omega]
    show (if nd (L.getD (X.length + 1 + t) 0) then _ else rsIdx nd L (X.length + 1 + t)) = _
    have hget : L.getD (X.length + 1 + t) 0 = R[t]'(by omega) := by
      rw [hL, List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
        show X.length + 1 + t - X.length = t + 1 by omega, List.cons_append, List.getD_cons_succ,
        List.getD_append _ _ _ _ (by omega), List.getD_eq_getElem]
    rw [hget, hR _ (List.getElem_mem _), if_neg (by simp)]
    exact rsIdx_run hL ha hR t (by omega)

/-! ### The layout -/

variable {n : ℕ}

/-- The block of a path in the layout: the separator `n`, then the vertices of the path. -/
def layBlock (n : ℕ) (P : List (Fin n)) : List ℕ := n :: P.map Fin.val

/-- A position of the layout that holds a vertex lies inside the block of a path. -/
theorem exists_block_of_getD :
    ∀ {Ps : List (List (Fin n))} {j : ℕ} {y : Fin n},
      j < (Ps.flatMap (layBlock n)).length → (Ps.flatMap (layBlock n)).getD j 0 = y.val →
      ∃ Pre Q Post Q1 Q2, Ps = Pre ++ Q :: Post ∧ Q = Q1 ++ y :: Q2 ∧
        j = (Pre.flatMap (layBlock n)).length + 1 + Q1.length
  | [], j, y, hj, _ => by simp at hj
  | P :: rest, j, y, hj, hget => by
    rw [List.flatMap_cons] at hj hget
    by_cases hjP : j < (layBlock n P).length
    · rw [List.getD_append _ _ _ _ hjP] at hget
      cases j with
      | zero =>
        simp only [layBlock, List.getD_cons_zero] at hget
        exact absurd hget (by have := y.2; omega)
      | succ i =>
        simp only [layBlock, List.getD_cons_succ, List.length_cons, List.length_map] at hget hjP
        have hi : i < P.length := by omega
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map] at hget
        have hPi : P[i] = y := Fin.ext hget
        refine ⟨[], P, rest, P.take i, P.drop (i + 1), rfl, ?_, ?_⟩
        · rw [← hPi]; simp
        · simp [List.length_take, Nat.min_eq_left hi.le]; omega
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hget
      obtain ⟨Pre, Q, Post, Q1, Q2, h1, h2, h3⟩ :=
        exists_block_of_getD (Ps := rest) (j := j - (layBlock n P).length) (by
          rw [List.length_append] at hj; omega) hget
      refine ⟨P :: Pre, Q, Post, Q1, Q2, by rw [h1]; rfl, h2, ?_⟩
      rw [List.flatMap_cons, List.length_append]
      omega

theorem mem_flatMap_layBlock {Ps : List (List (Fin n))} {y : Fin n} :
    y.val ∈ Ps.flatMap (layBlock n) ↔ ∃ P ∈ Ps, y ∈ P := by
  simp only [List.mem_flatMap, layBlock, List.mem_cons, List.mem_map]
  constructor
  · rintro ⟨P, hP, h | ⟨z, hz, hzy⟩⟩
    · exact absurd h (by have := y.2; omega)
    · exact ⟨P, hP, (Fin.ext hzy) ▸ hz⟩
  · rintro ⟨P, hP, hy⟩
    exact ⟨P, hP, Or.inr ⟨y, hy, rfl⟩⟩

theorem le_of_mem_flatMap_layBlock {Ps : List (List (Fin n))} {v : ℕ}
    (hv : v ∈ Ps.flatMap (layBlock n)) : v ≤ n := by
  simp only [List.mem_flatMap, layBlock, List.mem_cons, List.mem_map] at hv
  obtain ⟨P, -, h | ⟨z, -, rfl⟩⟩ := hv
  · omega
  · exact z.2.le

variable {l m p h k r : ℕ} (x : Alg92Input l m p h k r) (segs : List (List (Fin x.n)))

/-- The layout of `H ∪ F`: every path of `fPaths`, each after the separator `n`. -/
def layout : List ℕ := (fPaths x segs).flatMap (layBlock x.n)

open Classical in
/-- The node test on numbers: a number below `n` is a node when its vertex is a node, and the
separator `n` (or any larger number) counts as a node. -/
noncomputable def ndB (v : ℕ) : Bool :=
  if hv : v < x.n then decide ((⟨v, hv⟩ : Fin x.n) ∈ fNodes x segs) else true

variable {x segs}

theorem ndB_val (y : Fin x.n) : ndB x segs y.val = decide (y ∈ fNodes x segs) := by
  simp [ndB, y.2]

theorem ndB_of_le {v : ℕ} (hv : x.n ≤ v) : ndB x segs v = true := by
  simp [ndB, show ¬ v < x.n by omega]

theorem mem_layout_iff {y : Fin x.n} : y.val ∈ layout x segs ↔ OnPath (fPaths x segs) y :=
  mem_flatMap_layBlock

/-- A vertex on no path stands for itself. -/
theorem cRep_of_not_onPath {S : Finset (Fin n)} {Ps : List (List (Fin n))} {y : Fin n}
    (hy : ¬ OnPath Ps y) : cRep S Ps y = y := by
  have hnone : pathOf Ps y = none := by
    unfold pathOf
    rw [List.find?_eq_none]
    intro P hP
    simpa using fun h => hy ⟨P, hP, h⟩
  unfold cRep cBlob
  split_ifs
  · simp
  · simp [hnone]

section Sweep

variable {paths : Fin k → List (Fin x.n)} (hF : IsFSystem x segs paths)
include hF

/-- **What the pass finds.** Let `rs` hold, for every non-node `v` of the layout, the start of the
run of one of its positions, and let `en` hold, at the start of the run of every node position
`j`, the position `j - 1`. Then for every non-node `y` on a path, the run of `y` lies at the
positions `rs y` to `en (rs y)` of the layout, it ends with `cRep y`, it is the blob of `y`, and
the position before it holds `cPrev y`. -/
theorem sweep_spec {rsA enA : ℕ → ℕ}
    (hS1 : ∀ v ∈ layout x segs, ndB x segs v = false → ∃ j < (layout x segs).length,
      (layout x segs).getD j 0 = v ∧ rsA v = rsIdx (ndB x segs) (layout x segs) j)
    (hS2 : ∀ j < (layout x segs).length, ndB x segs ((layout x segs).getD j 0) = true →
      enA (rsIdx (ndB x segs) (layout x segs) j) = j - 1)
    {y : Fin x.n} (hyS : y ∉ fNodes x segs) (hy : OnPath (fPaths x segs) y) :
    1 ≤ rsA y.val ∧ rsA y.val ≤ enA (rsA y.val) ∧ enA (rsA y.val) < (layout x segs).length ∧
      (layout x segs).getD (enA (rsA y.val)) 0 = (cRep (fNodes x segs) (fPaths x segs) y).val ∧
      ((layout x segs).drop (rsA y.val)).take (enA (rsA y.val) + 1 - rsA y.val) =
        (cBlob (fNodes x segs) (fPaths x segs) y).map Fin.val ∧
      (layout x segs).getD (rsA y.val - 1) 0 = (cPrev (fNodes x segs) (fPaths x segs) y).val := by
  have hP := hF.isPathSystem
  have hnd : ndB x segs y.val = false := by simp [ndB_val, hyS]
  obtain ⟨j, hj, hget, hrs⟩ := hS1 y.val (mem_layout_iff.mpr hy) hnd
  obtain ⟨Pre, Q, Post, Q1, Q2, hPs, hQ, hjpos⟩ := exists_block_of_getD hj hget
  have hQmem : Q ∈ fPaths x segs := by rw [hPs]; simp
  obtain ⟨A, a, R, c, B, hdec, ha, hc, hR, hyR, hrun⟩ :=
    hP.exists_run hQmem (by rw [hQ]; simp) hyS
  obtain ⟨R1, R2, rfl⟩ := List.append_of_mem hyR
  have hQnd := hP.nodup Q hQmem
  have hQ1 : Q1 = A ++ a :: R1 :=
    (nodup_split_unique hQnd hQ (A' := A ++ a :: R1) (B' := R2 ++ c :: B)
      (by rw [hdec]; simp)).1
  -- the layout around the run
  set R := R1 ++ y :: R2 with hRdef
  set X := Pre.flatMap (layBlock x.n) ++ x.n :: A.map Fin.val with hX
  have hL : layout x segs = X ++ a.val :: R.map Fin.val ++ c.val :: (B.map Fin.val ++
      Post.flatMap (layBlock x.n)) := by
    rw [layout, hPs, List.flatMap_append, List.flatMap_cons, hdec]
    simp [X, layBlock]
  have haN : ndB x segs a.val = true := by simp [ndB_val, ha]
  have hcN : ndB x segs c.val = true := by simp [ndB_val, hc]
  have hRN : ∀ v ∈ R.map Fin.val, ndB x segs v = false := by
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨z, hz, rfl⟩ := hv
    simp [ndB_val, hR z hz]
  have hL' : layout x segs = X ++ a.val :: R.map Fin.val ++ (c.val :: (B.map Fin.val ++
      Post.flatMap (layBlock x.n))) := by rw [hL]
  have hrun_idx := rsIdx_run hL' haN hRN
  have hXlen : X.length = (Pre.flatMap (layBlock x.n)).length + 1 + A.length := by
    simp [X]; omega
  have hjX : j = X.length + 1 + R1.length := by
    rw [hjpos, hQ1, hXlen]; simp; omega
  have hRlen : R.length = R1.length + 1 + R2.length := by simp [R]; omega
  have hq : rsA y.val = X.length + 1 := by
    rw [hrs, hjX, hrun_idx R1.length (by simp [hRlen]; omega)]
  -- the end of the run
  have hcpos : (layout x segs).getD (X.length + 1 + R.length) 0 = c.val := by
    rw [hL, List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
      show X.length + 1 + R.length - X.length = R.length + 1 by omega, List.cons_append,
      List.getD_cons_succ,
      List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hLlen : X.length + 1 + R.length < (layout x segs).length := by
    rw [hL]; simp; omega
  have hen : enA (rsA y.val) = X.length + R.length := by
    have := hS2 _ hLlen (by rw [hcpos]; exact hcN)
    rw [hrun_idx R.length (by simp), ← hq] at this
    rw [this]; omega
  have hRne : R ≠ [] := by simp [R]
  have hrep : cRep (fNodes x segs) (fPaths x segs) y = R.getLast hRne := by
    simp only [cRep, (hrun y (by simp [R])).1]
  refine ⟨by omega, by rw [hen, hq]; omega, by rw [hen]; omega, ?_, ?_, ?_⟩
  · rw [hen, hrep, hL, List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
      show X.length + R.length - X.length = (R.length - 1) + 1 by omega, List.cons_append,
      List.getD_cons_succ,
      List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
      List.getElem_map, List.getLast_eq_getElem]
  · rw [hen, hq, (hrun y (by simp [R])).1, hL, List.append_assoc,
      show X.length + R.length + 1 - (X.length + 1) = R.length by omega,
      List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      show X.length + 1 - X.length = 1 by omega, List.drop_one, List.cons_append, List.tail_cons,
      List.take_append,
      List.take_of_length_le (by simp), List.length_map, Nat.sub_self, List.take_zero,
      List.append_nil]
  · rw [hq, Nat.add_sub_cancel, (hrun y (by simp [R])).2.1, hL, List.append_assoc,
      List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.cons_append, List.getD_cons_zero]

end Sweep

end Alg92

end GraphMinor.Compute
