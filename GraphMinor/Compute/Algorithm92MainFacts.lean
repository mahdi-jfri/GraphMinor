module

public import GraphMinor.Compute.Algorithm92LiftStarSpec
public import GraphMinor.Compute.Algorithm97Aux

/-!
# Graph Minors XIII, (9.2): sizes and ranges for the whole program (`Algorithm92MainFacts.lean`)

The program of (9.2) after `F` (page 101 of Graph Minors XIII) runs the programs of the files
`Algorithm92Build*.lean` to `Algorithm92LiftStar*.lean` one after the other. This file proves the
facts that join them:

* the lengths of the layout and of the encoding of `F` are linear in `n`
  (`length_layout_le`, `length_encSegs92_le`);
* the key `compKey x segs` has length at most `keyLen92 h k` and entries at most `bound92 h k`
  (`length_compKey_le`, `le_of_mem_compKey`), so it is one of the finitely many lists
  `lists (bound92 h k) (keyLen92 h k)`;
* the range facts that `modelProg_exec` needs (`modelRange`).
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

variable {l m p h k r : ℕ} {x : Alg92Input l m p h k r} {segs : List (List (Fin x.n))}

/-- The bound on the length of the key. -/
def keyLen92 (h k : ℕ) : ℕ :=
  1 + elemWallNumVerts h + ((elemWallEdges h).length + k) * (1 + bound92 h k)

theorem le_of_mem_layout {v : ℕ} (hv : v ∈ layout x segs) : v ≤ x.n := by
  simp only [layout, List.mem_flatMap, layBlock, List.mem_cons, List.mem_map] at hv
  obtain ⟨P, -, rfl | ⟨y, -, rfl⟩⟩ := hv
  · exact le_rfl
  · exact y.2.le

theorem length_encSegs92_le (hnd : ∀ P ∈ segs, P.length ≤ x.n) :
    (encSegs92 segs).length ≤ 1 + segs.length * (x.n + 1) := by
  unfold encSegs92
  rw [List.length_cons, List.length_flatMap]
  have : (segs.map (fun P => (P.length :: P.map Fin.val).length)).sum ≤
      (segs.map (fun _ => x.n + 1)).sum :=
    List.sum_le_sum (fun P hP => by simpa using hnd P hP)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at this
  omega

theorem length_encList_le : x.W.encList.length ≤ 3 + 3 * elemWallNumVerts h + x.n :=
  length_encList_le_maxWallEncLen_self x.hW_valid.2.2

theorem length_layout_le (hnd : ∀ P ∈ segs, P.length ≤ x.n) :
    (layout x segs).length ≤
      3 + 3 * elemWallNumVerts h + x.n + 2 * (elemWallEdges h).length + 1 +
        segs.length * (x.n + 1) := by
  have h1 := length_layout (x := x) (segs := segs)
  have h2 := length_encSegs92_le hnd
  have h3 := length_encList_le (x := x)
  omega

section FSystem

variable {paths : Fin k → List (Fin x.n)} (hF : IsFSystem x segs paths)
include hF

theorem length_filter_isRepB_le {P : List (Fin x.n)} (hP : P ∈ fPaths x segs) :
    (P.filter (isRepB (fNodes x segs) (fPaths x segs))).length ≤ (fVerts x segs).card := by
  classical
  have hnd : (P.filter (isRepB (fNodes x segs) (fPaths x segs))).Nodup :=
    (hF.isPathSystem.nodup P hP).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  refine Finset.card_le_card fun y hy => ?_
  rw [List.mem_toFinset, List.mem_filter] at hy
  refine mem_cVerts_iff.mpr (Or.inr ⟨⟨P, hP, hy.1⟩, ?_⟩)
  simpa [isRepB] using hy.2

theorem le_of_mem_compKey (hs : segs.length ≤ k) {v : ℕ} (hv : v ∈ compKey x segs) :
    v ≤ bound92 h k := by
  have hN := card_fVerts_le hF hs
  simp only [compKey, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap] at hv
  rcases hv with rfl | ⟨u, -, rfl⟩ | ⟨P, -, rfl | ⟨y, -, rfl⟩⟩
  · exact hN
  · exact (fι_lt segs _).le.trans hN
  · exact hN
  · exact (fι_lt segs _).le.trans hN

theorem length_compKey_le (hs : segs.length ≤ k) :
    (compKey x segs).length ≤ keyLen92 h k := by
  have hN := card_fVerts_le hF hs
  unfold compKey keyLen92
  rw [List.length_cons, List.length_append, List.length_map, List.length_finRange,
    List.length_flatMap]
  have hsum : ((fPaths x segs).map (fun P => ((fVerts x segs).card ::
      ((P.filter (isRepB (fNodes x segs) (fPaths x segs))).map
        (fun y => (fι x segs y).val))).length)).sum ≤
      ((fPaths x segs).map (fun _ => 1 + bound92 h k)).sum :=
    List.sum_le_sum fun P hP => by
      have := length_filter_isRepB_le hF hP
      simp only [List.length_cons, List.length_map]
      omega
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hsum
  have hlen : (fPaths x segs).length ≤ (elemWallEdges h).length + k := by
    simp [fPaths]; omega
  have := Nat.mul_le_mul_right (1 + bound92 h k) hlen
  omega

/-- The range facts that `modelProg_exec` needs, on the arrays of the compressed copy. -/
theorem modelRange (K : Fin p → Finset (Fin (fVerts x segs).card)) :
    ∀ i < p, ∀ y < x.n, (ndB x segs y || onpB x segs y) = true →
      repvF x segs y < x.n ∧
        1 + i * (fVerts x segs).card + rankF x segs (repvF x segs y) <
          (1 :: encBitSetsUpTo K p).length := by
  intro i hi y hy _
  have hrep : repvF x segs y = (cRep (fNodes x segs) (fPaths x segs) ⟨y, hy⟩).val :=
    repv_eq hF hy
  refine ⟨by rw [hrep]; exact (cRep _ _ _).2, ?_⟩
  rw [hrep, rankF_eq_fι _ hF, List.length_cons, length_encBitSetsUpTo _ _ le_rfl]
  have h1 := fι_lt segs (cRep (fNodes x segs) (fPaths x segs) ⟨y, hy⟩)
  have h2 : (i + 1) * (fVerts x segs).card ≤ p * (fVerts x segs).card :=
    Nat.mul_le_mul_right _ hi
  rw [Nat.add_mul, Nat.one_mul] at h2
  omega

end FSystem

end Alg92

end GraphMinor.Compute
