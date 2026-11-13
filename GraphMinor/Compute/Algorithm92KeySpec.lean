module

public import GraphMinor.Compute.Algorithm92KeyProg

/-!
# Graph Minors XIII, (9.2): the key array is `compKey` (`Algorithm92KeySpec.lean`)

The program of `Algorithm92KeyProg.lean`, run on the arrays that the numbering wrote for the
layout of `H ∪ F`, writes exactly the key `compKey x segs` of the compressed copy of `H ∪ F`
(`keyArr_eq_compKey`, page 101 of Graph Minors XIII).
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

open WallOfHeight

variable {l m p h k r : ℕ} {x : Alg92Input l m p h k r} {segs : List (List (Fin x.n))}

variable (x segs) in
/-- The numbers that the numbering writes into `aRank`. -/
noncomputable def rankF (z : ℕ) : ℕ :=
  if isV (ndB x segs) (onpB x segs) (repF x segs) z then
    (vlist (ndB x segs) (onpB x segs) (repF x segs) z).length else 0

variable (x segs) in
/-- The vertices that the numbering writes into `aRep`. -/
noncomputable def repvF (z : ℕ) : ℕ := repv (ndB x segs) (onpB x segs) (repF x segs) z

section FSystem

variable {paths : Fin k → List (Fin x.n)} (hF : IsFSystem x segs paths)
include hF

theorem rankF_eq {y : Fin x.n} (hy : y ∈ fVerts x segs) : rankF x segs y.val = (fι x segs y).val := by
  rw [rankF, isV_eq hF y.2, if_pos (by simpa using hy), length_vlist_eq_fι hF hy]

theorem keyOne_path {P : List (Fin x.n)} (hP : ∀ y ∈ P, OnPath (fPaths x segs) y) :
    (P.map Fin.val).flatMap (keyOne x.n (fVerts x segs).card (repvF x segs) (rankF x segs)) =
      (P.filter (isRepB (fNodes x segs) (fPaths x segs))).map (fun y => (fι x segs y).val) := by
  induction P with
  | nil => rfl
  | cons y P ih =>
    rw [List.map_cons, List.flatMap_cons, ih (fun z hz => hP z (List.mem_cons_of_mem _ hz)),
      List.filter_cons]
    have hrep : repvF x segs y.val = (cRep (fNodes x segs) (fPaths x segs) y).val := repv_eq hF y.2
    unfold keyOne
    rw [if_neg (Nat.ne_of_lt y.2), hrep]
    by_cases hc : cRep (fNodes x segs) (fPaths x segs) y = y
    · have hyV : y ∈ fVerts x segs :=
        mem_cVerts_iff.mpr (Or.inr ⟨hP y (List.mem_cons_self), hc⟩)
      rw [if_pos (by rw [hc]), rankF_eq hF hyV]
      simp [isRepB, hc]
    · rw [if_neg (fun h => hc (Fin.ext h))]
      simp [isRepB, hc]

/-- **The key array is `compKey`.** -/
theorem keyArr_eq_compKey :
    (fVerts x segs).card :: bvRanks (elemWallNumVerts h) (rankF x segs) x.W.encList ++
      (layout x segs).flatMap (keyOne x.n (fVerts x segs).card (repvF x segs) (rankF x segs)) =
    compKey x segs := by
  have e1 : bvRanks (elemWallNumVerts h) (rankF x segs) x.W.encList =
      (List.finRange (elemWallNumVerts h)).map (fun u => (fι x segs (x.W.branchVert u)).val) := by
    refine List.ext_getElem (by simp [bvRanks]) fun u h1 h2 => ?_
    have hu : u < elemWallNumVerts h := by simpa [bvRanks] using h1
    simp only [bvRanks, List.getElem_map, List.getElem_range, List.getElem_finRange]
    rw [getD_encList_bv u hu, rankF_eq hF (mem_cVerts_iff.mpr (Or.inl
      (branchVert_mem_fNodes segs _)))]
    rfl
  have e2 : (layout x segs).flatMap (keyOne x.n (fVerts x segs).card (repvF x segs) (rankF x segs)) =
      (fPaths x segs).flatMap (fun P => (fVerts x segs).card ::
        ((P.filter (isRepB (fNodes x segs) (fPaths x segs))).map (fun y => (fι x segs y).val))) := by
    rw [layout, List.flatMap_assoc]
    refine List.flatMap_congr fun P hP => ?_
    rw [layBlock, List.flatMap_cons, keyOne, if_pos rfl, List.singleton_append,
      keyOne_path hF (fun y hy => ⟨P, hP, hy⟩)]
  rw [e1, e2]
  rfl

end FSystem

end Alg92

end GraphMinor.Compute
