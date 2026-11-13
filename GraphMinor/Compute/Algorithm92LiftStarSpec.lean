module

public import GraphMinor.Compute.Algorithm92LiftStarRun

/-!
# Graph Minors XIII, (9.2): the star program writes the lifted star (`Algorithm92LiftStarSpec.lean`)

The program `starProg` of `Algorithm92LiftStarRun.lean` works on plain lists. Here the lists are
the arrays that the earlier programs wrote for the layout of `H ∪ F` (page 101 of Graph Minors
XIII). For these arrays, the lifted rays are the rays `liftRay` of the blob map `cBlobMap`
(`liftN_eq_liftRay`, `liftRays_eq_encHPaths`), and every vertex of the compressed graph passes the
tests that the program needs (`goodV_of_fVerts`).
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

/-! ### The lift of a ray as one list -/

theorem BlobMap.liftTail_eq_flatMap {N n : ℕ} (B : BlobMap N n) :
    ∀ (prev : Fin N) (L : List (Fin N)), B.liftTail prev L =
      (List.range L.length).flatMap (fun t => B.piece ((prev :: L).getD t prev) (L.getD t prev))
  | prev, [] => by simp [BlobMap.liftTail]
  | prev, v :: rest => by
    rw [BlobMap.liftTail, BlobMap.liftTail_eq_flatMap B v rest, List.length_cons,
      List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    have hc : ∀ t ∈ List.range rest.length,
        B.piece ((v :: rest).getD t v) (rest.getD t v) =
          B.piece ((prev :: v :: rest).getD (t + 1) prev) ((v :: rest).getD (t + 1) prev) := by
      intro t ht
      rw [List.mem_range] at ht
      have h1 : t < (v :: rest).length := by simp; omega
      simp only [List.getD_cons_succ, List.getD_eq_getElem _ _ ht, List.getD_eq_getElem _ _ h1]
    rw [List.flatMap_congr hc]
    rfl

variable {l m p h k r : ℕ} {x : Alg92Input l m p h k r} {segs : List (List (Fin x.n))}

variable (x segs) in
/-- The blob map of the compressed copy of `H ∪ F`. -/
noncomputable abbrev fBlobMap : BlobMap (fVerts x segs).card x.n :=
  cBlobMap (fNodes x segs) (fPaths x segs) (fE x segs) (fι x segs)

theorem rankF_eq_fι (y : Fin x.n) {paths : Fin k → List (Fin x.n)} (hF : IsFSystem x segs paths) :
    rankF x segs y.val = (fι x segs y).val := by
  by_cases hy : y ∈ fVerts x segs
  · exact rankF_eq hF hy
  · have hV : isV (ndB x segs) (onpB x segs) (repF x segs) y.val = false := by
      rw [isV_eq hF y.2]; simpa using hy
    simp only [rankF, hV, fι, hy, dite_false]
    rfl

theorem card_fVerts_le_n : (fVerts x segs).card ≤ x.n := by
  simpa using Finset.card_le_univ (fVerts x segs)

section FSystem

variable {paths : Fin k → List (Fin x.n)} (hF : IsFSystem x segs paths)
include hF

/-- The facts of the sweep at a vertex on a path that is not a node. -/
theorem sweepF {y : Fin x.n} (hyS : y ∉ fNodes x segs) (hy : OnPath (fPaths x segs) y) :
    1 ≤ rsF (ndB x segs) (layout x segs) (layout x segs).length y.val ∧
    rsF (ndB x segs) (layout x segs) (layout x segs).length y.val ≤
      enF (ndB x segs) (layout x segs) (layout x segs).length
        (rsF (ndB x segs) (layout x segs) (layout x segs).length y.val) ∧
    enF (ndB x segs) (layout x segs) (layout x segs).length
        (rsF (ndB x segs) (layout x segs) (layout x segs).length y.val) < (layout x segs).length ∧
    ((layout x segs).drop (rsF (ndB x segs) (layout x segs) (layout x segs).length y.val)).take
        (enF (ndB x segs) (layout x segs) (layout x segs).length
          (rsF (ndB x segs) (layout x segs) (layout x segs).length y.val) + 1 -
            rsF (ndB x segs) (layout x segs) (layout x segs).length y.val) =
      (cBlob (fNodes x segs) (fPaths x segs) y).map Fin.val ∧
    (layout x segs).getD (rsF (ndB x segs) (layout x segs) (layout x segs).length y.val - 1) 0 =
      (cPrev (fNodes x segs) (fPaths x segs) y).val := by
  obtain ⟨h1, h2, h3, -, h5, h6⟩ := sweep_spec hF
    (rsA := rsF (ndB x segs) (layout x segs) (layout x segs).length)
    (enA := enF (ndB x segs) (layout x segs) (layout x segs).length)
    (fun v hv hvn => by
      obtain ⟨j, hj, h1, h2⟩ := rsF_spec (layout x segs).length v hvn (by
        obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hv
        exact ⟨j, hj, by rw [List.getD_eq_getElem _ _ hj, hjv]⟩)
      exact ⟨j, hj, h1, h2⟩)
    (fun j hj hnd => enF_spec _ j hj hnd) hyS hy
  exact ⟨h1, h2, h3, h5, h6⟩

omit hF in
theorem onPath_of_fVerts {y : Fin x.n} (hy : y ∈ fVerts x segs) (hyS : y ∉ fNodes x segs) :
    OnPath (fPaths x segs) y := by
  rcases mem_cVerts_iff.mp hy with h | h
  · exact absurd h hyS
  · exact h.1

/-- Every vertex of the compressed graph passes the tests of the star program. -/
theorem goodV_of_fVerts (v : Fin (fVerts x segs).card) :
    GoodV (vlist (ndB x segs) (onpB x segs) (repF x segs) x.n) (layout x segs) (ndB x segs)
      (rsF (ndB x segs) (layout x segs) (layout x segs).length)
      (enF (ndB x segs) (layout x segs) (layout x segs).length) x.n v.val := by
  have hE := getD_vlist_eq_fE hF v
  refine ⟨lt_of_lt_of_le v.2 card_fVerts_le_n, by rw [hE]; exact (fE x segs v).2, fun hnd => ?_⟩
  rw [hE] at hnd ⊢
  have hyS : fE x segs v ∉ fNodes x segs := by simpa [ndB_val] using hnd
  obtain ⟨h1, h2, h3, -, h5⟩ := sweepF hF hyS (onPath_of_fVerts (Finset.orderEmbOfFin_mem _ _ _)
    hyS)
  exact ⟨h1, h2, h3, by rw [h5]; exact (cPrev _ _ _).2⟩

/-- The piece that the program writes is the piece of the blob map. -/
theorem pieceN_eq (prev v : Fin (fVerts x segs).card) :
    pieceN (vlist (ndB x segs) (onpB x segs) (repF x segs) x.n) (layout x segs) (ndB x segs)
      (rsF (ndB x segs) (layout x segs) (layout x segs).length)
      (enF (ndB x segs) (layout x segs) (layout x segs).length) (rankF x segs) prev.val v.val =
      ((fBlobMap x segs).piece prev v).map Fin.val := by
  have hE := getD_vlist_eq_fE hF v
  have hnode : (fBlobMap x segs).isNode v = decide (fE x segs v ∈ fNodes x segs) := rfl
  have hnv : (fBlobMap x segs).node v = fE x segs v := rfl
  have hbl : (fBlobMap x segs).blob v = cBlob (fNodes x segs) (fPaths x segs) (fE x segs v) := rfl
  have hen : ((fBlobMap x segs).ends v).1 =
      fι x segs (cPrev (fNodes x segs) (fPaths x segs) (fE x segs v)) := rfl
  unfold pieceN BlobMap.piece
  simp only [hE, ndB_val, hnode, hnv, hbl, hen]
  by_cases hS : fE x segs v ∈ fNodes x segs
  · simp [hS]
  · obtain ⟨-, -, -, h4, h5⟩ := sweepF hF hS (onPath_of_fVerts
      (Finset.orderEmbOfFin_mem _ _ _) hS)
    simp only [hS, decide_false, Bool.false_eq_true, if_false]
    rw [h5, rankF_eq_fι _ hF, h4]
    by_cases hp : prev = fι x segs (cPrev (fNodes x segs) (fPaths x segs) (fE x segs v))
    · rw [if_pos (by rw [hp]), if_pos hp]
    · rw [if_neg (fun h => hp (Fin.ext h.symm)), if_neg hp, List.map_reverse]

theorem stepPiece_eq (κ : List (Fin (fVerts x segs).card)) {t : ℕ} (ht : t < κ.length) :
    stepPiece (vlist (ndB x segs) (onpB x segs) (repF x segs) x.n) (layout x segs) (ndB x segs)
      (rsF (ndB x segs) (layout x segs) (layout x segs).length)
      (enF (ndB x segs) (layout x segs) (layout x segs).length) (rankF x segs) (κ.map Fin.val) t =
      if t = 0 then [((fBlobMap x segs).node κ[0]).val]
      else ((fBlobMap x segs).piece κ[t - 1] κ[t]).map Fin.val := by
  have hg : ∀ j (hj : j < κ.length), (κ.map Fin.val).getD j 0 = κ[j].val := fun j hj => by
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map]
  unfold stepPiece
  split_ifs with h0
  · subst h0
    rw [hg 0 ht, getD_vlist_eq_fE hF]
    rfl
  · rw [hg t ht, hg (t - 1) (by omega), pieceN_eq hF]

/-- **The lifted ray of the program is `liftRay`.** -/
theorem liftN_eq_liftRay (κ : List (Fin (fVerts x segs).card)) :
    liftN (vlist (ndB x segs) (onpB x segs) (repF x segs) x.n) (layout x segs) (ndB x segs)
      (rsF (ndB x segs) (layout x segs) (layout x segs).length)
      (enF (ndB x segs) (layout x segs) (layout x segs).length) (rankF x segs) (κ.map Fin.val)
      κ.length = ((fBlobMap x segs).liftRay κ).map Fin.val := by
  cases κ with
  | nil => simp [liftN, BlobMap.liftRay]
  | cons c rest =>
    rw [liftN, BlobMap.liftRay, BlobMap.liftTail_eq_flatMap, List.length_cons,
      List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      stepPiece_eq hF _ (by simp), if_pos rfl]
    conv_rhs => rw [List.map_cons, List.map_flatMap]
    have hc : ∀ t ∈ List.range rest.length,
        stepPiece (vlist (ndB x segs) (onpB x segs) (repF x segs) x.n) (layout x segs) (ndB x segs)
          (rsF (ndB x segs) (layout x segs) (layout x segs).length)
          (enF (ndB x segs) (layout x segs) (layout x segs).length) (rankF x segs)
          ((c :: rest).map Fin.val) (t + 1) =
        ((fBlobMap x segs).piece ((c :: rest).getD t c) (rest.getD t c)).map Fin.val := by
      intro t ht
      rw [List.mem_range] at ht
      rw [stepPiece_eq hF _ (by simp; omega), if_neg (by omega),
        List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ ht]
      simp only [Nat.add_sub_cancel, List.getElem_cons_succ]
    rw [List.flatMap_congr hc]
    rfl

/-- **The lifted rays of the program are the encoding of the rays `liftRay`.** -/
theorem liftRays_eq_encHPaths {l' : ℕ} (rays : Fin l' → List (Fin (fVerts x segs).card)) :
    liftRays (vlist (ndB x segs) (onpB x segs) (repF x segs) x.n) (layout x segs) (ndB x segs)
      (rsF (ndB x segs) (layout x segs) (layout x segs).length)
      (enF (ndB x segs) (layout x segs) (layout x segs).length) (rankF x segs)
      ((List.finRange l').map (fun i => (rays i).map Fin.val)) =
      encHPaths (fun i => (fBlobMap x segs).liftRay (rays i)) := by
  unfold liftRays encHPaths
  rw [List.flatMap_def, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, lenPre]
  rw [List.length_map, liftN_eq_liftRay hF, List.length_map]

end FSystem

/-- The encoding of rays is the list that the star program reads. -/
theorem encHPaths_eq {N l' : ℕ} (rays : Fin l' → List (Fin N)) :
    encHPaths rays = (((List.finRange l').map (fun i => (rays i).map Fin.val)).map lenPre).flatten := by
  unfold encHPaths
  rw [List.flatMap_def, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp [lenPre]

end Alg92

end GraphMinor.Compute
