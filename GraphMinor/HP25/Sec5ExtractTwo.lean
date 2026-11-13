module

public import GraphMinor.HP25.Sec5ExtractClose
public import GraphMinor.HP25.Sec5UndoT2

/-!
# Extraction of one level through the collapse edges and the loop edges

The completion of a path adds collapse edges and then loop edges, and keeps only some
of them in the graph `H` of the subinstances. This file extracts a crossing of `C` in `G` from a
crossing of a subinstance along the following route:

1. lift the subinstance crossing to a crossing of `C` in `H` (`liftSubCrossingBySearches`);
2. view it in `H_full ≥ H`, the graph with all collapse and loop edges (`CrossingWalks.mapLe`, no
   search);
3. undo the loop edges in reverse order, from `H_full` down to `G₂ = G + all collapse edges`
   (`undoChainBySearches` over an `AddedEdgeChain`);
4. undo the collapse edges in reverse order, from `G₂` down to `G`, by Claim 5.5 with no search
   (`undoT2Chain`).

`extractCrossingTwoPart_valid` and `extractCrossingTwoPart_searches_le` hold with no hypothesis.
`extractCrossingTwoPart_isSome` has the hypotheses of `liftSubCrossingBySearches_isSome` and
`t3.Exhaustive verts` for the loop edges, which is the open exhaustiveness of rules 1 to 4.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {C A B : List V} {a b : V} {k : ℕ}

/-- View a pair of walks of `H` in a larger graph `H'`. -/
@[expose] def CrossingWalks.mapLe {H H' : SimpleGraph V} {T : List V} (hle : H ≤ H')
    (cr : CrossingWalks H T) : CrossingWalks H' T :=
  ⟨cr.u₁, cr.v₁, cr.u₂, cr.v₂, cr.Q.mapLe hle, cr.R.mapLe hle⟩

theorem CrossingWalks.mapLe_valid {H H' : SimpleGraph V} {T : List V} (hle : H ≤ H')
    {cr : CrossingWalks H T} (hcr : cr.Valid) : (cr.mapLe hle).Valid := by
  obtain ⟨hidx, hQ, hR, hdisj⟩ := hcr
  refine ⟨hidx, ⟨hQ.1.mapLe hle, hQ.2.1, hQ.2.2.1, ?_⟩, ⟨hR.1.mapLe hle, hR.2.1, hR.2.2.1, ?_⟩, ?_⟩
  · simpa [CrossingWalks.mapLe, SimpleGraph.Walk.support_mapLe_eq_support] using hQ.2.2.2
  · simpa [CrossingWalks.mapLe, SimpleGraph.Walk.support_mapLe_eq_support] using hR.2.2.2
  · simpa [CrossingWalks.mapLe, SimpleGraph.Walk.support_mapLe_eq_support] using hdisj

/-- **Extraction of one level along the two-part route.** `t2` is the run of collapse steps from
`G` to `G₂`, `t3` the run of loop steps from `G₂` to `H_full`, and `H ≤ H_full` the graph of the
subinstances. Returns a crossing of `C` in `G` and the number of searches. -/
@[expose] def extractCrossingTwoPart [DecidableEq V] [WalkSearch V] {H G₂ H_full : SimpleGraph V}
    [DecidableRel H.Adj] {m : List V} (verts C P_supp : List V) (hle : H ≤ H_full)
    (t2 : T2Chain V C A B a b k G G₂) (t3 : AddedEdgeChain V C A B a b k G₂ H_full)
    (subCr : CrossingWalks (restrict H (sideSetOf G (a :: m ++ [b]) A)) (a :: A ++ b :: m.reverse) ⊕
      CrossingWalks (restrict H (sideComplOf G (a :: m ++ [b]) A)) (b :: B ++ a :: m)) :
    Option (CrossingWalks G C) × ℕ :=
  let liftRes := liftSubCrossingBySearches (G := G) (A := A) (B := B) (a := a) (b := b)
    verts C P_supp subCr
  match liftRes.1 with
  | some crH =>
    let undoRes := undoChainBySearches verts t3 (crH.mapLe hle)
    match undoRes.1 with
    | some cr₂ => (undoT2Chain t2 cr₂, liftRes.2 + undoRes.2)
    | none => (none, liftRes.2 + undoRes.2)
  | none => (none, liftRes.2)

/-- Every crossing returned by `extractCrossingTwoPart` is a valid crossing of `C` in `G`. -/
theorem extractCrossingTwoPart_valid [DecidableEq V] [WalkSearch V] [LawfulWalkSearch V]
    {H G₂ H_full : SimpleGraph V} [DecidableRel H.Adj] {m : List V} {verts P_supp : List V}
    (hle : H ≤ H_full) (t2 : T2Chain V C A B a b k G G₂)
    (t3 : AddedEdgeChain V C A B a b k G₂ H_full)
    {subCr : CrossingWalks (restrict H (sideSetOf G (a :: m ++ [b]) A)) (a :: A ++ b :: m.reverse) ⊕
      CrossingWalks (restrict H (sideComplOf G (a :: m ++ [b]) A)) (b :: B ++ a :: m)}
    {crG : CrossingWalks G C}
    (h : (extractCrossingTwoPart verts C P_supp hle t2 t3 subCr).1 = some crG) :
    crG.Valid := by
  simp only [extractCrossingTwoPart] at h
  rcases hlift : (liftSubCrossingBySearches (G := G) (A := A) (B := B) (a := a) (b := b)
    verts C P_supp subCr).1 with _ | crH <;> rw [hlift] at h
  · simp at h
  · dsimp only at h
    rcases hund : (undoChainBySearches verts t3 (crH.mapLe hle)).1 with _ | cr₂ <;>
      rw [hund] at h
    · simp at h
    · dsimp only at h
      have hv₂ := undoChainBySearches_valid verts t3
        (CrossingWalks.mapLe_valid hle (liftSubCrossingBySearches_valid hlift)) hund
      obtain ⟨crG', hG', hvG'⟩ := undoT2Chain_spec t2 hv₂
      rw [hG'] at h
      cases h
      exact hvG'

/-- `extractCrossingTwoPart` makes at most `28 + 44 * t3.length` searches: the collapse edges
need none. -/
theorem extractCrossingTwoPart_searches_le [DecidableEq V] [WalkSearch V]
    {H G₂ H_full : SimpleGraph V} [DecidableRel H.Adj] {m : List V} (verts P_supp : List V)
    (hle : H ≤ H_full) (t2 : T2Chain V C A B a b k G G₂)
    (t3 : AddedEdgeChain V C A B a b k G₂ H_full)
    (subCr : CrossingWalks (restrict H (sideSetOf G (a :: m ++ [b]) A)) (a :: A ++ b :: m.reverse) ⊕
      CrossingWalks (restrict H (sideComplOf G (a :: m ++ [b]) A)) (b :: B ++ a :: m)) :
    (extractCrossingTwoPart verts C P_supp hle t2 t3 subCr).2 ≤ 28 + 44 * t3.length := by
  simp only [extractCrossingTwoPart]
  have h1 := liftSubCrossingBySearches_searches_le (G := G) (A := A) (B := B) (a := a) (b := b)
    verts C P_supp subCr
  rcases (liftSubCrossingBySearches (G := G) (A := A) (B := B) (a := a) (b := b)
    verts C P_supp subCr).1 with _ | crH
  · dsimp only; omega
  · dsimp only
    have h2 := undoChainBySearches_searches_le verts t3 (crH.mapLe hle)
    rcases (undoChainBySearches verts t3 (crH.mapLe hle)).1 with _ | cr₂ <;>
      · dsimp only; omega

/-- **Completeness of `extractCrossingTwoPart`.** Under the hypotheses of
`liftSubCrossingBySearches_isSome` and the exhaustiveness `t3.Exhaustive verts` of the loop
steps (open: `BridgeSearchExhaustive`), it returns `some` crossing. The collapse steps need no
hypothesis (`undoT2Chain_spec`). -/
theorem extractCrossingTwoPart_isSome [DecidableEq V] [WalkSearch V] [LawfulWalkSearch V]
    {H G₂ H_full : SimpleGraph V} [DecidableRel H.Adj]
    {m verts : List V} (hverts : ∀ v : V, v ∈ verts)
    (hC : IsCycleList G C) (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ []) (hB : B ≠ [])
    (hGH : G ≤ H) {P' : H.Walk a b}
    (hH : ∀ u v, H.Adj u v → G.Adj u v ∨ IsListEdge P'.support u v)
    (hP' : IsTPath H C P') (hm : P'.support = a :: m ++ [b])
    (hind : ∀ u ∈ P'.support, ∀ v ∈ P'.support, H.Adj u v → IsListEdge P'.support u v)
    (hsep : Separates G {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B})
    (hsides : OnBothSidesList G C A B P'.support)
    (htight : IsTight H C A B P'.support)
    (hle : H ≤ H_full) (t2 : T2Chain V C A B a b k G G₂)
    (t3 : AddedEdgeChain V C A B a b k G₂ H_full) (hexh : t3.Exhaustive verts)
    (subCr : CrossingWalks (restrict H (sideSetOf G (a :: m ++ [b]) A)) (a :: A ++ b :: m.reverse) ⊕
      CrossingWalks (restrict H (sideComplOf G (a :: m ++ [b]) A)) (b :: B ++ a :: m))
    (hvalid : Sum.elim CrossingWalks.Valid CrossingWalks.Valid subCr) :
    (extractCrossingTwoPart verts C P'.support hle t2 t3 subCr).1.isSome = true := by
  simp only [extractCrossingTwoPart]
  have hlift_some :=
    liftSubCrossingBySearches_isSome hverts hC hrot hA hB hGH hH hP' hm hind hsep hsides htight
      subCr hvalid
  obtain ⟨crH, hcrH⟩ := Option.isSome_iff_exists.mp hlift_some
  rw [hcrH]
  dsimp only
  have hund_some := undoChainBySearches_isSome hverts t3 hexh
    (CrossingWalks.mapLe_valid hle (liftSubCrossingBySearches_valid hcrH))
  obtain ⟨cr₂, hcr₂⟩ := Option.isSome_iff_exists.mp hund_some
  rw [hcr₂]
  dsimp only
  obtain ⟨crG, hG, -⟩ := undoT2Chain_spec t2
    (undoChainBySearches_valid verts t3
      (CrossingWalks.mapLe_valid hle (liftSubCrossingBySearches_valid hcrH)) hcr₂)
  rw [hG]
  rfl

end GraphMinor.HP25
