module

public import GraphMinor.Compute.GM06LinkageRowsEncoding
public import GraphMinor.Compute.GM06EdgeMaskData
public import GraphMinor.Compute.GM06InducedEdgeBits
import GraphMinor.Compute.GM06PullbackWalkEncoding
import GraphMinor.GM06.Section3Induce
import GraphMinor.GM11.Section5
import GraphMinor.GM11.Walks

/-!
# The path rows survive the two deletion reductions

Reductions 1 and 2 in VI (5.7), page 133, delete edges or vertices
without changing the given linkage. Transfer its encoded walks to
the retained subdrawing, preserving their support, edge list and
directed words. Updating only the activity words leaves the dart
endpoints unchanged. The deleted-edge mask and the induced mask
both retain each edge of the given paths, so their original rows
continue to encode exactly the same linkage paths. Returned linkage
rows also lift back to the old graph without any changes.
-/

public section
universe u v
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

/-- Retagging activity words does not change either endpoint of a dart. -/
theorem gm06Dart_endpoints_retag {n : ℕ} (tagged : List ((Fin n × Fin n) × ℕ))
    (mask : List ℕ) (d : Fin (2 * tagged.length)) :
    let d' : Fin (2 * (gm06RetagEdges tagged mask).length) :=
      ⟨d.val, by rw [gm06RetagEdges_length]; exact d.isLt⟩
    gm06DartTail (gm06RetagEdges tagged mask) d' = gm06DartTail tagged d ∧
      gm06DartHead (gm06RetagEdges tagged mask) d' = gm06DartHead tagged d := by
  simp [gm06DartTail, gm06DartHead, gm06RetagEdges, List.getElem_mapIdx]

/-- A walk and its directed row pass to any graph retaining all
its links and vertices, provided its row words remain active. -/
theorem GM06WalkDartEncoding.exists_retag_transfer
    {n : ℕ} {α : Type u} {β : Type v} {G H : Graph α β}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → α}
    {edge : Fin tagged.length → β} {x y : α} {W : GraphWalk G x y} {row : List ℕ}
    (h : GM06WalkDartEncoding G tagged vertex edge W row)
    (mask : List ℕ) (hlen : mask.length = tagged.length)
    (hl : ∀ e a b, e ∈ W.edges → G.IsLink e a b → H.IsLink e a b)
    (hV : ∀ z ∈ W.support, z ∈ H.vertexSet)
    (hkeep : ∀ d ∈ row, mask[d / 2]?.getD 0 = 1) :
    ∃ W' : GraphWalk H x y,
      GM06WalkDartEncoding H (gm06RetagEdges tagged mask) vertex
        (fun j => edge (Fin.cast (gm06RetagEdges_length tagged mask) j)) W' row ∧
      W'.support = W.support ∧ W'.edges = W.edges := by
  induction h with
  | nil hx => exact ⟨.nil (hV _ (by simp)), .nil _, rfl, rfl⟩
  | @cons x y z e he R row d hd hactive hedge htail hhead hrest ih =>
    obtain ⟨R', hR', hs, heq⟩ := ih
      (fun f a b hf hlink => hl f a b (List.mem_cons_of_mem e hf) hlink)
      (fun p hp => hV p (List.mem_cons_of_mem x hp))
      (fun q hq => hkeep q (List.mem_cons_of_mem d hq))
    have hd' : d < 2 * (gm06RetagEdges tagged mask).length := by
      rw [gm06RetagEdges_length]; exact hd
    have hflag : ((gm06RetagEdges tagged mask)[d / 2]'(by omega)).2 = 1 := by
      rw [gm06RetagEdges_getElem tagged mask hlen (show d / 2 < tagged.length by omega)]
      have hm := hkeep d (List.mem_cons_self)
      simpa only [List.getElem?_eq_getElem (show d / 2 < mask.length by omega), Option.getD_some] using hm
    have hend := gm06Dart_endpoints_retag tagged mask ⟨d, hd⟩
    refine ⟨.cons (hl e x y (List.mem_cons_self) he) R',
      .cons hd' hflag hedge ?_ ?_ hR', ?_, ?_⟩
    · exact (congrArg vertex hend.1).trans htail
    · exact (congrArg vertex hend.2).trans hhead
    · simp only [GraphWalk.support_cons, hs]
    · simp only [GraphWalk.edges_cons, heq]

/-- If a subdrawing retains the given linkage, replacing activity
words by its exact edge mask preserves the entire path-row encoding. -/
theorem gm06LinkageRowsEncoding_restrict
    {n k : ℕ} {G H : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (M : CylinderLinkage k H)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n → ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder) (rows : List (List ℕ))
    (hrows : GM06LinkageRowsEncoding L tagged vertex edge rows)
    (hHG : H.IsSubdrawing G) (hpaths : M.pathDrawing = L.pathDrawing) (hcurves : M.curve = L.curve)
    (mask : List ℕ) (hlen : mask.length = tagged.length)
    (hkeep : ∀ j : Fin tagged.length, tagged[j].2 = 1 → edge j ∈ H.E →
      mask[j.val]?.getD 0 = 1) :
    GM06LinkageRowsEncoding M (gm06RetagEdges tagged mask) vertex
      (fun j => edge (Fin.cast (gm06RetagEdges_length tagged mask) j)) rows := by
  refine ⟨hrows.1, ?_⟩
  intro i
  rw [hcurves, hpaths]
  obtain ⟨W, hsimple, henc, hW⟩ := hrows.2 i
  have hpath : (L.pathDrawing i).IsSubdrawing H := by
    rw [← hpaths]
    exact (M.isSubdrawing i).1
  have hV : ∀ z ∈ W.support, z ∈ H.V := by
    intro z hz
    apply hpath.1
    rw [← hW, walkDrawing_V]
    exact hz
  have hE : ∀ e ∈ W.edges, e ∈ H.E := by
    intro e he
    apply hpath.2
    rw [← hW, walkDrawing_E]
    exact he
  have hm : ∀ d ∈ (rows[i.val]?.getD []), mask[d / 2]?.getD 0 = 1 := by
    intro d hd
    obtain ⟨hd', hflag⟩ := henc.active_words d hd
    let j : Fin tagged.length := ⟨d / 2, by omega⟩
    have he : edge j ∈ W.edges := (henc.edge_mem_iff _).mpr ⟨d, hd, hd', rfl⟩
    exact hkeep j hflag (hE _ he)
  obtain ⟨W', henc', hs, he⟩ := henc.exists_retag_transfer mask hlen
    (fun e a b he hl => (hHG.isLink_iff (hE e he)).mpr hl) hV hm
  refine ⟨W', ?_, henc', ?_⟩
  · change W'.support.Nodup
    rw [hs]
    exact hsimple
  · apply Drawing.ext_of_V_E
    · rw [walkDrawing_V, hs, ← walkDrawing_V G W, hW]
    · rw [walkDrawing_E, he, ← walkDrawing_E G W, hW]

/-- Clearing the deleted edge's activity flag preserves the given
linkage rows whenever that linkage survives the edge deletion. -/
theorem gm06LinkageRowsEncoding_deleteEdge
    {n k : ℕ} {G : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (tagged : List ((Fin n × Fin n) × ℕ))
    (vertex : Fin n → ClosedCylinder) (edge : Fin tagged.length → Set ClosedCylinder)
    (rows : List (List ℕ)) (hrows : GM06LinkageRowsEncoding L tagged vertex edge rows)
    (d : Fin tagged.length) (M : CylinderLinkage k (G.deleteEdge (edge d)))
    (hpaths : M.pathDrawing = L.pathDrawing) (hcurves : M.curve = L.curve) :
    let mask := (tagged.map Prod.snd).set d.val 0
    GM06LinkageRowsEncoding M (gm06RetagEdges tagged mask) vertex
      (fun j => edge (Fin.cast (gm06RetagEdges_length tagged mask) j)) rows := by
  let mask := (tagged.map Prod.snd).set d.val 0
  have hHG : (G.deleteEdge (edge d)).IsSubdrawing G := by
    refine ⟨?_, ?_⟩
    · rw [GraphMinor.GM11.deleteEdge_V]
    · rw [deleteEdge_E]; exact sdiff_subset
  apply gm06LinkageRowsEncoding_restrict L M tagged vertex edge rows hrows hHG hpaths hcurves
    mask (by simp only [mask, List.length_set, List.length_map])
  intro j hj he
  have hjd : d.val ≠ j.val := by
    intro hh
    have heq : d = j := Fin.ext hh
    rw [deleteEdge_E] at he
    exact he.2 (heq ▸ mem_singleton _)
  rw [List.getElem?_eq_getElem (show j.val < mask.length by simp only [mask, List.length_set, List.length_map]; exact j.isLt),
    Option.getD_some, List.getElem_set_ne hjd, List.getElem_map]
  exact hj

/-- The induced edge mask retains every given path row when the
induced drawing contains exactly the same given linkage. -/
theorem gm06LinkageRowsEncoding_induce
    {n k : ℕ} {G : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (tagged : List ((Fin n × Fin n) × ℕ))
    (vertex : Fin n ↪ ClosedCylinder) (edge : Fin tagged.length → Set ClosedCylinder)
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (rows : List (List ℕ)) (hrows : GM06LinkageRowsEncoding L tagged vertex edge rows)
    (C : Finset (Fin n)) (hC : vertex '' (C : Set (Fin n)) ⊆ G.V)
    (M : CylinderLinkage k (induceDrawing G (vertex '' (C : Set (Fin n)))))
    (hpaths : M.pathDrawing = L.pathDrawing) (hcurves : M.curve = L.curve) :
    let mask := gm06InducedEdgeBits tagged C
    GM06LinkageRowsEncoding M (gm06RetagEdges tagged mask) vertex
      (fun j => edge (Fin.cast (gm06RetagEdges_length tagged mask) j)) rows := by
  let mask := gm06InducedEdgeBits tagged C
  apply gm06LinkageRowsEncoding_restrict L M tagged vertex edge rows hrows
    (induceDrawing_isSubdrawing G hC) hpaths hcurves mask (gm06InducedEdgeBits_length tagged C)
  intro j hj he
  rw [induceDrawing_E] at he
  have hl := hlinks j hj
  have hu : tagged[j].1.1 ∈ C := by
    obtain ⟨x, hx, heq⟩ := he.2 (show vertex tagged[j].1.1 ∈ closure (edge j) ∩ G.V from
      hl.2.2.2.symm ▸ mem_insert _ _)
    exact vertex.injective heq ▸ hx
  have hv : tagged[j].1.2 ∈ C := by
    obtain ⟨x, hx, heq⟩ := he.2 (show vertex tagged[j].1.2 ∈ closure (edge j) ∩ G.V from
      hl.2.2.2.symm ▸ mem_insert_of_mem (vertex tagged[j].1.1) (mem_singleton (vertex tagged[j].1.2)))
    exact vertex.injective heq ▸ hx
  rw [List.getElem?_eq_getElem (show j.val < mask.length by rw [gm06InducedEdgeBits_length]; exact j.isLt), Option.getD_some]
  exact (gm06InducedEdgeBits_getElem_eq_one tagged C j.isLt).mpr ⟨hj, hu, hv⟩

/-- An encoded walk in a retained graph lifts back to its old
activity table with exactly the same row, support and edge list. -/
theorem GM06WalkDartEncoding.exists_unretag_transfer
    {n : ℕ} {α : Type u} {β : Type v} (G : Graph α β) {H : Graph α β}
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n → α)
    (edge : Fin tagged.length → β) (mask : List ℕ) (hlen : mask.length = tagged.length)
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hV : H.vertexSet ⊆ G.vertexSet)
    (hmask : ∀ j : Fin tagged.length, mask[j.val]?.getD 0 = 1 → tagged[j].2 = 1)
    {x y : α} {W : GraphWalk H x y} {row : List ℕ}
    (h : GM06WalkDartEncoding H (gm06RetagEdges tagged mask) vertex
      (fun j => edge (Fin.cast (gm06RetagEdges_length tagged mask) j)) W row) :
    ∃ R : GraphWalk G x y, GM06WalkDartEncoding G tagged vertex edge R row ∧
      R.support = W.support ∧ R.edges = W.edges := by
  have hcover : ∀ z ∈ H.vertexSet, ∃ x ∈ G.vertexSet, x ∈ G.vertexSet ∧ id x = z :=
    fun z hz => ⟨z, hV hz, hV hz, rfl⟩
  have hword : ∀ (d : ℕ) (hd : d < 2 * (gm06RetagEdges tagged mask).length),
      ((gm06RetagEdges tagged mask)[d / 2]'(by omega)).2 = 1 →
      ∃ hdold : d < 2 * tagged.length,
        (tagged[d / 2]'(by omega)).2 = 1 ∧
        id (edge ⟨d / 2, by omega⟩) =
          edge (Fin.cast (gm06RetagEdges_length tagged mask) ⟨d / 2, by omega⟩) ∧
        id (vertex (gm06DartTail tagged ⟨d, hdold⟩)) = vertex (gm06DartTail (gm06RetagEdges tagged mask) ⟨d, hd⟩) ∧
        id (vertex (gm06DartHead tagged ⟨d, hdold⟩)) = vertex (gm06DartHead (gm06RetagEdges tagged mask) ⟨d, hd⟩) ∧
        vertex (gm06DartTail tagged ⟨d, hdold⟩) ∈ G.vertexSet ∧
        vertex (gm06DartHead tagged ⟨d, hdold⟩) ∈ G.vertexSet := by
    intro d hd hflag
    have hdold : d < 2 * tagged.length := by simpa only [gm06RetagEdges_length] using hd
    have hj : d / 2 < tagged.length := by omega
    rw [gm06RetagEdges_getElem tagged mask hlen hj] at hflag
    have hflagOld : (tagged[d / 2]'hj).2 = 1 := hmask ⟨d / 2, hj⟩ (by
      simpa only [List.getElem?_eq_getElem (show d / 2 < mask.length by omega), Option.getD_some] using hflag)
    have hl := gm06Dart_isLink G tagged vertex edge hlinks ⟨d, hdold⟩ hflagOld
    have hend := gm06Dart_endpoints_retag tagged mask ⟨d, hdold⟩
    exact ⟨hdold, hflagOld, rfl, (congrArg vertex hend.1).symm,
      (congrArg vertex hend.2).symm, hl.left_mem, hl.right_mem⟩
  obtain ⟨s, hs, t, ht, R, hR, hfx, hfy, hsupport, hedges, _⟩ :=
    h.exists_image_pullback G tagged vertex edge id id G.vertexSet
      (fun _ _ _ _ he => he) hlinks hcover hword
  change s = x at hfx
  change t = y at hfy
  cases hfx
  cases hfy
  exact ⟨R, hR, by simpa only [List.map_id] using hsupport, by simpa only [List.map_id] using hedges⟩

/-- A returned linkage in a deleted or induced drawing needs no
row changes when it is returned to the old graph. Its paths and
curves, hence its winding, remain exactly the same. -/
theorem gm06LinkageRowsEncoding_lift_subdrawing
    {n k : ℕ} {G H : Drawing ClosedCylinder} {θ : ℝ}
    (hHG : H.IsSubdrawing G)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n → ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder) (mask : List ℕ) (hlen : mask.length = tagged.length)
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hmask : ∀ j : Fin tagged.length, mask[j.val]?.getD 0 = 1 → tagged[j].2 = 1)
    (M : CylinderLinkage k H) (hθ : M.HasTheta θ) (rows : List (List ℕ))
    (hrows : GM06LinkageRowsEncoding M (gm06RetagEdges tagged mask) vertex
      (fun j => edge (Fin.cast (gm06RetagEdges_length tagged mask) j)) rows) :
    ∃ N : CylinderLinkage k G, N.HasTheta θ ∧ GM06LinkageRowsEncoding N tagged vertex edge rows ∧
      N.pathDrawing = M.pathDrawing ∧ N.curve = M.curve := by
  let N : CylinderLinkage k G := {
    pathDrawing := M.pathDrawing
    curve := M.curve
    isSubdrawing := fun j => ⟨(M.isSubdrawing j).1.trans hHG,
      ((M.isSubdrawing j).1.trans hHG).U_subset⟩
    isPath := M.isPath
    curve_parametrizes := M.curve_parametrizes
    curve_one_mem := M.curve_one_mem
    pairwise_disjoint := M.pairwise_disjoint }
  refine ⟨N, hθ, ⟨hrows.1, ?_⟩, rfl, rfl⟩
  intro j
  obtain ⟨W, hW, henc, hP⟩ := hrows.2 j
  obtain ⟨R, hR, hs, he⟩ := henc.exists_unretag_transfer G.toGraph tagged vertex edge mask hlen hlinks hHG.1 hmask
  refine ⟨R, ?_, hR, ?_⟩
  · change R.support.Nodup
    rw [hs]
    exact hW
  · change walkDrawing G R = M.pathDrawing j
    apply Drawing.ext_of_V_E
    · rw [walkDrawing_V, hs, ← walkDrawing_V H W, hP]
    · rw [walkDrawing_E, he, ← walkDrawing_E H W, hP]

end GraphMinor.Compute
