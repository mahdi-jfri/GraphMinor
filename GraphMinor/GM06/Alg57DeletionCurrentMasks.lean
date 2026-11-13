module

public import GraphMinor.GM06.Alg57RestrictedCurrentDrawing
import GraphMinor.GM06.Section5DeletedMaskGraph
import GraphMinor.GM06.Section5InducedMaskGraph
import GraphMinor.GM06.Section3Induce

/-!
# The literal deletion masks realize the retained current drawings

The deletion branches of VI (5.7), page 133, either clear one
ordinary edge flag or retain an induced set of live vertices.
Their finite masks only remove old active edges. Actual new links
and coverage then prove the exact mask interpretation needed by
the current-relation restriction theorem. This connects the two
literal mask updates to the positive pruned rows and undo records.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- New links and edge coverage make a mask exact when it only
removes old active labels and the old active edge labels are injective. -/
theorem GM06CurrentDrawingRep.mask_iff_of_links_and_cover
    {k : ℕ} {x : GM06SuccessorInput} {G H : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (mask : List ℕ) (hlen : mask.length = rep.tagged.length)
    (hremove : ∀ j : Fin rep.tagged.length,
      mask[j.val]'(hlen.symm ▸ j.isLt) = 1 → rep.tagged[j].2 = 1)
    (hlinks : ∀ j : Fin rep.tagged.length,
      mask[j.val]'(hlen.symm ▸ j.isLt) = 1 →
        H.toGraph.IsLink (rep.edge j) (rep.vertex rep.tagged[j].1.1) (rep.vertex rep.tagged[j].1.2))
    (hcover : ∀ e ∈ H.E, ∃ j : Fin rep.tagged.length,
      mask[j.val]'(hlen.symm ▸ j.isLt) = 1 ∧ rep.edge j = e) :
    ∀ j : Fin rep.tagged.length,
      mask[j.val]'(hlen.symm ▸ j.isLt) = 1 ↔ rep.tagged[j].2 = 1 ∧ rep.edge j ∈ H.E := by
  intro j
  constructor
  · intro hj
    exact ⟨hremove j hj, (hlinks j hj).edge_mem⟩
  · rintro ⟨hj, he⟩
    obtain ⟨l, hl, hle⟩ := hcover _ he
    have hlj : l = j := rep.edge_inj (hremove l hl) hj hle
    subst l
    exact hl

/-- Reduction 2 retains a subdrawing, as required by the deletion
and undo interpretations. This is part of its printed separation. -/
theorem Section5Reduction2Step.subdrawing
    {k : ℕ} {G H : Drawing ClosedCylinder} {L : CylinderLinkage k G} {M : CylinderLinkage k H}
    (step : Section5Reduction2Step k G L H M) : H.IsSubdrawing G := by
  obtain ⟨_, _, hsep, _⟩ := step
  exact ⟨hsep.1.vertexSet_mono, hsep.1.edgeSet_mono⟩

/-- Reduction 2 keeps the given path subdrawings literally. -/
theorem Section5Reduction2Step.pathDrawing_eq
    {k : ℕ} {G H : Drawing ClosedCylinder} {L : CylinderLinkage k G} {M : CylinderLinkage k H}
    (step : Section5Reduction2Step k G L H M) : M.pathDrawing = L.pathDrawing := by
  obtain ⟨_, _, _, _, _, _, _, hpaths, _⟩ := step
  exact hpaths

/-- Reduction 2 keeps the given parametrizations literally. -/
theorem Section5Reduction2Step.curve_eq
    {k : ℕ} {G H : Drawing ClosedCylinder} {L : CylinderLinkage k G} {M : CylinderLinkage k H}
    (step : Section5Reduction2Step k G L H M) : M.curve = L.curve := by
  obtain ⟨_, _, _, _, _, _, _, _, hcurves⟩ := step
  exact hcurves

/-- Clearing one active edge slot realizes the actual edge-deleted
current drawing, with exactly the filtered rotations and an actual
unchanged-row undo step. All vertex slots keep their live status. -/
theorem GM06CurrentDrawingRep.exists_deleted_currentDrawingRep
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) (d : Fin rep.tagged.length) (hd : rep.tagged[d].2 = 1)
    (M : CylinderLinkage k (G.deleteEdge (rep.edge d)))
    (hH : IsCylinderSection5Drawing k (G.deleteEdge (rep.edge d)))
    (hpaths : M.pathDrawing = L.pathDrawing) (hcurves : M.curve = L.curve) :
    let mask := (rep.tagged.map Prod.snd).set d.val 0
    ∃ cur : GM06CurrentDrawingRep (gm06RestrictSuccessorInput x mask) (G.deleteEdge (rep.edge d)) M,
      cur.live = rep.live ∧ cur.vertex = rep.vertex ∧
      cur.tagged = gm06RetagEdges rep.tagged mask ∧
      GM06UndoStep x.vertexCount k ⟨G, rep.tagged, rep.vertex, rep.edge⟩
        ⟨G.deleteEdge (rep.edge d), cur.tagged, cur.vertex, cur.edge⟩ none := by
  dsimp only
  let mask := (rep.tagged.map Prod.snd).set d.val 0
  have hlen : mask.length = rep.tagged.length := by simp only [mask, List.length_set, List.length_map]
  have hremove (j : Fin rep.tagged.length) (hj : mask[j.val]'(hlen.symm ▸ j.isLt) = 1) :
      rep.tagged[j].2 = 1 := by
    by_cases hdj : d.val = j.val
    · have hjd : j = d := Fin.ext hdj.symm
      subst j
      simp only [mask, List.getElem_set_self] at hj
      exact False.elim (Nat.zero_ne_one hj)
    · simpa only [mask, List.getElem_set_ne hdj, List.getElem_map, Fin.getElem_fin] using hj
  obtain ⟨hlinks, hcover⟩ := deleted_mask_links_and_cover G rep.tagged rep.vertex rep.edge
    rep.edge_inj rep.links rep.edge_cover d hd
  have hmask := rep.mask_iff_of_links_and_cover mask hlen hremove hlinks hcover
  have hA (a : Fin x.vertexCount) : a ∈ rep.live ↔
      a ∈ rep.live ∧ rep.vertex a ∈ (G.deleteEdge (rep.edge d)).V := by
    rw [GraphMinor.GM11.deleteEdge_V]
    exact ⟨fun ha => ⟨ha, rep.vertex_mem a ha⟩, And.left⟩
  exact rep.exists_restricted_currentDrawingRep hG hH (deleteEdge_isSubdrawing G (rep.edge d))
    M hpaths hcurves mask hlen hmask rep.live hA

/-- The induced live-vertex mask realizes exactly that induced
current drawing. The original vertex map and all surviving permanent
edge labels remain unchanged, and the rotations are the exact filters. -/
theorem GM06CurrentDrawingRep.exists_induced_currentDrawingRep
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hvinj : Function.Injective rep.vertex) (hG : IsCylinderSection5Drawing k G)
    (C : Finset (Fin x.vertexCount)) (hC : C ⊆ rep.live)
    (M : CylinderLinkage k (induceDrawing G (rep.vertex '' (C : Set (Fin x.vertexCount)))))
    (hH : IsCylinderSection5Drawing k (induceDrawing G (rep.vertex '' (C : Set (Fin x.vertexCount)))))
    (hpaths : M.pathDrawing = L.pathDrawing) (hcurves : M.curve = L.curve) :
    let mask := gm06InducedEdgeBits rep.tagged C
    ∃ cur : GM06CurrentDrawingRep (gm06RestrictSuccessorInput x mask)
        (induceDrawing G (rep.vertex '' (C : Set (Fin x.vertexCount)))) M,
      cur.live = C ∧ cur.vertex = rep.vertex ∧
      cur.tagged = gm06RetagEdges rep.tagged mask ∧
      GM06UndoStep x.vertexCount k ⟨G, rep.tagged, rep.vertex, rep.edge⟩
        ⟨induceDrawing G (rep.vertex '' (C : Set (Fin x.vertexCount))), cur.tagged, cur.vertex, cur.edge⟩ none := by
  dsimp only
  let vertex : Fin x.vertexCount ↪ ClosedCylinder := ⟨rep.vertex, hvinj⟩
  let mask := gm06InducedEdgeBits rep.tagged C
  have hlen : mask.length = rep.tagged.length := gm06InducedEdgeBits_length rep.tagged C
  have hCgeom : rep.vertex '' (C : Set (Fin x.vertexCount)) ⊆ G.V := by
    rintro y ⟨a, ha, rfl⟩
    exact rep.vertex_mem a (hC ha)
  have hremove (j : Fin rep.tagged.length) (hj : mask[j.val]'(hlen.symm ▸ j.isLt) = 1) :
      rep.tagged[j].2 = 1 := (gm06InducedEdgeBits_getElem_eq_one rep.tagged C j.isLt).mp hj |>.1
  obtain ⟨hlinks, hcover⟩ := induced_mask_links_and_cover G rep.tagged vertex rep.edge
    rep.links rep.edge_cover C hCgeom
  have hmask := rep.mask_iff_of_links_and_cover mask hlen hremove hlinks hcover
  have hA (a : Fin x.vertexCount) : a ∈ C ↔ a ∈ rep.live ∧
      rep.vertex a ∈ (induceDrawing G (rep.vertex '' (C : Set (Fin x.vertexCount)))).V := by
    rw [induceDrawing_V G hCgeom]
    constructor
    · intro ha
      exact ⟨hC ha, a, ha, rfl⟩
    · rintro ⟨_, c, hc, hca⟩
      exact hvinj hca ▸ hc
  exact rep.exists_restricted_currentDrawingRep hG hH (induceDrawing_isSubdrawing G hCgeom)
    M hpaths hcurves mask hlen hmask C hA

end GraphMinor.GM06
