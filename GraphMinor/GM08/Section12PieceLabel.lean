module

public import GraphMinor.GM08.Section11Cells
public import GraphMinor.GM08.Section12PieceEmbedding
import GraphMinor.GM08.Section12PieceDrawing
import GraphMinor.GM08.Section12Pullback
import GraphMinor.GM16.DrawingGraphPaths
import GraphMinor.GM08.Section9DiscContext
import Mathlib.Data.List.Nodup

/-!
# The smaller rooted graph assigned to a foundation disc

Cut out the drawing inside the ring and pull it back to the original
graph. Order its boundary vertices and carry this order through the
drawing isomorphism. Reading the piece in its own disc proves that it
embeds in a disc. The strict bound on the number of ring vertices then
puts this label in the smaller class used in VIII, Section 12.
-/

public section

namespace GraphMinor.GM08

open Set Surface Graph

universe u v w

/-- A normal ring with fewer than `k` vertices gives the smaller rooted
graph label in the construction on VIII, page 272. Section 12 uses the
foundation size bound to supply the strict inequality. -/
theorem exists_ring_graph_label {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] (hS : IsClosedDisc (univ : Set S))
    (X : RootedGraph α β) (gd : GraftDrawing X.G X.toGraft.T S)
    {F : Set S} (hF : IsOArc F) (hNormal : gd.drawing.IsNormal F)
    {k : ℕ} (hcard : (gd.drawing.V ∩ F).ncard < k) :
    ∃ (R : RootedGraph α β) (μ : List S),
      R ∈ discRootedClassA S ((k : ℤ) - 1) ∧ IsRingGraph X gd F R μ := by
  classical
  have : T2Space S := (isSurface_of_closedDisc_univ hS).2.1
  have : Nonempty S := by
    obtain ⟨x, hx⟩ := hS.nonempty_discInt
    exact ⟨x⟩
  obtain ⟨J, hJD, hJV, hJE, hJU, hJN⟩ :=
    exists_drawing_inside_ring hS gd.drawing hF hNormal
  obtain ⟨G, hGX, hGV, hGE, hbij⟩ :=
    exists_subgraph_of_iso gd.iso (GM16.toGraph_le_of_isSubdrawing hJD)
  let T := {v ∈ V(X.G) | gd.iso.fv v ∈ gd.drawing.V ∩ F}
  have hTV : T ⊆ V(G) := by
    intro v hv
    rw [hGV]
    refine ⟨hv.1, ?_⟩
    change gd.iso.fv v ∈ J.V
    rw [hJV]
    exact ⟨hv.2.1, .inl hv.2.2⟩
  have hTfin : T.Finite := X.finite_G.1.subset (sep_subset _ _)
  let τ := hTfin.toFinset.toList
  have hτ : ∀ v, v ∈ τ ↔ v ∈ T := by intro v; simp [τ]
  have hn : τ.Nodup := Finset.nodup_toList _
  let R : RootedGraph α β := {
    G := G
    τ := τ
    τ_subset := fun v hv => hTV ((hτ v).mp hv)
    finite_G := ⟨X.finite_G.1.subset hGX.vertexSet_mono,
      X.finite_G.2.subset hGX.edgeSet_mono⟩ }
  let μ := τ.map gd.iso.fv
  have hμn : μ.Nodup := (List.nodup_map_iff_inj_on hn).mpr (by
    intro x hx y hy hxy
    exact gd.iso.fv_injOn ((hτ x).mp hx).1 ((hτ y).mp hy).1 hxy)
  have hμset : {x | x ∈ μ} = gd.drawing.V ∩ F := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
      exact ((hτ v).mp hv).2
    · intro hx
      obtain ⟨v, hv, hvx⟩ := gd.iso.exists_fv hx.1
      exact List.mem_map.mpr ⟨v, (hτ v).mpr ⟨hv, hvx.symm ▸ hx⟩, hvx⟩
  have hindex : R.index = (gd.drawing.V ∩ F).ncard := by
    change τ.length = _
    rw [← List.length_map (f := gd.iso.fv) (as := τ)]
    change μ.length = _
    rw [← hμset]
    have heq : {x | x ∈ μ} = (μ.toFinset : Set S) := by ext x; simp
    rw [heq, ncard_coe_finset, List.toFinset_card_of_nodup hμn]
  have hEmb : EmbedsGraft S R.toGraft := by
    obtain ⟨B, hB, hBd, -, hDisc⟩ := exists_ring_disc hS hF
    apply embedsGraft_of_drawing_in_disc hS R.toGraft J hB (hDisc ▸ hJU)
      (hBd.symm ▸ hJN) hbij.toIso
    intro x hx
    change gd.iso.fv x ∈ discBd B ↔ x ∈ τ
    rw [hBd, hτ]
    have hxX := hGX.vertexSet_mono hx
    constructor
    · intro hxF
      exact ⟨hxX, gd.iso.fv_mem hxX, hxF⟩
    · exact fun ht => ht.2.2
  refine ⟨R, μ, ⟨?_, hEmb, hn⟩, hGX, ?_, ?_, hμn, hμset, ?_, ?_⟩
  · rw [hindex]
    omega
  · rw [hGV]
    ext v
    constructor
    · rintro ⟨hv, hvJ⟩
      change gd.iso.fv v ∈ J.V at hvJ
      rw [gd.iso.fv_of_mem hv, hJV] at hvJ
      exact ⟨hv, hvJ⟩
    · rintro ⟨hv, hvJ⟩
      refine ⟨hv, ?_⟩
      change gd.iso.fv v ∈ J.V
      rw [gd.iso.fv_of_mem hv, hJV]
      exact hvJ
  · rw [hGE]
    ext e
    constructor
    · rintro ⟨he, heJ⟩
      change gd.iso.fe e ∈ J.E at heJ
      rw [gd.iso.fe_of_mem he, hJE] at heJ
      exact ⟨he, heJ⟩
    · rintro ⟨he, heJ⟩
      refine ⟨he, ?_⟩
      change gd.iso.fe e ∈ J.E
      rw [gd.iso.fe_of_mem he, hJE]
      exact heJ
  · exact (List.length_map (f := gd.iso.fv) (as := τ)).symm
  · intro n hn hn'
    have hv := ((hτ (τ[n])).mp (List.getElem_mem hn)).1
    refine ⟨hv, ?_⟩
    change (gd.iso.vertexEquiv ⟨τ[n], hv⟩).1 = μ[n]
    rw [← gd.iso.fv_of_mem hv]
    exact (List.getElem_map (f := gd.iso.fv) (l := τ) (i := n)).symm

end GraphMinor.GM08
