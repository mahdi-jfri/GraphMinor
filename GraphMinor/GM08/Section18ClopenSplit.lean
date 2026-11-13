module

public import GraphMinor.GM08.Section18Subgraft
import GraphMinor.GM08.Section18SplitOuter
import GraphMinor.GM21.Section6Side
import GraphMinor.GM08.Section11Transport

/-!
# Splitting a graft drawing along an open and closed set

Page 288 of VIII splits a graft drawn in a surface by the components of the
surface. Let `K` be an open and closed subset of `Σ`. Each edge of a drawing
is connected, so it lies in `K` or misses it. So the vertices and edges drawn
in `K` and those drawn off `K` form a direct sum (`exists_clopen_split`), and
each piece is drawn in its part of `Σ`. Since `K` is open, a point of `K` is
on the boundary of `K` exactly when it is on the boundary of `Σ`, so the roots
of each piece are the old roots drawn there.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology Graph GraphMinor.Surface

universe u v w

/-- In a subgraph, an edge of the subgraph links the same ends as in the graph. -/
theorem isLink_of_le_of_mem {α : Type u} {β : Type v} {H G : Graph α β} (hHG : H ≤ G)
    {e : β} {x y : α} (h : G.IsLink e x y) (he : e ∈ E(H)) : H.IsLink e x y := by
  obtain ⟨u, w, huw⟩ := exists_isLink_of_mem_edgeSet he
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := (huw.mono hHG).eq_and_eq_or_eq_and_eq h
  · exact huw
  · exact huw.symm

/-- **The piece of a graft drawn in an open and closed set.** -/
theorem exists_clopen_piece {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    [T2Space S] [Nonempty S] {X : Graft α β} (gd : GraftDrawing X.G X.T S) {K : Set S}
    (hK : IsClopen K) :
    ∃ A : Graft α β, A.G = X.G.induce {v ∈ V(X.G) | gd.iso.fv v ∈ K} ∧
      A.T = X.T ∩ {v ∈ V(X.G) | gd.iso.fv v ∈ K} ∧ EmbedsGraft K A := by
  classical
  have hedge : ∀ e ∈ gd.drawing.E, (∃ y ∈ e, y ∉ Kᶜ) → Disjoint e Kᶜ := by
    rintro e he ⟨y, hye, hyK⟩
    rw [disjoint_compl_right_iff_subset]
    exact he.2.2.1.isConnected.isPreconnected.subset_isClopen hK ⟨y, hye, not_not.mp hyK⟩
  obtain ⟨J, hJ, hJU, hJV, hJE⟩ := exists_outside_drawing_edges hK.isClosed.isOpen_compl hedge
  rw [compl_compl] at hJU hJV
  have hf : IsClosedEmbedding (Subtype.val : K → S) := hK.isClosed.isClosedEmbedding_subtypeVal
  have hbdK : ∀ y : K, y ∈ bd K ↔ y.1 ∈ bd S := fun y =>
    (GM21.Side.mem_bd_iff_of_isOpenEmbedding hK.isOpen.isOpenEmbedding_subtypeVal).symm
  obtain ⟨A, hAX, hAV, hAE, hAT, hAemb⟩ := exists_subgraft_embedsGraft gd hJ hf
    (fun x hx => by rw [hJU] at hx; exact ⟨⟨x, hx.2⟩, rfl⟩)
    (fun y hyU hyb => by
      rw [hJU] at hyU
      rw [hJV]
      exact ⟨gd.isProper ⟨(hbdK y).mp hyb, hyU.1⟩, hyU.2⟩)
    (X.T ∩ {v ∈ V(X.G) | gd.iso.fv v ∈ K})
    (fun v hv => ⟨hv.2.1, by
      rw [hJV]
      exact ⟨(show gd.iso.fv v ∈ gd.drawing.V from Iso.fv_mem (a := gd.iso) hv.2.1), hv.2.2⟩⟩)
    (fun v hv hvJ => by
      rw [hJV] at hvJ
      constructor
      · rintro ⟨y, hy, hyv⟩
        refine ⟨?_, hv, hvJ.2⟩
        have hb : (gd.iso.vertexEquiv ⟨v, hv⟩).1 ∈ bd S := by
          rw [← Iso.fv_of_mem hv, ← hyv]; exact (hbdK y).mp hy
        exact (gd.mem_bd_iff v hv).mp hb
      · rintro ⟨hvT, -, hvK⟩
        have hb : gd.iso.fv v ∈ bd S := by
          rw [Iso.fv_of_mem hv]
          exact (gd.mem_bd_iff v hv).mpr hvT
        exact ⟨⟨_, hvK⟩, (hbdK ⟨_, hvK⟩).mpr hb, rfl⟩)
  refine ⟨A, ?_, hAT, hAemb⟩
  have hVeq : V(A.G) = {v ∈ V(X.G) | gd.iso.fv v ∈ K} := by
    rw [hAV, hJV]
    ext v
    exact ⟨fun h => ⟨h.1, h.2.2⟩,
      fun h => ⟨h.1, (show gd.iso.fv v ∈ gd.drawing.V from Iso.fv_mem (a := gd.iso) h.1), h.2⟩⟩
  refine Graph.ext (by rw [hVeq]; rfl) fun e x y => ?_
  rw [induce_isLink]
  constructor
  · intro h
    exact ⟨h.mono hAX, hVeq ▸ h.left_mem, hVeq ▸ h.right_mem⟩
  · rintro ⟨h, hx, -⟩
    refine isLink_of_le_of_mem hAX h ?_
    rw [hAE, hJE]
    have hge : gd.iso.fe e ∈ gd.drawing.E := Iso.fe_mem (a := gd.iso) h.edge_mem
    refine ⟨h.edge_mem, hge, ?_⟩
    rw [disjoint_compl_right_iff_subset]
    refine hge.2.2.1.isConnected.isPreconnected.subset_isClopen hK ?_
    have hl := ((Iso.isGraphBij gd.iso).isLink e h.edge_mem x h.left_mem y h.right_mem).mp h
    have hxc : gd.iso.fv x ∈ closure (gd.iso.fe e) := by
      have : gd.iso.fv x ∈ closure (gd.iso.fe e) ∩ gd.drawing.V := by
        rw [hl.2.2.2]; exact mem_insert _ _
      exact this.1
    obtain ⟨z, hzK, hze⟩ := mem_closure_iff.mp hxc K hK.isOpen hx.2
    exact ⟨z, hze, hzK⟩

/-- **Splitting a graft drawing along an open and closed set.** The part
drawn in `K` and the part drawn off `K` form a direct sum, and each is drawn
in its part of `Σ`. -/
theorem exists_clopen_split {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    [T2Space S] [Nonempty S] {X : Graft α β} (gd : GraftDrawing X.G X.T S) {K : Set S}
    (hK : IsClopen K) :
    ∃ A B : Graft α β, IsGraftDirectSum X A B ∧ EmbedsGraft K A ∧
      EmbedsGraft (Kᶜ : Set S) B ∧ A.T = X.T ∩ {v ∈ V(X.G) | gd.iso.fv v ∈ K} ∧
      A.G = X.G.induce {v ∈ V(X.G) | gd.iso.fv v ∈ K} := by
  obtain ⟨A, hAG, hAT, hA⟩ := exists_clopen_piece gd hK
  obtain ⟨B, hBG, hBT, hB⟩ := exists_clopen_piece gd hK.compl
  have hcompl : {v ∈ V(X.G) | gd.iso.fv v ∈ Kᶜ} = V(X.G) \ {v ∈ V(X.G) | gd.iso.fv v ∈ K} := by
    ext v
    exact ⟨fun h => ⟨h.1, fun h' => h.2 h'.2⟩, fun h => ⟨h.1, fun h' => h.2 ⟨h.1, h'⟩⟩⟩
  refine ⟨A, B, ⟨_, sep_subset _ _, ?_, hAG, hcompl ▸ hBG, hAT, ?_⟩, hA, hB, hAT, hAG⟩
  · intro e x y hl
    have hl' := ((Iso.isGraphBij gd.iso).isLink e hl.edge_mem x hl.left_mem y hl.right_mem).mp hl
    have hge : gd.iso.fe e ∈ gd.drawing.E := hl'.1
    have hmem : ∀ z ∈ ({x, y} : Set α), gd.iso.fv z ∈ closure (gd.iso.fe e) := by
      intro z hz
      have : gd.iso.fv z ∈ closure (gd.iso.fe e) ∩ gd.drawing.V := by
        rw [hl'.2.2.2]
        rcases hz with rfl | rfl
        · exact mem_insert _ _
        · exact mem_insert_of_mem _ rfl
      exact this.1
    have hpc : IsPreconnected (closure (gd.iso.fe e)) :=
      hge.2.2.1.isConnected.isPreconnected.closure
    have key : ∀ a b, a ∈ ({x, y} : Set α) → b ∈ ({x, y} : Set α) →
        gd.iso.fv a ∈ K → gd.iso.fv b ∈ K := fun a b ha hb haK =>
      hpc.subset_isClopen hK ⟨_, hmem a ha, haK⟩ (hmem b hb)
    constructor
    · rintro ⟨hx, hxK⟩
      exact ⟨hl.right_mem, key x y (mem_insert _ _) (mem_insert_of_mem _ rfl) hxK⟩
    · rintro ⟨hy, hyK⟩
      exact ⟨hl.left_mem, key y x (mem_insert_of_mem _ rfl) (mem_insert _ _) hyK⟩
  · rw [hBT]
    ext v
    constructor
    · rintro ⟨hvT, -, hvK⟩
      exact ⟨hvT, fun h => hvK h.2⟩
    · rintro ⟨hvT, hvK⟩
      exact ⟨hvT, X.T_subset hvT, fun h => hvK ⟨X.T_subset hvT, h⟩⟩

end GraphMinor.GM08
