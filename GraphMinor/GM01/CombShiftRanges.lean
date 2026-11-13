module

public import GraphMinor.GM01.CombSegmentSupports

/-!
# The exact vertices and edges selected by a comb interval

For the contraction in Graph Minors I, (4.9), page 58, an internal
attachment outside the two ends must be assigned to a source vertex
outside their two-cell intervals. The consecutive-comb embedding has
exactly the vertices in its spine-index interval and reflects adjacency.
Thus an edge with both ends in one of those intervals is selected in
that end, including its whole replacing path.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- The consecutive-comb embedding selects exactly its interval of
spine positions, with every attached binary vertex at those positions. -/
theorem mem_range_combShiftEmbedding_iff {γ L m : ℕ} (offset : ℕ) (hbound : offset + m ≤ L)
    (v : (pathComb γ L).verts) :
    v ∈ range (combShiftEmbedding (γ := γ) offset hbound) ↔
      offset ≤ (pathCombSpineIndex v.val).val ∧
        (pathCombSpineIndex v.val).val < offset + m := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [combShiftEmbedding_spineIndex]
    have hw := (pathCombSpineIndex w.val).isLt
    omega
  · rintro ⟨hlo, hhi⟩
    obtain ⟨v, hv⟩ := v
    cases v with
    | inl k =>
      change offset ≤ k.val at hlo
      change k.val < offset + m at hhi
      let j : Fin m := ⟨k.val - offset, by omega⟩
      refine ⟨⟨Sum.inl j, pathComb_spine_mem γ m j⟩, ?_⟩
      apply Subtype.ext
      apply congrArg Sum.inl
      apply Fin.ext
      change offset + (k.val - offset) = k.val
      omega
    | inr pair =>
      obtain ⟨k, word⟩ := pair
      change offset ≤ k.val at hlo
      change k.val < offset + m at hhi
      let j : Fin m := ⟨k.val - offset, by omega⟩
      have hv' : Sum.inr (j, word) ∈ (pathComb γ m).verts := hv
      refine ⟨⟨Sum.inr (j, word), hv'⟩, ?_⟩
      apply Subtype.ext
      apply congrArg Sum.inr
      apply Prod.ext
      · apply Fin.ext
        change offset + (k.val - offset) = k.val
        omega
      · rfl

/-- The selected interval in the ambient source vertex type. -/
theorem mem_range_combShiftEmbedding_val_iff {γ L m : ℕ} (offset : ℕ)
    (hbound : offset + m ≤ L) (v : PathCombVertex L) :
    v ∈ range (fun w : (pathComb γ m).verts ↦ (combShiftEmbedding offset hbound w).val) ↔
      v ∈ (pathComb γ L).verts ∧ offset ≤ (pathCombSpineIndex v).val ∧
        (pathCombSpineIndex v).val < offset + m := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨(combShiftEmbedding offset hbound w).property,
      (mem_range_combShiftEmbedding_iff offset hbound _).mp (mem_range_self w)⟩
  · rintro ⟨hv, hlo, hhi⟩
    obtain ⟨w, hw⟩ := (mem_range_combShiftEmbedding_iff offset hbound ⟨v, hv⟩).mpr ⟨hlo, hhi⟩
    exact ⟨w, congrArg Subtype.val hw⟩

/-- Disjoint intervals remain disjoint in the ambient vertex type. -/
theorem disjoint_combShiftEmbedding_val_ranges {γ L m m' : ℕ} (offset offset' : ℕ)
    (hbound : offset + m ≤ L) (hbound' : offset' + m' ≤ L) (hgap : offset + m ≤ offset') :
    Disjoint (range (fun w : (pathComb γ m).verts ↦ (combShiftEmbedding offset hbound w).val))
      (range (fun w : (pathComb γ m').verts ↦ (combShiftEmbedding offset' hbound' w).val)) := by
  apply Set.disjoint_left.mpr
  intro v hv hv'
  have h := (mem_range_combShiftEmbedding_val_iff offset hbound v).mp hv
  have h' := (mem_range_combShiftEmbedding_val_iff offset' hbound' v).mp hv'
  omega

/-- Shifting a consecutive interval reflects as well as preserves
comb adjacency. No new edge appears between selected vertices. -/
theorem combShiftEmbedding_adj_iff {γ L m : ℕ} (offset : ℕ) (hbound : offset + m ≤ L)
    (v w : (pathComb γ m).verts) :
    (pathComb γ L).coe.Adj (combShiftEmbedding offset hbound v) (combShiftEmbedding offset hbound w) ↔
      (pathComb γ m).coe.Adj v w := by
  constructor
  · intro hvw
    obtain ⟨v, hv⟩ := v
    obtain ⟨w, hw⟩ := w
    cases v with
    | inl i =>
      cases w with
      | inl j =>
        apply pathComb_spine_adj (γ := γ)
        apply pathGraph_adj.mpr
        rcases pathGraph_adj.mp hvw with hfor | hback
        · exact Or.inl (by change offset + i.val + 1 = offset + j.val at hfor; omega)
        · exact Or.inr (by change offset + j.val + 1 = offset + i.val at hback; omega)
      | inr pair =>
        exact ⟨(combShiftIndex offset hbound).injective hvw.1, hvw.2⟩
    | inr pair =>
      cases w with
      | inl j => exact ⟨(combShiftIndex offset hbound).injective hvw.1, hvw.2⟩
      | inr pair' => exact ⟨(combShiftIndex offset hbound).injective hvw.1, hvw.2⟩
  · exact combShiftEmbedding_adj offset hbound

/-- A replacing path whose two source ends are in a selected interval
belongs wholly to that interval's subdivision support. -/
theorem path_subset_combSegmentSupport {α β : Type*} {γ L m : ℕ}
    (c : (pathComb γ L).verts → α) (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (offset : ℕ) (hbound : offset + m ≤ L) (e : (pathComb γ L).coe.edgeSet)
    {a b : (pathComb γ L).verts} (he : e.val = s(a,b))
    (ha : offset ≤ (pathCombSpineIndex a.val).val ∧ (pathCombSpineIndex a.val).val < offset + m)
    (hb : offset ≤ (pathCombSpineIndex b.val).val ∧ (pathCombSpineIndex b.val).val < offset + m) :
    V(P e) ⊆ combSegmentSupport c P offset hbound := by
  obtain ⟨a', ha'⟩ := (mem_range_combShiftEmbedding_iff offset hbound a).mpr ha
  obtain ⟨b', hb'⟩ := (mem_range_combShiftEmbedding_iff offset hbound b).mpr hb
  have hab : (pathComb γ L).coe.Adj a b := by
    have h := e.property
    rw [he] at h
    exact h
  have hab' : (pathComb γ m).coe.Adj a' b' :=
    (combShiftEmbedding_adj_iff offset hbound a' b').mp (ha'.symm ▸ hb'.symm ▸ hab)
  let e' : (pathComb γ m).coe.edgeSet := ⟨s(a',b'), hab'⟩
  have hmap : combShiftEdges offset hbound e' = e := by
    apply Subtype.ext
    exact (combShiftEdges_ends offset hbound (e := e') rfl).trans (by rw [ha', hb', he])
  intro x hx
  exact Or.inr (Set.mem_iUnion.mpr ⟨e', hmap.symm ▸ hx⟩)

/-- Membership in a selected segment is membership at a selected
centre or on a replacing path with both source ends selected. This
allows reflection of the two ends in the choice after GM01 (4.9). -/
theorem mem_combSegmentSupport_iff {α β : Type*} {γ L m : ℕ}
    (c : (pathComb γ L).verts → α) (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (offset : ℕ) (hbound : offset + m ≤ L) (x : α) :
    x ∈ combSegmentSupport c P offset hbound ↔
      (∃ v : (pathComb γ L).verts, offset ≤ (pathCombSpineIndex v.val).val ∧
        (pathCombSpineIndex v.val).val < offset + m ∧ c v = x) ∨
      ∃ e : (pathComb γ L).coe.edgeSet, x ∈ V(P e) ∧
        ∀ v ∈ e.val, offset ≤ (pathCombSpineIndex v.val).val ∧
          (pathCombSpineIndex v.val).val < offset + m := by
  let f := combShiftEmbedding (γ := γ) offset hbound
  let hf := fun {a b} (h : (pathComb γ m).coe.Adj a b) ↦ combShiftEmbedding_adj offset hbound h
  constructor
  · rintro (⟨w, hw⟩ | hxP)
    · have h := (mem_range_combShiftEmbedding_iff offset hbound (f w)).mp (mem_range_self w)
      exact Or.inl ⟨f w, h.1, h.2, hw⟩
    · obtain ⟨e, hxe⟩ := Set.mem_iUnion.mp hxP
      refine Or.inr ⟨subdivisionEmbeddingEdges f hf e, hxe, ?_⟩
      intro v hv
      exact (mem_range_combShiftEmbedding_iff offset hbound v).mp
        (subdivisionEmbeddingEdges_mem_range f hf e hv)
  · rintro (⟨v, hlo, hhi, hv⟩ | ⟨e, hxe, hEnds⟩)
    · obtain ⟨w, hw⟩ := (mem_range_combShiftEmbedding_iff offset hbound v).mpr ⟨hlo, hhi⟩
      exact Or.inl ⟨w, (congrArg c hw).trans hv⟩
    · obtain ⟨edge, he⟩ := e
      induction edge using Sym2.inductionOn with
      | hf a b =>
        exact path_subset_combSegmentSupport c P offset hbound ⟨s(a,b), he⟩ rfl
          (hEnds a (Sym2.mem_mk_left a b)) (hEnds b (Sym2.mem_mk_right a b)) hxe

end GraphMinor.GM01
