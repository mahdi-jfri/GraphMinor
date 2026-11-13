module

public import GraphMinor.Kruskal.TopologicalTransport
import GraphMinor.Minor.Basic
import Mathlib.Logic.Encodable.Basic

/-!
# Renaming subdivision sequences

A fixed pair of injective name maps preserves each edge subdivision: fresh
names stay fresh, and the two new links have the mapped ends. Thus a
subdivision sequence on countable ambient types can be given natural-number
names throughout. This lets edge-path constructions use pairs and sums for
names while still meeting the exact definition of topological containment.
-/

@[expose] public section

namespace GraphMinor.Kruskal

open Graph Set

/-- Rename a graph using fixed embeddings of its ambient name types. -/
abbrev renameBy {α β α' β' : Type*} (G : Graph α β)
    (v : α ↪ α') (e : β ↪ β') : Graph α' β' :=
  renameGraph G ⟨fun x ↦ v x.val, v.injective.comp Subtype.val_injective⟩
    ⟨fun d ↦ e d.val, e.injective.comp Subtype.val_injective⟩

theorem vertexSet_renameBy {α β α' β' : Type*} (G : Graph α β)
    (v : α ↪ α') (e : β ↪ β') : V(renameBy G v e) = v '' V(G) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.val, a.property, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem edgeSet_renameBy {α β α' β' : Type*} (G : Graph α β)
    (v : α ↪ α') (e : β ↪ β') : E(renameBy G v e) = e '' E(G) := by
  ext d
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.val, a.property, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem renameBy_isLink_iff {α β α' β' : Type*} (G : Graph α β)
    (v : α ↪ α') (e : β ↪ β') (d : β') (x y : α') :
    (renameBy G v e).IsLink d x y ↔
      ∃ a b c, G.IsLink a b c ∧ e a = d ∧ v b = x ∧ v c = y := by
  constructor
  · rintro ⟨a, b, c, h, ha, hb, hc⟩
    exact ⟨a.val, b.val, c.val, h, ha, hb, hc⟩
  · rintro ⟨a, b, c, h, ha, hb, hc⟩
    exact ⟨⟨a, h.edge_mem⟩, ⟨b, h.left_mem⟩, ⟨c, h.right_mem⟩, h, ha, hb, hc⟩

theorem renameBy_isLink {α β α' β' : Type*} (G : Graph α β)
    (v : α ↪ α') (e : β ↪ β') (d : β) (x y : α) :
    (renameBy G v e).IsLink (e d) (v x) (v y) ↔ G.IsLink d x y := by
  rw [renameBy_isLink_iff]
  constructor
  · rintro ⟨a, b, c, h, ha, hb, hc⟩
    have had := e.injective ha
    have hbx := v.injective hb
    have hcy := v.injective hc
    simpa only [had, hbx, hcy] using h
  · exact fun h ↦ ⟨d, x, y, h, rfl, rfl, rfl⟩

/-- Fixed injective maps preserve an edge subdivision, including its freshness
conditions. -/
theorem isEdgeSubdivision_renameBy {α β α' β' : Type*} {G H : Graph α β}
    (vMap : α ↪ α') (eMap : β ↪ β') (h : GM04.IsEdgeSubdivision G H) :
    GM04.IsEdgeSubdivision (renameBy G vMap eMap) (renameBy H vMap eMap) := by
  obtain ⟨d, u, w, a, f, g, hd, ha, hf, hg, hfg, hV, hE, hlinks⟩ := h
  have freshV : vMap a ∉ V(renameBy G vMap eMap) := by
    rw [vertexSet_renameBy]
    rintro ⟨b, hb, heq⟩
    exact ha (vMap.injective heq ▸ hb)
  have freshE (b : β) (hb : b ∉ E(G)) : eMap b ∉ E(renameBy G vMap eMap) := by
    rw [edgeSet_renameBy]
    rintro ⟨c, hc, heq⟩
    exact hb (eMap.injective heq ▸ hc)
  refine ⟨eMap d, vMap u, vMap w, vMap a, eMap f, eMap g,
    (renameBy_isLink G vMap eMap d u w).2 hd, freshV, freshE f hf, freshE g hg,
    (fun heq ↦ hfg (eMap.injective heq)), ?_, ?_, ?_⟩
  · rw [vertexSet_renameBy, hV, image_insert_eq, vertexSet_renameBy]
  · rw [edgeSet_renameBy, hE, image_insert_eq, image_insert_eq,
      image_sdiff eMap.injective, image_singleton, edgeSet_renameBy]
  · intro b x y
    constructor
    · intro hlink
      obtain ⟨b, x, y, hsource, rfl, rfl, rfl⟩ :=
        (renameBy_isLink_iff H vMap eMap b x y).1 hlink
      rcases (hlinks b x y).1 hsource with hold | hnew | hnew
      · exact Or.inl ⟨fun heq ↦ hold.1 (eMap.injective heq),
          (renameBy_isLink G vMap eMap b x y).2 hold.2⟩
      · obtain ⟨rfl, hends⟩ := hnew
        rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)
        · exact Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)
      · obtain ⟨rfl, hends⟩ := hnew
        rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)
        · exact Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)
    · rintro (⟨hne, hlink⟩ | ⟨rfl, hends⟩ | ⟨rfl, hends⟩)
      · obtain ⟨b, x, y, hsource, rfl, rfl, rfl⟩ :=
          (renameBy_isLink_iff G vMap eMap _ _ _).1 hlink
        apply (renameBy_isLink H vMap eMap b x y).2
        exact (hlinks b x y).2 (Or.inl ⟨fun heq ↦ hne (congrArg eMap heq), hsource⟩)
      · rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (renameBy_isLink H vMap eMap f u a).2
            ((hlinks f u a).2 (Or.inr (Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)))
        · exact (renameBy_isLink H vMap eMap f a u).2
            ((hlinks f a u).2 (Or.inr (Or.inl ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)))
      · rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (renameBy_isLink H vMap eMap g a w).2
            ((hlinks g a w).2 (Or.inr (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)))
        · exact (renameBy_isLink H vMap eMap g w a).2
            ((hlinks g w a).2 (Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)))

/-- A subdivision sequence with countable ambient names witnesses the exact
natural-name definition of topological containment. -/
theorem isTopologicalMinor_of_countable_subdivisions {α β : Type*}
    [Countable α] [Countable β] {G H : Graph α β}
    (h : Relation.ReflTransGen GM04.IsEdgeSubdivision G H) :
    GM04.IsTopologicalMinor G H := by
  obtain ⟨v, hv⟩ := exists_injective_nat α
  obtain ⟨e, he⟩ := exists_injective_nat β
  let vMap : α ↪ ℕ := ⟨v, hv⟩
  let eMap : β ↪ ℕ := ⟨e, he⟩
  have hseq : Relation.ReflTransGen GM04.IsEdgeSubdivision
      (renameBy G vMap eMap) (renameBy H vMap eMap) :=
    h.lift (fun K ↦ renameBy K vMap eMap) (fun _ _ hstep ↦
      isEdgeSubdivision_renameBy vMap eMap hstep)
  let φ := renameGraphIso G
    ⟨fun x ↦ vMap x.val, vMap.injective.comp Subtype.val_injective⟩
    ⟨fun d ↦ eMap d.val, eMap.injective.comp Subtype.val_injective⟩
  let ψ := renameGraphIso H
    ⟨fun x ↦ vMap x.val, vMap.injective.comp Subtype.val_injective⟩
    ⟨fun d ↦ eMap d.val, eMap.injective.comp Subtype.val_injective⟩
  exact ⟨renameBy G vMap eMap, renameBy H vMap eMap, ⟨φ⟩, hseq, H, le_rfl, ⟨ψ.symm⟩⟩

end GraphMinor.Kruskal
