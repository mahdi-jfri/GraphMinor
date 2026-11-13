module

public import GraphMinor.GM04.Patchwork.Defs

/-!
# Pairings from bijections

For the robustness step of IV (9.2), a bijection between disjoint sets of
prescribed nodes gives a pairing on all nodes. Nodes outside the two sets
remain isolated. We verify the pairing and the two conditions defining
which sets it pairs.
-/

@[expose] public section

namespace GraphMinor.GM04

open Set

variable {α : Type*} {V X Y : Set α}

/-- The pairing joining each element of `X` to its image in `Y`, with the
other nodes of `V` isolated. This is used in IV (9.2), page 254. -/
def equivPairing (hX : X ⊆ V) (hY : Y ⊆ V) (hXY : Disjoint X Y) (e : X ≃ Y) :
    (⊤ : SimpleGraph α).Subgraph where
  verts := V
  Adj a b := ∃ x : X, (a = x ∧ b = e x) ∨ (b = x ∧ a = e x)
  adj_sub := by
    rintro a b ⟨x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact fun h ↦ (Set.disjoint_left.mp hXY x.property (h ▸ (e x).property))
    · exact fun h ↦ (Set.disjoint_left.mp hXY x.property (h.symm ▸ (e x).property))
  edge_vert := by
    rintro a b ⟨x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact hX x.property
    · exact hY (e x).property
  symm := ⟨by
    rintro a b ⟨x, h | h⟩
    · exact ⟨x, Or.inr h⟩
    · exact ⟨x, Or.inl h⟩⟩

/-- Every node in this pairing has at most one neighbour. -/
theorem equivPairing_neighbor_unique (hX : X ⊆ V) (hY : Y ⊆ V)
    (hXY : Disjoint X Y) (e : X ≃ Y) {a b c : α}
    (hab : (equivPairing hX hY hXY e).Adj a b)
    (hac : (equivPairing hX hY hXY e).Adj a c) : b = c := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hac
  rcases hx with ⟨hax, hbx⟩ | ⟨hbx, hax⟩ <;>
    rcases hy with ⟨hay, hcy⟩ | ⟨hcy, hay⟩
  · have hxy : x = y := Subtype.ext (hax.symm.trans hay)
    exact hbx.trans ((congrArg (fun z : X ↦ (e z : α)) hxy).trans hcy.symm)
  · exact False.elim (Set.disjoint_left.mp hXY
      (show a ∈ X from hax ▸ x.property) (show a ∈ Y from hay ▸ (e y).property))
  · exact False.elim (Set.disjoint_left.mp hXY
      (show a ∈ X from hay ▸ y.property) (show a ∈ Y from hax ▸ (e x).property))
  · have hxy : x = y := e.injective (Subtype.ext (hax.symm.trans hay))
    exact hbx.trans ((congrArg Subtype.val hxy).trans hcy.symm)

/-- The graph made from the bijection is a pairing in `V`. -/
theorem isPairing_equivPairing (hV : V.Finite) (hX : X ⊆ V) (hY : Y ⊆ V)
    (hXY : Disjoint X Y) (e : X ≃ Y) : IsPairing V (equivPairing hX hY hXY e) :=
  (isPairing_iff hV).mpr ⟨subset_rfl,
    fun _ _ _ hab hac ↦ equivPairing_neighbor_unique hX hY hXY e hab hac⟩

/-- The bijection's pairing pairs precisely the two prescribed sets, in the
sense of Graph Minors IV, Section 6. -/
theorem pairs_equivPairing (hV : V.Finite) (hX : X ⊆ V) (hY : Y ⊆ V)
    (hXY : Disjoint X Y) (e : X ≃ Y) : Pairs V (equivPairing hX hY hXY e) X Y := by
  apply (pairs_iff_of_isPairing hV (isPairing_equivPairing hV hX hY hXY e)).mpr
  refine ⟨hX, hY, hXY, ?_, ?_⟩
  · rintro a b ⟨x, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨x.property, (e x).property⟩
    · exact Or.inr ⟨(e x).property, x.property⟩
  · rintro a (ha | ha)
    · exact ⟨e ⟨a, ha⟩, ⟨⟨a, ha⟩, Or.inl ⟨rfl, rfl⟩⟩⟩
    · exact ⟨e.symm ⟨a, ha⟩, ⟨e.symm ⟨a, ha⟩, Or.inr ⟨rfl,
        congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩).symm⟩⟩⟩

end GraphMinor.GM04
