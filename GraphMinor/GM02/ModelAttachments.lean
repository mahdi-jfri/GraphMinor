module

public import GraphMinor.GM02.MinorModelEnds
import Mathlib.Data.Set.Card.Arithmetic

/-!
# A bounded set of marks for a minor model

For II (4.8), mark every end of a representing edge and one chosen vertex
of each branch. Each edge contributes at most two ends. Thus the total
number of marks is at most twice the target edge count plus its vertex
count. Every mark is an original vertex, and each branch has a mark.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v u' v'

/-- All ends of the edges representing target edges. -/
def representingEnds {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (H : Graph α' β') (G : Graph α β) (ηe : β' → β) : Set α :=
  {x | ∃ e ∈ E(H), G.Inc (ηe e) x}

/-- The marks in the finite-pattern argument: representing-edge ends and
one chosen vertex of each branch. -/
def modelMarks {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    (H : Graph α' β') (G : Graph α β) (ηe : β' → β) (root : V(H) → α) : Set α :=
  representingEnds H G ηe ∪ Set.range root

/-- A set indexed by a finite type has cardinality at most the index count. -/
private theorem ncard_range_le_nat_card {ι : Type*} [Finite ι] {α : Type*} (f : ι → α) :
    (Set.range f).ncard ≤ Nat.card ι := by
  rw [← Set.image_univ]
  simpa only [Set.ncard_univ] using (Set.ncard_image_le (s := Set.univ) (f := f) (Set.finite_univ))

/-- The representing-edge ends contribute at most two vertices per target
edge. Repeated ends and ends shared between edges only reduce this count. -/
theorem IsMinorModel.ncard_representingEnds_le
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'} {ηv : α' → Set α} {ηe : β' → β}
    (hm : IsMinorModel H G ηv ηe) (hEH : E(H).Finite) :
    (representingEnds H G ηe).ncard ≤ 2 * E(H).ncard := by
  let : Finite E(H) := hEH.to_subtype
  have hex : ∀ e : E(H), ∃ a b, G.IsLink (ηe e.val) a b :=
    fun e => Graph.exists_isLink_of_mem_edgeSet (hm.edge_mem e.val e.property)
  choose a b hab using hex
  let f : E(H) × Bool → α := fun p => if p.2 then a p.1 else b p.1
  have heq : representingEnds H G ηe = Set.range f := by
    ext x
    constructor
    · rintro ⟨e, he, hx⟩
      rcases hx.eq_or_eq_of_isLink (hab ⟨e, he⟩) with h | h
      · exact ⟨(⟨e, he⟩, true), h.symm⟩
      · exact ⟨(⟨e, he⟩, false), h.symm⟩
    · rintro ⟨⟨e, flag⟩, rfl⟩
      cases flag with
      | false => exact ⟨e.val, e.property, (hab e).inc_right⟩
      | true => exact ⟨e.val, e.property, (hab e).inc_left⟩
  rw [heq]
  have hbool : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  simpa only [Nat.card_prod, hbool, Nat.card_coe_set_eq, Nat.mul_comm] using
    ncard_range_le_nat_card f

/-- Marking one vertex of each branch adds at most the target vertex count. -/
theorem IsMinorModel.ncard_modelMarks_le
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'} {ηv : α' → Set α} {ηe : β' → β}
    (hm : IsMinorModel H G ηv ηe) (hVH : V(H).Finite) (hEH : E(H).Finite)
    (root : V(H) → α) :
    (modelMarks H G ηe root).ncard ≤ 2 * E(H).ncard + V(H).ncard := by
  let : Finite V(H) := hVH.to_subtype
  have he := GraphMinor.GM02.IsMinorModel.ncard_representingEnds_le hm hEH
  have hr : (Set.range root).ncard ≤ V(H).ncard := by
    simpa only [Nat.card_coe_set_eq] using ncard_range_le_nat_card root
  exact (Set.ncard_union_le _ _).trans (Nat.add_le_add he hr)

/-- Every mark is a source vertex if each chosen branch vertex belongs to
its branch. -/
theorem IsMinorModel.modelMarks_subset
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'} {ηv : α' → Set α} {ηe : β' → β}
    (hm : IsMinorModel H G ηv ηe) (root : V(H) → α)
    (hroot : ∀ u, root u ∈ ηv u.val) : modelMarks H G ηe root ⊆ V(G) := by
  rintro x (⟨e, _, hx⟩ | ⟨u, rfl⟩)
  · exact hx.vertex_mem
  · exact hm.vertex_subset u.val u.property (hroot u)

end GraphMinor.GM02
