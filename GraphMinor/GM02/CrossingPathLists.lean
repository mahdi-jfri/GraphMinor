module

public import GraphMinor.GM02.CrossingScheme
public import GraphMinor.GM02.PathListArrangement
import GraphMinor.GM02.CrossingSchemeSupports

/-!
# Recording the paths of a crossing scheme

For II (2.8), orient each path by the fixed order chosen for its original
unordered pair. Record its internal separator vertices as a list. Mark
unused separator vertices reserved for the first side, and original
separator terminals belonging to the first termination. These marks also
record the possible first-edge color when both original ends are in the
separator.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- The graph formed by the two terminations in condition (iv). -/
abbrev CrossingScheme.pairGraph {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀) : SimpleGraph α :=
  SimpleGraph.fromEdgeSet (C.left.pairs ∪ C.right.pairs : Finset (Sym2 α))

/-- Choose the path belonging to an original pair in condition (iv). -/
noncomputable def CrossingScheme.pairPath {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀)
    (p : {p // p ∈ A₀.pairs}) : C.pairGraph.Walk p.val.out.1 p.val.out.2 :=
  C.path_union.choose p

/-- The chosen paths have no repeated vertices. -/
theorem CrossingScheme.pairPath_isPath {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀)
    (p : {p // p ∈ A₀.pairs}) : (C.pairPath p).IsPath :=
  C.path_union.choose_spec.1 p

/-- Different original pairs have disjoint chosen paths. -/
theorem CrossingScheme.pairPath_disjoint {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀)
    (p q : {p // p ∈ A₀.pairs}) (hpq : p ≠ q) :
    Disjoint {a | a ∈ (C.pairPath p).support} {a | a ∈ (C.pairPath q).support} :=
  C.path_union.choose_spec.2.1 p q hpq

/-- All path vertices belong to the two new supports. -/
theorem CrossingScheme.pairPath_support_subset {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀)
    (p : {p // p ∈ A₀.pairs}) :
    {a | a ∈ (C.pairPath p).support} ⊆ C.left.support ∪ C.right.support := by
  intro a ha
  rw [← C.path_union.choose_spec.2.2.1]
  exact Set.mem_iUnion.2 ⟨p, ha⟩

/-- Both endpoints of an original pair lie on its chosen path. -/
theorem CrossingScheme.pairPath_endpoint_mem {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀)
    (p : {p // p ∈ A₀.pairs}) {a : α} (ha : a ∈ p.val) :
    a ∈ (C.pairPath p).support := by
  have hout : s(p.val.out.1, p.val.out.2) = p.val := p.val.out_eq
  rw [← hout, Sym2.mem_iff] at ha
  rcases ha with rfl | rfl
  · exact (C.pairPath p).start_mem_support
  · exact (C.pairPath p).end_mem_support

/-- A chosen path contains no original terminal other than its own ends,
since every other terminal belongs to a disjoint chosen path. -/
theorem CrossingScheme.pairPath_original_iff {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀)
    (p : {p // p ∈ A₀.pairs}) {a : α} (ha : a ∈ (C.pairPath p).support) :
    a ∈ A₀.support ↔ a ∈ p.val := by
  constructor
  · intro ha₀
    obtain ⟨q, hqa⟩ := Set.mem_iUnion.1 ha₀
    obtain ⟨hq, haq⟩ := Set.mem_iUnion.1 hqa
    have haQ := C.pairPath_endpoint_mem ⟨q, hq⟩ haq
    have hpq : p = ⟨q, hq⟩ := by
      by_contra hn
      exact Set.disjoint_left.1 (C.pairPath_disjoint p ⟨q, hq⟩ hn) ha haQ
    rw [hpq]
    exact haq
  · intro hap
    exact Set.mem_iUnion.2 ⟨p.val, Set.mem_iUnion.2 ⟨p.property, hap⟩⟩

/-- Every non-end vertex of a chosen path is a nonterminal separator
vertex. These are exactly the vertices recorded in its internal list. -/
theorem CrossingScheme.pairPath_internal_separator {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀)
    (p : {p // p ∈ A₀.pairs}) {a : α} (ha : a ∈ (C.pairPath p).support)
    (hn : a ∉ p.val) : a ∈ (V(H) ∩ V(H')) \ A₀.support := by
  have ha₀ : a ∉ A₀.support := fun h => hn ((C.pairPath_original_iff p ha).1 h)
  have haU := C.pairPath_support_subset p ha
  rw [C.support_union_eq] at haU
  rcases haU with haOld | haBoth
  · exact (ha₀ haOld).elim
  · exact C.inter_support_subset haBoth

/-- Lists and marks associated with a crossing scheme for the insertion
count. Terminal separator vertices are marked rather than put in the lists. -/
noncomputable def CrossingScheme.pathListArrangement {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀) :
    PathListArrangement (V(H) ∩ V(H')) {p // p ∈ A₀.pairs} where
  paths p := (C.pairPath p).support.filter (fun a => a ∈ (V(H) ∩ V(H')) \ A₀.support)
  nodup p := (C.pairPath_isPath p).support_nodup.filter _
  vertex_mem _ _ ha := (of_decide_eq_true (List.mem_filter.1 ha).2).1
  disjoint p q hpq a hap haq := Set.disjoint_left.1 (C.pairPath_disjoint p q hpq)
    (List.mem_filter.1 hap).1 (List.mem_filter.1 haq).1
  marked := C.reservedLeft ∪ (A₀.support ∩ (V(H) ∩ V(H')) ∩ C.left.support)
  marked_subset _ ha := ha.elim (fun h => C.reservedLeft_subset h) (fun h => h.1.2)
  marked_unused a ha p hap := by
    obtain ⟨haP, haBool⟩ := List.mem_filter.1 hap
    have ⟨haX, ha₀⟩ := of_decide_eq_true haBool
    rcases ha with haZ | haTerm
    · have haU : a ∈ C.reservedLeft ∪ C.reservedRight := Or.inl haZ
      rw [C.reserved_union] at haU
      have haNew := C.pairPath_support_subset p haP
      exact haU.2 (haNew.elim (fun h => Or.inl (Or.inr h)) Or.inr)
    · exact ha₀ haTerm.1.1

end GraphMinor.GM02
