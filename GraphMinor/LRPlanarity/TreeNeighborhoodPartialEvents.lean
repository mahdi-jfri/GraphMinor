module

public import GraphMinor.LRPlanarity.TreeNeighborhoodContourEvents
public import GraphMinor.LRPlanarity.TreeNeighborhoodContourRecursion
import Mathlib.Data.List.Perm.Basic

/-!
# The finite markers on a partially attached tree

Part IV, Section 7b of the planarity note leaves one marker for every
unattached child and keeps every port at an included vertex. This file
records that finite set. Adding a leaf deletes its child marker and adds
exactly its local incidence list. The local list is disjoint from the
old marker set because its vertex was not previously included.
-/

public section
namespace GraphMinor.LRPlanarity

open Classical

/-- Part IV, Section 7b: ports at included vertices and child incidences
whose parent is included but whose child is not yet included. -/
@[expose] noncomputable def partialContourEvents {N : ℕ} (T : Forest N)
    (G : SimpleGraph (Fin N)) (S : Finset (Fin N)) : Finset (ContourEvent N) :=
  (Set.toFinite {event : ContourEvent N | match event with
    | .child w => w ∉ S ∧ ∃ v ∈ S, T.parent w = some v
    | .port p => T.BackEdge G p.edge ∧ p.vertex ∈ S}).toFinset

/-- A retained child marker has its parent, but not itself, included. -/
theorem child_mem_partialContourEvents_iff {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (S : Finset (Fin N)) (w : Fin N) :
    ContourEvent.child w ∈ partialContourEvents T G S ↔
      w ∉ S ∧ ∃ v ∈ S, T.parent w = some v := by
  simp only [partialContourEvents,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]

/-- A port marker is present exactly when its incident vertex is included. -/
theorem port_mem_partialContourEvents_iff {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (S : Finset (Fin N)) (p : Port N) :
    ContourEvent.port p ∈ partialContourEvents T G S ↔ T.BackEdge G p.edge ∧ p.vertex ∈ S := by
  simp only [partialContourEvents,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]

/-- The initial root polygon carries exactly its valid local incidence list. -/
theorem mem_partialContourEvents_singleton_iff {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    {order : ContourOrder N} (hvalid : ValidContourOrder T G order)
    (root : Fin N) (hroot : T.parent root = none) (event : ContourEvent N) :
    event ∈ partialContourEvents T G {root} ↔ event ∈ order root := by
  cases event with
  | port p =>
    rw [port_mem_partialContourEvents_iff,port_mem_valid_contour_iff hvalid]
    simp only [Finset.mem_singleton]
  | child w =>
    rw [child_mem_partialContourEvents_iff,child_mem_valid_contour_iff hvalid]
    constructor
    · rintro ⟨_,v,hv,hp⟩
      have he : v = root := Finset.mem_singleton.mp hv
      exact he ▸ hp
    · intro hp
      have hne : w ≠ root := by
        intro he
        rw [he,hroot] at hp
        cases hp
      exact ⟨by simpa only [Finset.mem_singleton] using hne,root,Finset.mem_singleton_self _,hp⟩

/-- A new vertex's local events are absent from the old partial marker set. -/
theorem local_events_not_partial {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    {order : ContourOrder N} (hvalid : ValidContourOrder T G order) (S : Finset (Fin N))
    (leaf : Fin N) (hleaf : leaf ∉ S) {event : ContourEvent N}
    (he : event ∈ order leaf) : event ∉ partialContourEvents T G S := by
  cases event with
  | port p =>
    have hp := (port_mem_valid_contour_iff hvalid leaf p).mp he
    intro hmem
    have hs := ((port_mem_partialContourEvents_iff T G S p).mp hmem).2
    exact hleaf (hp.2 ▸ hs)
  | child w =>
    have hp := (child_mem_valid_contour_iff hvalid leaf w).mp he
    intro hmem
    obtain ⟨_,v,hv,hpv⟩ := (child_mem_partialContourEvents_iff T G S w).mp hmem
    have heq : v = leaf := Option.some.inj (hpv.symm.trans hp)
    exact hleaf (heq ▸ hv)

/-- Part IV, Section 7b: inserting a leaf removes its retained child marker
and adds its local incidence list. -/
theorem mem_partialContourEvents_insert_iff {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    (hT : T.IsDFS G) {order : ContourOrder N} (hvalid : ValidContourOrder T G order)
    (S : Finset (Fin N)) (hclosed : ∀ v ∈ S, ∀ u, T.parent v = some u → u ∈ S)
    (leaf : Fin N) (hleaf : leaf ∉ S) (event : ContourEvent N) :
    event ∈ partialContourEvents T G (insert leaf S) ↔
      (event ∈ partialContourEvents T G S ∧ event ≠ ContourEvent.child leaf) ∨ event ∈ order leaf := by
  cases event with
  | port p =>
    rw [port_mem_partialContourEvents_iff,port_mem_partialContourEvents_iff,
      port_mem_valid_contour_iff hvalid]
    have hne : ContourEvent.port p ≠ ContourEvent.child leaf := by intro h; cases h
    simp only [Finset.mem_insert]
    constructor
    · rintro ⟨hb,he | hs⟩
      · exact Or.inr ⟨hb,he⟩
      · exact Or.inl ⟨⟨hb,hs⟩,hne⟩
    · rintro (⟨⟨hb,hs⟩,_⟩ | ⟨hb,he⟩)
      · exact ⟨hb,Or.inr hs⟩
      · exact ⟨hb,Or.inl he⟩
  | child w =>
    rw [child_mem_partialContourEvents_iff,child_mem_partialContourEvents_iff,
      child_mem_valid_contour_iff hvalid]
    constructor
    · rintro ⟨hw,v,hv,hp⟩
      have hwNotLeaf : w ≠ leaf := fun he => hw (Finset.mem_insert.mpr (Or.inl he))
      have hwNotS : w ∉ S := fun h => hw (Finset.mem_insert_of_mem h)
      rcases Finset.mem_insert.mp hv with he | hvS
      · exact Or.inr (he ▸ hp)
      · exact Or.inl ⟨⟨hwNotS,v,hvS,hp⟩,fun he => hwNotLeaf (ContourEvent.child.inj he)⟩
    · rintro (⟨⟨hwS,v,hv,hp⟩,hneq⟩ | hp)
      · have hwl : w ≠ leaf := fun he => hneq (congrArg ContourEvent.child he)
        exact ⟨fun h => (Finset.mem_insert.mp h).elim hwl hwS,v,Finset.mem_insert_of_mem hv,hp⟩
      · have hwS : w ∉ S := fun hw => hleaf (hclosed w hw leaf hp)
        have hwl : w ≠ leaf := by
          intro he
          rw [he] at hp
          have hd := (hT.2.1 leaf leaf hp).2
          exact Nat.ne_of_lt (Nat.lt_succ_self (T.depth leaf)) hd
        exact ⟨fun h => (Finset.mem_insert.mp h).elim hwl hwS,leaf,Finset.mem_insert_self _ _,hp⟩

end GraphMinor.LRPlanarity
