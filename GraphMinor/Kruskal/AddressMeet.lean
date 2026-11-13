module

public import GraphMinor.Kruskal.Addresses
public import Mathlib.Data.List.Infix

/-!
# Common ancestors of vertex addresses

Prefixes of a vertex address are the vertices on its path from the root.
The longest common prefix is therefore the last common ancestor of two
vertices. We prove its prefix properties and that it remains an address of
the same tree. These facts describe how recursive tree embeddings separate
branches and hence how their replacing edge paths can meet.
-/

@[expose] public section

namespace GraphMinor.Kruskal

/-- The longest common prefix of two vertex addresses. -/
def addressMeet : List ℕ → List ℕ → List ℕ
  | a :: p, b :: q => if a = b then a :: addressMeet p q else []
  | _, _ => []

/-- The common ancestor lies on the path to the first vertex. -/
theorem addressMeet_prefix_left (p q : List ℕ) : addressMeet p q <+: p := by
  induction p generalizing q with
  | nil => exact List.prefix_rfl
  | cons a p ih =>
    cases q with
    | nil => exact List.nil_prefix
    | cons b q =>
      by_cases hab : a = b
      · subst b
        simpa only [addressMeet, ↓reduceIte, List.cons_prefix_cons, true_and] using ih q
      · simp only [addressMeet, hab, ↓reduceIte, List.nil_prefix]

/-- The common ancestor lies on the path to the second vertex. -/
theorem addressMeet_prefix_right (p q : List ℕ) : addressMeet p q <+: q := by
  induction p generalizing q with
  | nil => exact List.nil_prefix
  | cons a p ih =>
    cases q with
    | nil => exact List.prefix_rfl
    | cons b q =>
      by_cases hab : a = b
      · subst b
        simpa only [addressMeet, ↓reduceIte, List.cons_prefix_cons, true_and] using ih q
      · simp only [addressMeet, hab, ↓reduceIte, List.nil_prefix]

/-- Every common ancestor is an ancestor of the longest common prefix. -/
theorem prefix_addressMeet {r p q : List ℕ} (hp : r <+: p) (hq : r <+: q) :
    r <+: addressMeet p q := by
  induction r generalizing p q with
  | nil => exact List.nil_prefix
  | cons a r ih =>
    cases p with
    | nil => exact (List.cons_ne_nil _ _ (List.prefix_nil.1 hp)).elim
    | cons b p =>
      obtain ⟨rfl, hptail⟩ := List.cons_prefix_cons.1 hp
      cases q with
      | nil => exact (List.cons_ne_nil _ _ (List.prefix_nil.1 hq)).elim
      | cons c q =>
        obtain ⟨rfl, hqtail⟩ := List.cons_prefix_cons.1 hq
        simpa only [addressMeet, ↓reduceIte, List.cons_prefix_cons, true_and] using ih hptail hqtail

/-- An address is a prefix of another exactly when it is their last common
ancestor. -/
theorem addressMeet_eq_left_iff (p q : List ℕ) : addressMeet p q = p ↔ p <+: q := by
  constructor
  · intro h
    simpa only [h] using addressMeet_prefix_right p q
  · intro h
    exact (addressMeet_prefix_left p q).sublist.antisymm
      (prefix_addressMeet List.prefix_rfl h).sublist

/-- All ancestors of a vertex are vertices of the same ordered tree. -/
theorem OrderedTree.prefix_mem_addresses (t : OrderedTree) {p q : List ℕ}
    (hq : q ∈ t.addresses) (hp : p <+: q) : p ∈ t.addresses := by
  refine OrderedTree.rec
    (motive_1 := fun t ↦ ∀ p q, q ∈ t.addresses → p <+: q → p ∈ t.addresses)
    (motive_2 := fun ts ↦ ∀ j : Fin ts.length, ∀ p q,
      q ∈ (ts[j]).addresses → p <+: q → p ∈ (ts[j]).addresses) ?_ ?_ ?_ t p q hq hp
  · intro ts ih p q hq hp
    cases q with
    | nil =>
      have heq : p = [] := List.prefix_nil.1 hp
      subst p
      exact OrderedTree.nil_mem_addresses _
    | cons i q =>
      rcases List.prefix_cons_iff.1 hp with hnil | ⟨r, hpr, hrq⟩
      · subst p
        exact OrderedTree.nil_mem_addresses _
      · obtain ⟨j, rfl, hbranch⟩ := (OrderedTree.cons_mem_addresses_iff ts i q).1 hq
        subst p
        apply (OrderedTree.cons_mem_addresses_iff ts j.val r).2
        exact ⟨j, rfl, ih j r q hbranch hrq⟩
  · exact fun j ↦ Fin.elim0 j
  · intro t ts iht ihts j p q hq hp
    cases j using Fin.cases with
    | zero => exact iht p q hq hp
    | succ j => exact ihts j p q hq hp

/-- The last common ancestor of two vertices is a vertex of their tree. -/
theorem OrderedTree.addressMeet_mem (t : OrderedTree) {p q : List ℕ}
    (hp : p ∈ t.addresses) : addressMeet p q ∈ t.addresses :=
  t.prefix_mem_addresses hp (addressMeet_prefix_left p q)

end GraphMinor.Kruskal
