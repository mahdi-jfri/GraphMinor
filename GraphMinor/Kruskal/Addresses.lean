module

public import GraphMinor.Kruskal.OrderedTrees
public import GraphMinor.GM04.Tree
public import Mathlib.Data.Finset.Union

/-!
# Vertex addresses of ordered rooted trees

A vertex is named by the list of branch indices on its path from the root.
The root has address `[]`. Removing the last index gives the parent. This
realizes a finite ordered tree as the rooted trees of Graph Minors IV,
Section 2, page 230, whose edges point away from the root.
-/

@[expose] public section

namespace GraphMinor.Kruskal.OrderedTree

/-- The finite set of addresses of vertices. At a branch with index `i`,
prefix `i` to every address of that branch. -/
def addresses : OrderedTree → Finset (List ℕ)
  | .node ts => insert [] (Finset.univ.biUnion fun i : Fin ts.length ↦
      (addresses ts[i]).image (fun p ↦ i.val :: p))
termination_by t => sizeOf t
decreasing_by
  exact sizeOf_lt_of_mem_children (.node ts) ts[i] (List.getElem_mem _)

/-- The empty address is the root of every tree. -/
theorem nil_mem_addresses (t : OrderedTree) : [] ∈ t.addresses := by
  cases t
  simp only [addresses, Finset.mem_insert_self]

/-- A nonempty address chooses one branch and then an address in that branch. -/
theorem cons_mem_addresses_iff (ts : List OrderedTree) (i : ℕ) (p : List ℕ) :
    i :: p ∈ (OrderedTree.node ts).addresses ↔
      ∃ j : Fin ts.length, i = j.val ∧ p ∈ (ts[j]).addresses := by
  simp only [addresses, Finset.mem_insert, List.cons_ne_nil, false_or,
    Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨j, q, hq, hqp⟩
    obtain ⟨hi, hp⟩ := List.cons.inj hqp
    exact ⟨j, hi.symm, hp ▸ hq⟩
  · rintro ⟨j, rfl, hp⟩
    exact ⟨j, p, hp, rfl⟩

/-- The parent of an address is also a vertex. -/
theorem dropLast_mem_addresses (t : OrderedTree) (p : List ℕ) (hp : p ∈ t.addresses) :
    p.dropLast ∈ t.addresses := by
  refine OrderedTree.rec
    (motive_1 := fun t ↦ ∀ p, p ∈ t.addresses → p.dropLast ∈ t.addresses)
    (motive_2 := fun ts ↦ ∀ i : Fin ts.length, ∀ p,
      p ∈ (ts[i]).addresses → p.dropLast ∈ (ts[i]).addresses) ?_ ?_ ?_ t p hp
  · intro ts ih p hp
    cases p with
    | nil => exact nil_mem_addresses _
    | cons i p =>
      obtain ⟨j, rfl, hbranch⟩ := (cons_mem_addresses_iff ts i p).1 hp
      cases p with
      | nil => exact nil_mem_addresses _
      | cons k p =>
        rw [List.dropLast_cons_cons]
        exact (cons_mem_addresses_iff ts j.val _).2 ⟨j, rfl, ih j _ hbranch⟩
  · exact fun i ↦ Fin.elim0 i
  · intro t ts iht ihts i p hp
    cases i using Fin.cases with
    | zero => exact iht p hp
    | succ i => exact ihts i p hp

/-- Repeatedly taking parents reaches the empty address. -/
theorem exists_iterate_dropLast_eq_nil (p : List ℕ) :
    ∃ n, List.dropLast^[n] p = [] := by
  induction hn : p.length using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    cases p with
    | nil => exact ⟨0, rfl⟩
    | cons i p =>
      have hlt : (i :: p).dropLast.length < n := by
        rw [← hn, List.length_dropLast]
        simp
      obtain ⟨k, hk⟩ := ih _ hlt _ rfl
      exact ⟨k + 1, by simpa only [Function.iterate_succ_apply] using hk⟩

/-- Realize an ordered tree as a finite rooted tree, using vertex addresses
and the operation of removing the last index as parent. -/
@[reducible] def toRootedTree (t : OrderedTree) : GM04.RootedTree (List ℕ) where
  verts := t.addresses
  root := []
  parent := List.dropLast
  root_mem := nil_mem_addresses t
  parent_mem := dropLast_mem_addresses t
  parent_root := rfl
  exists_iterate_eq_root _ _ := exists_iterate_dropLast_eq_nil _

/-- Join a branch address to the root's address set. `none` names the root,
and `some ⟨i, p⟩` prefixes the branch index `i` to `p`. -/
def branchAddress (ts : List OrderedTree) :
    Option (Σ i : Fin ts.length, {p // p ∈ (ts[i]).addresses}) →
      {p // p ∈ (OrderedTree.node ts).addresses}
  | none => ⟨[], nil_mem_addresses _⟩
  | some ⟨i, p⟩ => ⟨i.val :: p.val,
      (cons_mem_addresses_iff ts i.val p.val).2 ⟨i, rfl, p.property⟩⟩

/-- Root addresses and branch addresses give every vertex exactly once. -/
theorem branchAddress_bijective (ts : List OrderedTree) :
    Function.Bijective (branchAddress ts) := by
  constructor
  · intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y =>
        obtain ⟨i, p⟩ := y
        have h : ([] : List ℕ) = i.val :: p.val := congrArg Subtype.val hxy
        cases h
    | some x =>
      obtain ⟨i, p⟩ := x
      cases y with
      | none =>
        have h : i.val :: p.val = ([] : List ℕ) := congrArg Subtype.val hxy
        cases h
      | some y =>
        obtain ⟨j, q⟩ := y
        have h := List.cons.inj (congrArg Subtype.val hxy)
        have hij : i = j := Fin.ext h.1
        subst j
        have hpq : p = q := Subtype.ext h.2
        subst q
        rfl
  · rintro ⟨p, hp⟩
    cases p with
    | nil => exact ⟨none, Subtype.ext rfl⟩
    | cons i p =>
      obtain ⟨j, rfl, hbranch⟩ := (cons_mem_addresses_iff ts i p).1 hp
      exact ⟨some ⟨j, ⟨p, hbranch⟩⟩, Subtype.ext rfl⟩

/-- The equivalence from the root and its indexed branches to all addresses. -/
noncomputable def branchAddressEquiv (ts : List OrderedTree) :
    Option (Σ i : Fin ts.length, {p // p ∈ (ts[i]).addresses}) ≃
      {p // p ∈ (OrderedTree.node ts).addresses} :=
  Equiv.ofBijective (branchAddress ts) (branchAddress_bijective ts)

end GraphMinor.Kruskal.OrderedTree
