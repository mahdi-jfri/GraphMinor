module

public import GraphMinor.Kruskal.Addresses
import Mathlib.Data.List.OfFn

/-!
# Addressing a finite indexed family of branches

A finite indexed family of branch trees gives an ordered tree by `List.ofFn`.
Its vertices are the root or a branch index together with a vertex in that
branch. The explicit equivalence keeps these descriptions available when
assembling rooted-tree isomorphisms.
-/

@[expose] public section

namespace GraphMinor.Kruskal.OrderedTree

/-- Insert the branch index in front of its address, or use the empty
address for the root. -/
def ofFnBranchAddress {n : ℕ} (f : Fin n → OrderedTree) :
    Option (Σ i : Fin n, {p // p ∈ (f i).addresses}) →
      {p // p ∈ (OrderedTree.node (List.ofFn f)).addresses}
  | none => ⟨[], nil_mem_addresses _⟩
  | some ⟨i, p⟩ => ⟨i.val :: p.val, by
      apply (cons_mem_addresses_iff (List.ofFn f) i.val p.val).2
      refine ⟨⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩, rfl, ?_⟩
      simpa only [Fin.getElem_fin, List.getElem_ofFn] using p.property⟩

/-- The indexed root-and-branch description is a bijection. -/
theorem ofFnBranchAddress_bijective {n : ℕ} (f : Fin n → OrderedTree) :
    Function.Bijective (ofFnBranchAddress f) := by
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
      obtain ⟨j, rfl, hbranch⟩ := (cons_mem_addresses_iff (List.ofFn f) i p).1 hp
      let j' : Fin n := ⟨j.val, by simpa only [List.length_ofFn] using j.isLt⟩
      have hj : p ∈ (f j').addresses := by
        simpa only [Fin.getElem_fin, List.getElem_ofFn] using hbranch
      exact ⟨some ⟨j', ⟨p, hj⟩⟩, Subtype.ext rfl⟩

/-- The equivalence from the root and finite indexed branches to addresses. -/
noncomputable def ofFnBranchEquiv {n : ℕ} (f : Fin n → OrderedTree) :
    Option (Σ i : Fin n, {p // p ∈ (f i).addresses}) ≃
      {p // p ∈ (OrderedTree.node (List.ofFn f)).addresses} :=
  Equiv.ofBijective (ofFnBranchAddress f) (ofFnBranchAddress_bijective f)

end GraphMinor.Kruskal.OrderedTree
