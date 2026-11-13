module

public import GraphMinor.GM04.TreeLemma.Basic
import Mathlib.Data.Finset.Dedup

/-!
# Splitting a rooted tree into branches

Graph Minors IV, Section 2, page 230 directs edges away from the root. Every
other vertex therefore lies in exactly one branch rooted at a child of the
root. We prove this directly from the parent iterates, and prove that each
branch has fewer vertices. These facts support recursion over finite trees.
-/

public section

namespace GraphMinor.Kruskal

open GraphMinor.GM04

/-- Membership in the list of children has the meaning given by the
rooted-tree definition: a non-root vertex with the specified parent. -/
theorem mem_children_iff {ι : Type*} (T : RootedTree ι) (v c : ι) :
    c ∈ T.children v ↔ c ≠ T.root ∧ c ∈ T.verts ∧ T.parent c = v := by
  classical
  simp only [RootedTree.children, Finset.mem_filter, T.mem_edges, and_assoc]

/-- A branch at a child of the root has strictly fewer vertices than the
whole tree. -/
theorem root_branch_card_lt {ι : Type*} (T : RootedTree ι) {c : ι}
    (hc : c ∈ T.children T.root) : (T.subtreeAt c).card < T.verts.card := by
  obtain ⟨hne, hmem, _⟩ := (mem_children_iff T T.root c).1 hc
  simpa only [T.subtreeAt_root] using
    T.subtreeAt_card_lt_of_reaches_of_ne (T.root_reaches hmem) hne.symm

/-- Every non-root vertex is reached by a child of the root. Take the last
vertex before the root in a shortest sequence of parent steps. -/
theorem exists_root_child_reaches {ι : Type*} (T : RootedTree ι) {v : ι}
    (hv : v ∈ T.verts) (hne : v ≠ T.root) :
    ∃ c ∈ T.children T.root, T.Reaches c v := by
  classical
  have hex := T.exists_iterate_eq_root v hv
  have hpos : 0 < Nat.find hex := by
    by_contra hn
    have hzero : Nat.find hex = 0 := Nat.eq_zero_of_not_pos hn
    exact hne (by simpa only [hzero, Function.iterate_zero_apply] using Nat.find_spec hex)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  let c := T.parent^[k] v
  have hc : c ∈ T.verts := T.iterate_parent_mem hv k
  have hcn : c ≠ T.root := by
    intro hcr
    exact Nat.find_min hex (by omega : k < Nat.find hex) hcr
  have hpc : T.parent c = T.root := by
    have hs := Nat.find_spec hex
    rw [hk, Function.iterate_succ_apply'] at hs
    exact hs
  exact ⟨c, (mem_children_iff T T.root c).2 ⟨hcn, hc, hpc⟩, hv, k, rfl⟩

/-- Distinct children of the root have disjoint sets of descendants.
Ancestors of a vertex form a chain, and no root child lies strictly above
another root child. -/
theorem root_child_eq_of_reaches {ι : Type*} (T : RootedTree ι) {c d v : ι}
    (hc : c ∈ T.children T.root) (hd : d ∈ T.children T.root)
    (hcv : T.Reaches c v) (hdv : T.Reaches d v) : c = d := by
  obtain ⟨hcn, _, hpc⟩ := (mem_children_iff T T.root c).1 hc
  obtain ⟨hdn, _, hpd⟩ := (mem_children_iff T T.root d).1 hd
  rcases hcv.total_of_reaches T hdv with hcd | hdc
  · rcases hcd.eq_or_reaches_parent T with h | h
    · exact h
    · rw [hpd] at h
      exact (hcn (T.reaches_root_iff.1 h)).elim
  · rcases hdc.eq_or_reaches_parent T with h | h
    · exact h.symm
    · rw [hpc] at h
      exact (hdn (T.reaches_root_iff.1 h)).elim

/-- The root is outside every branch at one of its children. -/
theorem root_not_mem_root_branch {ι : Type*} (T : RootedTree ι) {c : ι}
    (hc : c ∈ T.children T.root) : T.root ∉ T.subtreeAt c := by
  intro hroot
  have hne := ((mem_children_iff T T.root c).1 hc).1
  exact hne (T.reaches_root_iff.1 (T.mem_subtreeAt.1 hroot))

/-- Read the root or a vertex in one of its branches as a vertex of the
whole rooted tree. The branch index is the child at its root. -/
@[expose] def rootBranchVertex {ι : Type*} (T : RootedTree ι) :
    Option (Σ c : {c // c ∈ T.children T.root}, {v // v ∈ T.subtreeAt c.val}) →
      {v // v ∈ T.verts}
  | none => ⟨T.root, T.root_mem⟩
  | some ⟨c, v⟩ => ⟨v.val, T.subtreeAt_subset_verts c.val v.property⟩

/-- The root and the branches partition the actual vertex set. -/
theorem rootBranchVertex_bijective {ι : Type*} (T : RootedTree ι) :
    Function.Bijective (rootBranchVertex T) := by
  constructor
  · intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y =>
        obtain ⟨c, v⟩ := y
        have hv : T.root = v.val := congrArg Subtype.val hxy
        have hmem := v.property
        rw [← hv] at hmem
        exact (root_not_mem_root_branch T c.property hmem).elim
    | some x =>
      obtain ⟨c, v⟩ := x
      cases y with
      | none =>
        have hv : v.val = T.root := congrArg Subtype.val hxy
        have hmem := v.property
        rw [hv] at hmem
        exact (root_not_mem_root_branch T c.property hmem).elim
      | some y =>
        obtain ⟨d, w⟩ := y
        have hvw : v.val = w.val := congrArg Subtype.val hxy
        have hcd : c = d := Subtype.ext (root_child_eq_of_reaches T c.property d.property
          (T.mem_subtreeAt.1 v.property) (hvw.symm ▸ T.mem_subtreeAt.1 w.property))
        subst d
        have heq : v = w := Subtype.ext hvw
        subst w
        rfl
  · intro v
    by_cases hv : v.val = T.root
    · exact ⟨none, Subtype.ext hv.symm⟩
    · obtain ⟨c, hc, hcv⟩ := exists_root_child_reaches T v.property hv
      exact ⟨some ⟨⟨c, hc⟩, ⟨v.val, T.mem_subtreeAt.2 hcv⟩⟩, Subtype.ext rfl⟩

/-- The vertex equivalence induced by the branch partition. It sends `none`
to the root and a branch vertex to that same vertex in the whole tree. -/
noncomputable def rootBranchEquiv {ι : Type*} (T : RootedTree ι) :
    Option (Σ c : {c // c ∈ T.children T.root}, {v // v ∈ T.subtreeAt c.val}) ≃
      {v // v ∈ T.verts} :=
  Equiv.ofBijective (rootBranchVertex T) (rootBranchVertex_bijective T)

/-- The branch partition equivalence has the stated root-and-branch map. -/
theorem rootBranchEquiv_apply {ι : Type*} (T : RootedTree ι)
    (x : Option (Σ c : {c // c ∈ T.children T.root}, {v // v ∈ T.subtreeAt c.val})) :
    rootBranchEquiv T x = rootBranchVertex T x := by rfl

end GraphMinor.Kruskal
