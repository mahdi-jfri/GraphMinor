module

public import GraphMinor.Kruskal.RootedGraph
public import GraphMinor.Kruskal.RootedBranches
public import GraphMinor.Kruskal.OfFnAddresses
import Mathlib.Logic.Equiv.Option
import Mathlib.Data.Fintype.EquivFin

/-!
# Representing finite rooted trees by ordered trees

Split a rooted tree into its root and the branches at its children. Recursively
represent each smaller branch by an ordered tree and list those trees in any
order. The vertex equivalence is the branch partition on one side and the
address partition on the other. It preserves roots and parents, so it also
gives an isomorphism of the underlying undirected graphs.
-/

public section

namespace GraphMinor.Kruskal

open GraphMinor.GM04 OrderedTree

private noncomputable abbrev branchTree {ι : Type*} (T : RootedTree ι)
    (c : {v // v ∈ T.children T.root}) : RootedTree ι :=
  T.subtree c.val ((mem_children_iff T T.root c.val).1 c.property).2.1

private noncomputable def assemblyBranches {ι : Type*} (T : RootedTree ι) {n : ℕ}
    (c : Fin n ≃ {v // v ∈ T.children T.root}) (f : Fin n → OrderedTree)
    (φ : ∀ i, RootedTreeIso (f i).toRootedTree (branchTree T (c i))) :
    (Σ i : Fin n, {p // p ∈ (f i).addresses}) ≃
      (Σ d : {v // v ∈ T.children T.root}, {v // v ∈ T.subtreeAt d.val}) :=
  Equiv.sigmaCongr c (fun i ↦ (φ i).vertices)

private noncomputable def assemblyVertices {ι : Type*} (T : RootedTree ι) {n : ℕ}
    (c : Fin n ≃ {v // v ∈ T.children T.root}) (f : Fin n → OrderedTree)
    (φ : ∀ i, RootedTreeIso (f i).toRootedTree (branchTree T (c i))) :
    {p // p ∈ (OrderedTree.node (List.ofFn f)).addresses} ≃ {v // v ∈ T.verts} :=
  (ofFnBranchEquiv f).symm.trans
    ((Equiv.optionCongr (assemblyBranches T c f φ)).trans (rootBranchEquiv T))

private theorem assemblyVertices_apply {ι : Type*} (T : RootedTree ι) {n : ℕ}
    (c : Fin n ≃ {v // v ∈ T.children T.root}) (f : Fin n → OrderedTree)
    (φ : ∀ i, RootedTreeIso (f i).toRootedTree (branchTree T (c i)))
    (x : Option (Σ i : Fin n, {p // p ∈ (f i).addresses})) :
    assemblyVertices T c f φ (ofFnBranchEquiv f x) =
      rootBranchEquiv T (Equiv.optionCongr (assemblyBranches T c f φ) x) := by
  simp only [assemblyVertices, Equiv.trans_apply, Equiv.symm_apply_apply]

private theorem assemblyVertices_none {ι : Type*} (T : RootedTree ι) {n : ℕ}
    (c : Fin n ≃ {v // v ∈ T.children T.root}) (f : Fin n → OrderedTree)
    (φ : ∀ i, RootedTreeIso (f i).toRootedTree (branchTree T (c i))) :
    (assemblyVertices T c f φ (ofFnBranchAddress f none)).val = T.root := by
  change (assemblyVertices T c f φ (ofFnBranchEquiv f none)).val = T.root
  rw [assemblyVertices_apply, rootBranchEquiv_apply]
  rfl

private theorem assemblyVertices_some {ι : Type*} (T : RootedTree ι) {n : ℕ}
    (c : Fin n ≃ {v // v ∈ T.children T.root}) (f : Fin n → OrderedTree)
    (φ : ∀ i, RootedTreeIso (f i).toRootedTree (branchTree T (c i)))
    (i : Fin n) (p : {p // p ∈ (f i).addresses}) :
    (assemblyVertices T c f φ (ofFnBranchAddress f (some ⟨i, p⟩))).val =
      ((φ i).vertices p).val := by
  change (assemblyVertices T c f φ (ofFnBranchEquiv f (some ⟨i, p⟩))).val = _
  rw [assemblyVertices_apply, rootBranchEquiv_apply]
  rfl

private noncomputable def assembleRootedIso {ι : Type*} (T : RootedTree ι) {n : ℕ}
    (c : Fin n ≃ {v // v ∈ T.children T.root}) (f : Fin n → OrderedTree)
    (φ : ∀ i, RootedTreeIso (f i).toRootedTree (branchTree T (c i))) :
    RootedTreeIso (OrderedTree.node (List.ofFn f)).toRootedTree T where
  vertices := assemblyVertices T c f φ
  root_eq := assemblyVertices_none T c f φ
  parent_eq p := by
    obtain ⟨x, rfl⟩ := (ofFnBranchAddress_bijective f).2 p
    cases x with
    | none =>
      change (assemblyVertices T c f φ (ofFnBranchAddress f none)).val =
        T.parent (assemblyVertices T c f φ (ofFnBranchAddress f none)).val
      rw [assemblyVertices_none, T.parent_root]
    | some x =>
      obtain ⟨i, p⟩ := x
      by_cases hp : p.val = []
      · have hpr : p = ⟨[], nil_mem_addresses (f i)⟩ := Subtype.ext hp
        subst p
        change (assemblyVertices T c f φ (ofFnBranchAddress f none)).val =
          T.parent (assemblyVertices T c f φ
            (ofFnBranchAddress f (some ⟨i, ⟨[], nil_mem_addresses (f i)⟩⟩))).val
        rw [assemblyVertices_none, assemblyVertices_some, (φ i).root_eq]
        exact ((mem_children_iff T T.root (c i).val).1 (c i).property).2.2.symm
      · let pp : {p // p ∈ (f i).addresses} :=
          ⟨p.val.dropLast, dropLast_mem_addresses (f i) p.val p.property⟩
        have hdrop : (i.val :: p.val).dropLast = i.val :: p.val.dropLast :=
          List.dropLast_cons_of_ne_nil hp
        change (assemblyVertices T c f φ
          ⟨(i.val :: p.val).dropLast, _⟩).val =
          T.parent (assemblyVertices T c f φ (ofFnBranchAddress f (some ⟨i, p⟩))).val
        have haddr : (⟨(i.val :: p.val).dropLast,
            dropLast_mem_addresses _ _ (ofFnBranchAddress f (some ⟨i, p⟩)).property⟩ :
            {p // p ∈ (OrderedTree.node (List.ofFn f)).addresses}) =
            ofFnBranchAddress f (some ⟨i, pp⟩) := Subtype.ext hdrop
        rw [haddr, assemblyVertices_some, assemblyVertices_some]
        have hpar := (φ i).parent_eq p
        have hne := ((φ i).ne_root_iff p).2 hp
        exact hpar.trans (T.subtree_parent_of_ne (c i).val
          ((mem_children_iff T T.root (c i).val).1 (c i).property).2.1 hne)

/-- Every finite rooted tree has an ordered-tree representation preserving
the root and every parent. The recursion uses strictly smaller root branches,
not an assumed tree embedding or a graph containment statement. -/
theorem exists_orderedTree_iso {ι : Type*} (T : RootedTree ι) :
    ∃ t : OrderedTree, Nonempty (RootedTreeIso t.toRootedTree T) := by
  classical
  induction hn : T.verts.card using Nat.strong_induction_on generalizing T with
  | _ n ih =>
    let C := {v // v ∈ T.children T.root}
    let k := Fintype.card C
    let c : Fin k ≃ C := (Fintype.equivFin C).symm
    have hbranches : ∀ i : Fin k, ∃ t : OrderedTree,
        Nonempty (RootedTreeIso t.toRootedTree (branchTree T (c i))) := by
      intro i
      have hlt : (branchTree T (c i)).verts.card < n := by
        simpa only [RootedTree.subtree_verts, ← hn] using
          root_branch_card_lt T (c i).property
      exact ih _ hlt (branchTree T (c i)) rfl
    choose f hφ using hbranches
    let φ := fun i ↦ Classical.choice (hφ i)
    exact ⟨OrderedTree.node (List.ofFn f), ⟨assembleRootedIso T c f φ⟩⟩

end GraphMinor.Kruskal
