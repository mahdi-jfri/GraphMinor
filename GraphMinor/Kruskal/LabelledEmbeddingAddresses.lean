module

public import GraphMinor.Kruskal.LabelledAddressEmbedding

/-!
# Recursive labelled embeddings give labelled address maps

Match branch indices at a root, or descend into a single branch. Carrying
these choices through the recursive embedding relation gives one injective
address map which both preserves common ancestors and compares the labels
at all source vertices.
-/

@[expose] public section

namespace GraphMinor.Kruskal.LabelledTree

variable {L : Type*} {r : L → L → Prop}

namespace BranchAddressEmbedding

/-- There are no branches to map from the empty list. -/
def nil (us : List (LabelledTree L)) : BranchAddressEmbedding r [] us where
  indices := ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
  branches := fun i ↦ Fin.elim0 i

/-- Match the first branch, then use the matching for the remaining branches. -/
def cons {s t : LabelledTree L} {ts us : List (LabelledTree L)}
    (φ : AddressEmbedding r s t) (ψ : BranchAddressEmbedding r ts us) :
    BranchAddressEmbedding r (s :: ts) (t :: us) where
  indices := {
    toFun := Fin.cases 0 (fun i ↦ (ψ.indices i).succ)
    inj' := by
      intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j =>
          have h : 0 = (ψ.indices j).val + 1 := congrArg Fin.val hij
          omega
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          have h : (ψ.indices i).val + 1 = 0 := congrArg Fin.val hij
          omega
        | succ j =>
          have h : (ψ.indices i).val + 1 = (ψ.indices j).val + 1 := congrArg Fin.val hij
          exact congrArg Fin.succ (ψ.indices.injective (Fin.ext (Nat.add_right_cancel h))) }
  branches := Fin.cases φ (fun i ↦ ψ.branches i)

/-- Skip an unmatched target branch. -/
def skip {t : LabelledTree L} {ts us : List (LabelledTree L)}
    (ψ : BranchAddressEmbedding r ts us) : BranchAddressEmbedding r ts (t :: us) where
  indices := ψ.indices.trans ⟨Fin.succ, Fin.succ_injective _⟩
  branches := fun i ↦ ψ.branches i

end BranchAddressEmbedding

/-- An embedding into one branch gives an embedding into the whole target,
with unchanged source labels and a prefixed target address. -/
def AddressEmbedding.dive {s : LabelledTree L} {a : L} {ts : List (LabelledTree L)}
    (i : Fin ts.length) (φ : AddressEmbedding r s ts[i]) :
    AddressEmbedding r s (.node a ts) := by
  let i' : Fin (ts.map shape).length := ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
  let φ' : OrderedTree.AddressEmbedding s.shape (ts.map shape)[i'] :=
    φ.underlying.changeTrees rfl (by simp only [Fin.getElem_fin, List.getElem_map]; rfl)
  let ψ := (OrderedTree.AddressEmbedding.dive i' φ').changeTrees rfl
    (shape_node a ts).symm
  refine ⟨ψ, ?_⟩
  intro p
  change r (s.labelAt p.val) ((node a ts).labelAt (i.val :: (φ.underlying.vertices p).val))
  rw [labelAt_cons]
  exact φ.labels p

/-- Every recursive labelled tree embedding has an address embedding which
retains the comparisons of labels at every mapped vertex. -/
theorem Embeds.exists_labelledAddressEmbedding {s t : LabelledTree L}
    (h : Embeds r s t) : Nonempty (AddressEmbedding r s t) := by
  refine Embeds.rec
    (motive_1 := fun s t _ ↦ Nonempty (AddressEmbedding r s t))
    (motive_2 := fun ts us _ ↦ Nonempty (BranchAddressEmbedding r ts us))
    (root := ?_) (dive := ?_) (nil := ?_) (cons := ?_) (cons_right := ?_) h
  · intro a b ts us hab _ ih
    obtain ⟨ψ⟩ := ih
    exact ⟨AddressEmbedding.root hab ψ⟩
  · intro s t a ts ht _ ih
    obtain ⟨φ⟩ := ih
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
    exact ⟨AddressEmbedding.dive ⟨i, hi⟩ φ⟩
  · intro us
    exact ⟨BranchAddressEmbedding.nil us⟩
  · intro s t ts us _ _ ihst ihsub
    obtain ⟨φ⟩ := ihst
    obtain ⟨ψ⟩ := ihsub
    exact ⟨BranchAddressEmbedding.cons φ ψ⟩
  · intro t ts us _ ih
    obtain ⟨ψ⟩ := ih
    exact ⟨BranchAddressEmbedding.skip ψ⟩

/-- A recursive matching of branch lists gives explicit branch indices
and labelled address maps in every matched pair. -/
theorem exists_branchAddressEmbedding {ts us : List (LabelledTree L)}
    (h : List.SublistForall₂ (Embeds r) ts us) :
    Nonempty (BranchAddressEmbedding r ts us) := by
  induction h with
  | nil => exact ⟨BranchAddressEmbedding.nil _⟩
  | cons h _ ih =>
    obtain ⟨φ⟩ := h.exists_labelledAddressEmbedding
    obtain ⟨ψ⟩ := ih
    exact ⟨BranchAddressEmbedding.cons φ ψ⟩
  | cons_right _ ih =>
    obtain ⟨ψ⟩ := ih
    exact ⟨BranchAddressEmbedding.skip ψ⟩

end GraphMinor.Kruskal.LabelledTree
