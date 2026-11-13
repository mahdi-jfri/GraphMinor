module

public import GraphMinor.Kruskal.LabelledShape
public import GraphMinor.Kruskal.AddressRootEquations

/-!
# Address embeddings preserving vertex labels

The recursive labelled tree relation supplies an injective address map.
The map preserves common ancestors, and each source label is below the
label at its image. These two properties retain both the edge paths and
the attachment multiplicities needed when the trees represent forests.
-/

@[expose] public section

namespace GraphMinor.Kruskal.LabelledTree

open OrderedTree

variable {L : Type*} {r : L → L → Prop}

/-- A tree address embedding with a comparison of labels at every vertex. -/
structure AddressEmbedding (r : L → L → Prop) (s t : LabelledTree L) where
  underlying : OrderedTree.AddressEmbedding s.shape t.shape
  labels : ∀ p, r (s.labelAt p.val) (t.labelAt (underlying.vertices p).val)

/-- Branches are matched injectively and each matched pair has a labelled
address embedding. -/
structure BranchAddressEmbedding (r : L → L → Prop)
    (ts us : List (LabelledTree L)) where
  indices : Fin ts.length ↪ Fin us.length
  branches : ∀ i, AddressEmbedding r ts[i] us[indices i]

namespace BranchAddressEmbedding

/-- The branch matching after forgetting labels. -/
def shapeIndices {ts us : List (LabelledTree L)} (φ : BranchAddressEmbedding r ts us) :
    Fin (ts.map shape).length ↪ Fin (us.map shape).length where
  toFun i := ⟨(φ.indices ⟨i.val, by simpa only [List.length_map] using i.isLt⟩).val,
    by simpa only [List.length_map] using
      (φ.indices ⟨i.val, by simpa only [List.length_map] using i.isLt⟩).isLt⟩
  inj' := by
    intro i j hij
    have he : φ.indices ⟨i.val, by simpa only [List.length_map] using i.isLt⟩ =
        φ.indices ⟨j.val, by simpa only [List.length_map] using j.isLt⟩ :=
      Fin.ext (congrArg (fun z : Fin (us.map shape).length ↦ z.val) hij)
    have hi := φ.indices.injective he
    exact Fin.ext (congrArg (fun z : Fin ts.length ↦ z.val) hi)

/-- The underlying address embedding in a matched branch. -/
def shapeBranches {ts us : List (LabelledTree L)} (φ : BranchAddressEmbedding r ts us)
    (i : Fin (ts.map shape).length) :
    OrderedTree.AddressEmbedding (ts.map shape)[i] (us.map shape)[φ.shapeIndices i] :=
  (φ.branches ⟨i.val, by simpa only [List.length_map] using i.isLt⟩).underlying.changeTrees
    (by simp only [Fin.getElem_fin, List.getElem_map])
    (by simp only [Fin.getElem_fin, List.getElem_map]; rfl)

end BranchAddressEmbedding

/-- Matching the root labels and matching branches gives a labelled
embedding of the whole trees. -/
noncomputable def AddressEmbedding.root {a b : L} {ts us : List (LabelledTree L)}
    (hab : r a b) (φ : BranchAddressEmbedding r ts us) :
    AddressEmbedding r (.node a ts) (.node b us) := by
  let ψ := OrderedTree.AddressEmbedding.rootWithEquations φ.shapeIndices φ.shapeBranches
  let hψ := ψ.changeTrees (shape_node a ts).symm (shape_node b us).symm
  refine ⟨hψ, ?_⟩
  intro p
  cases hp : p.val with
  | nil =>
    have heq : (hψ.vertices p).val = [] := by
      change (ψ.vertices ⟨p.val, _⟩).val = []
      have hp' : (⟨p.val, by simpa only [shape_node] using p.property⟩ :
          {p // p ∈ (OrderedTree.node (ts.map shape)).addresses}) =
          ⟨[], nil_mem_addresses _⟩ := Subtype.ext hp
      rw [hp']
      exact OrderedTree.AddressEmbedding.rootWithEquations_nil
        φ.shapeIndices φ.shapeBranches
    simpa only [hp, heq, labelAt_nil] using hab
  | cons i q =>
    have hm : i :: q ∈ (OrderedTree.node (ts.map shape)).addresses := by
      simpa only [shape_node, hp] using p.property
    obtain ⟨j, hij, hq⟩ := (cons_mem_addresses_iff _ i q).mp hm
    subst i
    let j' : Fin ts.length := ⟨j.val, by simpa only [List.length_map] using j.isLt⟩
    let q' : {p // p ∈ (ts[j']).shape.addresses} :=
      ⟨q, by simpa only [Fin.getElem_fin, List.getElem_map] using hq⟩
    have heq : (hψ.vertices p).val =
        (φ.indices j').val :: ((φ.branches j').underlying.vertices q').val := by
      change (ψ.vertices ⟨p.val, _⟩).val = _
      have hp' : (⟨p.val, by simpa only [shape_node] using p.property⟩ :
          {p // p ∈ (OrderedTree.node (ts.map shape)).addresses}) =
          branchAddress (ts.map shape) (some ⟨j, ⟨q, hq⟩⟩) := Subtype.ext hp
      rw [hp']
      exact OrderedTree.AddressEmbedding.rootWithEquations_cons
        φ.shapeIndices φ.shapeBranches j ⟨q, hq⟩
    rw [heq]
    have hl := (φ.branches j').labels q'
    simpa only [hp, ← labelAt_cons a ts j' q,
      ← labelAt_cons b us (φ.indices j') _, j', q'] using hl

end GraphMinor.Kruskal.LabelledTree
