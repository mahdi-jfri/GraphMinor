module

public import GraphMinor.Compute.GM02BoundaryInput
public import GraphMinor.Compute.GM02CompactTermination
public import GraphMinor.Compute.GM02TerminalVertices
public import GraphMinor.Compute.GM02PullbackBits

/-!
# The actual numbered boundary instance of a recursive call

Retain the original terminal support and the intersection of the side
vertex sets. Restrict the original termination to those surviving
vertices, number it by compact ranks, and pull back both side subsets.
These are exactly the terminal pairs and side flags consumed by the
finite crossing-scheme catalogue. No scheme output is part of this data.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Classical GraphMinor.GM02

/-- Vertices outside the terminal-support union separator. -/
def gm02BoundaryDeletedSet (x : GM02SimpleTerminatedInput) (L R : Finset (Fin x.n)) :
    Finset (Fin x.n) := ((gm02TerminalVertices x.A).toFinset ∪ (L ∩ R))ᶜ

/-- Every prescribed endpoint survives boundary deletion. -/
theorem gm02Boundary_support_survives (x : GM02SimpleTerminatedInput) (L R : Finset (Fin x.n)) :
    x.A.support ⊆ {v | v ∉ gm02BoundaryDeletedSet x L R} := by
  intro v hv
  have hvQ : v ∈ (gm02TerminalVertices x.A).toFinset := by
    change v ∈ ((gm02TerminalVertices x.A).toFinset : Set (Fin x.n))
    rw [gm02TerminalVertices_toFinset]
    exact hv
  simp only [gm02BoundaryDeletedSet, Finset.mem_compl, not_not, Set.mem_ofPred_eq]
  exact Finset.mem_union_left _ hvQ

/-- Every separator vertex survives the boundary deletion determined by
its two vertex-side arrays. -/
theorem gm02Boundary_separator_survives {β : Type*} (x : GM02SimpleTerminatedInput)
    (L R : Finset (Fin x.n)) (H H' : Graph (Fin x.n) β)
    (hHL : V(H) = (L : Set (Fin x.n))) (hHR : V(H') = (R : Set (Fin x.n))) :
    V(H) ∩ V(H') ⊆ {v | v ∉ gm02BoundaryDeletedSet x L R} := by
  intro v hv
  change v ∉ gm02BoundaryDeletedSet x L R
  simp only [gm02BoundaryDeletedSet, Finset.mem_compl, not_not]
  apply Finset.mem_union_right
  apply Finset.mem_inter.2
  constructor
  · change v ∈ (L : Set (Fin x.n))
    rw [← hHL]
    exact hv.1
  · change v ∈ (R : Set (Fin x.n))
    rw [← hHR]
    exact hv.2

/-- The plain boundary instance obtained from the actual parent data. -/
noncomputable def gm02CompressedBoundaryInput (x : GM02SimpleTerminatedInput)
    (L R : Finset (Fin x.n)) : GM02BoundaryInput where
  n := (gm02BoundaryDeletedSet x L R)ᶜ.card
  A := gm02CompactTermination (gm02BoundaryDeletedSet x L R)
    (x.A.rebase (gm02Boundary_support_survives x L R))
  left := gm02PullbackVertexSet (compactEmb (gm02BoundaryDeletedSet x L R)) L
  right := gm02PullbackVertexSet (compactEmb (gm02BoundaryDeletedSet x L R)) R

/-- The boundary vertex count is exactly the support union separator size. -/
theorem gm02CompressedBoundaryInput_size (x : GM02SimpleTerminatedInput) (L R : Finset (Fin x.n)) :
    (gm02CompressedBoundaryInput x L R).n = ((gm02TerminalVertices x.A).toFinset ∪ (L ∩ R)).card := by
  simp only [gm02CompressedBoundaryInput, gm02BoundaryDeletedSet, compl_compl]

/-- The original terminal index is preserved in the boundary input. -/
theorem gm02CompressedBoundaryInput_index (x : GM02SimpleTerminatedInput) (L R : Finset (Fin x.n)) :
    (gm02CompressedBoundaryInput x L R).A.index = x.A.index := by
  simp only [gm02CompressedBoundaryInput, gm02CompactTermination_index, Termination.rebase_index]

/-- Boundary compression never increases the number of vertices. -/
theorem gm02CompressedBoundaryInput_size_le (x : GM02SimpleTerminatedInput) (L R : Finset (Fin x.n)) :
    (gm02CompressedBoundaryInput x L R).n ≤ x.n := by
  rw [gm02CompressedBoundaryInput_size]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_univ ((gm02TerminalVertices x.A).toFinset ∪ (L ∩ R))

/-- Under the recursive index and separator bounds, the catalogue input
has at most seven times the fixed internal width parameter vertices. -/
theorem gm02CompressedBoundaryInput_size_bound (x : GM02SimpleTerminatedInput)
    (L R : Finset (Fin x.n)) {w : ℕ} (hindex : x.A.index ≤ 3 * w) (hsep : (L ∩ R).card ≤ w) :
    (gm02CompressedBoundaryInput x L R).n ≤ 7 * w := by
  have hQ : (gm02TerminalVertices x.A).toFinset.card = 2 * x.A.index := by
    have hc := congrArg Set.ncard (gm02TerminalVertices_toFinset x.A)
    simpa only [Set.ncard_coe_finset, x.A.support_ncard] using hc
  rw [gm02CompressedBoundaryInput_size]
  have hu := Finset.card_union_le (gm02TerminalVertices x.A).toFinset (L ∩ R)
  omega

end GraphMinor.Compute
