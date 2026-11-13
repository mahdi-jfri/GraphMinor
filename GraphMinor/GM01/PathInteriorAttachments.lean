module

public import GraphMinor.GM01.BlockAttachmentRegions
import GraphMinor.GM16.PathEndSubpath

/-!
# Attachment paths inside a separator witness

In the proof of Graph Minors I, (4.3), page 56, a witness path has no
internal vertex in its two endpoint sets. A subpath whose ends avoid
both sets therefore avoids them entirely: an original end cannot be
internal to a subpath. Joining a vertex outside the block union to an
interior block in this way places it in an attachment region.
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- A subpath whose ends avoid the two endpoint sets of a trimmed path
avoids both sets entirely. This supplies the omitted end check when
choosing the subpath in GM01 (4.3), page 56. -/
theorem disjoint_subpath_endpoint_sets {α β : Type*}
    {G P Q : Graph α β} {A B : Set α} {a b x u : α}
    (hP : IsFromToPathWithEnds G P A B a b)
    (hQ : IsGraphPathWithEnds G Q x u) (hQP : Q ≤ P)
    (hx : x ∉ A ∪ B) (hu : u ∉ A ∪ B) : Disjoint V(Q) (A ∪ B) := by
  apply Set.disjoint_left.mpr
  intro y hy hyAB
  have hyEnd : y = a ∨ y = b := by
    rcases hyAB with hyA | hyB
    · exact Or.inl (mem_singleton_iff.mp (hP.2.1 ▸ ⟨hQP.vertexSet_mono hy, hyA⟩))
    · exact Or.inr (mem_singleton_iff.mp (hP.2.2 ▸ ⟨hQP.vertexSet_mono hy, hyB⟩))
  have hyOwn : y = x ∨ y = u := by
    rcases hyEnd with rfl | rfl
    · exact GraphMinor.GM16.path_start_mem_subpath_is_end hP.1 hQ hQP hy
    · exact GraphMinor.GM16.path_start_mem_subpath_is_end hP.1.symm hQ hQP hy
  rcases hyOwn with rfl | rfl
  · exact hx hyAB
  · exact hu hyAB

/-- The outside-block case of the subpath argument in GM01 (4.3),
page 56. The block union outside the interior blocks lies in the two
endpoint sets, so a subpath avoiding those sets is an attachment path. -/
theorem mem_blockAttachmentRegion_of_witness_subpath {α β : Type*}
    {G P : Graph α β} {U D A B : Set α} {a b x u : α}
    (hP : IsFromToPathWithEnds G P A B a b)
    (hxP : x ∈ V(P)) (huP : u ∈ V(P)) (hxU : x ∉ U)
    (hAU : A ⊆ U) (hBU : B ⊆ U) (huD : u ∈ D)
    (hD : Disjoint D (A ∪ B)) (hcover : U ⊆ A ∪ D ∪ B) :
    x ∈ blockAttachmentRegion G U D := by
  obtain ⟨Q, hQP, _, hQ⟩ := hP.1.exists_subpath hxP huP
  have hxAB : x ∉ A ∪ B := by
    rintro (h | h)
    · exact hxU (hAU h)
    · exact hxU (hBU h)
  have huAB : u ∉ A ∪ B := fun h ↦ Set.disjoint_left.mp hD huD h
  have hAvoid := disjoint_subpath_endpoint_sets hP hQ hQP hxAB huAB
  have hAvoidD : Disjoint V(Q) (U \ D) := by
    apply Set.disjoint_left.mpr
    intro y hy hyUD
    rcases hcover hyUD.1 with (hyA | hyD) | hyB
    · exact Set.disjoint_left.mp hAvoid hy (Or.inl hyA)
    · exact hyUD.2 hyD
    · exact Set.disjoint_left.mp hAvoid hy (Or.inr hyB)
  exact path_subset_blockAttachmentRegion hQ huD hAvoidD hQ.left_mem

end GraphMinor.GM01
