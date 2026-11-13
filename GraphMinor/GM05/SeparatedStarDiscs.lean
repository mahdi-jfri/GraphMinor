module

public import GraphMinor.Surface.Defs
public import GraphMinor.Surface.TopologyStatements
public import GraphMinor.GM07.StarDisc
import GraphMinor.GM07.SideDisc

/-!
# Vertex discs away from nonincident edges

For the neighbourhoods in GM V, (8.14), choose a star disc at each
vertex. The closed set to avoid consists of all other vertices and
the closures of edges not incident with this vertex. The finite star
disc selection theorem makes these discs pairwise disjoint.
-/

public section
namespace GraphMinor.GM05
open Set Surface

/-- Disjoint star discs can also avoid every nonincident edge closure.
These are the vertex neighbourhoods for GM V, (8.14), page 113. -/
theorem exists_separated_star_discs {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) (D : Drawing S) :
    ∃ R : S → Set S,
      (∀ v ∈ D.V, GM07.IsStarDisc D v (R v)) ∧
      (∀ v ∈ D.V, ∀ w ∈ D.V, w ≠ v → w ∉ R v) ∧
      (∀ v ∈ D.V, ∀ e ∈ D.E, v ∉ closure e → Disjoint (R v) (closure e)) ∧
      ∀ u ∈ D.V, ∀ v ∈ D.V, u ≠ v → Disjoint (R u) (R v) := by
  classical
  let : T2Space S := hS.2.1
  let P : S → Set S := fun v ↦ (D.V \ {v}) ∪ ⋃ e ∈ {e ∈ D.E | v ∉ closure e}, closure e
  have hP : ∀ v ∈ D.V, IsClosed (P v) := by
    intro v _
    apply (D.finite_V.subset sdiff_subset).isClosed.union
    exact (D.finite_edges.subset (fun _ he ↦ he.1)).isClosed_biUnion fun _ _ ↦ isClosed_closure
  have hvP : ∀ v ∈ D.V, v ∉ P v := by
    intro v _ hv
    rcases hv with hv | hv
    · exact hv.2 rfl
    · obtain ⟨e,he,hve⟩ := mem_iUnion₂.mp hv
      exact he.2 hve
  obtain ⟨R,hR,hdis⟩ := GM07.exists_star_family hS D subset_rfl hP hvP
  refine ⟨R,fun v hv ↦ (hR v hv).1,?_,?_,hdis⟩
  · intro v hv w hw hwv hwR
    exact disjoint_left.mp (hR v hv).2 hwR (.inl ⟨hw,hwv⟩)
  · intro v hv e he hve
    exact (hR v hv).2.mono_right (fun x hx ↦ .inr (mem_iUnion₂.mpr ⟨e,⟨he,hve⟩,hx⟩))

end GraphMinor.GM05
