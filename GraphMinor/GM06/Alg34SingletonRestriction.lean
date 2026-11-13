module

public import GraphMinor.GM06.Alg34InducedRep
public import GraphMinor.Compute.GM06Alg34SingletonData

/-!
# The induced division in a singleton reduction

Deleting a singleton block's vertex removes that block entirely.
Disjointness keeps every other division block away from the removed
vertex, so every other block is unchanged. The computed vertex image
and restricted division are therefore exactly the two set differences
used in (3.3)(i).
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {x : GM06DrawingData} {S : Type u} [TopologicalSpace S] [T1Space S]
  {G : Drawing S} {Δ : Set (Set S)}

/-- The finite singleton-survivor list denotes exactly vertex deletion
in the represented drawing. -/
theorem singleton_vertexImage (h : GM06DrawingRep x G Δ) (v : Fin x.n) :
    h.vertexImage (x.singletonSurvivors v) = G.V \ {(h.vertex v).val} := by
  ext p
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwv := (x.mem_singletonSurvivors_iff v w).mp hw
    refine ⟨(h.vertex w).property, ?_⟩
    intro heq
    exact hwv (h.vertex.injective (Subtype.ext heq))
  · rintro ⟨hpV, hpv⟩
    obtain ⟨w, hw⟩ := h.vertex.surjective ⟨p, hpV⟩
    have hwp : (h.vertex w).val = p := congrArg Subtype.val hw
    have hwv : w ≠ v := by
      intro heq
      exact hpv ((congrArg (fun w => (h.vertex w).val) heq).symm.trans hwp).symm
    exact ⟨w, (x.mem_singletonSurvivors_iff v w).mpr hwv, hwp⟩

/-- Every other division block is contained in the surviving vertices,
using disjointness from the singleton block. -/
theorem singleton_other_block_subset (h : GM06DrawingRep x G Δ) (v : Fin x.n)
    (hD : IsDivision Δ) (hsub : divisionUnion Δ ⊆ G.V) (hv : {(h.vertex v).val} ∈ Δ)
    {δ : Set S} (hδ : δ ∈ Δ) (hne : δ ≠ {(h.vertex v).val}) :
    δ ⊆ h.vertexImage (x.singletonSurvivors v) := by
  rw [h.singleton_vertexImage v]
  intro p hp
  refine ⟨hsub ⟨δ, hδ, hp⟩, ?_⟩
  exact fun hpv => Set.disjoint_left.mp (hD.2.2 hδ hv hne) hp hpv

/-- The computed restricted division is exactly the old division with
the selected singleton block removed, as in Graph Minors VI (3.3)(i). -/
theorem singleton_inducedDivision (h : GM06DrawingRep x G Δ) (v : Fin x.n)
    (hD : IsDivision Δ) (hsub : divisionUnion Δ ⊆ G.V) (hv : {(h.vertex v).val} ∈ Δ) :
    h.inducedDivision (x.singletonSurvivors v) = Δ \ {{(h.vertex v).val}} := by
  apply Set.Subset.antisymm
  · rintro A ⟨δ, ⟨hδ, hnonempty⟩, rfl⟩
    have hne : δ ≠ {(h.vertex v).val} := by
      intro heq
      obtain ⟨p, hpδ, hpV⟩ := hnonempty
      rw [heq] at hpδ
      have hnot := (h.singleton_vertexImage v).subset hpV
      exact hnot.2 hpδ
    have heq : δ ∩ h.vertexImage (x.singletonSurvivors v) = δ :=
      inter_eq_left.mpr (h.singleton_other_block_subset v hD hsub hv hδ hne)
    change δ ∩ h.vertexImage (x.singletonSurvivors v) ∈ Δ \ {{(h.vertex v).val}}
    rw [heq]
    exact ⟨hδ, hne⟩
  · rintro δ ⟨hδ, hne⟩
    have heq : δ ∩ h.vertexImage (x.singletonSurvivors v) = δ :=
      inter_eq_left.mpr (h.singleton_other_block_subset v hD hsub hv hδ hne)
    refine ⟨δ, ⟨hδ, ?_⟩, heq⟩
    exact heq.symm ▸ hD.2.1 δ hδ

/-- The singleton payload represents precisely the drawing and division
obtained by the deletion in Graph Minors VI (3.3)(i). -/
theorem singletonData_rep (h : GM06DrawingRep x G Δ) (v : Fin x.n)
    (hD : IsDivision Δ) (hsub : divisionUnion Δ ⊆ G.V) (hv : {(h.vertex v).val} ∈ Δ) :
    Nonempty (GM06DrawingRep (x.singletonData v)
      (induceDrawing G (G.V \ {(h.vertex v).val})) (Δ \ {{(h.vertex v).val}})) := by
  have hr := h.inducedData_rep (x.singletonSurvivors v)
  rw [h.singleton_vertexImage v, h.singleton_inducedDivision v hD hsub hv] at hr
  exact hr

end GraphMinor.Compute.GM06DrawingRep
