module

public import GraphMinor.GM06.Alg34InteriorComponentCorrect
public import GraphMinor.Compute.GM06Alg34InteriorReduce
import GraphMinor.GM06.Alg34SingletonExhaustCorrect

/-!
# Feasibility under exhaustive interior-component deletion

Each selected finite component represents an actual component away from
the boundary. Apply (3.3)(ii) at each deletion. The division stays fixed,
and its boundary vertices survive, so the same argument applies again.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]

/-- Exhausting (3.3)(ii) preserves a represented drawing, its boundary
division, and the exact finite feasibility answer. -/
theorem reduceInteriorComponents_correct {x : GM06DrawingData} {G : Drawing S}
    {Δ : Set (Set S)} (h : GM06DrawingRep x G Δ) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ ⊆ G.V ∩ bd S) :
    ∃ G' : Drawing S,
      Nonempty (GM06DrawingRep (gm06ReduceInteriorComponents x) G' Δ) ∧
      divisionUnion Δ ⊆ G'.V ∩ bd S ∧
      (IsFeasible x.graph x.divisionSet ↔
        IsFeasible (gm06ReduceInteriorComponents x).graph
          (gm06ReduceInteriorComponents x).divisionSet) := by
  induction x using gm06ReduceInteriorComponents.induct generalizing G with
  | case1 x hnone =>
    rw [gm06ReduceInteriorComponents, hnone]
    exact ⟨G, ⟨h⟩, hbd, Iff.rfl⟩
  | case2 x a hfind ih =>
    have ha := gm06FindInteriorComponent_sound x a hfind
    obtain ⟨hnew⟩ := h.interiorComponentData_rep a ha hD hbd
    have hbd' : divisionUnion Δ ⊆ _ ∩ bd S :=
      fun p hp => ⟨hnew.divisionUnion_subset hp, (hbd hp).2⟩
    obtain ⟨G', hrep', hbd'', hfeas'⟩ := ih hnew hbd'
    rw [gm06ReduceInteriorComponents, hfind]
    exact ⟨G', hrep', hbd'',
      (h.interiorComponentData_feasible_iff a ha hD hbd).trans hfeas'⟩

end GraphMinor.Compute.GM06DrawingRep
