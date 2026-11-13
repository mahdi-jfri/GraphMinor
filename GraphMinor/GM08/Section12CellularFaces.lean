module

public import GraphMinor.GM08.Defs6to18
public import GraphMinor.GM11.Defs
import GraphMinor.GM08.Section9DiscContext
import GraphMinor.GM11.Walks
import GraphMinor.Surface.DiscGrow

/-!
# Empty petal interiors are regions

A closed disc whose boundary lies in a drawing and whose interior
misses the drawing has that interior as a region. Apply this to each
new loop petal. The old non-loop edges remain non-loops because the
vertex set did not change. Hence the replacement drawing is cellular,
as required before deriving the portraits in VIII, Section 12.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u v

/-- A closed disc in the disc ambient space is the inside disc of its
own boundary. This identifies the regions bounded by the new loops
in VIII, Section 12. -/
theorem isInsideDisc_of_closedDisc_univ {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDisc (univ : Set S)) {B : Set S} (hB : IsClosedDisc B) :
    IsInsideDisc univ (discBd B) B := by
  obtain ⟨E, hE, huniq⟩ := disc_oArc univ (discBd B) hS (subset_univ _) hB.isOArc_discBd
  exact (huniq B (subset_univ _) hB rfl).symm ▸ hE

/-- An empty disc interior bounded by drawing points is a region.
The connected component containing an interior point cannot cross the
boundary of the disc. This checks the new loop faces in Section 12. -/
theorem discInt_mem_regions {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDisc (univ : Set S)) (D : Drawing S)
    {B : Set S} (hB : IsClosedDisc B) (hbd : discBd B ⊆ D.U)
    (hdis : Disjoint (discInt B) D.U) : discInt B ∈ D.R := by
  have : T2Space S := (isSurface_of_closedDisc_univ hS).2.1
  have hman := (isSurface_of_closedDisc_univ hS).2.2
  obtain ⟨x, hx⟩ := hB.nonempty_discInt
  have hin : discInt B ⊆ univ \ D.U := fun y hy => ⟨mem_univ _, disjoint_left.mp hdis hy⟩
  have hxD := hin hx
  refine ⟨x, hxD, Subset.antisymm ?_ ?_⟩
  · have hCbd : Disjoint (connectedComponentIn (univ \ D.U) x) (discBd B) := by
      apply disjoint_left.mpr
      intro y hyC hyB
      exact (connectedComponentIn_subset _ _ hyC).2 (hbd hyB)
    rcases hB.side hman isPreconnected_connectedComponentIn hCbd with hi | ho
    · exact hi
    · exact False.elim (disjoint_left.mp ho (mem_connectedComponentIn hxD) hx.1)
  · exact hB.isPreconnected_discInt.subset_connectedComponentIn hx hin

/-- The petal replacement is cellular: every remaining loop is a new
petal boundary, and the petal interior is an empty region. This proves
the cellularity check for the drawing in VIII, Section 12, page 274. -/
theorem isCellularDrawing_loop_replacement {S : Type u} [TopologicalSpace S] [T1Space S]
    (hS : IsClosedDisc (univ : Set S)) (D H : Drawing S)
    {ι : Type v} (v : ι → S) (E : ι → Set S)
    (hE : ∀ i, IsClosedDisc (E i) ∧ v i ∈ discBd (E i) ∧ E i ∩ D.U = {v i} ∧
      closure (discBd (E i) \ {v i}) = discBd (E i))
    (hEE : ∀ i j, i ≠ j → E i ∩ E j ⊆ {v i} ∩ {v j})
    (hV : H.V = D.V)
    (hEdges : H.E = {e ∈ D.E | ¬ D.IsLoop e} ∪ range (fun i => discBd (E i) \ {v i}))
    (hU : H.U = (D.span D.V {e ∈ D.E | ¬ D.IsLoop e}).U ∪ ⋃ i, discBd (E i)) :
    IsCellularDrawing H := by
  have hsub : (D.span D.V {e ∈ D.E | ¬ D.IsLoop e}).IsSubdrawing D := Drawing.span_isSubdrawing D _ _
  have hint : ∀ i, Disjoint (discInt (E i)) H.U := by
    intro i
    apply disjoint_left.mpr
    intro x hxint hxU
    rw [hU] at hxU
    rcases hxU with hxOld | hxNew
    · have hxv : x = v i := mem_singleton_iff.mp ((hE i).2.2.1 ▸
        And.intro hxint.1 (hsub.U_subset hxOld))
      exact hxint.2 (hxv.symm ▸ (hE i).2.1)
    · obtain ⟨j, hxj⟩ := mem_iUnion.mp hxNew
      by_cases hij : i = j
      · subst j
        exact hxint.2 hxj
      · have hxv : x = v i := mem_singleton_iff.mp
          (hEE i j hij ⟨hxint.1, discBd_subset _ hxj⟩).1
        exact hxint.2 (hxv.symm ▸ (hE i).2.1)
  intro e he
  have heE : e ∈ H.E := he.1
  rw [hEdges] at heE
  rcases heE with heOld | heNew
  · obtain ⟨w, hw⟩ := he.2
    exact False.elim (heOld.2 ⟨heOld.1, w, by rwa [hV] at hw⟩)
  · obtain ⟨i, rfl⟩ := heNew
    refine ⟨E i, ?_, discInt_mem_regions hS H (hE i).1 ?_ (hint i)⟩
    · rw [(hE i).2.2.2]
      exact isInsideDisc_of_closedDisc_univ hS (hE i).1
    · rw [hU]
      exact fun x hx => .inr (mem_iUnion.mpr ⟨i, hx⟩)

end GraphMinor.GM08
