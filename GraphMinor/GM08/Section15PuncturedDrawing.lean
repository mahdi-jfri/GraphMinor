module

public import GraphMinor.Surface.Defs
public import GraphMinor.GM12.Section3Punctured
import GraphMinor.GM12.Section3BoundaryEquality
import GraphMinor.GM08.Section12Subspace

/-!
# Reading the tube drawing between separated empty sides

Restrict the drawing to the complement of the two empty disc interiors.
No drawing point is lost. Inclusion preserves the graph and identifies
its boundary vertices with the old vertices on the two disc boundaries.
This is the root-preserving change of ambient surface in VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- Read a drawing between two empty discs in their complement. Its
boundary roots are exactly the old vertices on their boundary union,
as required after the framing adjustment in VIII (15.4), page 282. -/
theorem exists_drawing_in_two_disc_complement {S : Type w} [TopologicalSpace S]
    (hS : IsClosedSurface S) (G : Drawing S) {D E : Set S}
    (hD : IsClosedDisc D) (hE : IsClosedDisc E) (hDE : Disjoint D E)
    (hDoff : Disjoint (discInt D) G.U) (hEoff : Disjoint (discInt E) G.U)
    (hnD : G.IsNormal (discBd D)) (hnE : G.IsNormal (discBd E)) :
    let Q := GM12.discComplement (![D, E] : Fin 2 → Set S)
    ∃ G' : Drawing Q, G'.U = (Subtype.val : Q → S) ⁻¹' G.U ∧
      G'.V = (Subtype.val : Q → S) ⁻¹' G.V ∧ G'.IsProper ∧
      (Subtype.val : Q → S) '' (G'.V ∩ bd Q) = G.V ∩ (discBd D ∪ discBd E) ∧
      ∃ i : Iso G'.toGraph G.toGraph,
        ∀ v : G'.V, (i.vertexEquiv v).1 = v.1.1 := by
  classical
  have : T2Space S := hS.2.1
  let P : Fin 2 → Set S := ![D, E]
  have hP : ∀ i, IsClosedDisc (P i) := by intro i; fin_cases i <;> assumption
  have hdis : Pairwise (fun i j => Disjoint (P i) (P j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hDE
    · exact hDE.symm
    · exact (hij rfl).elim
  have avoid : ∀ A : Set S, Disjoint (discInt A) G.U → G.IsNormal (discBd A) →
      G.U ∩ A = G.V ∩ discBd A := by
    intro A hoff hn
    apply subset_antisymm
    · intro x hx
      have hxb : x ∈ discBd A := by
        by_contra hb
        exact disjoint_left.mp hoff ⟨hx.2, hb⟩ hx.1
      exact ⟨hn ⟨hxb, hx.1⟩, hxb⟩
    · exact fun x hx => ⟨G.V_subset_U hx.1, discBd_subset A hx.2⟩
  have havoid : ∀ i, G.U ∩ P i = G.V ∩ discBd (P i) := by
    intro i
    fin_cases i
    · exact avoid D hDoff hnD
    · exact avoid E hEoff hnE
  have hUC := GM12.drawing_support_subset_discComplement hS G P hP hdis havoid
  let G' := GM12.drawingInSubspace G (GM12.discComplement P) hUC
  have hg := isGraphBij_drawingInSubspace G isClosed_closure hUC
  refine ⟨G', GM12.drawingInSubspace_U G _ hUC, GM12.drawingInSubspace_V G _ hUC,
    GM12.drawingInDiscComplement_isProper hS G P hP hdis havoid, ?_,
    hg.toIso, (fun _ => rfl)⟩
  have h := GM12.drawingInDiscComplement_boundary_vertices_eq hS G P hP hdis hUC
  convert h using 1
  ext x
  simp [GM12.discBoundaryVertices, P, Fin.exists_fin_two, and_or_left]

end GraphMinor.GM08
