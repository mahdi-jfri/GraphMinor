module

public import GraphMinor.GM05.VertexPorts
public import GraphMinor.GM05.DiscStarFamilies

/-!
# Choosing the stars at every original vertex

For GM V, (8.14), each original vertex has one disc and one fixed
port for every copy and incident edge. The middle lines make these
ports distinct. Apply the closed-disc star construction separately
at each vertex, including those with no incident edges.
-/

public section
namespace GraphMinor.GM05
open Set Surface

/-- All vertex stars for the copy drawings in GM V, (8.14), page 113.
Each ray joins its new centre to the port of its labelled middle line. -/
theorem exists_copy_vertex_stars {S : Type} [TopologicalSpace S] [T2Space S]
    (D : Drawing S) (m : ℕ) (R : S → Set S) (hR : ∀ w ∈ D.V, IsClosedDisc (R w))
    (u v : D.E → S) (hl : ∀ e, D.toGraph.IsLink e.val (u e) (v e))
    (p q : Fin m × D.E → S) (M : Fin m × D.E → Set S)
    (hM : ∀ a, IsLineWithEnds (M a) (p a) (q a))
    (hp : ∀ a, p a ∈ discBd (R (u a.2))) (hq : ∀ a, q a ∈ discBd (R (v a.2)))
    (hdis : Pairwise (fun a b ↦ Disjoint (M a) (M b))) :
    ∃ x : D.V → Fin m → S, ∃ L : ∀ w : D.V, Fin m × IncidentEdge D w → Set S,
      ∀ w : D.V,
        (∀ i, x w i ∈ discBd (R w.val)) ∧
        (∀ i j, i ≠ j → x w i ≠ x w j) ∧
        (∀ i a, x w i ≠ vertexPort D u p q w a) ∧
        (∀ a, IsLineWithEnds (L w a) (x w a.1) (vertexPort D u p q w a) ∧
          L w a ⊆ R w.val ∧ L w a ∩ discBd (R w.val) = {x w a.1,vertexPort D u p q w a}) ∧
        (∀ i e f, e ≠ f → L w (i,e) ∩ L w (i,f) = {x w i}) ∧
        (∀ a b, a ≠ b → (L w a ∩ L w b).Finite) ∧
        ∀ i j l e f g, i ≠ j → j ≠ l → i ≠ l →
          L w (i,e) ∩ L w (j,f) ∩ L w (l,g) = ∅ := by
  classical
  let : Fintype D.E := D.finite_edges.fintype
  let : ∀ w : D.V, Fintype (IncidentEdge D w) := fun _ ↦ Fintype.ofFinite _
  have hex := fun w : D.V ↦ exists_disc_fixed_port_stars (hR w.val w.prop) m
    (vertexPort D u p q w) (vertexPort_mem_discBd D R u v p q hl hp hq w)
    (vertexPort_injective D u p q M hM hdis w)
  choose x L hstars using hex
  exact ⟨x,L,hstars⟩

end GraphMinor.GM05
