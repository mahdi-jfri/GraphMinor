module

public import GraphMinor.GM12.Section4OneCrossingHalfEdges
public import GraphMinor.GM12.Section4HalfEdgeFeasibility

/-!
# Vertex contact discs for the one-crossing source drawing

For XII (4.5), claim (1), page 253, select the unique crossing
of each subdivided edge and split there. The crossing points
lie inside the chosen crossing discs, while the source vertices
lie outside them. Clip and thicken the resulting half-edge
stars. This gives disjoint closed vertex discs whose contacts
with the crossing-disc union are the assigned edge-end classes.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The one-crossing source drawing has disjoint closed vertex
discs with exact, distinct edge-end contacts on the frontier
of the crossing-disc union. This proves the vertex-disc
construction in XII (4.5), claim (1), page 253. -/
theorem exists_one_crossing_contact_discs {S V E : Type} [TopologicalSpace S] [T2Space S]
    [NormalSpace S] [ConnectedSpace S] [Fintype V] [Fintype E]
    (hS : IsClosedSurface S) (v : V → S) (hinj : Function.Injective v) (κ : E × Bool → V) (P : E → Set S)
    (hP : ∀ e, IsLineWithEnds (P e) (v (κ (e, false))) (v (κ (e, true))))
    (hPV : ∀ e w, v w ∈ P e → w = κ (e, false) ∨ w = κ (e, true))
    (hcross : ∀ e, ∃ x ∈ edgeMeetingPoints v P, P e ∩ edgeMeetingPoints v P = {x})
    (Z : Set S) (hZ : IsClosed Z) (hvZ : ∀ w, v w ∉ Z)
    (hMZ : edgeMeetingPoints v P ⊆ interior Z) :
    ∃ (q : E × Bool → S) (D : V → Set S), Function.Injective q ∧
      (∀ i, q i ∈ P i.1 ∩ frontier Z) ∧ (∀ w, IsClosedDisc (D w)) ∧
      (∀ w z, w ≠ z → Disjoint (D w) (D z)) ∧
      ∀ w, D w ∩ Z = {z | ∃ i, κ i = w ∧ q i = z} := by
  obtain ⟨x, L, hx, hline, hsub, hvertex, hinter, -, -⟩ :=
    exists_one_crossing_halfedges v κ P hP hPV hcross
  obtain ⟨q, hq, hqL, D, hD, hDD, hDZ⟩ := exists_halfedge_contact_discs
    hS v hinj κ (fun i : E × Bool => x i.1) L
    hline hvertex hinter Z hZ hvZ (fun i => hMZ (hx i.1).1)
  exact ⟨q, D, hq, (fun i => ⟨hsub i (hqL i).1, (hqL i).2⟩), hD, hDD, hDZ⟩

end GraphMinor.GM12
