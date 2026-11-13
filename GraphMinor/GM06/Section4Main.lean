module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4Routed
import GraphMinor.GM06.Section4Uncross
import GraphMinor.GM06.Section4Minimal

/-!
# Graph Minors VI (4.1): boundary-path obstructions

A feasible routed forest supplies a path in the specified boundary class.
Uncrossing gives the least enclosed path, which rules out obstruction (i).
Every boundary vertex of that least path lies on the corresponding path in
the feasible forest. This rules out obstruction (ii) by connectivity and
obstruction (iii) by comparing subpaths inside the enclosed disc.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

universe u

/-- Graph Minors VI (4.1)(i), page 124: if the specified minimal path does not
exist, there is no forest subgraph homotopic to `H`. Feasibility supplies a
path in its class, and the proved minimal-path existence then applies. -/
theorem theorem_4_1_i
    {S : Type u} [TopologicalSpace S] {G H Hst : Drawing S} {s t : S} {A : Set S}
    (hS : IsSurface S) (hG : G.IsProper) (hbd : H.V ∩ bd S = G.V ∩ bd S)
    (hseg : IsSegmentOf (bd S) (H.V ∩ bd S) A)
    (hs : s ∈ H.V ∩ bd S) (ht : t ∈ H.V ∩ bd S) (hst : s ≠ t)
    (hHst : IsSubpathOf H Hst s t) (hHA : PathHomotopicToArc Hst s t A)
    (hno : ¬ ∃ P : Drawing S, IsMinimalBoundaryPath G s t A P) :
    ¬ HasHomotopicForestSubgraph G H := by
  let : T2Space S := hS.2.1
  intro hfeas
  obtain ⟨P₀, hP₀, hPA₀⟩ :=
    exists_subpath_homotopicToArc_of_hasHomotopicForestSubgraph hfeas hs ht hst hHst hHA
  have hsegG : IsSegmentOf (bd S) (G.V ∩ bd S) A := by rw [← hbd]; exact hseg
  exact hno (exists_isMinimalBoundaryPath_of_segment_path hS hG hst hsegG hP₀ hPA₀)

/-- Graph Minors VI, (4.1), page 124: any of the three printed boundary-path
obstructions rules out a forest subgraph homotopic to the specified forest.
The proof supplies the minimal-path existence and uncrossing implicit in the
paper's statement that the proof is clear. -/
theorem theorem_4_1_proof : Statement41.{u} := by
  intro S _ G H hS hG _ _ hbd hcondition
  obtain ⟨A, hseg, s, hs, t, ht, hst, _, _, ⟨Hst, hHst, hHA⟩, hbad⟩ := hcondition
  rcases hbad with hno | htwo | hthree
  · exact theorem_4_1_i hS hG hbd hseg hs ht hst hHst hHA hno
  · obtain ⟨P, hP, C, hC, hnot, hmeet⟩ := htwo
    exact theorem_4_1_ii hS hG hbd hseg hs ht hst hHst hHA hP C hC hnot hmeet
  · obtain ⟨P, hP, x, hx, Hxt, Pxt, hHxt, hPxt, hnot⟩ := hthree
    exact theorem_4_1_iii hS hG hbd hseg hs ht hst hHst hHA hP hx Hxt Pxt hHxt hPxt hnot

end GraphMinor.GM06
