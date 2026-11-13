module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM11.Walks

/-!
# The initial vertex of a path has valency one

For VI (5.1), page 129, an initial vertex with no incident edges
outside its linkage path has valency one. In a simple walk, an edge
incident with the first vertex must be the first edge. No loop can
occur there. Counting the two kinds of incident edges proves the claim.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

universe u

/-- If every edge incident with the start of a path is already an
edge of that path, the start has valency one. This is the degree step
used in Graph Minors VI (5.1), page 129. -/
theorem valency_eq_one_of_incident_edges_in_path {S : Type u} [TopologicalSpace S] [T1Space S]
    {G P : Drawing S} {s t : S}
    (hP : IsPathDrawing P s t) (hPG : P.IsSubdrawing G)
    (hincident : ∀ e ∈ G.E, s ∈ closure e → e ∈ P.E) :
    vertexValency G.toGraph s = 1 := by
  have hst := isPathDrawing_start_ne_end hP
  obtain ⟨W, hW, _, hE⟩ := hP.1
  cases W with
  | nil _ => exact False.elim (hst rfl)
  | @cons s a t e hl T =>
    have hsnot : s ∉ T.support := (List.nodup_cons.mp hW).1
    have hsa : s ≠ a := fun he => hsnot (he.symm ▸ T.start_mem_support)
    have hlink : G.toGraph.IsLink e s a := (hPG.isLink_iff hl.1).mp hl
    have huniq {f : Set S} {b : S} (hf : G.toGraph.IsLink f s b) : f = e := by
      have hscl : s ∈ closure f ∩ G.V := by
        rw [hf.2.2.2]
        exact mem_insert s {b}
      have hfP := hincident f hf.1 hscl.1
      have hfW : f ∈ e :: T.edges := by
        have hh := hfP
        rw [hE] at hh
        exact hh
      rcases List.mem_cons.mp hfW with hfe | hfT
      · exact hfe
      · have hflink : P.toGraph.IsLink f s b := (hPG.isLink_iff hfP).mpr hf
        exact False.elim (hsnot (T.left_mem_support_of_mem_edges hfT hflink))
    have hA : {f ∈ G.E | ∃ b ≠ s, G.toGraph.IsLink f s b} = {e} := by
      ext f
      constructor
      · rintro ⟨_, b, _, hf⟩
        exact mem_singleton_iff.mpr (huniq hf)
      · intro hf
        have heq := mem_singleton_iff.mp hf
        subst f
        exact ⟨hlink.1, a, hsa.symm, hlink⟩
    have hB : {f ∈ G.E | G.toGraph.IsLink f s s} = ∅ := by
      ext f
      constructor
      · rintro ⟨_, hf⟩
        have hfe := huniq hf
        subst f
        have ha : a ∈ ({s, s} : Set S) := by
          rw [← hf.2.2.2, hlink.2.2.2]
          exact mem_insert_of_mem s (mem_singleton a)
        have has : a = s := by
          simpa only [mem_insert_iff, mem_singleton_iff, or_self] using ha
        exact False.elim (hsa has.symm)
      · intro hf
        exact False.elim hf
    unfold vertexValency
    change {f ∈ G.E | ∃ b ≠ s, G.toGraph.IsLink f s b}.ncard +
      2 * {f ∈ G.E | G.toGraph.IsLink f s s}.ncard = 1
    rw [hA, hB, ncard_singleton, ncard_empty]

end GraphMinor.GM06
