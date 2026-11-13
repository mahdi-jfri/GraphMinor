module

public import GraphMinor.GM07.Defs
import GraphMinor.GM07.Section2Base

/-!
# Orienting a drawing

Choose the two ends of every edge of a drawing to obtain a surface digraph.
No vertices or edges are changed. This allows VIII (18.1) to apply the
surface-digraph statements of VII (9.1) to drawings of grafts.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

/-- Any drawing can be given an orientation, as needed to apply VII (9.1)
in VIII (18.1). -/
theorem exists_surfaceDigraph_for_surface_reduction {S : Type w} [TopologicalSpace S]
    [T1Space S] [Nonempty S] (D : Drawing S) :
    ∃ G : GM07.SurfaceDigraph S, G.G = D := by
  classical
  have hex : ∀ e ∈ D.E, ∃ u v, D.toGraph.IsLink e u v :=
    fun e he => (D.toGraph.edge_mem_iff_exists_isLink e).mp he
  choose p m hlink using hex
  let plus : Set S → S := fun e => if he : e ∈ D.E then p e he else Classical.arbitrary S
  let minus : Set S → S := fun e => if he : e ∈ D.E then m e he else Classical.arbitrary S
  refine ⟨{
    G := D
    plus := plus
    minus := minus
    plus_mem := ?_
    minus_mem := ?_
    ends_eq := ?_ }, rfl⟩
  · intro e he
    simp only [plus, dite_eq_left he]
    exact (hlink e he).2.1
  · intro e he
    simp only [minus, dite_eq_left he]
    exact (hlink e he).2.2.1
  · intro e he
    simp only [plus, minus, dite_eq_left he]
    exact (hlink e he).2.2.2.symm.trans (GM07.tilde_eq_closure_inter_V D he).symm

end GraphMinor.GM08
