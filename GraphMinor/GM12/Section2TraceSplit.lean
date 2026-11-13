module

public import GraphMinor.GM12.Section2TraceComposition
public import GraphMinor.GM12.Section2TraceParameters
import GraphMinor.GM11.Regions

/-!
# Splitting trace steps at a vertex visit

For the restriction and induction steps of XII (2.1), pages 243--244,
split a trace at a parameter which maps to a drawing vertex. Such a
parameter cannot lie in the interior of a recorded region interval.
Remove the first two edges until the split point is reached, then
rebuild that prefix. Both pieces remain trace steps on their respective
parameter intervals, and their concatenation is the original walk.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- Split trace steps at any parameter in the interval which maps to
an original drawing vertex. Both resulting walks keep their trace-step
properties, and concatenate exactly to the original walk. -/
theorem traceSteps_split_at_vertex_parameter
    {S : Type*} [TopologicalSpace S] {Γ K : Drawing S} {f : ℝ → S}
    {a b : ℝ} {u v : S} (W : GraphWalk K.toGraph u v) (hW : TraceSteps Γ K f a b W)
    {s : ℝ} (hs : s ∈ Icc a b) (hfs : f s ∈ Γ.V) :
    ∃ (x : S) (P : GraphWalk K.toGraph u x) (Q : GraphWalk K.toGraph x v),
      f s = x ∧ W = P.append Q ∧ TraceSteps Γ K f a s P ∧ TraceSteps Γ K f s b Q := by
  have hp := traceSteps_parameters W hW
  by_cases hsa : s = a
  · subst s
    have huK := W.mem_vertexSet_of_mem_support W.start_mem_support
    exact ⟨u, .nil huK, W, hp.2.1, rfl, ⟨rfl, hp.2.1, hp.2.2.1⟩, hW⟩
  · cases hWcase : W with
    | nil hv =>
      rw [hWcase] at hW
      have hsa' : s = a := le_antisymm (hs.2.trans_eq hW.1.symm) hs.1
      exact (hsa hsa').elim
    | cons hlink rest =>
      rw [hWcase] at hW
      cases hrestcase : rest with
      | nil hv => rw [hrestcase] at hW; exact hW.elim
      | cons hlink' tail =>
        rw [hrestcase] at hW
        obtain ⟨c, hac, hfa, hu, hfc, hwK, r, hr, hwr, hfr, hleave, henter, htail⟩ := hW
        have hcs : c ≤ s := by
          by_contra hn
          have hsc : s < c := lt_of_not_ge hn
          have has : a < s := lt_of_le_of_ne hs.1 (Ne.symm hsa)
          exact region_subset hr (hfr s ⟨has, hsc⟩) (Γ.V_subset_U hfs)
        obtain ⟨x, P, Q, hfx, htailEq, hP, hQ⟩ :=
          traceSteps_split_at_vertex_parameter tail htail ⟨hcs, hs.2⟩ hfs
        let A := GraphWalk.cons hlink (GraphWalk.cons hlink' P)
        refine ⟨x, A, Q, hfx, ?_, ?_, hQ⟩
        · change GraphWalk.cons hlink (GraphWalk.cons hlink' tail) =
            GraphWalk.cons hlink (GraphWalk.cons hlink' (P.append Q))
          rw [htailEq]
        · exact ⟨c, hac, hfa, hu, hfc, hwK, r, hr, hwr, hfr, hleave, henter, hP⟩
termination_by W.length

decreasing_by
  simp_all only [GraphWalk.length, GraphWalk.edges, List.length_cons]
  omega

/-- Extract the trace steps between two vertex visits in their parameter
order. Every vertex and edge of the extracted walk belongs to the original
walk, as required when splitting curves in XII (2.1), page 244. -/
theorem traceSteps_between_vertex_parameters
    {S : Type*} [TopologicalSpace S] {Γ K : Drawing S} {f : ℝ → S}
    {a b : ℝ} {u v : S} (W : GraphWalk K.toGraph u v) (hW : TraceSteps Γ K f a b W)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc s b)
    (hfs : f s ∈ Γ.V) (hft : f t ∈ Γ.V) :
    ∃ (x y : S) (M : GraphWalk K.toGraph x y),
      f s = x ∧ f t = y ∧ TraceSteps Γ K f s t M ∧
      (∀ z ∈ M.support, z ∈ W.support) ∧ (∀ e ∈ M.edges, e ∈ W.edges) := by
  obtain ⟨x, P, Q, hfx, hWsplit, _, hQ⟩ :=
    traceSteps_split_at_vertex_parameter W hW hs hfs
  obtain ⟨y, M, R, hfy, hQsplit, hM, _⟩ :=
    traceSteps_split_at_vertex_parameter Q hQ ht hft
  refine ⟨x, y, M, hfx, hfy, hM, ?_, ?_⟩
  · intro z hz
    rw [hWsplit, GraphWalk.mem_support_append, hQsplit, GraphWalk.mem_support_append]
    exact Or.inr (Or.inl hz)
  · intro e he
    rw [hWsplit, GraphWalk.edges_append, List.mem_append,
      hQsplit, GraphWalk.edges_append, List.mem_append]
    exact Or.inr (Or.inl he)

end GraphMinor.GM12
