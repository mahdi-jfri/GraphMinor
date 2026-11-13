module

public import GraphMinor.GM12.Section73CircuitVisitCount
public import GraphMinor.GM12.Section73LineEnds
import GraphMinor.GM11.Section88
import GraphMinor.GM11.Ties

/-!
# A walk along a line and back

The line case of the tie selection used in XII (7.3), page 262,
needs a closed walk visiting each vertex at most twice. Start
with any closed walk whose point set is a line. Cut it at the
two ends. A shortest path between the ends is no longer than
either of the two parts. Its point set is the whole line,
since a connected subset containing both ends of a line is the
whole line. Following this path and returning along it therefore
has no greater length and gives the required visit bounds.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 Classical

/-- A closed walk whose point set is a line can be replaced by
a simple path and its reverse, without increasing length. -/
theorem exists_path_backtrack_of_line_walk
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    {K : Drawing S} {u a b : S} (W : GraphWalk K.toGraph u u)
    (hLine : IsLineWithEnds (walkDrawing K W).U a b) :
    ∃ P : GraphWalk K.toGraph a b, P.IsSimple ∧
      (walkDrawing K P).U = (walkDrawing K W).U ∧
      2 * P.length ≤ W.length := by
  let N := walkDrawing K W
  have hNK : N.IsSubdrawing K := walkDrawing_isSubdrawing K W
  obtain ⟨ha, hb⟩ := line_ends_mem_vertices hLine
  obtain ⟨Z, hZS, hZE⟩ := hNK.exists_walk_down W
    (by intro x hx; rw [walkDrawing_V]; exact hx)
    (by intro e he; rw [walkDrawing_E]; exact he)
  rw [walkDrawing_V] at ha hb
  have haZ : a ∈ Z.support := by rw [hZS]; exact ha
  have hbZ : b ∈ Z.support := by rw [hZS]; exact hb
  obtain ⟨A, B, hZ⟩ := GraphWalk.exists_append_of_mem Z haZ
  have hbBA : b ∈ (B.append A).support := by
    rw [hZ] at hbZ
    rcases (GraphWalk.mem_support_append _ _).mp hbZ with hbA | hbB
    · exact (GraphWalk.mem_support_append _ _).mpr (Or.inr hbA)
    · exact (GraphWalk.mem_support_append _ _).mpr (Or.inl hbB)
  obtain ⟨Q, R, hBA⟩ := GraphWalk.exists_append_of_mem (B.append A) hbBA
  obtain ⟨a', ha', b', hb', P, hP, hmin, _, _⟩ :=
    exists_shortest (A := ({a} : Set S)) (B := ({b} : Set S))
      ⟨a, rfl, b, rfl, ⟨Q⟩⟩
  have haa' : a' = a := ha'
  have hbb' : b' = b := hb'
  subst a'
  subst b'
  have hPQ := hmin a rfl b rfl Q
  have hPR := hmin a rfl b rfl R.reverse
  rw [GraphWalk.length_reverse] at hPR
  have hlen : 2 * P.length ≤ W.length := by
    have hZlen : Z.length = W.length := congrArg List.length hZE
    have hlenAB := congrArg GraphWalk.length hZ
    have hlenBA := congrArg GraphWalk.length hBA
    rw [GraphWalk.length_append] at hlenAB
    rw [GraphWalk.length_append, GraphWalk.length_append] at hlenBA
    omega
  have hab : a ≠ b := by
    obtain ⟨e, he0, he1⟩ := hLine
    intro he
    have h01 : (0 : unitInterval) = 1 := e.injective (Subtype.ext (he0.trans (he.trans he1.symm)))
    exact zero_ne_one h01
  have hPU : (walkDrawing N P).U = N.U := by
    have hPL := isLine_of_isPathBetween (walkDrawing_isPathBetween N hP) hab
    have hpre : IsPreconnected (walkDrawing N P).U := by
      obtain ⟨f, hf, hr, _, _⟩ := hPL.exists_arc
      rw [← hr]
      exact isPreconnected_range hf.1
    apply hLine.eq_of_subset hpre (walkDrawing_isSubdrawing N P).U_subset
    · exact (walkDrawing N P).V_subset_U (by rw [walkDrawing_V]; exact P.start_mem_support)
    · exact (walkDrawing N P).V_subset_U (by rw [walkDrawing_V]; exact P.end_mem_support)
  obtain ⟨P', hPS, hPE⟩ := hNK.exists_walk_up P
  have hdraw : walkDrawing K P' = walkDrawing N P := by
    apply Drawing.ext_of_V_E
    · simp only [walkDrawing_V, hPS]
    · simp only [walkDrawing_E, hPE]
  refine ⟨P', ?_, hdraw ▸ hPU, ?_⟩
  · change P'.support.Nodup
    rw [hPS]
    exact hP
  · have hlen' : P'.length = P.length := congrArg List.length hPE
    rwa [hlen']

/-- The normalized closed walk visits each point at most twice,
and either end of the line at most once. -/
theorem exists_line_walk_with_visit_bound
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    {K : Drawing S} {u a b : S} (W : GraphWalk K.toGraph u u)
    (hLine : IsLineWithEnds (walkDrawing K W).U a b) :
    ∃ Z : GraphWalk K.toGraph a a, Z.length ≤ W.length ∧
      (walkDrawing K Z).U = (walkDrawing K W).U ∧
      (∀ v, walkVertexCount v Z ≤ 2) ∧
      (∀ v, v = a ∨ v = b → walkVertexCount v Z ≤ 1) := by
  obtain ⟨P, hP, hPU, hlen⟩ := exists_path_backtrack_of_line_walk W hLine
  refine ⟨P.append P.reverse, ?_, ?_, ?_, ?_⟩
  · rw [GraphWalk.length_append, GraphWalk.length_reverse]
    omega
  · ext x
    rw [mem_U_append, mem_U_reverse, or_self, hPU]
  · exact fun v => (walkVertexCount_backtrack_bounds P hP v).1
  · exact fun v => (walkVertexCount_backtrack_bounds P hP v).2

end GraphMinor.GM12
