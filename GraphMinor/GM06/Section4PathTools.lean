module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5Red
import GraphMinor.GM07.CuffForest
import GraphMinor.GM11.Ties

/-!
# Subpaths of a path drawing

A path drawing joins any two of its vertices by a subpath. Its point set
is a line, so it contains no circle and its graph is a forest. These
facts justify the subpaths used in the last argument of VI (4.2), page 126.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

/-- Both end vertices of a path drawing belong to its vertex set. -/
theorem isPathDrawing_end_vertices
    {S : Type u} [TopologicalSpace S] {P : Drawing S} {s t : S}
    (hP : IsPathDrawing P s t) : s ∈ P.V ∧ t ∈ P.V := by
  obtain ⟨W, _, hV, _⟩ := hP.1
  rw [hV]
  exact ⟨W.start_mem_support, W.end_mem_support⟩

/-- Any two distinct vertices of a path drawing are joined by a subpath
of that drawing. -/
theorem exists_subpath_of_isPathDrawing
    {S : Type u} [TopologicalSpace S] [T1Space S]
    {P : Drawing S} {s t x y : S} (hP : IsPathDrawing P s t)
    (hx : x ∈ P.V) (hy : y ∈ P.V) (hxy : x ≠ y) :
    ∃ Q : Drawing S, IsSubpathOf P Q x y := by
  classical
  obtain ⟨W, _, hV, _⟩ := hP.1
  have hxW : x ∈ W.support := by rw [hV] at hx; exact hx
  have hyW : y ∈ W.support := by rw [hV] at hy; exact hy
  obtain ⟨Wx, _, _⟩ := W.exists_append_of_mem hxW
  obtain ⟨Wy, _, _⟩ := W.exists_append_of_mem hyW
  obtain ⟨R, hR, _, _⟩ := GM11.GraphWalk.exists_isSimple (Wx.reverse.append Wy)
  have hsub := walkDrawing_isSubdrawing P R
  exact ⟨walkDrawing P R, hsub, hsub.U_subset,
    isPathDrawing_walkDrawing_of_isSimple P hR hxy⟩

/-- The point set of a path drawing is a line. -/
theorem isLine_U_of_isPathDrawing
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {P : Drawing S} {s t : S} (hP : IsPathDrawing P s t) : IsLine P.U := by
  obtain ⟨f, hf⟩ := hP.2
  let e : unitInterval ≃ₜ range f := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective f hf.1) f.continuous.rangeFactorization
  exact ⟨e.trans (Homeomorph.setCongr hf.2.1)⟩

/-- A path drawing is a graph forest, since a line contains no circle. -/
theorem isGraphForest_of_isPathDrawing
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {P : Drawing S} {s t : S} (hP : IsPathDrawing P s t) : IsGraphForest P.toGraph := by
  exact GM07.isForest_of_noOArc fun F hF hFP =>
    GM11.not_isOArc_of_subset_line (isLine_U_of_isPathDrawing hP) hF hFP

/-- A path drawing whose only possible vertices are its two distinct
ends has exactly one edge. -/
theorem ncard_edges_eq_one_of_path_vertices_subset_ends
    {S : Type u} [TopologicalSpace S] {P : Drawing S} {s t : S}
    (hP : IsPathDrawing P s t) (hst : s ≠ t) (hV : P.V ⊆ {s, t}) :
    P.E.ncard = 1 := by
  classical
  obtain ⟨W, hW, hWV, hWE⟩ := hP.1
  have hsub : W.support.toFinset ⊆ ({s, t} : Finset S) := by
    intro x hx
    have hxP : x ∈ P.V := by
      rw [hWV]
      exact List.mem_toFinset.mp hx
    simpa only [Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] using hV hxP
  have hbound := Finset.card_le_card hsub
  have hlen : W.length ≤ 1 := by
    rw [List.toFinset_card_of_nodup hW, GM11.length_support] at hbound
    have hcard : ({s, t} : Finset S).card = 2 := by simp [hst]
    rw [hcard] at hbound
    omega
  cases W with
  | nil hs => exact False.elim (hst rfl)
  | @cons _ v _ e hl R =>
    cases R with
    | nil hv =>
      have hE : P.E = {e} := by
        rw [hWE]
        ext x
        simp [GraphWalk.edges]
      rw [hE, Set.ncard_singleton]
    | cons hl' R' =>
      have hlen' : 2 ≤ (GraphWalk.cons hl (GraphWalk.cons hl' R')).length := by
        simp only [GraphWalk.length, GraphWalk.edges, List.length_cons]
        exact Nat.le_add_left 2 _
      exact False.elim (Nat.not_succ_le_self 1 (hlen'.trans hlen))

end GraphMinor.GM06
