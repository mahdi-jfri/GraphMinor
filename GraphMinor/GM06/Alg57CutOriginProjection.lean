module

public import GraphMinor.Compute.GM06CutAdjacencyMath
import GraphMinor.Compute.GM06CutRowsFacts

/-!
# Projecting computed copied origins

In the cut of VI (5.7), page 133, every original row contributes two
consecutive copied slots. A copied outgoing end projects to an end
of that original row. The origin scatter therefore projects to the
original row index. This also holds for empty and retired slots.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute

private theorem splitRowsFrom_project_mem (marks : GM06CutTables)
    (rows : List (List ℕ)) (base v q : ℕ)
    (hq : q ∈ (gm06SplitRotationRowsFrom marks base rows).getD v []) :
    gm06UncutDart q ∈ rows.getD (v / 2) [] := by
  induction rows generalizing base v with
  | nil => simp [gm06SplitRotationRowsFrom] at hq
  | cons row rows ih =>
    rw [gm06SplitRotationRowsFrom_cons, gm06SplitVertexRows_eq_selected] at hq
    simp only [List.cons_append, List.nil_append] at hq
    cases v with
    | zero =>
      simp only [List.getD_cons_zero] at hq
      apply gm06SplitVertexRows_project_mem (gm06CutPositionAt marks base) row
      rw [gm06SplitVertexRows_eq_selected]
      exact List.mem_flatten.mpr ⟨_, List.mem_cons_self, hq⟩
    | succ v =>
      cases v with
      | zero =>
        simp only [List.getD_cons_succ, List.getD_cons_zero] at hq
        apply gm06SplitVertexRows_project_mem (gm06CutPositionAt marks base) row
        rw [gm06SplitVertexRows_eq_selected]
        exact List.mem_flatten.mpr ⟨_, by simp, hq⟩
      | succ v =>
        simp only [List.getD_cons_succ] at hq
        have hh := ih (base + 1) v hq
        have hv : (v + 1 + 1) / 2 = v / 2 + 1 := by omega
        simpa only [hv, List.getD_cons_succ] using hh

private theorem splitRowsFrom_right_marked (marks : GM06CutTables)
    (rows : List (List ℕ)) (base v q : ℕ)
    (hq : q ∈ (gm06SplitRotationRowsFrom marks base rows).getD v [])
    (hv : v % 2 = 1) : gm06CutPositionAt marks (base + v / 2) ≠ none := by
  induction rows generalizing base v with
  | nil => simp [gm06SplitRotationRowsFrom] at hq
  | cons row rows ih =>
    rw [gm06SplitRotationRowsFrom_cons] at hq
    cases v with
    | zero => omega
    | succ v =>
      cases v with
      | zero =>
        intro hpos
        simp only [Nat.zero_add, Nat.reduceDiv, Nat.add_zero] at hpos
        rw [hpos] at hq
        simp [gm06SplitVertexRows] at hq
      | succ v =>
        rw [gm06SplitVertexRows_eq_selected] at hq
        simp only [List.cons_append, List.nil_append, List.getD_cons_succ] at hq
        have hv' : v % 2 = 1 := by omega
        have hh := ih (base + 1) v hq hv'
        have he : base + (v + 1 + 1) / 2 = (base + 1) + v / 2 := by omega
        rwa [he]

/-- A nonempty odd copied row comes only from a marked split vertex. -/
theorem splitRows_right_marked (marks : GM06CutTables) (rows : List (List ℕ))
    (v q : ℕ) (hq : q ∈ (gm06SplitRotationRows marks rows).getD v [])
    (hv : v % 2 = 1) : gm06CutPositionAt marks (v / 2) ≠ none := by
  simpa only [Nat.zero_add] using splitRowsFrom_right_marked marks rows 0 v q hq hv

/-- A copied row end projects to the original row at half its slot. -/
theorem splitRows_project_mem (marks : GM06CutTables) (rows : List (List ℕ))
    (v q : ℕ) (hq : q ∈ (gm06SplitRotationRows marks rows).getD v []) :
    gm06UncutDart q ∈ rows.getD (v / 2) [] :=
  splitRowsFrom_project_mem marks rows 0 v q hq

/-- The numeric origin computed by scattering copied rows projects
to the row of the original directed end. -/
theorem cutOrigins_project_mem {m q : ℕ} (marks : GM06CutTables) (rows : List (List ℕ))
    (hn : rows.flatten.Nodup) (hq : q ∈ (gm06SplitRotationRows marks rows).flatten)
    (hb : q < 4 * m) :
    let v := (gm06CutOrigins m (gm06SplitRotationRows marks rows))[q]?.getD 0
    v < 2 * rows.length ∧ gm06UncutDart q ∈ rows.getD (v / 2) [] := by
  obtain ⟨row, hr, hqr⟩ := List.mem_flatten.mp hq
  obtain ⟨v, hv, heq⟩ := List.mem_iff_getElem.mp hr
  have hz : (row, v) ∈ (gm06SplitRotationRows marks rows).zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    exact List.getElem?_eq_some_iff.mpr ⟨hv, heq⟩
  have ho := gm06CutOrigins_getElem? _ row (gm06SplitRotationRows_nodup marks rows hn) hz hqr hb
  dsimp only
  rw [ho]
  simp only [Option.getD_some]
  refine ⟨by simpa only [gm06SplitRotationRows_length] using hv, ?_⟩
  apply splitRows_project_mem marks rows v q
  simpa only [List.getD_eq_getElem _ _ hv, heq] using hqr

/-- Each active copied origin belongs to the computed copied vertex
list when its original slot is among the supplied live labels. -/
theorem cutOrigins_mem_vertices {m q : ℕ} (marks : GM06CutTables)
    (rows : List (List ℕ)) (live : List ℕ) (hn : rows.flatten.Nodup)
    (hq : q ∈ (gm06SplitRotationRows marks rows).flatten) (hb : q < 4 * m)
    (hlive : ∀ v < rows.length, gm06UncutDart q ∈ rows.getD v [] → v ∈ live) :
    (gm06CutOrigins m (gm06SplitRotationRows marks rows))[q]?.getD 0 ∈
      gm06CutVertices marks live := by
  let v := (gm06CutOrigins m (gm06SplitRotationRows marks rows))[q]?.getD 0
  obtain ⟨hv, hm⟩ := cutOrigins_project_mem marks rows hn hq hb
  have hvhalf : v / 2 < rows.length := by dsimp only [v]; omega
  have hvl : v / 2 ∈ live := hlive _ hvhalf hm
  have hvlen : v < (gm06SplitRotationRows marks rows).length := by
    rw [gm06SplitRotationRows_length]
    exact hv
  have hrow : q ∈ (gm06SplitRotationRows marks rows).getD v [] := by
    rw [List.getD_eq_getElem _ _ hvlen]
    exact (gm06CutOrigins_row_iff _ (gm06SplitRotationRows_nodup marks rows hn) hq hb hvlen).mp rfl
  apply List.mem_flatMap.mpr
  refine ⟨v / 2, hvl, ?_⟩
  change v ∈ if gm06CutPositionAt marks (v / 2) = none then
    [gm06CutVertex (v / 2) true] else
      [gm06CutVertex (v / 2) true, gm06CutVertex (v / 2) false]
  have heven : v % 2 = 0 ∨ v % 2 = 1 := by omega
  rcases heven with he | ho
  · have hve : v = gm06CutVertex (v / 2) true := by
      simp only [gm06CutVertex, Bool.not_true, Bool.toNat_false, Nat.add_zero]
      omega
    split_ifs
    · exact List.mem_singleton.mpr hve
    · exact List.mem_cons.mpr (Or.inl hve)
  · have hpos := splitRows_right_marked marks rows v q hrow ho
    rw [ite_eq_right hpos]
    have hvo : v = gm06CutVertex (v / 2) false := by
      simp only [gm06CutVertex, Bool.not_false, Bool.toNat_true]
      omega
    exact List.mem_cons_of_mem _ (List.mem_singleton.mpr hvo)

end GraphMinor.GM06
