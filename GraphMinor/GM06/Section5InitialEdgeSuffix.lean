module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section3Induce
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5Components
import GraphMinor.GM11.Walks

/-!
# The path after removal of its first edge

For Reduction 3 of VI, page 129, a valency-one initial vertex forces
its sole edge to be the first edge of the linkage walk. Its remaining
walk is simple and avoids that initial vertex. The original path is
the union of the closed first edge and this remaining path.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11

private theorem exists_suffix_after_forced_first_link
    {G P : Drawing ClosedCylinder} {s v t : ClosedCylinder} {a : Set ClosedCylinder}
    (hP : IsPathDrawing P s t) (hPG : P.IsSubdrawing G)
    (hl : G.toGraph.IsLink a s v) (hvs : v ≠ s) (hvt : v ≠ t)
    (hforced : ∀ e ∈ G.E, e ≠ a → s ∉ closure e) :
    ∃ B : Drawing ClosedCylinder, IsPathDrawing B v t ∧
      B.IsSubdrawing (induceDrawing G (G.V \ {s})) ∧ P.U = closure a ∪ B.U := by
  obtain ⟨W, hW, hV, hE⟩ := hP.1
  cases W with
  | nil hv =>
    exact False.elim ((isPathDrawing_start_ne_end hP) rfl)
  | @cons s w t e hlink R =>
    have hlinkG := (hPG.isLink_iff hlink.1).mp hlink
    have hscl : s ∈ closure e :=
      (show s ∈ closure e ∩ G.V from hlinkG.2.2.2.symm ▸ mem_insert s {w}).1
    have hea : e = a := by
      by_contra hne
      exact hforced e hlinkG.1 hne hscl
    have hwne : w ≠ s := by
      intro hws
      exact (List.nodup_cons.mp hW).1 (hws ▸ R.start_mem_support)
    have hwv : w = v := by
      have hp : ({s, w} : Set ClosedCylinder) = {s, v} :=
        hlinkG.2.2.2.symm.trans (hea.symm ▸ hl.2.2.2)
      have hw : w ∈ ({s, v} : Set ClosedCylinder) := hp ▸ mem_insert_of_mem s rfl
      rcases hw with hws | hwv
      · exact False.elim (hwne hws)
      · exact hwv
    subst w
    let B := walkDrawing P R
    have hB : B.IsSubdrawing G := (walkDrawing_isSubdrawing P R).trans hPG
    have hsnot : s ∉ R.support := (List.nodup_cons.mp hW).1
    have hBs : B.IsSubdrawing (induceDrawing G (G.V \ {s})) :=
      subdrawing_induce_of_vertices_subset hB sdiff_subset (by
        intro x hx
        refine ⟨hB.1 hx, ?_⟩
        intro hxs
        subst x
        exact hsnot (by simpa only [B, walkDrawing_V, mem_ofPred_eq] using hx))
    refine ⟨B, isPathDrawing_walkDrawing_of_isSimple P hW.of_cons hvt, hBs, ?_⟩
    have hPW : P = walkDrawing P (.cons hlink R) := by
      apply Drawing.ext_of_V_E
      · exact hV.trans (walkDrawing_V P (.cons hlink R)).symm
      · exact hE.trans (walkDrawing_E P (.cons hlink R)).symm
    ext x
    rw [hPW, mem_walkDrawing_U]
    change (x ∈ s :: R.support ∨ ∃ f ∈ e :: R.edges, x ∈ closure f) ↔
      x ∈ closure a ∪ (walkDrawing P R).U
    rw [mem_union, mem_walkDrawing_U]
    simp only [List.mem_cons, exists_eq_or_imp]
    rw [hea]
    constructor
    · rintro ((rfl | hx) | (hxa | hx))
      · exact Or.inl (hea ▸ hscl)
      · exact Or.inr (Or.inl hx)
      · exact Or.inl hxa
      · exact Or.inr (Or.inr hx)
    · rintro (hxa | (hx | hx))
      · exact Or.inr (Or.inl hxa)
      · exact Or.inl (Or.inr hx)
      · exact Or.inr (Or.inr hx)

/-- Removing the sole initial edge from a linkage path leaves a
nondegenerate path in the drawing with that initial vertex deleted. -/
theorem exists_suffix_of_initial_valency_one_edge
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G) (i : Fin k)
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v)
    (hvs : v ≠ cylinderM1Point k i) (hvC : v ∉ cylinderCuff2) :
    ∃ B : Drawing ClosedCylinder, IsPathDrawing B v (L.curve i 1) ∧
      B.IsSubdrawing (induceDrawing G (G.V \ {cylinderM1Point k i})) ∧
      (L.pathDrawing i).U = closure a ∪ B.U := by
  apply exists_suffix_after_forced_first_link (L.isPath i) (L.isSubdrawing i).1 hl hvs
  · intro hvt
    apply hvC
    obtain ⟨j, hj⟩ := L.curve_one_mem i
    rw [hvt, ← hj]
    rfl
  · intro e he hne
    exact not_mem_closure_edge_of_ne_red3 hval hl hvs he hne

end GraphMinor.GM06
