module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section3Induce
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section3Dual
import GraphMinor.GM11.Walks

/-!
# Removing a vertex of valency one before contraction

For Reduction 3 of VI, page 129, deleting the initial vertex removes
exactly its sole edge. The remaining drawing meets that closed edge
only at the other end. Thus a map collapsing this edge, and injective
elsewhere, is injective on the remaining drawing.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- Deleting an initial vertex of valency one removes exactly its
incident edge, and the remaining point set meets its closure only at
the other end. -/
theorem deleted_initial_vertex_drawing
    {k : ℕ} {G : Drawing ClosedCylinder} {i : Fin k}
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v)
    (hvs : v ≠ cylinderM1Point k i) :
    let J := induceDrawing G (G.V \ {cylinderM1Point k i})
    J.E = G.E \ {a} ∧ J.U ∩ closure a = {v} ∧
      G.U = J.U ∪ closure a := by
  classical
  intro J
  let s := cylinderM1Point k i
  have hJV : J.V = G.V \ {s} := induceDrawing_V G sdiff_subset
  have hJE : J.E = G.E \ {a} := by
    rw [induceDrawing_E]
    ext e
    constructor
    · rintro ⟨he, hends⟩
      refine ⟨he, ?_⟩
      intro hea
      subst e
      have hscl : s ∈ closure a :=
        (show s ∈ closure a ∩ G.V from hl.2.2.2.symm ▸ mem_insert s {v}).1
      exact (hends ⟨hscl, hl.2.1⟩).2 rfl
    · rintro ⟨he, hne⟩
      refine ⟨he, fun x hx => ⟨hx.2, ?_⟩⟩
      intro hxs
      subst x
      exact not_mem_closure_edge_of_ne_red3 hval hl hvs he hne hx.1
  have hcl : closure a = a ∪ {s, v} :=
    closure_edge_eq_union_ends G hl hvs.symm
  have hdisj (e : Set ClosedCylinder) (he : e ∈ J.E) : Disjoint e (closure a) := by
    rw [hJE] at he
    rw [hcl]
    refine (disjoint_edges_of_ne G he.1 hl.1 he.2).union_right ?_
    refine disjoint_left.mpr ?_
    intro x hxe hxp
    have hxV : x ∉ G.V := (he.1.2.1 hxe).2
    rcases hxp with rfl | hxp
    · exact hxV hl.2.1
    · exact hxV (mem_singleton_iff.mp hxp ▸ hl.2.2.1)
  have hvJ : v ∈ J.U := J.V_subset_U (by rw [hJV]; exact ⟨hl.2.2.1, hvs⟩)
  have hvcl : v ∈ closure a := by rw [hcl]; exact Or.inr (mem_insert_of_mem s rfl)
  have hinter : J.U ∩ closure a = {v} := by
    apply subset_antisymm
    · rintro x ⟨hxJ, hxa⟩
      rw [induceDrawing_U G sdiff_subset] at hxJ
      rcases hxJ with hxV | hxE
      · have hpair : x ∈ ({s, v} : Set ClosedCylinder) := by
          rw [← hl.2.2.2]; exact ⟨hxa, hxV.1⟩
        rcases hpair with hxs | hxv
        · exact False.elim (hxV.2 hxs)
        · exact hxv
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxE
        exact False.elim (disjoint_left.mp (hdisj e he) hxe hxa)
    · rintro x rfl
      exact ⟨hvJ, hvcl⟩
  refine ⟨hJE, hinter, subset_antisymm ?_ ?_⟩
  · rw [G.U_eq]
    rintro x (hxV | hxE)
    · by_cases hxs : x = s
      · right
        rw [hxs, hcl]
        exact Or.inr (mem_insert s {v})
      · exact Or.inl (J.V_subset_U (by rw [hJV]; exact ⟨hxV, hxs⟩))
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxE
      by_cases hea : e = a
      · exact Or.inr (hea ▸ hxe)
      · exact Or.inl (J.closure_subset_U (by rw [hJE]; exact ⟨he, hea⟩) hxe)
  · exact union_subset (induceDrawing_isSubdrawing G sdiff_subset).U_subset
      (G.closure_subset_U hl.1)

/-- A collapse with one closed-edge fiber is injective on the drawing
remaining after deletion of the initial vertex. -/
theorem injOn_deleted_initial_vertex_drawing
    {k : ℕ} {G : Drawing ClosedCylinder} {i : Fin k}
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v)
    (hvs : v ≠ cylinderM1Point k i)
    {π : ClosedCylinder → ClosedCylinder}
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure a)
    (hi : InjOn π (closure a)ᶜ) :
    InjOn π (induceDrawing G (G.V \ {cylinderM1Point k i})).U := by
  obtain ⟨_, hinter, _⟩ := deleted_initial_vertex_drawing hval hl hvs
  intro x hx y hy hxy
  by_cases hxa : x ∈ closure a
  · have hya : y ∈ closure a := by
      rw [← hfiber] at hxa ⊢
      change π y = cylinderM1Point k i
      exact hxy.symm.trans hxa
    have hxv : x = v := by have := hinter ▸ (show x ∈ _ ∩ closure a from ⟨hx, hxa⟩); exact this
    have hyv : y = v := by have := hinter ▸ (show y ∈ _ ∩ closure a from ⟨hy, hya⟩); exact this
    exact hxv.trans hyv.symm
  · apply hi hxa _ hxy
    intro hya
    have hxb : x ∈ closure a := by
      rw [← hfiber] at hya ⊢
      change π x = cylinderM1Point k i
      exact hxy.trans hya
    exact hxa hxb

end GraphMinor.GM06
