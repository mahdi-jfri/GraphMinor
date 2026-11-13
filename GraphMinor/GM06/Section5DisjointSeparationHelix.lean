module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5AdjoinBoundary
import GraphMinor.GM06.Section5CuffRootComponent
import GraphMinor.GM06.Section5DetachedHelixAvoidance
import GraphMinor.GM06.Section5SeparationGeometry
import GraphMinor.GM06.Section5SeparationHelices
import GraphMinor.GM06.Section3Induce
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# Reduction 2 for disjoint sides

In VI (5.5), page 130, first handle a separation with no common
vertex. The discarded drawing misses the cuffs and the retained
drawing. Its components are detached from the augmented component
containing the cuffs. The constructed disc detours avoid all of them,
so the retained helix becomes normal in the old drawing with no
increase in potential.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- The case of VI (5.5), Reduction 2, with disjoint vertex sets.
All discarded edges and any enclosed retained components are handled
by the constructed detached-component enclosures. -/
theorem theorem_5_5_red2_of_disjoint_sides
    {k : ℕ} {G G₁ G₂ : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (L₁ : CylinderLinkage k G₁)
    (hG : IsCylinderSection5Drawing k G) (hG₁ : IsCylinderSection5Drawing k G₁)
    (hsep : IsGraphSeparation G.toGraph G₁.toGraph G₂.toGraph)
    (hdisV : Disjoint G₁.V G₂.V)
    (f : Curve ClosedCylinder) (hf : IsHelix k G₁ f) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ curvePhi k G g ≤ curvePhi k G₁ f := by
  have h₁ : G₁.IsSubdrawing G := ⟨hsep.1.vertexSet_mono, hsep.1.edgeSet_mono⟩
  have h₂ : G₂.IsSubdrawing G := ⟨hsep.2.1.vertexSet_mono, hsep.2.1.edgeSet_mono⟩
  have hsets := point_sets_of_graph_separation hsep
  have hdisU : Disjoint G₁.U G₂.U := by
    rw [Set.disjoint_iff_inter_eq_empty, hsets.2]
    exact Set.disjoint_iff_inter_eq_empty.mp hdisV
  have hdisbd : Disjoint (bd ClosedCylinder) G₂.U := by
    apply disjoint_left.mpr
    intro x hxb hx₂
    have hxGV : x ∈ G.V := hG.2.1 ⟨hxb, h₂.U_subset hx₂⟩
    have hxM : x ∈ cylinderM1 k ∪ cylinderM2 k := hG.2.2 ▸ ⟨hxGV, hxb⟩
    have hx₁ : x ∈ G₁.V := (hG₁.2.2.symm ▸ hxM).1
    exact disjoint_left.mp hdisU (G₁.V_subset_U hx₁) hx₂
  obtain ⟨F, hGF, hFU, _⟩ := exists_drawing_adjoining_boundary L hG
  have hG₁F : G₁.IsSubdrawing F :=
    ⟨h₁.1.trans hGF.1, h₁.2.trans hGF.2⟩
  have hbdF : bd ClosedCylinder ⊆ F.U := hFU ▸ subset_union_right
  obtain ⟨C, hC, hCbd⟩ := exists_sphere_component_containing_cuffs hG.1 L hGF hbdF
  let A : Set (OnePoint EuclideanPlane) := cylinderToSphere '' (G₁.U ∪ bd ClosedCylinder)
  let B : Set (OnePoint EuclideanPlane) := cylinderToSphere '' G₂.U
  have hAc : IsClosed A := isClosedEmbedding_cylinderToSphere.isClosedMap _
    (G₁.isClosed_U.union (isClosed_bd ClosedCylinder))
  have hBc : IsClosed B := isClosedEmbedding_cylinderToSphere.isClosedMap _ G₂.isClosed_U
  have hdisAB : Disjoint A B := by
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    have hyx : y = x := injective_cylinderToSphere he
    subst y
    rcases hx with hx | hx
    · exact disjoint_left.mp hdisU hx hy
    · exact disjoint_left.mp hdisbd hx hy
  have hCU : compPointSet C ⊆ (cylinderSphereDrawing F).U := by
    rw [← biUnion_compPointSet_eq_U (cylinderSphereDrawing F)]
    exact fun x hx => mem_iUnion₂.mpr ⟨C, hC, hx⟩
  have hcover : compPointSet C ⊆ A ∪ B := by
    intro x hx
    have hxF := hCU hx
    rw [cylinderSphereDrawing_U, hFU, ← hsets.1] at hxF
    obtain ⟨y, hy, rfl⟩ := hxF
    rcases hy with (hy | hy) | hy
    · exact Or.inl (mem_image_of_mem _ (Or.inl hy))
    · exact Or.inr (mem_image_of_mem _ hy)
    · exact Or.inl (mem_image_of_mem _ (Or.inr hy))
  have hcap : compPointSet C ∩ (A ∩ B) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨_, hxA, hxB⟩
    exact disjoint_left.mp hdisAB hxA hxB
  have hCA : compPointSet C ⊆ A := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp
      (isConnected_compPointSet (cylinderSphereDrawing F) hC).isPreconnected
      A B hAc hBc hcover hcap with h | h
    · exact h
    · let i : Fin k := ⟨0, hG.1⟩
      let s := cylinderM1Point k i
      have hsb : s ∈ bd ClosedCylinder := by rw [bd_closedCylinder]; exact Or.inl rfl
      have hsC := hCbd (mem_image_of_mem cylinderToSphere hsb)
      exact False.elim (disjoint_left.mp hdisAB (mem_image_of_mem _ (Or.inr hsb)) (h hsC))
  obtain ⟨g, hg, hφ, hgr⟩ := exists_helix_avoiding_components_detached_from_cuffs
    hG₁F hC hCbd f hf
  have havoid : range g ∩ G₂.U = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxg, hx₂⟩
    have hxF : x ∈ F.U := hGF.U_subset (h₂.U_subset hx₂)
    have hxC := hgr ⟨hxg, hxF⟩
    exact disjoint_left.mp hdisAB (hCA hxC) (mem_image_of_mem _ hx₂)
  let i : Fin k := ⟨0, hG.1⟩
  have hs : cylinderM1Point k i ∈ G₁.V :=
    (L₁.isSubdrawing i).1.1 (isPathDrawing_end_vertices (L₁.isPath i)).1
  obtain ⟨hgOld, heq⟩ := helix_of_separation_avoids_discarded_side hsep hs g hg
    (havoid ▸ empty_subset _)
  exact ⟨g, hgOld, heq.le.trans hφ⟩

end GraphMinor.GM06
