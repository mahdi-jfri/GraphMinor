module

public import GraphMinor.GM05.ExpansionDefs
public import GraphMinor.Planar.Defs
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM05.DrawingSubdivisionMinor
import GraphMinor.GM05.ParallelMiddleLines
import GraphMinor.GM05.CopyVertexStars
import GraphMinor.GM05.DiscStarSupports
import GraphMinor.GM05.StarSystemModels
import GraphMinor.GM05.BranchUnionExpansion
import GraphMinor.GM05.RegionUnionMultiplicity
import GraphMinor.Minor.Basic

/-!
# Arbitrarily many expansions with multiplicity two

This is the geometric construction in GM V, (8.14), page 113.
Subdivide to remove loops, choose parallel edge middles and fixed-port
stars, and planarize their union. Each copy gives a minor model.
Restrict to its branch vertices and compose with the original graph's
minor in the subdivision. Three resulting expansions through one
vertex would lie in three stars of one vertex disc, which was excluded
when the star centres were chosen.
-/

public section
namespace GraphMinor.GM05
open Set Surface Graph
universe u v

/-- The union construction in GM V, proof of (8.14), page 113:
a graph drawn on a nonempty closed surface has arbitrarily many
expansions in a finite graph drawn there, with each host vertex in
at most two specified expansions. -/
theorem exists_surface_expansion_family {α : Type u} {β : Type v}
    {H : Graph α β} {S : Type} [TopologicalSpace S] [Nonempty S]
    (hS : IsClosedSurface S) (Γ : GraphDrawing H S) (m : ℕ) :
    ∃ D : Drawing S, ∃ A : Fin m → Graph S (Set S),
      (∀ i, IsHExpansion H D.toGraph (A i)) ∧
      ∀ z : S, {i | z ∈ V(A i)}.ncard ≤ 2 := by
  classical
  let : T2Space S := hS.2.1
  obtain ⟨J,hJU,hJV,hJloop,hΓJ⟩ := exists_loopFree_minor_refinement Γ.drawing
  have hHJ : IsIsoMinor H J.toGraph := Γ.iso.isIsoMinor_left hΓJ
  let : Fintype J.E := J.finite_edges.fintype
  let : ∀ w : J.V, Fintype (IncidentEdge J w) := fun _ ↦ Fintype.ofFinite _
  obtain ⟨R,u,v,p,q,M,hRdisc,hRdis,hsrc,hMiddle,hMdis⟩ := exists_parallel_middle_lines hS J hJloop m
  have hlink := fun e ↦ (hsrc e).1
  have hne := fun e ↦ (hsrc e).2
  have hM := fun a ↦ (hMiddle a).1
  have hMu := fun a ↦ (hMiddle a).2.1
  have hMv := fun a ↦ (hMiddle a).2.2.1
  have hp := fun a ↦ (hMiddle a).2.2.2.1
  have hq := fun a ↦ (hMiddle a).2.2.2.2.1
  have haway := fun a ↦ (hMiddle a).2.2.2.2.2
  obtain ⟨x,L,hStars⟩ := exists_copy_vertex_stars J m R hRdisc u v hlink p q M hM hp hq hMdis
  have hx : ∀ w i, x w i ∈ R w.val := fun w i ↦ discBd_subset _ ((hStars w).1 i)
  have hxne := fun w ↦ (hStars w).2.1
  have hL := fun w a ↦ ((hStars w).2.2.2.1 a).1
  have hLR := fun w a ↦ ((hStars w).2.2.2.1 a).2.1
  have hfin := fun w ↦ (hStars w).2.2.2.2.2.1
  obtain ⟨D,ηv,ηe,hm,hηbound⟩ := exists_models_of_star_system J m R hRdis u v hlink hne p q M
    hM hMu hMv haway hMdis x L hx hxne hL hLR hfin
  have hStarThree : ∀ w : J.V, ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      starSupport (x w) (L w) i ∩ starSupport (x w) (L w) j ∩ starSupport (x w) (L w) k = ∅ := by
    intro w
    exact (disc_star_support_intersections (x w) (vertexPort J u p q w) (L w)
      (hStars w).1 (hStars w).2.1 (hStars w).2.2.1
      (fun a ↦ ((hStars w).2.2.2.1 a).2.2) (hStars w).2.2.2.2.2.1
      (hStars w).2.2.2.2.2.2).2
  have hregion : Pairwise (fun w z : J.V ↦ Disjoint (R w.val) (R z.val)) := by
    intro w z hwz
    exact hRdis w.val w.prop z.val z.prop (fun he ↦ hwz (Subtype.ext he))
  have hStarR : ∀ i w, starSupport (x w) (L w) i ⊆ R w.val := fun i w ↦
    starSupport_subset (x w) (L w) i (hx w i) (fun e ↦ hLR w (i,e))
  have hcount : ∀ z : S, {i | z ∈ ⋃ w : J.V, starSupport (x w) (L w) i}.ncard ≤ 2 :=
    region_union_multiplicity_le_two m (fun w : J.V ↦ R w.val)
      (fun i w ↦ starSupport (x w) (L w) i) hregion hStarR hStarThree
  choose A hA hAbound using fun i ↦ exists_expansion_in_branch_union hHJ
    J.finite_V J.finite_edges D.finite_V D.finite_edges (hm i)
  refine ⟨D,A,hA,?_⟩
  intro z
  have hsub : {i | z ∈ V(A i)} ⊆ {i | z ∈ ⋃ w : J.V, starSupport (x w) (L w) i} := by
    intro i hzi
    obtain ⟨w,hw,hzw⟩ := mem_iUnion₂.mp (hAbound i hzi)
    exact mem_iUnion.mpr ⟨⟨w,hw⟩,hηbound i w hw hzw⟩
  exact (ncard_le_ncard hsub (toFinite _)).trans (hcount z)

end GraphMinor.GM05
