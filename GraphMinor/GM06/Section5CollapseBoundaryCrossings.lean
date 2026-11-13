module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CollapseInChart
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5CollapseChartFibers
import Mathlib.Topology.Separation.Hausdorff

/-!
# Fixed boundary crossings of the rectangular collapse

This proves the local boundary fact used in Lemma 8 of our proof
of VI (5.7), page 133 (outlined in `Alg57Algorithm.lean`). A continuous map that is
the identity outside its support also fixes the support's frontier.
A surviving open edge misses the exceptional fibre. Injectivity off
that fibre then shows that its intersection with the fixed frontier
is unchanged. In particular, reading the edges at the same boundary
parameters gives the same ordered crossings after contraction.

The result applies to the actual rectangular formula and its pasted
homotopy. It concerns boundary crossings, without an orientation sign
for homeomorphisms of surfaces.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- Continuity extends the identity outside a set to its frontier. -/
theorem collapse_fixes_frontier
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (π : C(S, S)) (D : Set S) (hout : ∀ x ∉ D, π x = x) :
    ∀ x ∈ frontier D, π x = x := by
  have hclosed : IsClosed {x : S | π x = x} :=
    isClosed_eq π.continuous continuous_id
  have hfix : closure Dᶜ ⊆ {x : S | π x = x} :=
    closure_minimal (fun x hx => hout x hx) hclosed
  intro x hx
  rw [frontier_eq_closure_inter_closure] at hx
  exact hfix hx.2

/-- Every stage of an identity-outside homotopy fixes the same
frontier, including its final collapse. -/
theorem collapse_homotopy_fixes_frontier
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (H : C(unitInterval × S, S)) (D : Set S)
    (hout : ∀ x ∉ D, ∀ t, H (t, x) = x) :
    ∀ x ∈ frontier D, ∀ t, H (t, x) = x := by
  intro x hx t
  let π : C(S, S) := ⟨fun y => H (t, y),
    H.continuous.comp (continuous_const.prodMk continuous_id)⟩
  exact collapse_fixes_frontier π D (fun y hy => hout y hy t) x hx

/-- A fixed point belongs to an image of a set avoiding the exceptional
fibre exactly when it belonged to that set before the collapse. -/
theorem mem_image_iff_of_fixed_collapse
    {S : Type*} {π : S → S} {s y : S} {A F : Set S}
    (hfibre : π ⁻¹' {s} = A) (hi : InjOn π Aᶜ)
    (hFA : Disjoint F A) (hfix : π y = y) :
    y ∈ π '' F ↔ y ∈ F := by
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hxA : x ∉ A := disjoint_left.mp hFA hx
    have hπx : π x ≠ s := fun h => hxA (hfibre ▸ h)
    have hyA : y ∉ A := by
      intro hy
      have hπy : π y = s := show y ∈ π ⁻¹' {s} from hfibre.symm ▸ hy
      exact hπx (hxy.trans (hfix.symm.trans hπy))
    have heq : x = y := hi hxA hyA (hxy.trans hfix.symm)
    exact heq ▸ hx
  · intro hy
    exact ⟨y, hy, hfix⟩

/-- On the fixed support boundary, an edge avoiding the exceptional
fibre has exactly the same geometric crossings after the collapse. -/
theorem image_inter_frontier_of_collapse
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (π : C(S, S)) {s : S} {A D F : Set S}
    (hfibre : π ⁻¹' {s} = A) (hi : InjOn π Aᶜ)
    (hout : ∀ x ∉ D, π x = x) (hFA : Disjoint F A) :
    (π '' F) ∩ frontier D = F ∩ frontier D := by
  ext y
  constructor
  · rintro ⟨hy, hyD⟩
    exact ⟨(mem_image_iff_of_fixed_collapse hfibre hi hFA
      (collapse_fixes_frontier π D hout y hyD)).mp hy, hyD⟩
  · rintro ⟨hy, hyD⟩
    exact ⟨(mem_image_iff_of_fixed_collapse hfibre hi hFA
      (collapse_fixes_frontier π D hout y hyD)).mpr hy, hyD⟩

/-- A parametrization of the fixed frontier reads identical crossing
parameters. Thus it reads the same order, without changing its
orientation or choosing a new boundary parametrization. -/
theorem boundary_crossing_parameters_of_collapse
    {S T : Type*} [TopologicalSpace S] [T2Space S]
    (π : C(S, S)) {s : S} {A D F : Set S}
    (hfibre : π ⁻¹' {s} = A) (hi : InjOn π Aᶜ)
    (hout : ∀ x ∉ D, π x = x) (hFA : Disjoint F A)
    (B : T → S) (hB : range B ⊆ frontier D) :
    (∀ t, π (B t) = B t) ∧ B ⁻¹' (π '' F) = B ⁻¹' F := by
  have hfix : ∀ t, π (B t) = B t := fun t =>
    collapse_fixes_frontier π D hout (B t) (hB ⟨t, rfl⟩)
  refine ⟨hfix, ?_⟩
  ext t
  exact mem_image_iff_of_fixed_collapse hfibre hi hFA (hfix t)

/-- Distinct open drawing edges miss the closure of a non-loop edge:
they miss its open edge and both of its vertex ends. -/
theorem disjoint_open_edge_closed_link
    {S : Type*} [TopologicalSpace S]
    {G : Drawing S} {a f : Set S}
    {s v : S} (hl : G.toGraph.IsLink a s v) (hvs : v ≠ s)
    (hf : f ∈ G.E) (hfa : f ≠ a) : Disjoint f (closure a) := by
  rw [closure_edge_eq_union_ends G hl hvs.symm]
  refine (disjoint_edges_of_ne G hf hl.edge_mem hfa).union_right ?_
  apply disjoint_left.mpr
  intro x hxf hx
  have hxV : x ∉ G.V := (hf.2.1 hxf).2
  rcases hx with rfl | hx
  · exact hxV hl.2.1
  · exact hxV (mem_singleton_iff.mp hx ▸ hl.2.2.1)

/-- The rectangular contraction maps its closed chart onto itself. -/
theorem image_chart_of_rectangle_collapse
    {S : Type*} [TopologicalSpace S] {D : Set S}
    (e : Section5CollapseRectangle ≃ₜ D) (π : S → S)
    (hchart : ∀ z, π (e z).1 = (e (section5RectangleCollapse z)).1) :
    π '' D = D := by
  apply subset_antisymm
  · rintro y ⟨x, hx, rfl⟩
    let z := e.symm ⟨x, hx⟩
    have hz : (e z).1 = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
    rw [← hz, hchart]
    exact (e (section5RectangleCollapse z)).2
  · intro y hy
    obtain ⟨z, hz⟩ := section5RectangleCollapse_surjective (e.symm ⟨y, hy⟩)
    refine ⟨(e z).1, (e z).2, ?_⟩
    rw [hchart, hz]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)

/-- Outside the chart the rectangular collapse is the identity, and
inside it no point can leave it. Its full chart preimage is exact. -/
theorem preimage_chart_of_rectangle_collapse
    {S : Type*} [TopologicalSpace S] {D : Set S}
    (e : Section5CollapseRectangle ≃ₜ D) (π : S → S)
    (hchart : ∀ z, π (e z).1 = (e (section5RectangleCollapse z)).1)
    (hout : ∀ x ∉ D, π x = x) : π ⁻¹' D = D := by
  ext x
  constructor
  · intro hx
    by_contra hxD
    exact hxD (hout x hxD ▸ hx)
  · intro hx
    have hh := mem_image_of_mem π hx
    rwa [image_chart_of_rectangle_collapse e π hchart] at hh

/-- The local crossing assertion of Lemma 8, for the actual pasted
rectangular formula and every retained ordinary edge. The same
boundary points, with the same parameter values, meet that edge's
image. The exceptional-fibre and injectivity facts are derived from
the rectangular formula, rather than supplied as rotation data. -/
theorem rectangle_collapse_preserves_edge_boundary_crossings
    {T : Type*} {G : Drawing ClosedCylinder} {a f : Set ClosedCylinder}
    {s v : ClosedCylinder} (hl : G.toGraph.IsLink a s v) (hvs : v ≠ s)
    (hf : f ∈ G.E) (hfa : f ≠ a) {D : Set ClosedCylinder}
    (e : Section5CollapseRectangle ≃ₜ D) (π : C(ClosedCylinder, ClosedCylinder))
    (hchart : ∀ z, π (e z).1 = (e (section5RectangleCollapse z)).1)
    (hout : ∀ x ∉ D, π x = x)
    (hsegment : (fun z => (e z).1) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1} = closure a)
    (B : T → ClosedCylinder) (hB : range B ⊆ frontier D) :
    (∀ t, π (B t) = B t) ∧ B ⁻¹' (π '' f) = B ⁻¹' f := by
  have hfibre : π ⁻¹' {(e section5RectangleOrigin).1} = closure a := by
    rw [fiber_of_rectangle_collapse_in_chart e π hchart hout, hsegment]
  have hi : InjOn π (closure a)ᶜ := by
    rw [← hsegment]
    exact injOn_of_rectangle_collapse_in_chart e π hchart hout
  exact boundary_crossing_parameters_of_collapse π hfibre hi hout
    (disjoint_open_edge_closed_link hl hvs hf hfa) B hB

end GraphMinor.GM06
