module

public import GraphMinor.GM06.Section5ContractedRegionEquiv
public import GraphMinor.GM11.LocalCone
import GraphMinor.GM06.Section3Dual

/-!
# Polar charts fixed by an edge collapse

For the local rotation argument in VI (5.7), page 133, a collapse
maps every old drawing atom to a new atom. A vertex maps to a
vertex, the contracted open edge maps to its new vertex, and the
remaining edges map to their retained edges. Regions map to regions
by the region correspondence. Thus an old polar chart fixed
pointwise by the collapse is still a polar chart for the new drawing.

The argument works in the cylinder and in its capped sphere. It supplies the unchanged local charts
in Lemma 8 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`), without requiring an
orientation theorem for surface maps.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- The exact graph images and sole exceptional fibre imply that
all drawing atoms map to drawing atoms. In particular, this derives
the region part rather than adding it to a rotation witness. -/
theorem image_atom_of_closed_edge_collapse
    {S : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    {G G' : Drawing S} {e : Set S} {s v : S}
    (hl : G.toGraph.IsLink e s v) (π : C(S, S))
    (hfibre : π ⁻¹' {s} = closure e) (hi : InjOn π (closure e)ᶜ)
    (hsurj : Function.Surjective π)
    (hV : G'.V = π '' G.V) (hE : G'.E = (image π) '' (G.E \ {e}))
    (hU : G'.U = π '' G.U) : ∀ a ∈ G.A, π '' a ∈ G'.A := by
  have hscl : s ∈ closure e :=
    (show s ∈ closure e ∩ G.V from hl.2.2.2.symm ▸ mem_insert s {v}).1
  have hπs : π s = s := show s ∈ π ⁻¹' {s} from hfibre.symm ▸ hscl
  have hsV : s ∈ G'.V := by
    rw [hV]
    exact ⟨s, hl.2.1, hπs⟩
  have hoff : ∀ x, π x ≠ s → x ∉ closure e := by
    intro x hx hxe
    have hh : π x = s := show x ∈ π ⁻¹' {s} from hfibre.symm ▸ hxe
    exact hx hh
  have hinj : ∀ x y, π x ≠ s → π y ≠ s → π x = π y → x = y :=
    fun x y hx hy hxy => hi (hoff x hx) (hoff y hy) hxy
  intro a ha
  rcases ha with (⟨w, hw, rfl⟩ | ha) | ha
  · rw [image_singleton]
    exact Or.inl (Or.inl ⟨π w, hV ▸ mem_image_of_mem π hw, rfl⟩)
  · by_cases hae : a = e
    · subst a
      obtain ⟨x, hx⟩ := hl.edge_mem.2.2.1.nonempty
      have himage : π '' e = {s} := by
        apply subset_antisymm
        · rintro y ⟨z, hz, rfl⟩
          exact show z ∈ π ⁻¹' {s} from hfibre.symm ▸ subset_closure hz
        · intro y hy
          have hys : y = s := hy
          rw [hys]
          exact ⟨x, hx, show x ∈ π ⁻¹' {s} from hfibre.symm ▸ subset_closure hx⟩
      rw [himage]
      exact Or.inl (Or.inl ⟨s, hsV, rfl⟩)
    · exact Or.inl (Or.inr (hE ▸ mem_image_of_mem (image π) ⟨ha, hae⟩))
  · exact Or.inr (image_region_of_cylinder_contraction π s hinj
      (fun z _ => hsurj z) (G'.V_subset_U hsV)
      (hfibre.symm ▸ G.closure_subset_U hl.edge_mem) hU ha).1

/-- A polar chart fixed by a map carrying old atoms to new atoms
remains polar. Its disc, centre, rays and boundary parameters do
not change. -/
theorem isPolar_of_fixed_atom_images
    {S : Type*} [TopologicalSpace S] {G G' : Drawing S}
    {v : S} {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar G v Φ)
    (π : S → S) (hfixed : ∀ x, π (Φ x) = Φ x)
    (hatom : ∀ a ∈ G.A, π '' a ∈ G'.A) : IsPolar G' v Φ := by
  refine ⟨hp.inj, hp.centre, hp.nhd, ?_⟩
  intro x hx c hc
  obtain ⟨a, ha, hxa, hca⟩ := hp.ray x hx c hc
  refine ⟨π '' a, hatom a ha, ?_, ?_⟩
  · exact ⟨Φ x, hxa, hfixed x⟩
  · exact ⟨Φ (discScale c x), hca, hfixed _⟩

/-- In the exact closed-edge collapse, a fixed old polar chart is
a polar chart of the contracted drawing. All hypotheses concern
the map and graph images, rather than a desired rotation order. -/
theorem isPolar_of_closed_edge_collapse_fixed_chart
    {S : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    {G G' : Drawing S} {e : Set S} {s v w : S}
    (hl : G.toGraph.IsLink e s v) (π : C(S, S))
    (hfibre : π ⁻¹' {s} = closure e) (hi : InjOn π (closure e)ᶜ)
    (hsurj : Function.Surjective π)
    (hV : G'.V = π '' G.V) (hE : G'.E = (image π) '' (G.E \ {e}))
    (hU : G'.U = π '' G.U)
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar G w Φ)
    (hfixed : ∀ x, π (Φ x) = Φ x) : IsPolar G' w Φ :=
  isPolar_of_fixed_atom_images hp π hfixed
    (image_atom_of_closed_edge_collapse hl π hfibre hi hsurj hV hE hU)

/-- A chart outside the closed support of the actual collapse is
unchanged as a chart of the new drawing. This applies to a small
chart at any vertex outside that support. -/
theorem isPolar_of_closed_edge_collapse_outside_support
    {S : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    {G G' : Drawing S} {e : Set S} {s v w : S}
    (hl : G.toGraph.IsLink e s v) (π : C(S, S))
    (hfibre : π ⁻¹' {s} = closure e) (hi : InjOn π (closure e)ᶜ)
    (hsurj : Function.Surjective π)
    (hV : G'.V = π '' G.V) (hE : G'.E = (image π) '' (G.E \ {e}))
    (hU : G'.U = π '' G.U) {D : Set S} (hout : ∀ x ∉ D, π x = x)
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar G w Φ) (hΦD : Disjoint (range Φ) D) :
    IsPolar G' w Φ := by
  apply isPolar_of_closed_edge_collapse_fixed_chart hl π hfibre hi hsurj hV hE hU hp
  intro x
  exact hout (Φ x) (disjoint_left.mp hΦD (mem_range_self x))

/-- A chart disjoint from the collapsed edge can be moved by the
collapse. Its centre is the image vertex, and its rays still lie in
single drawing atoms. Openness off the collapsed edge supplies its
new neighbourhood, even when the old chart was not fixed. -/
theorem isPolar_of_closed_edge_collapse_mapped_chart
    {S : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    {G G' : Drawing S} {e : Set S} {s v w : S}
    (hl : G.toGraph.IsLink e s v) (π : C(S, S))
    (hfibre : π ⁻¹' {s} = closure e) (hi : InjOn π (closure e)ᶜ)
    (hsurj : Function.Surjective π)
    (hopen : ∀ U : Set S, IsOpen U → Disjoint U (closure e) → IsOpen (π '' U))
    (hV : G'.V = π '' G.V) (hE : G'.E = (image π) '' (G.E \ {e}))
    (hU : G'.U = π '' G.U)
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar G w Φ)
    (hΦe : Disjoint (range Φ) (closure e)) : IsPolar G' (π w) (π.comp Φ) := by
  have hdis : ∀ x, Φ x ∉ closure e :=
    fun x => disjoint_left.mp hΦe (mem_range_self x)
  have hnhd : π w ∈ interior (range (π.comp Φ)) := by
    apply mem_interior.mpr
    refine ⟨π '' interior (range Φ), ?_, hopen _ isOpen_interior
      (hΦe.mono_left interior_subset), ⟨w, hp.nhd, rfl⟩⟩
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := interior_subset hx
    exact ⟨z, rfl⟩
  refine ⟨fun x y hxy => hp.inj (hi (hdis x) (hdis y) hxy), ?_, hnhd, ?_⟩
  · change π (Φ polarCentre) = π w
    rw [hp.centre]
  · intro x hx c hc
    obtain ⟨a, ha, hxa, hca⟩ := hp.ray x hx c hc
    exact ⟨π '' a, image_atom_of_closed_edge_collapse hl π hfibre hi hsurj hV hE hU a ha,
      ⟨Φ x, hxa, rfl⟩, ⟨Φ (discScale c x), hca, rfl⟩⟩

end GraphMinor.GM06
