module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5ContractionRegions
import GraphMinor.GM11.Regions

/-!
# The region bijection of an initial-edge collapse

This proves Lemma 9 of our proof of VI (5.7), page 133 (outlined in
`Alg57Algorithm.lean`). The exceptional fibre is contained in the drawing, and
all other fibres are singletons. The inverse image of the new
drawing is therefore exactly the old drawing. A complementary
component pulls back to a component, and every old component is
obtained in this way. Thus taking its image gives a region
bijection. The proof works on any compact Hausdorff ambient space,
so it also applies to the capped drawing. Compactness makes the collapse closed, which identifies
the images of region closures. No region cache is used by the program.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- A contraction with its exceptional fibre inside the old drawing
has exactly that drawing as the inverse image of its image drawing. -/
theorem preimage_drawing_pointSet_of_cylinder_contraction
    {S : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    {G G' : Drawing S} (π : C(S, S)) (s : S)
    (hinj : ∀ x y, π x ≠ s → π y ≠ s → π x = π y → x = y)
    (hfibre : π ⁻¹' {s} ⊆ G.U) (hU : G'.U = π '' G.U) :
    π ⁻¹' G'.U = G.U := by
  ext x
  constructor
  · intro hx
    change π x ∈ G'.U at hx
    by_cases hxs : π x = s
    · exact hfibre hxs
    · obtain ⟨y, hy, hyx⟩ := hU ▸ hx
      have hys : π y ≠ s := fun h => hxs (hyx.symm.trans h)
      exact hinj y x hys hxs hyx ▸ hy
  · intro hx
    exact hU.symm ▸ mem_image_of_mem π hx

/-- The image of every old region is a new region, its full
inverse image is that old region, and its closure is the image
of the old closure. This is the region assertion of Lemma 9. -/
theorem image_region_of_cylinder_contraction
    {S : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    {G G' : Drawing S} (π : C(S, S)) (s : S)
    (hinj : ∀ x y, π x ≠ s → π y ≠ s → π x = π y → x = y)
    (hsurj : ∀ z, z ≠ s → ∃ x, π x = z)
    (hs : s ∈ G'.U) (hfibre : π ⁻¹' {s} ⊆ G.U) (hU : G'.U = π '' G.U)
    {r : Set S} (hr : r ∈ G.R) :
    π '' r ∈ G'.R ∧ π ⁻¹' (π '' r) = r ∧ π '' closure r = closure (π '' r) := by
  have hpre := preimage_drawing_pointSet_of_cylinder_contraction π s hinj hfibre hU
  obtain ⟨x, hxr⟩ := region_nonempty hr
  have hxoff : x ∉ G.U := region_subset hr hxr
  have hyoff : π x ∉ G'.U := by
    intro hy
    have hx : x ∈ π ⁻¹' G'.U := hy
    exact hxoff (hpre ▸ hx)
  let R := connectedComponentIn (univ \ G'.U) (π x)
  have hR : R ∈ G'.R := ⟨π x, ⟨mem_univ _, hyoff⟩, rfl⟩
  obtain ⟨hRpre, hRcl⟩ := preimage_region_of_contraction π s hinj hsurj hs hfibre hU hR
  have hxpre : x ∈ π ⁻¹' R := mem_connectedComponentIn ⟨mem_univ _, hyoff⟩
  have hRr : π ⁻¹' R = r := region_eq_of_mem hRpre hr hxpre hxr
  have honto : R ⊆ range π := by
    intro z hz
    apply hsurj z
    intro hzs
    exact region_subset hR hz (hzs.symm ▸ hs)
  have himage : π '' r = R := by
    rw [← hRr]
    exact image_preimage_eq_of_subset honto
  refine ⟨himage.symm ▸ hR, ?_, ?_⟩
  · rw [himage]
    exact hRr
  · have hh : π '' closure r = closure R := by simpa only [hRr] using hRcl
    exact hh.trans (congrArg closure himage.symm)

/-- Taking region images is a bijection under the actual collapse,
with inverse given by region preimages and exact closure images.
This does not assume that any facial closure is a disc. -/
theorem exists_region_equiv_of_cylinder_contraction
    {S : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    {G G' : Drawing S} (π : C(S, S)) (s : S)
    (hinj : ∀ x y, π x ≠ s → π y ≠ s → π x = π y → x = y)
    (hsurj : ∀ z, z ≠ s → ∃ x, π x = z)
    (hs : s ∈ G'.U) (hfibre : π ⁻¹' {s} ⊆ G.U) (hU : G'.U = π '' G.U) :
    ∃ e : G.R ≃ G'.R,
      (∀ r, (e r).val = π '' r.val) ∧
      (∀ r, (e.symm r).val = π ⁻¹' r.val) ∧
      ∀ r, π '' closure r.val = closure (e r).val := by
  let f : G.R → G'.R := fun r =>
    ⟨π '' r.val, (image_region_of_cylinder_contraction π s hinj hsurj hs hfibre hU r.property).1⟩
  have hpre : ∀ r : G.R, π ⁻¹' (f r).val = r.val := fun r =>
    (image_region_of_cylinder_contraction π s hinj hsurj hs hfibre hU r.property).2.1
  have hfi : Function.Injective f := by
    intro r t hrt
    apply Subtype.ext
    rw [← hpre r, ← hpre t]
    exact congrArg (fun z : G'.R => π ⁻¹' z.val) hrt
  have hfs : Function.Surjective f := by
    intro r
    obtain ⟨hrpre, _⟩ := preimage_region_of_contraction π s hinj hsurj hs hfibre hU r.property
    refine ⟨⟨π ⁻¹' r.val, hrpre⟩, Subtype.ext ?_⟩
    apply image_preimage_eq_of_subset
    intro z hz
    apply hsurj z
    intro heq
    exact region_subset r.property hz (heq.symm ▸ hs)
  let e := Equiv.ofBijective f ⟨hfi, hfs⟩
  refine ⟨e, fun _ => rfl, ?_, ?_⟩
  · intro r
    have hh := hpre (e.symm r)
    change π ⁻¹' (e (e.symm r)).val = (e.symm r).val at hh
    rw [e.apply_symm_apply] at hh
    exact hh.symm
  · intro r
    exact (image_region_of_cylinder_contraction π s hinj hsurj hs hfibre hU r.property).2.2

/-- Lemma 9 of our proof of VI (5.7), specialized to the exact
fibre and complement properties of Reduction 3's rectangular collapse. -/
theorem exists_initial_edge_collapse_region_equiv
    {k : ℕ} {G G' : Drawing ClosedCylinder} {i : Fin k}
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure a)
    (hi : InjOn π (closure a)ᶜ)
    (hsurj : ∀ z, z ≠ cylinderM1Point k i → ∃ x ∉ closure a, π x = z)
    (hs : cylinderM1Point k i ∈ G'.U) (hU : G'.U = π '' G.U) :
    ∃ e : G.R ≃ G'.R,
      (∀ r, (e r).val = π '' r.val) ∧
      (∀ r, (e.symm r).val = π ⁻¹' r.val) ∧
      ∀ r, π '' closure r.val = closure (e r).val := by
  have hoff : ∀ x, π x ≠ cylinderM1Point k i → x ∉ closure a := by
    intro x hx hxa
    have hx' : x ∈ π ⁻¹' {cylinderM1Point k i} := hfiber.symm ▸ hxa
    exact hx hx'
  apply exists_region_equiv_of_cylinder_contraction π (cylinderM1Point k i)
    (fun x y hx hy heq => hi (hoff x hx) (hoff y hy) heq)
    (fun z hz => by obtain ⟨x, _, hx⟩ := hsurj z hz; exact ⟨x, hx⟩) hs ?_ hU
  rw [hfiber]
  exact G.closure_subset_U hl.edge_mem

end GraphMinor.GM06
