module

public import GraphMinor.GM06.Section5PolarHalfedgeEquiv
import GraphMinor.GM06.Section5PolarEdgeAccess
import GraphMinor.GM11.Walks

/-!
# Subdrawing points on the polar rim are its directed ends

For the barrier in VI (5.7), page 133, the rim meets the linkage
and cuffs in exactly their incident directed ends. A noncentral
point of a polar chart cannot be a drawing vertex, since radial
scaling would keep it at that vertex and violate injectivity.
Every subdrawing point on the rim is therefore an edge point.
The edge correspondence then identifies its directed-end label.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- The polar rim contains no drawing vertex. -/
theorem polar_rim_not_mem_vertices
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {v : S} {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    (w : Circle) : polarRimMap Φ w ∉ Γ.V := by
  intro hw
  let c : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have hc : 0 < c := by change (0 : ℝ) < 1 / 2; norm_num
  have ha : ({polarRimMap Φ w} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨_, hw, rfl⟩)
  have hh := (polar_ray_mem_atom_iff hp ha (polarDiscPoint_one_ne_centre w) c hc).mp
    (mem_singleton (polarRimMap Φ w))
  rw [discScale_polarDiscPoint_one] at hh
  have heq : polarRayMap Φ w c = polarRayMap Φ w 1 := mem_singleton_iff.mp hh
  have hcone : c = 1 := (isArcMap_polarRayMap hp.inj w).2 heq
  have hcval := congrArg Subtype.val hcone
  norm_num [c] at hcval

/-- A polar ray whose rim lies in a closed subdrawing remains in
that subdrawing along its whole radial segment. -/
theorem polar_ray_range_subset_subdrawing_of_rim_mem
    {S : Type u} [TopologicalSpace S] [T2Space S] [LocallyConnectedSpace S]
    {Γ T : Drawing S} (hT : T.IsSubdrawing Γ) {v : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ) (w : Circle)
    (hw : polarRimMap Φ w ∈ T.U) : range (polarRayMap Φ w) ⊆ T.U := by
  have hn : IsGammaNice Γ T.U := isGammaNice_of_frontier hT subset_rfl
    (frontier_subset_closure.trans (by rw [T.isClosed_U.closure_eq]))
  rintro _ ⟨r, rfl⟩
  have hh := hp.star T.isClosed_U hn hw r
  rwa [discScale_polarDiscPoint_one] at hh

/-- A labelled polar ray belongs to a subdrawing at its rim exactly
when its directed end's edge is retained in that subdrawing. -/
theorem polar_rim_mem_subdrawing_iff_halfedge_edge_mem
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {Γ T : Drawing S} (hT : T.IsSubdrawing Γ)
    {γ : Set S → I → S} (hγ : EdgePar Γ γ)
    {v : S} {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    (a : halfEdges Γ γ v) (w : Circle)
    (hw : ∀ t : I, 0 < t → Φ (polarDiscPoint t w) ∈ range (spoke γ a.1)) :
    polarRimMap Φ w ∈ T.U ↔ a.1.1 ∈ T.E := by
  have hwa := polar_rim_mem_edge_of_halfedge_ray hγ hp a w hw
  constructor
  · intro hwT
    have hwV : polarRimMap Φ w ∉ T.V := fun hh => polar_rim_not_mem_vertices hp w (hT.1 hh)
    obtain ⟨e, he, hwe⟩ := T.exists_edge_of_mem hwT hwV
    have hae : a.1.1 = e := Γ.edge_eq_of_mem a.2.1 (hT.2 he) hwa hwe
    exact hae.symm ▸ he
  · intro haT
    exact (haT.2.1 hwa).1

/-- The polar rim of a subdrawing is precisely the image of its
incident directed ends under the geometric rim labelling. -/
theorem polar_rim_subdrawing_eq_image_halfedges
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {Γ T : Drawing S} (hT : T.IsSubdrawing Γ)
    {γ : Set S → I → S} (hγ : EdgePar Γ γ)
    {v : S} {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    (d : halfEdges Γ γ v ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e})
    (hd : ∀ a, ∀ t : I, 0 < t → Φ (polarDiscPoint t (d a).1) ∈ range (spoke γ a.1)) :
    (polarRimMap Φ) ⁻¹' T.U = (fun a => (d a).1) '' {a | a.1.1 ∈ T.E} := by
  ext w
  constructor
  · intro hwT
    have hwU : polarRimMap Φ w ∈ Γ.U := hT.U_subset hwT
    obtain ⟨e, he, hwe⟩ := Γ.exists_edge_of_mem hwU (polar_rim_not_mem_vertices hp w)
    let w' : {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e} := ⟨w, e, he, hwe⟩
    let a := d.symm w'
    have haw : (d a).1 = w := congrArg Subtype.val (d.apply_symm_apply w')
    refine ⟨a, ?_, haw⟩
    apply (polar_rim_mem_subdrawing_iff_halfedge_edge_mem hT hγ hp a (d a).1 (hd a)).mp
    rwa [haw]
  · rintro ⟨a, haT, rfl⟩
    exact (polar_rim_mem_subdrawing_iff_halfedge_edge_mem hT hγ hp a (d a).1 (hd a)).mpr haT

end GraphMinor.GM06
