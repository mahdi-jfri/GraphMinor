module

public import GraphMinor.GM06.Section5CappedCollapse
public import GraphMinor.GM06.Section5ContractedRegionEquiv
import GraphMinor.GM06.Alg511AdjoinCuffs
import GraphMinor.GM06.Section5Red
import GraphMinor.GM19.Section6Contract

/-!
# The cuff-augmented drawing under the actual collapse

The rotations used in VI (5.7), page 133, include both cuffs and
are read on the sphere. Adjoining the cuffs commutes with a
boundary-fixing collapse. The resulting sphere drawing has exactly
the image vertices and surviving image edges. Its regions have the
same image and closure correspondence as the ordinary drawing.

The edge-image assertion uses the homeomorphism away from the
closed contracted edge. It allows loops among the retained edges
and does not impose valency one on the augmented source.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- Exact image point and vertex sets determine the surviving image
edges when the only nonsingleton fibre is a closed non-loop edge.
The remaining edges may be loops, including loops at its ends. -/
theorem edges_eq_of_closed_edge_collapse
    {S : Type} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    {G G' : Drawing S} {e : Set S} {s v : S}
    (hl : G.toGraph.IsLink e s v) (hvs : v ≠ s)
    (π : C(S, S)) (hfibre : π ⁻¹' {s} = closure e)
    (hi : InjOn π (closure e)ᶜ)
    (hU : G'.U = π '' G.U) (hV : G'.V = π '' G.V) :
    G'.E = (image π) '' (G.E \ {e}) := by
  classical
  let : Nonempty S := ⟨s⟩
  have hscl : s ∈ closure e := by
    rw [closure_edge_eq_union_ends G hl hvs.symm]
    exact Or.inr (mem_insert _ _)
  have hπcl : ∀ x ∈ closure e, π x = s := fun x hx =>
    show x ∈ π ⁻¹' {s} from hfibre.symm ▸ hx
  have hπoff : ∀ x ∉ closure e, π x ≠ s := fun x hx heq => hx (hfibre ▸ heq)
  have hsimage : s ∈ π '' G.V := ⟨s, hl.left_mem, hπcl s hscl⟩
  let J := G.deleteEdge e
  have hJU : J.U = G.U \ e := deleteEdge_U G hl.edge_mem
  have hJV : J.V = G.V :=
    Subset.antisymm (deleteEdge_isSubdrawing G e).1 (fun _ hx => Or.inl ⟨hx, hx⟩)
  have hJE : arcComponentsIn (J.U \ J.V) = G.E \ {e} := deleteEdge_E G e
  have hoff : J.U \ J.V ⊆ (closure e)ᶜ := by
    rintro x ⟨hx, hxV⟩ hxcl
    rw [hJU] at hx
    rw [hJV] at hxV
    exact hx.2 (by rw [← G.closure_diff_V hl.edge_mem]; exact ⟨hxcl, hxV⟩)
  have himage : G'.U \ G'.V = π '' (J.U \ J.V) := by
    rw [hU, hV, hJU, hJV]
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hyV⟩
      refine ⟨y, ⟨⟨hy, ?_⟩, fun h => hyV ⟨y, h, rfl⟩⟩, rfl⟩
      intro hye
      exact hyV ((hπcl y (subset_closure hye)).symm ▸ hsimage)
    · rintro ⟨y, ⟨⟨hy, hye⟩, hyV⟩, rfl⟩
      refine ⟨⟨y, hy, rfl⟩, ?_⟩
      rintro ⟨z, hzV, hzy⟩
      have hyoff : y ∉ closure e := by
        intro hycl
        exact hye (by rw [← G.closure_diff_V hl.edge_mem]; exact ⟨hycl, hyV⟩)
      have hzoff : z ∉ closure e := fun hzc =>
        hπoff y hyoff (hzy.symm.trans (hπcl z hzc))
      exact hyV (hi hzoff hyoff hzy ▸ hzV)
  let g : S → S := Function.invFunOn π (closure e)ᶜ
  have hleft : LeftInvOn g π (closure e)ᶜ := hi.leftInvOn_invFunOn
  have hgc : ContinuousOn g (π '' (closure e)ᶜ) := by
    rw [continuousOn_iff_isClosed]
    intro C hC
    refine ⟨π '' (C ∪ closure e), π.continuous.isClosedMap _ (hC.union isClosed_closure), ?_⟩
    ext y
    constructor
    · rintro ⟨hyC, hyr⟩
      refine ⟨?_, hyr⟩
      obtain ⟨x, hx, rfl⟩ := hyr
      exact ⟨g (π x), Or.inl hyC, by rw [hleft hx]⟩
    · rintro ⟨⟨x, hx, rfl⟩, hyr⟩
      refine ⟨?_, hyr⟩
      obtain ⟨z, hz, hzx⟩ := hyr
      have hxoff : x ∉ closure e := fun h => hπoff z hz (hzx.trans (hπcl x h))
      have hxC : x ∈ C := hx.resolve_right hxoff
      change g (π x) ∈ C
      rw [hleft hxoff]
      exact hxC
  change arcComponentsIn (G'.U \ G'.V) = _
  rw [himage, GM19.arcComponentsIn_image_eq π.continuous.continuousOn
    (hgc.mono (image_mono hoff)) (hleft.mono hoff), hJE]

/-- A given cuff augmentation, including its actual old rotation
curves, has an image cuff augmentation under a boundary-fixed
initial-edge collapse. No new choice of the old drawing is needed. -/
theorem exists_cuff_augmentation_of_closed_edge_collapse
    {k : ℕ} {G G' F : Drawing ClosedCylinder} {e : Set ClosedCylinder}
    {s v : ClosedCylinder}
    (hG' : IsCylinderSection5Drawing k G')
    (hGF : G.IsSubdrawing F) (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V)
    (hl : G.toGraph.IsLink e s v) (hvs : v ≠ s)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfibre : π ⁻¹' {s} = closure e) (hi : InjOn π (closure e)ᶜ)
    (hbd : ∀ x ∈ bd ClosedCylinder, π x = x)
    (hU : G'.U = π '' G.U) (hV : G'.V = π '' G.V) :
    ∃ F' : Drawing ClosedCylinder,
      G'.IsSubdrawing F' ∧ F'.U = G'.U ∪ bd ClosedCylinder ∧ F'.V = G'.V ∧
      F'.U = π '' F.U ∧ F'.V = π '' F.V ∧ F'.E = (image π) '' (F.E \ {e}) := by
  obtain ⟨F', _, _, hG'F', hF'U, hF'V, _⟩ := alg511_exists_drawing_with_cuffs hG'
  have hboundary : π '' bd ClosedCylinder = bd ClosedCylinder := by
    apply subset_antisymm
    · rintro y ⟨x, hx, rfl⟩
      rw [hbd x hx]
      exact hx
    · intro x hx
      exact ⟨x, hx, hbd x hx⟩
  have hFUimage : F'.U = π '' F.U := by
    rw [hF'U, hFU, image_union, hboundary, hU]
  have hFVimage : F'.V = π '' F.V := by rw [hF'V, hFV, hV]
  have hlF : F.toGraph.IsLink e s v := by
    refine ⟨hGF.2 hl.edge_mem, ?_⟩
    simpa only [hFV] using hl.2
  exact ⟨F', hG'F', hF'U, hF'V, hFUimage, hFVimage,
    edges_eq_of_closed_edge_collapse hlF hvs π hfibre hi hFUimage hFVimage⟩

/-- The capped version of the same edge collapse has the exact
vertex and edge images needed to interpret the permanent rotation
words. Its region bijection includes full preimages and closure
images, even when a region boundary repeats vertices. -/
theorem cylinderSphereDrawing_closed_edge_collapse
    {F F' : Drawing ClosedCylinder} {e : Set ClosedCylinder}
    {s v : ClosedCylinder} (hl : F.toGraph.IsLink e s v) (hvs : v ≠ s)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfibre : π ⁻¹' {s} = closure e) (hi : InjOn π (closure e)ᶜ)
    (hsurj : Function.Surjective π)
    (hU : F'.U = π '' F.U) (hV : F'.V = π '' F.V)
    (πS : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (hπS : ∀ x, πS (cylinderToSphere x) = cylinderToSphere (π x))
    (hoff : ∀ y ∉ range cylinderToSphere, πS y = y) :
    let Γ := cylinderSphereDrawing F
    let Γ' := cylinderSphereDrawing F'
    let a := cylinderToSphere '' e
    πS ⁻¹' {cylinderToSphere s} = closure a ∧
    InjOn πS (closure a)ᶜ ∧ Function.Surjective πS ∧
    Γ'.U = πS '' Γ.U ∧ Γ'.V = πS '' Γ.V ∧
    Γ'.E = (image πS) '' (Γ.E \ {a}) ∧
    ∃ η : Γ.R ≃ Γ'.R,
      (∀ r, (η r).val = πS '' r.val) ∧
      (∀ r, (η.symm r).val = πS ⁻¹' r.val) ∧
      ∀ r, πS '' closure r.val = closure (η r).val := by
  have hcl : closure (cylinderToSphere '' e) = cylinderToSphere '' closure e :=
    isClosedEmbedding_cylinderToSphere.isClosedMap.closure_image_eq_of_continuous
      continuous_cylinderToSphere e
  have hfibreS : πS ⁻¹' {cylinderToSphere s} = closure (cylinderToSphere '' e) := by
    rw [hcl]
    exact fibre_of_capped_cylinder_collapse hπS hoff hfibre
  have hiS : InjOn πS (closure (cylinderToSphere '' e))ᶜ := by
    rw [hcl]
    exact injOn_of_capped_cylinder_collapse hπS hoff hi
  have hsurjS := surjective_of_capped_cylinder_collapse hπS hoff hsurj
  have hcomm (A : Set ClosedCylinder) :
      cylinderToSphere '' (π '' A) = πS '' (cylinderToSphere '' A) := by
    rw [image_image, image_image]
    exact image_congr (fun x _ => (hπS x).symm)
  have hUS : (cylinderSphereDrawing F').U = πS '' (cylinderSphereDrawing F).U := by
    rw [cylinderSphereDrawing_U, cylinderSphereDrawing_U, hU, hcomm]
  have hVS : (cylinderSphereDrawing F').V = πS '' (cylinderSphereDrawing F).V := by
    rw [cylinderSphereDrawing_V, cylinderSphereDrawing_V, hV, hcomm]
  have hlS : (cylinderSphereDrawing F).toGraph.IsLink
      (cylinderToSphere '' e) (cylinderToSphere s) (cylinderToSphere v) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [cylinderSphereDrawing_E]
      exact mem_image_of_mem (image cylinderToSphere) hl.edge_mem
    · rw [cylinderSphereDrawing_V]
      exact mem_image_of_mem cylinderToSphere hl.left_mem
    · rw [cylinderSphereDrawing_V]
      exact mem_image_of_mem cylinderToSphere hl.right_mem
    · rw [hcl, cylinderSphereDrawing_V, ← image_inter injective_cylinderToSphere,
        hl.2.2.2, image_pair]
  have hES := edges_eq_of_closed_edge_collapse hlS
    (fun heq => hvs (injective_cylinderToSphere heq)) πS hfibreS hiS hUS hVS
  have hscl : cylinderToSphere s ∈ closure (cylinderToSphere '' e) := by
    rw [closure_edge_eq_union_ends (cylinderSphereDrawing F) hlS
      (show cylinderToSphere s ≠ cylinderToSphere v from
        fun heq => hvs (injective_cylinderToSphere heq.symm))]
    exact Or.inr (mem_insert _ _)
  have hπs : πS (cylinderToSphere s) = cylinderToSphere s :=
    show cylinderToSphere s ∈ πS ⁻¹' {cylinderToSphere s} from hfibreS.symm ▸ hscl
  have hsNew : cylinderToSphere s ∈ (cylinderSphereDrawing F').U := by
    rw [hUS, ← hπs]
    exact mem_image_of_mem πS ((cylinderSphereDrawing F).V_subset_U hlS.left_mem)
  have hnot : ∀ x, πS x ≠ cylinderToSphere s → x ∉ closure (cylinderToSphere '' e) :=
    fun x hx hxe => hx (show x ∈ πS ⁻¹' {cylinderToSphere s} from hfibreS.symm ▸ hxe)
  obtain ⟨η, hη, hηinv, hηcl⟩ := exists_region_equiv_of_cylinder_contraction πS
    (cylinderToSphere s) (fun x y hx hy heq => hiS (hnot x hx) (hnot y hy) heq)
    (fun y _ => hsurjS y) hsNew (by
      rw [hfibreS]
      exact (cylinderSphereDrawing F).closure_subset_U hlS.edge_mem) hUS
  exact ⟨hfibreS, hiS, hsurjS, hUS, hVS, hES, η, hη, hηinv, hηcl⟩

end GraphMinor.GM06
