module

public import GraphMinor.GM08.Section11Transport
public import GraphMinor.GM07.Defs
public import GraphMinor.Surface.Defs
import GraphMinor.GM07.Section3
import GraphMinor.GM08.Section4

/-!
# Transferring the minor of VIII (9.3) to abstract grafts

A homeomorphism of the disc gives a bijection of the drawing graphs.
Compose it with the original drawing isomorphism, then transfer the
boundary-rooted minor model back through the host drawing isomorphism.
A root is sent to the branch containing its matching boundary vertex.
-/

public section

namespace GraphMinor.GM08

open Set Surface Graph

universe u v u' v' w

/-- Graph bijections compose, so the map matching boundary roots may
be composed with the original drawing isomorphism in VIII (9.3). -/
theorem IsGraphBij.trans {α β γ δ ε ζ : Type*}
    {G : Graph α β} {H : Graph γ δ} {K : Graph ε ζ}
    {f : α → γ} {g : β → δ} {f' : γ → ε} {g' : δ → ζ}
    (h : IsGraphBij G H f g) (h' : IsGraphBij H K f' g') :
    IsGraphBij G K (f' ∘ f) (g' ∘ g) where
  bijV := h'.bijV.comp h.bijV
  bijE := h'.bijE.comp h.bijE
  isLink e he x hx y hy := (h.isLink e he x hx y hy).trans
    (h'.isLink (g e) (h.bijE.mapsTo he) (f x) (h.bijV.mapsTo hx) (f y) (h.bijV.mapsTo hy))

/-- A homeomorphism gives the expected bijection of drawing graphs,
used for the boundary adjustment in VIII (9.3), page 270. -/
theorem isGraphBij_mapDrawingHomeo {S : Type u} {S' : Type v}
    [TopologicalSpace S] [TopologicalSpace S'] (α : S ≃ₜ S') (D : Drawing S) :
    IsGraphBij D.toGraph (GM07.mapDrawingHomeo α D).toGraph α (image α) where
  bijV := ⟨fun _ hx => mem_image_of_mem α hx, α.injective.injOn,
    fun _ ⟨x, hx, heq⟩ => ⟨x, hx, heq⟩⟩
  bijE := by
    rw [show E((GM07.mapDrawingHomeo α D).toGraph) = (image α) '' D.E from
      GM07.mapDrawingHomeo_E α D]
    exact ⟨fun _ hx => mem_image_of_mem (image α) hx,
      (image_injective.mpr α.injective).injOn, fun _ ⟨e, he, heq⟩ => ⟨e, he, heq⟩⟩
  isLink e _ x _ y _ := by
    constructor
    · exact GM07.mapDrawingHomeo_isLink α
    · intro hl
      have h := GM07.mapDrawingHomeo_isLink α.symm hl
      rw [GM07.mapDrawingHomeo_symm_mapDrawingHomeo] at h
      have heq : α.symm '' (α '' e) = e := by
        simp only [image_image, α.symm_apply_apply, image_id']
      simpa only [α.symm_apply_apply, heq] using h

/-- Transfer the model used in VIII (9.3) to the abstract grafts.
The root branch contains the boundary vertex itself before the transfer. -/
theorem isGraftSimulatedIn_of_drawing_model {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'} {S : Type w}
    [TopologicalSpace S] [Nonempty S] [Nonempty β]
    {Y : Graft α' β'} {X : Graft α β} (gd : GraftDrawing X.G X.T S)
    {H : Drawing S} {f : α' → S} {g : β' → Set S}
    (hbij : IsGraphBij Y.G H.toGraph f g)
    (hbd : H.V ∩ bd S = gd.drawing.V ∩ bd S)
    (hroot : ∀ v ∈ Y.T, f v ∈ bd S)
    {ηv : S → Set S} {ηe : Set S → Set S}
    (hm : IsMinorModel H.toGraph gd.drawing.toGraph ηv ηe)
    (hmroot : ∀ v ∈ H.V ∩ bd S, v ∈ ηv v)
    (hk : X.index = Y.index) : IsGraftSimulatedIn Y X := by
  classical
  have m := (isGraphSimulation_comp hbij.isMinorModel hm).pullHost
    gd.iso.isGraphBij (fun _ => Classical.arbitrary β)
  refine ⟨_, _, m, hk, ?_⟩
  intro v hv
  have hvH : f v ∈ H.V := hbij.bijV.mapsTo (Y.T_subset hv)
  have hvbd : f v ∈ H.V ∩ bd S := ⟨hvH, hroot v hv⟩
  have hvG : f v ∈ gd.drawing.V := (hbd ▸ hvbd).1
  obtain ⟨x, hx, hxf⟩ := gd.iso.exists_fv hvG
  refine ⟨x, ⟨hx, ?_⟩, ?_⟩
  · rw [hxf]
    exact mem_biUnion (mem_singleton (f v)) (hmroot (f v) hvbd)
  · exact (gd.mem_bd_iff x hx).mp (by rw [← gd.iso.fv_of_mem hx, hxf]; exact hroot v hv)

end GraphMinor.GM08
