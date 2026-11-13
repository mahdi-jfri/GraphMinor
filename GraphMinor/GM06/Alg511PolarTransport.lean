module

public import GraphMinor.GM06.Alg511CuffRotations
public import GraphMinor.GM07.Section9MoveOff
public import Mathlib.Logic.Equiv.Set
import GraphMinor.Surface.PlaneDisc
import Mathlib.Tactic

/-!
# Transporting labelled polar data through an ambient homeomorphism

For the orientation step of VI (5.11), page 134, original edge
labels and their parameter directions stay fixed when the drawing
is carried by the ambient map. Transport every edge curve and
both ends of each edge, including loops. The resulting half-edge
bijection keeps its ordinary directed labels and carries every
spoke point to its image. Polar discs are carried by the same map.
The atom calculation needed for their rays concerns the drawing
itself and uses no encoded region rows.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u v
variable {S : Type u} {T : Type v} [TopologicalSpace S] [TopologicalSpace T]

private theorem homeo_symm_image_image (H : S ≃ₜ T) (e : Set S) :
    H.symm '' (H '' e) = e := by
  ext p
  constructor
  · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    simpa only [H.symm_apply_apply] using hr
  · intro hp
    exact ⟨H p, mem_image_of_mem H hp, H.symm_apply_apply p⟩

/-- Carry every edge parameter through the ambient homeomorphism.
The inverse image identifies which original edge is parametrized. -/
@[expose] noncomputable def alg511ImageEdgePar (H : S ≃ₜ T) (γ : Set S → I → S)
    (e : Set T) (t : I) : T := H (γ (H.symm '' e) t)

/-- On an image edge the transported curve is exactly the image
of its original curve, with the same parameter value. -/
theorem alg511ImageEdgePar_image (H : S ≃ₜ T) (γ : Set S → I → S) (e : Set S) (t : I) :
    alg511ImageEdgePar H γ (H '' e) t = H (γ e t) := by
  rw [alg511ImageEdgePar, homeo_symm_image_image H]

variable [T2Space S] [T2Space T] [Nonempty S]

/-- Ambient transport gives a genuine parametrization of every
edge of the image drawing. -/
theorem alg511_image_edgePar (H : S ≃ₜ T) {Γ : Drawing S} {γ : Set S → I → S}
    (hγ : EdgePar Γ γ) : EdgePar (GM07.embedDrawing H.isClosedEmbedding Γ) (alg511ImageEdgePar H γ) := by
  have heq : ∀ e : Set S, alg511ImageEdgePar H γ (H '' e) = fun t => H (γ e t) :=
    fun e => funext (alg511ImageEdgePar_image H γ e)
  constructor
  · intro e he
    obtain ⟨f, hf, rfl⟩ := (GM07.embedDrawing_E H.isClosedEmbedding Γ) ▸ he
    rw [heq]
    exact H.continuous.comp (hγ.cont f hf)
  · intro e he
    obtain ⟨f, hf, rfl⟩ := (GM07.embedDrawing_E H.isClosedEmbedding Γ) ▸ he
    rw [alg511ImageEdgePar_image, GM07.embedDrawing_V]
    exact mem_image_of_mem H (hγ.zero f hf)
  · intro e he
    obtain ⟨f, hf, rfl⟩ := (GM07.embedDrawing_E H.isClosedEmbedding Γ) ▸ he
    rw [alg511ImageEdgePar_image, GM07.embedDrawing_V]
    exact mem_image_of_mem H (hγ.one f hf)
  · intro e he
    obtain ⟨f, hf, rfl⟩ := (GM07.embedDrawing_E H.isClosedEmbedding Γ) ▸ he
    rw [heq]
    intro s hs t ht heq
    exact hγ.inj f hf hs ht (H.injective heq)
  · intro e he
    obtain ⟨f, hf, rfl⟩ := (GM07.embedDrawing_E H.isClosedEmbedding Γ) ▸ he
    rw [heq, ← image_image, hγ.image f hf]

/-- The edge bijection induced by the ambient homeomorphism. -/
@[expose] noncomputable def alg511ImageEdgeEquiv (H : S ≃ₜ T) (Γ : Drawing S) :
    Γ.E ≃ (GM07.embedDrawing H.isClosedEmbedding Γ).E :=
  (Equiv.Set.image (image H) Γ.E (Set.image_injective.mpr H.injective)).trans
    (Set.equivOfEq (GM07.embedDrawing_E H.isClosedEmbedding Γ).symm)

/-- A labelled edge keeps exactly its image point set. -/
theorem alg511ImageEdgeEquiv_val (H : S ≃ₜ T) (Γ : Drawing S) (e : Γ.E) :
    (alg511ImageEdgeEquiv H Γ e).val = H '' e.val := rfl

/-- Carry an actual half-edge while retaining its Boolean end.
Applying the inverse map gives the inverse half-edge bijection. -/
@[expose] noncomputable def alg511ImageHalfEdges (H : S ≃ₜ T) (Γ : Drawing S)
    (γ : Set S → I → S) (z : S) :
    halfEdges Γ γ z ≃ halfEdges (GM07.embedDrawing H.isClosedEmbedding Γ) (alg511ImageEdgePar H γ) (H z) where
  toFun a := ⟨(H '' a.val.1, a.val.2), by
    refine ⟨?_, ?_⟩
    · rw [GM07.embedDrawing_E]
      exact mem_image_of_mem (image H) a.property.1
    · change alg511ImageEdgePar H γ (H '' a.val.1) (endOf a.val.2) = H z
      rw [alg511ImageEdgePar_image]
      exact congrArg H a.property.2⟩
  invFun a := ⟨(H.symm '' a.val.1, a.val.2), by
    refine ⟨?_, ?_⟩
    · have hm := a.property.1
      rw [GM07.embedDrawing_E] at hm
      obtain ⟨e, he, heq⟩ := hm
      rw [← heq]
      change H.symm '' (H '' e) ∈ Γ.E
      rw [homeo_symm_image_image H]
      exact he
    · exact H.injective a.property.2⟩
  left_inv a := by exact Subtype.ext (Prod.ext (homeo_symm_image_image H _) rfl)
  right_inv a := by exact Subtype.ext (Prod.ext (homeo_symm_image_image H.symm _) rfl)

/-- The transported half-edge has the same finite directed label,
including either one of the two ends of a loop. -/
theorem alg511ImageHalfEdges_label (H : S ≃ₜ T) {Γ : Drawing S} {m : ℕ}
    (edge : Fin m ≃ Γ.E) (γ : Set S → I → S) (z : S) (a : halfEdges Γ γ z) :
    halfEdgeLabel (edge.trans (alg511ImageEdgeEquiv H Γ)) (alg511ImageHalfEdges H Γ γ z a) =
      halfEdgeLabel edge a := by
  change 2 * (edge.symm ((alg511ImageEdgeEquiv H Γ).symm
      ((alg511ImageEdgeEquiv H Γ) ⟨a.val.1, a.property.1⟩))).val + a.val.2.toNat = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The entire transported spoke has the exact original parameter
and the exact image point, rather than merely the same endpoint. -/
theorem alg511ImageHalfEdges_spoke (H : S ≃ₜ T) {Γ : Drawing S}
    (γ : Set S → I → S) (z : S) (a : halfEdges Γ γ z) (t : I) :
    spoke (alg511ImageEdgePar H γ) (alg511ImageHalfEdges H Γ γ z a).val t =
      H (spoke γ a.val t) := by
  exact alg511ImageEdgePar_image H γ a.val.1 _

private theorem image_atom (H : S ≃ₜ T) (Γ : Drawing S) {a : Set S} (ha : a ∈ Γ.A) :
    H '' a ∈ (GM07.embedDrawing H.isClosedEmbedding Γ).A := by
  rcases ha with (⟨p, hp, rfl⟩ | he) | hr
  · apply Or.inl
    apply Or.inl
    exact ⟨H p, by rw [GM07.embedDrawing_V]; exact mem_image_of_mem H hp,
      (image_singleton : H '' {p} = {H p}).symm⟩
  · apply Or.inl
    apply Or.inr
    rw [GM07.embedDrawing_E]
    exact mem_image_of_mem (image H) he
  · apply Or.inr
    change H '' a ∈ componentsIn (univ \ (GM07.embedDrawing H.isClosedEmbedding Γ).U)
    rw [GM07.embedDrawing_U, ← compl_eq_univ_sdiff, ← image_compl_eq H.bijective,
      componentsIn_image H.continuous.continuousOn H.symm.continuous.continuousOn
        (fun p _ => H.symm_apply_apply p)]
    apply mem_image_of_mem (image H)
    simpa only [Drawing.R, ← compl_eq_univ_sdiff] using hr

/-- The polar chart carried through the same ambient map. -/
@[expose] noncomputable def alg511ImagePolarChart (H : S ≃ₜ T) (Φ : C(ClosedUnitDisc, S)) :
    C(ClosedUnitDisc, T) := (⟨H, H.continuous⟩ : C(S, T)).comp Φ

/-- An ambient homeomorphism carries a polar chart to a polar
chart of the image drawing, including all of its drawing rays. -/
theorem alg511_isPolar_image (H : S ≃ₜ T) {Γ : Drawing S} {z : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ z Φ) :
    IsPolar (GM07.embedDrawing H.isClosedEmbedding Γ) (H z) (alg511ImagePolarChart H Φ) := by
  refine ⟨H.injective.comp hp.inj, ?_, ?_, ?_⟩
  · change H (Φ polarCentre) = H z
    rw [hp.centre]
  · change H z ∈ interior (range (H ∘ Φ))
    rw [range_comp, ← H.image_interior]
    exact mem_image_of_mem H hp.nhd
  · intro x hx c hc
    obtain ⟨a, ha, hx', hc'⟩ := hp.ray x hx c hc
    exact ⟨H '' a, image_atom H Γ ha, mem_image_of_mem H hx', mem_image_of_mem H hc'⟩

end GraphMinor.GM06
