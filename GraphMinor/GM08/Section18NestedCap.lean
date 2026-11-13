module

public import GraphMinor.GM08.Section15Defs
public import GraphMinor.GM12.Section3Punctured
import GraphMinor.GM08.Section15PuncturedCylinder
import GraphMinor.GM07.Section9DiscSphere
import GraphMinor.GM11.PerimeterPull
import GraphMinor.GM11.GlueDiscs
import GraphMinor.GM12.Section3ModelComplexity
import GraphMinor.GM12.Section3PuncturedBoundary
import GraphMinor.GM16.SpanTransport

/-!
# The cylinder left by two discs of a sphere, with its cap

Remove the interiors of two disjoint closed discs `P₁, P₂` from a sphere `Z`.
What is left is a cylinder `Q`. The sphere itself, moved to the model sphere,
caps `Q` with the discs `P₁` and `P₂` (`exists_nestedCap`). So hoops of `Q`
and their sides can be read in `Z`: an `O`-arc of `Q` that bounds a disc of
`Z` around `P₁` and a disc around `P₂` is a hoop, and these are its two discs
(`isHoop_of_discs`). The split step of (18.3), page 287, frames the inner
piece of a graft in such a cylinder.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe u

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ConnectedSpace Z]

/-- **The cap of the cylinder between two discs of a sphere.** -/
theorem exists_nestedCap (hZ : IsClosedSurface Z) (hsph : IsSphere Z) {P₁ P₂ : Set Z}
    (h₁ : IsClosedDisc P₁) (h₂ : IsClosedDisc P₂) (hd : Disjoint P₁ P₂) :
    IsCylinder (GM12.discComplement ![P₁, P₂]) ∧
      ∃ (cap : CylinderSphereCap (GM12.discComplement ![P₁, P₂])) (e : Z ≃ₜ cap.Z),
        (∀ q, cap.j q = e q.1) ∧ cap.D₁ = e '' P₁ ∧ cap.D₂ = e '' P₂ := by
  classical
  set Q := GM12.discComplement ![P₁, P₂] with hQ
  obtain ⟨hcyl, hcuffs, hne, -⟩ := cylinder_complement_two_discs hZ hsph h₁ h₂ hd
  refine ⟨hcyl, ?_⟩
  obtain ⟨e⟩ := hsph
  have hP : ∀ i, IsClosedDisc ((![P₁, P₂] : Fin 2 → Set Z) i) := by
    intro i; fin_cases i <;> assumption
  have hdis : Pairwise (fun i j => Disjoint ((![P₁, P₂] : Fin 2 → Set Z) i)
      ((![P₁, P₂] : Fin 2 → Set Z) j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hij rfl).elim
  have hmem := GM07.mem_discComplement_iff hZ _ hP hdis
  have hman : ∀ x : Z, IsManifoldPoint x := fun x => (hZ.2.2 x).isManifoldPoint
  have hbQ : ∀ i, discBd ((![P₁, P₂] : Fin 2 → Set Z) i) ⊆ Q :=
    GM12.disc_boundary_subset_discComplement hZ _ hP hdis
  have hQc : IsClosed Q := isClosed_closure
  have hsph' : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hsZ := (GM11.IsSphere.isClosedSurface hsph').1
  have hcZ : ConnectedSpace (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface hsph').2
  have himb : ∀ P : Set Z, P ⊆ Q →
      e '' P = (fun q : Q => e q.1) '' ((Subtype.val : Q → Z) ⁻¹' P) := by
    intro P hPQ
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hPQ hx⟩, hx, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.1, hq, rfl⟩
  have hinter : ∀ i, Q ∩ (![P₁, P₂] : Fin 2 → Set Z) i =
      discBd ((![P₁, P₂] : Fin 2 → Set Z) i) := by
    intro i
    apply subset_antisymm
    · rintro x ⟨hxQ, hxP⟩
      by_contra hb
      exact (hmem x).mp hxQ i ⟨hxP, hb⟩
    · intro x hx
      exact ⟨hbQ i hx, discBd_subset _ hx⟩
  refine ⟨{
    Z := OnePoint EuclideanPlane
    C₁ := (Subtype.val : Q → Z) ⁻¹' discBd P₁
    C₂ := (Subtype.val : Q → Z) ⁻¹' discBd P₂
    C₁_ne_C₂ := hne
    cuffs_eq := hcuffs
    j := fun q => e q.1
    D₁ := e '' P₁
    D₂ := e '' P₂
    isClosedSurface := hsZ
    isSphere := hsph'
    connectedSpace := hcZ
    isClosedEmbedding := e.isClosedEmbedding.comp hQc.isClosedEmbedding_subtypeVal
    isClosedDisc_D₁ := (GM11.isClosedDisc_image h₁ e.continuous.continuousOn e.injective.injOn).1
    isClosedDisc_D₂ := (GM11.isClosedDisc_image h₂ e.continuous.continuousOn e.injective.injOn).1
    disjoint_D := (disjoint_image_iff e.injective).mpr hd
    discBd_D₁ := ?_
    discBd_D₂ := ?_
    union_eq := ?_
    inter_D₁ := ?_
    inter_D₂ := ?_ }, e, fun _ => rfl, rfl, rfl⟩
  · rw [(GM11.isClosedDisc_image h₁ e.continuous.continuousOn e.injective.injOn).2]
    exact himb _ (hbQ 0)
  · rw [(GM11.isClosedDisc_image h₂ e.continuous.continuousOn e.injective.injOn).2]
    exact himb _ (hbQ 1)
  · apply eq_univ_of_forall
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    by_cases h1 : x ∈ P₁
    · exact .inl (.inr ⟨x, h1, rfl⟩)
    by_cases h2 : x ∈ P₂
    · exact .inr ⟨x, h2, rfl⟩
    refine .inl (.inl ⟨⟨x, ?_⟩, rfl⟩)
    refine (hmem x).mpr fun i hi => ?_
    fin_cases i
    · exact h1 hi.1
    · exact h2 hi.1
  · ext y
    constructor
    · rintro ⟨⟨q, rfl⟩, ⟨x, hx, hxe⟩⟩
      refine ⟨q, ?_, rfl⟩
      have : x = q.1 := e.injective hxe
      subst this
      exact (hinter 0).subset ⟨q.2, hx⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, rfl⟩, ⟨q.1, discBd_subset _ hq, rfl⟩⟩
  · ext y
    constructor
    · rintro ⟨⟨q, rfl⟩, ⟨x, hx, hxe⟩⟩
      refine ⟨q, ?_, rfl⟩
      have : x = q.1 := e.injective hxe
      subst this
      exact (hinter 1).subset ⟨q.2, hx⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, rfl⟩, ⟨q.1, discBd_subset _ hq, rfl⟩⟩

/-- **Hoops read in a sphere.** Let `e` carry a sphere `Z` onto the cap sphere
of `Σ`, with `ι : Σ → Z` the matching map. An `O`-arc `H` of `Σ` whose image
in `Z` bounds a closed disc around `P₁` and a closed disc around `P₂`, meeting
in the image of `H` and covering `Z`, is a hoop, and its two discs are the
images of these. -/
theorem CylinderSphereCap.isHoop_of_discs {S : Type*} [TopologicalSpace S]
    (cap : CylinderSphereCap S) (hS : IsSurface S) {W : Type*} [TopologicalSpace W]
    [T2Space W] (e : W ≃ₜ cap.Z) {ι : S → W} (hj : ∀ q, cap.j q = e (ι q)) {P₁ P₂ : Set W}
    (hD₁ : cap.D₁ = e '' P₁) (hD₂ : cap.D₂ = e '' P₂) {H : Set S} (hH : IsOArc H)
    {E₁ E₂ : Set W} (hE₁ : IsClosedDisc E₁) (hE₂ : IsClosedDisc E₂)
    (hb₁ : discBd E₁ = ι '' H) (hb₂ : discBd E₂ = ι '' H) (hcup : E₁ ∪ E₂ = univ)
    (hcap : E₁ ∩ E₂ = ι '' H) (hP₁ : P₁ ⊆ E₁) (hP₂ : P₂ ⊆ E₂) :
    ∃ hHh : IsHoop H, cap.disc₁ hS hHh = e '' E₁ ∧ cap.disc₂ hS hHh = e '' E₂ := by
  have : T2Space cap.Z := cap.t2Space_Z
  have hjH : cap.j '' H = e '' (ι '' H) := by
    rw [image_image]
    exact image_congr fun q _ => hj q
  have hi₁ := GM11.isClosedDisc_image hE₁ e.continuous.continuousOn e.injective.injOn
  have hi₂ := GM11.isClosedDisc_image hE₂ e.continuous.continuousOn e.injective.injOn
  have hb₁' : discBd (e '' E₁) = cap.j '' H := by rw [hi₁.2, hb₁, hjH]
  have hb₂' : discBd (e '' E₂) = cap.j '' H := by rw [hi₂.2, hb₂, hjH]
  have hcup' : e '' E₁ ∪ e '' E₂ = univ := by
    rw [← image_union, hcup, image_univ, e.range_coe]
  have hcap' : e '' E₁ ∩ e '' E₂ = cap.j '' H := by
    rw [← image_inter e.injective, hcap, hjH]
  have hD₁' : cap.D₁ ⊆ e '' E₁ := hD₁ ▸ image_mono hP₁
  have hD₂' : cap.D₂ ⊆ e '' E₂ := hD₂ ▸ image_mono hP₂
  have hHh : IsHoop H := (cap.isHoop_iff_exists_discs hS hH).mpr
    ⟨_, _, hi₁.1, hi₂.1, hb₁', hb₂', hcup', hcap', hD₁', hD₂'⟩
  obtain ⟨s₁, s₂, sb₁, sb₂, -, -, sD₁, sD₂⟩ := cap.disc₁_disc₂_spec hS hHh
  exact ⟨hHh, cap.hoop_discs_unique hi₁.1 hi₂.1 hb₁' hb₂' hcap' hD₁' hD₂' s₁ s₂ sb₁ sb₂ sD₁ sD₂⟩

end GraphMinor.GM08
