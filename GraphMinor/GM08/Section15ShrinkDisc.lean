module

public import GraphMinor.Surface.Defs
import GraphMinor.Surface.CutIArc
import GraphMinor.Surface.AddCrosscap
import GraphMinor.Surface.InvarianceOfDomain
import GraphMinor.GM07.Taper

/-!
# Shrinking an empty side while keeping selected roots

Push a disc boundary into its interior, fixing a chosen finite subset.
The new disc meets the old boundary exactly in that subset. Applied to
an empty side of a tube, this separates its framing hoops while keeping
the roots assigned to that side, in the disc construction of (15.4).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

/-- A closed disc can be shrunk so that its intersection with its old
boundary is exactly a chosen finite subset, all on its new boundary.
This is the empty-side adjustment in the short-tube proof of
Graph Minors VIII (15.4), page 282. -/
theorem exists_shrunk_disc_fixing_finite_boundary {S : Type w}
    [TopologicalSpace S] [T2Space S] {D Z : Set S} (hD : IsClosedDisc D)
    (hZ : Z.Finite) (hZD : Z ⊆ discBd D) :
    ∃ E : Set S, IsClosedDisc E ∧ E ⊆ D ∧
      E ∩ discBd D = Z ∧ Z ⊆ discBd E := by
  classical
  obtain ⟨eD⟩ := hD
  have hdiscD : IsClosedDisc D := ⟨eD⟩
  obtain ⟨eM⟩ := nonempty_disc_homeo
  have hsurf : IsSurface D :=
    isSurface_of_homeo (eM.trans eD) (isSurface_model 0 0 1).1
  have : CompactSpace D := hsurf.1
  have hO : IsOArc (bd D) :=
    isOArc_of_image IsEmbedding.subtypeVal hdiscD.isOArc_discBd
  have hC : IsCuff (bd D) := isCuff_of_oArc hO
  obtain ⟨φ⟩ := hO
  let ZD : Set D := Subtype.val ⁻¹' Z
  have hZDfin : ZD.Finite := hZ.preimage Subtype.val_injective.injOn
  obtain ⟨H, hH, _, hinj, hfix, _, hbd, _, _⟩ :=
    GM07.exists_taper_sides hsurf hC φ hZDfin.isClosed
  let h : D → D := fun y => H (1, y)
  let f : D → S := fun y => (h y).1
  have hhc : Continuous h := hH.comp (continuous_const.prodMk continuous_id)
  have hfc : Continuous f := continuous_subtype_val.comp hhc
  have hfi : Function.Injective f := Subtype.val_injective.comp hinj
  have hemb : IsEmbedding f := (hfc.isClosedEmbedding hfi).isEmbedding
  let E := f '' univ
  let e : D ≃ₜ E := (Homeomorph.Set.univ D).symm.trans (hemb.homeomorphImage univ)
  have heval : ∀ y : D, (e y).1 = f y := fun _ => rfl
  have hdisc : IsClosedDisc E := ⟨eD.trans e⟩
  have hnewbd : discBd E = f '' bd D := by
    rw [discBd, ← image_bd_homeomorph e, image_image]
    exact image_congr (fun y _ => heval y)
  have hprebd : ∀ y : D, y.1 ∈ discBd D → y ∈ bd D := by
    intro y hy
    obtain ⟨z, hz, hez⟩ := hy
    have heq : z = y := Subtype.ext hez
    exact heq ▸ hz
  have hZnew : Z ⊆ discBd E := by
    intro z hz
    have hzD : z ∈ D := discBd_subset D (hZD hz)
    let y : D := ⟨z, hzD⟩
    have hyZ : y ∈ ZD := hz
    have hybd : y ∈ bd D := hprebd y (hZD hz)
    rw [hnewbd]
    refine ⟨y, hybd, ?_⟩
    exact congrArg Subtype.val (hfix y hyZ)
  refine ⟨E, hdisc, ?_, ?_, hZnew⟩
  · rintro z ⟨y, _, rfl⟩
    exact (h y).2
  · apply subset_antisymm
    · rintro z ⟨⟨y, _, rfl⟩, hz⟩
      have hybd : h y ∈ bd D := hprebd (h y) hz
      exact hbd y hybd
    · intro z hz
      exact ⟨discBd_subset E (hZnew hz), hZD hz⟩

end GraphMinor.GM08
