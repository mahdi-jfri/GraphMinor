module

public import GraphMinor.GM05.CrosscapChartReflection
import GraphMinor.Surface.PlaneDisc
import GraphMinor.Surface.InvarianceOfDomain
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The closed disc and its reversed boundary triple

For the crosscap obstruction in GM V, (8.10), a continuous injective
chart of the closed unit disc has a closed-disc image. If a surface
homeomorphism acts on the chart by conjugation, it maps that image
onto itself. The images of `1`, `I`, and `-I` are distinct boundary
points, with the first fixed and the other two exchanged.
-/

public section

namespace GraphMinor.GM05

open Set Topology Metric Surface

universe u

private theorem complex_disc_mem_bd (z : ↥(closedBall (0 : ℂ) 1)) (hz : ‖z.1‖=1) :
    z ∈ bd ↥(closedBall (0 : ℂ) 1) := by
  have hm : z.1 ∈ discBd (closedBall (0 : ℂ) 1) := by
    rw [isClosedDisc_closedBall.2]
    exact mem_sphere_zero_iff_norm.mpr hz
  obtain ⟨w,hw,he⟩ := hm
  have he' : w=z := Subtype.ext he
  exact he' ▸ hw

/-- A reflected injective chart supplies an invariant closed disc with
one fixed boundary point and two exchanged boundary points. -/
theorem reflected_disc_image {T : Type u} [TopologicalSpace T] [T2Space T]
    (f : ↥(closedBall (0 : ℂ) 1) → T) (hc : Continuous f) (hi : Function.Injective f)
    (e : T ≃ₜ T) (hreflect : ∀ z,e (f z)=f (complexDiscConj z)) :
    ∃ E : Set T,IsClosedDisc E ∧ e '' E=E ∧ ∃ a b c : T,
      a ∈ discBd E ∧ b ∈ discBd E ∧ c ∈ discBd E ∧
      a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ e a=a ∧ e b=c ∧ e c=b := by
  let : CompactSpace ↥(closedBall (0 : ℂ) 1) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let eF : ↥(closedBall (0 : ℂ) 1) ≃ₜ range f := (hc.isClosedEmbedding hi).isEmbedding.toHomeomorph
  obtain ⟨φ⟩ := isClosedDisc_closedBall.1
  have hE : IsClosedDisc (range f) := ⟨φ.trans eF⟩
  have hboundary (z : ↥(closedBall (0 : ℂ) 1)) (hz : ‖z.1‖=1) : f z ∈ discBd (range f) := by
    have hm : eF z ∈ bd (range f) := by
      rw [← image_bd_homeomorph eF]
      exact mem_image_of_mem _ (complex_disc_mem_bd z hz)
    exact ⟨eF z,hm,rfl⟩
  have himage : e '' range f=range f := by
    apply Subset.antisymm
    · rintro _ ⟨y,⟨z,rfl⟩,rfl⟩
      exact ⟨complexDiscConj z,(hreflect z).symm⟩
    · rintro _ ⟨z,rfl⟩
      refine ⟨f (complexDiscConj.symm z),⟨complexDiscConj.symm z,rfl⟩,?_⟩
      rw [hreflect,complexDiscConj.apply_symm_apply]
  let zA : ↥(closedBall (0 : ℂ) 1) := ⟨1,by simp⟩
  let zB : ↥(closedBall (0 : ℂ) 1) := ⟨Complex.I,by simp⟩
  let zC : ↥(closedBall (0 : ℂ) 1) := ⟨-Complex.I,by simp⟩
  have hab₀ : zA ≠ zB := by
    intro he
    have hh := congrArg (fun z : ↥(closedBall (0 : ℂ) 1) ↦ z.1.im) he
    norm_num [zA,zB] at hh
  have hbc₀ : zB ≠ zC := by
    intro he
    have hh := congrArg (fun z : ↥(closedBall (0 : ℂ) 1) ↦ z.1.im) he
    norm_num [zB,zC] at hh
  have hac₀ : zA ≠ zC := by
    intro he
    have hh := congrArg (fun z : ↥(closedBall (0 : ℂ) 1) ↦ z.1.im) he
    norm_num [zA,zC] at hh
  have hA : complexDiscConj zA=zA := by
    apply Subtype.ext
    rw [complexDiscConj_val]
    simp [zA]
  have hB : complexDiscConj zB=zC := by
    apply Subtype.ext
    rw [complexDiscConj_val]
    simp [zB,zC]
  have hC : complexDiscConj zC=zB := by
    apply Subtype.ext
    rw [complexDiscConj_val]
    simp [zB,zC]
  refine ⟨range f,hE,himage,f zA,f zB,f zC,hboundary zA (by simp [zA]),
    hboundary zB (by simp [zB]),hboundary zC (by simp [zC]),
    fun he ↦ hab₀ (hi he),fun he ↦ hbc₀ (hi he),fun he ↦ hac₀ (hi he),?_,?_,?_⟩
  · rw [hreflect,hA]
  · rw [hreflect,hB]
  · rw [hreflect,hC]

end GraphMinor.GM05
