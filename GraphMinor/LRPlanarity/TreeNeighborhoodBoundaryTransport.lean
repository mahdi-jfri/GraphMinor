module

public import GraphMinor.Surface.DomainPair
import GraphMinor.Surface.ArcTools

/-!
# Transporting a boundary traversal through one attachment

Part IV, Section 7b of the planarity note replaces one boundary interval
by the child's detour and keeps the rest fixed. A boundary match carries
the old traversal to the new boundary. Restrict to the unit interval and
extend constantly beyond its ends, so continuity outside the boundary
parameter interval requires no extension of the boundary match itself.
The two half-open injectivity properties and all old parameters survive.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7b: a boundary match transports a once-around traversal,
preserving its parameter values on the closed unit interval. -/
theorem exists_transported_boundary_traversal {C C' : Set ℂ} {h k : ℂ → ℂ}
    (hmatch : BdMatch C C' h k) (f : ℝ → ℂ) (hf : Continuous f)
    (hIco : InjOn f (Ico (0 : ℝ) 1)) (hIoc : InjOn f (Ioc (0 : ℝ) 1))
    (himage : f '' Icc (0 : ℝ) 1 = C) :
    ∃ g : ℝ → ℂ, Continuous g ∧ InjOn g (Ico (0 : ℝ) 1) ∧ InjOn g (Ioc (0 : ℝ) 1) ∧
      g '' Icc (0 : ℝ) 1 = C' ∧ ∀ t ∈ Icc (0 : ℝ) 1, g t = h (f t) := by
  obtain ⟨hmap,kmap,hleft,hright,hcont,_⟩ := hmatch
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, f t ∈ C := fun t ht => himage ▸ mem_image_of_mem f ht
  let a : unitInterval → ℂ := fun t => h (f t.val)
  have ha : Continuous a := hcont.comp_continuous (hf.comp continuous_subtype_val)
    (fun t => hmem t.val t.property)
  let g := extI a
  have heval : ∀ t ∈ Icc (0 : ℝ) 1, g t = h (f t) := fun _ ht => extI_of_mem a ht
  refine ⟨g,continuous_extI ha,?_,?_,?_,heval⟩
  · intro x hx y hy he
    rw [heval x ⟨hx.1,hx.2.le⟩,heval y ⟨hy.1,hy.2.le⟩] at he
    apply hIco hx hy
    have he' := congrArg k he
    rw [hleft (hmem x ⟨hx.1,hx.2.le⟩),hleft (hmem y ⟨hy.1,hy.2.le⟩)] at he'
    exact he'
  · intro x hx y hy he
    rw [heval x ⟨hx.1.le,hx.2⟩,heval y ⟨hy.1.le,hy.2⟩] at he
    apply hIoc hx hy
    have he' := congrArg k he
    rw [hleft (hmem x ⟨hx.1.le,hx.2⟩),hleft (hmem y ⟨hy.1.le,hy.2⟩)] at he'
    exact he'
  · apply Subset.antisymm
    · rintro x ⟨t,ht,rfl⟩
      rw [heval t ht]
      exact hmap (hmem t ht)
    · intro x hx
      obtain ⟨t,ht,he⟩ := himage.symm ▸ kmap hx
      refine ⟨t,ht,?_⟩
      rw [heval t ht,he,hright hx]

end GraphMinor.LRPlanarity
