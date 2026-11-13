module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.CrossCut
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-!
# Parameters of an initial subarc

For the edge contraction in VI Reduction 3, page 129, an arc of a
linkage path that starts at its initial vertex is a prefix of the
path parameter. Take the inverse of the whole-path parametrization.
The resulting interval map is continuous and injective, starts at
zero, and is therefore strictly increasing. Its range is the interval
between its two endpoint values.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

universe u

/-- A proper initial subarc of an injectively parametrized path has
range equal to an initial parameter interval. This identifies the
segment contracted by Reduction 3. -/
theorem exists_parameter_of_initial_subarc
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (f g : C(unitInterval, S)) (hf : IsArcMap f) (hg : IsArcMap g)
    (hsub : range g ⊆ range f) (hstart : g 0 = f 0) (hend : g 1 ≠ f 1) :
    ∃ τ ∈ Ioo (0 : unitInterval) 1, f τ = g 1 ∧ range g = f '' Icc 0 τ := by
  let e : unitInterval ≃ₜ range f := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective f hf.2) f.continuous.rangeFactorization
  let ψ : C(unitInterval, unitInterval) :=
    ⟨fun t => e.symm ⟨g t, hsub (mem_range_self t)⟩,
      e.symm.continuous.comp (g.continuous.subtype_mk (fun t => hsub (mem_range_self t)))⟩
  have hψ (t) : f (ψ t) = g t :=
    congrArg Subtype.val (e.apply_symm_apply ⟨g t, hsub (mem_range_self t)⟩)
  have hψ0 : ψ 0 = 0 := hf.2 ((hψ 0).trans hstart)
  have hiψ : Function.Injective ψ := by
    intro a b he
    apply hg.2
    rw [← hψ a, ← hψ b, he]
  have hm : StrictMono ψ := ψ.continuous.strictMono_of_inj_boundedOrder
    (by change ψ 0 ≤ ψ 1; rw [hψ0]; exact bot_le) hiψ
  have hτ0 : 0 < ψ 1 := by
    have hh := hm (show (0 : unitInterval) < 1 from zero_lt_one)
    rwa [hψ0] at hh
  have hτ1 : ψ 1 < 1 := by
    apply lt_of_le_of_ne le_top
    intro he
    exact hend (he ▸ hψ 1).symm
  have hr : range ψ = Icc 0 (ψ 1) := by
    have hh := ψ.continuous.image_Icc_of_strictMono hm (a := (0 : unitInterval)) (b := 1)
    rw [show Icc (0 : unitInterval) 1 = univ from Icc_bot_top, image_univ, hψ0] at hh
    exact hh
  refine ⟨ψ 1, ⟨hτ0, hτ1⟩, hψ 1, ?_⟩
  calc
    range g = range (f ∘ ψ) := congrArg range (funext fun t => (hψ t).symm)
    _ = f '' range ψ := range_comp _ _
    _ = f '' Icc 0 (ψ 1) := by rw [hr]

end GraphMinor.GM06
