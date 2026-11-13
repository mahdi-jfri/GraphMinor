module

public import GraphMinor.GM06.Alg57Find4Link

/-!
# A simple walk along an arc follows the parameter

Let the point set of a drawing `P` lie on an arc `f '' [0, 1]`, with `f` injective on `[0, 1]`, and
let `W` be a walk of `P` from `f 0` to `x = f τ`. Then every vertex `f σ` of `P` that is not on `W`
comes after `x` along the arc: `τ < σ` (`param_lt_of_not_mem_walk`). The reason: the point set of
`W` is connected, lies on the arc and contains `f 0` and `f τ`, so it contains `f '' [0, τ]`; a
vertex of `P` in the point set of `W` is on `W`.

Applied to the prefixes of a simple walk of `P₁` from `s₁`, this says that the order of the walk
is the order of the parameter of `L.curve 0`, which is what the lifted incidence at the vertices of
`P₁` needs to tell its forward dart from its backward dart.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {S : Type*} [TopologicalSpace S]

/-- The point set of a walk is preconnected. -/
theorem isPreconnected_walkDrawing_U' [T1Space S] (Γ : Drawing S) {u v : S}
    (W : GraphWalk Γ.toGraph u v) : IsPreconnected (walkDrawing Γ W).U := by
  induction W with
  | @nil a ha =>
    have hEq : (walkDrawing Γ (.nil ha)).U = {a} := by
      ext y
      rw [mem_walkDrawing_U]
      simp [GraphWalk.support_nil]
    rw [hEq]
    exact isPreconnected_singleton
  | @cons a w b e hlink r ih =>
    have hEq : (walkDrawing Γ (.cons hlink r)).U = closure e ∪ (walkDrawing Γ r).U := by
      ext y
      rw [mem_walkDrawing_U, mem_union, mem_walkDrawing_U]
      simp only [GraphWalk.support_cons, List.mem_cons, GraphWalk.edges_cons]
      constructor
      · rintro ((rfl | hyr) | ⟨f, rfl | hfr, hyf⟩)
        · left
          have : y ∈ closure e ∩ Γ.V := by rw [hlink.2.2.2]; simp
          exact this.1
        · exact Or.inr (Or.inl hyr)
        · exact Or.inl hyf
        · exact Or.inr (Or.inr ⟨f, hfr, hyf⟩)
      · rintro (hye | (hyr | ⟨f, hfr, hyf⟩))
        · exact Or.inr ⟨e, Or.inl rfl, hye⟩
        · exact Or.inl (Or.inr hyr)
        · exact Or.inr ⟨f, Or.inr hfr, hyf⟩
    rw [hEq]
    have he_pre : IsPreconnected (closure e) := hlink.1.2.2.1.isConnected.isPreconnected.closure
    have hw_e : w ∈ closure e := by
      have : w ∈ closure e ∩ Γ.V := by rw [hlink.2.2.2]; simp
      exact this.1
    have hw_r : w ∈ (walkDrawing Γ r).U := (mem_walkDrawing_U Γ r).mpr (Or.inl r.start_mem_support)
    exact he_pre.union' ⟨w, hw_e, hw_r⟩ ih

/-- **A walk from the start of an arc covers the arc up to its end.** If the point set of `P` lies
on the arc `f '' [0, 1]` and `W` is a walk of `P` from `f 0` to `f τ`, then a vertex `f σ` of `P`
off `W` has `τ < σ`. -/
theorem param_lt_of_not_mem_walk [T2Space S] {P : Drawing S} {f : ℝ → S} (hf : Continuous f)
    (hinj : InjOn f (Icc 0 1)) (hU : P.U ⊆ f '' Icc 0 1) {x : S}
    (W : GraphWalk P.toGraph (f 0) x) {τ σ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) (hx : f τ = x)
    (hσ : σ ∈ Icc (0 : ℝ) 1) (hyV : f σ ∈ P.V) (hy : f σ ∉ W.support) : τ < σ := by
  by_contra hle
  push_neg at hle
  set A := (walkDrawing P W).U
  have hA := isPreconnected_walkDrawing_U' P W
  have hAU : A ⊆ P.U := (walkDrawing_isSubdrawing P W).U_subset
  let g : Icc (0 : ℝ) 1 → S := fun u => f u
  have hg : Continuous g := hf.comp continuous_subtype_val
  have hginj : Function.Injective g := fun u v h => Subtype.ext (hinj u.2 v.2 h)
  have hemb : IsClosedEmbedding g := hg.isClosedEmbedding hginj
  have hrange : A ⊆ range g := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := hU (hAU hz)
    exact ⟨⟨u, hu⟩, rfl⟩
  have hB : IsPreconnected (g ⁻¹' A) := by
    rw [← hemb.isInducing.isPreconnected_image, image_preimage_eq_inter_range,
      inter_eq_left.mpr hrange]
    exact hA
  have hC : IsPreconnected (Subtype.val '' (g ⁻¹' A) : Set ℝ) :=
    hB.image _ continuous_subtype_val.continuousOn
  have h0 : (0 : ℝ) ∈ Subtype.val '' (g ⁻¹' A) :=
    ⟨⟨0, left_mem_Icc.mpr zero_le_one⟩,
      (mem_walkDrawing_U P W).mpr (Or.inl W.start_mem_support), rfl⟩
  have hτC : τ ∈ Subtype.val '' (g ⁻¹' A) :=
    ⟨⟨τ, hτ⟩, (mem_walkDrawing_U P W).mpr (Or.inl (hx ▸ W.end_mem_support)), rfl⟩
  obtain ⟨u, hu, hu'⟩ := hC.Icc_subset h0 hτC ⟨hσ.1, hle⟩
  have hσA : f σ ∈ A := by
    rw [← hu']
    exact hu
  exact hy (mem_support_of_mem_walkDrawing_U (Drawing.IsSubdrawing.refl P) W hσA hyV)

end GraphMinor.GM06
