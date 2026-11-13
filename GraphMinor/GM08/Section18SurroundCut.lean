module

public import GraphMinor.GM08.Section18Complexity
public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18CylinderCutSide
import GraphMinor.GM08.Section18CutDisc
import GraphMinor.GM08.Section18CutSide
import GraphMinor.Surface.CutOArc
import GraphMinor.Surface.CutCyl
import GraphMinor.Surface.CutComp
import GraphMinor.GM07.Section5a
import GraphMinor.GM07.Section8

/-!
# Cutting along a circle that surrounds a cuff

Types (iv) and (v) of a schism on page 241 of VII are made of circles that
surround cuffs. Before we cut along a whole schism (VIII (18.2), page 286),
we cut along one such circle `A`, which surrounds the cuff `C` and misses the
boundary. The circle-cut theorem gives three cases.
- The pieces are simpler. Then the measure `g` already drops.
- One piece is a closed disc. Then `A` is planar, which is false since `A`
  surrounds `C`.
- One piece is a cylinder `W` and the other is a copy of `Σ`. Then the
  cylinder lies in `Σ`, and capping one cuff `D` of `Σ` makes all of it
  planar. As `A` lies in it, `A` is planar in `Σ + D̂`, so `D = C`, for
  otherwise `Σ` would be a cylinder.

So in the last case every part of the cylinder piece is planar in `Σ + Ĉ`.
This tells us later which piece holds the rest of the schism.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

private theorem component_eq_univ' {T : Type w} [TopologicalSpace T] [ConnectedSpace T]
    {K : Set T} (hK : K ∈ spaceComponents T) : K = univ := by
  rw [spaceComponents_eq] at hK
  obtain ⟨x, rfl⟩ := hK
  exact PreconnectedSpace.connectedComponent_eq_univ x

/-- The output of a cut along a circle surrounding the cuff `C`, in the case
of a cylinder piece `W` and a copy `Wᶜ` of `Σ`. -/
def SurroundCopyCase {S T : Type w} [TopologicalSpace S] [TopologicalSpace T]
    (ψ : T → S) (A C : Set S) (W : Set T) : Prop :=
  IsClopen W ∧ ConnectedSpace (Wᶜ : Set T) ∧ Nonempty ((Wᶜ : Set T) ≃ₜ S) ∧
    InjOn ψ Wᶜ ∧ Nonempty (W ≃ₜ SurfaceModel 0 0 2) ∧
    (∃ X Y : Set T, X ∪ Y = ψ ⁻¹' A ∧ X ⊆ W ∧ Y ⊆ Wᶜ ∧ IsOArc Y ∧ BijOn ψ Y A) ∧
    (∀ Z ⊆ W, GM07.IsPlanarInCappedCuff C (ψ '' Z)) ∧
    ∀ z ∈ W, ψ z ∈ bd S → ψ z ∈ C

private theorem surroundCopyCase_of_sides {S T : Type w} [TopologicalSpace S]
    [TopologicalSpace T] [ConnectedSpace S] (hS : IsSurface S) (hT : IsSurface T)
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    {A C : Set S} (hA : IsOArc A) (hoff : Disjoint A (bd S)) (hsur : GM07.SurroundsCuff A C)
    {ψ : T → S} (hcut : IsCutting ψ A) {X Y W W' : Set T}
    (hun : X ∪ Y = ψ ⁻¹' A) (hX : IsOArc X) (hY : IsOArc Y)
    (hbX : BijOn ψ X A) (hbY : BijOn ψ Y A) (hXW : X ⊆ W) (hYW : Y ⊆ W')
    (hW : IsClopen W) (hUW : W ∪ W' = univ) (hdis : Disjoint W W')
    (hc : ConnectedSpace W) (hc' : ConnectedSpace W')
    (hcyl : Nonempty (W ≃ₜ SurfaceModel 0 0 2)) (hcopy : Nonempty (W' ≃ₜ S)) :
    SurroundCopyCase ψ A C W := by
  have : T2Space S := hS.2.1
  have hAc : IsClosed A := (GM07.IsOArc.isSolid hA).2
  have hWc : Wᶜ = W' := by
    ext z
    constructor
    · intro hz
      exact (hUW.symm ▸ mem_univ z : z ∈ W ∪ W').resolve_left hz
    · intro hz hzW
      exact disjoint_left.mp hdis hzW hz
  have hYX : Disjoint Y W := disjoint_left.mpr fun z hz hzW =>
    disjoint_left.mp hdis hzW (hYW hz)
  have hXW' : Disjoint X W' := disjoint_left.mpr fun z hz hzW' =>
    disjoint_left.mp hdis (hXW hz) hzW'
  obtain ⟨D, hD, hp, hbdD⟩ :=
    exists_cuff_planar_of_cylinder_cut_side hS hT hcut hAc hW hcyl hun hYX hXW hX hbX
  have hDC : D = C := by
    by_contra hne
    have hpA : GM07.IsPlanarInCappedCuff D A := hbX.image_eq ▸ hp X hXW
    exact hncyl (GM07.surroundsCuff_and_planarInCappedCuff_imp_cylinder hS hsur.1 hD
      (Ne.symm hne) hA hsur hpA)
  subst hDC
  refine ⟨hW, hWc ▸ hc', hWc ▸ hcopy, ?_, hcyl, ⟨X, Y, hun, hXW, hWc ▸ hYW, hY, hbY⟩, hp,
    fun z hz hzb => hbdD z hz hzb fun hzA => disjoint_left.mp hoff hzA hzb⟩
  rw [hWc]
  exact injOn_cut_side hcut (union_comm X Y ▸ hun) hXW' hbY.injOn

/-- **A cut along a circle that surrounds a cuff.** Either the measure drops,
or the cut has a cylinder piece `W`, every part of which is planar in
`Σ + Ĉ`, and a copy `Wᶜ` of `Σ` on which the cut map is one to one. -/
theorem exists_surround_cut {S : Type w} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    {A C : Set S} (hA : IsOArc A) (hoff : Disjoint A (bd S)) (hsur : GM07.SurroundsCuff A C) :
    ∃ (T : Type w) (_ : TopologicalSpace T) (ψ : T → S), IsSurface T ∧ IsCutting ψ A ∧
      (surfaceComplexity T < surfaceComplexity S ∨ ∃ W : Set T, SurroundCopyCase ψ A C W) := by
  have : T2Space S := hS.2.1
  obtain ⟨T, tT, ψ, hT, hcut, hcase, hlifts⟩ := cutOArc S A hS inferInstance hA hoff
  let := tT
  have : CompactSpace T := hT.1
  refine ⟨T, tT, ψ, hT, hcut, ?_⟩
  rcases hcase with hsimp | hcopy | hdisc
  · left
    obtain ⟨x⟩ := (inferInstance : Nonempty S)
    obtain ⟨y, _⟩ := hcut.2.1 x
    have : Nonempty T := ⟨y⟩
    exact surfaceComplexity_lt_of_cutIsSimpler hsimp
  · right
    obtain ⟨K₁, K₂, hne, hcomps, ⟨e₁⟩, ⟨e₂⟩⟩ := hcopy
    obtain ⟨ecyl⟩ := nonempty_cyl_homeo
    have hK₁ : K₁ ∈ spaceComponents T := hcomps ▸ (Or.inl rfl : K₁ ∈ ({K₁, K₂} : Set (Set T)))
    have hK₂ : K₂ ∈ spaceComponents T := hcomps ▸ (Or.inr rfl : K₂ ∈ ({K₁, K₂} : Set (Set T)))
    have hnotconn : ¬ ConnectedSpace T := fun h =>
      hne ((component_eq_univ' hK₁).trans (component_eq_univ' hK₂).symm)
    rcases hlifts with ⟨X, Y, -, hun, hX, hY, hbX, hbY⟩ | hpre
    · obtain ⟨x, hx⟩ := (GM07.IsOArc.isConnected hX).nonempty
      obtain ⟨y, hy⟩ := (GM07.IsOArc.isConnected hY).nonempty
      rcases cut_comps hcut hT hX.isPreconnected hY.isPreconnected hun hx hy with hconn |
        ⟨W₁, W₂, -, hW, hXW, hYW, hW₁, hW₂, hU, hdis, hc₁, hc₂⟩
      · exact absurd hconn hnotconn
      · rw [hW] at hK₁ hK₂
        rcases hK₁ with rfl | rfl
        · have h2 : K₂ = W₂ := hK₂.resolve_left (Ne.symm hne)
          subst h2
          exact ⟨K₁, surroundCopyCase_of_sides hS hT hncyl hA hoff hsur hcut hun hX hY hbX hbY
            hXW hYW hW₁ hU hdis hc₁ hc₂ ⟨e₁.trans ecyl.symm⟩ ⟨e₂⟩⟩
        · have h2 : K₂ = W₁ := by
            rcases hK₂ with h | h
            · exact h
            · exact absurd h.symm hne
          subst h2
          exact ⟨K₁, surroundCopyCase_of_sides hS hT hncyl hA hoff hsur hcut
            (union_comm X Y ▸ hun) hY hX hbY hbX hYW hXW hW₂ (union_comm K₂ K₁ ▸ hU)
            hdis.symm hc₂ hc₁ ⟨e₁.trans ecyl.symm⟩ ⟨e₂⟩⟩
    · exact absurd (connected_of_cut hcut hT hpre.isPreconnected rfl
        (GM07.IsOArc.isConnected hpre).nonempty) hnotconn
  · exact absurd hdisc (not_cutHasDisc_of_circle_lifts hS hT hcut hsur.2.2 hlifts)

end GraphMinor.GM08
