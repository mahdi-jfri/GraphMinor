module

public import GraphMinor.GM21.Section6Restrict
public import GraphMinor.GM21.Section6Induction
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.CutIArc
import GraphMinor.Surface.CutComp
import GraphMinor.GM07.Section5a
import GraphMinor.GM17.ReplaceDisc
import GraphMinor.GM17.CutSide
import GraphMinor.GM19.FragmentRegion

/-!
# Graph Minors XXI, (6.3), claim (2): cutting along a line

Claim (2) of the proof of (6.3) (page 28 of the preprint) takes a proper line `F` with ends
`a, b ∈ V(Γ)` that "does not separate $\Sigma$", and says: "Let $\Sigma'$ be obtained from $\Sigma$ by
cutting along $F$. By (4.1)(i) and (4.1)(ii), either $\hat{\Sigma}'$ is simpler than $\hat{\Sigma}$,
or $\hat{\Sigma}'$ is homeomorphic to $\hat{\Sigma}$ and $c(\Sigma') < c(\Sigma)$."

We cut with `cutIArc`. It gives a surface `Σ'`, the map `ψ : Σ' → Σ` that glues the two lifts `X, Y`
of `F` back together, and the shape of `Σ'`. This file collects what the cut gives
(`IsLineCut`) and proves the two cases that the rest of the proof of (6.3) uses
(`exists_lineCut`):

* either `Σ'` is connected, and then its type comes before the type of `Σ` in the order of the
  induction (`Induction.TypeLt`);
* or `Σ'` has two components, and then their images `Σ₁, Σ₂` in `Σ` are connected surfaces with
  `Σ₁ ∪ Σ₂ = Σ` and `Σ₁ ∩ Σ₂ = F`, so `F` separates `Σ`, and both ends of `F` lie in one cuff.

The first case is the setting of claim (2); the second is the setting of claim (4).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace CutLine

open Set Function Topology GraphMinor.Surface GraphMinor.GM21.Induction

/-- The data of the cut of `Σ` along a proper line `F` with ends `a, b`: a surface `Σ'`, the map
`ψ : Σ' → Σ` that undoes the cut (`IsCutting`), and the two lifts `X, Y` of `F`, which are disjoint
lines that `ψ` maps one to one onto `F`. The lift `X` has ends `a₁, b₁` over `a, b`, and `Y` has
ends `a₂, b₂`. -/
structure IsLineCut {S S' : Type} [TopologicalSpace S] [TopologicalSpace S'] (ψ : S' → S)
    (F : Set S) (a b : S) (X Y : Set S') (a₁ b₁ a₂ b₂ : S') : Prop where
  surface : IsSurface S'
  cutting : IsCutting ψ F
  disjoint : Disjoint X Y
  union : X ∪ Y = ψ ⁻¹' F
  lineX : IsLineWithEnds X a₁ b₁
  lineY : IsLineWithEnds Y a₂ b₂
  bijX : BijOn ψ X F
  bijY : BijOn ψ Y F
  map_a₁ : ψ a₁ = a
  map_b₁ : ψ b₁ = b
  map_a₂ : ψ a₂ = a
  map_b₂ : ψ b₂ = b

variable {S : Type} [TopologicalSpace S]

/-- A lift of a line, mapped one to one onto the line, has its ends over the ends of the line. -/
theorem exists_ends_of_bijOn [T2Space S] {S' : Type} [TopologicalSpace S'] {ψ : S' → S}
    (hψ : Continuous ψ) {K : Set S'} (hK : IsLine K) {F : Set S} {a b : S}
    (hF : IsLineWithEnds F a b) (hbij : BijOn ψ K F) :
    ∃ u v, IsLineWithEnds K u v ∧ ψ u = a ∧ ψ v = b := by
  obtain ⟨f⟩ := hK
  have hline : IsLineWithEnds K (f 0) (f 1) := ⟨f, rfl, rfl⟩
  obtain ⟨c, hc, hr, h0, h1⟩ := hline.exists_arc
  have harc : IsArcMap (ψ ∘ c) :=
    ⟨hψ.comp hc.1, fun s t he => hc.2 (hbij.injOn (hr ▸ mem_range_self s)
      (hr ▸ mem_range_self t) he)⟩
  have h3 := harc.isLineWithEnds
  rw [range_comp, hr, hbij.image_eq] at h3
  have h4 := (GM17.lineEnds_eq h3).symm.trans (GM17.lineEnds_eq hF)
  simp only [Function.comp, h0, h1] at h4
  rcases Set.pair_eq_pair_iff.mp h4 with ⟨h5, h6⟩ | ⟨h5, h6⟩
  · exact ⟨_, _, hline, h5, h6⟩
  · exact ⟨_, _, hline.symm, h6, h5⟩

/-- The images of the two parts of a disconnected cut. Let `W₁ ⊇ X` and `W₂ ⊇ Y` be the two parts.
Then `ψ` is one to one on each part, so `Σ₁ = ψ(W₁)` and `Σ₂ = ψ(W₂)` are copies of the parts, hence
connected surfaces. They cover `Σ`, since `ψ` is onto, and they meet exactly in `F`, since `ψ` is one
to one off `F` and both contain `ψ(X) = ψ(Y) = F`. -/
theorem sides_of_parts {S' : Type} [TopologicalSpace S'] (hS : IsSurface S) {ψ : S' → S}
    {F : Set S} {a b : S} {X Y : Set S'} {a₁ b₁ a₂ b₂ : S'}
    (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂) {W₁ W₂ : Set S'} (hX₁ : X ⊆ W₁) (hX₂ : Y ⊆ W₂)
    (hW₁ : IsClopen W₁) (hW₂ : IsClopen W₂) (hU : W₁ ∪ W₂ = univ) (hdW : Disjoint W₁ W₂)
    (hc₁ : ConnectedSpace W₁) (hc₂ : ConnectedSpace W₂) :
    ∃ S₁ S₂ : Set S, IsSurface S₁ ∧ IsSurface S₂ ∧ ConnectedSpace S₁ ∧ ConnectedSpace S₂ ∧
      S₁ ∪ S₂ = univ ∧ S₁ ∩ S₂ = F ∧ (S₁ \ F).Nonempty ∧ (S₂ \ F).Nonempty := by
  have hY := h.surface
  have : CompactSpace S' := hY.1
  have : T2Space S := hS.2.1
  have hψc : Continuous ψ := h.cutting.1
  have hcov : ∀ {W K : Set S'}, InjOn ψ K → ψ ⁻¹' F ∩ W = K → InjOn ψ W :=
      fun {W K} hK hcovK y hy y' hy' he => by
    by_cases hF : ψ y ∈ F
    · exact hK (hcovK ▸ ⟨hF, hy⟩) (hcovK ▸ ⟨(he ▸ hF : ψ y' ∈ F), hy'⟩) he
    · exact h.cutting.2.2.1 hF (by rw [mem_preimage, ← he]; exact hF) he
  have hdis₁ : Disjoint W₁ Y := disjoint_of_subset_right hX₂ hdW
  have hdis₂ : Disjoint W₂ X := disjoint_of_subset_right hX₁ hdW.symm
  have hcov₁ : ψ ⁻¹' F ∩ W₁ = X := by
    apply subset_antisymm
    · rintro y ⟨hy, hyW⟩
      exact (h.union ▸ hy : y ∈ X ∪ Y).resolve_right fun hyY => disjoint_left.mp hdis₁ hyW hyY
    · intro y hy
      exact ⟨h.union ▸ .inl hy, hX₁ hy⟩
  have hcov₂ : ψ ⁻¹' F ∩ W₂ = Y := by
    apply subset_antisymm
    · rintro y ⟨hy, hyW⟩
      exact (h.union ▸ hy : y ∈ X ∪ Y).resolve_left fun hyX => disjoint_left.mp hdis₂ hyW hyX
    · intro y hy
      exact ⟨h.union ▸ .inr hy, hX₂ hy⟩
  have hinj₁ : InjOn ψ W₁ := hcov h.bijX.injOn hcov₁
  have hinj₂ : InjOn ψ W₂ := hcov h.bijY.injOn hcov₂
  -- `ψ` restricted to a part is a copy of the part.
  have hcopy : ∀ {W : Set S'}, IsClopen W → InjOn ψ W → ConnectedSpace W →
      IsSurface (ψ '' W) ∧ ConnectedSpace (ψ '' W) := fun {W} hW hinj hcW => by
    have hcomp : CompactSpace W := isCompact_iff_compactSpace.mp hW.1.isCompact
    have hsurf : IsSurface W := isSurface_sub hY hW
    let g : W → ψ '' W := fun y => ⟨ψ y.1, mem_image_of_mem ψ y.2⟩
    have hgc : Continuous g := (hψc.comp continuous_subtype_val).subtype_mk _
    have hgbij : Bijective g := by
      refine ⟨fun y y' he => Subtype.ext (hinj y.2 y'.2 (congrArg Subtype.val he)), ?_⟩
      rintro ⟨_, y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    let e : W ≃ₜ ψ '' W := hgc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hgbij)
    refine ⟨GM07.isSurface_of_homeomorph e.symm hsurf, ?_⟩
    exact e.surjective.connectedSpace e.continuous
  obtain ⟨hs₁, hcn₁⟩ := hcopy hW₁ hinj₁ hc₁
  obtain ⟨hs₂, hcn₂⟩ := hcopy hW₂ hinj₂ hc₂
  -- Each part has a point off `bd(Σ')`, and its image is off `F`.
  have : T2Space S' := hY.2.1
  have hoff : ∀ {W : Set S'}, IsClopen W → W.Nonempty → (ψ '' W \ F).Nonempty := fun {W} hW hne => by
    obtain ⟨y, hyW, hyb⟩ := (GM19.dense_interior' hY).inter_open_nonempty W hW.2 hne
    exact ⟨ψ y, mem_image_of_mem ψ hyW, fun hyF => hyb (h.cutting.2.2.2.2 hyF)⟩
  refine ⟨ψ '' W₁, ψ '' W₂, hs₁, hs₂, hcn₁, hcn₂, ?_, ?_,
    hoff hW₁ ⟨a₁, hX₁ h.lineX.left_mem⟩, hoff hW₂ ⟨a₂, hX₂ h.lineY.left_mem⟩⟩
  · rw [← image_union, hU, image_univ, h.cutting.2.1.range_eq]
  · apply subset_antisymm
    · rintro x ⟨⟨y, hy, rfl⟩, ⟨y', hy', he⟩⟩
      by_contra hF
      have := h.cutting.2.2.1 (show y' ∈ ψ ⁻¹' Fᶜ by rw [mem_preimage, he]; exact hF) hF he
      exact disjoint_left.mp hdW hy (this ▸ hy')
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := h.bijX.surjOn hx
      obtain ⟨y', hy', he⟩ := h.bijY.surjOn hx
      exact ⟨mem_image_of_mem ψ (hX₁ hy), ⟨y', hX₂ hy', he⟩⟩

/-- **The cut along a proper line** (Graph Minors XXI, proof of (6.3), claims (2) and (4),
pages 28–29 of the preprint). Let `F` be a proper line with ends `a ≠ b` in a connected surface `Σ`
of type `(n, c)`. Cutting along `F` gives a surface `Σ'` with the data `IsLineCut`, and either
* `Σ'` is connected and has a type `(n', c')` before `(n, c)`; this is "(4.1)(i) and (4.1)(ii)" in
  claim (2); or
* `F` separates `Σ` into two connected surfaces `Σ₁, Σ₂` with `Σ₁ ∪ Σ₂ = Σ` and `Σ₁ ∩ Σ₂ = F`, and
  both ends of `F` lie in one cuff. -/
theorem exists_lineCut [ConnectedSpace S] (hS : IsSurface S) {n c : ℕ} (hT : HasType S n c)
    {F : Set S} {a b : S} (hF : IsProperLineInSurface F a b) :
    ∃ (S' : Type) (_ : TopologicalSpace S') (ψ : S' → S) (X Y : Set S') (a₁ b₁ a₂ b₂ : S'),
      IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂ ∧
      ((ConnectedSpace S' ∧ ∃ n' c', HasType S' n' c' ∧ TypeLt n' c' n c) ∨
        (connectedComponentIn (bd S) a = connectedComponentIn (bd S) b ∧
          ∃ S₁ S₂ : Set S, IsSurface S₁ ∧ IsSurface S₂ ∧ ConnectedSpace S₁ ∧
            ConnectedSpace S₂ ∧ S₁ ∪ S₂ = univ ∧ S₁ ∩ S₂ = F ∧ (S₁ \ F).Nonempty ∧
              (S₂ \ F).Nonempty)) := by
  have hne : a ≠ b := hF.ne
  have ht2 : T2Space S := hS.2.1
  obtain ⟨Y, tY, ψ, hY, hψ, h1, h2, X, X', hd, hun, lX, lX', bX, bX'⟩ :=
    cutIArc.{0} S F a b hS inferInstance hne hF.inter_bd_eq hF.1
  obtain ⟨a₁, b₁, hlX, ha₁, hb₁⟩ := exists_ends_of_bijOn hψ.1 lX hF.1 bX
  obtain ⟨a₂, b₂, hlX', ha₂, hb₂⟩ := exists_ends_of_bijOn hψ.1 lX' hF.1 bX'
  have hcut : IsLineCut ψ F a b X X' a₁ b₁ a₂ b₂ :=
    ⟨hY, hψ, hd, hun, hlX, hlX', bX, bX', ha₁, hb₁, ha₂, hb₂⟩
  refine ⟨Y, tY, ψ, X, X', a₁, b₁, a₂, b₂, hcut, ?_⟩
  have : CompactSpace Y := hY.1
  have pX := GM17.isPreconnected_line hlX
  have pX' := GM17.isPreconnected_line hlX'
  rcases cut_comps hψ hY pX pX' hun hlX.left_mem hlX'.left_mem with hYc |
    ⟨W₁, W₂, hne', hsc, hX₁, hX₂, hW₁, hW₂, hU, hdW, hc₁, hc₂⟩
  · left
    refine ⟨hYc, ?_⟩
    have hone : ∀ C ∈ spaceComponents Y, C = univ := fun C hC => by
      rw [spaceComponents_eq] at hC
      obtain ⟨y, rfl⟩ := hC
      exact PreconnectedSpace.connectedComponent_eq_univ y
    have hunivc : univ ∈ spaceComponents Y := by
      rw [spaceComponents_eq]
      exact ⟨a₁, PreconnectedSpace.connectedComponent_eq_univ a₁⟩
    by_cases hs : connectedComponentIn (bd S) a = connectedComponentIn (bd S) b
    · rcases h2 hs with hc | ⟨C₁, C₂, hneC, heq, -, -⟩
      · obtain ⟨a', b', c', a'', b'', c'', ⟨e⟩, ⟨e'⟩, hle₁, hle₂, hlt⟩ := hc.2 univ hunivc
        have hT' : HasType Y (2 * a' + b') c' :=
          ⟨a', b', rfl, ⟨(Homeomorph.Set.univ Y).symm.trans e⟩⟩
        obtain ⟨hn, hc'⟩ := hT.unique ⟨a'', b'', rfl, ⟨e'⟩⟩
        refine ⟨_, _, hT', ?_⟩
        rcases lt_or_eq_of_le (show 2 * a' + b' ≤ n by omega) with hlt' | heq'
        · exact Or.inl hlt'
        · exact Or.inr ⟨heq', by omega⟩
      · exfalso
        exact hneC ((hone C₁ (heq ▸ mem_insert _ _)).trans
          (hone C₂ (heq ▸ mem_insert_of_mem _ rfl)).symm)
    · obtain ⟨-, a', b', c', ⟨e⟩, ⟨e'⟩⟩ := h1 hs
      obtain ⟨hn, hc'⟩ := hT.unique ⟨a', b', rfl, ⟨e⟩⟩
      exact ⟨_, _, ⟨a', b', rfl, ⟨e'⟩⟩, Or.inr ⟨hn.symm, by omega⟩⟩
  · right
    have hs : connectedComponentIn (bd S) a = connectedComponentIn (bd S) b := by
      by_contra hs
      obtain ⟨hYc, -⟩ := h1 hs
      have hone : ∀ C ∈ spaceComponents Y, C = univ := fun C hC => by
        rw [spaceComponents_eq] at hC
        obtain ⟨y, rfl⟩ := hC
        exact PreconnectedSpace.connectedComponent_eq_univ y
      exact hne' ((hone W₁ (hsc ▸ mem_insert _ _)).trans
        (hone W₂ (hsc ▸ mem_insert_of_mem _ rfl)).symm)
    exact ⟨hs, sides_of_parts hS hcut hX₁ hX₂ hW₁ hW₂ hU hdW hc₁ hc₂⟩

end CutLine
end GM21
end GraphMinor
