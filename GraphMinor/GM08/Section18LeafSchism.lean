module

public import GraphMinor.GM07.Defs
import GraphMinor.GM07.CuffShift
import GraphMinor.GM07.Section8
import GraphMinor.GM08.Section18Schism
import GraphMinor.GM12.Section3SolidConnections

/-!
# A small schism from a retraction off the boundary

The paper derives VIII (18.1) from VII (9.1) and the remark on page 242 of VII
that every schismatic set includes a schism. That remark is false (see the
correction on page 242 in `corrections/GM07.md`). Here we prove what replaces
it for the drawings used in the corrected form of (18.1).

Let `g` be a map of the surface, homotopic to the identity, whose image misses
the boundary. Suppose also that `g` sends a point into the drawing only if the
point was already in the drawing, and sends vertices to vertices. Then `g`
sends a normal set to a normal set with no more vertices, and its image misses
the boundary. The image of a solid connected set that is not near-planar is
again solid, connected and not near-planar, since the homotopy carries the
image back to the set. A schismatic subset of the image misses the boundary,
so it is a schism. So every alpha candidate gives a normal schism with no more
vertices.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

local notation "𝕀" => unitInterval

variable {S : Type u} [TopologicalSpace S]

/-- The image of a solid set under a continuous map of a compact Hausdorff
space is solid. The map onto the image is a quotient map, and quotients keep
local path-connectedness. -/
theorem isSolid_image_of_continuous [CompactSpace S] [T2Space S] {g : S → S}
    (hg : Continuous g) {X : Set S} (hX : IsSolid X) : IsSolid (g '' X) := by
  have hXc : IsCompact X := hX.2.isCompact
  have hYc : IsCompact (g '' X) := hXc.image hg
  refine ⟨?_, hYc.isClosed⟩
  have : LocallyPathConnectedSpace X :=
    GM12.locallyPathConnectedSpace_of_isLocallyArcConnected hX.1
  have : CompactSpace X := isCompact_iff_compactSpace.mp hXc
  let f : X → g '' X := fun x => ⟨g x, x, x.2, rfl⟩
  have hf : Continuous f := (hg.comp continuous_subtype_val).subtype_mk _
  have hfs : Function.Surjective f := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hq : IsQuotientMap f := hf.isClosedMap.isQuotientMap hf hfs
  have : LocallyPathConnectedSpace (g '' X) := hq.locallyPathConnectedSpace
  exact GM12.isLocallyArcConnected_of_locallyPathConnectedSpace

/-- A solid set is planar if its image under a map homotopic to the identity
is planar. -/
theorem isPlanar_of_image_homotopy [CompactSpace S] [T2Space S] {T : Type u}
    [TopologicalSpace T] (hT : IsSurface T) [ConnectedSpace T] (hns : ¬ IsSphere T)
    {j : S → T} (hj : IsEmbedding j) {g : S → S} {Φ : 𝕀 × S → S} (hΦ : Continuous Φ)
    (h0 : ∀ x, Φ (0, x) = x) (h1 : ∀ x, Φ (1, x) = g x) {X : Set S} (hX : IsSolid X)
    (hp : IsPlanar (j '' (g '' X))) : IsPlanar (j '' X) := by
  obtain ⟨Δ, hΔ, hs'⟩ := hp
  refine GM07.isPlanar_of_homotopy (H := fun q => j (Φ q)) hT hj hX (.inl hns)
    (hj.continuous.comp hΦ) (fun y => by simp [h0]) fun F _ hFX => ⟨Δ, hΔ, fun y hy => ?_⟩
  simp only [h1]
  exact hs' (mem_image_of_mem j (mem_image_of_mem g (hFX hy)))

/-- A solid set is near-planar if its image under a map homotopic to the
identity is near-planar. -/
theorem isNearPlanar_of_image_homotopy (hS : IsSurface S) [ConnectedSpace S] {a b c : ℕ}
    (habc : 3 ≤ 3 * a + 3 * b + c) (hm : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hns : ¬ IsSphere S) {g : S → S} {Φ : 𝕀 × S → S} (hΦ : Continuous Φ)
    (h0 : ∀ x, Φ (0, x) = x) (h1 : ∀ x, Φ (1, x) = g x) {X : Set S} (hX : IsSolid X)
    (hp : GM07.IsNearPlanar (g '' X)) : GM07.IsNearPlanar X := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  rcases hp with hp | ⟨C, hC, hp⟩
  · left
    simpa using isPlanar_of_image_homotopy hS hns IsEmbedding.id hΦ h0 h1 hX
      (by simpa using hp)
  · right
    refine ⟨C, hC, ?_⟩
    have hCc : IsCuff C := hp.1
    obtain ⟨T₁, tT, j, D, hc, -⟩ := GM07.exists_cappedCuff hS hCc
    have hT := hc.isSurface
    have : ConnectedSpace T₁ := hc.connectedSpace hS
    have hns' := GM07.not_isSphere_cap hS habc hm hc
    obtain ⟨-, -, h2⟩ := hp
    exact GM07.isPlanarInCappedCuff_of_cap hS hc
      (isPlanar_of_image_homotopy hT hns' hc.isEmbedding hΦ h0 h1 hX (h2 _ j D hc))

/-- **A small schism from a retraction off the boundary.** Let `g` be homotopic
to the identity with image off the boundary, such that `g x` is in the drawing
only if `x` is, and `g` sends vertices into vertices or off the drawing. Then
every alpha candidate gives a normal schism with no more vertices, and the
schism misses the boundary. -/
theorem exists_normal_schism_of_retraction (hS : IsSurface S) [ConnectedSpace S]
    {a b c : ℕ} (habc : 3 ≤ 3 * a + 3 * b + c) (hm : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hns : ¬ IsSphere S) (hcuffs : (cuffs S).Nonempty) (G : Drawing S)
    {g : S → S} {Φ : 𝕀 × S → S} (hΦ : Continuous Φ)
    (h0 : ∀ x, Φ (0, x) = x) (h1 : ∀ x, Φ (1, x) = g x)
    (hbd : ∀ x, g x ∉ bd S) (hU : ∀ x, g x ∈ G.U → x ∈ G.U)
    (hV : ∀ x ∈ G.V, g x ∈ G.U → g x ∈ G.V)
    {X : Set S} (hX : GM07.IsAlphaCandidate G X) :
    ∃ F : Set S, GM07.IsSchism F ∧ G.IsNormal F ∧ F ∩ bd S = ∅ ∧
      (G.V ∩ F).ncard ≤ (G.V ∩ X).ncard := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  obtain ⟨hsol, hconn, hnorm, hnp⟩ := hX
  have hg : Continuous g := by
    have : g = fun x => Φ (1, x) := funext fun x => (h1 x).symm
    rw [this]
    exact hΦ.comp (continuous_const.prodMk continuous_id)
  -- the image is normal
  have hnY : G.IsNormal (g '' X) := by
    rintro _ ⟨⟨x, hx, rfl⟩, hgx⟩
    exact hV x (hnorm ⟨hx, hU x hgx⟩) hgx
  have hY : GM07.IsAlphaCandidate G (g '' X) :=
    ⟨isSolid_image_of_continuous hg hsol, hconn.image g hg.continuousOn, hnY,
      fun h => hnp (isNearPlanar_of_image_homotopy hS habc hm hns hΦ h0 h1 hsol h)⟩
  obtain ⟨F, hFY, hF, hnF⟩ := GM07.exists_schismatic_of_isAlphaCandidate hS hns G _ hY
  have hoff : F ∩ bd S = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr ?_
    rintro z ⟨hzF, hzb⟩
    obtain ⟨x, -, rfl⟩ := hFY hzF
    exact hbd x hzb
  refine ⟨F, isSchism_of_isSchismatic_of_disjoint_boundary hS hcuffs hF hoff, hnF, hoff, ?_⟩
  -- every vertex of the image comes from a vertex of `X`
  have hsub : G.V ∩ F ⊆ g '' (G.V ∩ X) := by
    rintro z ⟨hzV, hzF⟩
    obtain ⟨x, hx, rfl⟩ := hFY hzF
    exact ⟨x, ⟨hnorm ⟨hx, hU x (G.V_subset_U hzV)⟩, hx⟩, rfl⟩
  have hfin : (G.V ∩ X).Finite := G.finite_V.inter_of_left X
  exact (ncard_le_ncard hsub (hfin.image g)).trans (ncard_image_le hfin)

end GraphMinor.GM08
