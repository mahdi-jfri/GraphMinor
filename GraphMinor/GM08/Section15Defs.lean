module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM07.CylinderCap
public import GraphMinor.Surface.CutComp
public import GraphMinor.Surface.DiscsInSurface
public import GraphMinor.Surface.ModelCriterion

/-!
# Graph Minors VIII, Section 15: Tubes, Definitions and Cylinder Topology (pages 279–282)

This file formalizes the definitions of Section 15 ("Tubes", pages 279–282) of N. Robertson and
P. D. Seymour, *Graph Minors. VIII. A Kuratowski Theorem for General Surfaces*,
J. Combin. Theory Ser. B **48** (1990), 255–288, together with the capped-sphere API for hoops,
sides, laminar hoops, sub-cylinders $\Sigma(F_1, F_2)$, tubes, framings, width, length,
$\mathcal{G}(r, k)$, and $\mathcal{A}(k, r, s)$.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Topology Graph GraphMinor.Surface GraphMinor.GM11

universe u v w w'

/-! ## 1. Cylinders, Hoops, and Capped Cylinders -/

/-- A *cylinder* is a surface homeomorphic to $\Sigma(0, 0, 2)$.
Graph Minors VIII, Section 15 (page 279):
"A *cylinder* is a surface homeomorphic to $\Sigma(0, 0, 2)$." -/
def IsCylinder (S : Type w) [TopologicalSpace S] : Prop :=
  IsSurface S ∧ Nonempty (S ≃ₜ SurfaceModel 0 0 2)

namespace IsCylinder

variable {S : Type w} [TopologicalSpace S]

theorem isSurface (hS : IsCylinder S) : IsSurface S := hS.1

theorem compactSpace (hS : IsCylinder S) : CompactSpace S := hS.1.1

theorem t2Space (hS : IsCylinder S) : T2Space S := hS.1.2.1

theorem connectedSpace (hS : IsCylinder S) : ConnectedSpace S := by
  obtain ⟨e⟩ := hS.2
  have := (isSurface_model 0 0 2).2
  exact e.symm.surjective.connectedSpace e.symm.continuous

theorem nonempty (hS : IsCylinder S) : Nonempty S := by
  have := hS.connectedSpace
  infer_instance

theorem congr {S' : Type w'} [TopologicalSpace S'] (e : S ≃ₜ S') (hS : IsCylinder S) :
    IsCylinder S' := by
  obtain ⟨⟨hc, ht2, hman⟩, ⟨e₀⟩⟩ := hS
  refine ⟨⟨e.compactSpace, e.t2Space, fun y => ?_⟩, ⟨e.symm.trans e₀⟩⟩
  obtain ⟨U, V, hU, hV, hxU, ⟨φ⟩⟩ := hman (e.symm y)
  refine ⟨e '' U, V, e.isOpenMap U hU, hV, ⟨e.symm y, hxU, e.apply_symm_apply y⟩, ?_⟩
  exact ⟨(e.isEmbedding.homeomorphImage U).symm.trans φ⟩

theorem ncard_cuffs (hS : IsCylinder S) : (cuffs S).ncard = 2 := by
  obtain ⟨e⟩ := hS.2
  obtain ⟨ht, f, hf⟩ := presents_ew 0 0 2
  have : T2Space (SurfaceModel 0 0 2) := ht
  rw [ncard_cuffs_congr e, Surface.ncard_cuffs hf]

theorem exists_cuffs (hS : IsCylinder S) :
    ∃ C₁ C₂ : Set S, C₁ ≠ C₂ ∧ cuffs S = {C₁, C₂} :=
  ncard_eq_two.mp hS.ncard_cuffs

theorem not_isSphere (hS : IsCylinder S) : ¬ IsSphere S := by
  rintro ⟨e⟩
  have hbd : bd S = ∅ := by
    ext x
    simp only [mem_empty_iff_false, iff_false]
    intro hx
    have hZ : IsClosedSurface (OnePoint EuclideanPlane) := by
      obtain ⟨s₀⟩ := GM12.isSphere_model_zero
      have h0 := (isSurface_model 0 0 0).1
      have : CompactSpace (SurfaceModel 0 0 0) := h0.1
      have : T2Space (SurfaceModel 0 0 0) := h0.2.1
      refine ⟨s₀.compactSpace, s₀.t2Space, fun z => ?_⟩
      have hi : IsInteriorPoint (s₀.symm z) := by
        by_contra hn
        have hnc : (cuffs (SurfaceModel 0 0 0)).ncard = 0 := by
          obtain ⟨_, f, hf⟩ := presents_ew 0 0 0
          exact Surface.ncard_cuffs hf
        have hce : cuffs (SurfaceModel 0 0 0) = ∅ :=
          (ncard_eq_zero (cuff_statement _ h0).2.1).mp hnc
        have hmem : connectedComponentIn (bd (SurfaceModel 0 0 0)) (s₀.symm z) ∈
            cuffs (SurfaceModel 0 0 0) := ⟨s₀.symm z, hn, rfl⟩
        rw [hce] at hmem
        exact hmem
      have := (isInteriorPoint_homeomorph_iff s₀ (s₀.symm z)).mpr hi
      rwa [s₀.apply_symm_apply] at this
    exact hx ((isInteriorPoint_homeomorph_iff e x).mp (hZ.2.2 (e x)))
  obtain ⟨C₁, C₂, _, hc⟩ := hS.exists_cuffs
  have hC₁ : C₁ ∈ cuffs S := by rw [hc]; simp
  obtain ⟨x, hx, -⟩ := hC₁
  rw [hbd] at hx
  exact hx

end IsCylinder

/-- A *hoop* in a cylinder $\Sigma$ is an $O$-arc that is not null-homotopic in $\Sigma$.
Graph Minors VIII, Section 15 (page 279):
"There are two kinds of $O$-arc in a cylinder; those that are null-homotopic and bound a disc, and
those that wind once around $\Sigma$. A *hoop* is an $O$-arc of the second kind." -/
def IsHoop {S : Type w} [TopologicalSpace S] (F : Set S) : Prop :=
  IsOArc F ∧ ¬ IsNullHomotopicOArc F

theorem isNullHomotopicOArc_image_homeomorph {S : Type w} {S' : Type w'}
    [TopologicalSpace S] [TopologicalSpace S'] (e : S ≃ₜ S') {F : Set S} :
    IsNullHomotopicOArc (e '' F) ↔ IsNullHomotopicOArc F := by
  constructor
  · rintro ⟨φ, c, -, ψ, -, h0, h1⟩
    let φ' : Circle ≃ₜ F := φ.trans (e.isEmbedding.homeomorphImage F).symm
    refine ⟨φ', e.symm c, mem_univ _, ContinuousMap.comp ⟨e.symm, e.symm.continuous⟩ ψ,
      fun _ => mem_univ _, fun x => ?_, fun x => ?_⟩
    · change e.symm (ψ (x, 0)) = (φ' x).1
      rw [h0 x]
      change e.symm (φ x).1 = ((e.isEmbedding.homeomorphImage F).symm (φ x)).1
      obtain ⟨y, hy, hyeq⟩ := (φ x).2
      have hsub : (e.isEmbedding.homeomorphImage F) ⟨y, hy⟩ = φ x := Subtype.ext hyeq
      rw [← hsub, Homeomorph.symm_apply_apply]
      exact e.symm_apply_apply y
    · change e.symm (ψ (x, 1)) = e.symm c
      rw [h1 x]; rfl
  · rintro ⟨φ, c, -, ψ, -, h0, h1⟩
    let φ' : Circle ≃ₜ e '' F := φ.trans (e.isEmbedding.homeomorphImage F)
    refine ⟨φ', e c, mem_univ _, ContinuousMap.comp ⟨e, e.continuous⟩ ψ,
      fun _ => mem_univ _, fun x => ?_, fun x => ?_⟩
    · change e (ψ (x, 0)) = (φ' x).1
      rw [h0 x]; rfl
    · change e (ψ (x, 1)) = e c
      rw [h1 x]; rfl

namespace IsHoop

variable {S : Type w} [TopologicalSpace S] {F : Set S}

theorem isOArc (h : IsHoop F) : IsOArc F := h.1

theorem nonempty (h : IsHoop F) : F.Nonempty := by
  obtain ⟨φ⟩ := h.1
  exact ⟨(φ 1).1, (φ 1).2⟩

theorem isCompact (h : IsHoop F) : IsCompact F := by
  obtain ⟨φ⟩ := h.1
  have : F = range (fun x => (φ x).1) := by
    ext y
    exact ⟨fun hy => ⟨φ.symm ⟨y, hy⟩, by simp⟩, fun ⟨x, hx⟩ => hx ▸ (φ x).2⟩
  rw [this]
  exact isCompact_range (continuous_subtype_val.comp φ.continuous)

theorem isClosed [T2Space S] (h : IsHoop F) : IsClosed F := h.isCompact.isClosed

theorem image_homeomorph {S' : Type w'} [TopologicalSpace S'] (e : S ≃ₜ S') :
    IsHoop (e '' F) ↔ IsHoop F := by
  refine ⟨fun ⟨hO, hn⟩ => ⟨?_, fun hnull => hn ((isNullHomotopicOArc_image_homeomorph e).mpr hnull)⟩,
    fun ⟨⟨φ⟩, hn⟩ => ⟨⟨φ.trans (e.isEmbedding.homeomorphImage F)⟩,
      fun hnull => hn ((isNullHomotopicOArc_image_homeomorph e).mp hnull)⟩⟩
  obtain ⟨φ⟩ := hO
  exact ⟨φ.trans (e.isEmbedding.homeomorphImage F).symm⟩

end IsHoop

/-- A sphere `Z` obtained from a cylinder `S` by capping its two cuffs `C₁, C₂` with disjoint
closed discs `D₁, D₂` (`GM07.exists_sphere_cap`). -/
structure CylinderSphereCap (S : Type w) [TopologicalSpace S] where
  /-- The capped sphere type. -/
  Z : Type
  /-- Topology on `Z`. -/
  [tsZ : TopologicalSpace Z]
  /-- First cuff of `S`. -/
  C₁ : Set S
  /-- Second cuff of `S`. -/
  C₂ : Set S
  /-- The two cuffs are distinct. -/
  C₁_ne_C₂ : C₁ ≠ C₂
  /-- The cuffs of `S` are `{C₁, C₂}`. -/
  cuffs_eq : cuffs S = {C₁, C₂}
  /-- Closed embedding of `S` into `Z`. -/
  j : S → Z
  /-- First cap disc in `Z`. -/
  D₁ : Set Z
  /-- Second cap disc in `Z`. -/
  D₂ : Set Z
  /-- `Z` is a closed surface. -/
  isClosedSurface : IsClosedSurface Z
  /-- `Z` is a 2-sphere. -/
  isSphere : IsSphere Z
  /-- `Z` is connected. -/
  connectedSpace : ConnectedSpace Z
  /-- `j` is a closed embedding. -/
  isClosedEmbedding : IsClosedEmbedding j
  /-- `D₁` is a closed disc. -/
  isClosedDisc_D₁ : IsClosedDisc D₁
  /-- `D₂` is a closed disc. -/
  isClosedDisc_D₂ : IsClosedDisc D₂
  /-- `D₁` and `D₂` are disjoint. -/
  disjoint_D : Disjoint D₁ D₂
  /-- Boundary of `D₁` is `j '' C₁`. -/
  discBd_D₁ : discBd D₁ = j '' C₁
  /-- Boundary of `D₂` is `j '' C₂`. -/
  discBd_D₂ : discBd D₂ = j '' C₂
  /-- `range j ∪ D₁ ∪ D₂ = univ`. -/
  union_eq : range j ∪ D₁ ∪ D₂ = univ
  /-- `range j ∩ D₁ = j '' C₁`. -/
  inter_D₁ : range j ∩ D₁ = j '' C₁
  /-- `range j ∩ D₂ = j '' C₂`. -/
  inter_D₂ : range j ∩ D₂ = j '' C₂

attribute [instance] CylinderSphereCap.tsZ CylinderSphereCap.connectedSpace

namespace CylinderSphereCap

variable {S : Type w} [TopologicalSpace S]

theorem exists_of_isCylinder (hS : IsCylinder S) : Nonempty (CylinderSphereCap S) := by
  obtain ⟨C₁, C₂, hne, hcuffs⟩ := hS.exists_cuffs
  obtain ⟨Z, tZ, j, D₁, D₂, hcs, hsph, hconn, hj, hD₁, hD₂, hdis, hb₁, hb₂, hcov, hi₁, hi₂⟩ :=
    GM07.exists_sphere_cap hS.1 hS.2 hcuffs hne
  exact ⟨{
    Z := Z, tsZ := tZ, C₁ := C₁, C₂ := C₂, C₁_ne_C₂ := hne, cuffs_eq := hcuffs,
    j := j, D₁ := D₁, D₂ := D₂, isClosedSurface := hcs, isSphere := hsph,
    connectedSpace := hconn, isClosedEmbedding := hj, isClosedDisc_D₁ := hD₁,
    isClosedDisc_D₂ := hD₂, disjoint_D := hdis, discBd_D₁ := hb₁, discBd_D₂ := hb₂,
    union_eq := hcov, inter_D₁ := hi₁, inter_D₂ := hi₂ }⟩

/-- Swapping `(C₁, D₁)` and `(C₂, D₂)` in a `CylinderSphereCap`. -/
abbrev swap (cap : CylinderSphereCap S) : CylinderSphereCap S where
  Z := cap.Z
  tsZ := cap.tsZ
  C₁ := cap.C₂
  C₂ := cap.C₁
  C₁_ne_C₂ := cap.C₁_ne_C₂.symm
  cuffs_eq := by rw [cap.cuffs_eq, pair_comm]
  j := cap.j
  D₁ := cap.D₂
  D₂ := cap.D₁
  isClosedSurface := cap.isClosedSurface
  isSphere := cap.isSphere
  connectedSpace := cap.connectedSpace
  isClosedEmbedding := cap.isClosedEmbedding
  isClosedDisc_D₁ := cap.isClosedDisc_D₂
  isClosedDisc_D₂ := cap.isClosedDisc_D₁
  disjoint_D := cap.disjoint_D.symm
  discBd_D₁ := cap.discBd_D₂
  discBd_D₂ := cap.discBd_D₁
  union_eq := by rw [union_right_comm, cap.union_eq]
  inter_D₁ := cap.inter_D₂
  inter_D₂ := cap.inter_D₁

/-- Pulling back a `CylinderSphereCap S'` along a homeomorphism `e : S ≃ₜ S'`. -/
abbrev comapHomeomorph {S' : Type w'} [TopologicalSpace S'] (e : S ≃ₜ S')
    (cap : CylinderSphereCap S') : CylinderSphereCap S where
  Z := cap.Z
  tsZ := cap.tsZ
  C₁ := e.symm '' cap.C₁
  C₂ := e.symm '' cap.C₂
  C₁_ne_C₂ := fun h => cap.C₁_ne_C₂ (e.symm.injective.image_injective h)
  cuffs_eq := by
    have hc : cuffs S = image e.symm '' cuffs S' := by
      have hbd : bd S = e.symm '' bd S' := by
        ext x
        simp only [bd, mem_ofPred_eq, mem_image]
        constructor
        · intro hx
          refine ⟨e x, fun hi => hx ((isInteriorPoint_homeomorph_iff e x).mp hi), e.symm_apply_apply x⟩
        · rintro ⟨y, hy, rfl⟩ hi
          exact hy ((isInteriorPoint_homeomorph_iff e.symm y).mp hi)
      rw [cuffs, cuffs, hbd]
      exact componentsIn_image e.symm.continuous.continuousOn e.continuous.continuousOn
        (fun y _ => e.apply_symm_apply y)
    rw [hc, cap.cuffs_eq, image_pair]
  j := cap.j ∘ e
  D₁ := cap.D₁
  D₂ := cap.D₂
  isClosedSurface := cap.isClosedSurface
  isSphere := cap.isSphere
  connectedSpace := cap.connectedSpace
  isClosedEmbedding := cap.isClosedEmbedding.comp e.isClosedEmbedding
  isClosedDisc_D₁ := cap.isClosedDisc_D₁
  isClosedDisc_D₂ := cap.isClosedDisc_D₂
  disjoint_D := cap.disjoint_D
  discBd_D₁ := by
    rw [cap.discBd_D₁]
    simp [image_image]
  discBd_D₂ := by
    rw [cap.discBd_D₂]
    simp [image_image]
  union_eq := by
    rw [range_comp, e.surjective.range_eq, image_univ, cap.union_eq]
  inter_D₁ := by
    rw [range_comp, e.surjective.range_eq, image_univ, cap.inter_D₁]
    simp [image_image]
  inter_D₂ := by
    rw [range_comp, e.surjective.range_eq, image_univ, cap.inter_D₂]
    simp [image_image]

theorem t2Space_Z (cap : CylinderSphereCap S) : T2Space cap.Z := cap.isClosedSurface.2.1

theorem compactSpace_Z (cap : CylinderSphereCap S) : CompactSpace cap.Z := cap.isClosedSurface.1

theorem isManifoldPoint_Z (cap : CylinderSphereCap S) (z : cap.Z) : IsManifoldPoint z :=
  (cap.isClosedSurface.2.2 z).isManifoldPoint

theorem inj (cap : CylinderSphereCap S) : Injective cap.j :=
  cap.isClosedEmbedding.injective

theorem C₁_mem_cuffs (cap : CylinderSphereCap S) : cap.C₁ ∈ cuffs S := by
  rw [cap.cuffs_eq]; simp

theorem C₂_mem_cuffs (cap : CylinderSphereCap S) : cap.C₂ ∈ cuffs S := by
  rw [cap.cuffs_eq]; simp

theorem disjoint_cuffs (cap : CylinderSphereCap S) : Disjoint cap.C₁ cap.C₂ :=
  cuffs_disjoint cap.C₁_mem_cuffs cap.C₂_mem_cuffs cap.C₁_ne_C₂

theorem bd_eq (cap : CylinderSphereCap S) : bd S = cap.C₁ ∪ cap.C₂ := by
  rw [← sUnion_cuffs, cap.cuffs_eq, sUnion_pair]

theorem mem_C₁_of_j_mem_D₁ (cap : CylinderSphereCap S) {x : S} (hx : cap.j x ∈ cap.D₁) :
    x ∈ cap.C₁ := by
  have h : cap.j x ∈ range cap.j ∩ cap.D₁ := ⟨⟨x, rfl⟩, hx⟩
  rw [cap.inter_D₁] at h
  obtain ⟨y, hy, he⟩ := h
  exact cap.inj he ▸ hy

theorem mem_C₂_of_j_mem_D₂ (cap : CylinderSphereCap S) {x : S} (hx : cap.j x ∈ cap.D₂) :
    x ∈ cap.C₂ := by
  have h : cap.j x ∈ range cap.j ∩ cap.D₂ := ⟨⟨x, rfl⟩, hx⟩
  rw [cap.inter_D₂] at h
  obtain ⟨y, hy, he⟩ := h
  exact cap.inj he ▸ hy

theorem disjoint_range_discInt_D₁ (cap : CylinderSphereCap S) :
    Disjoint (range cap.j) (discInt cap.D₁) := by
  refine disjoint_left.mpr ?_
  rintro _ ⟨x, rfl⟩ ⟨hxD, hxB⟩
  exact hxB (cap.discBd_D₁ ▸ mem_image_of_mem cap.j (cap.mem_C₁_of_j_mem_D₁ hxD))

theorem disjoint_range_discInt_D₂ (cap : CylinderSphereCap S) :
    Disjoint (range cap.j) (discInt cap.D₂) := by
  refine disjoint_left.mpr ?_
  rintro _ ⟨x, rfl⟩ ⟨hxD, hxB⟩
  exact hxB (cap.discBd_D₂ ▸ mem_image_of_mem cap.j (cap.mem_C₂_of_j_mem_D₂ hxD))

theorem subset_range_of_disjoint_discInts (cap : CylinderSphereCap S) {X : Set cap.Z}
    (h1 : Disjoint X (discInt cap.D₁)) (h2 : Disjoint X (discInt cap.D₂)) :
    X ⊆ range cap.j := by
  intro z hz
  have hc : z ∈ range cap.j ∪ cap.D₁ ∪ cap.D₂ := cap.union_eq ▸ mem_univ z
  rcases hc with (h | h) | h
  · exact h
  · have hb : z ∈ discBd cap.D₁ := by
      by_contra hn
      exact disjoint_left.mp h1 hz ⟨h, hn⟩
    rw [cap.discBd_D₁] at hb
    exact image_subset_range _ _ hb
  · have hb : z ∈ discBd cap.D₂ := by
      by_contra hn
      exact disjoint_left.mp h2 hz ⟨h, hn⟩
    rw [cap.discBd_D₂] at hb
    exact image_subset_range _ _ hb

theorem isOArc_image (cap : CylinderSphereCap S) {F : Set S} (hF : IsOArc F) :
    IsOArc (cap.j '' F) := by
  obtain ⟨φ⟩ := hF
  exact ⟨φ.trans (cap.isClosedEmbedding.isEmbedding.homeomorphImage F)⟩

/-- If `Δ` is a closed disc in `cap.Z` whose boundary is disjoint from `discInt D_i`, then
either `D_i ⊆ Δ` or `Disjoint (discInt D_i) Δ`. -/
theorem disc_subset_or_disjoint (cap : CylinderSphereCap S) {Δ D : Set cap.Z}
    (hΔ : IsClosedDisc Δ) (hD : IsClosedDisc D) (hdis : Disjoint (discBd Δ) (discInt D)) :
    D ⊆ Δ ∨ Disjoint (discInt D) Δ := by
  have : T2Space cap.Z := cap.t2Space_Z
  by_cases hne : (discInt D ∩ Δ).Nonempty
  · left
    have hopenΔ : IsOpen (discInt Δ) := hΔ.isOpen_discInt cap.isManifoldPoint_Z
    have hclΔ : IsClosed Δ := hΔ.isCompact.isClosed
    have hsub_int : discInt D ⊆ Δ := by
      obtain ⟨z₀, hz₀D, hz₀Δ⟩ := hne
      have hz₀_int : z₀ ∈ discInt Δ := ⟨hz₀Δ, fun hb => disjoint_left.mp hdis hb hz₀D⟩
      by_contra hnot
      obtain ⟨z₁, hz₁D, hz₁n⟩ := not_subset.mp hnot
      have hcov : discInt D ⊆ discInt Δ ∪ (univ \ Δ) := fun z hz => by
        by_cases hzΔ : z ∈ Δ
        · exact Or.inl ⟨hzΔ, fun hb => disjoint_left.mp hdis hb hz⟩
        · exact Or.inr ⟨mem_univ z, hzΔ⟩
      have hd : Disjoint (discInt D ∩ discInt Δ) (discInt D ∩ (univ \ Δ)) :=
        disjoint_left.mpr fun z h1 h2 => h2.2.2 h1.2.1
      rcases hD.isPreconnected_discInt (discInt Δ) (univ \ Δ) hopenΔ (isOpen_univ.sdiff hclΔ) hcov
          ⟨z₀, hz₀D, hz₀_int⟩ ⟨z₁, hz₁D, mem_univ z₁, hz₁n⟩ with ⟨w, hwD, hw1, hw2⟩
      exact hw2.2 (discInt_subset Δ hw1)
    exact hD.subset_closure_discInt.trans (closure_minimal hsub_int hclΔ)
  · exact Or.inr (not_nonempty_iff_eq_empty.mp hne |> disjoint_iff_inter_eq_empty.mpr)

/-- Characterization of hoops in `S` via `cap : CylinderSphereCap S`: an `O`-arc `F` is a hoop
if and only if `j '' F` bounds two closed discs `E₁ ⊇ D₁` and `E₂ ⊇ D₂` in `cap.Z`. -/
theorem isHoop_iff_exists_discs (cap : CylinderSphereCap S) (hS : IsSurface S) {F : Set S}
    (hF : IsOArc F) :
    IsHoop F ↔ ∃ E₁ E₂ : Set cap.Z,
      IsClosedDisc E₁ ∧ IsClosedDisc E₂ ∧
      discBd E₁ = cap.j '' F ∧ discBd E₂ = cap.j '' F ∧
      E₁ ∪ E₂ = univ ∧ E₁ ∩ E₂ = cap.j '' F ∧
      cap.D₁ ⊆ E₁ ∧ cap.D₂ ⊆ E₂ := by
  have : T2Space S := hS.2.1
  have : T2Space cap.Z := cap.t2Space_Z
  obtain ⟨p, hp⟩ := cap.isClosedDisc_D₁.nonempty_discInt
  obtain ⟨a, ha⟩ := cap.isClosedDisc_D₂.nonempty_discInt
  have hpr : p ∉ range cap.j := fun hr => disjoint_left.mp cap.disjoint_range_discInt_D₁ hr hp
  have har : a ∉ range cap.j := fun hr => disjoint_left.mp cap.disjoint_range_discInt_D₂ hr ha
  constructor
  · intro hhoop
    obtain ⟨Δ₁, Δ₂, -, h1, h2, b1, b2, hcup, hcap_eq, -, -⟩ :=
      sphere_disc cap.Z cap.isSphere (cap.j '' F) (cap.isOArc_image hF)
    have hdisF1 : Disjoint (cap.j '' F) (discInt cap.D₁) :=
      cap.disjoint_range_discInt_D₁.mono_left (image_subset_range _ _)
    have hdisF2 : Disjoint (cap.j '' F) (discInt cap.D₂) :=
      cap.disjoint_range_discInt_D₂.mono_left (image_subset_range _ _)
    have hD1_or : cap.D₁ ⊆ Δ₁ ∨ cap.D₁ ⊆ Δ₂ := by
      rcases cap.disc_subset_or_disjoint h1 cap.isClosedDisc_D₁ (b1 ▸ hdisF1) with h | h
      · exact Or.inl h
      · right
        rcases cap.disc_subset_or_disjoint h2 cap.isClosedDisc_D₁ (b2 ▸ hdisF1) with h' | h'
        · exact h'
        · exfalso
          rcases (hcup ▸ mem_univ p : p ∈ Δ₁ ∪ Δ₂) with hp1 | hp2
          · exact disjoint_left.mp h hp hp1
          · exact disjoint_left.mp h' hp hp2
    have hD2_or : cap.D₂ ⊆ Δ₁ ∨ cap.D₂ ⊆ Δ₂ := by
      rcases cap.disc_subset_or_disjoint h1 cap.isClosedDisc_D₂ (b1 ▸ hdisF2) with h | h
      · exact Or.inl h
      · right
        rcases cap.disc_subset_or_disjoint h2 cap.isClosedDisc_D₂ (b2 ▸ hdisF2) with h' | h'
        · exact h'
        · exfalso
          rcases (hcup ▸ mem_univ a : a ∈ Δ₁ ∪ Δ₂) with ha1 | ha2
          · exact disjoint_left.mp h ha ha1
          · exact disjoint_left.mp h' ha ha2
    rcases hD1_or with hD1_1 | hD1_2 <;> rcases hD2_or with hD2_1 | hD2_2
    · exfalso
      have hdis2_1 : Disjoint Δ₂ (discInt cap.D₁) := by
        refine disjoint_left.mpr fun z hz2 hz1 => ?_
        have hzf : z ∈ cap.j '' F := hcap_eq ▸ ⟨hD1_1 hz1.1, hz2⟩
        exact disjoint_left.mp hdisF1 hzf hz1
      have hdis2_2 : Disjoint Δ₂ (discInt cap.D₂) := by
        refine disjoint_left.mpr fun z hz2 hz2' => ?_
        have hzf : z ∈ cap.j '' F := hcap_eq ▸ ⟨hD2_1 hz2'.1, hz2⟩
        exact disjoint_left.mp hdisF2 hzf hz2'
      have hsubr := cap.subset_range_of_disjoint_discInts hdis2_1 hdis2_2
      obtain ⟨eΔ, -⟩ := GM07.exists_pull_homeo cap.isClosedEmbedding.isEmbedding hsubr
      obtain ⟨φΔ⟩ := h2
      have hdiscS : IsClosedDisc (cap.j ⁻¹' Δ₂) := ⟨φΔ.trans eΔ.symm⟩
      have hFsub : F ⊆ cap.j ⁻¹' Δ₂ :=
        fun x hx => Surface.discBd_subset Δ₂ (b2 ▸ mem_image_of_mem _ hx)
      exact hhoop.2 (isNullHomotopicOArcIn_of_subset_disc hF (subset_univ _) hdiscS hFsub)
    · exact ⟨Δ₁, Δ₂, h1, h2, b1, b2, hcup, hcap_eq, hD1_1, hD2_2⟩
    · exact ⟨Δ₂, Δ₁, h2, h1, b2, b1, by rw [union_comm, hcup], by rw [inter_comm, hcap_eq],
        hD1_2, hD2_1⟩
    · exfalso
      have hdis1_1 : Disjoint Δ₁ (discInt cap.D₁) := by
        refine disjoint_left.mpr fun z hz1 hz1' => ?_
        have hzf : z ∈ cap.j '' F := hcap_eq ▸ ⟨hz1, hD1_2 hz1'.1⟩
        exact disjoint_left.mp hdisF1 hzf hz1'
      have hdis1_2 : Disjoint Δ₁ (discInt cap.D₂) := by
        refine disjoint_left.mpr fun z hz1 hz2' => ?_
        have hzf : z ∈ cap.j '' F := hcap_eq ▸ ⟨hz1, hD2_2 hz2'.1⟩
        exact disjoint_left.mp hdisF2 hzf hz2'
      have hsubr := cap.subset_range_of_disjoint_discInts hdis1_1 hdis1_2
      obtain ⟨eΔ, -⟩ := GM07.exists_pull_homeo cap.isClosedEmbedding.isEmbedding hsubr
      obtain ⟨φΔ⟩ := h1
      have hdiscS : IsClosedDisc (cap.j ⁻¹' Δ₁) := ⟨φΔ.trans eΔ.symm⟩
      have hFsub : F ⊆ cap.j ⁻¹' Δ₁ :=
        fun x hx => Surface.discBd_subset Δ₁ (b1 ▸ mem_image_of_mem _ hx)
      exact hhoop.2 (isNullHomotopicOArcIn_of_subset_disc hF (subset_univ _) hdiscS hFsub)
  · rintro ⟨E₁, E₂, hE₁, -, hb₁, -, -, hcap_eq, hD₁, hD₂⟩
    refine ⟨hF, ?_⟩
    have ha_not : a ∉ E₁ := fun ha1 => by
      have haf : a ∈ cap.j '' F := hcap_eq ▸ ⟨ha1, hD₂ ha.1⟩
      exact har (image_subset_range _ _ haf)
    exact GM07.not_null_of_separating hS cap.isSphere cap.isClosedEmbedding hF hE₁ hb₁
      (hD₁ hp.1) ha_not hpr har

/-- Uniqueness of the two discs `(E₁, E₂)` bounded by `j '' F` with `D₁ ⊆ E₁` and `D₂ ⊆ E₂`. -/
theorem hoop_discs_unique (cap : CylinderSphereCap S) {F : Set S}
    {E₁ E₂ E₁' E₂' : Set cap.Z}
    (hE₁ : IsClosedDisc E₁) (hE₂ : IsClosedDisc E₂)
    (hb₁ : discBd E₁ = cap.j '' F) (hb₂ : discBd E₂ = cap.j '' F)
    (hinter : E₁ ∩ E₂ = cap.j '' F) (hD₁ : cap.D₁ ⊆ E₁) (hD₂ : cap.D₂ ⊆ E₂)
    (hE₁' : IsClosedDisc E₁') (hE₂' : IsClosedDisc E₂')
    (hb₁' : discBd E₁' = cap.j '' F) (hb₂' : discBd E₂' = cap.j '' F)
    (hD₁' : cap.D₁ ⊆ E₁') (hD₂' : cap.D₂ ⊆ E₂') :
    E₁' = E₁ ∧ E₂' = E₂ := by
  have hFO : IsOArc (cap.j '' F) := hb₁ ▸ hE₁.isOArc_discBd
  obtain ⟨Δ₁, Δ₂, -, -, -, -, -, -, -, -, huniq⟩ := sphere_disc cap.Z cap.isSphere _ hFO
  obtain ⟨p, hp⟩ := cap.isClosedDisc_D₁.nonempty_discInt
  obtain ⟨a, ha⟩ := cap.isClosedDisc_D₂.nonempty_discInt
  have hpr : p ∉ range cap.j := fun hr => disjoint_left.mp cap.disjoint_range_discInt_D₁ hr hp
  have har : a ∉ range cap.j := fun hr => disjoint_left.mp cap.disjoint_range_discInt_D₂ hr ha
  have h12_ne : E₁ ≠ E₂ := fun heq => by
    have hp_in : p ∈ cap.j '' F := hinter ▸ ⟨hD₁ hp.1, heq ▸ hD₁ hp.1⟩
    exact hpr (image_subset_range _ _ hp_in)
  have hpair : ∀ Δ, IsClosedDisc Δ → discBd Δ = cap.j '' F → Δ = E₁ ∨ Δ = E₂ := by
    intro Δ hΔ hbΔ
    rcases huniq E₁ hE₁ hb₁ with rfl | rfl <;> rcases huniq E₂ hE₂ hb₂ with h | h
    · exact absurd h.symm h12_ne
    · subst h; exact huniq Δ hΔ hbΔ
    · subst h; exact (huniq Δ hΔ hbΔ).symm
    · exact absurd h.symm h12_ne
  refine ⟨?_, ?_⟩
  · rcases hpair E₁' hE₁' hb₁' with h | h
    · exact h
    · exfalso
      have hp_in : p ∈ cap.j '' F := hinter ▸ ⟨hD₁ hp.1, h ▸ hD₁' hp.1⟩
      exact hpr (image_subset_range _ _ hp_in)
  · rcases hpair E₂' hE₂' hb₂' with h | h
    · exfalso
      have ha_in : a ∈ cap.j '' F := hinter ▸ ⟨h ▸ hD₂' ha.1, hD₂ ha.1⟩
      exact har (image_subset_range _ _ ha_in)
    · exact h

/-- Both cuffs `C₁` and `C₂` of a cylinder `S` are hoops. -/
theorem isHoop_C₁ (cap : CylinderSphereCap S) (hS : IsSurface S) : IsHoop cap.C₁ := by
  have hO : IsOArc cap.C₁ := (cuff_statement S hS).2.2 cap.C₁ cap.C₁_mem_cuffs
  rw [cap.isHoop_iff_exists_discs hS hO]
  obtain ⟨Δ₁, Δ₂, hne, h1, h2, b1, b2, hcup, hcap, -, huniq⟩ :=
    sphere_disc cap.Z cap.isSphere (cap.j '' cap.C₁) (cap.isOArc_image hO)
  rcases huniq cap.D₁ cap.isClosedDisc_D₁ cap.discBd_D₁ with rfl | rfl
  · refine ⟨cap.D₁, Δ₂, cap.isClosedDisc_D₁, h2, cap.discBd_D₁, b2, hcup, hcap, Subset.rfl, ?_⟩
    intro z hz
    exact (hcup ▸ mem_univ z).resolve_left (disjoint_right.mp cap.disjoint_D hz)
  · refine ⟨cap.D₁, Δ₁, cap.isClosedDisc_D₁, h1, cap.discBd_D₁, b1,
      by rw [union_comm, hcup], by rw [inter_comm, hcap], Subset.rfl, ?_⟩
    intro z hz
    exact (hcup ▸ mem_univ z).resolve_right (disjoint_right.mp cap.disjoint_D hz)

theorem isHoop_C₂ (cap : CylinderSphereCap S) (hS : IsSurface S) : IsHoop cap.C₂ :=
  cap.swap.isHoop_C₁ hS

/-- For a hoop `F` in `S`, `cap.disc₁ hS hF` is the unique closed disc in `cap.Z` bounded by
`j '' F` that contains `D₁`. -/
noncomputable def disc₁ (cap : CylinderSphereCap S) (hS : IsSurface S) {F : Set S}
    (hF : IsHoop F) : Set cap.Z :=
  Classical.choose ((cap.isHoop_iff_exists_discs hS hF.1).mp hF)

/-- For a hoop `F` in `S`, `cap.disc₂ hS hF` is the unique closed disc in `cap.Z` bounded by
`j '' F` that contains `D₂`. -/
noncomputable def disc₂ (cap : CylinderSphereCap S) (hS : IsSurface S) {F : Set S}
    (hF : IsHoop F) : Set cap.Z :=
  Classical.choose (Classical.choose_spec ((cap.isHoop_iff_exists_discs hS hF.1).mp hF))

theorem disc₁_disc₂_spec (cap : CylinderSphereCap S) (hS : IsSurface S) {F : Set S}
    (hF : IsHoop F) :
    IsClosedDisc (cap.disc₁ hS hF) ∧ IsClosedDisc (cap.disc₂ hS hF) ∧
    discBd (cap.disc₁ hS hF) = cap.j '' F ∧ discBd (cap.disc₂ hS hF) = cap.j '' F ∧
    cap.disc₁ hS hF ∪ cap.disc₂ hS hF = univ ∧
    cap.disc₁ hS hF ∩ cap.disc₂ hS hF = cap.j '' F ∧
    cap.D₁ ⊆ cap.disc₁ hS hF ∧ cap.D₂ ⊆ cap.disc₂ hS hF :=
  Classical.choose_spec (Classical.choose_spec ((cap.isHoop_iff_exists_discs hS hF.1).mp hF))

/-- The `C₁`-side of a hoop `F` in `S`: `j ⁻¹' (discInt (cap.disc₁ hS hF))`. -/
noncomputable def side₁ (cap : CylinderSphereCap S) (hS : IsSurface S) {F : Set S}
    (hF : IsHoop F) : Set S :=
  cap.j ⁻¹' discInt (cap.disc₁ hS hF)

/-- The `C₂`-side of a hoop `F` in `S`: `j ⁻¹' (discInt (cap.disc₂ hS hF))`. -/
noncomputable def side₂ (cap : CylinderSphereCap S) (hS : IsSurface S) {F : Set S}
    (hF : IsHoop F) : Set S :=
  cap.j ⁻¹' discInt (cap.disc₂ hS hF)

theorem side₁_eq_preimage_diff (cap : CylinderSphereCap S) (hS : IsSurface S) {F : Set S}
    (hF : IsHoop F) :
    cap.side₁ hS hF = cap.j ⁻¹' (cap.disc₁ hS hF \ cap.j '' F) := by
  simp only [side₁, discInt, (cap.disc₁_disc₂_spec hS hF).2.2.1]

theorem side₂_eq_preimage_diff (cap : CylinderSphereCap S) (hS : IsSurface S) {F : Set S}
    (hF : IsHoop F) :
    cap.side₂ hS hF = cap.j ⁻¹' (cap.disc₂ hS hF \ cap.j '' F) := by
  simp only [side₂, discInt, (cap.disc₁_disc₂_spec hS hF).2.2.2.1]

theorem isOpen_side₁ (cap : CylinderSphereCap S) (hS : IsSurface S) {F : Set S} (hF : IsHoop F) :
    IsOpen (cap.side₁ hS hF) :=
  ((cap.disc₁_disc₂_spec hS hF).1.isOpen_discInt cap.isManifoldPoint_Z).preimage
    cap.isClosedEmbedding.continuous

theorem isOpen_side₂ (cap : CylinderSphereCap S) (hS : IsSurface S) {F : Set S} (hF : IsHoop F) :
    IsOpen (cap.side₂ hS hF) :=
  ((cap.disc₁_disc₂_spec hS hF).2.1.isOpen_discInt cap.isManifoldPoint_Z).preimage
    cap.isClosedEmbedding.continuous

theorem side₁_union_side₂ (cap : CylinderSphereCap S) (hS : IsSurface S) {F : Set S}
    (hF : IsHoop F) :
    cap.side₁ hS hF ∪ cap.side₂ hS hF = univ \ F := by
  obtain ⟨-, -, hb₁, hb₂, hcup, hcap, -, -⟩ := cap.disc₁_disc₂_spec hS hF
  ext x
  simp only [side₁, side₂, discInt, hb₁, hb₂, mem_union, mem_preimage, mem_sdiff, mem_univ,
    true_and, mem_image, cap.inj.eq_iff, exists_eq_right]
  constructor
  · rintro (⟨_, hnf⟩ | ⟨_, hnf⟩) <;> exact hnf
  · intro hnf
    rcases (hcup ▸ mem_univ (cap.j x) : cap.j x ∈ cap.disc₁ hS hF ∪ cap.disc₂ hS hF) with h1 | h2
    · exact Or.inl ⟨h1, hnf⟩
    · exact Or.inr ⟨h2, hnf⟩

theorem disjoint_side₁_side₂ (cap : CylinderSphereCap S) (hS : IsSurface S) {F : Set S}
    (hF : IsHoop F) :
    Disjoint (cap.side₁ hS hF) (cap.side₂ hS hF) := by
  obtain ⟨-, -, hb₁, -, -, hcap, -, -⟩ := cap.disc₁_disc₂_spec hS hF
  refine disjoint_left.mpr fun x hx1 hx2 => ?_
  rw [cap.side₁_eq_preimage_diff hS hF] at hx1
  rw [cap.side₂_eq_preimage_diff hS hF] at hx2
  exact hx1.2 (hcap ▸ ⟨hx1.1, hx2.1⟩)

theorem C₁_diff_subset_side₁ (cap : CylinderSphereCap S) (hS : IsSurface S) {F : Set S}
    (hF : IsHoop F) :
    cap.C₁ \ F ⊆ cap.side₁ hS hF := by
  obtain ⟨-, -, -, -, -, -, hD₁, -⟩ := cap.disc₁_disc₂_spec hS hF
  intro x ⟨hxC, hxF⟩
  rw [cap.side₁_eq_preimage_diff hS hF]
  refine ⟨hD₁ (Surface.discBd_subset _ (cap.discBd_D₁ ▸ mem_image_of_mem _ hxC)), ?_⟩
  rintro ⟨y, hyF, heq⟩
  exact hxF (cap.inj heq ▸ hyF)

theorem C₂_diff_subset_side₂ (cap : CylinderSphereCap S) (hS : IsSurface S) {F : Set S}
    (hF : IsHoop F) :
    cap.C₂ \ F ⊆ cap.side₂ hS hF := by
  obtain ⟨-, -, -, -, -, -, -, hD₂⟩ := cap.disc₁_disc₂_spec hS hF
  intro x ⟨hxC, hxF⟩
  rw [cap.side₂_eq_preimage_diff hS hF]
  refine ⟨hD₂ (Surface.discBd_subset _ (cap.discBd_D₂ ▸ mem_image_of_mem _ hxC)), ?_⟩
  rintro ⟨y, hyF, heq⟩
  exact hxF (cap.inj heq ▸ hyF)

/-- Every connected component `K` of `S \ F` contained in `cap.side₁ hS hF` meets `C₁ \ F`.
This makes `{cap.side₁ hS hF, cap.side₂ hS hF}` strictly intrinsic to `(S, F)`, independent of
the choice of `cap : CylinderSphereCap S`. -/
theorem component_meets_C₁_of_subset_side₁ (cap : CylinderSphereCap S) (hS : IsSurface S)
    {F K : Set S} (hF : IsHoop F) (hK : K ∈ componentsIn (univ \ F))
    (hKsub : K ⊆ cap.side₁ hS hF) :
    (K ∩ (cap.C₁ \ F)).Nonempty := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := hS.locallyConnected
  have : T2Space cap.Z := cap.t2Space_Z
  obtain ⟨hE₁, -, hb₁, -, -, -, hD₁, -⟩ := cap.disc₁_disc₂_spec hS hF
  obtain ⟨x₀, hx₀F, rfl⟩ := hK
  let K₀ := connectedComponentIn (univ \ F) x₀
  have hK₀_open : IsOpen K₀ := (isOpen_univ.sdiff hF.isClosed).connectedComponentIn
  have hK₀_subF : K₀ ⊆ univ \ F := connectedComponentIn_subset _ _
  by_contra hdis_ne
  have hdisC₁ : Disjoint K₀ cap.C₁ := by
    refine disjoint_left.mpr fun x hxK hxC => hdis_ne ⟨x, hxK, hxC, (hK₀_subF hxK).2⟩
  have hdisC₂ : Disjoint K₀ cap.C₂ := by
    refine disjoint_left.mpr fun x hxK hxC => ?_
    have hx2 : x ∈ cap.side₂ hS hF := cap.C₂_diff_subset_side₂ hS hF ⟨hxC, (hK₀_subF hxK).2⟩
    exact disjoint_left.mp (cap.disjoint_side₁_side₂ hS hF) (hKsub hxK) hx2
  have hjK_dis1 : Disjoint (cap.j '' K₀) cap.D₁ := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨x, hxK, rfl⟩ hxD
    exact disjoint_left.mp hdisC₁ hxK (cap.mem_C₁_of_j_mem_D₁ hxD)
  have hjK_dis2 : Disjoint (cap.j '' K₀) cap.D₂ := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨x, hxK, rfl⟩ hxD
    exact disjoint_left.mp hdisC₂ hxK (cap.mem_C₂_of_j_mem_D₂ hxD)
  have hjK_compl : (cap.j '' K₀)ᶜ = cap.j '' K₀ᶜ ∪ cap.D₁ ∪ cap.D₂ := by
    ext z
    simp only [mem_compl_iff, mem_union]
    constructor
    · intro hnz
      rcases (cap.union_eq ▸ mem_univ z : z ∈ range cap.j ∪ cap.D₁ ∪ cap.D₂) with (⟨x, rfl⟩ | h) | h
      · exact Or.inl (Or.inl ⟨x, fun hxK => hnz ⟨x, hxK, rfl⟩, rfl⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · rintro ((⟨x, hx, rfl⟩ | h) | h) ⟨y, hyK, heq⟩
      · exact hx (cap.inj heq ▸ hyK)
      · exact disjoint_left.mp hjK_dis1 ⟨y, hyK, heq⟩ h
      · exact disjoint_left.mp hjK_dis2 ⟨y, hyK, heq⟩ h
  have hjK_open : IsOpen (cap.j '' K₀) := by
    rw [← isClosed_compl_iff, hjK_compl]
    exact ((cap.isClosedEmbedding.isClosedMap _ hK₀_open.isClosed_compl).union
      cap.isClosedDisc_D₁.isCompact.isClosed).union cap.isClosedDisc_D₂.isCompact.isClosed
  have hjK_cl : closure (cap.j '' K₀) ∩ discInt (cap.disc₁ hS hF) ⊆ cap.j '' K₀ := by
    have hcl_eq : closure (cap.j '' K₀) = cap.j '' closure K₀ :=
      (image_closure_subset_closure_image cap.isClosedEmbedding.continuous).antisymm'
        (closure_minimal (image_mono subset_closure)
          (cap.isClosedEmbedding.isClosedMap _ isClosed_closure))
    rw [hcl_eq]
    rintro _ ⟨⟨x, hxcl, rfl⟩, hxInt⟩
    have hxF : x ∈ univ \ F := ⟨mem_univ x, fun hx => hxInt.2 (hb₁ ▸ mem_image_of_mem _ hx)⟩
    have hxU : IsOpen (connectedComponentIn (univ \ F) x) :=
      (isOpen_univ.sdiff hF.isClosed).connectedComponentIn
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp hxcl _ hxU (mem_connectedComponentIn hxF)
    have hxeq : connectedComponentIn (univ \ F) x = K₀ :=
      (connectedComponentIn_eq hw1).trans (connectedComponentIn_eq hw2).symm
    exact ⟨x, hxeq ▸ mem_connectedComponentIn hxF, rfl⟩
  obtain ⟨p, hp⟩ := cap.isClosedDisc_D₁.nonempty_discInt
  have hpr : p ∉ range cap.j := fun hr => disjoint_left.mp cap.disjoint_range_discInt_D₁ hr hp
  have hpInt : p ∈ discInt (cap.disc₁ hS hF) :=
    ⟨hD₁ hp.1, fun hb => hpr (hb₁ ▸ hb |> image_subset_range _ _)⟩
  have hcov : discInt (cap.disc₁ hS hF) ⊆ cap.j '' K₀ ∪ (univ \ closure (cap.j '' K₀)) :=
    fun z hz => by
      by_cases hzK : z ∈ cap.j '' K₀
      · exact Or.inl hzK
      · exact Or.inr ⟨mem_univ z, fun hzcl => hzK (hjK_cl ⟨hzcl, hz⟩)⟩
  have hpn : p ∉ cap.j '' K₀ := fun hk => hpr (image_subset_range _ _ hk)
  rcases hE₁.isPreconnected_discInt (cap.j '' K₀) (univ \ closure (cap.j '' K₀))
      hjK_open (isOpen_univ.sdiff isClosed_closure) hcov
      ⟨cap.j x₀, hKsub (mem_connectedComponentIn hx₀F),
        mem_image_of_mem _ (mem_connectedComponentIn hx₀F)⟩
      ⟨p, hpInt, mem_univ p, fun hcl => hpn (hjK_cl ⟨hcl, hpInt⟩)⟩ with ⟨z, -, hz1, hz2⟩
  exact hz2.2 (subset_closure hz1)

theorem side₁_eq_sUnion_components (cap : CylinderSphereCap S) (hS : IsSurface S) {F : Set S}
    (hF : IsHoop F) :
    cap.side₁ hS hF =
      ⋃₀ {K ∈ componentsIn (univ \ F) | (K ∩ (cap.C₁ \ F)).Nonempty} := by
  have hcov := cap.side₁_union_side₂ hS hF
  have hdis := cap.disjoint_side₁_side₂ hS hF
  ext x
  simp only [mem_sUnion, mem_ofPred_eq]
  constructor
  · intro hx1
    have hxF : x ∈ univ \ F := hcov ▸ Or.inl hx1
    let K := connectedComponentIn (univ \ F) x
    have hK_mem : K ∈ componentsIn (univ \ F) := ⟨x, hxF, rfl⟩
    have hK_sub : K ⊆ cap.side₁ hS hF := by
      intro y hy
      rcases (hcov ▸ connectedComponentIn_subset _ _ hy : y ∈ cap.side₁ hS hF ∪ cap.side₂ hS hF)
        with hy1 | hy2
      · exact hy1
      · exfalso
        rcases isPreconnected_connectedComponentIn (cap.side₁ hS hF) (cap.side₂ hS hF)
            (cap.isOpen_side₁ hS hF) (cap.isOpen_side₂ hS hF)
            (hcov ▸ connectedComponentIn_subset _ _)
            ⟨x, mem_connectedComponentIn hxF, hx1⟩ ⟨y, hy, hy2⟩ with ⟨z, -, hz1, hz2⟩
        exact disjoint_left.mp hdis hz1 hz2
    exact ⟨K, ⟨hK_mem, cap.component_meets_C₁_of_subset_side₁ hS hF hK_mem hK_sub⟩,
      mem_connectedComponentIn hxF⟩
  · rintro ⟨K, ⟨hK_mem, z, hzK, hzC₁⟩, hxK⟩
    obtain ⟨x₀, hx₀F, rfl⟩ := hK_mem
    have hz1 : z ∈ cap.side₁ hS hF := cap.C₁_diff_subset_side₁ hS hF hzC₁
    rcases (hcov ▸ connectedComponentIn_subset _ _ hxK : x ∈ cap.side₁ hS hF ∪ cap.side₂ hS hF)
      with hx1 | hx2
    · exact hx1
    · exfalso
      rcases isPreconnected_connectedComponentIn (cap.side₁ hS hF) (cap.side₂ hS hF)
          (cap.isOpen_side₁ hS hF) (cap.isOpen_side₂ hS hF)
          (hcov ▸ connectedComponentIn_subset _ _)
          ⟨z, hzK, hz1⟩ ⟨x, hxK, hx2⟩ with ⟨w, -, hw1, hw2⟩
      exact disjoint_left.mp hdis hw1 hw2

theorem side₂_eq_sUnion_components (cap : CylinderSphereCap S) (hS : IsSurface S) {F : Set S}
    (hF : IsHoop F) :
    cap.side₂ hS hF =
      ⋃₀ {K ∈ componentsIn (univ \ F) | (K ∩ (cap.C₂ \ F)).Nonempty} := by
  have heq : cap.side₂ hS hF = cap.swap.side₁ hS hF := by
    obtain ⟨h1, h2, hb1, hb2, _, hcap, hD1, hD2⟩ := cap.disc₁_disc₂_spec hS hF
    obtain ⟨h1', h2', hb1', hb2', _, _, hD1', hD2'⟩ := cap.swap.disc₁_disc₂_spec hS hF
    have huniq := cap.swap.hoop_discs_unique h2 h1 hb2 hb1 (by rw [inter_comm, hcap]) hD2 hD1
      h1' h2' hb1' hb2' hD1' hD2'
    simp only [side₂, side₁, swap, huniq.1]
  rw [heq]
  exact cap.swap.side₁_eq_sUnion_components hS hF

theorem sides_pair_eq_of_caps (cap cap' : CylinderSphereCap S) (hS : IsSurface S) {F : Set S}
    (hF : IsHoop F) :
    ({cap.side₁ hS hF, cap.side₂ hS hF} : Set (Set S)) =
      {cap'.side₁ hS hF, cap'.side₂ hS hF} := by
  have hcuffs : ({cap.C₁, cap.C₂} : Set (Set S)) = {cap'.C₁, cap'.C₂} :=
    cap.cuffs_eq.symm.trans cap'.cuffs_eq
  have h1 : cap.C₁ ∈ ({cap'.C₁, cap'.C₂} : Set (Set S)) := hcuffs ▸ mem_insert _ _
  have h2 : cap.C₂ ∈ ({cap'.C₁, cap'.C₂} : Set (Set S)) := hcuffs ▸ mem_insert_of_mem _ rfl
  rw [cap.side₁_eq_sUnion_components hS hF, cap.side₂_eq_sUnion_components hS hF,
    cap'.side₁_eq_sUnion_components hS hF, cap'.side₂_eq_sUnion_components hS hF]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) cap.C₁_ne_C₂
  · rw [h1, mem_singleton_iff.mp h2]
  · rw [mem_singleton_iff.mp h1, h2, pair_comm]
  · exact absurd ((mem_singleton_iff.mp h1).trans (mem_singleton_iff.mp h2).symm) cap.C₁_ne_C₂

end CylinderSphereCap

/-! ## 2. Sides of a Hoop, Laminar Hoops, and $\Sigma(F_1, F_2)$ -/

/-- `(S₁, S₂)` is the unordered pair of *sides* of a hoop `F` in a cylinder `S`.
Graph Minors VIII, Section 15 (pages 279–280):
"If $F$ is a hoop then $\Sigma - F$ is naturally divided into two parts, which we call the *sides*
of $F$." -/
def IsHoopSidePair {S : Type w} [TopologicalSpace S] (F S₁ S₂ : Set S) : Prop :=
  ∃ (hS : IsCylinder S) (hF : IsHoop F) (cap : CylinderSphereCap S),
    (S₁ = cap.side₁ hS.1 hF ∧ S₂ = cap.side₂ hS.1 hF) ∨
    (S₁ = cap.side₂ hS.1 hF ∧ S₂ = cap.side₁ hS.1 hF)

section SidesAndLaminar

variable {S : Type w} [TopologicalSpace S]

theorem IsHoopSidePair.symm {F S₁ S₂ : Set S} (h : IsHoopSidePair F S₁ S₂) :
    IsHoopSidePair F S₂ S₁ := by
  obtain ⟨hS, hF, cap, h12 | h21⟩ := h
  · exact ⟨hS, hF, cap, Or.inr ⟨h12.2, h12.1⟩⟩
  · exact ⟨hS, hF, cap, Or.inl ⟨h21.2, h21.1⟩⟩

theorem CylinderSphereCap.isHoopSidePair (cap : CylinderSphereCap S) (hS : IsCylinder S)
    {F : Set S} (hF : IsHoop F) :
    IsHoopSidePair F (cap.side₁ hS.1 hF) (cap.side₂ hS.1 hF) :=
  ⟨hS, hF, cap, Or.inl ⟨rfl, rfl⟩⟩

theorem CylinderSphereCap.isHoopSidePair_iff (cap : CylinderSphereCap S) (hS : IsCylinder S)
    {F S₁ S₂ : Set S} (hF : IsHoop F) :
    IsHoopSidePair F S₁ S₂ ↔
      (S₁ = cap.side₁ hS.1 hF ∧ S₂ = cap.side₂ hS.1 hF) ∨
      (S₁ = cap.side₂ hS.1 hF ∧ S₂ = cap.side₁ hS.1 hF) := by
  constructor
  · rintro ⟨_, _, cap', hpair⟩
    have hset := cap'.sides_pair_eq_of_caps cap hS.1 hF
    have hswap : cap'.swap.side₁ hS.1 hF = cap'.side₂ hS.1 hF ∧
        cap'.swap.side₂ hS.1 hF = cap'.side₁ hS.1 hF := by
      obtain ⟨h1, h2, hb1, hb2, _, hcap, hD1, hD2⟩ := cap'.disc₁_disc₂_spec hS.1 hF
      obtain ⟨h1', h2', hb1', hb2', _, _, hD1', hD2'⟩ := cap'.swap.disc₁_disc₂_spec hS.1 hF
      have hu := cap'.swap.hoop_discs_unique h2 h1 hb2 hb1 (by rw [inter_comm, hcap]) hD2 hD1
        h1' h2' hb1' hb2' hD1' hD2'
      exact ⟨by simp [CylinderSphereCap.side₁, CylinderSphereCap.side₂, CylinderSphereCap.swap, hu.1],
        by simp [CylinderSphereCap.side₁, CylinderSphereCap.side₂, CylinderSphereCap.swap, hu.2]⟩
    have hcuffs : ({cap'.C₁, cap'.C₂} : Set (Set S)) = {cap.C₁, cap.C₂} :=
      cap'.cuffs_eq.symm.trans cap.cuffs_eq
    have hC₁ : cap'.C₁ ∈ ({cap.C₁, cap.C₂} : Set (Set S)) := hcuffs ▸ mem_insert _ _
    have hC₂ : cap'.C₂ ∈ ({cap.C₁, cap.C₂} : Set (Set S)) := hcuffs ▸ mem_insert_of_mem _ rfl
    have heq_or : (cap'.side₁ hS.1 hF = cap.side₁ hS.1 hF ∧ cap'.side₂ hS.1 hF = cap.side₂ hS.1 hF) ∨
        (cap'.side₁ hS.1 hF = cap.side₂ hS.1 hF ∧ cap'.side₂ hS.1 hF = cap.side₁ hS.1 hF) := by
      rw [cap'.side₁_eq_sUnion_components hS.1 hF, cap'.side₂_eq_sUnion_components hS.1 hF,
        cap.side₁_eq_sUnion_components hS.1 hF, cap.side₂_eq_sUnion_components hS.1 hF]
      rcases hC₁ with h1 | h1 <;> rcases hC₂ with h2 | h2
      · exact absurd (h1.trans h2.symm) cap'.C₁_ne_C₂
      · exact Or.inl ⟨by rw [h1], by rw [mem_singleton_iff.mp h2]⟩
      · exact Or.inr ⟨by rw [mem_singleton_iff.mp h1], by rw [h2]⟩
      · exact absurd ((mem_singleton_iff.mp h1).trans (mem_singleton_iff.mp h2).symm) cap'.C₁_ne_C₂
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases heq_or with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨e1, e2⟩
    · exact Or.inr ⟨e1, e2⟩
    · exact Or.inr ⟨e2, e1⟩
    · exact Or.inl ⟨e2, e1⟩
  · intro h
    exact ⟨hS, hF, cap, h⟩

theorem IsHoopSidePair.union_eq {F S₁ S₂ : Set S} (h : IsHoopSidePair F S₁ S₂) :
    S₁ ∪ S₂ = univ \ F := by
  obtain ⟨hS, hF, cap, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · exact cap.side₁_union_side₂ hS.1 hF
  · rw [union_comm]; exact cap.side₁_union_side₂ hS.1 hF

theorem IsHoopSidePair.disjoint {F S₁ S₂ : Set S} (h : IsHoopSidePair F S₁ S₂) :
    Disjoint S₁ S₂ := by
  obtain ⟨hS, hF, cap, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · exact cap.disjoint_side₁_side₂ hS.1 hF
  · exact (cap.disjoint_side₁_side₂ hS.1 hF).symm

/-- Two hoops $F_1, F_2$ in a cylinder $\Sigma$ are *laminar* if $F_2 \setminus F_1$ lies
completely in one side of $F_1$.
Graph Minors VIII, Section 15 (page 280):
"If $F_1$, $F_2$ are hoops and $F_2 - F_1$ lies completely in one side of $F_1$, it follows that
$F_1 - F_2$ lies completely in one side of $F_2$. In these circumstances we say that $F_1$, $F_2$
are *laminar*." -/
def AreLaminarHoops {S : Type w} [TopologicalSpace S] (F₁ F₂ : Set S) : Prop :=
  IsCylinder S ∧ IsHoop F₁ ∧ IsHoop F₂ ∧
    ∃ S₁ S₂ : Set S, IsHoopSidePair F₁ S₁ S₂ ∧ (F₂ \ F₁ ⊆ S₁ ∨ F₂ \ F₁ ⊆ S₂)

/-- Key disc-inclusion equivalence in `cap.Z`: `F₂ \ F₁ ⊆ cap.side₂ F₁` if and only if
`cap.disc₁ F₁ ⊆ cap.disc₁ F₂` (which simultaneously forces `cap.disc₂ F₂ ⊆ cap.disc₂ F₁`). -/
theorem CylinderSphereCap.subset_side₂_iff_disc₁_subset (cap : CylinderSphereCap S)
    (hS : IsSurface S) {F₁ F₂ : Set S} (hF₁ : IsHoop F₁) (hF₂ : IsHoop F₂) :
    F₂ \ F₁ ⊆ cap.side₂ hS hF₁ ↔ cap.disc₁ hS hF₁ ⊆ cap.disc₁ hS hF₂ := by
  have : T2Space cap.Z := cap.t2Space_Z
  obtain ⟨hE₁, hE₁', hbE₁, hbE₁', hcupE, hcapE, hD₁E, hD₂E⟩ := cap.disc₁_disc₂_spec hS hF₁
  obtain ⟨hG₁, hG₁', hbG₁, hbG₁', hcupG, hcapG, hD₁G, hD₂G⟩ := cap.disc₁_disc₂_spec hS hF₂
  constructor
  · intro hsub
    have hjF₂_sub : cap.j '' F₂ ⊆ cap.disc₂ hS hF₁ := by
      rintro _ ⟨x, hx₂, rfl⟩
      by_cases hx₁ : x ∈ F₁
      · exact Surface.discBd_subset _ (hbE₁' ▸ mem_image_of_mem _ hx₁)
      · exact (cap.side₂_eq_preimage_diff hS hF₁ ▸ hsub ⟨hx₂, hx₁⟩).1
    have hdis_bd : Disjoint (discBd (cap.disc₁ hS hF₂)) (discInt (cap.disc₁ hS hF₁)) := by
      rw [hbG₁]
      refine disjoint_left.mpr fun z hz₂ ⟨hz₁, hnz⟩ => ?_
      exact hnz (hbE₁ ▸ (hcapE ▸ ⟨hz₁, hjF₂_sub hz₂⟩))
    rcases cap.disc_subset_or_disjoint hG₁ hE₁ hdis_bd with h | h
    · exact h
    · exfalso
      obtain ⟨p, hp⟩ := cap.isClosedDisc_D₁.nonempty_discInt
      have hpr : p ∉ range cap.j :=
        fun hr => disjoint_left.mp cap.disjoint_range_discInt_D₁ hr hp
      have hpE : p ∈ discInt (cap.disc₁ hS hF₁) :=
        ⟨hD₁E hp.1, fun hb => hpr (hbE₁ ▸ hb |> image_subset_range _ _)⟩
      exact disjoint_left.mp h hpE (hD₁G hp.1)
  · intro hdisc x ⟨hx₂, hx₁⟩
    rw [cap.side₂_eq_preimage_diff hS hF₁]
    have hnf : cap.j x ∉ cap.j '' F₁ := by
      rintro ⟨y, hy, he⟩
      exact hx₁ (cap.inj he ▸ hy)
    refine ⟨?_, hnf⟩
    rcases (hcupE ▸ mem_univ (cap.j x) : cap.j x ∈ cap.disc₁ hS hF₁ ∪ cap.disc₂ hS hF₁) with h1 | h2
    · exfalso
      have hxIntE : cap.j x ∈ discInt (cap.disc₁ hS hF₁) := ⟨h1, hbE₁ ▸ hnf⟩
      have hxIntG : cap.j x ∈ discInt (cap.disc₁ hS hF₂) :=
        discInt_mono cap.isManifoldPoint_Z hE₁ hdisc hxIntE
      exact hxIntG.2 (hbG₁ ▸ mem_image_of_mem _ hx₂)
    · exact h2

theorem CylinderSphereCap.disc₂_subset_iff_disc₁_subset (cap : CylinderSphereCap S)
    (hS : IsSurface S) {F₁ F₂ : Set S} (hF₁ : IsHoop F₁) (hF₂ : IsHoop F₂) :
    cap.disc₂ hS hF₂ ⊆ cap.disc₂ hS hF₁ ↔ cap.disc₁ hS hF₁ ⊆ cap.disc₁ hS hF₂ := by
  have : T2Space cap.Z := cap.t2Space_Z
  obtain ⟨hE₁, hE₁', hbE₁, hbE₁', hcupE, hcapE, -, -⟩ := cap.disc₁_disc₂_spec hS hF₁
  obtain ⟨hG₁, hG₁', hbG₁, hbG₁', hcupG, hcapG, -, -⟩ := cap.disc₁_disc₂_spec hS hF₂
  constructor
  · intro hsub2
    have hsub_int : discInt (cap.disc₁ hS hF₁) ⊆ cap.disc₁ hS hF₂ := by
      intro z ⟨hz1, hnzb⟩
      rcases (hcupG ▸ mem_univ z : z ∈ cap.disc₁ hS hF₂ ∪ cap.disc₂ hS hF₂) with hg1 | hg2
      · exact hg1
      · exfalso
        have hz2 : z ∈ cap.disc₂ hS hF₁ := hsub2 hg2
        exact hnzb (hbE₁ ▸ (hcapE ▸ ⟨hz1, hz2⟩))
    exact hE₁.subset_closure_discInt.trans (closure_minimal hsub_int hG₁.isCompact.isClosed)
  · intro hsub1
    have hsub_int : discInt (cap.disc₂ hS hF₂) ⊆ cap.disc₂ hS hF₁ := by
      intro z ⟨hz2, hnzb⟩
      rcases (hcupE ▸ mem_univ z : z ∈ cap.disc₁ hS hF₁ ∪ cap.disc₂ hS hF₁) with he1 | he2
      · exfalso
        have hg1 : z ∈ cap.disc₁ hS hF₂ := hsub1 he1
        exact hnzb (hbG₁' ▸ (hcapG ▸ ⟨hg1, hz2⟩))
      · exact he2
    exact hG₁'.subset_closure_discInt.trans (closure_minimal hsub_int hE₁'.isCompact.isClosed)

theorem CylinderSphereCap.subset_side₁_iff_disc₁_superset (cap : CylinderSphereCap S)
    (hS : IsSurface S) {F₁ F₂ : Set S} (hF₁ : IsHoop F₁) (hF₂ : IsHoop F₂) :
    F₂ \ F₁ ⊆ cap.side₁ hS hF₁ ↔ cap.disc₁ hS hF₂ ⊆ cap.disc₁ hS hF₁ := by
  have hswap : ∀ {H : Set S} (hH : IsHoop H),
      cap.swap.disc₁ hS hH = cap.disc₂ hS hH ∧ cap.swap.side₂ hS hH = cap.side₁ hS hH := by
    intro H hH
    obtain ⟨h1, h2, hb1, hb2, _, hcap, hD1, hD2⟩ := cap.disc₁_disc₂_spec hS hH
    obtain ⟨h1', h2', hb1', hb2', _, _, hD1', hD2'⟩ := cap.swap.disc₁_disc₂_spec hS hH
    have hu := cap.swap.hoop_discs_unique h2 h1 hb2 hb1 (by rw [inter_comm, hcap]) hD2 hD1
      h1' h2' hb1' hb2' hD1' hD2'
    exact ⟨hu.1, by simp [CylinderSphereCap.side₂, CylinderSphereCap.side₁,
      CylinderSphereCap.swap, hu.2]⟩
  rw [← (hswap hF₁).2, cap.swap.subset_side₂_iff_disc₁_subset hS hF₁ hF₂,
    (hswap hF₁).1, (hswap hF₂).1, cap.disc₂_subset_iff_disc₁_subset hS hF₂ hF₁]

/-- `cap.disc₁` is injective on hoops of `S`. -/
theorem CylinderSphereCap.disc₁_inj (cap : CylinderSphereCap S) (hS : IsSurface S)
    {F₁ F₂ : Set S} (hF₁ : IsHoop F₁) (hF₂ : IsHoop F₂)
    (heq : cap.disc₁ hS hF₁ = cap.disc₁ hS hF₂) : F₁ = F₂ := by
  have hb₁ := (cap.disc₁_disc₂_spec hS hF₁).2.2.1
  have hb₂ := (cap.disc₁_disc₂_spec hS hF₂).2.2.1
  exact cap.inj.image_injective (hb₁.symm.trans (heq ▸ hb₂))

/-- No hoop is a proper subset of another hoop. -/
theorem IsHoop.eq_of_subset (hS : IsCylinder S) {F₁ F₂ : Set S} (hF₁ : IsHoop F₁)
    (hF₂ : IsHoop F₂) (hsub : F₂ ⊆ F₁) : F₁ = F₂ := by
  obtain ⟨cap⟩ := CylinderSphereCap.exists_of_isCylinder hS
  have hdiff : F₂ \ F₁ = ∅ := sdiff_eq_empty.mpr hsub
  have h1 : cap.disc₁ hS.1 hF₁ ⊆ cap.disc₁ hS.1 hF₂ :=
    (cap.subset_side₂_iff_disc₁_subset hS.1 hF₁ hF₂).mp (hdiff ▸ empty_subset _)
  have h2 : cap.disc₁ hS.1 hF₂ ⊆ cap.disc₁ hS.1 hF₁ :=
    (cap.subset_side₁_iff_disc₁_superset hS.1 hF₁ hF₂).mp (hdiff ▸ empty_subset _)
  exact cap.disc₁_inj hS.1 hF₁ hF₂ (Subset.antisymm h1 h2)

theorem CylinderSphereCap.areLaminarHoops_iff (cap : CylinderSphereCap S) (hS : IsCylinder S)
    {F₁ F₂ : Set S} (hF₁ : IsHoop F₁) (hF₂ : IsHoop F₂) :
    AreLaminarHoops F₁ F₂ ↔
      cap.disc₁ hS.1 hF₁ ⊆ cap.disc₁ hS.1 hF₂ ∨ cap.disc₁ hS.1 hF₂ ⊆ cap.disc₁ hS.1 hF₁ := by
  constructor
  · rintro ⟨_, _, _, S₁, S₂, hpair, hsub⟩
    rcases (cap.isHoopSidePair_iff hS hF₁).mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hsub with h | h
      · exact Or.inr ((cap.subset_side₁_iff_disc₁_superset hS.1 hF₁ hF₂).mp h)
      · exact Or.inl ((cap.subset_side₂_iff_disc₁_subset hS.1 hF₁ hF₂).mp h)
    · rcases hsub with h | h
      · exact Or.inl ((cap.subset_side₂_iff_disc₁_subset hS.1 hF₁ hF₂).mp h)
      · exact Or.inr ((cap.subset_side₁_iff_disc₁_superset hS.1 hF₁ hF₂).mp h)
  · intro hor
    refine ⟨hS, hF₁, hF₂, cap.side₁ hS.1 hF₁, cap.side₂ hS.1 hF₁,
      cap.isHoopSidePair hS hF₁, ?_⟩
    rcases hor with h | h
    · exact Or.inr ((cap.subset_side₂_iff_disc₁_subset hS.1 hF₁ hF₂).mpr h)
    · exact Or.inl ((cap.subset_side₁_iff_disc₁_superset hS.1 hF₁ hF₂).mpr h)

theorem AreLaminarHoops.refl (hS : IsCylinder S) {F : Set S} (hF : IsHoop F) :
    AreLaminarHoops F F := by
  obtain ⟨cap⟩ := CylinderSphereCap.exists_of_isCylinder hS
  exact (cap.areLaminarHoops_iff hS hF hF).mpr (Or.inl Subset.rfl)

/-- Graph Minors VIII, Section 15 (page 280):
"If $F_1$, $F_2$ are hoops and $F_2 - F_1$ lies completely in one side of $F_1$, it follows that
$F_1 - F_2$ lies completely in one side of $F_2$." -/
theorem AreLaminarHoops.symm {F₁ F₂ : Set S} (h : AreLaminarHoops F₁ F₂) :
    AreLaminarHoops F₂ F₁ := by
  obtain ⟨hS, hF₁, hF₂, -⟩ := id h
  obtain ⟨cap⟩ := CylinderSphereCap.exists_of_isCylinder hS
  exact (cap.areLaminarHoops_iff hS hF₂ hF₁).mpr
    ((cap.areLaminarHoops_iff hS hF₁ hF₂).mp h).symm

/-- For distinct laminar hoops $F_1, F_2$ in a cylinder $\Sigma$, $\Sigma(F_1, F_2)$ is the
complement of the side of $F_1$ not containing $F_2 \setminus F_1$ and the side of $F_2$ not
containing $F_1 \setminus F_2$; for $F_1 = F_2$, $\Sigma(F_1, F_1) = F_1$.
Graph Minors VIII, Section 15 (page 280):
"If $F_1$, $F_2$ are distinct laminar hoops, then $\Sigma$ is divided naturally into three
parts—the side of $F_1$ not containing $F_2 - F_1$, the side of $F_2$ not containing $F_1 - F_2$,
and the remainder, which we denote by $\Sigma(F_1, F_2)$." -/
noncomputable def cylinderBetween {S : Type w} [TopologicalSpace S] (F₁ F₂ : Set S) : Set S :=
  by
    classical
    exact if F₁ = F₂ then F₁ else
      (univ \ ⋃ (A₁ : Set S) (_ : ∃ B₁, IsHoopSidePair F₁ A₁ B₁ ∧ F₂ \ F₁ ⊆ B₁), A₁) \
        ⋃ (A₂ : Set S) (_ : ∃ B₂, IsHoopSidePair F₂ A₂ B₂ ∧ F₁ \ F₂ ⊆ B₂), A₂

theorem cylinderBetween_self (F : Set S) : cylinderBetween F F = F := by
  simp [cylinderBetween]

theorem cylinderBetween_comm (F₁ F₂ : Set S) :
    cylinderBetween F₁ F₂ = cylinderBetween F₂ F₁ := by
  classical
  by_cases h : F₁ = F₂
  · subst h; rfl
  · have h' : F₂ ≠ F₁ := Ne.symm h
    simp only [cylinderBetween, h, h', ↓reduceIte]
    ext x
    simp only [mem_sdiff, mem_univ, true_and]
    tauto

/-- Uniform capped-sphere formula for $\Sigma(F_1, F_2)$ when `cap.disc₁ F₁ ⊆ cap.disc₁ F₂`
(valid for both $F_1 \ne F_2$ and $F_1 = F_2$). -/
theorem CylinderSphereCap.cylinderBetween_eq_of_disc₁_subset (cap : CylinderSphereCap S)
    (hS : IsCylinder S) {F₁ F₂ : Set S} (hF₁ : IsHoop F₁) (hF₂ : IsHoop F₂)
    (hle : cap.disc₁ hS.1 hF₁ ⊆ cap.disc₁ hS.1 hF₂) :
    cylinderBetween F₁ F₂ = cap.j ⁻¹' (cap.disc₁ hS.1 hF₂ ∩ cap.disc₂ hS.1 hF₁) := by
  classical
  obtain ⟨-, -, hbE₁, hbE₁', hcupE, hcapE, -, -⟩ := cap.disc₁_disc₂_spec hS.1 hF₁
  obtain ⟨-, -, hbG₁, hbG₁', hcupG, hcapG, -, -⟩ := cap.disc₁_disc₂_spec hS.1 hF₂
  by_cases heq : F₁ = F₂
  · subst heq
    rw [cylinderBetween_self, hcapE, preimage_image_eq _ cap.inj]
  · simp only [cylinderBetween, heq, ↓reduceIte]
    have hnot21 : ¬ (cap.disc₁ hS.1 hF₂ ⊆ cap.disc₁ hS.1 hF₁) :=
      fun hge => heq (cap.disc₁_inj hS.1 hF₁ hF₂ (Subset.antisymm hle hge))
    have hsub12 : F₂ \ F₁ ⊆ cap.side₂ hS.1 hF₁ :=
      (cap.subset_side₂_iff_disc₁_subset hS.1 hF₁ hF₂).mpr hle
    have hnsub11 : ¬ (F₂ \ F₁ ⊆ cap.side₁ hS.1 hF₁) :=
      fun h => hnot21 ((cap.subset_side₁_iff_disc₁_superset hS.1 hF₁ hF₂).mp h)
    have hsub21 : F₁ \ F₂ ⊆ cap.side₁ hS.1 hF₂ :=
      (cap.subset_side₁_iff_disc₁_superset hS.1 hF₂ hF₁).mpr hle
    have hnsub22 : ¬ (F₁ \ F₂ ⊆ cap.side₂ hS.1 hF₂) :=
      fun h => hnot21 ((cap.subset_side₂_iff_disc₁_subset hS.1 hF₂ hF₁).mp h)
    have hU₁ : (⋃ (A₁ : Set S) (_ : ∃ B₁, IsHoopSidePair F₁ A₁ B₁ ∧ F₂ \ F₁ ⊆ B₁), A₁) =
        cap.side₁ hS.1 hF₁ := by
      apply Subset.antisymm
      · refine iUnion₂_subset fun A₁ ⟨B₁, hp, hs⟩ => ?_
        rcases (cap.isHoopSidePair_iff hS hF₁).mp hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Subset.rfl
        · exact absurd hs hnsub11
      · exact subset_iUnion₂_of_subset (cap.side₁ hS.1 hF₁)
          ⟨cap.side₂ hS.1 hF₁, cap.isHoopSidePair hS hF₁, hsub12⟩ Subset.rfl
    have hU₂ : (⋃ (A₂ : Set S) (_ : ∃ B₂, IsHoopSidePair F₂ A₂ B₂ ∧ F₁ \ F₂ ⊆ B₂), A₂) =
        cap.side₂ hS.1 hF₂ := by
      apply Subset.antisymm
      · refine iUnion₂_subset fun A₂ ⟨B₂, hp, hs⟩ => ?_
        rcases (cap.isHoopSidePair_iff hS hF₂).mp hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd hs hnsub22
        · exact Subset.rfl
      · exact subset_iUnion₂_of_subset (cap.side₂ hS.1 hF₂)
          ⟨cap.side₁ hS.1 hF₂, (cap.isHoopSidePair hS hF₂).symm, hsub21⟩ Subset.rfl
    rw [hU₁, hU₂]
    ext x
    simp only [mem_sdiff, mem_univ, true_and, mem_preimage,
      CylinderSphereCap.side₁, CylinderSphereCap.side₂, discInt, hbE₁, hbG₁']
    constructor
    · rintro ⟨hn1, hn2⟩
      refine ⟨?_, ?_⟩
      · rcases (hcupG ▸ mem_univ (cap.j x) : cap.j x ∈ cap.disc₁ hS.1 hF₂ ∪ cap.disc₂ hS.1 hF₂)
          with hg1 | hg2
        · exact hg1
        · by_cases hxf2 : cap.j x ∈ cap.j '' F₂
          · exact (hcapG ▸ hxf2).1
          · exact absurd ⟨hg2, hxf2⟩ hn2
      · rcases (hcupE ▸ mem_univ (cap.j x) : cap.j x ∈ cap.disc₁ hS.1 hF₁ ∪ cap.disc₂ hS.1 hF₁)
          with he1 | he2
        · by_cases hxf1 : cap.j x ∈ cap.j '' F₁
          · exact (hcapE ▸ hxf1).2
          · exact absurd ⟨he1, hxf1⟩ hn1
        · exact he2
    · rintro ⟨hg1, he2⟩
      refine ⟨fun ⟨he1, hnf1⟩ => hnf1 (hcapE ▸ ⟨he1, he2⟩),
        fun ⟨hg2, hnf2⟩ => hnf2 (hcapG ▸ ⟨hg1, hg2⟩)⟩

theorem subset_cylinderBetween_left {F₁ F₂ : Set S} (h : AreLaminarHoops F₁ F₂) :
    F₁ ⊆ cylinderBetween F₁ F₂ := by
  obtain ⟨hS, hF₁, hF₂, -⟩ := id h
  obtain ⟨cap⟩ := CylinderSphereCap.exists_of_isCylinder hS
  obtain ⟨-, -, hbE₁, hbE₁', -, -, -, -⟩ := cap.disc₁_disc₂_spec hS.1 hF₁
  rcases (cap.areLaminarHoops_iff hS hF₁ hF₂).mp h with hle | hge
  · rw [cap.cylinderBetween_eq_of_disc₁_subset hS hF₁ hF₂ hle]
    intro x hx
    exact ⟨hle (Surface.discBd_subset _ (hbE₁ ▸ mem_image_of_mem _ hx)),
      Surface.discBd_subset _ (hbE₁' ▸ mem_image_of_mem _ hx)⟩
  · rw [cylinderBetween_comm, cap.cylinderBetween_eq_of_disc₁_subset hS hF₂ hF₁ hge]
    have hle2 := (cap.disc₂_subset_iff_disc₁_subset hS.1 hF₂ hF₁).mpr hge
    intro x hx
    exact ⟨Surface.discBd_subset _ (hbE₁ ▸ mem_image_of_mem _ hx),
      hle2 (Surface.discBd_subset _ (hbE₁' ▸ mem_image_of_mem _ hx))⟩

theorem subset_cylinderBetween_right {F₁ F₂ : Set S} (h : AreLaminarHoops F₁ F₂) :
    F₂ ⊆ cylinderBetween F₁ F₂ :=
  cylinderBetween_comm F₁ F₂ ▸ subset_cylinderBetween_left h.symm

theorem isClosed_cylinderBetween {F₁ F₂ : Set S} (h : AreLaminarHoops F₁ F₂) :
    IsClosed (cylinderBetween F₁ F₂) := by
  obtain ⟨hS, hF₁, hF₂, -⟩ := id h
  obtain ⟨cap⟩ := CylinderSphereCap.exists_of_isCylinder hS
  have : T2Space cap.Z := cap.t2Space_Z
  rcases (cap.areLaminarHoops_iff hS hF₁ hF₂).mp h with hle | hge
  · rw [cap.cylinderBetween_eq_of_disc₁_subset hS hF₁ hF₂ hle]
    exact (((cap.disc₁_disc₂_spec hS.1 hF₂).1.isCompact.isClosed).inter
      ((cap.disc₁_disc₂_spec hS.1 hF₁).2.1.isCompact.isClosed)).preimage
      cap.isClosedEmbedding.continuous
  · rw [cylinderBetween_comm, cap.cylinderBetween_eq_of_disc₁_subset hS hF₂ hF₁ hge]
    exact (((cap.disc₁_disc₂_spec hS.1 hF₁).1.isCompact.isClosed).inter
      ((cap.disc₁_disc₂_spec hS.1 hF₂).2.1.isCompact.isClosed)).preimage
      cap.isClosedEmbedding.continuous

/-- A hoop `H` lies in `Σ(F₁, F₂)` (when `cap.disc₁ F₁ ⊆ cap.disc₁ F₂`) if and only if
`cap.disc₁ F₁ ⊆ cap.disc₁ H ⊆ cap.disc₁ F₂`. -/
theorem CylinderSphereCap.hoop_subset_cylinderBetween_iff (cap : CylinderSphereCap S)
    (hS : IsCylinder S) {F₁ F₂ H : Set S} (hF₁ : IsHoop F₁) (hF₂ : IsHoop F₂) (hH : IsHoop H)
    (hle : cap.disc₁ hS.1 hF₁ ⊆ cap.disc₁ hS.1 hF₂) :
    H ⊆ cylinderBetween F₁ F₂ ↔
      cap.disc₁ hS.1 hF₁ ⊆ cap.disc₁ hS.1 hH ∧ cap.disc₁ hS.1 hH ⊆ cap.disc₁ hS.1 hF₂ := by
  rw [cap.cylinderBetween_eq_of_disc₁_subset hS hF₁ hF₂ hle]
  rw [← cap.subset_side₂_iff_disc₁_subset hS.1 hF₁ hH,
    ← cap.subset_side₁_iff_disc₁_superset hS.1 hF₂ hH]
  rw [cap.side₂_eq_preimage_diff hS.1 hF₁, cap.side₁_eq_preimage_diff hS.1 hF₂]
  constructor
  · intro hsub
    refine ⟨fun x ⟨hxH, hx1⟩ => ⟨(hsub hxH).2, fun ⟨y, hy, he⟩ => hx1 (cap.inj he ▸ hy)⟩,
      fun x ⟨hxH, hx2⟩ => ⟨(hsub hxH).1, fun ⟨y, hy, he⟩ => hx2 (cap.inj he ▸ hy)⟩⟩
  · rintro ⟨h1, h2⟩ x hxH
    obtain ⟨-, -, -, hbE₁', -, -, -, -⟩ := cap.disc₁_disc₂_spec hS.1 hF₁
    obtain ⟨-, -, hbG₁, -, -, -, -, -⟩ := cap.disc₁_disc₂_spec hS.1 hF₂
    refine ⟨?_, ?_⟩
    · by_cases hx2 : x ∈ F₂
      · exact Surface.discBd_subset _ (hbG₁ ▸ mem_image_of_mem _ hx2)
      · exact (h2 ⟨hxH, hx2⟩).1
    · by_cases hx1 : x ∈ F₁
      · exact Surface.discBd_subset _ (hbE₁' ▸ mem_image_of_mem _ hx1)
      · exact (h1 ⟨hxH, hx1⟩).1

theorem areLaminarHoops_of_subset_cylinderBetween {F₁ F₂ H : Set S}
    (h12 : AreLaminarHoops F₁ F₂) (hH : IsHoop H) (hsub : H ⊆ cylinderBetween F₁ F₂) :
    AreLaminarHoops F₁ H ∧ AreLaminarHoops H F₂ := by
  obtain ⟨hS, hF₁, hF₂, -⟩ := id h12
  obtain ⟨cap⟩ := CylinderSphereCap.exists_of_isCylinder hS
  rcases (cap.areLaminarHoops_iff hS hF₁ hF₂).mp h12 with hle | hge
  · obtain ⟨h1, h2⟩ := (cap.hoop_subset_cylinderBetween_iff hS hF₁ hF₂ hH hle).mp hsub
    exact ⟨(cap.areLaminarHoops_iff hS hF₁ hH).mpr (Or.inl h1),
      (cap.areLaminarHoops_iff hS hH hF₂).mpr (Or.inl h2)⟩
  · rw [cylinderBetween_comm] at hsub
    obtain ⟨h1, h2⟩ := (cap.hoop_subset_cylinderBetween_iff hS hF₂ hF₁ hH hge).mp hsub
    exact ⟨(cap.areLaminarHoops_iff hS hF₁ hH).mpr (Or.inr h2),
      (cap.areLaminarHoops_iff hS hH hF₂).mpr (Or.inr h1)⟩

theorem CylinderSphereCap.cylinderBetween_union (cap : CylinderSphereCap S) (hS : IsCylinder S)
    {F₁ H F₂ : Set S} (hF₁ : IsHoop F₁) (hH : IsHoop H) (hF₂ : IsHoop F₂)
    (hle1 : cap.disc₁ hS.1 hF₁ ⊆ cap.disc₁ hS.1 hH)
    (hle2 : cap.disc₁ hS.1 hH ⊆ cap.disc₁ hS.1 hF₂) :
    cylinderBetween F₁ H ∪ cylinderBetween H F₂ = cylinderBetween F₁ F₂ := by
  rw [cap.cylinderBetween_eq_of_disc₁_subset hS hF₁ hH hle1,
    cap.cylinderBetween_eq_of_disc₁_subset hS hH hF₂ hle2,
    cap.cylinderBetween_eq_of_disc₁_subset hS hF₁ hF₂ (hle1.trans hle2), ← preimage_union]
  have hle1' := (cap.disc₂_subset_iff_disc₁_subset hS.1 hF₁ hH).mpr hle1
  have hle2' := (cap.disc₂_subset_iff_disc₁_subset hS.1 hH hF₂).mpr hle2
  have hcupH := (cap.disc₁_disc₂_spec hS.1 hH).2.2.2.2.1
  ext x
  simp only [mem_preimage, mem_union]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨hle2 h1, h2⟩
    · exact ⟨h1, hle1' h2⟩
  · rintro ⟨h1, h2⟩
    rcases (hcupH ▸ mem_univ (cap.j x) : cap.j x ∈ cap.disc₁ hS.1 hH ∪ cap.disc₂ hS.1 hH)
      with hh1 | hh2
    · exact Or.inl ⟨hh1, h2⟩
    · exact Or.inr ⟨h1, hh2⟩

theorem CylinderSphereCap.cylinderBetween_inter (cap : CylinderSphereCap S) (hS : IsCylinder S)
    {F₁ H F₂ : Set S} (hF₁ : IsHoop F₁) (hH : IsHoop H) (hF₂ : IsHoop F₂)
    (hle1 : cap.disc₁ hS.1 hF₁ ⊆ cap.disc₁ hS.1 hH)
    (hle2 : cap.disc₁ hS.1 hH ⊆ cap.disc₁ hS.1 hF₂) :
    cylinderBetween F₁ H ∩ cylinderBetween H F₂ = H := by
  rw [cap.cylinderBetween_eq_of_disc₁_subset hS hF₁ hH hle1,
    cap.cylinderBetween_eq_of_disc₁_subset hS hH hF₂ hle2, ← preimage_inter]
  have hle1' := (cap.disc₂_subset_iff_disc₁_subset hS.1 hF₁ hH).mpr hle1
  have hcapH := (cap.disc₁_disc₂_spec hS.1 hH).2.2.2.2.2.1
  have heq : (cap.disc₁ hS.1 hH ∩ cap.disc₂ hS.1 hF₁) ∩ (cap.disc₁ hS.1 hF₂ ∩ cap.disc₂ hS.1 hH) =
      cap.j '' H := by
    rw [← hcapH]
    ext z
    exact ⟨fun ⟨⟨h1, _⟩, ⟨_, h2⟩⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, hle1' h2⟩, ⟨hle2 h1, h2⟩⟩⟩
  rw [heq, preimage_image_eq _ cap.inj]

theorem CylinderSphereCap.cylinderBetween_mono (cap : CylinderSphereCap S) (hS : IsCylinder S)
    {F₁ F₁' F₂' F₂ : Set S} (hF₁ : IsHoop F₁) (hF₁' : IsHoop F₁')
    (hF₂' : IsHoop F₂') (hF₂ : IsHoop F₂)
    (h1 : cap.disc₁ hS.1 hF₁ ⊆ cap.disc₁ hS.1 hF₁')
    (h12 : cap.disc₁ hS.1 hF₁' ⊆ cap.disc₁ hS.1 hF₂')
    (h2 : cap.disc₁ hS.1 hF₂' ⊆ cap.disc₁ hS.1 hF₂) :
    cylinderBetween F₁' F₂' ⊆ cylinderBetween F₁ F₂ := by
  rw [cap.cylinderBetween_eq_of_disc₁_subset hS hF₁' hF₂' h12,
    cap.cylinderBetween_eq_of_disc₁_subset hS hF₁ hF₂ (h1.trans (h12.trans h2))]
  have h1' := (cap.disc₂_subset_iff_disc₁_subset hS.1 hF₁ hF₁').mpr h1
  exact preimage_mono (inter_subset_inter h2 h1')

theorem cylinderBetween_subset_cylinderBetween {F₁ F₂ F₁' F₂' : Set S}
    (h12 : AreLaminarHoops F₁ F₂) (h12' : AreLaminarHoops F₁' F₂')
    (hsub1 : F₁' ⊆ cylinderBetween F₁ F₂) (hsub2 : F₂' ⊆ cylinderBetween F₁ F₂) :
    cylinderBetween F₁' F₂' ⊆ cylinderBetween F₁ F₂ := by
  obtain ⟨hS, hF₁, hF₂, -⟩ := id h12
  obtain ⟨_, hF₁', hF₂', -⟩ := id h12'
  obtain ⟨cap⟩ := CylinderSphereCap.exists_of_isCylinder hS
  wlog hle12 : cap.disc₁ hS.1 hF₁ ⊆ cap.disc₁ hS.1 hF₂ generalizing F₁ F₂
  · rw [cylinderBetween_comm F₁ F₂] at hsub1 hsub2 ⊢
    exact this h12.symm hsub1 hsub2 hF₂ hF₁
      (((cap.areLaminarHoops_iff hS hF₁ hF₂).mp h12).resolve_left hle12)
  obtain ⟨ha1, ha2⟩ := (cap.hoop_subset_cylinderBetween_iff hS hF₁ hF₂ hF₁' hle12).mp hsub1
  obtain ⟨hb1, hb2⟩ := (cap.hoop_subset_cylinderBetween_iff hS hF₁ hF₂ hF₂' hle12).mp hsub2
  rcases (cap.areLaminarHoops_iff hS hF₁' hF₂').mp h12' with hle' | hge'
  · exact cap.cylinderBetween_mono hS hF₁ hF₁' hF₂' hF₂ ha1 hle' hb2
  · rw [cylinderBetween_comm F₁' F₂']
    exact cap.cylinderBetween_mono hS hF₁ hF₂' hF₁' hF₂ hb1 hge' ha2

/-- For the two cuffs `C₁, C₂` of a cylinder `S`, `Σ(C₁, C₂) = univ`. -/
theorem CylinderSphereCap.cylinderBetween_cuffs (cap : CylinderSphereCap S) (hS : IsCylinder S) :
    cylinderBetween cap.C₁ cap.C₂ = univ := by
  have hC₁ := cap.isHoop_C₁ hS.1
  have hC₂ := cap.isHoop_C₂ hS.1
  obtain ⟨hE₁, hE₁', hbE₁, hbE₁', hcupE, hcapE, hD₁E, hD₂E⟩ := cap.disc₁_disc₂_spec hS.1 hC₁
  obtain ⟨hG₁, hG₁', hbG₁, hbG₁', hcupG, hcapG, hD₁G, hD₂G⟩ := cap.disc₁_disc₂_spec hS.1 hC₂
  have hE₁_eq : cap.disc₁ hS.1 hC₁ = cap.D₁ := by
    obtain ⟨Δ₁, Δ₂, -, d1, d2, b1, b2, cup, meet, -, huniq⟩ :=
      sphere_disc cap.Z cap.isSphere (cap.j '' cap.C₁) (cap.isOArc_image hC₁.1)
    rcases huniq cap.D₁ cap.isClosedDisc_D₁ cap.discBd_D₁ with rfl | rfl
    · exact (cap.hoop_discs_unique cap.isClosedDisc_D₁ d2 cap.discBd_D₁ b2 meet Subset.rfl
        (fun z hz => (cup ▸ mem_univ z).resolve_left (disjoint_right.mp cap.disjoint_D hz))
        hE₁ hE₁' hbE₁ hbE₁' hD₁E hD₂E).1
    · exact (cap.hoop_discs_unique cap.isClosedDisc_D₁ d1 cap.discBd_D₁ b1
        (by rw [inter_comm, meet]) Subset.rfl
        (fun z hz => (cup ▸ mem_univ z).resolve_right (disjoint_right.mp cap.disjoint_D hz))
        hE₁ hE₁' hbE₁ hbE₁' hD₁E hD₂E).1
  have hG₁'_eq : cap.disc₂ hS.1 hC₂ = cap.D₂ := by
    obtain ⟨Δ₁, Δ₂, -, d1, d2, b1, b2, cup, meet, -, huniq⟩ :=
      sphere_disc cap.Z cap.isSphere (cap.j '' cap.C₂) (cap.isOArc_image hC₂.1)
    rcases huniq cap.D₂ cap.isClosedDisc_D₂ cap.discBd_D₂ with rfl | rfl
    · exact (cap.hoop_discs_unique d2 cap.isClosedDisc_D₂ b2 cap.discBd_D₂
        (by rw [inter_comm, meet])
        (fun z hz => (cup ▸ mem_univ z).resolve_left (disjoint_left.mp cap.disjoint_D hz))
        Subset.rfl hG₁ hG₁' hbG₁ hbG₁' hD₁G hD₂G).2
    · exact (cap.hoop_discs_unique d1 cap.isClosedDisc_D₂ b1 cap.discBd_D₂ meet
        (fun z hz => (cup ▸ mem_univ z).resolve_right (disjoint_left.mp cap.disjoint_D hz))
        Subset.rfl hG₁ hG₁' hbG₁ hbG₁' hD₁G hD₂G).2
  have hle : cap.disc₁ hS.1 hC₁ ⊆ cap.disc₁ hS.1 hC₂ := hE₁_eq ▸ hD₁G
  rw [cap.cylinderBetween_eq_of_disc₁_subset hS hC₁ hC₂ hle]
  refine eq_univ_of_forall fun x => ⟨?_, ?_⟩
  · rcases (hcupG ▸ mem_univ (cap.j x) : cap.j x ∈ cap.disc₁ hS.1 hC₂ ∪ cap.disc₂ hS.1 hC₂)
      with h1 | h2
    · exact h1
    · rw [hG₁'_eq] at h2
      exact Surface.discBd_subset _ (hbG₁ ▸ mem_image_of_mem _ (cap.mem_C₂_of_j_mem_D₂ h2))
  · rcases (hcupE ▸ mem_univ (cap.j x) : cap.j x ∈ cap.disc₁ hS.1 hC₁ ∪ cap.disc₂ hS.1 hC₁)
      with h1 | h2
    · rw [hE₁_eq] at h1
      exact Surface.discBd_subset _ (hbE₁' ▸ mem_image_of_mem _ (cap.mem_C₁_of_j_mem_D₁ h1))
    · exact h2

private theorem isHoopSidePair_image_homeomorph_imp {A : Type w} {B : Type w'}
    [TopologicalSpace A] [TopologicalSpace B] (f : A ≃ₜ B) {X U₁ U₂ : Set A} :
    IsHoopSidePair X U₁ U₂ → IsHoopSidePair (f '' X) (f '' U₁) (f '' U₂) := by
  rintro ⟨hA, hX, _, hpair⟩
  have hB := hA.congr f
  have hXf : IsHoop (f '' X) := (IsHoop.image_homeomorph f).mpr hX
  obtain ⟨capB⟩ := CylinderSphereCap.exists_of_isCylinder hB
  let capA := capB.comapHomeomorph f
  have hj : capA.j '' X = capB.j '' (f '' X) := by
    change (capB.j ∘ f) '' X = capB.j '' (f '' X)
    rw [image_comp]
  obtain ⟨h1A, h2A, hb1A, hb2A, _, hcapA, hD1A, hD2A⟩ := capA.disc₁_disc₂_spec hA.1 hX
  obtain ⟨h1B, h2B, hb1B, hb2B, _, _, hD1B, hD2B⟩ := capB.disc₁_disc₂_spec hB.1 hXf
  have hu := capB.hoop_discs_unique h1A h2A (hj ▸ hb1A) (hj ▸ hb2A) (hj ▸ hcapA) hD1A hD2A
    h1B h2B hb1B hb2B hD1B hD2B
  have hEG₁ : @discInt capB.Z capB.tsZ (capB.disc₁ hB.1 hXf) =
      @discInt capB.Z capB.tsZ (capA.disc₁ hA.1 hX) :=
    congrArg (@discInt capB.Z capB.tsZ) hu.1
  have hEG₂ : @discInt capB.Z capB.tsZ (capB.disc₂ hB.1 hXf) =
      @discInt capB.Z capB.tsZ (capA.disc₂ hA.1 hX) :=
    congrArg (@discInt capB.Z capB.tsZ) hu.2
  have hs1 : f '' capA.side₁ hA.1 hX = capB.side₁ hB.1 hXf := by
    change f '' (f ⁻¹' (capB.j ⁻¹' @discInt capB.Z capB.tsZ (capA.disc₁ hA.1 hX))) =
      capB.j ⁻¹' @discInt capB.Z capB.tsZ (capB.disc₁ hB.1 hXf)
    rw [f.surjective.image_preimage, hEG₁]
  have hs2 : f '' capA.side₂ hA.1 hX = capB.side₂ hB.1 hXf := by
    change f '' (f ⁻¹' (capB.j ⁻¹' @discInt capB.Z capB.tsZ (capA.disc₂ hA.1 hX))) =
      capB.j ⁻¹' @discInt capB.Z capB.tsZ (capB.disc₂ hB.1 hXf)
    rw [f.surjective.image_preimage, hEG₂]
  rcases (capA.isHoopSidePair_iff hA hX).mp ⟨hA, hX, _, hpair⟩ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hB, hXf, capB, Or.inl ⟨hs1, hs2⟩⟩
  · exact ⟨hB, hXf, capB, Or.inr ⟨hs2, hs1⟩⟩

/-- Transporting `IsHoopSidePair`, `AreLaminarHoops`, and `cylinderBetween` across a
homeomorphism `e : S ≃ₜ S'`. -/
theorem IsHoopSidePair.image_homeomorph {S' : Type w'} [TopologicalSpace S'] (e : S ≃ₜ S')
    {F S₁ S₂ : Set S} :
    IsHoopSidePair (e '' F) (e '' S₁) (e '' S₂) ↔ IsHoopSidePair F S₁ S₂ := by
  refine ⟨fun h => ?_, isHoopSidePair_image_homeomorph_imp e⟩
  simpa [image_image] using isHoopSidePair_image_homeomorph_imp e.symm h

private theorem areLaminarHoops_image_homeomorph_imp {A : Type w} {B : Type w'}
    [TopologicalSpace A] [TopologicalSpace B] (f : A ≃ₜ B) {X₁ X₂ : Set A} :
    AreLaminarHoops X₁ X₂ → AreLaminarHoops (f '' X₁) (f '' X₂) := by
  rintro ⟨hA, hX₁, hX₂, U₁, U₂, hp, hsub⟩
  refine ⟨hA.congr f, (IsHoop.image_homeomorph f).mpr hX₁, (IsHoop.image_homeomorph f).mpr hX₂,
    f '' U₁, f '' U₂, (IsHoopSidePair.image_homeomorph f).mpr hp, ?_⟩
  rw [← image_sdiff f.injective]
  exact hsub.imp image_mono image_mono

theorem AreLaminarHoops.image_homeomorph {S' : Type w'} [TopologicalSpace S'] (e : S ≃ₜ S')
    {F₁ F₂ : Set S} :
    AreLaminarHoops (e '' F₁) (e '' F₂) ↔ AreLaminarHoops F₁ F₂ := by
  refine ⟨fun h => ?_, areLaminarHoops_image_homeomorph_imp e⟩
  simpa [image_image] using areLaminarHoops_image_homeomorph_imp e.symm h

theorem image_cylinderBetween_homeomorph {S' : Type w'} [TopologicalSpace S'] (e : S ≃ₜ S')
    (F₁ F₂ : Set S) :
    e '' cylinderBetween F₁ F₂ = cylinderBetween (e '' F₁) (e '' F₂) := by
  classical
  by_cases h : F₁ = F₂
  · subst h; simp [cylinderBetween_self]
  · have he : e '' F₁ ≠ e '' F₂ := fun heq => h (e.injective.image_injective heq)
    simp only [cylinderBetween, h, he, ↓reduceIte]
    have hU : ∀ (X Y : Set S),
        e '' (⋃ (A : Set S) (_ : ∃ B, IsHoopSidePair X A B ∧ Y \ X ⊆ B), A) =
          ⋃ (A' : Set S') (_ : ∃ B', IsHoopSidePair (e '' X) A' B' ∧ e '' Y \ e '' X ⊆ B'), A' := by
      intro X Y
      ext z
      simp only [mem_image, mem_iUnion, exists_prop]
      constructor
      · rintro ⟨x, ⟨A, ⟨B, hp, hs⟩, hxA⟩, rfl⟩
        refine ⟨e '' A, ⟨e '' B, (IsHoopSidePair.image_homeomorph e).mpr hp, ?_⟩, x, hxA, rfl⟩
        rw [← image_sdiff e.injective]
        exact image_mono hs
      · rintro ⟨A', ⟨B', hp', hs'⟩, hzA'⟩
        refine ⟨e.symm z, ⟨e.symm '' A', ⟨e.symm '' B', ?_, ?_⟩, ⟨z, hzA', rfl⟩⟩,
          e.apply_symm_apply z⟩
        · have := (IsHoopSidePair.image_homeomorph e.symm).mpr hp'
          simpa [image_image] using this
        · have hs'' := image_mono (f := e.symm) hs'
          rw [← image_sdiff e.injective] at hs''
          simpa [image_image] using hs''
    rw [image_sdiff e.injective, image_sdiff e.injective, image_univ, e.surjective.range_eq,
      hU F₁ F₂, hU F₂ F₁]

end SidesAndLaminar

end GraphMinor.GM08
