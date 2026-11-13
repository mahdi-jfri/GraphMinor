module

public import GraphMinor.GM21.Defs
public import GraphMinor.GM11.Defs
public import GraphMinor.GM12.Section3SubspaceDrawing
import GraphMinor.GM12.Section3SubspaceArcs
import GraphMinor.GM12.Section3SubtypeComponents
import GraphMinor.Surface.PasteModel
import GraphMinor.Surface.Gluing
import GraphMinor.Surface.Cuffs
import GraphMinor.GM11.OArcCircuit
import GraphMinor.GM11.Ties
import GraphMinor.Surface.SurfaceGraph
import GraphMinor.Surface.SideCut
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.InvarianceOfDomain
import GraphMinor.GM07.GoodEdge
import GraphMinor.GM11.GlueDiscs

/-!
# Graph Minors XXI, Section 6: one side of a line through a region

Several proofs of Section 6 of *Graph Minors XXI* (the proofs of (6.5), (6.6), (6.7), and claim (4)
of the proof of (6.3), pages 25–29 of the preprint) take a proper line `F` in the surface `Σ` whose
ends `a, b` are vertices of the drawing `Γ` and whose other points miss `U(Γ)`, and look at one side
`Σ₁` of it: a surface `Σ₁ ⊆ Σ` with a second surface `Σ₂` such that `Σ₁ ∪ Σ₂ = Σ` and `Σ₁ ∩ Σ₂ = F`.

This file proves the topological facts about such a side that are needed to restrict a
presentation to it. We read `Σ₁` as a space of its own (the subtype `↥Σ₁`).

* A connected set that misses `F` and meets `Σ₁` lies in `Σ₁` (`subset_side`). So every edge of
  `Γ` and every space of `Γ` lies in `Σ₁` or misses it.
* A point of `Σ₁` outside `F` is in `bd(Σ₁)` exactly when it is in `bd(Σ)`, and every boundary
  point of `Σ₁` is in `F ∪ bd(Σ)` (`bd_side_subset`, `mem_bd_side_of_mem_bd`). Both follow because
  `Σ \ Σ₂` is an open set of `Σ` and of `Σ₁`.
* `Γ ∩ Σ₁`, read in `Σ₁`, is a drawing `sideDrawing Γ Σ₁`, with the vertices of `Γ` in `Σ₁` and
  the edges of `Γ` in `Σ₁`.
* Every cuff of `Σ₁` has at least two vertices of `Γ ∩ Σ₁` (`two_le_ncard_sideDrawing_cuff`):
  either it is a cuff of `Σ`, or it contains both ends of `F`.
* The spaces of `Γ ∩ Σ₁` in `Σ₁` that lie in `bd(Σ)` are the spaces of `Γ` in `Σ` that lie in
  `Σ₁` (`image_mem_drawingSpaces`, `preimage_mem_drawingSpaces`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Side

open Set Topology Function GraphMinor.Surface

universe w

variable {S : Type w} [TopologicalSpace S]

/-! ## Sides of a line -/

/-- A compact subset of a Hausdorff space is closed; in particular a surface in a surface. -/
theorem isClosed_of_isSurface [T2Space S] {S₁ : Set S} (h : IsSurface S₁) : IsClosed S₁ :=
  (isCompact_iff_compactSpace.mpr h.1).isClosed

/-- If `S₁, S₂` are closed, `S₁ ∪ S₂ = univ` and `S₁ ∩ S₂ = F`, then a preconnected set that misses
`F` and meets `S₁` lies in `S₁`. -/
theorem subset_side {S₁ S₂ F : Set S} (h₁ : IsClosed S₁) (h₂ : IsClosed S₂)
    (hun : S₁ ∪ S₂ = univ) (hint : S₁ ∩ S₂ = F) {X : Set S} (hX : IsPreconnected X)
    (hXF : Disjoint X F) (hX₁ : (X ∩ S₁).Nonempty) : X ⊆ S₁ := by
  intro x hxX
  by_contra hx1
  have hx2 : x ∈ S₂ := ((hun ▸ mem_univ x : x ∈ S₁ ∪ S₂)).resolve_left hx1
  obtain ⟨y, hyX, hy1, hy2⟩ := isPreconnected_closed_iff.mp hX S₁ S₂ h₁ h₂
    (by rw [hun]; exact subset_univ X) hX₁ ⟨x, hxX, hx2⟩
  exact disjoint_left.mp hXF hyX (hint ▸ ⟨hy1, hy2⟩)

/-- A preconnected set that misses `F` lies in `S₁` or misses it. -/
theorem subset_or_disjoint_side {S₁ S₂ F : Set S} (h₁ : IsClosed S₁) (h₂ : IsClosed S₂)
    (hun : S₁ ∪ S₂ = univ) (hint : S₁ ∩ S₂ = F) {X : Set S} (hX : IsPreconnected X)
    (hXF : Disjoint X F) : X ⊆ S₁ ∨ Disjoint X S₁ := by
  by_cases h : (X ∩ S₁).Nonempty
  · exact Or.inl (subset_side h₁ h₂ hun hint hX hXF h)
  · exact Or.inr (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h))

omit [TopologicalSpace S] in
/-- A set that misses `S₁` lies in `S₂`. -/
theorem subset_two_of_disjoint {S₁ S₂ : Set S} (hun : S₁ ∪ S₂ = univ) {X : Set S}
    (hX : Disjoint X S₁) : X ⊆ S₂ := fun x hx =>
  ((hun ▸ mem_univ x : x ∈ S₁ ∪ S₂)).resolve_left (disjoint_left.mp hX hx)

/-- For an open embedding `e`, `e x` is a boundary point exactly when `x` is. -/
theorem mem_bd_iff_of_isOpenEmbedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : X → Y} (he : IsOpenEmbedding e) {x : X} : e x ∈ bd Y ↔ x ∈ bd X :=
  ⟨fun h hx => h (isInteriorPoint_of_isOpenEmbedding he hx), bd_of_isOpenEmbedding he⟩

/-- A point of `S₁` outside `S₂` is a boundary point of `S₁` exactly when it is a boundary point
of `S`. The set `S \ S₂` is open and lies in `S₁`. -/
theorem mem_bd_side_iff {S₁ S₂ : Set S} (h₂ : IsClosed S₂) (hun : S₁ ∪ S₂ = univ) {x : S₁}
    (hx : x.1 ∉ S₂) : x ∈ bd S₁ ↔ x.1 ∈ bd S := by
  set O : Set S₁ := Subtype.val ⁻¹' S₂ᶜ with hO
  have hOo : IsOpen O := h₂.isOpen_compl.preimage continuous_subtype_val
  have hj : IsOpenEmbedding (Subtype.val : O → S₁) := hOo.isOpenEmbedding_subtypeVal
  have hrange : range (fun y : O => (y.1.1 : S)) = S₂ᶜ := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hz
      have hz1 : z ∈ S₁ := ((hun ▸ mem_univ z : z ∈ S₁ ∪ S₂)).resolve_right hz
      exact ⟨⟨⟨z, hz1⟩, hz⟩, rfl⟩
  have hk : IsOpenEmbedding (fun y : O => (y.1.1 : S)) :=
    ⟨IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal, hrange ▸ h₂.isOpen_compl⟩
  let x' : O := ⟨x, hx⟩
  exact (mem_bd_iff_of_isOpenEmbedding hj (x := x')).trans
    (mem_bd_iff_of_isOpenEmbedding hk (x := x')).symm

/-- A boundary point of a side `S₁` lies in `F ∪ bd(S)`. -/
theorem bd_side_subset {S₁ S₂ F : Set S} (h₂ : IsClosed S₂) (hun : S₁ ∪ S₂ = univ)
    (hint : S₁ ∩ S₂ = F) {x : S₁} (hx : x ∈ bd S₁) : x.1 ∈ F ∪ bd S := by
  by_cases hx2 : x.1 ∈ S₂
  · exact Or.inl (hint ▸ ⟨x.2, hx2⟩)
  · exact Or.inr ((mem_bd_side_iff h₂ hun hx2).mp hx)

/-- A point of a side `S₁` in `bd(S) \ F` is a boundary point of `S₁`. -/
theorem mem_bd_side_of_mem_bd {S₁ S₂ F : Set S} (h₂ : IsClosed S₂) (hun : S₁ ∪ S₂ = univ)
    (hint : S₁ ∩ S₂ = F) {x : S₁} (hx : x.1 ∈ bd S) (hxF : x.1 ∉ F) : x ∈ bd S₁ := by
  have hx2 : x.1 ∉ S₂ := fun h => hxF (hint ▸ ⟨x.2, h⟩)
  exact (mem_bd_side_iff h₂ hun hx2).mpr hx

/-- The interior points of a 2-manifold with boundary are dense. -/
theorem dense_compl_bd (h : ∀ x : S, IsManifoldPoint x) : Dense (bd S)ᶜ := by
  intro x
  rw [_root_.mem_closure_iff]
  intro O hO hxO
  obtain ⟨V, P, -, hxV, hVO, hPV, -, hPint, hVcl⟩ := (h x).exists_half hO hxO
  obtain ⟨y, hy⟩ : P.Nonempty := by
    by_contra hP
    rw [not_nonempty_iff_eq_empty] at hP
    have := hVcl hxV
    rw [hP, closure_empty] at this
    exact this
  exact ⟨y, hVO (hPV hy), fun hb => hb (hPint y hy)⟩

/-- Let `S₁, S₂` be surfaces in a surface `S` with `S₁ ∩ S₂ = F`, where `F` is a line. Then every
point of `F` is a boundary point of `S₁`. Otherwise a small closed disc around it in `S₁` is a
neighbourhood of it in `S`, and the part of that disc in `S₂`, which is in `F`, would contain a closed
disc. -/
theorem preimage_subset_bd_side [T2Space S] (hS : IsSurface S) {S₁ S₂ F : Set S} {a b : S}
    (hS₁ : IsSurface S₁) (hS₂ : IsSurface S₂) (hint : S₁ ∩ S₂ = F)
    (hF : IsLineWithEnds F a b) : Subtype.val ⁻¹' F ⊆ bd S₁ := by
  have : T2Space S₁ := hS₁.2.1
  have : T2Space S₂ := hS₂.2.1
  have hno_disc : ∀ E : Set S, IsClosedDisc E → ¬ E ⊆ F := fun E hE hEF =>
    GM11.not_isOArc_of_subset_line (by obtain ⟨φ, -, -⟩ := hF; exact ⟨φ⟩) hE.isOArc_discBd
      ((discBd_subset E).trans hEF)
  intro x hxF
  by_contra hnb
  have hxi : IsInteriorPoint x := by
    by_contra hn
    exact hnb hn
  obtain ⟨D₁, hD₁, hxD₁, -⟩ := GM07.exists_disc_in_open hxi isOpen_univ (mem_univ x)
  obtain ⟨hD, hD_bd⟩ := GM11.isClosedDisc_image hD₁ continuous_subtype_val.continuousOn
    Subtype.val_injective.injOn
  set D : Set S := Subtype.val '' D₁
  have hxD : x.1 ∈ discInt D := by
    refine ⟨mem_image_of_mem Subtype.val hxD₁.1, ?_⟩
    rw [hD_bd]
    rintro ⟨y, hy, hxy⟩
    exact hxD₁.2 (Subtype.ext hxy ▸ hy)
  have hDo : IsOpen (discInt D) := hD.isOpen_discInt hS.2.2
  have hx₂ : x.1 ∈ S₂ := (hint ▸ hxF).2
  let x₂ : S₂ := ⟨x.1, hx₂⟩
  have hUo : IsOpen (Subtype.val ⁻¹' discInt D : Set S₂) := hDo.preimage continuous_subtype_val
  obtain ⟨y₂, hy₂D, hy₂b⟩ :=
    (dense_compl_bd hS₂.2.2).inter_open_nonempty _ hUo ⟨x₂, hxD⟩
  have hy₂i : IsInteriorPoint y₂ := by
    by_contra hn
    exact hy₂b hn
  obtain ⟨E₂, hE₂, -, hE₂_sub⟩ := GM07.exists_disc_in_open hy₂i hUo hy₂D
  obtain ⟨hE, -⟩ := GM11.isClosedDisc_image hE₂ continuous_subtype_val.continuousOn
    Subtype.val_injective.injOn
  refine hno_disc (Subtype.val '' E₂) hE ?_
  rintro _ ⟨z, hz, rfl⟩
  rw [← hint]
  have hzD : z.1 ∈ discInt D := hE₂_sub hz
  obtain ⟨w, -, hwz⟩ := hzD.1
  exact ⟨hwz ▸ w.2, z.2⟩

/-- The boundary of a side: `bd(S₁) = S₁ ∩ (F ∪ bd(S))`. -/
theorem mem_bd_side_iff' [T2Space S] (hS : IsSurface S) {S₁ S₂ F : Set S} {a b : S}
    (hS₁ : IsSurface S₁) (hS₂ : IsSurface S₂) (hun : S₁ ∪ S₂ = univ) (hint : S₁ ∩ S₂ = F)
    (hF : IsLineWithEnds F a b) {x : S₁} : x ∈ bd S₁ ↔ x.1 ∈ F ∪ bd S := by
  have h₂ : IsClosed S₂ := isClosed_of_isSurface hS₂
  refine ⟨bd_side_subset h₂ hun hint, fun h => ?_⟩
  by_cases hxF : x.1 ∈ F
  · exact preimage_subset_bd_side hS hS₁ hS₂ hint hF hxF
  · exact mem_bd_side_of_mem_bd h₂ hun hint (h.resolve_left hxF) hxF

/-! ## The drawing `Γ ∩ Σ₁` in `Σ₁` -/

section SideDrawing

variable [T2Space S]

/-- The point set of `Γ ∩ S₁` lies in `S₁` when `S₁` is closed. -/
theorem interSet_U_subset (Γ : Drawing S) {S₁ : Set S} (h₁ : IsClosed S₁) :
    (Γ.interSet S₁).U ⊆ S₁ := by
  intro x hx
  rcases hx with (⟨⟨-, hx⟩, -⟩ | hx) | hx
  · exact hx
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    exact closure_minimal he.1.2 h₁ hxe.1
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    exact closure_minimal he.1.2 h₁ hxe

/-- The drawing `Γ ∩ S₁` (Graph Minors XXI, proof of (6.3), claim (4): "$\Gamma_i = \Gamma \cap
\Sigma_i$"), read as a drawing in the space `↥S₁`. Its vertices are those of `Γ` in `S₁`, and its
edges are those of `Γ` in `S₁`. -/
noncomputable def sideDrawing (Γ : Drawing S) {S₁ : Set S} (h₁ : IsClosed S₁) : Drawing S₁ :=
  GM12.drawingInSubspace (Γ.interSet S₁) S₁ (interSet_U_subset Γ h₁)

theorem sideDrawing_V (Γ : Drawing S) {S₁ : Set S} (h₁ : IsClosed S₁) :
    (sideDrawing Γ h₁).V = Subtype.val ⁻¹' Γ.V := by
  rw [sideDrawing, GM12.drawingInSubspace_V]
  ext x
  change x.1 ∈ Γ.spanV (Γ.V ∩ S₁) {e | e ∈ Γ.E ∧ e ⊆ S₁} ↔ x.1 ∈ Γ.V
  constructor
  · intro hx
    exact Γ.spanV_subset _ _ hx
  · intro hx
    exact Or.inl ⟨⟨hx, x.2⟩, hx⟩

theorem sideDrawing_E (Γ : Drawing S) {S₁ : Set S} (h₁ : IsClosed S₁) :
    (sideDrawing Γ h₁).E = (fun e : Set S => (Subtype.val : S₁ → S) ⁻¹' e) ''
      {e | e ∈ Γ.E ∧ e ⊆ S₁} := by
  rw [sideDrawing, GM12.drawingInSubspace_E, Drawing.interSet, Γ.span_E]
  congr 1
  ext e
  simp only [mem_inter_iff, mem_ofPred_eq]
  tauto

/-- A point of the drawing `Γ ∩ S₁` that is not a vertex lies in an edge of `Γ` inside `S₁`. -/
theorem exists_edge_of_mem_sideDrawing_U (Γ : Drawing S) {S₁ : Set S} (h₁ : IsClosed S₁)
    {x : S₁} (hxU : x ∈ (sideDrawing Γ h₁).U) (hxV : x ∉ (sideDrawing Γ h₁).V) :
    ∃ e ∈ Γ.E, e ⊆ S₁ ∧ x.1 ∈ e := by
  rw [sideDrawing, GM12.drawingInSubspace_U] at hxU
  rw [sideDrawing, GM12.drawingInSubspace_V] at hxV
  have h : x.1 ∈ Γ.spanU (Γ.V ∩ S₁) {e | e ∈ Γ.E ∧ e ⊆ S₁} \
      Γ.spanV (Γ.V ∩ S₁) {e | e ∈ Γ.E ∧ e ⊆ S₁} := ⟨hxU, hxV⟩
  rw [Γ.spanU_diff_spanV] at h
  obtain ⟨e, ⟨⟨he, heS⟩, -⟩, hxe⟩ := h
  exact ⟨e, he, heS, hxe⟩

end SideDrawing

/-! ## Cuffs and spaces of a side -/

section Cuffs

variable [T2Space S]

omit [T2Space S] in
/-- Let `Y ⊆ A ∪ B` be preconnected, with `A, B` closed, and let `Y` meet both `A` and `B`. Then
`Y` meets `A ∩ B`. -/
theorem inter_nonempty_of_preconnected {A B Y : Set S} (hA : IsClosed A) (hB : IsClosed B)
    (hY : IsPreconnected Y) (hYsub : Y ⊆ A ∪ B) (hYA : (Y ∩ A).Nonempty)
    (hYB : (Y ∩ B).Nonempty) : (Y ∩ (A ∩ B)).Nonempty :=
  isPreconnected_closed_iff.mp hY A B hA hB hYsub hYA hYB

variable {Γ : Drawing S} {S₁ S₂ F : Set S} {a b : S}

/-- Every cuff of a side `S₁` has at least two vertices of `Γ ∩ S₁`. A cuff of `S₁` that lies in
`bd(S)` is a cuff of `S`, which has two vertices of `Γ` by hypothesis; any other cuff of `S₁` meets
the interior of `F` and leaves `F`, so it passes through both ends `a, b` of `F`. -/
theorem two_le_ncard_sideDrawing_cuff (hS : IsSurface S) (hS₁ : IsSurface S₁)
    (h₁ : IsClosed S₁) (h₂ : IsClosed S₂) (hun : S₁ ∪ S₂ = univ) (hint : S₁ ∩ S₂ = F)
    (hF : IsLineWithEnds F a b) (hFbd : F ∩ bd S = {a, b}) (haV : a ∈ Γ.V) (hbV : b ∈ Γ.V)
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) :
    ∀ C₁ ∈ cuffs S₁, 2 ≤ ((sideDrawing Γ h₁).V ∩ C₁).ncard := by
  intro C₁ hC₁
  have hbdS : IsClosed (bd S) := (cuff_statement.{w} S hS).1
  have hFcl : IsClosed F := hF.isCompact.isClosed
  have hC₁O : IsOArc C₁ := (cuff_statement.{w} S₁ hS₁).2.2 C₁ hC₁
  set Z : Set S := Subtype.val '' C₁ with hZdef
  have hZO : IsOArc Z := by
    obtain ⟨φ⟩ := hC₁O
    exact ⟨φ.trans (IsEmbedding.subtypeVal.homeomorphImage C₁)⟩
  have hC₁bd : C₁ ⊆ bd S₁ := by
    obtain ⟨x, -, rfl⟩ := hC₁
    exact connectedComponentIn_subset _ _
  have hZsub : Z ⊆ F ∪ bd S := by
    rintro _ ⟨y, hy, rfl⟩
    exact bd_side_subset h₂ hun hint (hC₁bd hy)
  have hZpc : IsPathConnected Z := by
    obtain ⟨φ⟩ := hZO
    have : Z = range (fun t => (φ t).1) := by
      ext z; constructor
      · intro hz; exact ⟨φ.symm ⟨z, hz⟩, by simp⟩
      · rintro ⟨t, rfl⟩; exact (φ t).2
    rw [this]
    exact isPathConnected_range (continuous_subtype_val.comp φ.continuous)
  have hV₁fin : ((sideDrawing Γ h₁).V ∩ C₁).Finite := (sideDrawing Γ h₁).finite_V.subset
    inter_subset_left
  by_cases hZbd : Z ⊆ bd S
  · -- `Z` is a cuff of `S`.
    obtain ⟨z, hzZ⟩ : Z.Nonempty := by
      obtain ⟨φ⟩ := hZO
      exact ⟨(φ 1).1, (φ 1).2⟩
    set C := connectedComponentIn (bd S) z with hCdef
    have hC : C ∈ cuffs S := ⟨z, hZbd hzZ, rfl⟩
    have hZC : Z ⊆ C := hZpc.isConnected.isPreconnected.subset_connectedComponentIn hzZ hZbd
    have hCO : IsOArc C := (cuff_statement.{w} S hS).2.2 C hC
    have hZeq : Z = C := GM11.eq_of_oArc_subset hZO hCO hZC
    have himg : Γ.V ∩ C ⊆ Subtype.val '' ((sideDrawing Γ h₁).V ∩ C₁) := by
      rintro x ⟨hxV, hxC⟩
      rw [← hZeq] at hxC
      obtain ⟨y, hy, rfl⟩ := hxC
      refine ⟨y, ⟨?_, hy⟩, rfl⟩
      rw [sideDrawing_V]
      exact hxV
    calc 2 ≤ (Γ.V ∩ C).ncard := hge2 C hC
      _ ≤ (Subtype.val '' ((sideDrawing Γ h₁).V ∩ C₁)).ncard :=
          ncard_le_ncard himg (hV₁fin.image _)
      _ = ((sideDrawing Γ h₁).V ∩ C₁).ncard := ncard_image_of_injective _ Subtype.val_injective
  · -- `Z` meets the interior of `F` and leaves `F`, so it contains `a` and `b`.
    obtain ⟨p, hpZ, hpbd⟩ := not_subset.mp hZbd
    have hpF : p ∈ F := (hZsub hpZ).resolve_right hpbd
    have hZF : ¬ Z ⊆ F := fun h => GM11.not_isOArc_of_subset_line
      (by obtain ⟨φ, -, -⟩ := hF; exact ⟨φ⟩) hZO h
    obtain ⟨q, hqZ, hqF⟩ := not_subset.mp hZF
    have hqbd : q ∈ bd S := (hZsub hqZ).resolve_left hqF
    have hmeet : ∀ Y ⊆ Z, IsPreconnected Y → p ∈ Y → q ∈ Y → a ∈ Y ∨ b ∈ Y := by
      intro Y hYZ hY hpY hqY
      obtain ⟨y, hyY, hyF, hybd⟩ := inter_nonempty_of_preconnected hFcl hbdS hY
        (hYZ.trans hZsub) ⟨p, hpY, hpF⟩ ⟨q, hqY, hqbd⟩
      have : y ∈ ({a, b} : Set S) := hFbd ▸ ⟨hyF, hybd⟩
      rcases this with rfl | rfl
      · exact Or.inl hyY
      · exact Or.inr hyY
    have habd : a ∈ F ∩ bd S ∧ b ∈ F ∩ bd S := by
      rw [hFbd]; exact ⟨Or.inl rfl, Or.inr rfl⟩
    have hpa : p ≠ a := fun h => hpbd (h ▸ habd.1.2)
    have hpb : p ≠ b := fun h => hpbd (h ▸ habd.2.2)
    have hqa : q ≠ a := fun h => hqF (h ▸ hF.left_mem)
    have hqb : q ≠ b := fun h => hqF (h ▸ hF.right_mem)
    have hab : a ≠ b := hF.ne'
    have hboth : a ∈ Z ∧ b ∈ Z := by
      rcases hmeet Z subset_rfl hZpc.isConnected.isPreconnected hpZ hqZ with ha | hb
      · refine ⟨ha, ?_⟩
        rcases hmeet (Z \ {a}) sdiff_subset
          (isPathConnected_oArc_diff hZO ha).isConnected.isPreconnected ⟨hpZ, hpa⟩
          ⟨hqZ, hqa⟩ with h | h
        · exact absurd rfl h.2
        · exact h.1
      · refine ⟨?_, hb⟩
        rcases hmeet (Z \ {b}) sdiff_subset
          (isPathConnected_oArc_diff hZO hb).isConnected.isPreconnected ⟨hpZ, hpb⟩
          ⟨hqZ, hqb⟩ with h | h
        · exact h.1
        · exact absurd rfl h.2
    obtain ⟨⟨a', ha'C, ha'eq⟩, ⟨b', hb'C, hb'eq⟩⟩ := hboth
    have hsub : ({a', b'} : Set S₁) ⊆ (sideDrawing Γ h₁).V ∩ C₁ := by
      intro x hx
      rcases hx with hx | hx
      · rw [hx]
        refine ⟨?_, ha'C⟩
        rw [sideDrawing_V]
        change a'.1 ∈ Γ.V
        rw [ha'eq]
        exact haV
      · rw [mem_singleton_iff] at hx
        rw [hx]
        refine ⟨?_, hb'C⟩
        rw [sideDrawing_V]
        change b'.1 ∈ Γ.V
        rw [hb'eq]
        exact hbV
    have hne : a' ≠ b' := fun h => hab (by rw [← ha'eq, ← hb'eq, h])
    calc 2 = ({a', b'} : Set S₁).ncard := (ncard_pair hne).symm
      _ ≤ _ := ncard_le_ncard hsub hV₁fin

/-- The component of `bd(S₁) \ V(Γ ∩ S₁)` through a point of `bd(S)` is, in `S`, the component of
`bd(S) \ V(Γ)` through that point: it is a space of `Γ ∩ S₁` in `S₁` and a space of `Γ` in `S`. -/
theorem image_connectedComponentIn_eq (hS : IsSurface S) (h₁ : IsClosed S₁) (h₂ : IsClosed S₂)
    (hun : S₁ ∪ S₂ = univ) (hint : S₁ ∩ S₂ = F) (hFcl : IsClosed F)
    (hFbd : F ∩ bd S = {a, b}) (haV : a ∈ Γ.V) (hbV : b ∈ Γ.V) {x : S₁}
    (hx : x ∈ bd S₁ \ (sideDrawing Γ h₁).V) (hxbd : x.1 ∈ bd S) :
    Subtype.val '' connectedComponentIn (bd S₁ \ (sideDrawing Γ h₁).V) x =
      connectedComponentIn (bd S \ Γ.V) x.1 := by
  have hbdS : IsClosed (bd S) := (cuff_statement.{w} S hS).1
  have hFV : F ∩ bd S ⊆ Γ.V := by
    rw [hFbd]; rintro y (rfl | rfl) <;> assumption
  have hxV : x.1 ∉ Γ.V := by
    have := hx.2
    rwa [sideDrawing_V] at this
  apply Subset.antisymm
  · set T := Subtype.val '' connectedComponentIn (bd S₁ \ (sideDrawing Γ h₁).V) x
    have hTpc : IsPreconnected T :=
      isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn
    have hTsub : T ⊆ bd S ∪ F := by
      rintro _ ⟨y, hy, rfl⟩
      exact (bd_side_subset h₂ hun hint (connectedComponentIn_subset _ _ hy).1).symm
    have hTV : ∀ y ∈ T, y ∉ Γ.V := by
      rintro _ ⟨y, hy, rfl⟩ hyV
      have := (connectedComponentIn_subset _ _ hy).2
      rw [sideDrawing_V] at this
      exact this hyV
    have hxT : x.1 ∈ T := ⟨x, mem_connectedComponentIn hx, rfl⟩
    have hTF : ¬ (T ∩ F).Nonempty := by
      intro hne
      obtain ⟨y, hyT, hybd, hyF⟩ := inter_nonempty_of_preconnected hbdS hFcl hTpc hTsub
        ⟨x.1, hxT, hxbd⟩ hne
      exact hTV y hyT (hFV ⟨hyF, hybd⟩)
    refine hTpc.subset_connectedComponentIn hxT ?_
    intro y hy
    refine ⟨(hTsub hy).resolve_right fun hyF => hTF ⟨y, hy, hyF⟩, hTV y hy⟩
  · set C := connectedComponentIn (bd S \ Γ.V) x.1
    have hCpc : IsPreconnected C := isPreconnected_connectedComponentIn
    have hCF : Disjoint C F := by
      rw [disjoint_left]
      intro y hyC hyF
      have hy := connectedComponentIn_subset _ _ hyC
      exact hy.2 (hFV ⟨hyF, hy.1⟩)
    have hC₁ : C ⊆ S₁ := subset_side h₁ h₂ hun hint hCpc hCF
      ⟨x.1, mem_connectedComponentIn ⟨hxbd, hxV⟩, x.2⟩
    have hpre : IsPreconnected ((Subtype.val : S₁ → S) ⁻¹' C) := by
      rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
        inter_eq_right.mpr hC₁]
      exact hCpc
    have hsub : (Subtype.val : S₁ → S) ⁻¹' C ⊆
        connectedComponentIn (bd S₁ \ (sideDrawing Γ h₁).V) x := by
      refine hpre.subset_connectedComponentIn (mem_connectedComponentIn ⟨hxbd, hxV⟩) ?_
      intro y hy
      have hy' := connectedComponentIn_subset _ _ hy
      refine ⟨mem_bd_side_of_mem_bd h₂ hun hint hy'.1 (disjoint_left.mp hCF hy), ?_⟩
      rw [sideDrawing_V]
      exact hy'.2
    intro y hy
    exact ⟨⟨y, hC₁ hy⟩, hsub hy, rfl⟩

/-- A space of `Γ ∩ S₁` in `S₁` that lies in `bd(S)` is, in `S`, a space of `Γ`. -/
theorem image_mem_drawingSpaces (hS : IsSurface S) (h₁ : IsClosed S₁) (h₂ : IsClosed S₂)
    (hun : S₁ ∪ S₂ = univ) (hint : S₁ ∩ S₂ = F) (hFcl : IsClosed F)
    (hFbd : F ∩ bd S = {a, b}) (haV : a ∈ Γ.V) (hbV : b ∈ Γ.V) {s₁ : Set S₁}
    (hs₁ : s₁ ∈ drawingSpaces (sideDrawing Γ h₁)) (hs₁bd : s₁ ⊆ Subtype.val ⁻¹' bd S) :
    Subtype.val '' s₁ ∈ drawingSpaces Γ := by
  obtain ⟨x, hx, rfl⟩ := hs₁
  rw [image_connectedComponentIn_eq hS h₁ h₂ hun hint hFcl hFbd haV hbV hx
    (hs₁bd (mem_connectedComponentIn hx))]
  refine ⟨x.1, ⟨hs₁bd (mem_connectedComponentIn hx), ?_⟩, rfl⟩
  have := hx.2
  rwa [sideDrawing_V] at this

/-- A space of `Γ` in `S` that lies in `S₁` is, read in `S₁`, a space of `Γ ∩ S₁`. -/
theorem preimage_mem_drawingSpaces (hS : IsSurface S) (h₁ : IsClosed S₁) (h₂ : IsClosed S₂)
    (hun : S₁ ∪ S₂ = univ) (hint : S₁ ∩ S₂ = F) (hFcl : IsClosed F)
    (hFbd : F ∩ bd S = {a, b}) (haV : a ∈ Γ.V) (hbV : b ∈ Γ.V) {s : Set S}
    (hs : s ∈ drawingSpaces Γ) (hsS₁ : s ⊆ S₁) :
    (Subtype.val : S₁ → S) ⁻¹' s ∈ drawingSpaces (sideDrawing Γ h₁) := by
  obtain ⟨z, hz, rfl⟩ := hs
  have hzS₁ : z ∈ S₁ := hsS₁ (mem_connectedComponentIn hz)
  set x : S₁ := ⟨z, hzS₁⟩
  have hFV : F ∩ bd S ⊆ Γ.V := by
    rw [hFbd]; rintro y (rfl | rfl) <;> assumption
  have hzF : z ∉ F := fun h => hz.2 (hFV ⟨h, hz.1⟩)
  have hx : x ∈ bd S₁ \ (sideDrawing Γ h₁).V := by
    refine ⟨mem_bd_side_of_mem_bd h₂ hun hint hz.1 hzF, ?_⟩
    rw [sideDrawing_V]
    exact hz.2
  refine ⟨x, hx, ?_⟩
  rw [← image_connectedComponentIn_eq hS h₁ h₂ hun hint hFcl hFbd haV hbV hx hz.1,
    preimage_image_eq _ Subtype.val_injective]

end Cuffs

end Side
end GM21
end GraphMinor
