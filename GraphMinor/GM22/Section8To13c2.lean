module

public import GraphMinor.GM22.Section8To13c1
public import GraphMinor.GM13.Section7FourProof
public import GraphMinor.GM11.OArcCircuit
public import GraphMinor.GM16.SphereRespectful
public import GraphMinor.GM16.Metric

/-!
# Outer Region, Perimeter Circuit, Corners, and Tangle for Wall Drawings

This file continues the geometric setup for deriving Graph Minors XIII, Theorem (10.2) from
Graph Minors XXII, Theorem (8.3) (page 563):
- Characterization of perimeter vertices via `interior (fig1EnclosedSet W.height)`.
- Construction of the outer region `r₀` and perimeter circuit `C₀` satisfying Hypothesis (ii) of
  Theorem (8.3) and `drawingVertToGraph Γ '' C₀.V = V(W.perimeter)`.
- Construction of the four corners `PiSet` satisfying Hypothesis (iii) of Theorem (8.3) and
  `drawingVertToGraph Γ '' PiSet = W.corners`.
- Lifting of vertex sets of `elementaryWall` to `W.graph` (`liftElemSet`) and proof that no
  separation `(A, B) ∈ T` of order `≤ 3` in the wall tangle has `PiSet ⊆ A.vertexSet`,
  establishing Hypothesis (iv) of Theorem (8.3).
-/

@[expose] public section

namespace GraphMinor
namespace GM22

open Set Function Topology Graph Hypergraph
open GraphMinor.Surface
open GraphMinor.GM09
open GraphMinor.GM11
open GraphMinor.GM13
open GraphMinor.GM14

universe u v

/-! ## 1. Characterization of Perimeter Vertices and Outer Region / Circuit (`hyp_ii`, `hyp_iii`) -/

/-- For any vertex `v ∈ V(W.graph)` of a Fig. 1 drawn wall `W`, `v ∈ V(W.perimeter)` if and only if
`pos v ∉ interior (fig1EnclosedSet W.height)`. -/
theorem mem_perimeter_iff_pos_not_mem_interior {α : Type u} {β : Type v}
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hinj : InjOn pos V(W.graph))
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hΓe : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β) (hf : f ∈ E(W.graph)),
      f ∈ E(W.subdivisionPaths (W.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q)
    {v : α} (hv : v ∈ V(W.graph)) :
    v ∈ V(W.perimeter) ↔ pos v ∉ interior (fig1EnclosedSet W.height) := by
  constructor
  · intro hv_perim
    rw [Wall.perimeter, GM09.vertexSet_subgraphSUnion] at hv_perim
    obtain ⟨P, ⟨e₀, ⟨p, q, ⟨hadj, rfl⟩, hp_perim, hq_perim⟩, rfl⟩, hvP⟩ :=
      mem_iUnion₂.mp hv_perim
    have hseg := pos_mem_fig1Segment_of_mem_subdivisionPaths hΓv hΓe hadj hvP
    exact not_mem_interior_fig1EnclosedSet_of_perimeter_segment
      W.toWall.two_le_height W.toWall.even_height hp_perim hq_perim hadj hseg
  · intro hnot_int
    by_contra hv_not_perim
    have hrect := pos_mem_openInnerRect_of_not_perimeter hinj hpos_branch hΓv hΓe
      ⟨hv, hv_not_perim⟩
    have hh1 : 1 ≤ W.height := by have := W.toWall.two_le_height; omega
    exact hnot_int (openInnerRect_subset_interior_fig1EnclosedSet hh1 hrect)

/-- If `C` is a subdrawing of `N` with `C.U = F`, then `C.V = F ∩ N.V`. -/
theorem subdrawing_V_eq_inter_of_U_eq {S : Type*} [TopologicalSpace S]
    {N C : Drawing S} {F : Set S} (hsub : C.IsSubdrawing N) (hU : C.U = F) :
    C.V = F ∩ N.V := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · intro hx
    exact ⟨hU ▸ C.V_subset_U hx, hsub.1 hx⟩
  · rintro ⟨hxF, hxNV⟩
    by_contra hxCV
    obtain ⟨e, heC, hxe⟩ := exists_mem_arcComponent (F := C.U \ C.V) ⟨hU.symm ▸ hxF, hxCV⟩
    exact ((hsub.2 heC).2.1 hxe).2 hxNV

theorem subBd_eq_frontier {S : Type*} [TopologicalSpace S] (Δ : Set S) :
    subBd Δ = frontier Δ := by
  rw [subBd, ← compl_eq_univ_sdiff, ← frontier_eq_closure_inter_closure]

theorem interior_image_eq_of_isOpenEmbedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsOpenEmbedding f) (A : Set X) :
    interior (f '' A) = f '' interior A := by
  apply Subset.antisymm
  · intro y hy
    obtain ⟨x, hxA, rfl⟩ := interior_subset hy
    refine ⟨x, ?_, rfl⟩
    rw [mem_interior]
    refine ⟨f ⁻¹' interior (f '' A), ?_,
      hf.continuous.isOpen_preimage _ isOpen_interior, hy⟩
    intro z hz
    obtain ⟨w, hwA, hzw⟩ := interior_subset hz
    rwa [← hf.injective hzw]
  · exact (hf.isOpenMap _ isOpen_interior).subset_interior_iff.mpr (image_mono interior_subset)

/-- Given a Fig. 1 sphere drawing `Γ` of a wall `W`, the complement of the enclosed disc
`E₀ = fig1Sph φ '' fig1EnclosedSet W.height` has interior `r₀ ∈ Γ.drawing.R` bounded by a circuit
`C₀` of `Γ.drawing` whose vertex set corresponds under `drawingVertToGraph Γ` to `V(W.perimeter)`. -/
theorem exists_outer_region_and_perimeter_circuit {α : Type u} {β : Type v} [Nonempty α]
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hpos : ∀ v ∈ V(W.graph), pos v ∈ fig1Set W.height)
    (hinj : InjOn pos V(W.graph))
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hΓU : Γ.drawing.U = fig1Sph φ '' fig1Set W.height)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hΓe : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β) (hf : f ∈ E(W.graph)),
      f ∈ E(W.subdivisionPaths (W.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q) :
    let E₀ := fig1Sph φ '' fig1EnclosedSet W.height
    let r₀ := interior (closure E₀ᶜ)
    ∃ C₀ : Drawing (OnePoint EuclideanPlane),
      (C₀.IsSubdrawing Γ.drawing ∧ C₀.IsCircuit ∧ r₀ ∈ Γ.drawing.R ∧ subBd r₀ = C₀.U) ∧
      C₀.U = discBd E₀ ∧
      closure r₀ = closure E₀ᶜ ∧
      (∀ v ∈ V(W.graph), fig1Sph φ (pos v) ∈ C₀.V ↔ v ∈ V(W.perimeter)) ∧
      (∀ x ∈ Γ.drawing.V, x ∈ C₀.V ↔ drawingVertToGraph Γ x ∈ V(W.perimeter)) ∧
      drawingVertToGraph Γ '' C₀.V = V(W.perimeter) := by
  intro E₀ r₀
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  have hSph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hf_open : Topology.IsOpenEmbedding (fig1Sph φ) := isOpenEmbedding_fig1Sph φ
  have hf_emb : Topology.IsEmbedding (fig1Sph φ) := hf_open.isEmbedding
  have he : Even W.height := W.toWall.even_height
  have hh2 : 2 ≤ W.height := W.toWall.two_le_height
  have hC : IsClosedDisc E₀ := isClosedDisc_image_fig1EnclosedSet hS hf_emb (by omega)
  obtain ⟨hD, hBd, hCup, hMeet⟩ := GM16.isClosedDisc_closure_compl_of_isSphere hSph hC
  have hDrawing : Γ.drawing.U ⊆ E₀ := by
    rw [hΓU]; exact image_mono (fig1Set_subset_enclosed he hh2)
  have hBdU : discBd (closure E₀ᶜ) ⊆ Γ.drawing.U := by
    rw [hBd, hΓU]; exact discBd_image_enclosed_subset hS hf_emb he hh2
  have hEmpty : Disjoint r₀ Γ.drawing.U := by
    refine Set.disjoint_left.mpr fun w hwInt hwU => ?_
    have hwBd : w ∈ discBd E₀ := hMeet ▸ ⟨hDrawing hwU, interior_subset hwInt⟩
    have hwFr : w ∈ frontier (closure E₀ᶜ) :=
      (GM11.IsClosedDisc.frontier_eq_discBd hS hD).symm ▸ (hBd.symm ▸ hwBd)
    exact hwFr.2 hwInt
  obtain ⟨hr₀_R, hcl_r₀⟩ := GM16.empty_disc_is_region hS hD hBdU hEmpty
  have hsubBd_r₀ : subBd r₀ = discBd E₀ := by
    rw [subBd_eq_frontier]
    have hfr_eq : frontier r₀ = frontier (closure E₀ᶜ) := by
      rw [frontier, frontier, hcl_r₀, interior_interior, closure_closure]
    rw [hfr_eq, GM11.IsClosedDisc.frontier_eq_discBd hS hD, hBd]
  have hOArc : IsOArc (discBd E₀) := hC.isOArc_discBd
  have hBdU' : discBd E₀ ⊆ Γ.drawing.U := hBd ▸ hBdU
  obtain ⟨C₀, hC₀_circ, hC₀_sub, hC₀_U⟩ := GM11.exists_circuit_of_oArc hOArc hBdU'
  have hC₀_V : C₀.V = discBd E₀ ∩ Γ.drawing.V :=
    subdrawing_V_eq_inter_of_U_eq hC₀_sub hC₀_U
  have hmem_V : ∀ v ∈ V(W.graph), fig1Sph φ (pos v) ∈ C₀.V ↔ v ∈ V(W.perimeter) := by
    intro v hv
    have hpt_V : fig1Sph φ (pos v) ∈ Γ.drawing.V := by
      have := (Γ.iso.vertexEquiv ⟨v, hv⟩).2
      rwa [hΓv] at this
    rw [hC₀_V, mem_inter_iff, and_iff_left hpt_V,
      ← GM11.IsClosedDisc.frontier_eq_discBd hS hC,
      mem_perimeter_iff_pos_not_mem_interior hinj hpos_branch hΓv hΓe hv]
    have hpos_E₀ : fig1Sph φ (pos v) ∈ E₀ :=
      ⟨pos v, fig1Set_subset_enclosed he hh2 (hpos v hv), rfl⟩
    have hcl_E₀ : closure E₀ = E₀ := hC.isCompact.isClosed.closure_eq
    have hint_E₀ : interior E₀ = fig1Sph φ '' interior (fig1EnclosedSet W.height) :=
      interior_image_eq_of_isOpenEmbedding hf_open (fig1EnclosedSet W.height)
    rw [frontier, hcl_E₀, hint_E₀, mem_sdiff, and_iff_right hpos_E₀]
    constructor
    · intro hnot hz
      exact hnot ⟨pos v, hz, rfl⟩
    · rintro hnot ⟨z, hz, hzeq⟩
      obtain rfl : z = pos v := hf_open.injective hzeq
      exact hnot hz
  have hmem_x : ∀ x ∈ Γ.drawing.V, x ∈ C₀.V ↔ drawingVertToGraph Γ x ∈ V(W.perimeter) := by
    intro x hx
    obtain ⟨⟨v, hv⟩, hv_eq⟩ := Γ.iso.vertexEquiv.surjective ⟨x, hx⟩
    have hval : (Γ.iso.vertexEquiv ⟨v, hv⟩).1 = x := congrArg Subtype.val hv_eq
    have hx_eq : x = fig1Sph φ (pos v) := hval.symm.trans (hΓv ⟨v, hv⟩)
    have hdraw_eq : drawingVertToGraph Γ (fig1Sph φ (pos v)) = v := by
      rw [← hx_eq, ← hval, drawingVertToGraph_apply_vertexEquiv]
    rw [hx_eq, hdraw_eq]
    exact hmem_V v hv
  refine ⟨C₀, ⟨hC₀_sub, hC₀_circ, hr₀_R, hsubBd_r₀.trans hC₀_U.symm⟩,
    hC₀_U, hcl_r₀, hmem_V, hmem_x, ?_⟩
  ext u
  simp only [mem_image]
  constructor
  · rintro ⟨x, hxC₀, rfl⟩
    exact (hmem_x x (hC₀_sub.1 hxC₀)).mp hxC₀
  · intro hu_perim
    have hu_W : u ∈ V(W.graph) := W.toWall.perimeter_le.vertexSet_mono hu_perim
    refine ⟨fig1Sph φ (pos u), (hmem_V u hu_W).mpr hu_perim, ?_⟩
    have h1 := drawingVertToGraph_apply_vertexEquiv Γ ⟨u, hu_W⟩
    rwa [hΓv ⟨u, hu_W⟩] at h1

/-- The four corners `W.corner k` of a wall `W` belong to `V(W.perimeter)`. -/
theorem corner_mem_perimeter {α : Type u} {β : Type v} (W : Wall α β) (k : Fin 4) :
    W.corner k ∈ V(W.perimeter) := by
  have hp : elementaryWallCorner W.height k ∈ elementaryWallPerimeterVerts W.height := by
    have h2 := W.two_le_height
    fin_cases k <;> simp [elementaryWallCorner, elementaryWallPerimeterVerts,
      elementaryWallVerts] <;> omega
  exact branchVertex_mem_perimeter_of_mem_perimeterVerts W hp

/-- The set `PiSet` of the four drawn corners in the sphere drawing `Γ`. -/
def wallPiSet {α : Type u} {β : Type v} (W : Wall α β)
    (φ : EuclideanPlane ≃ₜ EuclideanPlane) (pos : α → ℝ × ℝ) :
    Set (OnePoint EuclideanPlane) :=
  Set.range (fun k : Fin 4 => fig1Sph φ (pos (W.corner k)))

/-- Properties of `wallPiSet`: `wallPiSet ⊆ C₀.V`, `wallPiSet.ncard = 4`, and
`drawingVertToGraph Γ '' wallPiSet = W.corners`. -/
theorem wallPiSet_props {α : Type u} {β : Type v} [Nonempty α]
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    {C₀ : Drawing (OnePoint EuclideanPlane)}
    (hinj : InjOn pos V(W.graph))
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hmem_V : ∀ v ∈ V(W.graph), fig1Sph φ (pos v) ∈ C₀.V ↔ v ∈ V(W.perimeter)) :
    wallPiSet W.toWall φ pos ⊆ C₀.V ∧
    (wallPiSet W.toWall φ pos).ncard = 4 ∧
    (∀ k : Fin 4,
      drawingVertToGraph Γ (fig1Sph φ (pos (W.toWall.corner k))) = W.toWall.corner k) ∧
    drawingVertToGraph Γ '' wallPiSet W.toWall φ pos = W.toWall.corners := by
  have hcorner_W : ∀ k : Fin 4, W.toWall.corner k ∈ V(W.graph) :=
    fun k => W.toWall.perimeter_le.vertexSet_mono (corner_mem_perimeter W.toWall k)
  have hsub : wallPiSet W.toWall φ pos ⊆ C₀.V := by
    rintro _ ⟨k, rfl⟩
    exact (hmem_V (W.toWall.corner k) (hcorner_W k)).mpr (corner_mem_perimeter W.toWall k)
  have hinj_k : Function.Injective (fun k : Fin 4 => fig1Sph φ (pos (W.toWall.corner k))) := by
    intro i j hij
    have hpos_ij : pos (W.toWall.corner i) = pos (W.toWall.corner j) :=
      (isOpenEmbedding_fig1Sph φ).injective hij
    have hcorner_ij : W.toWall.corner i = W.toWall.corner j :=
      hinj (hcorner_W i) (hcorner_W j) hpos_ij
    exact W.toWall.corner_injective hcorner_ij
  have hncard : (wallPiSet W.toWall φ pos).ncard = 4 := by
    unfold wallPiSet
    rw [ncard_range_of_injective hinj_k, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hdraw_k : ∀ k : Fin 4,
      drawingVertToGraph Γ (fig1Sph φ (pos (W.toWall.corner k))) = W.toWall.corner k := by
    intro k
    have h1 := drawingVertToGraph_apply_vertexEquiv Γ ⟨W.toWall.corner k, hcorner_W k⟩
    rwa [hΓv ⟨W.toWall.corner k, hcorner_W k⟩] at h1
  refine ⟨hsub, hncard, hdraw_k, ?_⟩
  ext u
  simp only [wallPiSet, Wall.corners, mem_image, mem_range]
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, (hdraw_k k).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨fig1Sph φ (pos (W.toWall.corner k)), ⟨k, rfl⟩, hdraw_k k⟩

/-! ## 2. Lifting Elementary Wall Sets (`liftElemSet`) and `hyp_iv` -/

/-- The lift of a coordinate set `C ⊆ ℕ × ℕ` to a vertex subset of `W.graph`: the branch vertices
of points in `C`, together with the vertices of subdivision paths of edges with both ends in `C`. -/
def liftElemSet {α : Type u} {β : Type v} (W : Wall α β) (C : Set (ℕ × ℕ)) : Set α :=
  {x : α |
    (∃ p ∈ C, ∃ hp : p ∈ elementaryWallVerts W.height, x = W.branchVertex p hp) ∨
    (∃ p ∈ C, ∃ q ∈ C, ∃ hadj : elementaryWallAdj W.height p q,
      x ∈ V(W.subdivisionPaths (W.baseEdge hadj)))}

theorem liftElemSet_subset_vertexSet {α : Type u} {β : Type v} (W : Wall α β) (C : Set (ℕ × ℕ)) :
    liftElemSet W C ⊆ V(W.graph) := by
  rintro x (⟨p, _, hp, rfl⟩ | ⟨p, _, q, _, hadj, hx⟩)
  · exact W.branchVertex_mem_graph p hp
  · exact (W.isGraphPathWithEnds_baseEdge hadj).le.vertexSet_mono hx

theorem branchVertex_mem_liftElemSet {α : Type u} {β : Type v} (W : Wall α β) {C : Set (ℕ × ℕ)}
    {p : ℕ × ℕ} (hpC : p ∈ C) (hp : p ∈ elementaryWallVerts W.height) :
    W.branchVertex p hp ∈ liftElemSet W C :=
  Or.inl ⟨p, hpC, hp, rfl⟩

theorem subdivisionPath_subset_liftElemSet {α : Type u} {β : Type v} (W : Wall α β)
    {C : Set (ℕ × ℕ)} {p q : ℕ × ℕ} (hpC : p ∈ C) (hqC : q ∈ C)
    (hadj : elementaryWallAdj W.height p q) :
    V(W.subdivisionPaths (W.baseEdge hadj)) ⊆ liftElemSet W C :=
  fun _ hx => Or.inr ⟨p, hpC, q, hqC, hadj, hx⟩

/-- Disjoint subsets `C₁, C₂ ⊆ ℕ × ℕ` lift to disjoint vertex subsets of `W.graph`. -/
theorem disjoint_liftElemSet {α : Type u} {β : Type v} (W : Wall α β) {C₁ C₂ : Set (ℕ × ℕ)}
    (hdisj : Disjoint C₁ C₂) :
    Disjoint (liftElemSet W C₁) (liftElemSet W C₂) := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  have hmem_C : ∀ {C : Set (ℕ × ℕ)}, x ∈ liftElemSet W C → x ∈ V(W.baseGraph) →
      ∃ p ∈ C, ∃ hp : p ∈ elementaryWallVerts W.height, x = W.branchVertex p hp := by
    rintro C (⟨p, hpC, hp, rfl⟩ | ⟨p, hpC, q, hqC, hadj, hxP⟩) hxB
    · exact ⟨p, hpC, hp, rfl⟩
    · have hx_ends : x ∈ ({W.branchVertex p hadj.1, W.branchVertex q hadj.2.1} : Set α) := by
        rw [← W.vertexSet_baseEdge_inter hadj]
        exact ⟨hxP, hxB⟩
      rcases hx_ends with rfl | rfl
      · exact ⟨p, hpC, hadj.1, rfl⟩
      · exact ⟨q, hqC, hadj.2.1, rfl⟩
  by_cases hxB : x ∈ V(W.baseGraph)
  · obtain ⟨p₁, hp₁C, hp₁, hxeq₁⟩ := hmem_C hx₁ hxB
    obtain ⟨p₂, hp₂C, hp₂, hxeq₂⟩ := hmem_C hx₂ hxB
    have hp_eq : p₁ = p₂ := W.branchVertex_injective hp₁ hp₂ (hxeq₁.symm.trans hxeq₂)
    exact Set.disjoint_left.mp hdisj hp₁C (hp_eq ▸ hp₂C)
  · rcases hx₁ with ⟨p₁, _, hp₁, rfl⟩ | ⟨p₁, hp₁C, q₁, hq₁C, hadj₁, hxP₁⟩
    · exact hxB (W.branchVertex_mem_baseGraph p₁ hp₁)
    · rcases hx₂ with ⟨p₂, _, hp₂, rfl⟩ | ⟨p₂, hp₂C, q₂, _, hadj₂, hxP₂⟩
      · exact hxB (W.branchVertex_mem_baseGraph p₂ hp₂)
      · have hne : s(p₁, q₁) ≠ s(p₂, q₂) := by
          intro heq
          rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Set.disjoint_left.mp hdisj hp₁C hp₂C
          · exact Set.disjoint_left.mp hdisj hq₁C hp₂C
        exact hxB ((W.baseEdge_paths_disjoint hadj₁ hadj₂ hne).2 ⟨hxP₁, hxP₂⟩)

/-- A walk in `P` whose vertex set `V(P)` is disjoint from `X_G` induces a walk in
`G.deleteVerts X_G` when `P ≤ G`. -/
theorem exists_walk_deleteVerts_of_isGraphPathWithEnds {α : Type u} {β : Type v}
    {G P : Graph α β} {u v : α} {X_G : Set α}
    (hP : IsGraphPathWithEnds G P u v) (hdisj : Disjoint V(P) X_G) :
    Nonempty (GraphWalk (G.deleteVerts X_G) u v) := by
  have hle : P ≤ G.deleteVerts X_G := by
    refine ⟨fun x hx => ?_, fun e x y hl => ?_⟩
    · rw [Graph.vertexSet_deleteVerts]
      exact ⟨hP.1.vertexSet_mono hx, Set.disjoint_left.mp hdisj hx⟩
    · rw [Graph.deleteVerts_isLink]
      exact ⟨hl.mono hP.1, Set.disjoint_left.mp hdisj hl.left_mem,
        Set.disjoint_left.mp hdisj hl.right_mem⟩
  obtain ⟨_, w, _, _, _⟩ := hP
  let rec hmono {x y : α} : GraphWalk P x y → GraphWalk (G.deleteVerts X_G) x y
    | .nil hx => .nil (hle.vertexSet_mono hx)
    | .cons hl rest => .cons (hl.mono hle) (hmono rest)
  exact ⟨hmono w⟩

/-- If `IsElemWallConn W.height C`, `p, q ∈ C`, and `Disjoint (liftElemSet W C) X_G`, then there is
a walk in `W.graph.deleteVerts X_G` from `W.branchVertex p hp` to `W.branchVertex q hq`. -/
theorem exists_walk_in_liftElemSet {α : Type u} {β : Type v} (W : Wall α β)
    {C : Set (ℕ × ℕ)} {X_G : Set α} (hdisj : Disjoint (liftElemSet W C) X_G)
    {p q : ℕ × ℕ} (hp : p ∈ elementaryWallVerts W.height)
    (hq : q ∈ elementaryWallVerts W.height)
    (hconn : IsElemWallConn W.height C) (hpC : p ∈ C) (hqC : q ∈ C) :
    Nonempty (GraphWalk (W.graph.deleteVerts X_G) (W.branchVertex p hp) (W.branchVertex q hq)) := by
  obtain ⟨w, hsupp⟩ := hconn.2 p hpC q hqC
  have hwalk : ∀ {a b : ℕ × ℕ} (w₀ : GraphWalk (elementaryWall W.height) a b),
      (∀ z ∈ w₀.support, z ∈ C) →
      ∀ (ha : a ∈ elementaryWallVerts W.height) (hb : b ∈ elementaryWallVerts W.height),
        Nonempty (GraphWalk (W.graph.deleteVerts X_G)
          (W.branchVertex a ha) (W.branchVertex b hb)) := by
    intro a b w₀
    induction w₀ with
    | @nil a ha' =>
      intro hsupp₀ ha _
      have haC : a ∈ C := hsupp₀ a (by simp [GraphWalk.support])
      have ha_mem : W.branchVertex a ha ∈ V(W.graph.deleteVerts X_G) := by
        rw [Graph.vertexSet_deleteVerts]
        exact ⟨W.branchVertex_mem_graph a ha,
          Set.disjoint_left.mp hdisj (branchVertex_mem_liftElemSet W haC ha)⟩
      exact ⟨GraphWalk.nil ha_mem⟩
    | @cons a a₁ b e hl rest ih =>
      intro hsupp₀ ha hb
      have haC : a ∈ C := hsupp₀ a (by simp [GraphWalk.support])
      have ha₁C : a₁ ∈ C := hsupp₀ a₁ (by
        simp [GraphWalk.support, Surface.GraphWalk.start_mem_support])
      have hadj : elementaryWallAdj W.height a a₁ := hl.1
      have hP := W.isGraphPathWithEnds_baseEdge hadj
      have hP_disj : Disjoint V(W.subdivisionPaths (W.baseEdge hadj)) X_G :=
        hdisj.mono_left (subdivisionPath_subset_liftElemSet W haC ha₁C hadj)
      obtain ⟨w₁⟩ := exists_walk_deleteVerts_of_isGraphPathWithEnds hP hP_disj
      obtain ⟨w₂⟩ := ih (fun z hz => hsupp₀ z (by simp [GraphWalk.support, hz])) hadj.2.1 hb
      exact ⟨w₁.append w₂⟩
  exact hwalk w hsupp hp hq

/-- Four pairwise disjoint coordinate sets connecting the four corners `elementaryWallCorner h k`
to four points on `elemRow h j₀` (for `j₀ < h`). -/
def cornerToRowSet (h j₀ : ℕ) (k : Fin 4) : Set (ℕ × ℕ) :=
  if k.1 = 0 then elemStripUpTo h 0 j₀
  else if k.1 = 1 then elemRowInterval h h 0 1 ∪ elemStrip h 1
  else if k.1 = 2 then {(2 * h, h)} ∪ elemStrip h (h - 1)
  else elemStripUpTo h h j₀

/-- The target point on `elemRow h j₀` reached by `cornerToRowSet h j₀ k`. -/
def cornerToRowTarget (h j₀ : ℕ) (k : Fin 4) : ℕ × ℕ :=
  if k.1 = 0 then (1, j₀)
  else if k.1 = 1 then (2, j₀)
  else if k.1 = 2 then (2 * h - 1, j₀)
  else (2 * h + 1, j₀)

theorem cornerToRowTarget_mem_elemRow {h j₀ : ℕ} (hh : 2 ≤ h) (hj₀ : j₀ < h) (k : Fin 4) :
    cornerToRowTarget h j₀ k ∈ elemRow h j₀ ∧
    cornerToRowTarget h j₀ k ∈ elementaryWallVerts h ∧
    elementaryWallCorner h k ∈ cornerToRowSet h j₀ k ∧
    cornerToRowTarget h j₀ k ∈ cornerToRowSet h j₀ k := by
  rcases k with ⟨k, hk⟩
  interval_cases k <;>
    simp [cornerToRowTarget, cornerToRowSet, elementaryWallCorner, elemRow, elemRowInterval,
      elemStripUpTo, elemStrip, elementaryWallVerts] <;> omega

/-- For `h ≥ 4` even and `j₀ < h`, the four sets `cornerToRowSet h j₀ k` are pairwise disjoint. -/
theorem pairwise_disjoint_cornerToRowSet {h j₀ : ℕ} (hh : 4 ≤ h) (hj₀ : j₀ < h) :
    Pairwise (fun k₁ k₂ : Fin 4 => Disjoint (cornerToRowSet h j₀ k₁) (cornerToRowSet h j₀ k₂)) := by
  rintro ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ hne
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ hp₁ hp₂
  interval_cases k₁ <;> interval_cases k₂ <;> try exact (hne rfl).elim
  all_goals
    simp [cornerToRowSet, elemRowInterval, elemStripUpTo, elemStrip] at hp₁ hp₂
    omega

/-- For `h ≥ 4` even and `j₀ < h`, each `cornerToRowSet h j₀ k` is walk-connected in
`elementaryWall h`. -/
theorem isElemWallConn_cornerToRowSet {h j₀ : ℕ} (hh : 4 ≤ h) (he : Even h) (hj₀ : j₀ < h)
    (k : Fin 4) :
    IsElemWallConn h (cornerToRowSet h j₀ k) := by
  have hh2 : 2 ≤ h := by omega
  fin_cases k
  · -- k = 0: `elemStripUpTo h 0 j₀`
    simpa [cornerToRowSet] using
      isElemWallConn_elemStripUpTo hh2 he (k := 0) (by omega) j₀ (by omega)
  · -- k = 1: `elemRowInterval h h 0 1 ∪ elemStrip h 1`
    change IsElemWallConn h (elemRowInterval h h 0 1 ∪ elemStrip h 1)
    have hrow01 : IsElemWallConn h (elemRowInterval h h 0 1) :=
      isElemWallConn_elemRowInterval le_rfl (by omega) (by omega) (by omega) (by omega)
    have hstrip1 : IsElemWallConn h (elemStrip h 1) :=
      isElemWallConn_elemStrip hh2 he (by omega)
    have h1h : (1, h) ∈ elementaryWallVerts h :=
      ⟨by omega, le_rfl, by intro h0; injection h0; omega, by intro h0; injection h0; omega⟩
    have h2h : (2, h) ∈ elementaryWallVerts h :=
      ⟨by omega, le_rfl, by intro h0; injection h0; omega, by intro h0; injection h0; omega⟩
    have hadj : elementaryWallAdj h (1, h) (2, h) :=
      ⟨h1h, h2h, Or.inl ⟨rfl, Or.inl rfl⟩⟩
    exact hrow01.union_of_adj hstrip1 ⟨h1h, rfl, by omega, le_rfl⟩ ⟨h2h, Or.inl rfl⟩ hadj
  · -- k = 2: `{(2 * h, h)} ∪ elemStrip h (h - 1)`
    change IsElemWallConn h ({(2 * h, h)} ∪ elemStrip h (h - 1))
    have h2hh : (2 * h, h) ∈ elementaryWallVerts h :=
      ⟨by omega, le_rfl, by intro h0; injection h0; omega, by intro h0; injection h0; omega⟩
    have h2hm1 : (2 * h - 1, h) ∈ elementaryWallVerts h :=
      ⟨by omega, le_rfl, by intro h0; injection h0; omega, by intro h0; injection h0; omega⟩
    have hsing : IsElemWallConn h {(2 * h, h)} := isElemWallConn_singleton h2hh
    have hstrip : IsElemWallConn h (elemStrip h (h - 1)) :=
      isElemWallConn_elemStrip hh2 he (by omega)
    have hadj : elementaryWallAdj h (2 * h, h) (2 * h - 1, h) :=
      ⟨h2hh, h2hm1, Or.inl ⟨rfl, Or.inr (by omega)⟩⟩
    exact hsing.union_of_adj hstrip rfl ⟨h2hm1, Or.inr (by omega)⟩ hadj
  · -- k = 3: `elemStripUpTo h h j₀`
    simpa [cornerToRowSet] using
      isElemWallConn_elemStripUpTo hh2 he (k := h) le_rfl j₀ (by omega)

/-- If `X` is a finite set with `X.ncard ≤ 3`, `f` is injective on `V`, and `F : Fin 4 → Set α`
are pairwise disjoint subsets of `V`, then some `F i` is disjoint from `{z ∈ V | f z ∈ X}`. -/
theorem exists_disjoint_preimage_of_ncard_le_three {α S : Type*} {f : α → S} {V : Set α}
    (hinj : InjOn f V) {X : Set S} (hXfin : X.Finite) (hX : X.ncard ≤ 3)
    {F : Fin 4 → Set α} (hFV : ∀ i, F i ⊆ V)
    (hdisj : Pairwise (fun i j => Disjoint (F i) (F j))) :
    ∃ i : Fin 4, Disjoint (F i) {z ∈ V | f z ∈ X} := by
  by_contra hno
  push Not at hno
  choose x hx using fun i : Fin 4 => Set.not_disjoint_iff.mp (hno i)
  have hinj_fx : Function.Injective (fun i : Fin 4 => f (x i)) := by
    intro i j hij
    have hxi_eq : x i = x j := hinj (hFV i (hx i).1) (hFV j (hx j).1) hij
    by_contra hne
    exact Set.disjoint_left.mp (hdisj hne) (hx i).1 (hxi_eq ▸ (hx j).1)
  have hrange : Set.range (fun i : Fin 4 => f (x i)) ⊆ X := by
    rintro _ ⟨i, rfl⟩
    exact (hx i).2.2
  have hcard1 : (Set.range (fun i : Fin 4 => f (x i))).ncard = 4 := by
    rw [ncard_range_of_injective hinj_fx, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hcard2 : (Set.range (fun i : Fin 4 => f (x i))).ncard ≤ X.ncard :=
    ncard_le_ncard hrange hXfin
  omega

/-- If `(A, B)` is a separation of `Γ.drawing.toHypergraph`, `u, v ∈ V(W.graph)` are joined by a
walk in `W.graph.deleteVerts {z ∈ V(W.graph) | pt z ∈ A.vertexSet ∩ B.vertexSet}`, and
`pt u ∈ A.vertexSet`, then `pt v ∈ A.vertexSet \ B.vertexSet`. -/
theorem mem_A_of_walk_deleteVerts_sep {α : Type u} {β : Type v}
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    {A B : Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane))}
    (hsep : Γ.drawing.toHypergraph.IsSeparation A B)
    {u v : α}
    (w : GraphWalk (W.graph.deleteVerts
      {z ∈ V(W.graph) | fig1Sph φ (pos z) ∈ A.vertexSet ∩ B.vertexSet}) u v)
    (huA : fig1Sph φ (pos u) ∈ A.vertexSet) :
    fig1Sph φ (pos v) ∈ A.vertexSet \ B.vertexSet := by
  induction w with
  | nil hu_del =>
    rw [Graph.vertexSet_deleteVerts] at hu_del
    exact ⟨huA, fun huB => hu_del.2 ⟨hu_del.1, huA, huB⟩⟩
  | @cons a a₁ b e hl rest ih =>
    have ha_del : a ∈ V(W.graph) \ _ := W.graph.vertexSet_deleteVerts _ ▸ hl.left_mem
    have ha_not_B : fig1Sph φ (pos a) ∉ B.vertexSet :=
      fun haB => ha_del.2 ⟨ha_del.1, huA, haB⟩
    have hl_W : W.graph.IsLink e a a₁ := hl.mono Graph.deleteVerts_le
    have he_W : e ∈ E(W.graph) := hl_W.edge_mem
    have ha_W : a ∈ V(W.graph) := hl_W.left_mem
    have ha₁_W : a₁ ∈ V(W.graph) := hl_W.right_mem
    have hl_Γ : Γ.drawing.toGraph.IsLink (Γ.iso.edgeEquiv ⟨e, he_W⟩).1
        (fig1Sph φ (pos a)) (fig1Sph φ (pos a₁)) := by
      have h1 := (Γ.iso.isLink_iff ⟨e, he_W⟩ ⟨a, ha_W⟩ ⟨a₁, ha₁_W⟩).mp hl_W
      rwa [hΓv ⟨a, ha_W⟩, hΓv ⟨a₁, ha₁_W⟩] at h1
    set e_S := (Γ.iso.edgeEquiv ⟨e, he_W⟩).1
    have he_S : e_S ∈ Γ.drawing.toHypergraph.edgeSet := (Γ.iso.edgeEquiv ⟨e, he_W⟩).2
    have ha_V : fig1Sph φ (pos a) ∈ Γ.drawing.V := by
      have h := (Γ.iso.vertexEquiv ⟨a, ha_W⟩).2
      rwa [hΓv] at h
    have ha₁_V : fig1Sph φ (pos a₁) ∈ Γ.drawing.V := by
      have h := (Γ.iso.vertexEquiv ⟨a₁, ha₁_W⟩).2
      rwa [hΓv] at h
    have ha_ends : fig1Sph φ (pos a) ∈ Γ.drawing.toHypergraph.ends e_S := by
      refine ⟨he_S, ha_V, ?_⟩
      have : fig1Sph φ (pos a) ∈ closure e_S ∩ Γ.drawing.V := by
        rw [hl_Γ.2.2.2]; exact Or.inl rfl
      exact this.1
    have ha₁_ends : fig1Sph φ (pos a₁) ∈ Γ.drawing.toHypergraph.ends e_S := by
      refine ⟨he_S, ha₁_V, ?_⟩
      have : fig1Sph φ (pos a₁) ∈ closure e_S ∩ Γ.drawing.V := by
        rw [hl_Γ.2.2.2]; exact Or.inr rfl
      exact this.1
    have he_AB : e_S ∈ A.edgeSet ∪ B.edgeSet := by
      change e_S ∈ (A ∪ B).edgeSet
      rwa [hsep.union_eq]
    rcases he_AB with heA | heB
    · have ha₁_A : fig1Sph φ (pos a₁) ∈ A.vertexSet :=
        A.vertex_mem_of_inc ((Set.ext_iff.mp (hsep.left_le.ends_eq e_S heA) _).mp ha₁_ends)
      exact ih ha₁_A
    · exfalso
      have ha_B : fig1Sph φ (pos a) ∈ B.vertexSet :=
        B.vertex_mem_of_inc ((Set.ext_iff.mp (hsep.right_le.ends_eq e_S heB) _).mp ha_ends)
      exact ha_not_B ha_B

/-- In the wall tangle `T` of a Fig. 1 sphere drawing `Γ` of `W` (with `4 ≤ W.height`), no
separation `(A, B) ∈ T` of order `≤ 3` satisfies `wallPiSet W.toWall φ pos ⊆ A.vertexSet`. -/
theorem tangle_no_order_le_three_corners {α : Type u} {β : Type v} [Nonempty β]
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hh4 : 4 ≤ W.height)
    (hinj : InjOn pos V(W.graph))
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    {T : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
      Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)))}
    (hT : GM10.IsTangle Γ.drawing.toHypergraph W.height T)
    (hrow : ∀ A B, (A, B) ∈ T → ∀ j : Fin W.height,
      ∃ e ∈ E(GM16.sphereWallRow W.height j), ∃ (f : β) (hf : f ∈ E(W.graph)),
        f ∈ E(W.subdivisionPaths (W.sphereEdge e)) ∧ (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ∉ A.edgeSet) :
    ∀ A B, (A, B) ∈ T → separationOrder A B ≤ 3 →
      ¬ (wallPiSet W.toWall φ pos ⊆ A.vertexSet) := by
  intro A B hAB hord hPi_sub
  have hsep : Γ.drawing.toHypergraph.IsSeparation A B := hT.isSeparation hAB
  set X_S := A.vertexSet ∩ B.vertexSet
  set X_G := {z ∈ V(W.graph) | fig1Sph φ (pos z) ∈ X_S}
  have hinj_pt : InjOn (fun z => fig1Sph φ (pos z)) V(W.graph) := by
    intro x hx y hy hxy
    exact hinj hx hy ((isOpenEmbedding_fig1Sph φ).injective hxy)
  have hXS_fin : X_S.Finite :=
    Γ.drawing.finite_V.subset ((inter_subset_left).trans hsep.left_le.vertexSet_subset)
  have hXS_card : X_S.ncard ≤ 3 := hord
  -- 1. Find a row `j₀ < 4` whose lifted set in `W.graph` is disjoint from `X_G`
  have hrow_disj : Pairwise (fun i j : Fin 4 =>
      Disjoint (liftElemSet W.toWall (elemRow W.height i.1))
        (liftElemSet W.toWall (elemRow W.height j.1))) :=
    fun i j hij => disjoint_liftElemSet W.toWall
      (Set.disjoint_left.mpr fun p hp₁ hp₂ => Fin.val_ne_of_ne hij (hp₁.2.symm.trans hp₂.2))
  obtain ⟨j₀, hj₀_disj⟩ := exists_disjoint_preimage_of_ncard_le_three hinj_pt hXS_fin hXS_card
    (fun i => liftElemSet_subset_vertexSet W.toWall _) hrow_disj
  have hj₀_lt : j₀.1 < W.height := by omega
  -- 2. By `hrow`, some subdivision path edge on row `j₀` is not in `A.edgeSet`
  obtain ⟨e_row, he_row, f, hf_W, hf_P, hf_not_A⟩ := hrow A B hAB ⟨j₀.1, hj₀_lt⟩
  obtain ⟨a₁, b₁, ⟨rfl, hadjE⟩, ha₁_j, hb₁_j⟩ := he_row
  have hadj_sph : (GM16.sphereWallSimpleGraph W.height).Adj a₁ b₁ := hadjE
  have hadj_elem : elementaryWallAdj W.height (sphereToWall a₁) (sphereToWall b₁) :=
    sphereToWall_adj hadj_sph
  rw [W.toWall.sphereEdge_mk hadj_elem] at hf_P
  have ha₁_row : sphereToWall a₁ ∈ elemRow W.height j₀.1 :=
    ⟨hadj_elem.1, congrArg Fin.val ha₁_j⟩
  have hb₁_row : sphereToWall b₁ ∈ elemRow W.height j₀.1 :=
    ⟨hadj_elem.2.1, congrArg Fin.val hb₁_j⟩
  -- The edge `f` has ends `u_f, v_f` in `W.subdivisionPaths (W.baseEdge hadj_elem)`
  obtain ⟨u_f, v_f, hlink_P⟩ :=
    (W.toWall.subdivisionPaths (W.toWall.baseEdge hadj_elem)).exists_isLink_of_mem_edgeSet hf_P
  have hP_path := W.toWall.isGraphPathWithEnds_baseEdge hadj_elem
  have hlink_W : W.graph.IsLink f u_f v_f := hlink_P.mono hP_path.1
  have hu_f_W : u_f ∈ V(W.graph) := hlink_W.left_mem
  have hv_f_W : v_f ∈ V(W.graph) := hlink_W.right_mem
  set f_S := (Γ.iso.edgeEquiv ⟨f, hf_W⟩).1
  have hf_S_E : f_S ∈ Γ.drawing.toHypergraph.edgeSet := (Γ.iso.edgeEquiv ⟨f, hf_W⟩).2
  have hf_S_AB : f_S ∈ A.edgeSet ∪ B.edgeSet := by
    change f_S ∈ (A ∪ B).edgeSet
    rwa [hsep.union_eq]
  have hf_S_B : f_S ∈ B.edgeSet := hf_S_AB.resolve_left hf_not_A
  have hlink_Γ : Γ.drawing.toGraph.IsLink f_S
      (fig1Sph φ (pos u_f)) (fig1Sph φ (pos v_f)) := by
    have h1 := (Γ.iso.isLink_iff ⟨f, hf_W⟩ ⟨u_f, hu_f_W⟩ ⟨v_f, hv_f_W⟩).mp hlink_W
    rwa [hΓv ⟨u_f, hu_f_W⟩, hΓv ⟨v_f, hv_f_W⟩] at h1
  have hu_f_B : fig1Sph φ (pos u_f) ∈ B.vertexSet := by
    have hu_f_V : fig1Sph φ (pos u_f) ∈ Γ.drawing.V := by
      have h := (Γ.iso.vertexEquiv ⟨u_f, hu_f_W⟩).2
      rwa [hΓv] at h
    have hends : fig1Sph φ (pos u_f) ∈ Γ.drawing.toHypergraph.ends f_S := by
      refine ⟨hf_S_E, hu_f_V, ?_⟩
      have : fig1Sph φ (pos u_f) ∈ closure f_S ∩ Γ.drawing.V := by
        rw [hlink_Γ.2.2.2]; exact Or.inl rfl
      exact this.1
    exact B.vertex_mem_of_inc ((Set.ext_iff.mp (hsep.right_le.ends_eq f_S hf_S_B) _).mp hends)
  -- 3. `u_f` is connected in `W.graph.deleteVerts X_G` to `W.branchVertex (sphereToWall a₁)`
  have hP_sub_row : V(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj_elem)) ⊆
      liftElemSet W.toWall (elemRow W.height j₀.1) :=
    subdivisionPath_subset_liftElemSet W.toWall ha₁_row hb₁_row hadj_elem
  have hP_disj_XG : Disjoint V(W.toWall.subdivisionPaths (W.toWall.baseEdge hadj_elem)) X_G :=
    hj₀_disj.mono_left hP_sub_row
  -- Any walk in `P` from `W.branchVertex (sphereToWall a₁)` to `u_f`
  obtain ⟨hle_PW, w_P, _, hsupp_P, _⟩ := hP_path
  have hu_f_supp : u_f ∈ w_P.support := (Set.ext_iff.mp hsupp_P u_f).mp hlink_P.left_mem
  have hle_P_del : W.toWall.subdivisionPaths (W.toWall.baseEdge hadj_elem) ≤
      W.graph.deleteVerts X_G := by
    refine ⟨fun x hx => ?_, fun e x y hl => ?_⟩
    · rw [Graph.vertexSet_deleteVerts]
      exact ⟨hle_PW.vertexSet_mono hx, Set.disjoint_left.mp hP_disj_XG hx⟩
    · rw [Graph.deleteVerts_isLink]
      exact ⟨hl.mono hle_PW, Set.disjoint_left.mp hP_disj_XG hl.left_mem,
        Set.disjoint_left.mp hP_disj_XG hl.right_mem⟩
  have hw_a₁_uf : Nonempty (GraphWalk (W.graph.deleteVerts X_G)
      (W.branchVertex (sphereToWall a₁) hadj_elem.1) u_f) := by
    have hreach : ∀ {x y : α} (w₀ : GraphWalk
        (W.toWall.subdivisionPaths (W.toWall.baseEdge hadj_elem)) x y),
        ∀ z ∈ w₀.support, Nonempty (GraphWalk (W.graph.deleteVerts X_G) x z) := by
      intro x y w₀
      induction w₀ with
      | nil hx =>
        intro z hz
        simp only [GraphWalk.support, List.mem_singleton] at hz
        subst hz
        exact ⟨GraphWalk.nil (hle_P_del.vertexSet_mono hx)⟩
      | @cons x x₁ y e₀ hl₀ rest₀ ih₀ =>
        intro z hz
        simp only [GraphWalk.support, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact ⟨GraphWalk.nil (hle_P_del.vertexSet_mono hl₀.left_mem)⟩
        · obtain ⟨w_z⟩ := ih₀ z hz
          exact ⟨GraphWalk.cons (hl₀.mono hle_P_del) w_z⟩
    exact hreach w_P u_f hu_f_supp
  -- 4. Find a `k : Fin 4` whose `cornerToRowSet W.height j₀.1 k` has lift disjoint from `X_G`
  have hcorner_disj : Pairwise (fun k₁ k₂ : Fin 4 =>
      Disjoint (liftElemSet W.toWall (cornerToRowSet W.height j₀.1 k₁))
        (liftElemSet W.toWall (cornerToRowSet W.height j₀.1 k₂))) :=
    fun k₁ k₂ hne => disjoint_liftElemSet W.toWall (pairwise_disjoint_cornerToRowSet hh4 hj₀_lt hne)
  obtain ⟨k, hk_disj⟩ := exists_disjoint_preimage_of_ncard_le_three hinj_pt hXS_fin hXS_card
    (fun i => liftElemSet_subset_vertexSet W.toWall _) hcorner_disj
  have htarget := cornerToRowTarget_mem_elemRow W.toWall.two_le_height hj₀_lt k
  have hcorner_vert : elementaryWallCorner W.height k ∈ elementaryWallVerts W.height := by
    have h2 := W.toWall.two_le_height
    fin_cases k <;> simp [elementaryWallCorner, elementaryWallVerts] <;> omega
  -- Walk from `W.corner k` to `W.branchVertex (cornerToRowTarget W.height j₀.1 k)`
  obtain ⟨w_corner_target⟩ := exists_walk_in_liftElemSet W.toWall hk_disj hcorner_vert htarget.2.1
    (isElemWallConn_cornerToRowSet hh4 W.toWall.even_height hj₀_lt k)
    htarget.2.2.1 htarget.2.2.2
  -- Walk along `elemRow W.height j₀.1` from `cornerToRowTarget` to `sphereToWall a₁`
  obtain ⟨w_target_a₁⟩ := exists_walk_in_liftElemSet W.toWall hj₀_disj htarget.2.1 hadj_elem.1
    (isElemWallConn_elemRow W.toWall.two_le_height hj₀_lt.le) htarget.1 ha₁_row
  obtain ⟨w_a₁_uf⟩ := hw_a₁_uf
  have w_total := (w_corner_target.append w_target_a₁).append w_a₁_uf
  have hcorner_A : fig1Sph φ (pos (W.toWall.corner k)) ∈ A.vertexSet :=
    hPi_sub ⟨k, rfl⟩
  have huf_not_B := (mem_A_of_walk_deleteVerts_sep hΓv hsep w_total hcorner_A).2
  exact huf_not_B hu_f_B

/-- Given a Fig. 1 sphere drawing `Γ` of a wall `W` with `max 4 θ ≤ W.height`, there exist a
tangle `T` of order `W.height` and a tangle metric `d` on `Γ.drawing` satisfying Hypothesis (iv) of
Theorem (8.3) as well as the row-avoidance property `hrow`. -/
theorem exists_wall_tangle_for_8_3 {α : Type u} {β : Type v} [Nonempty α] [Nonempty β]
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    {θ : ℕ} (hθ : θ ≤ W.height) (hh4 : 4 ≤ W.height)
    (hinj : InjOn pos V(W.graph))
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (h2cell : Γ.drawing.IsTwoCell) :
    ∃ (T : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
        Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane))))
      (d : Set (OnePoint EuclideanPlane) → Set (OnePoint EuclideanPlane) → ℕ),
      (θ ≤ W.height ∧ HasTangleMetric Γ.drawing W.height T d ∧
        ∀ A B, (A, B) ∈ T → separationOrder A B ≤ 3 →
          ¬ (wallPiSet W.toWall φ pos ⊆ A.vertexSet)) ∧
      (∀ A B, (A, B) ∈ T → ∀ j : Fin W.height,
        ∃ e ∈ E(GM16.sphereWallRow W.height j), ∃ (f : β) (hf : f ∈ E(W.graph)),
          f ∈ E(W.subdivisionPaths (W.sphereEdge e)) ∧
            (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ∉ A.edgeSet) := by
  obtain ⟨_, _, T, _, _, hCtrl, hrow⟩ :=
    W.toWall.exists_controlled_tangle (le_refl W.graph)
      W.toWall.vertexSet_finite W.toWall.edgeSet_finite Γ
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  have hSphere : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hresp := GM16.drawing_tangle_isRespectful_of_isSphere hS hSphere Γ.drawing
    hCtrl.isTangle_H
  obtain ⟨d, hd⟩ := GM16.exists_tangleMetric hS ⟨h2cell, hCtrl.isTangle_H, hresp⟩
  refine ⟨T, d, ⟨hθ, hd, tangle_no_order_le_three_corners hh4 hinj hΓv hCtrl.isTangle_H hrow⟩,
    hrow⟩

end GM22
end GraphMinor
