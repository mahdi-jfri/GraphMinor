module

public import GraphMinor.GM13.Section7Four
public import GraphMinor.GM13.Section7Naming
import GraphMinor.GM09.DiscDrawing

/-!
# Graph Minors XIII, (7.4): the drawing in coordinates

The proof of (7.4) (page 90) says "taking $\Sigma$ to be a sphere, and taking $\Gamma = H$". This
file records the
sphere drawing of a wall drawn as in Fig. 1 in the coordinates of Fig. 1: every vertex has a
position in the Fig. 1 point set, the distance `d` of two vertices is the distance of the Fig. 1
point set between their positions, and every edge of the path subdividing the edge `pq` of the
elementary wall is drawn on the unit segment from `p` to `q`
(`DrawnWall.IsFigure1.exists_fig1Coords`).
-/

public section

namespace GraphMinor.GM13

open Set Function
open Graph
open GraphMinor
open GraphMinor.Surface

universe u v

variable {α : Type u} {β : Type v}

/-- The map from the coordinates of Fig. 1 to the sphere, through a homeomorphism `φ` of the
plane. -/
@[expose] noncomputable def fig1Sph (φ : EuclideanPlane ≃ₜ EuclideanPlane) (z : ℝ × ℝ) :
    OnePoint EuclideanPlane :=
  ((φ (fig1PlaneEquiv z) : EuclideanPlane) : OnePoint EuclideanPlane)

theorem isOpenEmbedding_fig1Sph (φ : EuclideanPlane ≃ₜ EuclideanPlane) :
    Topology.IsOpenEmbedding (fig1Sph φ) :=
  isOpenEmbedding_fig1Sphere φ

theorem fig1Set_eq_cellSet (h : ℕ) : fig1Set h = cellSet (fig1WallCells h) := by
  have := (fig1WallSet_eq_image_fig1Set h).symm.trans (fig1WallSet_eq_cellSet h)
  exact fig1PlaneEquiv.injective.image_injective this

/-- **A wall drawn as in Fig. 1, in coordinates.** For a wall `W` drawn as in Fig. 1 there are a
homeomorphism `φ` of the plane, a position `pos v` in the Fig. 1 point set for each vertex `v`,
and a 2-cell drawing `Γ` of `W.graph` in the sphere, such that
- the distance of two vertices is the Fig. 1 distance of their positions;
- the drawing `Γ` is the Fig. 1 point set carried to the sphere by `fig1Sph φ`, each vertex is
  drawn at its position, and each edge of the path subdividing the edge `pq` of the elementary
  wall is drawn on the unit segment from `p` to `q`. -/
theorem DrawnWall.IsFigure1.exists_fig1Coords {W : DrawnWall α β} (hW : W.IsFigure1) :
    ∃ (φ : EuclideanPlane ≃ₜ EuclideanPlane) (pos : α → ℝ × ℝ)
      (Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)),
      (∀ v ∈ V(W.graph), pos v ∈ fig1Set W.height) ∧
      InjOn pos V(W.graph) ∧
      (∀ u ∈ V(W.graph), ∀ v ∈ V(W.graph), W.dist u v =
        planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells W.height))
          (fig1PlaneEquiv (pos u)) (fig1PlaneEquiv (pos v))) ∧
      Γ.drawing.U = fig1Sph φ '' fig1Set W.height ∧
      (∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1)) ∧
      (∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β) (hf : f ∈ E(W.graph)),
        f ∈ E(W.subdivisionPaths (W.baseEdge hadj)) →
          (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q) ∧
      Γ.drawing.IsTwoCell := by
  classical
  obtain ⟨φ, Γ₀, hΓ₀, hU, hv⟩ := hW
  have hUc : IsCompact Γ₀.drawing.U := by
    rw [hΓ₀.drawing_U_eq]; exact isCompact_fig1WallSet _
  let F : EuclideanPlane → OnePoint EuclideanPlane := fun x => ((φ x : EuclideanPlane) :
    OnePoint EuclideanPlane)
  have hF : Continuous F := OnePoint.continuous_coe.comp φ.continuous
  have hinj : InjOn F Γ₀.drawing.U := fun x _ y _ hxy =>
    φ.injective (OnePoint.coe_injective hxy)
  obtain ⟨Γ, hΓU, -, hΓv, -, hΓe, -⟩ := GM09.GraphDrawing.transportOn Γ₀ hUc hF.continuousOn hinj
  let pos : α → ℝ × ℝ := fun v => if hv : v ∈ V(W.graph) then
    fig1PlaneEquiv.symm (Γ₀.iso.vertexEquiv ⟨v, hv⟩).1 else 0
  have hpos : ∀ x : V(W.graph), fig1PlaneEquiv (pos x.1) = (Γ₀.iso.vertexEquiv x).1 := by
    intro x
    simp only [pos, dif_pos x.2, Homeomorph.apply_symm_apply]
  have hFfig : ∀ z, F (fig1PlaneEquiv z) = fig1Sph φ z := fun z => rfl
  have hU0 : Γ₀.drawing.U = fig1PlaneEquiv '' fig1Set W.height := by
    rw [hΓ₀.drawing_U_eq, fig1WallSet_eq_image_fig1Set]
  refine ⟨φ, pos, Γ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have h1 := Γ₀.drawing.V_subset_U (Γ₀.iso.vertexEquiv ⟨v, hv⟩).2
    rw [← hpos ⟨v, hv⟩, hU0] at h1
    obtain ⟨z, hz, hzeq⟩ := h1
    rwa [← fig1PlaneEquiv.injective hzeq]
  · intro u hu v hv huv
    have h1 : fig1PlaneEquiv (pos u) = fig1PlaneEquiv (pos v) := by rw [huv]
    rw [hpos ⟨u, hu⟩, hpos ⟨v, hv⟩] at h1
    have := Γ₀.iso.vertexEquiv.injective (Subtype.ext h1)
    exact congrArg Subtype.val this
  · intro u hu w hw
    rw [DrawnWall.dist, DrawnWall.planeDist, hU, hv u hu, hv w hw, planeWallDist_image_homeomorph,
      hΓ₀.drawing_U_eq, fig1WallSet_eq_cellSet, hpos ⟨u, hu⟩, hpos ⟨w, hw⟩]
  · rw [hΓU, hU0, image_image]
    rfl
  · intro x
    rw [hΓv x, ← hpos x]
    rfl
  · intro p q hadj f hf hfP
    have h0 : GM09.graphDrawingEdgeSet Γ f = (Γ.iso.edgeEquiv ⟨f, hf⟩).1 := by
      ext z; simp only [GM09.graphDrawingEdgeSet, mem_iUnion]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hf, h⟩⟩
    have h0' : GM09.graphDrawingEdgeSet Γ₀ f = (Γ₀.iso.edgeEquiv ⟨f, hf⟩).1 := by
      ext z; simp only [GM09.graphDrawingEdgeSet, mem_iUnion]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hf, h⟩⟩
    have h1 := hΓe f
    rw [h0, h0'] at h1
    rw [h1]
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ fig1PlaneEquiv '' fig1Segment p q := by
      rw [← hΓ₀.path_on_segment p q hadj]
      exact mem_iUnion₂.mpr ⟨⟨f, hf⟩, hfP, subset_closure hz⟩
    obtain ⟨w, hw, rfl⟩ := hz'
    exact ⟨w, hw, rfl⟩
  · have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
    refine fig1_isTwoCell GM09.isClosedSurface_sphere hsph (isOpenEmbedding_fig1Sph φ)
      W.toWall.even_height W.toWall.two_le_height ?_
    rw [hΓU, hU0, image_image]
    rfl

end GraphMinor.GM13
