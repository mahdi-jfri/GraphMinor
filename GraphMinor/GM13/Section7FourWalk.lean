module

public import GraphMinor.GM13.Section7FourRegions
public import GraphMinor.GM13.Section7FourRows
public import GraphMinor.GM13.Section7WallTangle
public import GraphMinor.GM14.Defs
import GraphMinor.GM09.RuralAdd
import GraphMinor.GM11.Regions
import GraphMinor.GM11.Rotation
import GraphMinor.GM11.RadialRegions
import GraphMinor.GM11.Section6
import GraphMinor.GM11.Section7
import GraphMinor.GM11.Section8
import GraphMinor.GM11.Ties
import GraphMinor.GM11.Walks
import GraphMinor.GM12.Section1
import GraphMinor.GM12.Section2SpokePaths
import GraphMinor.GM12.Section4WalkMetric
import GraphMinor.GM12.Section73MetricVisits
import GraphMinor.GM13.Section7
import GraphMinor.GM13.Section7Cells
import GraphMinor.GM13.Section7Five
import GraphMinor.Surface.DiscGrow

/-!
# Graph Minors XIII, (7.4): a small tangle metric gives a small wall distance

The proof of (7.4) (page 90) applies XII (4.4) to the wall `H` drawn in the sphere, with the
tangle of `H` whose small sides contain no row. XII (4.4) asks that the ends of the paths be
far apart in the metric `d` of this tangle, while (7.4) assumes that they are far apart in the
distance of `H`. The paper passes from one to the other without comment. This file proves the
step: if `d({x}, {y}) < N` and the height of the wall is at least `2N + 2`, then the distance
of `x` and `y` in `H` is at most `4N + 4` (`wallDist_le_of_tangleMetric_lt`).

The argument has three parts.
- A small metric gives a closed walk `W` of the radial drawing, of length less than `2N`, with
  `x` and `y` in `ins(W)` (XII, (7.3), `GM12.exists_tangleMetric_walk_with_two_visit_bound`).
- Two vertices of `H` on such a walk are at distance at most its length. Between two vertices
  of `H` that follow each other on the walk there is one vertex of the radial drawing, inside a
  region of `H`, and both vertices lie on the closure of that region
  (`le_length_of_radial_walk`).
- A vertex of `H` inside `ins(W)` is at distance at most `N + 2` from a vertex of `H` on `W`.
  Otherwise, by `exists_free_row_set`, a connected part of the drawing would join it to a whole
  row while missing the boundary of a disc `ins(C)`. Then the row lies in `ins(C)`, and the
  small side of the separation given by `ins(C)` contains the row, which the tangle forbids.
-/

public section

namespace GraphMinor.GM13

open Set Function
open Graph
open GraphMinor
open GraphMinor.Surface
open GraphMinor.GM14

universe u v

variable {α : Type u} {β : Type v}

section Radial

variable {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- The vertex of a radial edge that is not a vertex of `Γ` lies in a region of `Γ`, and the
other end lies on the closure of that region. -/
theorem radial_link_of_mem (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hrad : GM11.PreRad (GM11.PaintingOrDrawing.drawing Γ) K) {e : Set S} {x y : S}
    (hl : K.toGraph.IsLink e x y) (hx : x ∈ Γ.V) :
    y ∉ Γ.V ∧ ∃ r ∈ Γ.R, y ∈ r ∧ x ∈ closure r := by
  obtain ⟨v, hv, r, hr, w, hwr, hwV, hcap, her⟩ := GM11.spoke_ends hrad hS hl.1
  have hwΓ : w ∉ Γ.V := fun h => GM11.region_subset hr hwr (Γ.V_subset_U h)
  have hxy : closure e ∩ K.V = {x, y} := hl.2.2.2
  have hw : w ∈ ({x, y} : Set S) := by rw [← hxy, hcap]; exact Or.inr rfl
  rcases hw with rfl | hw
  · exact (hwΓ hx).elim
  · rw [mem_singleton_iff] at hw
    subst hw
    have hxe : x ∈ closure e := by
      have : x ∈ closure e ∩ K.V := by rw [hxy]; exact Or.inl rfl
      exact this.1
    exact ⟨hwΓ, r, hr, hwr, closure_mono her hxe⟩

/-- The other end of a radial edge at a vertex `x` that is not a vertex of `Γ` is a vertex of
`Γ`, and it lies on the closure of every region of `Γ` that contains `x`. -/
theorem radial_link_of_notMem (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hrad : GM11.PreRad (GM11.PaintingOrDrawing.drawing Γ) K) {e : Set S} {x y : S}
    (hl : K.toGraph.IsLink e x y) (hx : x ∉ Γ.V) :
    y ∈ Γ.V ∧ ∀ r ∈ Γ.R, x ∈ r → y ∈ closure r := by
  obtain ⟨v, hv, r, hr, w, hwr, hwV, hcap, her⟩ := GM11.spoke_ends hrad hS hl.1
  have hxy : closure e ∩ K.V = {x, y} := hl.2.2.2
  have hvm : v ∈ ({x, y} : Set S) := by rw [← hxy, hcap]; exact Or.inl rfl
  have hyv : y = v := by
    rcases hvm with rfl | hvm
    · exact (hx hv).elim
    · exact (mem_singleton_iff.mp hvm).symm
  subst hyv
  refine ⟨hv, fun r' hr' hxr' => ?_⟩
  have her' : e ⊆ r' := GM12.spoke_subset_region hS hrad hr' hl.1 hxr' hl.2.1
    (by have : x ∈ closure e ∩ K.V := by rw [hxy]; exact Or.inl rfl
        exact this.1)
  have hye : y ∈ closure e := by
    have : y ∈ closure e ∩ K.V := by rw [hxy]; exact Or.inr rfl
    exact this.1
  exact closure_mono her' hye

omit [TopologicalSpace S] [T2Space S] [ConnectedSpace S] in
theorem GraphWalk.start_mem_support {G : Graph S (Set S)} {a b : S} (W : GraphWalk G a b) :
    a ∈ W.support := by
  cases W <;> simp [GraphWalk.support]

/-- **Vertices on a radial walk are close.** Let `K` be a radial drawing of `Γ`, and let `D` be a
function with `D u u = 0` and the triangle inequality, such that any two vertices of `Γ` on the
closure of one region are at `D`-distance at most 2. Then any two vertices of `Γ` on a walk of `K`
are at `D`-distance at most the length of the walk. -/
theorem le_length_of_radial_walk (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hrad : GM11.PreRad (GM11.PaintingOrDrawing.drawing Γ) K) (D : S → S → ℕ)
    (hrefl : ∀ u, D u u = 0) (htri : ∀ u v w, D u w ≤ D u v + D v w)
    (hreg : ∀ r ∈ Γ.R, ∀ u v, u ∈ closure r → v ∈ closure r → u ∈ Γ.V → v ∈ Γ.V →
      D u v ≤ 2) :
    ∀ (n : ℕ) {a b : S} (W : GraphWalk K.toGraph a b), W.length = n →
      ∀ u ∈ W.support, ∀ v ∈ W.support, u ∈ Γ.V → v ∈ Γ.V → D u v ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b W hn u hu v hv huΓ hvΓ
  cases W with
  | nil ha =>
    simp only [GraphWalk.support, List.mem_singleton] at hu hv
    subst hu hv
    simp [hrefl]
  | @cons _ a' _ e hl rest =>
    have hlen : rest.length + 1 = n := by
      rw [← hn]; simp [GraphWalk.length, GraphWalk.edges]
    -- the key step: the start of the walk against a later vertex
    have key : a ∈ Γ.V → ∀ w ∈ rest.support, w ∈ Γ.V → D a w ≤ n ∧ D w a ≤ n := by
      intro haΓ w hw hwΓ
      obtain ⟨ha'Γ, r, hr, ha'r, har⟩ := radial_link_of_mem hS hrad hl haΓ
      cases rest with
      | nil _ =>
        simp only [GraphWalk.support, List.mem_singleton] at hw
        subst hw
        exact (ha'Γ hwΓ).elim
      | @cons _ a'' _ e' hl' rest' =>
        obtain ⟨ha''Γ, ha''r⟩ := radial_link_of_notMem hS hrad hl' ha'Γ
        have ha''r' := ha''r r hr ha'r
        have hlen' : rest'.length + 2 = n := by
          rw [← hlen]; simp [GraphWalk.length, GraphWalk.edges]
        have hw' : w ∈ rest'.support := by
          simp only [GraphWalk.support, List.mem_cons] at hw
          rcases hw with rfl | hw
          · exact (ha'Γ hwΓ).elim
          · exact hw
        have h1 := ih rest'.length (by omega) rest' rfl a'' rest'.start_mem_support w hw'
          ha''Γ hwΓ
        have h2 := ih rest'.length (by omega) rest' rfl w hw' a'' rest'.start_mem_support
          hwΓ ha''Γ
        have h3 := hreg r hr a a'' har ha''r' haΓ ha''Γ
        have h4 := hreg r hr a'' a ha''r' har ha''Γ haΓ
        have h5 := htri a a'' w
        have h6 := htri w a'' a
        omega
    simp only [GraphWalk.support, List.mem_cons] at hu hv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · simp [hrefl]
    · exact (key huΓ v hv hvΓ).1
    · exact (key hvΓ u hu huΓ).2
    · have := ih rest.length (by omega) rest rfl u hu v hv huΓ hvΓ
      omega

omit [T2Space S] [ConnectedSpace S] in
/-- The atom of a radial drawing that corresponds to a vertex `{v}` is `{v}`. -/
theorem correspondingAtom_singleton {Γ K : Drawing S} {v : S} (hv : v ∈ Γ.V) {a : Set S}
    (h : IsCorrespondingAtom Γ K {v} a) : a = {v} := by
  rcases h with ⟨-, -, ⟨w, -, hvw, rfl⟩ | ⟨he, -⟩ | ⟨hr, -⟩⟩
  · rw [hvw]
  · exact (GM11.edge_notMem_V he (mem_singleton v) hv).elim
  · exact (GM11.region_subset hr (mem_singleton v) (Γ.V_subset_U hv)).elim

end Radial

/-- A unit segment of row `j` of the elementary wall lies in the row segment `fig1RowSeg h j`. -/
theorem fig1Segment_subset_fig1RowSeg {h j x x' : ℕ} (hxx : x' = x + 1 ∨ x = x' + 1)
    (hx : 1 ≤ x) (hx' : 1 ≤ x') (hx2 : x ≤ 2 * h + 1) (hx2' : x' ≤ 2 * h + 1) :
    fig1Segment (x, j) (x', j) ⊆ fig1RowSeg h j := by
  unfold fig1Segment fig1RowSeg GM16.horizontalLatticeLine
  simp only [if_true, min_self]
  rintro ⟨s, t⟩ ⟨⟨hs1, hs2⟩, ht⟩
  refine ⟨⟨?_, ?_⟩, ht⟩
  · have : (1 : ℝ) ≤ ((min x x' : ℕ) : ℝ) := by exact_mod_cast le_min hx hx'
    simp only at hs1
    linarith
  · have : ((min x x' : ℕ) : ℝ) + 1 ≤ 2 * (h : ℝ) + 1 := by
      have : min x x' + 1 ≤ 2 * h + 1 := by omega
      exact_mod_cast this
    simp only at hs2
    linarith

/-- **A small tangle metric gives a small wall distance** (the step of the proof of (7.4), page
90, that passes from the distance of `H` to the metric of its tangle). Let `W` be a wall drawn as
in Fig. 1, and let `Γ` be its sphere drawing in the coordinates of Fig. 1 (as given by
`DrawnWall.IsFigure1.exists_fig1Coords`). Let `T` be a tangle of `Γ` whose small sides contain
no row (as given by `Wall.exists_controlled_tangle`), with metric `d`. If the height of `W` is at
least `2N + 2` and `d({x}, {y}) < N` for two vertices `x, y`, then `W.dist x y ≤ 4N + 4`. -/
theorem wallDist_le_of_tangleMetric_lt [Nonempty β] {W : DrawnWall α β}
    {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hpos : ∀ v ∈ V(W.graph), pos v ∈ fig1Set W.height)
    (hdist : ∀ u ∈ V(W.graph), ∀ v ∈ V(W.graph), W.dist u v =
      planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells W.height))
        (fig1PlaneEquiv (pos u)) (fig1PlaneEquiv (pos v)))
    (hΓU : Γ.drawing.U = fig1Sph φ '' fig1Set W.height)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hΓe : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β)
      (hf : f ∈ E(W.graph)), f ∈ E(W.subdivisionPaths (W.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q)
    {T : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
      Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)))}
    (hrow : ∀ A B, (A, B) ∈ T → ∀ j : Fin W.height,
      ∃ e ∈ E(GM16.sphereWallRow W.height j), ∃ (f : β) (hf : f ∈ E(W.graph)),
        f ∈ E(W.subdivisionPaths (W.sphereEdge e)) ∧ (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ∉ A.edgeSet)
    {d : Set (OnePoint EuclideanPlane) → Set (OnePoint EuclideanPlane) → ℕ}
    (hd : HasTangleMetric Γ.drawing W.height T d) {N : ℕ} (hN : 2 * N + 2 ≤ W.height)
    {x y : α} (hx : x ∈ V(W.graph)) (hy : y ∈ V(W.graph))
    (hlt : d {fig1Sph φ (pos x)} {fig1Sph φ (pos y)} < N) :
    W.dist x y ≤ 4 * N + 4 := by
  classical
  have he : Even W.height := W.toWall.even_height
  have hh2 : 2 ≤ W.height := W.toWall.two_le_height
  have hS : IsClosedSurface (OnePoint EuclideanPlane) := GM09.isClosedSurface_sphere
  obtain ⟨hResp, K, ins, hK, hder, hdeq⟩ := hd
  have hsl : GM11.IsSlope K (2 * W.height) ins :=
    GM11.isSlope_of_derived (Γ := GM11.PaintingOrDrawing.drawing Γ.drawing) hS
      ⟨hResp.2.1.one_le, hResp.2.1.isSeparation, hResp.2.1.order_lt, hResp.2.1.axiom1,
        hResp.2.1.axiom2⟩ hK.2.1.1 hder
  have hrad : GM11.PreRad (GM11.PaintingOrDrawing.drawing Γ.drawing) K := ⟨hK.1, hK.2.1⟩
  -- the distance on points of the sphere
  set U₀ := fig1PlaneEquiv '' cellSet (fig1WallCells W.height) with hU₀
  have hthin : IsThinPlaneDrawing U₀ := isThinPlaneDrawing_cellSet (fig1WallCells_not_square _)
  let q : OnePoint EuclideanPlane → ℝ × ℝ := Function.invFun (fig1Sph φ)
  have hq : ∀ z, q (fig1Sph φ z) = z :=
    Function.leftInverse_invFun (isOpenEmbedding_fig1Sph φ).injective
  have hqU : ∀ c ∈ Γ.drawing.U, fig1Sph φ (q c) = c ∧ q c ∈ fig1Set W.height := by
    intro c hc
    rw [hΓU] at hc
    obtain ⟨z, hz, rfl⟩ := hc
    rw [hq]
    exact ⟨rfl, hz⟩
  let D : OnePoint EuclideanPlane → OnePoint EuclideanPlane → ℕ := fun a b =>
    planeWallDist U₀ (fig1PlaneEquiv (q a)) (fig1PlaneEquiv (q b))
  have hrefl : ∀ a, D a a = 0 := fun a => by simp [D, planeWallDist]
  have htri : ∀ a b c, D a c ≤ D a b + D b c := fun a b c => planeWallDist_triangle hthin _ _ _
  have hcomm : ∀ a b, D a b = D b a := fun a b => planeWallDist_comm _ _ _
  have hreg : ∀ r ∈ Γ.drawing.R, ∀ u v, u ∈ closure r → v ∈ closure r → u ∈ Γ.drawing.V →
      v ∈ Γ.drawing.V → D u v ≤ 2 := by
    intro r hr u v hu hv huV hvV
    rw [← (hqU u (Γ.drawing.V_subset_U huV)).1] at hu
    rw [← (hqU v (Γ.drawing.V_subset_U hvV)).1] at hv
    exact planeWallDist_le_two_of_mem_closure_region (by omega) he hΓU hr hu hv
  -- the two points
  have hVpt : ∀ z (hz : z ∈ V(W.graph)), fig1Sph φ (pos z) ∈ Γ.drawing.V := by
    intro z hz
    have := (Γ.iso.vertexEquiv ⟨z, hz⟩).2
    rwa [hΓv] at this
  set a := fig1Sph φ (pos x) with ha
  set b := fig1Sph φ (pos y) with hb
  have haV := hVpt x hx
  have hbV := hVpt y hy
  have hDab : W.dist x y = D a b := by
    simp only [D, a, b, hq]
    exact hdist x hx y hy
  by_cases hxy : x = y
  · subst hxy
    rw [hDab, hrefl]
    omega
  have hab : ({a} : Set (OnePoint EuclideanPlane)) ≠ {b} := by
    intro h
    apply hxy
    have h1 : a = b := singleton_injective h
    have h2 : (Γ.iso.vertexEquiv ⟨x, hx⟩).1 = (Γ.iso.vertexEquiv ⟨y, hy⟩).1 := by
      rw [hΓv, hΓv]; exact h1
    exact congrArg Subtype.val (Γ.iso.vertexEquiv.injective (Subtype.ext h2))
  have hA : ∀ c ∈ Γ.drawing.V, ({c} : Set (OnePoint EuclideanPlane)) ∈ Γ.drawing.A :=
    fun c hc => Or.inl (Or.inl ⟨c, hc, rfl⟩)
  rw [hdeq _ (hA a haV) _ (hA b hbV)] at hlt
  obtain ⟨p, W', a', b', ha', hb', hlen, -, haW, hbW, -⟩ :=
    GM12.exists_tangleMetric_walk_with_two_visit_bound hS hK hsl hab (by omega)
  rw [correspondingAtom_singleton haV ha'] at haW
  rw [correspondingAtom_singleton hbV hb'] at hbW
  -- a vertex of `Γ` inside `ins(W')` is near a vertex of `Γ` on `W'`
  have hnear : ∀ c ∈ Γ.drawing.V, c ∈ GM11.insWalk ins K W' →
      ∃ u ∈ W'.support, u ∈ Γ.drawing.V ∧ D c u ≤ N + 2 := by
    intro c hcV hc
    rcases hc with hcU | hcC
    · refine ⟨c, ?_, hcV, by rw [hrefl]; omega⟩
      rcases GM11.walk_U_cases hcU with h | ⟨e, he, hce⟩
      · exact h
      · exfalso
        have heK : e ∈ K.E := by
          have : e ∈ (GM11.walkDrawing K W').E := by rw [GM11.walkDrawing_E]; exact he
          exact (GM11.walkDrawing_isSubdrawing K W').2 this
        exact GM11.edge_notMem_V heK hce (hK.2.1.2.1 hcV)
    · obtain ⟨C, ⟨hC, hCW⟩, hcC⟩ := mem_iUnion₂.mp hcC
      have hCK : C.IsSubdrawing K := hCW.trans (GM11.walkDrawing_isSubdrawing K W')
      have hClen : C.length ≤ W'.length := by
        apply (ncard_le_ncard (fun e he => ?_) W'.edges.finite_toSet).trans
          (GM11.ncard_mem_list_le W'.edges)
        have hem := hCW.2 he
        rwa [GM11.walkDrawing_E] at hem
      have hClt : C.length < 2 * W.height := by omega
      obtain ⟨hdisc, hbd, hT⟩ := hder C hC hCK hClt
      obtain ⟨hcount, hne⟩ := GM12.circuit_length_eq_two_mul_ncard hK.2.1 hC hCK
      have hCfin : (C.V ∩ Γ.drawing.V).Finite := Γ.drawing.finite_V.subset inter_subset_right
      have hCsupp : C.V ∩ Γ.drawing.V ⊆ {u | u ∈ W'.support} := by
        intro u hu
        have := hCW.1 hu.1
        rwa [GM11.walkDrawing_V] at this
      -- the positions of the vertices of `Γ` on `C`
      set X : Set (ℝ × ℝ) := q '' (C.V ∩ Γ.drawing.V) with hX
      have hXfin : X.Finite := hCfin.image q
      have hXN : X.ncard ≤ N := (ncard_image_le hCfin).trans (by omega)
      have hc' := hqU c (Γ.drawing.V_subset_U hcV)
      by_contra hcon
      push Not at hcon
      have hfar : ∀ z ∈ X, N + 2 < planeWallDist U₀ (fig1PlaneEquiv (q c)) (fig1PlaneEquiv z) := by
        rintro _ ⟨u, hu, rfl⟩
        exact hcon u (hCsupp hu) hu.2
      obtain ⟨j, Y, hj, hYc, hcY, hYset, hYX, hrowY⟩ :=
        exists_free_row_set he hN hXfin hXN hc'.2 hfar
      -- the image of `Y` misses `U(C)`, so it lies in `ins(C)`
      have hYC : Disjoint (fig1Sph φ '' Y) (frontier (ins C)) := by
        rw [← GM11.subBd_eq_frontier, hbd]
        refine disjoint_left.mpr ?_
        rintro _ ⟨z, hzY, rfl⟩ hzC
        have hzU : fig1Sph φ z ∈ Γ.drawing.U := by rw [hΓU]; exact ⟨z, hYset hzY, rfl⟩
        have hzK : fig1Sph φ z ∈ K.U := hCK.U_subset hzC
        have hzV : fig1Sph φ z ∈ Γ.drawing.V := by
          have hm : fig1Sph φ z ∈ (GM11.PaintingOrDrawing.drawing Γ.drawing).U ∩ K.U :=
            ⟨hzU, hzK⟩
          rw [hK.2.1.1] at hm
          exact hm
        have hzCV : fig1Sph φ z ∈ C.V := by
          rw [C.U_eq] at hzC
          rcases hzC with hzC | hzC
          · exact hzC
          · obtain ⟨e, heC, hze⟩ := mem_iUnion₂.mp hzC
            have : fig1Sph φ z ∈ closure e ∩ C.V := by
              rw [hCK.closure_inter_V heC]
              exact ⟨hze, hK.2.1.2.1 hzV⟩
            exact this.2
        exact disjoint_left.mp hYX hzY ⟨_, ⟨hzCV, hzV⟩, hq z⟩
      have hYsub : fig1Sph φ '' Y ⊆ ins C :=
        GM12.subset_of_disjoint_frontier
          (hYc.image _ (isOpenEmbedding_fig1Sph φ).continuous.continuousOn) hdisc.isClosed hYC
          (x := c) ⟨q c, hcY, hc'.1⟩ hcC
      -- the row `j` lies in `ins(C)`, against the choice of the tangle
      obtain ⟨e, he, f, hf, hfP, hfA⟩ := hrow _ _ hT ⟨j, hj⟩
      apply hfA
      refine ⟨(Γ.iso.edgeEquiv ⟨f, hf⟩).2, ?_⟩
      obtain ⟨a₁, b₁, ⟨rfl, hadjE⟩, ha₁, hb₁⟩ := he
      have hadj : (GM16.sphereWallSimpleGraph W.height).Adj a₁ b₁ := hadjE
      rw [W.sphereEdge_mk (sphereToWall_adj hadj)] at hfP
      refine (hΓe _ _ _ f hf hfP).trans ((image_mono ?_).trans hYsub)
      refine subset_trans ?_ hrowY
      have ha₁j : a₁.2.val = j := congrArg Fin.val ha₁
      have hb₁j : b₁.2.val = j := congrArg Fin.val hb₁
      have hstep : b₁.1.val = a₁.1.val + 1 ∨ a₁.1.val = b₁.1.val + 1 := by
        have h12 : a₁.2 = b₁.2 := ha₁.trans hb₁.symm
        rcases hadj with ⟨-, h | h⟩ | ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩
        · exact Or.inl h.symm
        · exact Or.inr h.symm
        · rw [h12] at h; omega
        · rw [h12] at h; omega
      have hpa : sphereToWall a₁ = (a₁.1.val + 1, j) := by simp [sphereToWall, ha₁j]
      have hpb : sphereToWall b₁ = (b₁.1.val + 1, j) := by simp [sphereToWall, hb₁j]
      rw [hpa, hpb]
      have := a₁.1.isLt
      have := b₁.1.isLt
      exact fig1Segment_subset_fig1RowSeg (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨u, huW, huV, hau⟩ := hnear a haV (haW rfl)
  obtain ⟨v, hvW, hvV, hbv⟩ := hnear b hbV (hbW rfl)
  have hwalk := le_length_of_radial_walk hS hrad D hrefl htri hreg _ W' rfl u huW v hvW huV hvV
  have h1 := htri a u b
  have h2 := htri u v b
  have h3 := hcomm b v
  rw [hDab]
  omega

end GraphMinor.GM13
