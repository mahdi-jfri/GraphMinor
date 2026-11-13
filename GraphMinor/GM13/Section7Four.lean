module

public import GraphMinor.GM13.Defs
public import GraphMinor.GM16.Defs
public import GraphMinor.GM16.Section3
public import GraphMinor.GM13.Section7Figure1
public import GraphMinor.GM09.DiscDrawing
public import GraphMinor.GM16.RectangleStackDisc
public import GraphMinor.GM16.IntervalTiling
public import GraphMinor.GM16.EmptyDiscRegion
public import GraphMinor.GM16.SphereComplementDisc
public import GraphMinor.GM16.RectangularDisc
public import GraphMinor.GM11.Regions
public import GraphMinor.GM11.Section6
public import GraphMinor.GM11.PaintingCells
public import GraphMinor.Surface.Wedge
public import GraphMinor.GM09.RuralAdd

/-!
# Graph Minors XIII, (7.4): pieces of the proof

The paper proves (7.4) from XII (4.4), whose conclusion is that a tangle controls a `K_p` minor.
This file proves the last step: a controlled minor is a model in the sense of Section 2 of
Graph Minors XIII (`HasGraphModel`).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function
open Graph
open GraphMinor
open GraphMinor.Surface

universe u v

variable {α : Type u} {β : Type v}

/-- A chain of adjacent vertices of a graph gives a walk of it. -/
theorem nonempty_graphWalk_of_reflTransGen {K : Graph α β} {x y : α} (hx : x ∈ V(K))
    (h : Relation.ReflTransGen K.Adj x y) : Nonempty (GraphWalk K x y) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨GraphWalk.nil hx⟩
  | head hxz _ ih =>
    obtain ⟨e, he⟩ := hxz
    obtain ⟨W⟩ := ih he.right_mem
    exact ⟨GraphWalk.cons he W⟩

/-- **A controlled minor is a model.** The branch sets of a minor controlled by a tangle
(`GM16.ControlsMinor`) form a model of `L` in `G`. -/
theorem hasGraphModel_of_controlsMinor {α' β' : Type*} {G : Graph α β} {L : Graph α' β'}
    {T : Set (Hypergraph α β × Hypergraph α β)} (h : GM16.ControlsMinor G L T) :
    HasGraphModel L G := by
  obtain ⟨a, b, hconn, hdisj, hlink, hloop, hinj, -⟩ := h
  apply hasGraphModel_of_exists_isGraphModel
  refine ⟨a, b, ⟨fun v hv => (hconn v hv).1, fun v hv => (hconn v hv).2.1, ?_,
    fun u v hu hv hne => hdisj u hu v hv hne, ?_, ?_, ?_, hinj⟩⟩
  · intro v hv x hx y hy
    exact nonempty_graphWalk_of_reflTransGen hx ((hconn v hv).2.2.2 x hx y hy)
  · intro e he
    obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
    by_cases hne : u = v
    · subst hne
      exact (hloop e he u huv.left_mem huv).1.1
    · exact (hlink e he u huv.left_mem v huv.right_mem hne huv).1
  · intro e u v huv hne
    exact (hlink e huv.edge_mem u huv.left_mem v huv.right_mem hne huv).2
  · intro e u huu
    have h := hloop e huu.edge_mem u huu.left_mem huu
    exact ⟨h.1.2, h.2⟩

/-! ## The sphere drawing of a wall drawn as in Fig. 1 -/

theorem elementaryWallVerts_finite (h : ℕ) : (elementaryWallVerts h).Finite :=
  ((Set.finite_Iic (2 * h + 1)).prod (Set.finite_Iic h)).subset
    (fun _ hp => ⟨hp.1, hp.2.1⟩)

/-- The Fig. 1 point set is compact: it is a finite union of unit segments. -/
theorem isCompact_fig1WallSet (h : ℕ) : IsCompact (fig1WallSet h) := by
  have hfin : {pq : (ℕ × ℕ) × (ℕ × ℕ) | elementaryWallAdj h pq.1 pq.2}.Finite :=
    ((elementaryWallVerts_finite h).prod (elementaryWallVerts_finite h)).subset
      (fun pq hpq => ⟨hpq.1, hpq.2.1⟩)
  have heq : fig1WallSet h = ⋃ pq ∈ {pq : (ℕ × ℕ) × (ℕ × ℕ) | elementaryWallAdj h pq.1 pq.2},
      fig1PlaneEquiv '' fig1Segment pq.1 pq.2 := by
    ext x; simp [fig1WallSet]
  rw [heq]
  refine hfin.isCompact_biUnion fun pq _ => IsCompact.image ?_ fig1PlaneEquiv.continuous
  unfold fig1Segment
  split_ifs
  · exact isCompact_Icc.prod isCompact_singleton
  · exact isCompact_singleton.prod isCompact_Icc

/-- **The sphere drawing of a wall drawn as in Fig. 1.** Composing the drawing of Fig. 1 with the
plane homeomorphism of `IsFigure1` and the inclusion of the plane in its one-point
compactification (a sphere) gives a drawing of the wall graph itself in the sphere, with point
set the image of `U(H)` and with each vertex drawn at the image of its point. This is the
drawing "taking $\Sigma$ to be a sphere, and taking $\Gamma = H$" of the proof of (7.4). -/
theorem DrawnWall.IsFigure1.exists_sphereDrawing {W : DrawnWall α β} (hW : W.IsFigure1) :
    ∃ Γ : GraphDrawing W.graph (OnePoint EuclideanPlane),
      Γ.drawing.U = (↑) '' W.drawingU ∧
      ∀ v : V(W.graph), (Γ.iso.vertexEquiv v).1 = ((W.vertexPoint v.1 : EuclideanPlane) :
        OnePoint EuclideanPlane) := by
  obtain ⟨φ, Γ₀, hΓ₀, hU, hv⟩ := hW
  have hUc : IsCompact Γ₀.drawing.U := by
    rw [hΓ₀.drawing_U_eq]; exact isCompact_fig1WallSet _
  let f : EuclideanPlane → OnePoint EuclideanPlane := fun x => ((φ x : EuclideanPlane) :
    OnePoint EuclideanPlane)
  have hf : Continuous f := OnePoint.continuous_coe.comp φ.continuous
  have hinj : InjOn f Γ₀.drawing.U := fun x _ y _ hxy =>
    φ.injective (OnePoint.coe_injective hxy)
  obtain ⟨Γ, hΓU, -, hΓv, -⟩ := GM09.GraphDrawing.transportOn Γ₀ hUc hf.continuousOn hinj
  refine ⟨Γ, ?_, fun v => ?_⟩
  · rw [hΓU, hU, image_image]
  · rw [hΓv v, hv v.1 v.2]

/-! ## The disc enclosed by the Fig. 1 wall

The rows of bricks of the elementary wall of height `h` are the rectangles
`[left y, 2h + left y] × [y, y + 1]` for `y < h`, where `left y` is `1` for even `y` and `0` for
odd `y` (the vertical edges between rows `y` and `y + 1` are at the `x` with `x + y` odd). Their
union is a stack of rectangles, and consecutive rows overlap in length `2h - 1`, so it is a closed
disc (`GM16.isClosedDisc_rectangleStack`). -/

/-- The left side of the row of bricks between rows `y` and `y + 1` of Fig. 1. -/
def fig1RowLeft (y : ℕ) : ℝ := if Even y then 1 else 0

/-- The right side of the row of bricks between rows `y` and `y + 1` of Fig. 1. -/
def fig1RowRight (h y : ℕ) : ℝ := 2 * (h : ℝ) + fig1RowLeft y

/-- The closed set enclosed by the outer cycle of the Fig. 1 wall of height `h`. -/
def fig1EnclosedSet (h : ℕ) : Set (ℝ × ℝ) :=
  GM16.rectangleStack fig1RowLeft (fig1RowRight h) h

theorem fig1RowLeft_bounds (y : ℕ) : 0 ≤ fig1RowLeft y ∧ fig1RowLeft y ≤ 1 := by
  unfold fig1RowLeft; split_ifs <;> norm_num

/-- **The set enclosed by the Fig. 1 wall is a closed disc**, in every surface the plane embeds
in. -/
theorem isClosedDisc_image_fig1EnclosedSet {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {f : (ℝ × ℝ) → S} (hf : Topology.IsEmbedding f) {h : ℕ} (hh : 1 ≤ h) :
    IsClosedDisc (f '' fig1EnclosedSet h) := by
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  refine GM16.isClosedDisc_rectangleStack hS hf fig1RowLeft (fig1RowRight h) (fun k => ?_)
    (fun k => ?_) hh
  · unfold fig1RowRight; linarith
  · have h1 := fig1RowLeft_bounds k
    have h2 := fig1RowLeft_bounds (k + 1)
    have hmax : max (fig1RowLeft k) (fig1RowLeft (k + 1)) ≤ 1 := max_le h1.2 h2.2
    have hmin : 2 * (h : ℝ) ≤ min (fig1RowRight h k) (fig1RowRight h (k + 1)) := by
      unfold fig1RowRight; exact le_min (by linarith) (by linarith)
    linarith

/-! ## The bricks of the Fig. 1 wall -/

/-- The Fig. 1 point set in `ℝ × ℝ` coordinates: the union of the unit segments of the edges of
the elementary wall. `fig1WallSet h` is its image under `fig1PlaneEquiv`. -/
def fig1Set (h : ℕ) : Set (ℝ × ℝ) :=
  ⋃ (p : ℕ × ℕ) (q : ℕ × ℕ) (_ : elementaryWallAdj h p q), fig1Segment p q

theorem fig1WallSet_eq_image_fig1Set (h : ℕ) :
    fig1WallSet h = fig1PlaneEquiv '' fig1Set h := by
  simp only [fig1WallSet, fig1Set, image_iUnion]

theorem horizontalLatticeLine_subset_fig1Set {h i j : ℕ} (hij : (i + 1, j) ∈ elementaryWallVerts h)
    (hi : (i, j) ∈ elementaryWallVerts h) :
    GM16.horizontalLatticeLine i j ⊆ fig1Set h := by
  intro z hz
  refine mem_iUnion.mpr ⟨(i, j), mem_iUnion.mpr ⟨(i + 1, j), mem_iUnion.mpr ⟨⟨hi, hij,
    Or.inl ⟨rfl, Or.inl rfl⟩⟩, ?_⟩⟩⟩
  simp only [fig1Segment]
  simpa using hz

theorem verticalLatticeLine_subset_fig1Set {h i j : ℕ} (hi : (i, j) ∈ elementaryWallVerts h)
    (hij : (i, j + 1) ∈ elementaryWallVerts h) (hodd : Odd (i + j)) :
    GM16.verticalLatticeLine i j ⊆ fig1Set h := by
  intro z hz
  refine mem_iUnion.mpr ⟨(i, j), mem_iUnion.mpr ⟨(i, j + 1), mem_iUnion.mpr ⟨⟨hi, hij,
    Or.inr ⟨rfl, Or.inl ⟨rfl, hodd⟩⟩⟩, ?_⟩⟩⟩
  simp only [fig1Segment]
  rw [ite_eq_right (by simp)]
  simpa using hz

/-- **The sides of a brick are drawn.** For `x + y` odd, `x + 2 ≤ 2h + 1` and `y + 1 ≤ h`, the
boundary of the rectangle `[x, x + 2] × [y, y + 1]` lies in the Fig. 1 set: its two horizontal
sides are two unit segments each, and its vertical sides are the vertical edges at columns `x`
and `x + 2`. -/
theorem frontier_brick_subset_fig1Set {h x y : ℕ} (he : Even h) (hx : x + 2 ≤ 2 * h + 1)
    (hy : y + 1 ≤ h) (hodd : Odd (x + y)) :
    frontier (Icc (x : ℝ) ((x : ℝ) + 2) ×ˢ Icc (y : ℝ) ((y : ℝ) + 1)) ⊆ fig1Set h := by
  obtain ⟨k, rfl⟩ := he
  obtain ⟨m, hm⟩ := hodd
  have hV : ∀ a b : ℕ, a ≤ 2 * (k + k) + 1 → b ≤ k + k → (a, b) ≠ (0, 0) →
      (a, b) ≠ (2 * (k + k) + 1, k + k) → (a, b) ∈ elementaryWallVerts (k + k) :=
    fun a b ha hb h1 h2 => ⟨ha, hb, h1, h2⟩
  have hHor : ∀ q : ℕ, (q = y ∨ q = y + 1) → ∀ z : ℝ × ℝ,
      z.1 ∈ Icc (x : ℝ) ((x : ℝ) + 2) → z.2 = (q : ℝ) → z ∈ fig1Set (k + k) := by
    intro q hq z hz1 hz2
    by_cases hcut : z.1 ≤ (x : ℝ) + 1
    · refine horizontalLatticeLine_subset_fig1Set (i := x) (j := q)
        (hV _ _ (by omega) (by omega) (by simp) ?_) (hV _ _ (by omega) (by omega) ?_ ?_) ?_
      · simp only [ne_eq, Prod.mk.injEq, not_and]; omega
      · simp only [ne_eq, Prod.mk.injEq, not_and]; omega
      · simp only [ne_eq, Prod.mk.injEq, not_and]; omega
      · exact ⟨⟨hz1.1, hcut⟩, by simpa using hz2⟩
    · refine horizontalLatticeLine_subset_fig1Set (i := x + 1) (j := q)
        (hV _ _ (by omega) (by omega) (by simp) ?_) (hV _ _ (by omega) (by omega) (by simp) ?_) ?_
      · simp only [ne_eq, Prod.mk.injEq, not_and]; omega
      · simp only [ne_eq, Prod.mk.injEq, not_and]; omega
      · refine ⟨⟨?_, ?_⟩, by simpa using hz2⟩
        · push_cast; linarith
        · push_cast; linarith [hz1.2]
  have hVer : ∀ c : ℕ, (c = x ∨ c = x + 2) → ∀ z : ℝ × ℝ,
      z.1 = (c : ℝ) → z.2 ∈ Icc (y : ℝ) ((y : ℝ) + 1) → z ∈ fig1Set (k + k) := by
    intro c hc z hz1 hz2
    refine verticalLatticeLine_subset_fig1Set (i := c) (j := y)
      (hV _ _ (by omega) (by omega) ?_ ?_) (hV _ _ (by omega) (by omega) ?_ ?_) ⟨m + (c - x) / 2,
        by omega⟩ ⟨by simpa using hz1, hz2⟩
    · simp only [ne_eq, Prod.mk.injEq, not_and]; omega
    · simp only [ne_eq, Prod.mk.injEq, not_and]; omega
    · simp only [ne_eq, Prod.mk.injEq, not_and]; omega
    · simp only [ne_eq, Prod.mk.injEq, not_and]; omega
  intro z hz
  rw [frontier_prod_eq, isClosed_Icc.closure_eq, isClosed_Icc.closure_eq,
    frontier_Icc (by linarith : (x : ℝ) ≤ (x : ℝ) + 2),
    frontier_Icc (by linarith : (y : ℝ) ≤ (y : ℝ) + 1)] at hz
  rcases hz with ⟨hz1, hz2⟩ | ⟨hz1, hz2⟩
  · rcases hz2 with hz2 | hz2
    · exact hHor y (Or.inl rfl) z hz1 hz2
    · exact hHor (y + 1) (Or.inr rfl) z hz1 (by rw [mem_singleton_iff] at hz2; simpa using hz2)
  · rcases hz1 with hz1 | hz1
    · exact hVer x (Or.inl rfl) z hz1 hz2
    · exact hVer (x + 2) (Or.inr rfl) z (by rw [mem_singleton_iff] at hz1; simpa using hz1) hz2

/-- **The inside of a brick is not drawn.** For `x + y` odd the open rectangle
`(x, x + 2) × (y, y + 1)` misses the Fig. 1 set: a horizontal segment lies on an integer
height, and the only vertical line through the open rectangle is at column `x + 1`, where
`x + 1 + y` is even, so there is no vertical edge there. -/
theorem disjoint_open_brick_fig1Set {h x y : ℕ} (hodd : Odd (x + y)) :
    Disjoint (Ioo (x : ℝ) ((x : ℝ) + 2) ×ˢ Ioo (y : ℝ) ((y : ℝ) + 1)) (fig1Set h) := by
  rw [Set.disjoint_left]
  rintro z ⟨⟨hx1, hx2⟩, hy1, hy2⟩ hz
  simp only [fig1Set, mem_iUnion] at hz
  obtain ⟨p, q, hadj, hz⟩ := hz
  unfold fig1Segment at hz
  split_ifs at hz with hpq
  · obtain ⟨-, hz2⟩ := hz
    rw [mem_singleton_iff] at hz2
    rw [hz2] at hy1 hy2
    have h1 : y < min p.2 q.2 := by exact_mod_cast hy1
    have h2 : min p.2 q.2 < y + 1 := by exact_mod_cast hy2
    omega
  · obtain ⟨hz1, hz2, hz3⟩ := hz
    rw [mem_singleton_iff] at hz1
    rw [hz1] at hx1 hx2
    have h1 : x < min p.1 q.1 := by exact_mod_cast hx1
    have h2 : min p.1 q.1 < x + 2 := by exact_mod_cast hx2
    have h3 : ((min p.2 q.2 : ℕ) : ℝ) < y + 1 := by linarith
    have h4 : (y : ℝ) < ((min p.2 q.2 : ℕ) : ℝ) + 1 := by linarith
    have h3' : min p.2 q.2 < y + 1 := by exact_mod_cast h3
    have h4' : y < min p.2 q.2 + 1 := by exact_mod_cast h4
    obtain ⟨-, -, hrow | ⟨hcol, hv⟩⟩ := hadj
    · exact hpq hrow.1
    · rcases hv with ⟨hv, ⟨c, hc⟩⟩ | ⟨hv, ⟨c, hc⟩⟩
      · rw [hcol] at h1 h2 hc; obtain ⟨m, hm⟩ := hodd
        simp only [min_self] at h1 h2
        have : min p.2 q.2 = p.2 := by omega
        omega
      · rw [hcol] at h1 h2; obtain ⟨m, hm⟩ := hodd
        simp only [min_self] at h1 h2
        have : min p.2 q.2 = q.2 := by omega
        omega

/-- A valid brick of the Fig. 1 wall of height `h`: its lower left corner `(x, y)` has `x + y`
odd, `x + 2 ≤ 2h + 1` and `y + 1 ≤ h`. -/
def IsFig1Brick (h x y : ℕ) : Prop := Odd (x + y) ∧ x + 2 ≤ 2 * h + 1 ∧ y + 1 ≤ h

/-- The closed rectangle of the brick with lower left corner `(x, y)`. -/
def fig1Brick (x y : ℕ) : Set (ℝ × ℝ) :=
  Icc (x : ℝ) ((x : ℝ) + 2) ×ˢ Icc (y : ℝ) ((y : ℝ) + 1)

/-- **The bricks cover the enclosed set**: row `y` of the enclosed set is
`[left y, left y + 2h] × [y, y + 1]`, which is the union of the `h` bricks of width two starting
at `left y`. -/
theorem exists_fig1Brick_of_mem_enclosed {h : ℕ} {z : ℝ × ℝ} (hz : z ∈ fig1EnclosedSet h) :
    ∃ x y, IsFig1Brick h x y ∧ z ∈ fig1Brick x y := by
  obtain ⟨y, hy, hzRow⟩ := mem_iUnion₂.mp hz
  have hh : 1 ≤ h := by omega
  set L : ℕ := if Even y then 1 else 0 with hL
  have hLr : fig1RowLeft y = (L : ℝ) := by
    simp only [fig1RowLeft, hL]; split_ifs <;> simp
  have hRow : z ∈ Icc (L : ℝ) ((L : ℝ) + 2 * (h : ℝ)) ×ˢ Icc (y : ℝ) ((y : ℝ) + 1) := by
    simpa only [fig1RowRight, hLr, add_comm (2 * (h : ℝ))] using hzRow
  have hTile := GM16.rectangle_eq_union_width_two (L : ℝ) (y : ℝ) ((y : ℝ) + 1) hh
  obtain ⟨k, hk, hzB⟩ := mem_iUnion₂.mp (hTile ▸ hRow)
  refine ⟨L + 2 * k, y, ⟨?_, ?_, by omega⟩, ?_⟩
  · by_cases hy2 : Even y
    · have hy2' := hy2
      obtain ⟨t, ht⟩ := hy2
      have : L = 1 := by simp [hL, hy2']
      exact ⟨k + t, by omega⟩
    · obtain ⟨t, ht⟩ := Nat.not_even_iff_odd.mp hy2
      have : L = 0 := by simp [hL, hy2]
      exact ⟨k + t, by omega⟩
  · have : L ≤ 1 := by simp only [hL]; split_ifs <;> omega
    omega
  · simpa only [fig1Brick, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hzB

/-- Every valid brick lies in the enclosed set. -/
theorem fig1Brick_subset_enclosed {h x y : ℕ} (hb : IsFig1Brick h x y) :
    fig1Brick x y ⊆ fig1EnclosedSet h := by
  obtain ⟨⟨m, hm⟩, hx, hy⟩ := hb
  intro z hz
  refine mem_iUnion₂.mpr ⟨y, by omega, ?_, hz.2⟩
  have hx' : ((x : ℝ) + 2) ≤ 2 * (h : ℝ) + 1 := by exact_mod_cast hx
  by_cases hy2 : Even y
  · obtain ⟨t, ht⟩ := hy2
    have h1 : 1 ≤ x := by omega
    have h1' : (1 : ℝ) ≤ x := by exact_mod_cast h1
    have hLv : fig1RowLeft y = 1 := ite_eq_left ⟨t, ht⟩
    simp only [fig1RowRight, hLv]
    exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  · obtain ⟨t, ht⟩ := Nat.not_even_iff_odd.mp hy2
    have h1 : x + 2 ≤ 2 * h := by omega
    have h1' : ((x : ℝ) + 2) ≤ 2 * (h : ℝ) := by exact_mod_cast h1
    have hLv : fig1RowLeft y = 0 := ite_eq_right hy2
    simp only [fig1RowRight, hLv]
    exact ⟨by linarith [hz.1.1, (Nat.cast_nonneg x : (0 : ℝ) ≤ x)], by linarith [hz.1.2]⟩

/-- A point of height in `[y, y + 1]` and abscissa in `[left y, left y + 2h]`, for `y < h`,
is in the enclosed set. -/
theorem mem_fig1EnclosedSet_of_row {h y : ℕ} (hy : y < h) {z : ℝ × ℝ}
    (hz1 : fig1RowLeft y ≤ z.1) (hz2 : z.1 ≤ 2 * (h : ℝ) + fig1RowLeft y)
    (hz3 : (y : ℝ) ≤ z.2) (hz4 : z.2 ≤ (y : ℝ) + 1) : z ∈ fig1EnclosedSet h :=
  mem_iUnion₂.mpr ⟨y, hy, ⟨hz1, hz2⟩, hz3, hz4⟩

/-- **The Fig. 1 set lies in the enclosed set.** A horizontal edge at height `j` lies in the row
of bricks just above or just below it, chosen by the parity of `j` when the edge is at an end of
its row; a vertical edge from height `j` lies in row `j`. -/
theorem fig1Set_subset_enclosed {h : ℕ} (he : Even h) (hh : 2 ≤ h) :
    fig1Set h ⊆ fig1EnclosedSet h := by
  obtain ⟨n, rfl⟩ := he
  have hL : ∀ y : ℕ, fig1RowLeft y = if Even y then 1 else 0 := fun _ => rfl
  intro z hz
  simp only [fig1Set, mem_iUnion] at hz
  obtain ⟨p, q, hadj, hz⟩ := hz
  obtain ⟨hp, hq, hrow | ⟨hcol, hv⟩⟩ := hadj
  · simp only [fig1Segment, ite_eq_left hrow.1] at hz
    obtain ⟨⟨hz1, hz2⟩, hz3⟩ := hz
    rw [mem_singleton_iff] at hz3
    -- the left end `(i, j)` and the right end `(i + 1, j)` of the edge
    obtain ⟨i, j, hi, hi1, hvi, hvi1⟩ : ∃ i j : ℕ, min p.1 q.1 = i ∧ min p.2 q.2 = j ∧
        (i, j) ∈ elementaryWallVerts (n + n) ∧ (i + 1, j) ∈ elementaryWallVerts (n + n) := by
      rcases hrow.2 with h1 | h1
      · refine ⟨p.1, p.2, by omega, by omega, hp, ?_⟩
        rw [show (p.1 + 1, p.2) = q from Prod.ext h1 hrow.1]; exact hq
      · refine ⟨q.1, q.2, by omega, by omega, hq, ?_⟩
        rw [show (q.1 + 1, q.2) = p from Prod.ext h1 hrow.1.symm]; exact hp
    rw [hi] at hz1 hz2; rw [hi1] at hz3
    obtain ⟨-, -, hne1, -⟩ := hvi
    obtain ⟨hi2, hj1, -, hne2⟩ := hvi1
    -- the row `y` used, with `left y ≤ i` and `i + 1 ≤ left y + 2h`
    obtain ⟨y, hyj, hy, hleft, hright⟩ : ∃ y : ℕ, (y = j ∨ y + 1 = j) ∧ y < n + n ∧
        ((if Even y then 1 else 0 : ℕ) ≤ i) ∧ i + 1 ≤ 2 * (n + n) + (if Even y then 1 else 0 : ℕ) := by
      by_cases hi0 : i = 0
      · subst hi0
        have hj0 : j ≠ 0 := fun h0 => hne1 (by rw [h0])
        by_cases hjo : Odd j
        · have hjn : j < n + n := by
            rcases Nat.lt_or_ge j (n + n) with h | h
            · exact h
            · exfalso; obtain ⟨m, hm⟩ := hjo; omega
          refine ⟨j, Or.inl rfl, hjn, ?_, ?_⟩ <;> rw [ite_eq_right (Nat.not_even_iff_odd.mpr hjo)] <;> omega
        · have hje : Even (j - 1 + 1) := by
            rw [Nat.sub_add_cancel (by omega)]; exact Nat.not_odd_iff_even.mp hjo
          have hjo' : ¬ Even (j - 1) := by
            intro h; obtain ⟨a, ha⟩ := h; obtain ⟨b, hb⟩ := hje; omega
          refine ⟨j - 1, Or.inr (by omega), by omega, ?_, ?_⟩ <;> rw [ite_eq_right hjo'] <;> omega
      · by_cases hi2' : i + 1 = 2 * (n + n) + 1
        · have hjh : j ≠ n + n := fun h0 => hne2 (by rw [h0, hi2'])
          by_cases hje : Even j
          · refine ⟨j, Or.inl rfl, by omega, ?_, ?_⟩ <;> rw [ite_eq_left hje] <;> omega
          · have hj0 : j ≠ 0 := by rintro rfl; exact hje ⟨0, rfl⟩
            have hje' : Even (j - 1) := by
              obtain ⟨b, hb⟩ := Nat.not_even_iff_odd.mp hje; exact ⟨b, by omega⟩
            refine ⟨j - 1, Or.inr (by omega), by omega, ?_, ?_⟩ <;> rw [ite_eq_left hje'] <;> omega
        · by_cases hjl : j < n + n
          · refine ⟨j, Or.inl rfl, hjl, ?_, ?_⟩ <;> split_ifs <;> omega
          · refine ⟨j - 1, Or.inr (by omega), by omega, ?_, ?_⟩ <;> split_ifs <;> omega
    have hLy : fig1RowLeft y = ((if Even y then 1 else 0 : ℕ) : ℝ) := by
      rw [hL]; split_ifs <;> simp
    have hleft' : ((if Even y then 1 else 0 : ℕ) : ℝ) ≤ i := by exact_mod_cast hleft
    have hright' : (i : ℝ) + 1 ≤ 2 * ((n + n : ℕ) : ℝ) + ((if Even y then 1 else 0 : ℕ) : ℝ) := by
      exact_mod_cast hright
    refine mem_fig1EnclosedSet_of_row hy (by rw [hLy]; linarith) (by rw [hLy]; linarith) ?_ ?_
    · rw [hz3]; rcases hyj with rfl | hyj
      · exact le_rfl
      · rw [← hyj]; push_cast; linarith
    · rw [hz3]; rcases hyj with rfl | hyj
      · linarith
      · rw [← hyj]; push_cast; linarith
  · -- a vertical edge from `(i, j)` to `(i, j + 1)` with `i + j` odd
    simp only [fig1Segment] at hz
    rw [ite_eq_right (by rcases hv with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega)] at hz
    obtain ⟨hz1, hz2, hz3⟩ := hz
    rw [mem_singleton_iff] at hz1
    obtain ⟨i, j, hi, hj, hodd, hjn, hin⟩ : ∃ i j : ℕ, min p.1 q.1 = i ∧ min p.2 q.2 = j ∧
        Odd (i + j) ∧ j < n + n ∧ i ≤ 2 * (n + n) + 1 := by
      rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨p.1, p.2, by omega, by omega, h2, by have := hq.2.1; omega, hp.1⟩
      · exact ⟨q.1, q.2, by omega, by omega, h2, by have := hp.2.1; omega, hq.1⟩
    rw [hi] at hz1; rw [hj] at hz2 hz3
    obtain ⟨m, hm⟩ := hodd
    have hbounds : ((if Even j then 1 else 0 : ℕ) ≤ i) ∧
        i ≤ 2 * (n + n) + (if Even j then 1 else 0 : ℕ) := by
      split_ifs with hje
      · obtain ⟨a, ha⟩ := hje; omega
      · obtain ⟨a, ha⟩ := Nat.not_even_iff_odd.mp hje; omega
    have hLy : fig1RowLeft j = ((if Even j then 1 else 0 : ℕ) : ℝ) := by
      rw [hL]; split_ifs <;> simp
    have h1 : ((if Even j then 1 else 0 : ℕ) : ℝ) ≤ i := by exact_mod_cast hbounds.1
    have h2 : (i : ℝ) ≤ 2 * ((n + n : ℕ) : ℝ) + ((if Even j then 1 else 0 : ℕ) : ℝ) := by
      exact_mod_cast hbounds.2
    exact mem_fig1EnclosedSet_of_row hjn (by rw [hLy, hz1]; exact h1)
      (by rw [hLy, hz1]; exact h2) hz2 hz3

/-! ## Every region of the Fig. 1 wall in the sphere is an open disc -/

section TwoCell

variable {S : Type*} [TopologicalSpace S] [T2Space S]

/-- The intrinsic boundary of an embedded brick is the image of the frontier of the
rectangle. -/
theorem discBd_image_fig1Brick {f : (ℝ × ℝ) → S} (hf : Topology.IsEmbedding f) (x y : ℕ) :
    IsClosedDisc (f '' fig1Brick x y) ∧
      discBd (f '' fig1Brick x y) = f '' frontier (fig1Brick x y) := by
  obtain ⟨hRect, hB⟩ := GM16.isClosedDisc_real_rectangle_with_boundary
    (by linarith : (x : ℝ) < (x : ℝ) + 2) (by linarith : (y : ℝ) < (y : ℝ) + 1)
  obtain ⟨hD, hImage⟩ := isClosedDisc_image_injOn hRect hRect.isCompact
    hf.continuous.continuousOn hf.injective.injOn
  exact ⟨hD, by rw [fig1Brick, hImage, hB]⟩

/-- **Each brick is a region** of any drawing with point set the image of the Fig. 1 set. -/
theorem fig1Brick_interior_mem_R (hS : IsClosedSurface S) {f : (ℝ × ℝ) → S}
    (hf : Topology.IsEmbedding f) {h : ℕ} (he : Even h) {D : Drawing S}
    (hU : D.U = f '' fig1Set h) {x y : ℕ} (hb : IsFig1Brick h x y) :
    interior (f '' fig1Brick x y) ∈ D.R := by
  obtain ⟨hD, hBd⟩ := discBd_image_fig1Brick hf x y
  refine (GM16.empty_disc_is_region hS hD ?_ ?_).1
  · rw [hBd, hU]
    exact image_mono (frontier_brick_subset_fig1Set he hb.2.1 hb.2.2 hb.1)
  · rw [hU, Set.disjoint_left]
    intro z hz hzU
    obtain ⟨w, hw, rfl⟩ := GM16.interior_image_rectangle_subset hf _ _ _ _ hz
    obtain ⟨w', hw', hww'⟩ := hzU
    rw [hf.injective hww'] at hw'
    exact Set.disjoint_left.mp (disjoint_open_brick_fig1Set (h := h) hb.1) hw hw'

/-- The boundary of the embedded enclosed disc is drawn: a point of it is in some brick, is not
inside that brick (it would then be inside the enclosed disc), so it is on the frontier of the
brick, which is drawn (`frontier_brick_subset_fig1Set`). -/
theorem discBd_image_enclosed_subset (hS : IsClosedSurface S) {f : (ℝ × ℝ) → S}
    (hf : Topology.IsEmbedding f) {h : ℕ} (he : Even h) (hh : 2 ≤ h) :
    discBd (f '' fig1EnclosedSet h) ⊆ f '' fig1Set h := by
  have hDisc := isClosedDisc_image_fig1EnclosedSet hS hf (by omega : 1 ≤ h)
  intro z hz
  obtain ⟨p, hp, rfl⟩ := Surface.discBd_subset _ hz
  obtain ⟨x, y, hb, hpB⟩ := exists_fig1Brick_of_mem_enclosed hp
  obtain ⟨hB, hBd⟩ := discBd_image_fig1Brick hf x y
  have hfr : f p ∈ discBd (f '' fig1Brick x y) := by
    rw [← GM11.IsClosedDisc.frontier_eq_discBd hS hB]
    refine ⟨subset_closure (mem_image_of_mem f hpB), fun hpInt => ?_⟩
    have hOut : f p ∈ frontier (f '' fig1EnclosedSet h) :=
      (GM11.IsClosedDisc.frontier_eq_discBd hS hDisc).symm ▸ hz
    exact hOut.2 (interior_mono (image_mono (fig1Brick_subset_enclosed hb)) hpInt)
  rw [hBd] at hfr
  exact image_mono (frontier_brick_subset_fig1Set he hb.2.1 hb.2.2 hb.1) hfr

/-- **The drawing of the Fig. 1 wall in a sphere is 2-cell.** Let `f` be an open embedding of
the plane in a sphere and `D` a drawing whose point set is the image of the Fig. 1 set. Every
region of `D` is an open disc: a region meeting the enclosed disc meets the inside of a brick
and is that inside; any other region is the inside of the complementary disc. -/
theorem fig1_isTwoCell (hS : IsClosedSurface S) (hSphere : IsSphere S) [ConnectedSpace S]
    {f : (ℝ × ℝ) → S} (hf : Topology.IsOpenEmbedding f) {h : ℕ} (he : Even h) (hh : 2 ≤ h)
    {D : Drawing S} (hU : D.U = f '' fig1Set h) : D.IsTwoCell := by
  refine ⟨inferInstance, fun r hr => ?_⟩
  obtain ⟨z, hzr⟩ := GM11.region_nonempty hr
  have hzU : z ∉ D.U := GM11.region_subset hr hzr
  by_cases hzE : z ∈ f '' fig1EnclosedSet h
  · obtain ⟨p, hp, rfl⟩ := hzE
    obtain ⟨x, y, hb, hpB⟩ := exists_fig1Brick_of_mem_enclosed hp
    obtain ⟨hB, -⟩ := discBd_image_fig1Brick hf.isEmbedding x y
    have hpOpen : p ∈ Ioo (x : ℝ) ((x : ℝ) + 2) ×ˢ Ioo (y : ℝ) ((y : ℝ) + 1) := by
      rw [← interior_Icc, ← interior_Icc, ← interior_prod_eq]
      by_contra hfr
      apply hzU
      rw [hU]
      exact mem_image_of_mem f
        (frontier_brick_subset_fig1Set he hb.2.1 hb.2.2 hb.1 ⟨subset_closure hpB, hfr⟩)
    have hInt : f p ∈ interior (f '' fig1Brick x y) := by
      refine interior_maximal (image_mono ?_) (hf.isOpenMap _ (isOpen_Ioo.prod isOpen_Ioo))
        (mem_image_of_mem f hpOpen)
      exact prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
    rw [GM11.region_eq_of_mem hr (fig1Brick_interior_mem_R hS hf.isEmbedding he hU hb) hzr hInt,
      GM11.interior_eq_sdiff_discBd hS hB]
    exact GM11.isOpenDisc_interior hS hB
  · have hC := isClosedDisc_image_fig1EnclosedSet hS hf.isEmbedding (by omega : 1 ≤ h)
    obtain ⟨hD, hBd, hCup, hMeet⟩ := GM16.isClosedDisc_closure_compl_of_isSphere hSphere hC
    have hDrawing : D.U ⊆ f '' fig1EnclosedSet h := by
      rw [hU]; exact image_mono (fig1Set_subset_enclosed he hh)
    have hzD : z ∈ closure (f '' fig1EnclosedSet h)ᶜ := (hCup.ge (mem_univ z)).resolve_left hzE
    have hzInt : z ∈ interior (closure (f '' fig1EnclosedSet h)ᶜ) := by
      by_contra hn
      have hzFr : z ∈ frontier (closure (f '' fig1EnclosedSet h)ᶜ) := ⟨subset_closure hzD, hn⟩
      have hzBd := GM11.IsClosedDisc.frontier_eq_discBd hS hD ▸ hzFr
      exact hzE (Surface.discBd_subset _ (hBd ▸ hzBd))
    have hBdU : discBd (closure (f '' fig1EnclosedSet h)ᶜ) ⊆ D.U := by
      rw [hBd, hU]; exact discBd_image_enclosed_subset hS hf.isEmbedding he hh
    have hEmpty : Disjoint (interior (closure (f '' fig1EnclosedSet h)ᶜ)) D.U := by
      refine Set.disjoint_left.mpr fun w hwInt hwU => ?_
      have hwBd : w ∈ discBd (f '' fig1EnclosedSet h) :=
        hMeet ▸ ⟨hDrawing hwU, interior_subset hwInt⟩
      have hwFr : w ∈ frontier (closure (f '' fig1EnclosedSet h)ᶜ) :=
        (GM11.IsClosedDisc.frontier_eq_discBd hS hD).symm ▸ (hBd.symm ▸ hwBd)
      exact hwFr.2 hwInt
    have hReg := (GM16.empty_disc_is_region hS hD hBdU hEmpty).1
    rw [GM11.region_eq_of_mem hr hReg hzr hzInt, GM11.interior_eq_sdiff_discBd hS hD]
    exact GM11.isOpenDisc_interior hS hD

end TwoCell

/-- The plane embedded in the sphere through the Fig. 1 coordinates and a homeomorphism `φ` of
the plane. -/
theorem isOpenEmbedding_fig1Sphere (φ : EuclideanPlane ≃ₜ EuclideanPlane) :
    Topology.IsOpenEmbedding (fun z : ℝ × ℝ =>
      ((φ (fig1PlaneEquiv z) : EuclideanPlane) : OnePoint EuclideanPlane)) :=
  OnePoint.isOpenEmbedding_coe.comp ((φ.isOpenEmbedding).comp fig1PlaneEquiv.isOpenEmbedding)

/-- **The sphere drawing of a Fig. 1 wall is 2-cell.** The drawing of
`DrawnWall.IsFigure1.exists_sphereDrawing` can be chosen 2-cell. -/
theorem DrawnWall.IsFigure1.exists_twoCell_sphereDrawing {W : DrawnWall α β} (hW : W.IsFigure1) :
    ∃ Γ : GraphDrawing W.graph (OnePoint EuclideanPlane),
      Γ.drawing.U = (↑) '' W.drawingU ∧
      (∀ v : V(W.graph), (Γ.iso.vertexEquiv v).1 = ((W.vertexPoint v.1 : EuclideanPlane) :
        OnePoint EuclideanPlane)) ∧ Γ.drawing.IsTwoCell := by
  obtain ⟨Γ, hΓU, hΓv⟩ := hW.exists_sphereDrawing
  refine ⟨Γ, hΓU, hΓv, ?_⟩
  obtain ⟨φ, Γ₀, hΓ₀, hU, -⟩ := hW
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  refine fig1_isTwoCell GM09.isClosedSurface_sphere hsph (isOpenEmbedding_fig1Sphere φ)
    (W.toWall.even_height) (W.toWall.two_le_height) ?_
  rw [hΓU, hU, hΓ₀.drawing_U_eq, fig1WallSet_eq_image_fig1Set, image_image, image_image]

end GraphMinor.GM13
