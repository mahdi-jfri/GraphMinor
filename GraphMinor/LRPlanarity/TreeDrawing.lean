module

public import GraphMinor.LRPlanarity.TreeDrawingWord
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Complex.Basic

/-!
# The upper tree drawing

Part IV, Section 5 of `docs/planarity/planarity_test.tex` draws the expanded search tree with
explicit coordinates. "For an internal vertex z, let L(z) and R(z) be the smallest and
largest indices of its descendant leaves, and put pos(z)=((L(z)+R(z))/2, D-depth(z))." Every tree
edge is drawn as its straight segment.

Here `D` is `leafDepth`, the largest depth of a leaf, and leaves are numbered from `0`. The
drawing uses two kinds of nodes (`Node`). An original vertex `v` sits at
`((L(v)+R(v))/2, D - depth(v))`. Below the vertex at which a port is attached, the leaf edge
of the port is subdivided until the leaf has depth `D`. Each subdivision vertex has the single
descendant leaf `i` of the port, so it sits at `(i, D - depth)`. The first of these vertices,
or the leaf itself when no subdivision is needed, is the node `Node.head`. The other
subdivision vertices lie on one vertical line below it, and they are handled with the lower
part of the drawing in `ContourDrawingPieces.lean`.

The main result, `upSeg_inter`, is the note's argument that "tree-edge images meet only at
common endpoints". Descendant intervals of distinct nodes of the same depth are disjoint
(`Node.disjoint`), so segments from distinct parents in one level strip have disjoint
horizontal ranges. Segments from one parent end at distinct points of the next level, so they
meet only at the parent. Segments in strips that are not adjacent do not meet, and segments in
adjacent strips meet only on their common boundary line, where distinct nodes have distinct
positions (`Node.pos_injective`).
-/

public section

namespace GraphMinor.LRPlanarity.Drawing

variable {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N} {order : ContourOrder N}

/-! ### Segments in coordinates -/

/-- A point of a segment of `ℂ`, in coordinates. -/
theorem segment_coords {a b z : ℂ} (h : z ∈ segment ℝ a b) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z.re = a.re + t * (b.re - a.re) ∧
      z.im = a.im + t * (b.im - a.im) := by
  rw [segment_eq_image'] at h
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := h
  refine ⟨t, ht0, ht1, ?_, ?_⟩ <;> simp

/-- A convex combination of two numbers in an interval lies in the interval. -/
theorem convex_comb_mem {lo hi a b t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : lo ≤ a ∧ a ≤ hi)
    (hb : lo ≤ b ∧ b ≤ hi) : lo ≤ a + t * (b - a) ∧ a + t * (b - a) ≤ hi := by
  have e : a + t * (b - a) = (1 - t) * a + t * b := by ring
  rw [e]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left ha.1 (sub_nonneg.2 ht1),
      mul_le_mul_of_nonneg_left hb.1 ht0]
  · nlinarith [mul_le_mul_of_nonneg_left ha.2 (sub_nonneg.2 ht1),
      mul_le_mul_of_nonneg_left hb.2 ht0]

/-! ### Nodes of the expanded tree and their positions -/

/-- The nodes of the expanded tree that the upper drawing uses: original vertices, and for each
port the first vertex below its original vertex on the subdivided leaf edge of the port. -/
inductive Node (N : ℕ) where
  | vertex : Fin N → Node N
  | head : Port N → Node N
  deriving DecidableEq

namespace Node

/-- The depth of a node in the expanded tree. -/
@[expose] def depth (T : Forest N) : Node N → ℕ
  | vertex v => T.depth v
  | head p => T.depth (portVertex p) + 1

/-- The smallest index of a descendant leaf of a node. -/
@[expose] noncomputable def lo (T : Forest N) (order : ContourOrder N) : Node N → ℕ
  | vertex v => leftIdx T order v
  | head p => portIdx T order p

/-- The largest index of a descendant leaf of a node. -/
@[expose] noncomputable def hi (T : Forest N) (order : ContourOrder N) : Node N → ℕ
  | vertex v => rightIdx T order v
  | head p => portIdx T order p

/-- The horizontal coordinate `(L(z)+R(z))/2` of a node. -/
@[expose] noncomputable def x (T : Forest N) (order : ContourOrder N) : Node N → ℝ
  | vertex v => ((leftIdx T order v : ℝ) + rightIdx T order v) / 2
  | head p => portIdx T order p

/-- The nodes that occur: all original vertices, and the heads of ports of back edges. -/
@[expose] def Valid (T : Forest N) (G : SimpleGraph (Fin N)) : Node N → Prop
  | vertex _ => True
  | head p => T.BackEdge G p.edge

/-- The parent of a node, which is always an original vertex. -/
@[expose] def Parent (T : Forest N) : Node N → Fin N → Prop
  | vertex c, p => T.parent c = some p
  | head q, p => portVertex q = p

/-- The original vertices among the two ends of the segment from the parent `p` to `n`. -/
@[expose] def IsEnd (n : Node N) (p w : Fin N) : Prop := w = p ∨ n = vertex w

end Node

/-- Part IV, Section 5: "Let D be their maximum depth", the largest depth of a leaf. -/
noncomputable def leafDepth (T : Forest N) (order : ContourOrder N) : ℕ :=
  (leafWord T order).toFinset.sup fun ℓ => T.depth ℓ.vertex + 1

/-- The position `(x, D - depth)` of a node. -/
@[expose] noncomputable def Node.pos (T : Forest N) (order : ContourOrder N) (n : Node N) : ℂ :=
  ⟨n.x T order, (leafDepth T order : ℝ) - n.depth T⟩

/-- The straight segment from an original vertex `p` to a node `n`. It is the drawing of the
tree edge from `p` to `n` when `n` is a child of `p`. -/
@[expose] noncomputable def upSeg (T : Forest N) (order : ContourOrder N) (n : Node N) (p : Fin N) :
    Set ℂ :=
  segment ℝ ((Node.vertex p).pos T order) (n.pos T order)

@[simp] theorem Node.depth_vertex (v : Fin N) : (Node.vertex v).depth T = T.depth v := rfl

@[simp] theorem Node.depth_head (p : Port N) :
    (Node.head p).depth T = T.depth (portVertex p) + 1 := rfl

theorem Node.valid_vertex (v : Fin N) : (Node.vertex v).Valid T G := trivial

@[simp] theorem Node.pos_re (n : Node N) : (n.pos T order).re = n.x T order := rfl

@[simp] theorem Node.pos_im (n : Node N) :
    (n.pos T order).im = (leafDepth T order : ℝ) - n.depth T := rfl

theorem depth_lt_leafDepth {ℓ : Leaf N} (h : ℓ ∈ leafWord T order) :
    T.depth ℓ.vertex + 1 ≤ leafDepth T order :=
  Finset.le_sup (f := fun ℓ : Leaf N => T.depth ℓ.vertex + 1) (List.mem_toFinset.2 h)

/-- "Every original vertex has a descendant leaf at strictly larger depth." -/
theorem vertex_depth_lt_leafDepth (hT : T.IsDFS G) (hO : ValidContourOrder T G order)
    (v : Fin N) : T.depth v + 1 ≤ leafDepth T order := by
  obtain ⟨ℓ, hl, ha⟩ := exists_leaf hT hO _ v rfl
  have := depth_lt_leafDepth ((mem_leafWord hT hO ℓ).2 hl)
  have := depth_le hT ha
  omega

theorem head_depth_le_leafDepth (hT : T.IsDFS G) (hO : ValidContourOrder T G order)
    {p : Port N} (hp : T.BackEdge G p.edge) : T.depth (portVertex p) + 1 ≤ leafDepth T order :=
  depth_lt_leafDepth (ℓ := .port p) ((mem_leafWord hT hO _).2 hp)

theorem Node.lo_le_hi (hT : T.IsDFS G) (hO : ValidContourOrder T G order) (n : Node N) :
    n.lo T order ≤ n.hi T order := by
  cases n with
  | vertex v => exact leftIdx_le_rightIdx hT hO v
  | head p => exact le_rfl

theorem Node.x_mem (hT : T.IsDFS G) (hO : ValidContourOrder T G order) (n : Node N) :
    (n.lo T order : ℝ) ≤ n.x T order ∧ n.x T order ≤ n.hi T order := by
  cases n with
  | vertex v =>
    have : (leftIdx T order v : ℝ) ≤ rightIdx T order v := by
      exact_mod_cast leftIdx_le_rightIdx hT hO v
    simp only [Node.lo, Node.hi, Node.x]
    constructor <;> linarith
  | head p => exact ⟨le_rfl, le_rfl⟩

theorem Node.Parent.depth_eq (hT : T.IsDFS G) {n : Node N} {p : Fin N} (h : n.Parent T p) :
    n.depth T = T.depth p + 1 := by
  cases n with
  | vertex c => exact depth_child hT h
  | head q =>
    simp only [Node.Parent] at h
    simp only [Node.depth, h]

/-- The interval of a node lies inside the interval of its parent. -/
theorem Node.Parent.interval (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {n : Node N}
    {p : Fin N} (hv : n.Valid T G) (h : n.Parent T p) :
    leftIdx T order p ≤ n.lo T order ∧ n.hi T order ≤ rightIdx T order p := by
  cases n with
  | vertex c => exact interval_mono hT hO (ancestor_of_parent h)
  | head q =>
    simp only [Node.Parent] at h
    have hq : Leaf.port q ∈ leafWord T order := (mem_leafWord hT hO _).2 hv
    have := (leafIdx_mem_iff hT hO hq p).2 (by rw [Leaf.vertex_port, h]; exact ancestor_refl p)
    exact this

/-- Part IV, Section 5: "descendant-leaf intervals of distinct vertices at the same depth are
disjoint." Here the nodes include the heads of ports. -/
theorem Node.disjoint (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {n₁ n₂ : Node N}
    (hv₁ : n₁.Valid T G) (hv₂ : n₂.Valid T G) (hne : n₁ ≠ n₂) (hd : n₁.depth T = n₂.depth T) :
    n₁.hi T order < n₂.lo T order ∨ n₂.hi T order < n₁.lo T order := by
  have key : ∀ (v : Fin N) (q : Port N), T.BackEdge G q.edge →
      T.depth v = T.depth (portVertex q) + 1 →
      rightIdx T order v < portIdx T order q ∨ portIdx T order q < leftIdx T order v := by
    intro v q hq hdq
    by_contra hc
    have hm := (leafIdx_mem_iff hT hO ((mem_leafWord hT hO (.port q)).2 hq) v).1
      (by unfold portIdx at hc; omega)
    have := depth_le hT hm
    simp only [Leaf.vertex_port] at this
    omega
  cases n₁ with
  | vertex v =>
    cases n₂ with
    | vertex w =>
      exact interval_disjoint_of_depth_eq hT hO (fun h => hne (by rw [h])) hd
    | head q =>
      rcases key v q hv₂ hd with h | h
      · exact Or.inl h
      · exact Or.inr h
  | head p =>
    cases n₂ with
    | vertex w =>
      rcases key w p hv₁ hd.symm with h | h
      · exact Or.inr h
      · exact Or.inl h
    | head q =>
      have hpq : p ≠ q := fun h => hne (by rw [h])
      have := portIdx_ne hT hO hv₁ hpq
      simp only [Node.lo, Node.hi]
      omega

/-- Distinct nodes have distinct positions. -/
theorem Node.pos_injective (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {n₁ n₂ : Node N}
    (hv₁ : n₁.Valid T G) (hv₂ : n₂.Valid T G) (h : n₁.pos T order = n₂.pos T order) :
    n₁ = n₂ := by
  by_contra hne
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [Node.pos_im, Node.pos_re] at him hre
  have hd : n₁.depth T = n₂.depth T := by
    exact_mod_cast (by linarith : (n₁.depth T : ℝ) = n₂.depth T)
  have hx₁ := Node.x_mem hT hO n₁
  have hx₂ := Node.x_mem hT hO n₂
  rcases Node.disjoint hT hO hv₁ hv₂ hne hd with h' | h'
  · have : (n₁.hi T order : ℝ) + 1 ≤ n₂.lo T order := by exact_mod_cast h'
    linarith
  · have : (n₂.hi T order : ℝ) + 1 ≤ n₁.lo T order := by exact_mod_cast h'
    linarith

/-! ### Segments of the upper drawing -/

/-- A point of the segment from the parent `p` to `n`, in coordinates. -/
theorem upSeg_coords (hT : T.IsDFS G) {n : Node N} {p : Fin N} (h : n.Parent T p) {z : ℂ}
    (hz : z ∈ upSeg T order n p) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      z.re = (Node.vertex p).x T order + t * (n.x T order - (Node.vertex p).x T order) ∧
      z.im = (leafDepth T order : ℝ) - T.depth p - t := by
  obtain ⟨t, ht0, ht1, hre, him⟩ := segment_coords hz
  refine ⟨t, ht0, ht1, by simpa using hre, ?_⟩
  rw [him]
  simp only [Node.pos_im, h.depth_eq hT, Node.depth_vertex]
  push_cast
  ring

/-- The segment from `p` to `n` lies in the level strip of `p`. -/
theorem upSeg_im_mem (hT : T.IsDFS G) {n : Node N} {p : Fin N} (h : n.Parent T p) {z : ℂ}
    (hz : z ∈ upSeg T order n p) :
    (leafDepth T order : ℝ) - T.depth p - 1 ≤ z.im ∧
      z.im ≤ (leafDepth T order : ℝ) - T.depth p := by
  obtain ⟨t, ht0, ht1, -, him⟩ := upSeg_coords hT h hz
  constructor <;> linarith

/-- The segment from `p` to `n` lies above the interval of `p`. -/
theorem upSeg_re_mem (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {n : Node N}
    {p : Fin N} (hv : n.Valid T G) (h : n.Parent T p) {z : ℂ} (hz : z ∈ upSeg T order n p) :
    (leftIdx T order p : ℝ) ≤ z.re ∧ z.re ≤ rightIdx T order p := by
  obtain ⟨t, ht0, ht1, hre, -⟩ := upSeg_coords hT h hz
  rw [hre]
  have hp := Node.x_mem hT hO (Node.vertex p)
  have hn := Node.x_mem hT hO n
  have hi := h.interval hT hO hv
  have h1 : (leftIdx T order p : ℝ) ≤ n.lo T order := by exact_mod_cast hi.1
  have h2 : (n.hi T order : ℝ) ≤ rightIdx T order p := by exact_mod_cast hi.2
  exact convex_comb_mem ht0 ht1 hp ⟨by linarith, by linarith⟩

/-- The only point of the segment on the level of `p` is the point of `p`. -/
theorem upSeg_eq_top (hT : T.IsDFS G) {n : Node N} {p : Fin N} (h : n.Parent T p) {z : ℂ}
    (hz : z ∈ upSeg T order n p) (him : z.im = (leafDepth T order : ℝ) - T.depth p) :
    z = (Node.vertex p).pos T order := by
  obtain ⟨t, ht0, ht1, hre, him'⟩ := upSeg_coords hT h hz
  have ht : t = 0 := by linarith
  subst ht
  apply Complex.ext
  · simp [hre]
  · simp [him]

/-- The only point of the segment on the level of `n` is the point of `n`. -/
theorem upSeg_eq_bot (hT : T.IsDFS G) {n : Node N} {p : Fin N} (h : n.Parent T p) {z : ℂ}
    (hz : z ∈ upSeg T order n p) (him : z.im = (leafDepth T order : ℝ) - T.depth p - 1) :
    z = n.pos T order := by
  obtain ⟨t, ht0, ht1, hre, him'⟩ := upSeg_coords hT h hz
  have ht : t = 1 := by linarith
  subst ht
  apply Complex.ext
  · simp only [hre, Node.pos_re]
    ring
  · simp only [him, Node.pos_im, h.depth_eq hT]
    push_cast
    ring

/-- The two ends of a segment of the upper drawing are distinct. -/
theorem upSeg_ends_ne (hT : T.IsDFS G) {n : Node N} {p : Fin N} (h : n.Parent T p) :
    (Node.vertex p).pos T order ≠ n.pos T order := by
  intro he
  have := congrArg Complex.im he
  simp only [Node.pos_im, h.depth_eq hT, Node.depth_vertex] at this
  push_cast at this
  linarith

/-- Segments from one parent to two nodes in adjacent strips: the case where the level of the
first child is the level of the second parent. -/
private theorem upSeg_inter_adjacent (hT : T.IsDFS G) (hO : ValidContourOrder T G order)
    {n₁ n₂ : Node N} {p₁ p₂ : Fin N} (hv₁ : n₁.Valid T G) (hp₁ : n₁.Parent T p₁)
    (hp₂ : n₂.Parent T p₂) (hd : T.depth p₂ = T.depth p₁ + 1) {z : ℂ}
    (h₁ : z ∈ upSeg T order n₁ p₁) (h₂ : z ∈ upSeg T order n₂ p₂) :
    ∃ w, z = (Node.vertex w).pos T order ∧ n₁.IsEnd p₁ w ∧ n₂.IsEnd p₂ w := by
  have i₁ := upSeg_im_mem hT hp₁ h₁
  have i₂ := upSeg_im_mem hT hp₂ h₂
  have hd' : (T.depth p₂ : ℝ) = T.depth p₁ + 1 := by exact_mod_cast hd
  have e₁ := upSeg_eq_bot hT hp₁ h₁ (by linarith)
  have e₂ := upSeg_eq_top hT hp₂ h₂ (by linarith)
  have hn : n₁ = Node.vertex p₂ :=
    Node.pos_injective hT hO hv₁ (Node.valid_vertex p₂) (e₁.symm.trans e₂)
  exact ⟨p₂, e₂, Or.inr hn, Or.inl rfl⟩

/-- Part IV, Section 5: "tree-edge images meet only at common endpoints." Two segments of the
upper drawing, to distinct nodes, meet only at the point of an original vertex that is an end
of both. -/
theorem upSeg_inter (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {n₁ n₂ : Node N}
    {p₁ p₂ : Fin N} (hv₁ : n₁.Valid T G) (hv₂ : n₂.Valid T G) (hp₁ : n₁.Parent T p₁)
    (hp₂ : n₂.Parent T p₂) (hne : n₁ ≠ n₂) {z : ℂ} (h₁ : z ∈ upSeg T order n₁ p₁)
    (h₂ : z ∈ upSeg T order n₂ p₂) :
    ∃ w, z = (Node.vertex w).pos T order ∧ n₁.IsEnd p₁ w ∧ n₂.IsEnd p₂ w := by
  have i₁ := upSeg_im_mem hT hp₁ h₁
  have i₂ := upSeg_im_mem hT hp₂ h₂
  rcases lt_trichotomy (T.depth p₁) (T.depth p₂) with hd | hd | hd
  · -- The strip of `p₂` is below the strip of `p₁`.
    have hd' : T.depth p₂ = T.depth p₁ + 1 := by
      by_contra hc
      have : (T.depth p₁ : ℝ) + 2 ≤ T.depth p₂ := by
        exact_mod_cast (by omega : T.depth p₁ + 2 ≤ T.depth p₂)
      linarith
    exact upSeg_inter_adjacent hT hO hv₁ hp₁ hp₂ hd' h₁ h₂
  · -- One level strip.
    by_cases hp : p₁ = p₂
    · subst hp
      obtain ⟨t₁, ht₁0, ht₁1, hre₁, him₁⟩ := upSeg_coords hT hp₁ h₁
      obtain ⟨t₂, ht₂0, ht₂1, hre₂, him₂⟩ := upSeg_coords hT hp₂ h₂
      have ht : t₂ = t₁ := by linarith
      subst ht
      have hx : n₁.x T order ≠ n₂.x T order := by
        intro hx
        apply hne
        apply Node.pos_injective hT hO hv₁ hv₂
        apply Complex.ext
        · simpa using hx
        · simp [hp₁.depth_eq hT, hp₂.depth_eq hT]
      have ht0 : t₂ = 0 := by
        have : t₂ * (n₁.x T order - n₂.x T order) = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · exact absurd (sub_eq_zero.1 h) hx
      refine ⟨p₁, upSeg_eq_top hT hp₁ h₁ (by rw [him₁, ht0]; ring), Or.inl rfl, Or.inl rfl⟩
    · exfalso
      have r₁ := upSeg_re_mem hT hO hv₁ hp₁ h₁
      have r₂ := upSeg_re_mem hT hO hv₂ hp₂ h₂
      rcases interval_disjoint_of_depth_eq hT hO hp hd with h | h
      · have : (rightIdx T order p₁ : ℝ) + 1 ≤ leftIdx T order p₂ := by exact_mod_cast h
        linarith
      · have : (rightIdx T order p₂ : ℝ) + 1 ≤ leftIdx T order p₁ := by exact_mod_cast h
        linarith
  · -- The strip of `p₁` is below the strip of `p₂`.
    have hd' : T.depth p₁ = T.depth p₂ + 1 := by
      by_contra hc
      have : (T.depth p₂ : ℝ) + 2 ≤ T.depth p₁ := by
        exact_mod_cast (by omega : T.depth p₂ + 2 ≤ T.depth p₁)
      linarith
    obtain ⟨w, hz, e₂, e₁⟩ := upSeg_inter_adjacent hT hO hv₂ hp₂ hp₁ hd' h₂ h₁
    exact ⟨w, hz, e₁, e₂⟩

/-- The segment from `p` to `n` passes through the point of no original vertex other than its
ends. -/
theorem vertex_mem_upSeg (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {n : Node N}
    {p w : Fin N} (hv : n.Valid T G) (h : n.Parent T p)
    (hw : (Node.vertex w).pos T order ∈ upSeg T order n p) : n.IsEnd p w := by
  have i := upSeg_im_mem hT h hw
  simp only [Node.pos_im, Node.depth_vertex] at i
  have h1 : T.depth p ≤ T.depth w := by
    have : (T.depth p : ℝ) ≤ T.depth w := by linarith
    exact_mod_cast this
  have h2 : T.depth w ≤ T.depth p + 1 := by
    have : (T.depth w : ℝ) ≤ T.depth p + 1 := by linarith
    exact_mod_cast this
  rcases Nat.lt_or_ge (T.depth p) (T.depth w) with hlt | hge
  · have hw' : T.depth w = T.depth p + 1 := by omega
    have e := upSeg_eq_bot hT h hw (by
      simp only [Node.pos_im, Node.depth_vertex, hw']
      push_cast
      ring)
    exact Or.inr (Node.pos_injective hT hO hv (Node.valid_vertex w) e.symm)
  · have hw' : T.depth w = T.depth p := by omega
    have e := upSeg_eq_top hT h hw (by simp only [Node.pos_im, Node.depth_vertex, hw'])
    exact Or.inl (by
      simpa using Node.pos_injective hT hO (Node.valid_vertex w) (Node.valid_vertex p) e)

end GraphMinor.LRPlanarity.Drawing
