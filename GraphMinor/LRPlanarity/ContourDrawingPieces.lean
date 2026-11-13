module

public import GraphMinor.LRPlanarity.TreeDrawing

/-!
# The lower U paths and the pieces of the drawing

Part IV, Section 5 of `docs/planarity/planarity_test.tex` draws each back edge below the tree.
"For each matched pair of genuine port leaves i<j, draw the polygonal U-shaped path with three
segments (i,0), (i,-(j-i)), (j,-(j-i)), (j,0)." Each back edge is then "its source-port path, its
lower U path, and its target-port path".

We cut the drawing into straight pieces (`Piece`):

* `up n p`, the segment of the upper tree from an original vertex `p` to a node `n`
  (`TreeDrawing.lean`).
* `vert q`, the vertical segment below the head of the port `q`. It is the rest of the
  subdivided leaf edge of `q`, down to the leaf at height `0`, followed by the vertical side of
  the U path of `q`. These two parts lie on one vertical line, so we draw them as one segment.
* `horiz b`, the bottom side of the U path of the back edge `b`.

Each piece belongs to one edge of the graph (`Piece.owner`). The main result, `Piece.inter`,
says that pieces of distinct edges meet only at the point of an original vertex that is an end
of both. For two upper pieces this is `upSeg_inter`. The other cases follow the note.

* Vertical pieces of distinct ports have distinct horizontal coordinates.
* A vertical piece meets the upper drawing only at its own head (`vertSeg_upSeg`). An upper
  segment over the index of the port starts at an ancestor of the vertex of the port, so it
  lies at the height of the head or above.
* "Nonalternation says that their intervals are either disjoint or one is strictly inside the
  other." So the port of another back edge inside the interval of `b` belongs to a strictly
  shorter U path, and its vertical piece stops above the bottom of the U path of `b`
  (`vertSeg_horizSeg`). U paths of the same depth have disjoint intervals
  (`horizSeg_disjoint`).
* "All their interior points have y<0, so they also miss the tree drawing, which lies in y>=0."
-/

public section

namespace GraphMinor.LRPlanarity.Drawing

variable {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N} {order : ContourOrder N}

/-! ### The intervals of two back edges -/

/-- The depth `j - i` of the U path of a back edge whose ports have the indices `i < j`. -/
@[expose] noncomputable def uDepth (T : Forest N) (order : ContourOrder N) (b : Arc N) : ℕ :=
  max (portIdx T order ⟨b, true⟩) (portIdx T order ⟨b, false⟩) -
    min (portIdx T order ⟨b, true⟩) (portIdx T order ⟨b, false⟩)

/-- The two ports of a back edge have distinct indices, so its U path has positive depth. -/
theorem uDepth_pos (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {b : Arc N}
    (hb : T.BackEdge G b) : 0 < uDepth T order b := by
  have := portIdx_ne hT hO (p := ⟨b, true⟩) (q := ⟨b, false⟩) hb (by simp)
  unfold uDepth
  omega

/-- Part IV, Section 5: "Nonalternation says that their intervals are either disjoint or one
is strictly inside the other." Here all four ends are distinct. -/
theorem port_intervals (hT : T.IsDFS G) (hO : ValidContourOrder T G order)
    (hN : Nonalternating (contourWord T order)) {b c : Arc N} (hb : T.BackEdge G b)
    (hc : T.BackEdge G c) (hbc : b ≠ c) :
    let i := portIdx T order ⟨b, true⟩
    let j := portIdx T order ⟨b, false⟩
    let k := portIdx T order ⟨c, true⟩
    let l := portIdx T order ⟨c, false⟩
    i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      ¬ AlternatingIndices i j k l := by
  refine ⟨portIdx_ne hT hO hb (by simp), portIdx_ne hT hO hb (by simp [hbc]),
    portIdx_ne hT hO hb (by simp [hbc]), portIdx_ne hT hO hb (by simp [hbc]),
    portIdx_ne hT hO hb (by simp [hbc]), portIdx_ne hT hO hc (by simp),
    not_alternating_portIdx hT hO hN hb hc hbc⟩

/-- A port of another back edge inside the interval of `b` belongs to a shorter U path. -/
theorem uDepth_lt_of_mem (hT : T.IsDFS G) (hO : ValidContourOrder T G order)
    (hN : Nonalternating (contourWord T order)) {b : Arc N} {q : Port N}
    (hb : T.BackEdge G b) (hq : T.BackEdge G q.edge) (hbq : b ≠ q.edge)
    (h₁ : min (portIdx T order ⟨b, true⟩) (portIdx T order ⟨b, false⟩) ≤ portIdx T order q)
    (h₂ : portIdx T order q ≤ max (portIdx T order ⟨b, true⟩) (portIdx T order ⟨b, false⟩)) :
    uDepth T order q.edge < uDepth T order b := by
  obtain ⟨c, s⟩ := q
  dsimp only at hq hbq h₁ h₂ ⊢
  have h := port_intervals hT hO hN hb hq hbq
  simp only at h
  unfold AlternatingIndices at h
  unfold uDepth
  cases s <;> omega

/-- U paths of two distinct back edges with the same depth have disjoint intervals. -/
theorem port_intervals_of_uDepth_eq (hT : T.IsDFS G) (hO : ValidContourOrder T G order)
    (hN : Nonalternating (contourWord T order)) {b c : Arc N} (hb : T.BackEdge G b)
    (hc : T.BackEdge G c) (hbc : b ≠ c) (hd : uDepth T order b = uDepth T order c) :
    max (portIdx T order ⟨b, true⟩) (portIdx T order ⟨b, false⟩) <
        min (portIdx T order ⟨c, true⟩) (portIdx T order ⟨c, false⟩) ∨
      max (portIdx T order ⟨c, true⟩) (portIdx T order ⟨c, false⟩) <
        min (portIdx T order ⟨b, true⟩) (portIdx T order ⟨b, false⟩) := by
  have h := port_intervals hT hO hN hb hc hbc
  simp only at h
  unfold AlternatingIndices at h
  unfold uDepth at hd
  omega

/-! ### The lower pieces -/

/-- The bottom corner `(i, -(j-i))` of the U path below the port with index `i`. -/
@[expose] noncomputable def lowPt (T : Forest N) (order : ContourOrder N) (p : Port N) : ℂ :=
  ⟨portIdx T order p, -(uDepth T order p.edge : ℝ)⟩

/-- The vertical segment from the head of a port down to the corner of its U path: the
subdivided leaf edge of the port, followed by the vertical side of the U path. -/
@[expose] noncomputable def vertSeg (T : Forest N) (order : ContourOrder N) (p : Port N) : Set ℂ :=
  segment ℝ ((Node.head p).pos T order) (lowPt T order p)

/-- The bottom side of the U path of a back edge. -/
@[expose] noncomputable def horizSeg (T : Forest N) (order : ContourOrder N) (b : Arc N) : Set ℂ :=
  segment ℝ (lowPt T order ⟨b, true⟩) (lowPt T order ⟨b, false⟩)

@[simp] theorem lowPt_re (p : Port N) : (lowPt T order p).re = portIdx T order p := rfl

@[simp] theorem lowPt_im (p : Port N) : (lowPt T order p).im = -(uDepth T order p.edge : ℝ) :=
  rfl

@[simp] theorem Node.x_head (p : Port N) : (Node.head p).x T order = portIdx T order p := rfl

/-- The vertical piece of a port lies on the vertical line of its index, from the bottom of
its U path up to its head. -/
theorem vertSeg_coords (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {q : Port N}
    (hq : T.BackEdge G q.edge) {z : ℂ} (hz : z ∈ vertSeg T order q) :
    z.re = portIdx T order q ∧ -(uDepth T order q.edge : ℝ) ≤ z.im ∧
      z.im ≤ (leafDepth T order : ℝ) - T.depth (portVertex q) - 1 := by
  obtain ⟨t, ht0, ht1, hre, him⟩ := segment_coords hz
  simp only [Node.pos_re, Node.x_head, lowPt_re, Node.pos_im, Node.depth_head, lowPt_im] at hre him
  refine ⟨by rw [hre]; ring, ?_⟩
  have hD : (T.depth (portVertex q) : ℝ) + 1 ≤ leafDepth T order := by
    exact_mod_cast head_depth_le_leafDepth hT hO hq
  have hm : (0 : ℝ) ≤ uDepth T order q.edge := Nat.cast_nonneg _
  have := convex_comb_mem (lo := -(uDepth T order q.edge : ℝ))
    (hi := (leafDepth T order : ℝ) - ↑(T.depth (portVertex q) + 1)) ht0 ht1
    (a := (leafDepth T order : ℝ) - ↑(T.depth (portVertex q) + 1))
    (b := -(uDepth T order q.edge : ℝ)) ⟨by push_cast; linarith, le_rfl⟩
    ⟨le_rfl, by push_cast; linarith⟩
  rw [him]
  push_cast at this ⊢
  constructor <;> linarith [this.1, this.2]

/-- The bottom side of a U path lies on the line `y = -(j-i)`, between `i` and `j`. -/
theorem horizSeg_coords {b : Arc N} {z : ℂ} (hz : z ∈ horizSeg T order b) :
    z.im = -(uDepth T order b : ℝ) ∧
      ((min (portIdx T order ⟨b, true⟩) (portIdx T order ⟨b, false⟩) : ℕ) : ℝ) ≤ z.re ∧
      z.re ≤ ((max (portIdx T order ⟨b, true⟩) (portIdx T order ⟨b, false⟩) : ℕ) : ℝ) := by
  obtain ⟨t, ht0, ht1, hre, him⟩ := segment_coords hz
  simp only [lowPt_re, lowPt_im] at hre him
  refine ⟨by rw [him]; ring, ?_⟩
  have := convex_comb_mem
    (lo := ((min (portIdx T order ⟨b, true⟩) (portIdx T order ⟨b, false⟩) : ℕ) : ℝ))
    (hi := ((max (portIdx T order ⟨b, true⟩) (portIdx T order ⟨b, false⟩) : ℕ) : ℝ)) ht0 ht1
    (a := (portIdx T order ⟨b, true⟩ : ℝ)) (b := (portIdx T order ⟨b, false⟩ : ℝ))
    ⟨Nat.cast_le.2 (min_le_left _ _), Nat.cast_le.2 (le_max_left _ _)⟩
    ⟨Nat.cast_le.2 (min_le_right _ _), Nat.cast_le.2 (le_max_right _ _)⟩
  rw [hre]
  exact this

/-- A vertical piece meets an upper segment only at its own head. -/
theorem vertSeg_upSeg (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {q : Port N}
    {n : Node N} {p : Fin N} (hq : T.BackEdge G q.edge) (hv : n.Valid T G) (hp : n.Parent T p)
    {z : ℂ} (h₁ : z ∈ vertSeg T order q) (h₂ : z ∈ upSeg T order n p) :
    n = Node.head q ∧ z = (Node.head q).pos T order := by
  obtain ⟨hre, -, him⟩ := vertSeg_coords hT hO hq h₁
  have r := upSeg_re_mem hT hO hv hp h₂
  have i := upSeg_im_mem hT hp h₂
  rw [hre] at r
  have hm : leftIdx T order p ≤ portIdx T order q ∧ portIdx T order q ≤ rightIdx T order p :=
    ⟨by exact_mod_cast r.1, by exact_mod_cast r.2⟩
  have ha := (leafIdx_mem_iff hT hO ((mem_leafWord hT hO (.port q)).2 hq) p).1 hm
  simp only [Leaf.vertex_port] at ha
  have hd₁ := depth_le hT ha
  have hd₂ : T.depth (portVertex q) ≤ T.depth p := by
    have : (T.depth (portVertex q) : ℝ) ≤ T.depth p := by linarith
    exact_mod_cast this
  have hpq : p = portVertex q := eq_of_ancestor_of_depth_eq hT ha (by omega)
  have hd : (T.depth p : ℝ) = T.depth (portVertex q) := by rw [hpq]
  have e := upSeg_eq_bot hT hp h₂ (by linarith)
  have e' : z = (Node.head q).pos T order := by
    apply Complex.ext
    · simp [hre]
    · simp only [Node.pos_im, Node.depth_head]
      push_cast
      linarith
  exact ⟨Node.pos_injective hT hO hv hq (e.symm.trans e'), e'⟩

/-- Vertical pieces of distinct ports are disjoint. -/
theorem vertSeg_disjoint (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {q q' : Port N}
    (hq : T.BackEdge G q.edge) (hq' : T.BackEdge G q'.edge) (hne : q ≠ q') {z : ℂ}
    (h₁ : z ∈ vertSeg T order q) (h₂ : z ∈ vertSeg T order q') : False := by
  have e₁ := (vertSeg_coords hT hO hq h₁).1
  have e₂ := (vertSeg_coords hT hO hq' h₂).1
  have : portIdx T order q = portIdx T order q' := by exact_mod_cast e₁.symm.trans e₂
  exact portIdx_ne hT hO hq hne this

/-- U paths lie below the upper drawing. -/
theorem horizSeg_upSeg (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {b : Arc N}
    {n : Node N} {p : Fin N} (hb : T.BackEdge G b) (hp : n.Parent T p) {z : ℂ}
    (h₁ : z ∈ horizSeg T order b) (h₂ : z ∈ upSeg T order n p) : False := by
  have e := (horizSeg_coords h₁).1
  have i := upSeg_im_mem hT hp h₂
  have hm : (1 : ℝ) ≤ uDepth T order b := by exact_mod_cast uDepth_pos hT hO hb
  have hD : (T.depth p : ℝ) + 1 ≤ leafDepth T order := by
    exact_mod_cast vertex_depth_lt_leafDepth hT hO p
  linarith

/-- A vertical piece meets the bottom of a U path only when the port belongs to that back edge,
and then only at its own corner. -/
theorem vertSeg_horizSeg (hT : T.IsDFS G) (hO : ValidContourOrder T G order)
    (hN : Nonalternating (contourWord T order)) {q : Port N} {b : Arc N}
    (hq : T.BackEdge G q.edge) (hb : T.BackEdge G b) {z : ℂ} (h₁ : z ∈ vertSeg T order q)
    (h₂ : z ∈ horizSeg T order b) : q.edge = b ∧ z = lowPt T order q := by
  obtain ⟨hre, hlo, -⟩ := vertSeg_coords hT hO hq h₁
  obtain ⟨him, r₁, r₂⟩ := horizSeg_coords h₂
  by_cases hqb : q.edge = b
  · refine ⟨hqb, Complex.ext (by simp [hre]) (by simp [him, hqb])⟩
  · exfalso
    rw [hre] at r₁ r₂
    have hlt := uDepth_lt_of_mem hT hO hN hb hq (Ne.symm hqb) (Nat.cast_le.1 r₁)
      (Nat.cast_le.1 r₂)
    have : (uDepth T order q.edge : ℝ) + 1 ≤ uDepth T order b := by exact_mod_cast hlt
    linarith

/-- The bottoms of distinct U paths are disjoint. -/
theorem horizSeg_disjoint (hT : T.IsDFS G) (hO : ValidContourOrder T G order)
    (hN : Nonalternating (contourWord T order)) {b c : Arc N} (hb : T.BackEdge G b)
    (hc : T.BackEdge G c) (hbc : b ≠ c) {z : ℂ} (h₁ : z ∈ horizSeg T order b)
    (h₂ : z ∈ horizSeg T order c) : False := by
  obtain ⟨e₁, r₁, s₁⟩ := horizSeg_coords h₁
  obtain ⟨e₂, r₂, s₂⟩ := horizSeg_coords h₂
  have hd : uDepth T order b = uDepth T order c := by
    have : (uDepth T order b : ℝ) = uDepth T order c := by linarith
    exact_mod_cast this
  rcases port_intervals_of_uDepth_eq hT hO hN hb hc hbc hd with h | h
  · have := (Nat.cast_le (α := ℝ)).2 (Nat.succ_le_of_lt h)
    rw [Nat.cast_succ] at this
    linarith
  · have := (Nat.cast_le (α := ℝ)).2 (Nat.succ_le_of_lt h)
    rw [Nat.cast_succ] at this
    linarith

/-- No vertical piece passes through the point of an original vertex. -/
theorem vertex_notMem_vertSeg (hT : T.IsDFS G) (hO : ValidContourOrder T G order)
    {q : Port N} (hq : T.BackEdge G q.edge) (w : Fin N) :
    (Node.vertex w).pos T order ∉ vertSeg T order q := by
  intro h
  obtain ⟨hre, -, him⟩ := vertSeg_coords hT hO hq h
  have hx := Node.x_mem hT hO (Node.vertex w)
  simp only [Node.pos_re] at hre
  rw [hre] at hx
  have hm : leftIdx T order w ≤ portIdx T order q ∧ portIdx T order q ≤ rightIdx T order w :=
    ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩
  have ha := (leafIdx_mem_iff hT hO ((mem_leafWord hT hO (.port q)).2 hq) w).1 hm
  simp only [Leaf.vertex_port] at ha
  have hd := depth_le hT ha
  simp only [Node.pos_im, Node.depth_vertex] at him
  have : (T.depth (portVertex q) : ℝ) + 1 ≤ T.depth w := by linarith
  have : T.depth (portVertex q) + 1 ≤ T.depth w := by exact_mod_cast this
  omega

/-- No U path passes through the point of an original vertex. -/
theorem vertex_notMem_horizSeg (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {b : Arc N}
    (w : Fin N) : (Node.vertex w).pos T order ∉ horizSeg T order b := by
  intro h
  have e := (horizSeg_coords h).1
  simp only [Node.pos_im, Node.depth_vertex] at e
  have hD : (T.depth w : ℝ) + 1 ≤ leafDepth T order := by
    exact_mod_cast vertex_depth_lt_leafDepth hT hO w
  have hm : (0 : ℝ) ≤ uDepth T order b := Nat.cast_nonneg _
  linarith

/-! ### Pieces and their edges -/

/-- The straight pieces of the drawing. -/
inductive Piece (N : ℕ) where
  | up : Node N → Fin N → Piece N
  | vert : Port N → Piece N
  | horiz : Arc N → Piece N

/-- The segment of a piece. -/
@[expose] noncomputable def Piece.set (T : Forest N) (order : ContourOrder N) : Piece N → Set ℂ
  | up n p => upSeg T order n p
  | vert q => vertSeg T order q
  | horiz b => horizSeg T order b

/-- The pieces that occur in the drawing. -/
@[expose] def Piece.Valid (T : Forest N) (G : SimpleGraph (Fin N)) : Piece N → Prop
  | up n p => n.Valid T G ∧ n.Parent T p
  | vert q => T.BackEdge G q.edge
  | horiz b => T.BackEdge G b

/-- The edge of the graph to which a piece belongs. -/
@[expose] def Piece.owner : Piece N → Sym2 (Fin N)
  | up (.vertex c) p => s(c, p)
  | up (.head q) _ => s(q.edge.1, q.edge.2)
  | vert q => s(q.edge.1, q.edge.2)
  | horiz b => s(b.1, b.2)

/-- The original vertices whose points are ends of a piece. -/
@[expose] def Piece.IsEnd : Piece N → Fin N → Prop
  | up n p, w => n.IsEnd p w
  | vert _, _ => False
  | horiz _, _ => False

private theorem Node.Parent.unique {n : Node N} {p₁ p₂ : Fin N} (h₁ : n.Parent T p₁)
    (h₂ : n.Parent T p₂) : p₁ = p₂ := by
  cases n with
  | vertex c => exact Option.some_injective _ ((show T.parent c = some p₁ from h₁).symm.trans h₂)
  | head q => exact (show portVertex q = p₁ from h₁).symm.trans h₂

private theorem Piece.inter_up_vert (hT : T.IsDFS G) (hO : ValidContourOrder T G order)
    {n : Node N} {p : Fin N} {q : Port N} (hv : n.Valid T G) (hp : n.Parent T p)
    (hq : T.BackEdge G q.edge) (hne : (Piece.up n p).owner ≠ (Piece.vert q).owner) {z : ℂ}
    (h₁ : z ∈ upSeg T order n p) (h₂ : z ∈ vertSeg T order q) : False := by
  obtain ⟨rfl, -⟩ := vertSeg_upSeg hT hO hq hv hp h₂ h₁
  exact hne rfl

/-- Pieces of distinct edges meet only at the point of an original vertex that is an end of
both. -/
theorem Piece.inter (hT : T.IsDFS G) (hO : ValidContourOrder T G order)
    (hN : Nonalternating (contourWord T order)) {P Q : Piece N} (hP : P.Valid T G)
    (hQ : Q.Valid T G) (hne : P.owner ≠ Q.owner) {z : ℂ} (h₁ : z ∈ P.set T order)
    (h₂ : z ∈ Q.set T order) :
    ∃ w, z = (Node.vertex w).pos T order ∧ P.IsEnd w ∧ Q.IsEnd w := by
  cases P with
  | up n₁ p₁ =>
    cases Q with
    | up n₂ p₂ =>
      have hn : n₁ ≠ n₂ := by
        rintro rfl
        exact hne (by rw [Node.Parent.unique hP.2 hQ.2])
      exact upSeg_inter hT hO hP.1 hQ.1 hP.2 hQ.2 hn h₁ h₂
    | vert q => exact (Piece.inter_up_vert hT hO hP.1 hP.2 hQ hne h₁ h₂).elim
    | horiz b => exact (horizSeg_upSeg hT hO hQ hP.2 h₂ h₁).elim
  | vert q =>
    cases Q with
    | up n p => exact (Piece.inter_up_vert hT hO hQ.1 hQ.2 hP (Ne.symm hne) h₂ h₁).elim
    | vert q' =>
      have hqq : q ≠ q' := by
        rintro rfl
        exact hne rfl
      exact (vertSeg_disjoint hT hO hP hQ hqq h₁ h₂).elim
    | horiz b =>
      obtain ⟨hqb, -⟩ := vertSeg_horizSeg hT hO hN hP hQ h₁ h₂
      exact (hne (by simp only [Piece.owner, hqb])).elim
  | horiz b =>
    cases Q with
    | up n p => exact (horizSeg_upSeg hT hO hP hQ.2 h₁ h₂).elim
    | vert q =>
      obtain ⟨hqb, -⟩ := vertSeg_horizSeg hT hO hN hQ hP h₂ h₁
      exact (hne (by simp only [Piece.owner, hqb])).elim
    | horiz c =>
      have hbc : b ≠ c := by
        rintro rfl
        exact hne rfl
      exact (horizSeg_disjoint hT hO hN hP hQ hbc h₁ h₂).elim

/-- A piece passes through the point of an original vertex only at its own ends. -/
theorem Piece.isEnd_of_mem (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {P : Piece N}
    (hP : P.Valid T G) {w : Fin N} (hw : (Node.vertex w).pos T order ∈ P.set T order) :
    P.IsEnd w := by
  cases P with
  | up n p => exact vertex_mem_upSeg hT hO hP.1 hP.2 hw
  | vert q => exact vertex_notMem_vertSeg hT hO hP w hw
  | horiz b => exact vertex_notMem_horizSeg hT hO w hw

end GraphMinor.LRPlanarity.Drawing
