module

public import GraphMinor.LRPlanarity.Statements
public import GraphMinor.LRPlanarity.ContourDrawingPieces
import GraphMinor.Surface.ArcTools
import GraphMinor.Surface.Lunes

/-!
# A nonalternating contour gives a polygonal plane drawing

This file proves `ContourDrawingStatement`, Part IV, Section 5 of
`docs/planarity/planarity_test.tex`: "This step applies to any finite rooted ordered tree with a
matching on some of its leaves whose pairs do not alternate in the leaf order."

The drawing is the one of the note. Vertices sit at the positions of the upper tree drawing
(`TreeDrawing.lean`). A tree edge is its straight segment. A back edge is "its source-port
path, its lower U path, and its target-port path": five straight pieces from its source down
to the bottom of its U path and back up to its target (`ContourDrawingPieces.lean`). After the
dummy port paths are deleted and the port and subdivision vertices are suppressed, these are the
lines of the plane embedding.

"These three pieces form a simple curve between the original endpoints." We prove this by
joining the five pieces one at a time, each new piece meeting the earlier ones only at its
first end (`isLine_backImage`). The note then says that "distinct original edges meet exactly
when they have a common endpoint, and then only there". This is the field `inter` of
`planeEmbedding`, which applies `Piece.inter` to a piece of each edge.

"For a disconnected graph, construct a drawing of each component independently and place
translated and scaled copies in disjoint rectangles." The contour word lists the components one
after the other, so the leaves of each component have a block of consecutive indices. The drawing of
a component is then its own drawing moved to the right by the number of earlier leaves, and up by
the difference of the largest leaf depths. These translated copies lie in disjoint vertical
strips, and the proofs above treat all components at once.
-/

public section

namespace GraphMinor.LRPlanarity

namespace Drawing

open Set

variable {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N} {order : ContourOrder N}

/-- The pieces of an edge `e`, oriented from its deeper end `e.1` to its other end `e.2`. A tree
edge is one segment. A back edge is its source-port path, its U path and its target-port path. -/
@[expose] def edgePieces (T : Forest N) (e : Arc N) : List (Piece N) :=
  if T.parent e.1 = some e.2 then [.up (.vertex e.1) e.2]
  else [.up (.head ⟨e, true⟩) e.1, .vert ⟨e, true⟩, .horiz e, .vert ⟨e, false⟩,
    .up (.head ⟨e, false⟩) e.2]

/-- The image of an oriented edge: the union of its pieces. -/
noncomputable def edgeImage (T : Forest N) (order : ContourOrder N) (e : Arc N) : Set ℂ :=
  ⋃ P ∈ edgePieces T e, P.set T order

open Classical in
/-- The line of the pair `u v`, oriented from the deeper end. -/
noncomputable def edgeLine (T : Forest N) (order : ContourOrder N) (u v : Fin N) : Set ℂ :=
  if T.Ancestor v u then edgeImage T order (u, v)
  else if T.Ancestor u v then edgeImage T order (v, u) else ∅

private theorem ancestor_antisymm (hT : T.IsDFS G) {u v : Fin N} (h₁ : T.Ancestor u v)
    (h₂ : T.Ancestor v u) : u = v := by
  rcases eq_or_depth_lt hT h₁ with h | h
  · exact h
  · rcases eq_or_depth_lt hT h₂ with h' | h'
    · exact h'.symm
    · omega

/-- An edge oriented from its deeper end, which is not a tree edge, is a back edge. -/
private theorem backEdge_of (hT : T.IsDFS G) {e : Arc N} (hadj : G.Adj e.1 e.2)
    (ha : T.Ancestor e.2 e.1) (hp : ¬ T.parent e.1 = some e.2) : T.BackEdge G e := by
  refine ⟨hadj, ha, ?_, hp⟩
  rcases eq_or_depth_lt hT ha with h | h
  · exact absurd h.symm hadj.ne
  · exact h

/-- The pieces of an oriented edge occur in the drawing, belong to this edge, and have only its
ends as original vertices. -/
theorem edgePieces_spec (hT : T.IsDFS G) {e : Arc N} (hadj : G.Adj e.1 e.2)
    (ha : T.Ancestor e.2 e.1) :
    ∀ P ∈ edgePieces T e, P.Valid T G ∧ P.owner = s(e.1, e.2) ∧
      ∀ w, P.IsEnd w → w = e.1 ∨ w = e.2 := by
  intro P hP
  unfold edgePieces at hP
  split_ifs at hP with hpar
  · simp only [List.mem_singleton] at hP
    subst hP
    refine ⟨⟨Node.valid_vertex _, hpar⟩, rfl, fun w hw => ?_⟩
    rcases hw with h | h
    · exact Or.inr h
    · exact Or.inl (by cases h; rfl)
  · have hb := backEdge_of hT hadj ha hpar
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl | rfl | rfl | rfl
    · refine ⟨⟨hb, portVertex_source e⟩, rfl, fun w hw => ?_⟩
      rcases hw with h | h
      · exact Or.inl h
      · cases h
    · exact ⟨hb, rfl, fun w hw => hw.elim⟩
    · exact ⟨hb, rfl, fun w hw => hw.elim⟩
    · exact ⟨hb, rfl, fun w hw => hw.elim⟩
    · refine ⟨⟨hb, portVertex_target e⟩, rfl, fun w hw => ?_⟩
      rcases hw with h | h
      · exact Or.inr h
      · cases h

private theorem inter_eq_singleton {A B : Set ℂ} {x : ℂ} (hA : x ∈ A) (hB : x ∈ B)
    (h : ∀ z ∈ A, z ∈ B → z = x) : A ∩ B = {x} :=
  Set.eq_singleton_iff_unique_mem.2 ⟨⟨hA, hB⟩, fun z hz => h z hz.1 hz.2⟩

/-- Part IV, Section 5: "These three pieces form a simple curve between the original
endpoints." The five pieces of a back edge form a line from its source to its target. -/
theorem isLine_backImage (hT : T.IsDFS G) (hO : ValidContourOrder T G order)
    (hN : Nonalternating (contourWord T order)) {b : Arc N} (hb : T.BackEdge G b) :
    Surface.IsLineWithEnds
      (upSeg T order (.head ⟨b, true⟩) b.1 ∪ vertSeg T order ⟨b, true⟩ ∪ horizSeg T order b ∪
        vertSeg T order ⟨b, false⟩ ∪ upSeg T order (.head ⟨b, false⟩) b.2)
      ((Node.vertex b.1).pos T order) ((Node.vertex b.2).pos T order) := by
  have hs : (Node.head (⟨b, true⟩ : Port N)).Parent T b.1 := portVertex_source b
  have ht : (Node.head (⟨b, false⟩ : Port N)).Parent T b.2 := portVertex_target b
  have hvs : (Node.head (⟨b, true⟩ : Port N)).Valid T G := hb
  have hvt : (Node.head (⟨b, false⟩ : Port N)).Valid T G := hb
  have hhst : (Node.head (⟨b, true⟩ : Port N)) ≠ Node.head ⟨b, false⟩ := by simp
  have hst : (⟨b, true⟩ : Port N) ≠ ⟨b, false⟩ := by simp
  have hm : (1 : ℝ) ≤ uDepth T order b := by exact_mod_cast uDepth_pos hT hO hb
  -- The ends of the five segments are distinct.
  have hl1 : Surface.IsLineWithEnds (upSeg T order (.head ⟨b, true⟩) b.1)
      ((Node.vertex b.1).pos T order) ((Node.head ⟨b, true⟩).pos T order) :=
    Surface.isLineWithEnds_segment (upSeg_ends_ne hT hs)
  have hlow : ∀ q : Port N, q.edge = b → T.depth (portVertex q) + 1 ≤ leafDepth T order →
      (Node.head q).pos T order ≠ lowPt T order q := by
    intro q hq hD he
    have := congrArg Complex.im he
    simp only [Node.pos_im, Node.depth_head, lowPt_im, hq] at this
    have hD' : ((T.depth (portVertex q) + 1 : ℕ) : ℝ) ≤ leafDepth T order := by exact_mod_cast hD
    push_cast at this hD'
    linarith
  have hl2 : Surface.IsLineWithEnds (vertSeg T order ⟨b, true⟩)
      ((Node.head ⟨b, true⟩).pos T order) (lowPt T order ⟨b, true⟩) :=
    Surface.isLineWithEnds_segment (hlow _ rfl (head_depth_le_leafDepth hT hO hb))
  have hl3 : Surface.IsLineWithEnds (horizSeg T order b) (lowPt T order ⟨b, true⟩)
      (lowPt T order ⟨b, false⟩) := by
    refine Surface.isLineWithEnds_segment fun he => ?_
    have := congrArg Complex.re he
    simp only [lowPt_re] at this
    exact portIdx_ne hT hO hb hst (by exact_mod_cast this)
  have hl4 : Surface.IsLineWithEnds (vertSeg T order ⟨b, false⟩) (lowPt T order ⟨b, false⟩)
      ((Node.head ⟨b, false⟩).pos T order) :=
    (Surface.isLineWithEnds_segment (hlow _ rfl (head_depth_le_leafDepth hT hO hb))).symm
  have hl5 : Surface.IsLineWithEnds (upSeg T order (.head ⟨b, false⟩) b.2)
      ((Node.head ⟨b, false⟩).pos T order) ((Node.vertex b.2).pos T order) :=
    (Surface.isLineWithEnds_segment (upSeg_ends_ne hT ht)).symm
  -- Each new piece meets the earlier ones only at its first end.
  have i1 : upSeg T order (.head ⟨b, true⟩) b.1 ∩ vertSeg T order ⟨b, true⟩ =
      {(Node.head ⟨b, true⟩).pos T order} :=
    inter_eq_singleton (right_mem_segment _ _ _) (left_mem_segment _ _ _)
      fun z h₁ h₂ => (vertSeg_upSeg hT hO hb hvs hs h₂ h₁).2
  have i2 : (upSeg T order (.head ⟨b, true⟩) b.1 ∪ vertSeg T order ⟨b, true⟩) ∩
      horizSeg T order b = {lowPt T order ⟨b, true⟩} := by
    refine inter_eq_singleton (Or.inr (right_mem_segment _ _ _)) (left_mem_segment _ _ _) ?_
    rintro z (h₁ | h₁) h₂
    · exact (horizSeg_upSeg hT hO hb hs h₂ h₁).elim
    · exact (vertSeg_horizSeg hT hO hN hb hb h₁ h₂).2
  have i3 : (upSeg T order (.head ⟨b, true⟩) b.1 ∪ vertSeg T order ⟨b, true⟩ ∪
      horizSeg T order b) ∩ vertSeg T order ⟨b, false⟩ = {lowPt T order ⟨b, false⟩} := by
    refine inter_eq_singleton (Or.inr (right_mem_segment _ _ _)) (right_mem_segment _ _ _) ?_
    rintro z ((h₁ | h₁) | h₁) h₂
    · exact (hhst (vertSeg_upSeg hT hO hb hvs hs h₂ h₁).1).elim
    · exact (vertSeg_disjoint hT hO hb hb hst h₁ h₂).elim
    · exact (vertSeg_horizSeg hT hO hN hb hb h₂ h₁).2
  have i4 : (upSeg T order (.head ⟨b, true⟩) b.1 ∪ vertSeg T order ⟨b, true⟩ ∪
      horizSeg T order b ∪ vertSeg T order ⟨b, false⟩) ∩ upSeg T order (.head ⟨b, false⟩) b.2 =
      {(Node.head ⟨b, false⟩).pos T order} := by
    refine inter_eq_singleton (Or.inr (left_mem_segment _ _ _)) (right_mem_segment _ _ _) ?_
    rintro z (((h₁ | h₁) | h₁) | h₁) h₂
    · exfalso
      obtain ⟨w, -, e₁, e₂⟩ := upSeg_inter hT hO hvs hvt hs ht hhst h₁ h₂
      rcases e₁ with rfl | e₁
      · rcases e₂ with e₂ | e₂
        · exact (hb.2.2.1).ne (by rw [e₂])
        · cases e₂
      · cases e₁
    · exact (hhst (vertSeg_upSeg hT hO hb hvt ht h₁ h₂).1.symm).elim
    · exact (horizSeg_upSeg hT hO hb ht h₁ h₂).elim
    · exact (vertSeg_upSeg hT hO hb hvt ht h₁ h₂).2
  exact (((hl1.union hl2 i1).union hl3 i2).union hl4 i3).union hl5 i4

/-- The image of an oriented edge is a line between the points of its ends. -/
theorem isLine_edgeImage (hT : T.IsDFS G) (hO : ValidContourOrder T G order)
    (hN : Nonalternating (contourWord T order)) {e : Arc N} (hadj : G.Adj e.1 e.2)
    (ha : T.Ancestor e.2 e.1) :
    Surface.IsLineWithEnds (edgeImage T order e) ((Node.vertex e.1).pos T order)
      ((Node.vertex e.2).pos T order) := by
  unfold edgeImage edgePieces
  split_ifs with hpar
  · simp only [List.mem_singleton, iUnion_iUnion_eq_left, Piece.set]
    exact (Surface.isLineWithEnds_segment (upSeg_ends_ne hT (n := .vertex e.1) hpar)).symm
  · have h := isLine_backImage hT hO hN (backEdge_of hT hadj ha hpar)
    simp only [List.mem_cons, List.not_mem_nil, or_false, iUnion_iUnion_eq_or_left,
      iUnion_iUnion_eq_left, Piece.set]
    simpa only [union_assoc] using h

/-- For adjacent `u v`, the line of `u v` is the image of the edge oriented from its deeper
end. -/
theorem edgeLine_eq (hT : T.IsDFS G) {u v : Fin N} (hadj : G.Adj u v) :
    ∃ e : Arc N, G.Adj e.1 e.2 ∧ T.Ancestor e.2 e.1 ∧
      edgeLine T order u v = edgeImage T order e ∧ s(e.1, e.2) = s(u, v) ∧
      ((e.1 = u ∧ e.2 = v) ∨ (e.1 = v ∧ e.2 = u)) := by
  unfold edgeLine
  by_cases h₁ : T.Ancestor v u
  · exact ⟨(u, v), hadj, h₁, by simp only [h₁, ↓reduceIte], rfl, Or.inl ⟨rfl, rfl⟩⟩
  · rcases hT.2.2 u v hadj with h₂ | h₂
    · exact ⟨(v, u), hadj.symm, h₂, by simp only [h₁, h₂, ↓reduceIte], Sym2.eq_swap,
        Or.inr ⟨rfl, rfl⟩⟩
    · exact absurd h₂ h₁

private theorem mem_edgeImage {e : Arc N} {z : ℂ} (h : z ∈ edgeImage T order e) :
    ∃ P ∈ edgePieces T e, z ∈ P.set T order := by
  simpa [edgeImage] using h

/-- The plane embedding of Part IV, Section 5. -/
noncomputable def planeEmbedding (hT : T.IsDFS G) (hO : ValidContourOrder T G order)
    (hN : Nonalternating (contourWord T order)) : HP25.PlaneEmbedding G Set.univ where
  pt v := (Node.vertex v).pos T order
  line := edgeLine T order
  finite := Set.finite_univ
  injOn u _ v _ h := by
    have := Node.pos_injective hT hO (Node.valid_vertex u) (Node.valid_vertex v) h
    simpa using this
  line_comm u v := by
    unfold edgeLine
    by_cases h₁ : T.Ancestor v u
    · by_cases h₂ : T.Ancestor u v
      · rw [ancestor_antisymm hT h₂ h₁]
      · simp only [h₁, h₂, ↓reduceIte]
    · by_cases h₂ : T.Ancestor u v
      · simp only [h₁, h₂, ↓reduceIte]
      · simp only [h₁, h₂, ↓reduceIte]
  isLine u _ v _ hadj := by
    obtain ⟨e, he, ha, hl, -, hends⟩ := edgeLine_eq (order := order) hT hadj
    have h := isLine_edgeImage hT hO hN he ha
    rw [hl]
    rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, h₂] at h
      exact h
    · rw [h₁, h₂] at h
      exact h.symm
  inter u _ v _ u' _ v' _ hadj hadj' hne := by
    rintro z ⟨h₁, h₂⟩
    obtain ⟨e, he, ha, hl, hs, hends⟩ := edgeLine_eq (order := order) hT hadj
    obtain ⟨e', he', ha', hl', hs', hends'⟩ := edgeLine_eq (order := order) hT hadj'
    rw [hl] at h₁
    rw [hl'] at h₂
    obtain ⟨P, hP, hzP⟩ := mem_edgeImage h₁
    obtain ⟨Q, hQ, hzQ⟩ := mem_edgeImage h₂
    obtain ⟨vP, oP, eP⟩ := edgePieces_spec hT he ha P hP
    obtain ⟨vQ, oQ, eQ⟩ := edgePieces_spec hT he' ha' Q hQ
    obtain ⟨w, rfl, hwP, hwQ⟩ := Piece.inter hT hO hN vP vQ (by rw [oP, oQ, hs, hs']; exact hne)
      hzP hzQ
    refine ⟨w, ⟨?_, ?_⟩, rfl⟩
    · rcases eP w hwP with h | h <;> rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
        simp [h, h₁, h₂]
    · rcases eQ w hwQ with h | h <;> rcases hends' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
        simp [h, h₁, h₂]
  avoid u _ v _ hadj w _ hw := by
    obtain ⟨e, he, ha, hl, -, hends⟩ := edgeLine_eq (order := order) hT hadj
    rw [hl] at hw
    obtain ⟨P, hP, hzP⟩ := mem_edgeImage hw
    obtain ⟨vP, -, eP⟩ := edgePieces_spec hT he ha P hP
    rcases eP w (Piece.isEnd_of_mem hT hO vP hzP) with h | h <;>
      rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp [h, h₁, h₂]

/-- The ends of the segment of a piece. -/
@[expose] noncomputable def Piece.ends (T : Forest N) (order : ContourOrder N) :
    Piece N → ℂ × ℂ
  | .up n p => ((Node.vertex p).pos T order, n.pos T order)
  | .vert q => ((Node.head q).pos T order, lowPt T order q)
  | .horiz b => (lowPt T order ⟨b, true⟩, lowPt T order ⟨b, false⟩)

private theorem Piece.set_eq (P : Piece N) :
    P.set T order = segment ℝ (P.ends T order).1 (P.ends T order).2 := by
  cases P <;> rfl

/-- Every line of the drawing is a finite union of straight segments. -/
theorem isPolygonal_planeEmbedding (hT : T.IsDFS G) (hO : ValidContourOrder T G order)
    (hN : Nonalternating (contourWord T order)) : IsPolygonal (planeEmbedding hT hO hN) := by
  classical
  intro u v hadj
  obtain ⟨e, -, -, hl, -⟩ := edgeLine_eq (order := order) hT hadj
  refine ⟨((edgePieces T e).map (Piece.ends T order)).toFinset, ?_⟩
  change edgeLine T order u v = _
  rw [hl]
  ext z
  simp only [edgeImage, mem_iUnion, List.mem_toFinset, List.mem_map, exists_prop]
  constructor
  · rintro ⟨P, hP, hz⟩
    exact ⟨P.ends T order, ⟨P, hP, rfl⟩, by rw [← Piece.set_eq]; exact hz⟩
  · rintro ⟨_, ⟨P, hP, rfl⟩, hz⟩
    exact ⟨P, hP, by rw [Piece.set_eq]; exact hz⟩

end Drawing

/-- Part IV, Section 5 of `docs/planarity/planarity_test.tex`: "Convert a nonalternating contour to
explicit curves". A depth-first forest with a valid contour order whose port pairs do not
alternate gives a polygonal plane embedding of the graph. -/
theorem contourDrawing_proved : ContourDrawingStatement := by
  intro N G T order hT hO _ hN
  exact ⟨Drawing.planeEmbedding hT hO hN, Drawing.isPolygonal_planeEmbedding hT hO hN⟩

end GraphMinor.LRPlanarity
