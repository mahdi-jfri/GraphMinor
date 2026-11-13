module

public import GraphMinor.GM13.Section7a
public import GraphMinor.GM16.LatticeLines
public import GraphMinor.Surface.Jordan
import GraphMinor.GM16.RectangularGridLines
import GraphMinor.GM16.RectangularGridLinePoints
import GraphMinor.GM16.RectangularGridLineIntersections
import GraphMinor.GM16.EmbeddedLineGraphDrawing
import GraphMinor.GM16.SimpleDrawingVertices
import GraphMinor.GM16.SubdivisionPathDrawings
import GraphMinor.GM16.SubdivisionCentreCover
import GraphMinor.GM16.FiniteDrawingUnion
import GraphMinor.GM16.DrawingFamilyCompatibility
import GraphMinor.GM16.GraphIsoUnion
import GraphMinor.GM16.DrawingGraphPaths
import GraphMinor.GM07.Section46DrawingContactCount

/-!
# Graph Minors XIII, Section 7: the drawing of a wall as in Fig. 1

On page 89 of Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), 65–110, a wall `H` is "drawn in the plane as in Fig. 1",
and its distance function is defined from that drawing. On page 97 the paper names the vertices
of the elementary wall by their coordinates in that figure, with the origin at the bottom left.

This file defines that drawing and proves that every wall has one.

- `IsFigure1CoordDrawing W Γ`: the drawing `Γ` of the wall `W` puts the branch vertex with
  coordinates `(x, y)` at the point `(x, y)` of the plane, and draws each subdivision path of an
  edge of the elementary wall inside the unit segment of that edge.
- `DrawnWall.IsFigure1 W`: the point set and the vertex points of `W` are the image of such a
  drawing under a homeomorphism of the plane. The distance function of page 90 only sees the
  drawing up to such a homeomorphism (`planeWallDist_image_homeomorph`).
- `exists_isFigure1CoordDrawing`: every wall has a drawing as in Fig. 1. We first draw the
  elementary wall with straight unit segments, and then draw each subdivision path on the
  segment of its edge.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function
open Graph SimpleGraph
open GraphMinor
open GraphMinor.Surface
open GraphMinor.GM09
open GraphMinor.GM11
open GraphMinor.GM16
open GraphMinor.GM07 (HasNoIsolatedVertices U_eq_closed_edges_of_no_isolated)

universe u v w t

variable {α : Type u} {β : Type v}

/-! ## The coordinates of Fig. 1 -/

/-- The homeomorphism `ℝ × ℝ ≃ₜ EuclideanPlane` that identifies the coordinates `(x, y)` of
Fig. 1 with points of the plane. -/
noncomputable def fig1PlaneEquiv : (ℝ × ℝ) ≃ₜ EuclideanPlane :=
  Complex.equivRealProdCLM.toHomeomorph.symm.trans complexPlane.toHomeomorph

/-- The unit segment of `ℝ × ℝ` between two adjacent vertices `p, q` of an elementary wall: it
is horizontal if `p` and `q` are in the same row, and vertical otherwise. -/
def fig1Segment (p q : ℕ × ℕ) : Set (ℝ × ℝ) :=
  if p.2 = q.2 then horizontalLatticeLine (min p.1 q.1) (min p.2 q.2)
  else verticalLatticeLine (min p.1 q.1) (min p.2 q.2)

theorem fig1Segment_symm (p q : ℕ × ℕ) : fig1Segment p q = fig1Segment q p := by
  unfold fig1Segment
  by_cases h : p.2 = q.2
  · simp only [h, ↓reduceIte, min_comm p.1 q.1]
  · simp only [h, Ne.symm h, ↓reduceIte, min_comm p.1 q.1, min_comm p.2 q.2]

/-- The edge of the elementary wall of height `h` between adjacent vertices `p` and `q`. -/
def elementaryWallEdge {h : ℕ} {p q : ℕ × ℕ} (hadj : elementaryWallAdj h p q) :
    E(elementaryWall h) :=
  ⟨s(p, q), p, q, hadj, rfl⟩

/-- The edge of a wall `W` that corresponds to the edge `pq` of the elementary wall. -/
def Wall.baseEdge (W : Wall α β) {p q : ℕ × ℕ} (hadj : elementaryWallAdj W.height p q) : β :=
  (W.baseIso.edgeEquiv (elementaryWallEdge hadj)).1

/-- A drawing `Γ` of a wall `W` in the plane is the drawing of Fig. 1 (Graph Minors XIII,
Section 7, page 89: "If $H$ is a wall, drawn in the plane as in Fig. 1, its *distance function*
$d$ is defined as follows"; Section 9, page 97: "Draw $J$ in the plane as in Fig. 1, and let us
name the vertices of $J$ by $x, y$-coordinates, taking the origin in the bottom left of the
figure."). The branch vertex with coordinates `p` is drawn at the point `p`, and the path that
subdivides the edge `pq` of the elementary wall is drawn on the unit segment from `p` to `q`: the
closures of its edges cover exactly that segment. -/
structure IsFigure1CoordDrawing (W : Wall α β) (Γ : GraphDrawing W.graph EuclideanPlane) :
    Prop where
  /-- The branch vertex with coordinates `p` is drawn at the point `p`. -/
  branchVertex_point : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height)
    (hW : W.branchVertex p hp ∈ V(W.graph)),
    (Γ.iso.vertexEquiv ⟨W.branchVertex p hp, hW⟩).1 = fig1PlaneEquiv (latticePoint p)
  /-- The path subdividing the edge `pq` is drawn on the segment from `p` to `q`. -/
  path_on_segment : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q),
    (⋃ (f : E(W.graph)) (_ : f.1 ∈ E(W.subdivisionPaths (W.baseEdge hadj))),
      closure (Γ.iso.edgeEquiv f).1) = fig1PlaneEquiv '' fig1Segment p q

/-- A drawn wall `W` is drawn in the plane as in Fig. 1 (Graph Minors XIII, Section 7, page 89)
if its point set and the points of its vertices are the image of a drawing as in Fig. 1
(`IsFigure1CoordDrawing`) under a homeomorphism of the plane. -/
def DrawnWall.IsFigure1 (W : DrawnWall α β) : Prop :=
  ∃ (φ : EuclideanPlane ≃ₜ EuclideanPlane) (Γ : GraphDrawing W.graph EuclideanPlane),
    IsFigure1CoordDrawing W.toWall Γ ∧ W.drawingU = φ '' Γ.drawing.U ∧
    ∀ (v : α) (hv : v ∈ V(W.graph)), W.vertexPoint v = φ (Γ.iso.vertexEquiv ⟨v, hv⟩).1

/-! ## The distance function does not see homeomorphisms of the plane -/

/-- The image of a line with ends `s, t` under a homeomorphism is a line with ends `φ s, φ t`. -/
theorem isLineWithEnds_image_homeomorph (φ : EuclideanPlane ≃ₜ EuclideanPlane)
    {F : Set EuclideanPlane} {s t : EuclideanPlane} (hF : IsLineWithEnds F s t) :
    IsLineWithEnds (φ '' F) (φ s) (φ t) := by
  obtain ⟨f, hf0, hf1⟩ := hF
  let g : F ≃ₜ φ '' F := φ.image F
  refine ⟨f.trans g, ?_, ?_⟩
  · change φ (f 0).1 = φ s
    rw [hf0]
  · change φ (f 1).1 = φ t
    rw [hf1]

/-- The distance function of a point set is unchanged by a homeomorphism of the plane: for
every line `F` from `s` to `t`, `φ '' F` is a line from `φ s` to `φ t` with as many points in
`φ '' U` as `F` has in `U`, and conversely with `φ.symm`. -/
theorem planeWallDist_image_homeomorph (φ : EuclideanPlane ≃ₜ EuclideanPlane)
    (U : Set EuclideanPlane) (s t : EuclideanPlane) :
    planeWallDist (φ '' U) (φ s) (φ t) = planeWallDist U s t := by
  have key : ∀ (ψ : EuclideanPlane ≃ₜ EuclideanPlane) (U : Set EuclideanPlane)
      (s t : EuclideanPlane) (k : ℕ),
      (∃ F : Set EuclideanPlane, IsLineWithEnds F s t ∧ (F ∩ U).Finite ∧ (F ∩ U).ncard = k) →
      ∃ F : Set EuclideanPlane, IsLineWithEnds F (ψ s) (ψ t) ∧ (F ∩ ψ '' U).Finite ∧
        (F ∩ ψ '' U).ncard = k := by
    rintro ψ U s t k ⟨F, hF, hfin, hcard⟩
    have himg : ψ '' F ∩ ψ '' U = ψ '' (F ∩ U) := (image_inter ψ.injective).symm
    refine ⟨ψ '' F, isLineWithEnds_image_homeomorph ψ hF, ?_, ?_⟩
    · rw [himg]; exact hfin.image ψ
    · rw [himg, ncard_image_of_injective _ ψ.injective, hcard]
  unfold planeWallDist
  by_cases hst : s = t
  · subst hst; simp
  · have hst' : φ s ≠ φ t := φ.injective.ne hst
    simp only [hst, hst', ↓reduceIte]
    congr 1
    ext k
    constructor
    · intro hk
      have := key φ.symm (φ '' U) (φ s) (φ t) k hk
      simpa [image_image] using this
    · exact key φ U s t k

/-! ## The elementary wall drawn with unit segments -/

/-- The unit segment of an edge of the elementary wall, as a function of the edge of
`elementaryWallSimpleGraph h`. -/
def elementaryWallSegment (h : ℕ) : Sym2 (elementaryWallVerts h) → Set (ℝ × ℝ) :=
  Sym2.lift ⟨fun u v => fig1Segment u.1 v.1, fun u v => fig1Segment_symm u.1 v.1⟩

private theorem elementaryWallSegment_eq_rectangularGridLine {h : ℕ} (u v : elementaryWallVerts h) :
    elementaryWallSegment h s(u, v) =
      rectangularGridLine s(elementaryWallGridEmbed h u.1, elementaryWallGridEmbed h v.1) := by
  change fig1Segment u.1 v.1 =
    rectangularGridLinePair (elementaryWallGridEmbed h u.1) (elementaryWallGridEmbed h v.1)
  unfold fig1Segment rectangularGridLinePair
  have hu1 := elementaryWallGridEmbed_fst u.2
  have hu2 := elementaryWallGridEmbed_snd u.2
  have hv1 := elementaryWallGridEmbed_fst v.2
  have hv2 := elementaryWallGridEmbed_snd v.2
  have h2eq : (u.1.2 = v.1.2) ↔
      ((elementaryWallGridEmbed h u.1).2 = (elementaryWallGridEmbed h v.1).2) := by
    rw [← Fin.val_inj, hu2, hv2]
  rw [hu1, hu2, hv1, hv2]
  by_cases h2 : u.1.2 = v.1.2
  · simp [h2, h2eq.mp h2]
  · have h2' : (elementaryWallGridEmbed h u.1).2 ≠ (elementaryWallGridEmbed h v.1).2 :=
      fun hc => h2 (h2eq.mpr hc)
    simp [h2, h2']

private theorem latticePoint_eq_rectangularGridPoint {h : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ elementaryWallVerts h) :
    latticePoint p = rectangularGridPoint (elementaryWallGridEmbed h p) := by
  unfold rectangularGridPoint
  rw [elementaryWallGridEmbed_fst hp, elementaryWallGridEmbed_snd hp]

/-- The elementary wall of height `h`, drawn as in Fig. 1: every vertex `p` at the point `p`, and
every edge as the unit segment between its ends. The construction is the straight-line drawing
of a subgraph of a grid. -/
theorem exists_elementaryWall_drawing (h : ℕ) :
    ∃ Γ : GraphDrawing (Graph.ofSimpleGraph (elementaryWallSimpleGraph h)) EuclideanPlane,
      (∀ u : V(Graph.ofSimpleGraph (elementaryWallSimpleGraph h)),
        (Γ.iso.vertexEquiv u).1 = fig1PlaneEquiv (latticePoint u.1.1)) ∧
      (∀ e : E(Graph.ofSimpleGraph (elementaryWallSimpleGraph h)),
        closure (Γ.iso.edgeEquiv e).1 = fig1PlaneEquiv '' elementaryWallSegment h e.1) := by
  let G₀ := Graph.ofSimpleGraph (elementaryWallSimpleGraph h)
  have : Finite (elementaryWallVerts h) := (elementaryWall_finite_V h).to_subtype
  let f : elementaryWallVerts h → ℝ × ℝ := fun u => latticePoint u.1
  have hf_inj : Injective f := by
    intro u v huv
    have h1 : (u.1.1 : ℝ) = v.1.1 := congrArg Prod.fst huv
    have h2 : (u.1.2 : ℝ) = v.1.2 := congrArg Prod.snd huv
    exact Subtype.ext (Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2))
  have hfP (u : elementaryWallVerts h) :
      f u = rectangularGridPoint (elementaryWallGridEmbed h u.1) :=
    latticePoint_eq_rectangularGridPoint u.2
  have hNoLoop : ∀ e v, ¬ G₀.IsLoopAt e v := by
    intro e v hloop
    have he : e ∈ (elementaryWallSimpleGraph h).edgeSet := hloop.2
    rw [hloop.1] at he
    exact (show (elementaryWallSimpleGraph h).Adj v v from he).ne rfl
  have hLine : ∀ e ∈ E(G₀), ∀ a b, G₀.IsLink e a b → IsLineWithEnds (elementaryWallSegment h e) (f a) (f b) := by
    intro e he a b hlink
    have hadj : elementaryWallAdj h a.1 b.1 := by
      have he' : e ∈ (elementaryWallSimpleGraph h).edgeSet := he
      rw [hlink.1] at he'
      exact he'
    rw [hlink.1, elementaryWallSegment_eq_rectangularGridLine a b, hfP a, hfP b]
    exact rectangularGridLine_isLine (elementaryWallAdj_imp_grid_adj hadj)
  have hVertex : ∀ e ∈ E(G₀), ∀ v ∈ V(G₀), f v ∈ elementaryWallSegment h e → G₀.Inc e v := by
    intro e he v _ hv
    have heH : e ∈ (elementaryWallSimpleGraph h).edgeSet := he
    induction e using Sym2.ind with
    | _ a b =>
    have hadj : elementaryWallAdj h a.1 b.1 := heH
    rw [elementaryWallSegment_eq_rectangularGridLine a b, hfP v] at hv
    rcases Sym2.mem_iff.mp
        (rectangularGridLine_vertex (elementaryWallAdj_imp_grid_adj hadj) hv) with hveq | hveq
    · have hva : v = a := Subtype.ext (elementaryWallGridEmbed_injOn h v.2 a.2 hveq)
      subst hva
      exact ⟨b, rfl, heH⟩
    · have hvb : v = b := Subtype.ext (elementaryWallGridEmbed_injOn h v.2 b.2 hveq)
      subst hvb
      exact ⟨a, Sym2.eq_swap, heH⟩
  have hMeet : ∀ e ∈ E(G₀), ∀ d ∈ E(G₀), e ≠ d → elementaryWallSegment h e ∩ elementaryWallSegment h d ⊆ f '' V(G₀) := by
    intro e he d hd hne x hx
    have heH : e ∈ (elementaryWallSimpleGraph h).edgeSet := he
    have hdH : d ∈ (elementaryWallSimpleGraph h).edgeSet := hd
    induction e using Sym2.ind with
    | _ a₁ b₁ =>
    induction d using Sym2.ind with
    | _ a₂ b₂ =>
    have hadj₁ : elementaryWallAdj h a₁.1 b₁.1 := heH
    have hadj₂ : elementaryWallAdj h a₂.1 b₂.1 := hdH
    rw [elementaryWallSegment_eq_rectangularGridLine a₁ b₁,
      elementaryWallSegment_eq_rectangularGridLine a₂ b₂] at hx
    have hne_grid :
        s(elementaryWallGridEmbed h a₁.1, elementaryWallGridEmbed h b₁.1) ≠
        s(elementaryWallGridEmbed h a₂.1, elementaryWallGridEmbed h b₂.1) := by
      intro heq
      apply hne
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Subtype.ext (elementaryWallGridEmbed_injOn h a₁.2 a₂.2 h1),
          Subtype.ext (elementaryWallGridEmbed_injOn h b₁.2 b₂.2 h2)]
      · rw [Subtype.ext (elementaryWallGridEmbed_injOn h a₁.2 b₂.2 h1),
          Subtype.ext (elementaryWallGridEmbed_injOn h b₁.2 a₂.2 h2)]
        exact Sym2.eq_swap
    obtain ⟨w, hw⟩ := rectangularGridLine_intersection
      (elementaryWallAdj_imp_grid_adj hadj₁) (elementaryWallAdj_imp_grid_adj hadj₂) hne_grid hx
    rcases Sym2.mem_iff.mp (rectangularGridLine_vertex
        (elementaryWallAdj_imp_grid_adj hadj₁) (hw ▸ hx.1)) with hwa | hwb
    · exact ⟨a₁, mem_univ _, by rw [hfP, ← hw, hwa]; rfl⟩
    · exact ⟨b₁, mem_univ _, by rw [hfP, ← hw, hwb]; rfl⟩
  obtain ⟨Γ, _, hV, hE⟩ := exists_graphDrawing_of_embedded_lines G₀ (Set.toFinite _)
    (Set.toFinite _) f hf_inj.injOn (elementaryWallSegment h) hNoLoop hLine hVertex hMeet
    fig1PlaneEquiv fig1PlaneEquiv.isEmbedding
  exact ⟨Γ, hV, hE⟩

/-! ## Every wall has a drawing as in Fig. 1 -/

/-- In a walk with at least one edge, every vertex of the walk is an end of one of its edges. -/
private theorem GraphWalk.exists_inc_of_mem_support {G : Graph α β} :
    ∀ {a b : α} (W : GraphWalk G a b), W.edges ≠ [] → ∀ x ∈ W.support,
      ∃ e ∈ W.edges, G.Inc e x
  | _, _, .nil _, h, _, _ => (h rfl).elim
  | _, _, .cons (e := e) hl rest, _, x, hx => by
    simp only [GraphWalk.support, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨e, List.mem_cons_self .., hl.inc_left⟩
    · by_cases hr : rest.edges = []
      · cases rest with
        | nil _ =>
          simp only [GraphWalk.support, List.mem_singleton] at hx
          subst hx
          exact ⟨e, List.mem_cons_self .., hl.inc_right⟩
        | cons _ _ => simp [GraphWalk.edges] at hr
      · obtain ⟨f, hf, hfx⟩ := GraphWalk.exists_inc_of_mem_support rest hr x hx
        exact ⟨f, List.mem_cons_of_mem _ hf, hfx⟩

/-- A drawing of a path between distinct ends has no isolated vertices. -/
private theorem pathDrawing_noIsolated {S : Type t} [TopologicalSpace S] {N P : Graph α β}
    (D : GraphDrawing P S) (hP : ∃ a b, IsGraphPathWithEnds N P a b ∧ a ≠ b) :
    HasNoIsolatedVertices D.drawing := by
  obtain ⟨a, b, ⟨_, W, _, hV, hE⟩, hab⟩ := hP
  intro z hz
  obtain ⟨x, hx⟩ := D.iso.vertexEquiv.surjective ⟨z, hz⟩
  have hxs : x.1 ∈ W.support := by
    have hx2 : x.1 ∈ V(P) := x.2
    exact (Set.ext_iff.mp hV x.1).mp hx2
  have hne : W.edges ≠ [] := by
    intro h0
    cases W with
    | nil _ => exact hab rfl
    | cons _ _ => simp [GraphWalk.edges] at h0
  obtain ⟨f, hfW, y, hfy⟩ := GraphWalk.exists_inc_of_mem_support W hne x.1 hxs
  have hfP : f ∈ E(P) := by rw [hE]; exact hfW
  have hy : y ∈ V(P) := hfy.right_mem
  have hl := (D.iso.isLink_iff ⟨f, hfP⟩ x ⟨y, hy⟩).mp hfy
  refine ⟨(D.iso.edgeEquiv ⟨f, hfP⟩).1, hl.1, hz, Or.inl hl.1, ?_⟩
  have hzx : z = (D.iso.vertexEquiv x).1 := by rw [hx]
  have hzc : z ∈ closure (D.iso.edgeEquiv ⟨f, hfP⟩).1 ∩ D.drawing.V := by
    rw [hl.2.2.2, hzx]; exact mem_insert _ _
  exact hzc.1

/-- A copy of `GM16.exists_subdivision_drawing` that also records that every edge of the path
replacing an edge `e` is drawn inside the closure of `e`. -/
private theorem exists_subdivision_drawing_on_edges
    {α : Type u} {β : Type v} {ν : Type w} [Finite ν] {S : Type t}
    [TopologicalSpace S] [T2Space S] {N : Graph α β} {H : SimpleGraph ν}
    (c : ν → α) (hc : Function.Injective c) (P : H.edgeSet → Graph α β)
    (hPaths : ∀ e : H.edgeSet, ∃ a b, e.val=s(a,b) ∧ H.Adj a b ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f, e ≠ f → Disjoint E(P e) E(P f) ∧ V(P e) ∩ V(P f) ⊆ range c)
    (hVN : V(N)=range c ∪ ⋃ e, V(P e)) (hEN : E(N)=⋃ e, E(P e))
    (hNoIsolated : ∀ v, ∃ w, H.Adj v w)
    (Γ : GraphDrawing (Graph.ofSimpleGraph H) S) :
    ∃ Γ' : GraphDrawing N S,
      (∀ v (x : V(N)), x.val=c v → (Γ'.iso.vertexEquiv x).val=simpleDrawingVertex Γ v) ∧
      ∀ e, (⋃ (f : E(N)) (_ : f.1 ∈ E(P e)), closure (Γ'.iso.edgeEquiv f).val) =
        closure (Γ.iso.edgeEquiv e).val := by
  classical
  obtain ⟨D,hDU,hCentre,hZMeet,hMeet⟩ := exists_subdivision_path_drawings c hc P hPaths Γ
  have hPathOnly' (e : H.edgeSet) : ∃ a b, IsGraphPathWithEnds N (P e) a b ∧ a ≠ b := by
    obtain ⟨a,b,_,hab,hp,_⟩ := hPaths e
    exact ⟨c a,c b,hp,hc.ne hab.ne⟩
  have hPathOnly (e : H.edgeSet) : ∃ a b, e.val=s(a,b) ∧ IsGraphPathWithEnds N (P e) (c a) (c b) := by
    obtain ⟨a,b,he,_,hPath,_⟩ := hPaths e
    exact ⟨a,b,he,hPath⟩
  have hCover := subdivision_centres_subset_path_union c P hPathOnly hNoIsolated
  have hVN' : V(N)=⋃ e, V(P e) := hVN.trans (union_eq_self_of_subset_left hCover)
  have hBaseCover : Γ.drawing.V ⊆ ⋃ e, (D e).drawing.V := by
    intro x hx
    obtain ⟨v,rfl⟩ := range_simpleDrawingVertex Γ ▸ hx
    obtain ⟨e,hv⟩ := mem_iUnion.mp (hCover (mem_range_self v))
    have hPoint : simpleDrawingVertex Γ v ∈ (D e).drawing.V :=
      hCentre e v ⟨c v,hv⟩ rfl ▸ ((D e).iso.vertexEquiv ⟨c v,hv⟩).property
    exact mem_iUnion_of_mem e hPoint
  obtain ⟨J,hJU,hJV,hJE⟩ := exists_drawing_of_finite_drawings
    (Set.toFinite (univ : Set H.edgeSet)) Γ.drawing.finite_V (fun e => (D e).drawing)
    (fun e _ => hZMeet e) (fun e _ f _ hne => hMeet e f hne)
  simp only [mem_univ,iUnion_true] at hJU hJV hJE
  have hJV' : J.V=⋃ e, (D e).drawing.V := hJV.trans (union_eq_self_of_subset_left hBaseCover)
  have hSub (e : H.edgeSet) : (D e).drawing.IsSubdrawing J := by
    constructor
    · intro x hx
      exact hJV'.symm ▸ mem_iUnion_of_mem e hx
    · intro f hf
      exact hJE.symm ▸ mem_iUnion_of_mem e hf
  have hQ (e : H.edgeSet) : (D e).drawing.toGraph ≤ J.toGraph := toGraph_le_of_isSubdrawing (hSub e)
  have hP (e : H.edgeSet) : P e ≤ N := by
    obtain ⟨_,_,_,_,hp,_⟩ := hPaths e
    exact hp.le
  have hTarget (e f : H.edgeSet) (hne : e ≠ f) :
      (D e).drawing.U ∩ (D f).drawing.U ⊆ range (simpleDrawingVertex Γ) := by
    rw [range_simpleDrawingVertex]
    exact hMeet e f hne
  have hPointSource (e : H.edgeSet) (v : ν) (hv : simpleDrawingVertex Γ v ∈ (D e).drawing.U) : c v ∈ V(P e) :=
    source_centre_mem_of_path_drawing_support c P
      (fun e => by obtain ⟨a,b,he,ha,hp,_⟩ := hPaths e; exact ⟨a,b,he,ha,hp⟩) Γ D hDU e v hv
  obtain ⟨hvF,hvB⟩ := drawing_family_vertex_maps_compatible P D c (simpleDrawingVertex Γ)
    (fun e f hne => (hInter e f hne).2) hTarget hPointSource hCentre
  have heF (i j : H.edgeSet) (e : β) (hi : e ∈ E(P i)) (hj : e ∈ E(P j)) :
      ((D i).iso.edgeEquiv ⟨e,hi⟩).val=((D j).iso.edgeEquiv ⟨e,hj⟩).val := by
    by_cases hij : i=j
    · subst j
      rfl
    exact ((disjoint_left.mp (hInter i j hij).1) hi hj).elim
  have heB (i j : H.edgeSet) (e : Set S) (hi : e ∈ (D i).drawing.E) (hj : e ∈ (D j).drawing.E) :
      ((D i).iso.edgeEquiv.symm ⟨e,hi⟩).val=((D j).iso.edgeEquiv.symm ⟨e,hj⟩).val := by
    by_cases hij : i=j
    · subst j
      rfl
    have hDisj := drawing_family_edges_disjoint (fun e => (D e).drawing) Γ.drawing.V hZMeet hMeet hij
    exact ((disjoint_left.mp hDisj) hi hj).elim
  obtain ⟨φ,hφV,hφE⟩ := exists_iso_of_subgraph_unions P (fun e => (D e).drawing.toGraph) hP hQ
    (fun e => (D e).iso) hVN' hEN hJV' hJE hvF hvB heF heB
  refine ⟨⟨J,φ⟩,?_,?_⟩
  swap
  · intro e
    rw [← hDU e, U_eq_closed_edges_of_no_isolated _ (pathDrawing_noIsolated (D e) (hPathOnly' e))]
    apply Subset.antisymm
    · refine iUnion₂_subset fun f hf => ?_
      have hEq : (φ.edgeEquiv f).val = ((D e).iso.edgeEquiv ⟨f.1,hf⟩).val := hφE e ⟨f.1,hf⟩
      change closure (φ.edgeEquiv f).val ⊆ _
      rw [hEq]
      exact subset_biUnion_of_mem (u := fun g => closure g) ((D e).iso.edgeEquiv ⟨f.1,hf⟩).property
    · refine iUnion₂_subset fun g hg => ?_
      obtain ⟨f, hf⟩ := (D e).iso.edgeEquiv.surjective ⟨g,hg⟩
      have hEq : (φ.edgeEquiv ⟨f.1,(hP e).edgeSet_mono f.2⟩).val = g := by
        rw [hφE e f, hf]
      intro x hx
      exact mem_iUnion₂.mpr ⟨⟨f.1,(hP e).edgeSet_mono f.2⟩, f.2, by
        change x ∈ closure (φ.edgeEquiv _).val
        rw [hEq]; exact hx⟩
  intro v x hx
  obtain ⟨e,hv⟩ := mem_iUnion.mp (hCover (mem_range_self v))
  have hxEq : x=⟨c v,(hP e).vertexSet_mono hv⟩ := Subtype.ext hx
  rw [hxEq]
  exact (hφV e ⟨c v,hv⟩).trans (hCentre e v ⟨c v,hv⟩ rfl)


/-- Every branch vertex of a wall is a vertex of the wall. -/
theorem Wall.branchVertex_mem_graph (W : Wall α β) (p : ℕ × ℕ)
    (hp : p ∈ elementaryWallVerts W.height) : W.branchVertex p hp ∈ V(W.graph) :=
  W.base_verts_subset (W.baseIso.vertexEquiv ⟨p, hp⟩).2

/-- Every vertex of `elementaryWallSimpleGraph h` (`1 ≤ h`) has a horizontal neighbour. -/
private theorem elementaryWallSimpleGraph_no_isolated {h : ℕ} (hh : 1 ≤ h)
    (u : elementaryWallVerts h) :
    ∃ v : elementaryWallVerts h, (elementaryWallSimpleGraph h).Adj u v := by
  rcases u with ⟨⟨x, y⟩, hx, hy, hne0, hneh⟩
  dsimp at hx hy hne0 hneh
  by_cases hx0 : x = 0
  · subst hx0
    have hy_pos : 0 < y := by
      by_contra h0
      exact hne0 (Prod.ext rfl (by omega))
    have hv : (1, y) ∈ elementaryWallVerts h := by
      refine ⟨by omega, hy, ?_, ?_⟩
      · intro h; injection h with h1 _; omega
      · intro h; injection h with h1 _; omega
    exact ⟨⟨(1, y), hv⟩, ⟨⟨hx, hy, hne0, hneh⟩, hv, Or.inl ⟨rfl, Or.inl rfl⟩⟩⟩
  · by_cases hxmax : x = 2 * h + 1
    · subst hxmax
      have hy_lt : y < h := by
        by_contra hge
        exact hneh (Prod.ext rfl (by omega))
      have hv : (2 * h, y) ∈ elementaryWallVerts h := by
        refine ⟨by omega, hy, ?_, ?_⟩
        · intro h; injection h with h1 _; omega
        · intro h; injection h with h1 _; omega
      exact ⟨⟨(2 * h, y), hv⟩, ⟨⟨hx, hy, hne0, hneh⟩, hv, Or.inl ⟨rfl, Or.inr (by simp)⟩⟩⟩
    · by_cases hy0 : y = 0
      · subst hy0
        have hv : (x + 1, 0) ∈ elementaryWallVerts h := by
          refine ⟨by omega, hy, ?_, ?_⟩
          · intro h; injection h with h1 _; omega
          · intro h; injection h with _ h2; omega
        exact ⟨⟨(x + 1, 0), hv⟩, ⟨⟨hx, hy, hne0, hneh⟩, hv, Or.inl ⟨rfl, Or.inl rfl⟩⟩⟩
      · have hv : (x - 1, y) ∈ elementaryWallVerts h := by
          refine ⟨by omega, hy, ?_, ?_⟩
          · intro h; injection h with h1 h2; omega
          · intro h; injection h with h1 _; omega
        exact ⟨⟨(x - 1, y), hv⟩, ⟨⟨hx, hy, hne0, hneh⟩, hv, Or.inl ⟨rfl, Or.inr (by simp; omega)⟩⟩⟩

/-- The branch vertices of a wall are exactly the vertices of its base graph. -/
private theorem Wall.range_branchVertex (W : Wall α β) :
    range (fun u : elementaryWallVerts W.height => W.branchVertex u.1 u.2) = V(W.baseGraph) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact (W.baseIso.vertexEquiv ⟨u.1, u.2⟩).2
  · intro hx
    obtain ⟨u, hu⟩ := W.baseIso.vertexEquiv.surjective ⟨x, hx⟩
    exact ⟨⟨u.1, u.2⟩, congrArg Subtype.val hu⟩

/-- The edge of the elementary wall named by an edge of `elementaryWallSimpleGraph h`. -/
private def simpleEdgeToWall (h : ℕ) (e : (elementaryWallSimpleGraph h).edgeSet) :
    E(elementaryWall h) :=
  elementaryWallEdgeTo h ⟨e.1, e.2⟩

private theorem simpleEdgeToWall_bijective (h : ℕ) : Bijective (simpleEdgeToWall h) := by
  have hb := elementaryWallEdgeTo_bijective h
  refine ⟨fun e f hef => Subtype.ext (congrArg Subtype.val (hb.1 hef)), fun x => ?_⟩
  obtain ⟨e, he⟩ := hb.2 x
  exact ⟨⟨e.1, e.2⟩, he⟩

/-- Reindexing a union over the edges of the base graph of a wall by the edges of
`elementaryWallSimpleGraph h`. -/
private theorem Wall.iUnion_baseEdge {γ : Type*} (W : Wall α β) (F : β → Set γ) :
    (⋃ b ∈ E(W.baseGraph), F b) =
      ⋃ e : (elementaryWallSimpleGraph W.height).edgeSet,
        F (W.baseIso.edgeEquiv (simpleEdgeToWall W.height e)).1 := by
  ext x
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨b, hb, hx⟩
    obtain ⟨e, he⟩ := (simpleEdgeToWall_bijective W.height).2 (W.baseIso.edgeEquiv.symm ⟨b, hb⟩)
    refine ⟨e, ?_⟩
    rw [he]
    simpa using hx
  · rintro ⟨e, hx⟩
    exact ⟨_, (W.baseIso.edgeEquiv (simpleEdgeToWall W.height e)).2, hx⟩

/-- **Every wall has a drawing as in Fig. 1** (Graph Minors XIII, Section 7, page 89). Draw the
elementary wall with unit segments (`exists_elementaryWall_drawing`), and draw the path that
subdivides each of its edges on the segment of that edge. -/
theorem Wall.exists_isFigure1CoordDrawing (W : Wall α β) :
    ∃ Γ : GraphDrawing W.graph EuclideanPlane, IsFigure1CoordDrawing W Γ := by
  classical
  set h := W.height with hh
  obtain ⟨Γ₀, hΓ₀V, hΓ₀E⟩ := exists_elementaryWall_drawing h
  have : Finite (elementaryWallVerts h) := (elementaryWall_finite_V h).to_subtype
  let c : elementaryWallVerts h → α := fun u => W.branchVertex u.1 u.2
  have hc : Injective c := by
    intro u v huv
    have h1 : W.baseIso.vertexEquiv ⟨u.1, u.2⟩ = W.baseIso.vertexEquiv ⟨v.1, v.2⟩ :=
      Subtype.ext huv
    exact Subtype.ext (congrArg Subtype.val (W.baseIso.vertexEquiv.injective h1))
  have hrange : range c = V(W.baseGraph) := W.range_branchVertex
  let B : (elementaryWallSimpleGraph h).edgeSet → β :=
    fun e => (W.baseIso.edgeEquiv (simpleEdgeToWall h e)).1
  have hBmem (e) : B e ∈ E(W.baseGraph) := (W.baseIso.edgeEquiv (simpleEdgeToWall h e)).2
  have hBinj : Injective B := by
    intro e f hef
    exact (simpleEdgeToWall_bijective h).1 (W.baseIso.edgeEquiv.injective (Subtype.ext hef))
  let P : (elementaryWallSimpleGraph h).edgeSet → Graph α β := fun e => W.subdivisionPaths (B e)
  have hPaths : ∀ e : (elementaryWallSimpleGraph h).edgeSet, ∃ a b, e.val = s(a, b) ∧
      (elementaryWallSimpleGraph h).Adj a b ∧
      IsGraphPathWithEnds W.graph (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a, c b} := by
    rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ a b =>
    have hadj : (elementaryWallSimpleGraph h).Adj a b := he
    have hlink : W.baseGraph.IsLink (B ⟨s(a, b), he⟩) (c a) (c b) := by
      have := (W.baseIso.isLink_iff (simpleEdgeToWall h ⟨s(a, b), he⟩) ⟨a.1, a.2⟩ ⟨b.1, b.2⟩).mp
        ⟨hadj, rfl⟩
      exact this
    obtain ⟨x, y, hxy, hpath, _, hVP⟩ := W.path_of_edge _ (hBmem ⟨s(a, b), he⟩)
    refine ⟨a, b, rfl, hadj, ?_, ?_⟩
    · rcases hxy.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hpath
      · exact hpath.symm
    · rw [hrange, hVP]
      rcases hxy.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact pair_comm _ _
  have hInter : ∀ e f, e ≠ f → Disjoint E(P e) E(P f) ∧ V(P e) ∩ V(P f) ⊆ range c := by
    intro e f hef
    rw [hrange]
    exact W.paths_disjoint _ (hBmem e) _ (hBmem f) (hBinj.ne hef)
  have hVN : V(W.graph) = range c ∪ ⋃ e, V(P e) := by
    rw [W.vertexSet_eq, hrange, W.iUnion_baseEdge (fun b => V(W.subdivisionPaths b))]
  have hEN : E(W.graph) = ⋃ e, E(P e) := by
    rw [W.edgeSet_eq, W.iUnion_baseEdge (fun b => E(W.subdivisionPaths b))]
  have hNoIso : ∀ v, ∃ w, (elementaryWallSimpleGraph h).Adj v w :=
    elementaryWallSimpleGraph_no_isolated (by have := W.two_le_height; omega)
  obtain ⟨Γ, hΓV, hΓE⟩ := exists_subdivision_drawing_on_edges c hc P hPaths hInter hVN hEN
    hNoIso Γ₀
  refine ⟨Γ, ⟨?_, ?_⟩⟩
  · intro p hp hW
    rw [hΓV ⟨p, hp⟩ ⟨W.branchVertex p hp, hW⟩ rfl]
    exact hΓ₀V ⟨⟨p, hp⟩, mem_univ _⟩
  · intro p q hadj
    have he : s((⟨p, hadj.1⟩ : elementaryWallVerts h), ⟨q, hadj.2.1⟩) ∈
        (elementaryWallSimpleGraph h).edgeSet := hadj
    have hB : W.baseEdge hadj = B ⟨_, he⟩ := rfl
    rw [hB]
    exact (hΓE ⟨_, he⟩).trans (hΓ₀E ⟨_, he⟩)

/-- Every wall can be drawn as in Fig. 1: there is a drawn wall with the same underlying wall
that is drawn in the plane as in Fig. 1 (Graph Minors XIII, Section 7, page 89). -/
theorem Wall.exists_drawnWall_isFigure1 (W : Wall α β) :
    ∃ D : DrawnWall α β, D.toWall = W ∧ D.IsFigure1 := by
  classical
  obtain ⟨Γ, hΓ⟩ := W.exists_isFigure1CoordDrawing
  let pt : α → EuclideanPlane := fun v =>
    if hv : v ∈ V(W.graph) then (Γ.iso.vertexEquiv ⟨v, hv⟩).1 else 0
  have hpt (v : α) (hv : v ∈ V(W.graph)) : pt v = (Γ.iso.vertexEquiv ⟨v, hv⟩).1 := by
    simp [pt, hv]
  refine ⟨{ W with
    drawingU := Γ.drawing.U
    vertexPoint := pt
    vertexPoint_mem := fun v hv => by
      rw [hpt v hv]
      exact Γ.drawing.V_subset_U (Γ.iso.vertexEquiv ⟨v, hv⟩).2
    vertexPoint_injOn := fun v hv w hw hvw => by
      rw [hpt v hv, hpt w hw] at hvw
      exact congrArg Subtype.val (Γ.iso.vertexEquiv.injective (Subtype.ext hvw)) }, rfl, ?_⟩
  refine ⟨Homeomorph.refl _, Γ, hΓ, by simp, fun v hv => ?_⟩
  exact hpt v hv


/-! ## The point set of a drawing as in Fig. 1 -/

/-- In a path between distinct ends, every vertex is an end of an edge of the path. -/
theorem IsGraphPathWithEnds.exists_inc {N P : Graph α β} {a b x : α}
    (hP : IsGraphPathWithEnds N P a b) (hab : a ≠ b) (hx : x ∈ V(P)) :
    ∃ f ∈ E(P), P.Inc f x := by
  obtain ⟨_, W, _, hV, hE⟩ := hP
  have hxs : x ∈ W.support := (Set.ext_iff.mp hV x).mp hx
  have hne : W.edges ≠ [] := by
    intro h0
    cases W with
    | nil _ => exact hab rfl
    | cons _ _ => simp [GraphWalk.edges] at h0
  obtain ⟨f, hfW, hfx⟩ := GraphWalk.exists_inc_of_mem_support W hne x hxs
  exact ⟨f, (Set.ext_iff.mp hE f).mpr hfW, hfx⟩

/-- The base graph of a wall has no loops, since the elementary wall has none. -/
theorem Wall.baseGraph_isLink_ne (W : Wall α β) {b : β} {u v : α}
    (h : W.baseGraph.IsLink b u v) : u ≠ v := by
  rintro rfl
  obtain ⟨e, he⟩ := W.baseIso.edgeEquiv.surjective ⟨b, h.edge_mem⟩
  obtain ⟨x, hx⟩ := W.baseIso.vertexEquiv.surjective ⟨u, h.left_mem⟩
  have hl : W.baseGraph.IsLink (W.baseIso.edgeEquiv e) (W.baseIso.vertexEquiv x)
      (W.baseIso.vertexEquiv x) := by rw [he, hx]; exact h
  have h0 := (W.baseIso.isLink_iff e x x).mpr hl
  exact elementaryWallAdj_irrefl x.1 h0.1

/-- Every edge of the base graph of a wall is the image of an edge `pq` of the elementary
wall. -/
theorem Wall.exists_baseEdge_eq (W : Wall α β) {b : β} (hb : b ∈ E(W.baseGraph)) :
    ∃ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q), W.baseEdge hadj = b := by
  obtain ⟨⟨e, p, q, hadj, rfl⟩, he⟩ := W.baseIso.edgeEquiv.surjective ⟨b, hb⟩
  exact ⟨p, q, hadj, congrArg Subtype.val he⟩

/-- The ends of the path subdividing the edge `pq` are the branch vertices `p` and `q`. -/
theorem Wall.isGraphPathWithEnds_baseEdge (W : Wall α β) {p q : ℕ × ℕ}
    (hadj : elementaryWallAdj W.height p q) :
    IsGraphPathWithEnds W.graph (W.subdivisionPaths (W.baseEdge hadj))
      (W.branchVertex p hadj.1) (W.branchVertex q hadj.2.1) := by
  have hlink : W.baseGraph.IsLink (W.baseEdge hadj) (W.branchVertex p hadj.1)
      (W.branchVertex q hadj.2.1) :=
    (W.baseIso.isLink_iff (elementaryWallEdge hadj) ⟨p, hadj.1⟩ ⟨q, hadj.2.1⟩).mp ⟨hadj, rfl⟩
  obtain ⟨x, y, hxy, hpath, _, _⟩ :=
    W.path_of_edge _ (W.baseIso.edgeEquiv (elementaryWallEdge hadj)).2
  rcases hxy.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hpath
  · exact hpath.symm

/-- Every vertex of a wall is an end of an edge of the path subdividing some edge `pq` of the
elementary wall. -/
theorem Wall.exists_inc_baseEdge (W : Wall α β) {x : α} (hx : x ∈ V(W.graph)) :
    ∃ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q),
      ∃ f ∈ E(W.subdivisionPaths (W.baseEdge hadj)),
        (W.subdivisionPaths (W.baseEdge hadj)).Inc f x := by
  have hmem : ∃ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q),
      x ∈ V(W.subdivisionPaths (W.baseEdge hadj)) := by
    rw [W.vertexSet_eq] at hx
    rcases hx with hx | hx
    · obtain ⟨u, hu⟩ := W.baseIso.vertexEquiv.surjective ⟨x, hx⟩
      obtain ⟨w, hw⟩ := elementaryWallSimpleGraph_no_isolated
        (by have := W.two_le_height; omega) ⟨u.1, u.2⟩
      have hadj : elementaryWallAdj W.height u.1 w.1 := hw
      refine ⟨u.1, w.1, hadj, ?_⟩
      have hxu : x = W.branchVertex u.1 hadj.1 := by
        rw [Wall.branchVertex]; exact (congrArg Subtype.val hu).symm
      rw [hxu]
      exact (W.isGraphPathWithEnds_baseEdge hadj).left_mem
    · obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp hx
      obtain ⟨p, q, hadj, rfl⟩ := W.exists_baseEdge_eq hb
      exact ⟨p, q, hadj, hxb⟩
  obtain ⟨p, q, hadj, hxP⟩ := hmem
  have hpq : W.branchVertex p hadj.1 ≠ W.branchVertex q hadj.2.1 := by
    intro h
    have h1 : W.baseIso.vertexEquiv ⟨p, hadj.1⟩ = W.baseIso.vertexEquiv ⟨q, hadj.2.1⟩ :=
      Subtype.ext h
    have h2 : p = q := congrArg Subtype.val (W.baseIso.vertexEquiv.injective h1)
    subst h2
    exact elementaryWallAdj_irrefl p hadj
  exact ⟨p, q, hadj, IsGraphPathWithEnds.exists_inc (W.isGraphPathWithEnds_baseEdge hadj) hpq hxP⟩

/-- The point set of the drawing of the elementary wall of height `h` in Fig. 1: the union of
the unit segments of its edges. -/
def fig1WallSet (h : ℕ) : Set EuclideanPlane :=
  ⋃ (p : ℕ × ℕ) (q : ℕ × ℕ) (_ : elementaryWallAdj h p q), fig1PlaneEquiv '' fig1Segment p q

/-- A wall drawn as in Fig. 1 has as point set the union of the unit segments of the edges of the
elementary wall. Every vertex is an end of an edge, so the closed edges cover the drawing; every
edge is drawn on the segment of its base edge; and the paths cover their segments. -/
theorem IsFigure1CoordDrawing.drawing_U_eq {W : Wall α β}
    {Γ : GraphDrawing W.graph EuclideanPlane} (hΓ : IsFigure1CoordDrawing W Γ) :
    Γ.drawing.U = fig1WallSet W.height := by
  have hno : GM07.HasNoIsolatedVertices Γ.drawing := by
    intro z hz
    obtain ⟨x, hx⟩ := Γ.iso.vertexEquiv.surjective ⟨z, hz⟩
    obtain ⟨p, q, hadj, f, hf, y, hfy⟩ := W.exists_inc_baseEdge x.2
    have hle := (W.isGraphPathWithEnds_baseEdge hadj).le
    have hfW : f ∈ E(W.graph) := hle.edgeSet_mono hf
    have hl := (Γ.iso.isLink_iff ⟨f, hfW⟩ x ⟨y, (hfy.mono hle).right_mem⟩).mp (hfy.mono hle)
    refine ⟨(Γ.iso.edgeEquiv ⟨f, hfW⟩).1, hl.1, hz, Or.inl hl.1, ?_⟩
    have hzx : z = (Γ.iso.vertexEquiv x).1 := by rw [hx]
    have hzc : z ∈ closure (Γ.iso.edgeEquiv ⟨f, hfW⟩).1 ∩ Γ.drawing.V := by
      rw [hl.2.2.2, hzx]; exact mem_insert _ _
    exact hzc.1
  rw [GM07.U_eq_closed_edges_of_no_isolated _ hno]
  apply Subset.antisymm
  · refine iUnion₂_subset fun g hg => ?_
    obtain ⟨f, hf⟩ := Γ.iso.edgeEquiv.surjective ⟨g, hg⟩
    have hfE : f.1 ∈ ⋃ e ∈ E(W.baseGraph), E(W.subdivisionPaths e) := by
      have h1 : f.1 ∈ E(W.graph) := f.2
      exact (Set.ext_iff.mp W.edgeSet_eq f.1).mp h1
    obtain ⟨b, hb, hfb⟩ := mem_iUnion₂.mp hfE
    obtain ⟨p, q, hadj, rfl⟩ := W.exists_baseEdge_eq hb
    intro z hz
    refine mem_iUnion₂.mpr ⟨p, q, mem_iUnion.mpr ⟨hadj, ?_⟩⟩
    rw [← hΓ.path_on_segment p q hadj]
    refine mem_iUnion₂.mpr ⟨f, hfb, ?_⟩
    rw [hf]; exact hz
  · refine iUnion₂_subset fun p q => iUnion_subset fun hadj => ?_
    rw [← hΓ.path_on_segment p q hadj]
    refine iUnion₂_subset fun f _ => ?_
    exact subset_biUnion_of_mem (u := fun g => closure g) (Γ.iso.edgeEquiv f).2

/-- The distance function of a wall drawn as in Fig. 1 is, up to the homeomorphism of the
drawing, the distance function of the point set `fig1WallSet h` of Fig. 1. -/
theorem DrawnWall.IsFigure1.exists_planeDist_eq {W : DrawnWall α β} (hW : W.IsFigure1) :
    ∃ φ : EuclideanPlane ≃ₜ EuclideanPlane, ∀ s t : EuclideanPlane,
      W.planeDist s t = planeWallDist (fig1WallSet W.height) (φ.symm s) (φ.symm t) := by
  obtain ⟨φ, Γ, hΓ, hU, _⟩ := hW
  refine ⟨φ, fun s t => ?_⟩
  rw [DrawnWall.planeDist, hU, hΓ.drawing_U_eq]
  have := planeWallDist_image_homeomorph φ (fig1WallSet W.height) (φ.symm s) (φ.symm t)
  rwa [φ.apply_symm_apply, φ.apply_symm_apply] at this

end GraphMinor.GM13
