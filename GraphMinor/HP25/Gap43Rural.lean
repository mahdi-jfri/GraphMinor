module

public import GraphMinor.HP25.Web
public import GraphMinor.GM09.RuralClean
public import GraphMinor.GM09.Section10c
import GraphMinor.GM09.RuralExtend
import GraphMinor.GM09.Section9
import GraphMinor.Surface.PlaneDisc
import GraphMinor.Surface.SurfaceGraph
import GraphMinor.Surface.Fan

/-!
# The gap of Lemma 4.3: a plane embedding from a rural drawing

A rural society `(G, Ω)` has a drawing in a closed disc `Δ` of the plane with the vertices of `Ω̄` on
the boundary, in the order of `Ω` (Graph Minors IX, Section 1). The drawing step of the gap
(`PlaneEmbedding.plane_gap`) needs a plane embedding in the sense of `HP25/Web.lean` in which the
edge between two consecutive vertices of `Ω` runs along the boundary of `Δ`. This file builds it.

* We take a presentation whose drawing meets the boundary `B` of `Δ` only in the vertices of `Ω̄`
  (`Neighborhood.IsRural.exists_clean`).
* For two consecutive vertices `u`, `w` of `Ω` we take the open arc of `B` from `u` to `w` that holds
  no vertex of `Ω̄` (`exists_bdArc`, from `GM09.exists_open_arcs`). Two such arcs for different pairs
  are disjoint (`eq_of_bdArc_meet`).
* The line of an edge is this arc, with its ends, when the ends are consecutive in `Ω`, and the
  closure of the drawn edge otherwise.
-/

public section

namespace GraphMinor.HP25

open Set Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM09

variable {V : Type*}

/-- `u` and `w` are consecutive in `Ω`: they are different vertices of `Ω̄` and no vertex of `Ω̄`
lies clockwise between them. -/
@[expose] def IsConsec (Ω : CyclicPerm V) (u w : V) : Prop :=
  u ∈ Ω.bar ∧ w ∈ Ω.bar ∧ u ≠ w ∧ Ω.interval u w = ∅

/-- With at least three vertices in `Ω̄`, two vertices are consecutive in at most one order. -/
theorem IsConsec.not_swap {Ω : CyclicPerm V} (h3 : 3 ≤ Ω.bar.ncard) {u w : V}
    (h : IsConsec Ω u w) : ¬ IsConsec Ω w u := by
  intro h'
  obtain ⟨v, hv, hvu, hvw⟩ : ∃ v ∈ Ω.bar, v ≠ u ∧ v ≠ w := by
    by_contra hno
    push Not at hno
    have hsub : Ω.bar ⊆ {u, w} := fun v hv => by
      by_cases hvu : v = u
      · exact Or.inl hvu
      · exact Or.inr (hno v hv hvu)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_pair h.2.2.1
    omega
  rcases Ω.mem_interval_or_interval_swap h.1 h.2.1 hv h.2.2.1 hvu hvw with hi | hi
  · rw [h.2.2.2] at hi
    exact hi
  · rw [h'.2.2.2] at hi
    exact hi

/-- **A preconnected set in a split arc.** If `X` minus `a, b` is the disjoint union of `I` and
`I₂`, and `I ∪ {a, b}`, `I₂ ∪ {a, b}` are closed, a preconnected set in `X` minus `a, b` that meets
`I` lies in `I`. -/
theorem subset_of_split {I I₂ X s : Set EuclideanPlane} {a b : EuclideanPlane}
    (hun : I ∪ I₂ = X \ {a, b}) (hd : Disjoint I I₂) (hc₁ : IsClosed (I ∪ {a, b}))
    (hc₂ : IsClosed (I₂ ∪ {a, b})) (hs : IsPreconnected s) (hsX : s ⊆ X \ {a, b})
    (hne : (s ∩ I).Nonempty) : s ⊆ I := by
  have hsplit := isPreconnected_iff_subset_of_disjoint.mp hs (I₂ ∪ {a, b})ᶜ (I ∪ {a, b})ᶜ
    hc₂.isOpen_compl hc₁.isOpen_compl ?_ ?_
  · rcases hsplit with h | h
    · intro x hx
      rcases (hun ▸ hsX hx : x ∈ I ∪ I₂) with h' | h'
      · exact h'
      · exact absurd (Or.inl h') (h hx)
    · obtain ⟨x, hx, hxI⟩ := hne
      exact absurd (Or.inl hxI) (h hx)
  · intro x hx
    rcases (hun ▸ hsX hx : x ∈ I ∪ I₂) with h' | h'
    · refine Or.inl fun h'' => ?_
      rcases h'' with h'' | h''
      · exact disjoint_left.mp hd h' h''
      · exact (hsX hx).2 h''
    · refine Or.inr fun h'' => ?_
      rcases h'' with h'' | h''
      · exact disjoint_left.mp hd h'' h'
      · exact (hsX hx).2 h''
  · refine Set.eq_empty_iff_forall_notMem.mpr fun x ⟨hx, h1, h2⟩ => ?_
    rcases (hun ▸ hsX hx : x ∈ I ∪ I₂) with h' | h'
    · exact h2 (Or.inl h')
    · exact h1 (Or.inl h')

/-- The data of a boundary arc between two points `a`, `b` of an `O`-arc `B`: an open arc `I` of `B`
with ends `a`, `b`, and the other open arc `I₂`. -/
structure IsBdArc (B I : Set EuclideanPlane) (a b : EuclideanPlane) : Prop where
  line : IsLineWithEnds (I ∪ {a, b}) a b
  sub : I ⊆ B \ {a, b}
  preconn : IsPreconnected I
  ends : a ∈ B ∧ b ∈ B
  split : ∃ I₂, I ∪ I₂ = B \ {a, b} ∧ Disjoint I I₂ ∧ IsClosed (I₂ ∪ {a, b})

/-- **The boundary arc between consecutive vertices.** Let the points `ν v` of the vertices of `Ω̄`
lie on the `O`-arc `B` in the order of `Ω`. For consecutive `u`, `w`, the open arc of `B` from `u` to
`w` holds no point of a vertex of `Ω̄`. -/
theorem exists_bdArc {Ω : CyclicPerm V} {B : Set EuclideanPlane} (φ : Circle ≃ₜ B)
    {ν : V → EuclideanPlane} (hinj : InjOn ν Ω.bar) (hmem : ∀ v ∈ Ω.bar, ν v ∈ B)
    (hag : ∀ v₁ v₂ v₃ : V, Ω.IsClockwise3 v₁ v₂ v₃ →
      ∃ (t₁ t₂ t₃ : ℝ), t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₁ + 2 * Real.pi ∧
        (φ (Circle.exp t₁)).1 = ν v₁ ∧ (φ (Circle.exp t₂)).1 = ν v₂ ∧ (φ (Circle.exp t₃)).1 = ν v₃)
    {u w : V} (h : IsConsec Ω u w) :
    ∃ I, IsBdArc B I (ν u) (ν w) ∧ ∀ v ∈ Ω.bar, ν v ∉ I := by
  obtain ⟨hu, hw, huw, hgap⟩ := h
  have hne : ν u ≠ ν w := fun e => huw (hinj hu hw e)
  obtain ⟨I₁, I₂, hp₁, -, hd, hun, -, hsnd, hl₁, hl₂⟩ := exists_open_arcs φ (hmem u hu) (hmem w hw) hne
  have hI₁ : I₁ ⊆ B \ {ν u, ν w} := hun ▸ subset_union_left
  refine ⟨I₁, ⟨hl₁, hI₁, hp₁, ⟨hmem u hu, hmem w hw⟩, I₂, hun, hd, ?_⟩, fun v hv hvI => ?_⟩
  · exact hl₂.isCompact.isClosed
  · have hvu : v ≠ u := fun e => (hI₁ hvI).2 (Or.inl (by rw [e]))
    have hvw : v ≠ w := fun e => (hI₁ hvI).2 (Or.inr (by rw [e]; rfl))
    rcases Ω.mem_interval_or_interval_swap hu hw hv huw hvu hvw with h' | h'
    · rw [hgap] at h'
      exact h'
    · obtain ⟨t₁, t₂, t₃, h₁₂, h₂₃, h₃₁, m₁, m₂, m₃⟩ := hag _ _ _ h'.2
      have := hsnd t₁ t₂ t₃ h₁₂ h₂₃ h₃₁ m₁ m₃
      rw [m₂] at this
      exact disjoint_left.mp hd hvI this

/-- **Different boundary arcs are disjoint.** If the boundary arcs of `u w` and of `u' w'` (both
free of the points of `Ω̄`) meet, the two pairs of points are the same. -/
theorem eq_of_bdArc_meet {B I I' P : Set EuclideanPlane} {a b a' b' : EuclideanPlane}
    (h : IsBdArc B I a b) (h' : IsBdArc B I' a' b') (hab' : a' ≠ b') (hP : ∀ p ∈ P, p ∉ I)
    (hP' : ∀ p ∈ P, p ∉ I') (ha : a ∈ P) (hb : b ∈ P) (ha' : a' ∈ P) (hmeet : (I ∩ I').Nonempty) :
    a' = a ∨ a' = b := by
  obtain ⟨I₂, hun, hd, hc₂⟩ := h.split
  have hc₁ : IsClosed (I ∪ {a, b}) := h.line.isCompact.isClosed
  have hb'I : b' ∉ I' := fun hb => (h'.sub hb).2 (Or.inr rfl)
  have hdiff : I' ∪ {a'} = (I' ∪ {a', b'}) \ {b'} := by
    ext p
    simp only [mem_union, mem_singleton_iff, mem_insert_iff, mem_sdiff]
    constructor
    · rintro (hp | rfl)
      · exact ⟨Or.inl hp, fun e => hb'I (e ▸ hp)⟩
      · exact ⟨Or.inr (Or.inl rfl), hab'⟩
    · rintro ⟨hp | hp | hp, hne⟩
      · exact Or.inl hp
      · exact Or.inr hp
      · exact absurd hp hne
  have hpre : IsPreconnected (I' ∪ {a'}) := by
    rw [hdiff]
    exact h'.line.isPreconnected_diff_right
  by_contra hno
  push Not at hno
  have hsub : I' ∪ {a'} ⊆ B \ {a, b} := by
    rintro p (hp | rfl)
    · refine ⟨(h'.sub hp).1, ?_⟩
      rintro (rfl | rfl)
      · exact hP' _ ha hp
      · exact hP' _ hb hp
    · exact ⟨h'.ends.1, fun h'' => by
        rcases h'' with e | e
        · exact hno.1 e
        · exact hno.2 e⟩
  have := subset_of_split hun hd hc₁ hc₂ hpre hsub (by
    obtain ⟨p, hpI, hpI'⟩ := hmeet
    exact ⟨p, Or.inl hpI', hpI⟩)
  exact hP a' ha' (this (Or.inr rfl))

/-! ### The drawn edges -/

section Drawn

variable {β : Type*} {G : Graph V β} (Γ : GraphDrawing G EuclideanPlane)

/-- The union of the closures of the drawn edges from `u` to `w`. In a simple graph this is the
closure of the one edge between them. -/
def drawnLine (u w : V) : Set EuclideanPlane :=
  ⋃ e ∈ {e | G.IsLink e u w}, closure (graphDrawingEdgeSet Γ e)

theorem drawnLine_comm (u w : V) : drawnLine Γ u w = drawnLine Γ w u := by
  ext p
  simp only [drawnLine, mem_iUnion, mem_ofPred_eq, exists_prop]
  exact ⟨fun ⟨e, he, hp⟩ => ⟨e, he.symm, hp⟩, fun ⟨e, he, hp⟩ => ⟨e, he.symm, hp⟩⟩

theorem drawnLine_eq (hs : IsSimpleGraph G) {e : β} {u w : V} (he : G.IsLink e u w) :
    drawnLine Γ u w = closure (graphDrawingEdgeSet Γ e) := by
  ext p
  simp only [drawnLine, mem_iUnion, mem_ofPred_eq, exists_prop]
  refine ⟨fun ⟨f, hf, hp⟩ => ?_, fun hp => ⟨e, he, hp⟩⟩
  rwa [hs.2 f hf.edge_mem e he.edge_mem u w hf he] at hp

/-- The closure of a drawn edge with two different ends is a line between their points. -/
theorem isLineWithEnds_closure_link {e : β} {u w : V} (he : G.IsLink e u w) (huw : u ≠ w) :
    IsLineWithEnds (closure (graphDrawingEdgeSet Γ e)) (vertexPt Γ u) (vertexPt Γ w) := by
  obtain ⟨hE, hcl⟩ := closure_inter_V_of_isLink Γ he
  have hne : vertexPt Γ u ≠ vertexPt Γ w := fun h =>
    huw (vertexPt_injOn Γ he.left_mem he.right_mem h)
  rcases Γ.drawing.edge_cond _ hE with ⟨a, b, -, hab, hline⟩ | ⟨a, ha, -⟩
  · rw [hcl] at hab
    rcases pair_eq_pair_iff.mp hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hline
    · rw [h1, h2]; exact hline.symm
  · rw [hcl] at ha
    have hu : vertexPt Γ u ∈ ({a} : Set EuclideanPlane) := ha ▸ Or.inl rfl
    have hw : vertexPt Γ w ∈ ({a} : Set EuclideanPlane) := ha ▸ Or.inr rfl
    exact (hne (hu.trans hw.symm)).elim

/-- The closure of a drawn edge is the edge and its two ends. -/
theorem closure_link_subset {e : β} {u w : V} (he : G.IsLink e u w) :
    closure (graphDrawingEdgeSet Γ e) ⊆ graphDrawingEdgeSet Γ e ∪ {vertexPt Γ u, vertexPt Γ w} := by
  obtain ⟨hE, hcl⟩ := closure_inter_V_of_isLink Γ he
  intro p hp
  by_cases hpV : p ∈ Γ.drawing.V
  · exact Or.inr (hcl ▸ ⟨hp, hpV⟩)
  · refine Or.inl ?_
    have := closure_edge_diff_V_eq Γ.drawing hE
    rw [← this]
    exact ⟨hp, hpV⟩

theorem closure_link_subset_U {e : β} (he : e ∈ E(G)) :
    closure (graphDrawingEdgeSet Γ e) ⊆ Γ.drawing.U :=
  closure_minimal ((graphDrawingEdgeSet_subset_sdiff_V Γ he).trans sdiff_subset)
    Γ.drawing.isClosed_U

/-- Two different drawn edges meet only at the points of their common ends. -/
theorem closure_link_inter {e f : β} {u w u' w' : V} (he : G.IsLink e u w) (hf : G.IsLink f u' w')
    (hef : e ≠ f) :
    closure (graphDrawingEdgeSet Γ e) ∩ closure (graphDrawingEdgeSet Γ f) ⊆
      {vertexPt Γ u, vertexPt Γ w} ∩ {vertexPt Γ u', vertexPt Γ w'} := by
  rintro p ⟨hpe, hpf⟩
  have hdisj := disjoint_graphDrawingEdgeSet_subgraphU Γ (GM09.singleEdgeSubgraph_le G f)
    he.edge_mem (by rw [GM09.edgeSet_singleEdgeSubgraph hf.edge_mem]; exact hef)
  have hpf' : p ∈ graphDrawingSubgraphU Γ (GM09.singleEdgeSubgraph G f) :=
    Or.inr (mem_iUnion₂.mpr ⟨f, by rw [GM09.edgeSet_singleEdgeSubgraph hf.edge_mem]; rfl, hpf⟩)
  rcases closure_link_subset Γ he hpe with h | h
  · exact absurd hpf' (disjoint_left.mp hdisj h)
  · refine ⟨h, ?_⟩
    obtain ⟨-, hcl⟩ := closure_inter_V_of_isLink Γ hf
    have hpV : p ∈ Γ.drawing.V := by
      rcases h with rfl | rfl
      · rw [← vertexEquiv_eq_vertexPt Γ ⟨u, he.left_mem⟩]
        exact (Γ.iso.vertexEquiv ⟨u, he.left_mem⟩).2
      · rw [← vertexEquiv_eq_vertexPt Γ ⟨w, he.right_mem⟩]
        exact (Γ.iso.vertexEquiv ⟨w, he.right_mem⟩).2
    exact hcl ▸ ⟨hpf, hpV⟩

end Drawn

theorem IsBdArc.symm {B I : Set EuclideanPlane} {a b : EuclideanPlane} (h : IsBdArc B I a b) :
    IsBdArc B I b a := by
  obtain ⟨hl, hs, hp, he, I₂, hu, hd, hc⟩ := h
  refine ⟨?_, ?_, hp, ⟨he.2, he.1⟩, I₂, ?_, hd, ?_⟩
  · rw [pair_comm]; exact hl.symm
  · rw [pair_comm]; exact hs
  · rw [pair_comm]; exact hu
  · rw [pair_comm]; exact hc

/-- **A plane embedding from a rural drawing.** Let `(G, Ω, Ω₀)` be a rural neighborhood with `G`
simple and at least three vertices in `Ω̄`, and let `K` be a simple graph whose edges are edges of
`G`. Then `K` has a plane embedding on `V(G)` inside the closed domain of an `O`-arc `F`, such that
the points of `F` that are vertices are the vertices of `Ω̄`, the line between two consecutive
vertices of `Ω` lies on `F`, and every other line meets `F` only at the points of its ends. -/
theorem exists_planeEmbedding {β : Type*} {N : Neighborhood V β} (hr : N.IsRural)
    (hs : IsSimpleGraph N.G) (h3 : 3 ≤ N.Ω.bar.ncard) (K : SimpleGraph V)
    (hK : ∀ u w, K.Adj u w → N.G.Adj u w) :
    ∃ (φ : PlaneEmbedding K V(N.G)) (F : Set ℂ), Nonempty (Circle ≃ₜ F) ∧ φ.U ⊆ closedInner F ∧
      (∀ v ∈ V(N.G), φ.pt v ∈ F → v ∈ N.Ω.bar) ∧
      (∀ u w, IsConsec N.Ω u w → φ.line u w ⊆ F) ∧
      (∀ u w, K.Adj u w → ¬ IsConsec N.Ω u w → ¬ IsConsec N.Ω w u →
        φ.line u w ∩ F ⊆ φ.pt '' {u, w}) := by
  classical
  obtain ⟨Pr, hclean, -, -⟩ := hr.exists_clean
  set Γ := Pr.Γ with hΓ
  set B := subBd Pr.Δ with hB
  set ν := vertexPt Γ with hν
  obtain ⟨φB, -, hag⟩ := Pr.agrees_Δ
  have hνV : ∀ {v}, v ∈ V(N.G) → graphDrawingVertexSet Γ v = {ν v} := fun hv =>
    vertexSet_eq_vertexPt Γ hv
  have hνB : ∀ v ∈ N.Ω.bar, ν v ∈ B := fun v hv =>
    hag.1 v hv (by rw [hνV (N.bar_subset hv)]; rfl)
  have hBν : ∀ v ∈ V(N.G), ν v ∈ B → v ∈ N.Ω.bar := fun v hv h =>
    (Pr.mem_bd_Δ_iff v hv).mp (by rw [hνV hv]; exact singleton_subset_iff.mpr h)
  have hinj : InjOn ν V(N.G) := vertexPt_injOn Γ
  have hag' : ∀ v₁ v₂ v₃ : V, N.Ω.IsClockwise3 v₁ v₂ v₃ →
      ∃ (t₁ t₂ t₃ : ℝ), t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₁ + 2 * Real.pi ∧
        (φB (Circle.exp t₁)).1 = ν v₁ ∧ (φB (Circle.exp t₂)).1 = ν v₂ ∧
        (φB (Circle.exp t₃)).1 = ν v₃ := by
    intro v₁ v₂ v₃ hcw
    obtain ⟨t₁, t₂, t₃, h1, h2, h3, m₁, m₂, m₃⟩ := hag.2 v₁ v₂ v₃ hcw
    have hb := hcw.2.1
    rw [hνV (N.bar_subset (hb v₁ (by simp)))] at m₁
    rw [hνV (N.bar_subset (hb v₂ (by simp)))] at m₂
    rw [hνV (N.bar_subset (hb v₃ (by simp)))] at m₃
    exact ⟨t₁, t₂, t₃, h1, h2, h3, mem_singleton_iff.mp m₁, mem_singleton_iff.mp m₂,
      mem_singleton_iff.mp m₃⟩
  -- the drawing meets `B` only at the points of `Ω̄`
  have hUB : ∀ p ∈ Γ.drawing.U, p ∈ B → ∃ v ∈ N.Ω.bar, p = ν v := by
    intro p hpU hpB
    have : p ∈ ⋃ v ∈ N.Ω.bar, graphDrawingVertexSet Γ v := hclean ▸ ⟨hpU, hpB⟩
    obtain ⟨v, hv, hpv⟩ := mem_iUnion₂.mp this
    rw [hνV (N.bar_subset hv)] at hpv
    exact ⟨v, hv, hpv⟩
  -- the boundary arcs
  have harc : ∀ u w, ∃ I : Set EuclideanPlane, IsConsec N.Ω u w →
      IsBdArc B I (ν u) (ν w) ∧ ∀ v ∈ N.Ω.bar, ν v ∉ I := by
    intro u w
    by_cases h : IsConsec N.Ω u w
    · obtain ⟨I, hI⟩ := exists_bdArc φB (hinj.mono N.bar_subset) hνB hag' h
      exact ⟨I, fun _ => hI⟩
    · exact ⟨∅, fun h' => absurd h' h⟩
  choose I hI using harc
  -- the open part `J u v` of the line of `u v`
  set J : V → V → Set EuclideanPlane := fun u v =>
    if IsConsec N.Ω u v then I u v else if IsConsec N.Ω v u then I v u
    else ⋃ e ∈ {e | N.G.IsLink e u v}, graphDrawingEdgeSet Γ e with hJ
  have hJcomm : ∀ u v, J u v = J v u := by
    intro u v
    by_cases h1 : IsConsec N.Ω u v
    · have h2 := h1.not_swap h3
      simp only [hJ, h1, h2, ↓reduceIte]
    by_cases h2 : IsConsec N.Ω v u
    · simp only [hJ, h2, h1, ↓reduceIte]
    simp only [hJ, h1, h2, ↓reduceIte]
    ext p
    simp only [mem_iUnion, mem_ofPred_eq, exists_prop]
    exact ⟨fun ⟨e, he, hp⟩ => ⟨e, he.symm, hp⟩, fun ⟨e, he, hp⟩ => ⟨e, he.symm, hp⟩⟩
  have hkind : ∀ u v, K.Adj u v →
      (∃ a b, IsConsec N.Ω a b ∧ s(a, b) = s(u, v) ∧ J u v = I a b) ∨
      (∃ e, N.G.IsLink e u v ∧ J u v = graphDrawingEdgeSet Γ e ∧ ¬ IsConsec N.Ω u v ∧
        ¬ IsConsec N.Ω v u) := by
    intro u v huv
    by_cases h1 : IsConsec N.Ω u v
    · exact Or.inl ⟨u, v, h1, rfl, by simp only [hJ, h1, ↓reduceIte]⟩
    by_cases h2 : IsConsec N.Ω v u
    · exact Or.inl ⟨v, u, h2, Sym2.eq_swap, by simp only [hJ, h1, h2, ↓reduceIte]⟩
    obtain ⟨e, he⟩ := hK u v huv
    refine Or.inr ⟨e, he, ?_, h1, h2⟩
    simp only [hJ, h1, h2, ↓reduceIte]
    ext p
    simp only [mem_iUnion, mem_ofPred_eq, exists_prop]
    exact ⟨fun ⟨f, hf, hp⟩ => by rwa [hs.2 f hf.edge_mem e he.edge_mem u v hf he] at hp,
      fun hp => ⟨e, he, hp⟩⟩
  -- basic facts on the pieces
  have hνU : ∀ t ∈ V(N.G), ν t ∈ Γ.drawing.U := fun t ht => vertexPt_mem_U Γ ht
  have hνVd : ∀ t ∈ V(N.G), ν t ∈ Γ.drawing.V := fun t ht => by
    rw [hν, ← vertexEquiv_eq_vertexPt Γ ⟨t, ht⟩]
    exact (Γ.iso.vertexEquiv ⟨t, ht⟩).2
  have hIfree : ∀ a b, IsConsec N.Ω a b → ∀ p ∈ I a b, p ∈ B ∧ p ∉ Γ.drawing.U := by
    intro a b hab p hp
    refine ⟨((hI a b hab).1.sub hp).1, fun hpU => ?_⟩
    obtain ⟨v, hv, rfl⟩ := hUB p hpU ((hI a b hab).1.sub hp).1
    exact (hI a b hab).2 v hv hp
  have hEfree : ∀ e ∈ E(N.G), ∀ p ∈ graphDrawingEdgeSet Γ e,
      p ∈ Γ.drawing.U ∧ p ∉ B ∧ p ∉ Γ.drawing.V := by
    intro e he p hp
    have h := graphDrawingEdgeSet_subset_sdiff_V Γ he hp
    refine ⟨h.1, fun hpB => ?_, h.2⟩
    obtain ⟨v, hv, rfl⟩ := hUB p h.1 hpB
    exact h.2 (hνVd v (N.bar_subset hv))
  have hconsV : ∀ a b, IsConsec N.Ω a b → a ∈ V(N.G) ∧ b ∈ V(N.G) := fun a b h =>
    ⟨N.bar_subset h.1, N.bar_subset h.2.1⟩
  -- (J2) no vertex on an open part
  have hJV : ∀ u v, K.Adj u v → ∀ t ∈ V(N.G), ν t ∉ J u v := by
    intro u v huv t ht hJt
    rcases hkind u v huv with ⟨a, b, hab, -, hJe⟩ | ⟨e, he, hJe, -⟩
    · rw [hJe] at hJt
      exact (hIfree a b hab _ hJt).2 (hνU t ht)
    · rw [hJe] at hJt
      exact (hEfree e he.edge_mem _ hJt).2.2 (hνVd t ht)
  -- (J3) the lines
  have hJline : ∀ u v, K.Adj u v → IsLineWithEnds (J u v ∪ {ν u, ν v}) (ν u) (ν v) := by
    intro u v huv
    rcases hkind u v huv with ⟨a, b, hab, he, hJe⟩ | ⟨e, he, hJe, -⟩
    · rw [hJe]
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (hI a b hab).1.line
      · exact (hI a b hab).1.symm.line
    · have heq : J u v ∪ {ν u, ν v} = closure (graphDrawingEdgeSet Γ e) := by
        rw [hJe]
        refine subset_antisymm (union_subset subset_closure ?_) (closure_link_subset Γ he)
        obtain ⟨-, hcl⟩ := closure_inter_V_of_isLink Γ he
        intro p hp
        have : p ∈ closure (graphDrawingEdgeSet Γ e) ∩ Γ.drawing.V := hcl ▸ hp
        exact this.1
      rw [heq]
      exact isLineWithEnds_closure_link Γ he huv.ne
  -- (J4) an open part misses every other line
  have hJdisj : ∀ u v u' v', K.Adj u v → K.Adj u' v' → s(u, v) ≠ s(u', v') →
      Disjoint (J u v) (J u' v' ∪ {ν u', ν v'}) := by
    intro u v u' v' huv huv' hne
    have hu'V : u' ∈ V(N.G) := (hK u' v' huv').choose_spec.left_mem
    have hv'V : v' ∈ V(N.G) := (hK u' v' huv').choose_spec.right_mem
    rcases hkind u v huv with ⟨a, b, hab, he, hJe⟩ | ⟨e, he, hJe, -⟩ <;>
      rcases hkind u' v' huv' with ⟨a', b', hab', he', hJe'⟩ | ⟨e', he', hJe', -⟩
    · -- two boundary arcs
      rw [hJe, hJe']
      have hu'Ω : u' ∈ N.Ω.bar ∧ v' ∈ N.Ω.bar := by
        rcases Sym2.eq_iff.mp he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hab'.1, hab'.2.1⟩
        · exact ⟨hab'.2.1, hab'.1⟩
      refine disjoint_left.mpr fun p hp hp' => ?_
      rcases hp' with hp' | hp'
      · have hmeet : (I a b ∩ I a' b').Nonempty := ⟨p, hp, hp'⟩
        have hP : ∀ q ∈ ν '' N.Ω.bar, q ∉ I a b := by
          rintro _ ⟨t, ht, rfl⟩; exact (hI a b hab).2 t ht
        have hP' : ∀ q ∈ ν '' N.Ω.bar, q ∉ I a' b' := by
          rintro _ ⟨t, ht, rfl⟩; exact (hI a' b' hab').2 t ht
        have hne' : ν a' ≠ ν b' := fun h => hab'.2.2.1 (hinj (hconsV a' b' hab').1
          (hconsV a' b' hab').2 h)
        have h1 := eq_of_bdArc_meet (hI a b hab).1 (hI a' b' hab').1 hne' hP hP'
          (mem_image_of_mem ν hab.1) (mem_image_of_mem ν hab.2.1) (mem_image_of_mem ν hab'.1)
          hmeet
        have h2 := eq_of_bdArc_meet (hI a b hab).1 (hI a' b' hab').1.symm hne'.symm hP hP'
          (mem_image_of_mem ν hab.1) (mem_image_of_mem ν hab.2.1) (mem_image_of_mem ν hab'.2.1)
          hmeet
        have hinj' := hinj.mono N.bar_subset
        have e1 : a' = a ∨ a' = b := h1.imp (hinj' hab'.1 hab.1) (hinj' hab'.1 hab.2.1)
        have e2 : b' = a ∨ b' = b := h2.imp (hinj' hab'.2.1 hab.1) (hinj' hab'.2.1 hab.2.1)
        apply hne
        rw [← he, ← he']
        rcases e1 with rfl | rfl <;> rcases e2 with rfl | rfl
        · exact absurd rfl hab'.2.2.1
        · rfl
        · exact Sym2.eq_swap
        · exact absurd rfl hab'.2.2.1
      · rcases hp' with rfl | rfl
        · exact (hI a b hab).2 u' hu'Ω.1 hp
        · exact (hI a b hab).2 v' hu'Ω.2 hp
    · -- a boundary arc and a drawn edge
      rw [hJe, hJe']
      refine disjoint_left.mpr fun p hp hp' => (hIfree a b hab p hp).2 ?_
      rcases hp' with hp' | hp'
      · exact (hEfree e' he'.edge_mem p hp').1
      · rcases hp' with rfl | rfl
        · exact hνU u' hu'V
        · exact hνU v' hv'V
    · -- a drawn edge and a boundary arc
      rw [hJe, hJe']
      refine disjoint_left.mpr fun p hp hp' => ?_
      have hf := hEfree e he.edge_mem p hp
      rcases hp' with hp' | hp'
      · exact hf.2.1 (hIfree a' b' hab' p hp').1
      · rcases hp' with rfl | rfl
        · exact hf.2.2 (hνVd u' hu'V)
        · exact hf.2.2 (hνVd v' hv'V)
    · -- two drawn edges
      rw [hJe, hJe']
      have hee : e ≠ e' := by
        rintro rfl
        apply hne
        rcases he.eq_and_eq_or_eq_and_eq he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
      have hdisj := disjoint_graphDrawingEdgeSet_subgraphU Γ (GM09.singleEdgeSubgraph_le N.G e')
        he.edge_mem (by rw [GM09.edgeSet_singleEdgeSubgraph he'.edge_mem]; exact hee)
      refine disjoint_left.mpr fun p hp hp' => ?_
      have hf := hEfree e he.edge_mem p hp
      rcases hp' with hp' | hp'
      · refine disjoint_left.mp hdisj hp (Or.inr (mem_iUnion₂.mpr ⟨e', ?_, subset_closure hp'⟩))
        rw [GM09.edgeSet_singleEdgeSubgraph he'.edge_mem]; rfl
      · rcases hp' with rfl | rfl
        · exact hf.2.2 (hνVd u' hu'V)
        · exact hf.2.2 (hνVd v' hv'V)
  -- (J5) the lines lie in `Δ`
  have hBΔ : B ⊆ Pr.Δ := fun p hp => by
    have := hp.1
    rwa [Pr.isClosedDisc_Δ.isCompact.isClosed.closure_eq] at this
  have hUΔ : Γ.drawing.U ⊆ Pr.Δ := fun p hp => (Pr.U_subset hp).1
  have hJΔ : ∀ u v, K.Adj u v → J u v ∪ {ν u, ν v} ⊆ Pr.Δ := by
    intro u v huv
    have huV : u ∈ V(N.G) := (hK u v huv).choose_spec.left_mem
    have hvV : v ∈ V(N.G) := (hK u v huv).choose_spec.right_mem
    refine union_subset ?_ ?_
    · rcases hkind u v huv with ⟨a, b, hab, -, hJe⟩ | ⟨e, he, hJe, -⟩
      · rw [hJe]
        exact fun p hp => hBΔ (hIfree a b hab p hp).1
      · rw [hJe]
        exact fun p hp => hUΔ (hEfree e he.edge_mem p hp).1
    · rintro p (rfl | rfl)
      · exact hUΔ (hνU u huV)
      · exact hUΔ (hνU v hvV)
  -- the plane embedding in `ℂ`
  set ι : EuclideanPlane → ℂ := fun p => complexPlane.symm p with hι
  have hιinj : Injective ι := complexPlane.symm.injective
  have hιc : Continuous ι := complexPlane.symm.continuous
  have hlinv : LeftInvOn complexPlane ι univ := fun x _ => complexPlane.apply_symm_apply x
  let φ : PlaneEmbedding K V(N.G) :=
    { pt := fun v => ι (ν v)
      line := fun u v => ι '' (J u v ∪ {ν u, ν v})
      finite := N.finite_V
      injOn := fun u hu w hw h => hinj hu hw (hιinj h)
      line_comm := fun u v => by simp only [hJcomm u v, pair_comm]
      isLine := fun u _ v _ huv =>
        GM09.IsLineWithEnds.image_of_injOn (hJline u v huv) hιc.continuousOn hιinj.injOn
      inter := by
        intro u hu v hv u' hu' v' hv' h1 h2 hne
        rw [← image_inter hιinj]
        rintro _ ⟨p, ⟨hp1, hp2⟩, rfl⟩
        have hpe : p ∈ ({ν u, ν v} : Set EuclideanPlane) := by
          rcases hp1 with h | h
          · exact absurd hp2 (disjoint_left.mp (hJdisj u v u' v' h1 h2 hne) h)
          · exact h
        have hpe' : p ∈ ({ν u', ν v'} : Set EuclideanPlane) := by
          rcases hp2 with h | h
          · exact absurd hp1 (disjoint_left.mp (hJdisj u' v' u v h2 h1 (Ne.symm hne)) h)
          · exact h
        rcases hpe with rfl | rfl <;> rcases hpe' with h | h
        · exact ⟨u, ⟨Or.inl rfl, Or.inl (hinj hu hu' h)⟩, rfl⟩
        · exact ⟨u, ⟨Or.inl rfl, Or.inr (hinj hu hv' h)⟩, rfl⟩
        · exact ⟨v, ⟨Or.inr rfl, Or.inl (hinj hv hu' h)⟩, rfl⟩
        · exact ⟨v, ⟨Or.inr rfl, Or.inr (hinj hv hv' h)⟩, rfl⟩
      avoid := by
        intro u hu v hv huv w hw h
        obtain ⟨p, hp, hpe⟩ := h
        obtain rfl := hιinj hpe
        rcases hp with h | h
        · exact absurd h (hJV u v huv w hw)
        · rcases h with h | h
          · exact Or.inl (hinj hw hu h)
          · exact Or.inr (hinj hw hv h) }
  -- the `O`-arc `F` and its closed domain
  have hFarc : Nonempty (Circle ≃ₜ (ι '' B)) :=
    IsOArc.image ⟨φB⟩ hιc.continuousOn complexPlane.continuous.continuousOn
      (fun x _ => complexPlane.apply_symm_apply x)
  have hΔ := IsClosedDisc.image Pr.isClosedDisc_Δ (f := ι) (f' := complexPlane)
    hιc.continuousOn complexPlane.continuous.continuousOn (fun x _ => complexPlane.apply_symm_apply x)
  have hcl : ι '' Pr.Δ = closedInner (ι '' B) :=
    eq_closedInner_of_discBd hFarc hΔ.1 (by rw [hΔ.2, hB, subBd_eq_discBd_plane Pr.isClosedDisc_Δ])
  refine ⟨φ, ι '' B, hFarc, ?_, ?_, ?_, ?_⟩
  · -- the drawing lies in the closed domain
    rw [← hcl]
    intro q hq
    simp only [PlaneEmbedding.U] at hq
    rcases hq with ⟨v, hv, rfl⟩ | hq
    · exact mem_image_of_mem ι (hUΔ (hνU v hv))
    · simp only [mem_iUnion] at hq
      obtain ⟨u, hu, v, hv, huv, hq⟩ := hq
      exact image_mono (hJΔ u v huv) hq
  · -- the vertices on `F` are those of `Ω̄`
    rintro v hv ⟨p, hp, hpe⟩
    obtain rfl := hιinj hpe
    exact hBν v hv hp
  · -- consecutive vertices: the line lies on `F`
    intro u w h
    refine image_mono (union_subset ?_ ?_)
    · have : J u w = I u w := by simp only [hJ, h, ↓reduceIte]
      rw [this]
      exact fun p hp => (hIfree u w h p hp).1
    · rintro p (rfl | rfl)
      · exact hνB u h.1
      · exact hνB w h.2.1
  · -- other edges meet `F` only at their ends
    intro u w huw h1 h2
    rw [← image_inter hιinj]
    rintro _ ⟨p, ⟨hp, hpB⟩, rfl⟩
    rcases hp with hp | hp
    · rcases hkind u w huw with ⟨a, b, hab, he, -⟩ | ⟨e, he, hJe, -⟩
      · exfalso
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h1 hab
        · exact h2 hab
      · rw [hJe] at hp
        exact absurd hpB (hEfree e he.edge_mem p hp).2.1
    · rcases hp with rfl | rfl
      · exact ⟨u, Or.inl rfl, rfl⟩
      · exact ⟨w, Or.inr rfl, rfl⟩

end GraphMinor.HP25
