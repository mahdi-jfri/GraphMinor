module

public import GraphMinor.HP25.Prop32
public import GraphMinor.HP25.RibConnected
public import GraphMinor.Surface.CrossCut
import GraphMinor.Surface.ChartCells
import GraphMinor.Surface.SurfaceGraph

/-!
# Tools for splitting a rib along a path

* `PlaneEmbedding.restrict`: an embedding of `G` on `R` restricted to a subset `R'` of `R`.
* `PlaneEmbedding.pathImage_reverse`: the image of a reversed path list.
* `IsListEdge l u v`: `uv` joins two consecutive entries of the list `l`, with lemmas for appended
  and reversed lists.
* Facts about a theta curve (`Surface.IsTheta`): the two closed inner domains cover the closed
  inner domain of the outer curve and meet in the middle arc, and a connected set inside the outer
  curve that misses the middle arc lies on one side (`IsTheta.sep`).
* `PlaneEmbedding.isRibEmbedding_restrict`: an embedding restricted to the vertices drawn in the
  closed inner domain of the image `F₁` of a cycle `C₁` has the faces of a rib with frame `C₁`, when
  the lines of its edges stay in that closed domain and the drawing inside `F₁` uses only these
  vertices and edges.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

/-! ### Edges of a list -/

/-- `uv` joins two consecutive entries of `l`. -/
@[expose] def IsListEdge (l : List V) (u v : V) : Prop :=
  ∃ p ∈ l.zip l.tail, s(u, v) = s(p.1, p.2)

theorem IsListEdge.symm {l : List V} {u v : V} (h : IsListEdge l u v) : IsListEdge l v u := by
  obtain ⟨p, hp, he⟩ := h
  exact ⟨p, hp, by rw [Sym2.eq_swap]; exact he⟩

theorem IsListEdge.append_left {l₁ l₂ : List V} {u v : V} (h : IsListEdge l₁ u v) :
    IsListEdge (l₁ ++ l₂) u v := by
  obtain ⟨p, hp, he⟩ := h
  obtain ⟨i, hi, h1, h2⟩ := mem_zip_tail_iff.mp (show (p.1, p.2) ∈ l₁.zip l₁.tail from hp)
  refine ⟨p, mem_zip_tail_iff.mpr ⟨i, by simp; omega, ?_, ?_⟩, he⟩
  · rw [List.getElem_append_left (by omega)]; exact h1
  · rw [List.getElem_append_left (by omega)]; exact h2

theorem IsListEdge.append_right {l₁ l₂ : List V} {u v : V} (h : IsListEdge l₂ u v) :
    IsListEdge (l₁ ++ l₂) u v := by
  obtain ⟨p, hp, he⟩ := h
  obtain ⟨i, hi, h1, h2⟩ := mem_zip_tail_iff.mp (show (p.1, p.2) ∈ l₂.zip l₂.tail from hp)
  refine ⟨p, mem_zip_tail_iff.mpr ⟨l₁.length + i, by simp; omega, ?_, ?_⟩, he⟩
  · rw [List.getElem_append_right (by omega)]; simpa using h1
  · rw [List.getElem_append_right (by omega)]
    simpa [show l₁.length + i + 1 - l₁.length = i + 1 by omega] using h2

theorem IsListEdge.reverse {l : List V} {u v : V} (h : IsListEdge l u v) :
    IsListEdge l.reverse u v := by
  obtain ⟨p, hp, he⟩ := h
  obtain ⟨i, hi, h1, h2⟩ := mem_zip_tail_iff.mp (show (p.1, p.2) ∈ l.zip l.tail from hp)
  refine ⟨(p.2, p.1), mem_zip_tail_iff.mpr ⟨l.length - 2 - i, by simp; omega, ?_, ?_⟩,
    by rw [he, Sym2.eq_swap]⟩
  · rw [List.getElem_reverse, ← h2]
    congr 1
    omega
  · rw [List.getElem_reverse, ← h1]
    congr 1
    omega

theorem IsListEdge.mem_left {l : List V} {u v : V} (h : IsListEdge l u v) : u ∈ l := by
  obtain ⟨p, hp, he⟩ := h
  have h1 := List.of_mem_zip hp
  rcases Sym2.eq_iff.mp he with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact h1.1
  · exact List.mem_of_mem_tail h1.2

theorem IsListEdge.mem_right {l : List V} {u v : V} (h : IsListEdge l u v) : v ∈ l :=
  h.symm.mem_left

/-- An edge of the list `x :: t ++ [x]` is an edge of the cycle `x :: t`. -/
theorem isCycleEdge_of_isListEdge {x : V} {t : List V} {u v : V}
    (h : IsListEdge (x :: t ++ [x]) u v) : PlaneEmbedding.IsCycleEdge (x :: t) u v := by
  obtain ⟨p, hp, he⟩ := h
  refine ⟨p, ?_, he⟩
  rw [zip_rotate_one_cons]
  exact hp

/-- An edge of the cycle `x :: t` is an edge of the list `x :: t ++ [x]`. -/
theorem isListEdge_of_isCycleEdge {x : V} {t : List V} {u v : V}
    (h : PlaneEmbedding.IsCycleEdge (x :: t) u v) : IsListEdge (x :: t ++ [x]) u v := by
  obtain ⟨p, hp, he⟩ := h
  refine ⟨p, ?_, he⟩
  rw [← zip_rotate_one_cons]
  exact hp

/-! ### Restricted embeddings and reversed paths -/

namespace PlaneEmbedding

/-- The embedding restricted to a subset `R'` of the vertex set. -/
@[expose] def restrict (φ : PlaneEmbedding G R) {R' : Set V} (h : R' ⊆ R) : PlaneEmbedding G R' where
  pt := φ.pt
  line := φ.line
  finite := φ.finite.subset h
  injOn := φ.injOn.mono h
  line_comm := φ.line_comm
  isLine := fun u hu v hv huv => φ.isLine u (h hu) v (h hv) huv
  inter := fun u hu v hv u' hu' v' hv' h1 h2 hne =>
    φ.inter u (h hu) v (h hv) u' (h hu') v' (h hv') h1 h2 hne
  avoid := fun u hu v hv huv w hw => φ.avoid u (h hu) v (h hv) huv w (h hw)

variable (φ : PlaneEmbedding G R)

theorem pathImage_concat (l : List V) (y x : V) :
    φ.pathImage (l ++ [y, x]) = φ.pathImage (l ++ [y]) ∪ φ.line y x := by
  rw [φ.pathImage_append l y [x], pathImage_cons_cons, pathImage_single, union_empty]

theorem pathImage_reverse : ∀ l : List V, φ.pathImage l.reverse = φ.pathImage l
  | [] => rfl
  | [x] => rfl
  | x :: y :: t => by
    rw [List.reverse_cons, List.reverse_cons, List.append_assoc, List.singleton_append,
      φ.pathImage_append t.reverse y [x], pathImage_cons_cons, pathImage_single, union_empty,
      ← List.reverse_cons, pathImage_reverse (y :: t), pathImage_cons_cons, φ.line_comm,
      union_comm]

end PlaneEmbedding

end GraphMinor.HP25

/-! ### Theta curves -/

namespace GraphMinor.Surface.IsTheta

open Set

variable {F F₁ F₂ A₁ A₂ c : Set ℂ} {p q : ℂ}

/-- The closed inner domains of the two sides cover the closed inner domain of `F`. -/
theorem closedInner_subset (h : IsTheta F F₁ F₂ A₁ A₂ c p q) :
    inner F ∪ F ⊆ (inner F₁ ∪ F₁) ∪ (inner F₂ ∪ F₂) := by
  rintro z (hz | hz)
  · by_cases hzc : z ∈ c
    · exact Or.inl (Or.inr (h.eq₁ ▸ Or.inr hzc))
    · have hz' : z ∈ inner F \ c := ⟨hz, hzc⟩
      rw [h.inner_sdiff] at hz'
      rcases hz' with h1 | h2
      · exact Or.inl (Or.inl h1)
      · exact Or.inr (Or.inl h2)
  · rw [h.eq] at hz
    rcases hz with h1 | h2
    · exact Or.inl (Or.inr (h.eq₁ ▸ Or.inl h1))
    · exact Or.inr (Or.inr (h.eq₂ ▸ Or.inl h2))

/-- The inner domain of one side misses the other side. -/
theorem inner_disjoint_side (h : IsTheta F F₁ F₂ A₁ A₂ c p q) : Disjoint (inner F₁) F₂ := by
  refine Set.disjoint_left.mpr fun z hz hz2 => ?_
  rw [h.eq₂] at hz2
  rcases hz2 with hA | hc
  · by_cases hpq : z ∈ ({p, q} : Set ℂ)
    · rcases hpq with rfl | rfl
      · exact hz.1 (h.eq₁ ▸ Or.inr h.ends.1)
      · exact hz.1 (h.eq₁ ▸ Or.inr h.ends.2)
    · exact Set.disjoint_left.mp h.parts₁.disjoint hz (h.open_arc_subset_outer ⟨hA, hpq⟩)
  · exact hz.1 (h.eq₁ ▸ Or.inr hc)

/-- The closed inner domains of the two sides meet in the middle arc. -/
theorem closedInner_inter (h : IsTheta F F₁ F₂ A₁ A₂ c p q) :
    (inner F₁ ∪ F₁) ∩ (inner F₂ ∪ F₂) ⊆ c := by
  rintro z ⟨h1 | h1, h2 | h2⟩
  · exact absurd h2 (Set.disjoint_left.mp h.disjoint_inner h1)
  · exact absurd h2 (Set.disjoint_left.mp h.inner_disjoint_side h1)
  · exact absurd h1 (Set.disjoint_left.mp h.symm.inner_disjoint_side h2)
  · exact h.inter_eq ▸ ⟨h1, h2⟩

theorem isClosed_closedInner (J : IsJordanParts F) : IsClosed (inner F ∪ F) := by
  rw [← J.closure_inner]
  exact isClosed_closure

/-- A connected set inside `F` that misses the middle arc lies on one side. -/
theorem sep (h : IsTheta F F₁ F₂ A₁ A₂ c p q) {Y : Set ℂ} (hY : IsPreconnected Y)
    (hYF : Y ⊆ inner F ∪ F) (hYc : Disjoint Y c) :
    Y ⊆ inner F₁ ∪ F₁ ∨ Y ⊆ inner F₂ ∪ F₂ := by
  refine (isPreconnected_iff_subset_of_disjoint_closed.mp hY) _ _
    (isClosed_closedInner h.parts₁) (isClosed_closedInner h.parts₂)
    (hYF.trans h.closedInner_subset) ?_
  refine Set.eq_empty_of_forall_notMem fun z ⟨hzY, hz⟩ => ?_
  exact Set.disjoint_left.mp hYc hzY (h.closedInner_inter hz)

end GraphMinor.Surface.IsTheta

namespace GraphMinor.HP25

open SimpleGraph Set Surface

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

namespace PlaneEmbedding

variable (φ : PlaneEmbedding G R)

/-- The point of a vertex of a cycle lies on the image of the cycle. -/
theorem pt_mem_cycleImage {L : List V} (hL : IsCycleList G L) (hLR : ∀ y ∈ L, y ∈ R) {v : V}
    (hv : v ∈ L) : φ.pt v ∈ φ.cycleImage L := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have hi' : i < (L.zip (L.rotate 1)).length := by simp [hi]
  have hmem := List.getElem_mem hi'
  simp only [List.getElem_zip] at hmem
  simp only [cycleImage, mem_iUnion]
  refine ⟨_, hmem, ?_⟩
  have := hL.2.2 _ hmem
  exact (φ.isLine _ (hLR _ (List.getElem_mem _)) _ (hLR _ (List.mem_rotate.mp (List.getElem_mem _)))
    this).left_mem

/-- An open connected set that misses the drawn set and has its frontier in the drawn set is a
face. -/
theorem mem_faces_of_frontier {f : Set ℂ} (hfo : IsOpen f) (hfc : IsConnected f)
    (hfU : f ⊆ φ.Uᶜ) (hfr : frontier f ⊆ φ.U) : f ∈ φ.faces := by
  obtain ⟨z, hz⟩ := hfc.nonempty
  have hfU' : f ⊆ univ \ φ.U := fun w hw => ⟨mem_univ _, hfU hw⟩
  refine ⟨z, hfU' hz, Subset.antisymm ?_ (hfc.isPreconnected.subset_connectedComponentIn hz hfU')⟩
  refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hfo
    ⟨z, mem_connectedComponentIn (hfU' hz), hz⟩ ?_
  rintro w ⟨hw1, hw2⟩
  rw [closure_eq_self_union_frontier] at hw1
  rcases hw1 with h | h
  · exact h
  · exact absurd (hfr h) (connectedComponentIn_subset _ _ hw2).2

/-- **The faces of a restricted embedding.** Restrict `φ` to the set `R₁` of the vertices drawn in
the closed inner domain of the image `F₁` of a cycle `C₁`. Suppose that the lines of the edges on
`R₁` stay in this closed domain, and that every drawn point inside `F₁` is drawn by `R₁`. Then the
restricted embedding has the faces of a rib with frame `C₁`. -/
theorem isRibEmbedding_restrict {C : List V} (hφ : φ.IsRibEmbedding C) {C₁ : List V}
    (hC₁ : IsCycleList G C₁) {R₁ : Set V} (hR₁ : R₁ ⊆ R) (hC₁R : ∀ x ∈ C₁, x ∈ R₁)
    (hR₁def : ∀ v ∈ R, φ.pt v ∈ inner (φ.cycleImage C₁) ∪ φ.cycleImage C₁ → v ∈ R₁)
    (hpt : ∀ v ∈ R₁, φ.pt v ∈ inner (φ.cycleImage C₁) ∪ φ.cycleImage C₁)
    (hline : ∀ u ∈ R₁, ∀ v ∈ R₁, G.Adj u v →
      φ.line u v ⊆ inner (φ.cycleImage C₁) ∪ φ.cycleImage C₁)
    (hU : ∀ z ∈ φ.U, z ∈ inner (φ.cycleImage C₁) → z ∈ (φ.restrict hR₁).U) :
    (φ.restrict hR₁).IsRibEmbedding C₁ := by
  set ψ := φ.restrict hR₁ with hψ
  set F₁ := φ.cycleImage C₁ with hF₁
  have hψF : ψ.cycleImage C₁ = F₁ := rfl
  have J₁ : IsJordanParts F₁ := isJordanParts (ψ.isOArc_cycleImage hC₁ hC₁R).some
  have hUψ : ψ.U ⊆ inner F₁ ∪ F₁ := by
    rintro z (⟨v, hv, rfl⟩ | hz)
    · exact hpt v hv
    · simp only [mem_iUnion] at hz
      obtain ⟨u, hu, v, hv, huv, hz⟩ := hz
      exact hline u hu v hv huv hz
  have hFψ : F₁ ⊆ ψ.U := ψ.cycleImage_subset_U hC₁ hC₁R
  have hψφ : ψ.U ⊆ φ.U := by
    rintro z (⟨v, hv, rfl⟩ | hz)
    · exact φ.pt_mem_U (hR₁ hv)
    · simp only [mem_iUnion] at hz
      obtain ⟨u, hu, v, hv, huv, hz⟩ := hz
      exact φ.line_subset_U (hR₁ hu) (hR₁ hv) huv hz
  have hout : outer F₁ ⊆ ψ.Uᶜ := fun z hz hzU => by
    rcases hUψ hzU with h | h
    · exact Set.disjoint_left.mp J₁.disjoint h hz
    · exact hz.1 h
  -- a face of `ψ` lies inside or outside `F₁`
  have hside : ∀ r ∈ ψ.faces, r ⊆ inner F₁ ∨ r = outer F₁ := by
    intro r hr
    obtain ⟨hro, hrc, hrU⟩ := ψ.isOpen_of_mem_faces hr
    have hrF : Disjoint r F₁ := Set.disjoint_left.mpr fun z hz hzF => hrU hz (hFψ hzF)
    obtain ⟨z, hz⟩ := hrc.nonempty
    have hzF : z ∈ F₁ᶜ := fun h => Set.disjoint_left.mp hrF hz h
    rw [← J₁.union_eq] at hzF
    rcases hzF with hzi | hzo
    · exact Or.inl (J₁.subset_inner hrc.isPreconnected hrF ⟨z, hz, hzi⟩)
    · right
      have h1 := J₁.subset_outer hrc.isPreconnected hrF ⟨z, hz, hzo⟩
      exact Subset.antisymm h1 (ψ.subset_face hr J₁.isConnected_outer.isPreconnected hout hzo hz)
  refine ⟨fun r hr hb => ?_, fun r hr hb => ?_, fun a b c hT => ?_⟩
  · -- the unbounded face is the outer domain of `F₁`
    rcases hside r hr with h | rfl
    · exact absurd (J₁.isBounded_inner.subset h) hb
    · exact J₁.frontier_outer
  · -- a bounded face of `ψ` is a face of `φ`
    have hri : r ⊆ inner F₁ := by
      rcases hside r hr with h | rfl
      · exact h
      · exact absurd hb J₁.not_isBounded_outer
    obtain ⟨hro, hrc, hrU⟩ := ψ.isOpen_of_mem_faces hr
    have hrφ : r ⊆ φ.Uᶜ := fun z hz hzU => hrU hz (hU z hzU (hri hz))
    obtain ⟨z, hz⟩ := hrc.nonempty
    obtain ⟨hf', hzf'⟩ := φ.mem_faces_of_notMem (hrφ hz)
    set r' := connectedComponentIn (univ \ φ.U) z
    have hrr' : r ⊆ r' := φ.subset_face hf' hrc.isPreconnected hrφ hz hzf'
    obtain ⟨hro', hrc', hrU'⟩ := φ.isOpen_of_mem_faces hf'
    have hr'F : Disjoint r' F₁ := Set.disjoint_left.mpr fun w hw hwF => hrU' hw (hψφ (hFψ hwF))
    have hr'i : r' ⊆ inner F₁ := J₁.subset_inner hrc'.isPreconnected hr'F ⟨z, hzf', hri hz⟩
    have hr'ψ : r' ⊆ ψ.Uᶜ := fun w hw hwU => hrU' hw (hψφ hwU)
    have he : r = r' := Subset.antisymm hrr' (ψ.subset_face hr hrc'.isPreconnected hr'ψ hzf' hz)
    obtain ⟨a, b, c, hT, hfr⟩ := hφ.2.1 r' hf' (J₁.isBounded_inner.subset hr'i)
    have hcl : frontier r' ⊆ inner F₁ ∪ F₁ := by
      rw [← J₁.closure_inner]
      exact frontier_subset_closure.trans (closure_mono hr'i)
    have hvert : ∀ v ∈ [a, b, c], v ∈ R₁ := by
      intro v hv
      have hvR : v ∈ R := hT.mem v hv
      refine hR₁def v hvR (hcl ?_)
      rw [hfr]
      exact φ.pt_mem_cycleImage hT.isCycleList hT.mem hv
    obtain ⟨-, -, -, hab, hbc, hac⟩ := hT
    refine ⟨a, b, c, ⟨hvert a (by simp), hvert b (by simp), hvert c (by simp), hab, hbc, hac⟩, ?_⟩
    rw [he]
    exact hfr
  · -- a triangle of `R₁` bounds a face of `φ`, which is a face of `ψ`
    obtain ⟨ha, hb, hc, hab, hbc, hac⟩ := hT
    have hT' : IsTriangleOn G R a b c := ⟨hR₁ ha, hR₁ hb, hR₁ hc, hab, hbc, hac⟩
    obtain ⟨r, hr, hrb, hfr⟩ := hφ.2.2 a b c hT'
    obtain ⟨hro, hrc, hrU⟩ := φ.isOpen_of_mem_faces hr
    refine ⟨r, ψ.mem_faces_of_frontier hro hrc (fun z hz hzU => hrU hz (hψφ hzU)) ?_, hrb, hfr⟩
    rw [hfr]
    have hT₁ : IsTriangleOn G R₁ a b c := ⟨ha, hb, hc, hab, hbc, hac⟩
    exact ψ.cycleImage_subset_U (IsTriangleOn.isCycleList hT₁) (IsTriangleOn.mem hT₁)

end PlaneEmbedding

end GraphMinor.HP25
