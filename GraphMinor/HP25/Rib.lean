module

public import GraphMinor.HP25.Embedding

/-!
# The faces of a rib, and Proposition 2.2

Humeau and Pous, arXiv:2505.16431v2, Section 2.2 (page 6).

In a plane embedding with the faces of a rib with frame `C` (`PlaneEmbedding.IsRibEmbedding`), the
image `F` of the frame is an `O`-arc. The unbounded face has frontier `F`, so it is the outer domain
of `F` (`PlaneEmbedding.eq_outer_of_frontier`), and the drawing misses the outer domain
(`PlaneEmbedding.IsRibEmbedding.disjoint_outer`). Likewise the face bounded by a triangle is the inner
domain of the image of the triangle (`PlaneEmbedding.IsRibEmbedding.inner_mem_faces`).

**Proposition 2.2** (`isRibOn_three_iff`, `isWebOn_three_iff`): "The $3$-ribs are the triangles;
the $3$-webs are the cliques of order at least $3$." The paper states it without proof. For a rib with
frame the triangle `abc`, the frame bounds both the outer face and an inner face, so the drawing
misses both domains of the image `F` of the frame and lies on `F`. Then every vertex is drawn on one of
the three lines of the frame, and so it is `a`, `b` or `c`. Conversely the triangle drawn with
straight sides between `0`, `1` and `i` is a rib.
-/

@[expose] public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

/-- A triangle is a cycle of length three. -/
theorem IsTriangleOn.isCycleList {a b c : V} (h : IsTriangleOn G R a b c) :
    IsCycleList G [a, b, c] := by
  obtain ⟨-, -, -, hab, hbc, hac⟩ := h
  refine ⟨by simp, ?_, ?_⟩
  · simp [hab.ne, hbc.ne, hac.ne]
  · simp [List.rotate, hab, hbc, hac.symm]

theorem IsTriangleOn.mem {a b c : V} (h : IsTriangleOn G R a b c) : ∀ x ∈ [a, b, c], x ∈ R := by
  obtain ⟨ha, hb, hc, -⟩ := h
  simp [ha, hb, hc]

namespace PlaneEmbedding

variable (φ : PlaneEmbedding G R)

/-- The image of a triangle `abc` is the union of its three lines. -/
theorem cycleImage_three (a b c : V) :
    φ.cycleImage [a, b, c] = φ.line a b ∪ φ.line b c ∪ φ.line c a := by
  ext z
  simp [cycleImage, List.rotate, or_assoc]

/-- The image of a cycle of `G` on `R` lies in the drawn set. -/
theorem cycleImage_subset_U {C : List V} (hC : IsCycleList G C) (hR : ∀ x ∈ C, x ∈ R) :
    φ.cycleImage C ⊆ φ.U := by
  intro z hz
  simp only [cycleImage, mem_iUnion] at hz
  obtain ⟨p, hp, hz⟩ := hz
  exact φ.line_subset_U (hR _ (List.of_mem_zip hp).1)
    (hR _ (List.mem_rotate.mp (List.of_mem_zip hp).2)) (hC.2.2 p hp) hz

variable {φ}

/-- In an embedding with the faces of a rib, the drawn set misses the outer domain of the image of
the frame: the unbounded face is this outer domain. -/
theorem IsRibEmbedding.disjoint_outer {C : List V} (h : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) : Disjoint φ.U (outer (φ.cycleImage C)) := by
  obtain ⟨r, hr, hb⟩ := φ.exists_unbounded_face
  have J := isJordanParts (φ.isOArc_cycleImage hC hR).some
  rw [← φ.eq_outer_of_frontier J hr (φ.cycleImage_subset_U hC hR) (h.1 r hr hb) hb]
  exact disjoint_compl_right.mono_right (φ.isOpen_of_mem_faces hr).2.2

/-- In an embedding with the faces of a rib, the inner domain of the image of a triangle is a face,
and so it misses the drawn set. -/
theorem IsRibEmbedding.inner_mem_faces {C : List V} (h : φ.IsRibEmbedding C) {a b c : V}
    (hT : IsTriangleOn G R a b c) :
    inner (φ.cycleImage [a, b, c]) ∈ φ.faces ∧ Disjoint φ.U (inner (φ.cycleImage [a, b, c])) := by
  obtain ⟨r, hr, hb, hfr⟩ := h.2.2 a b c hT
  have J := isJordanParts (φ.isOArc_cycleImage hT.isCycleList hT.mem).some
  rw [← φ.eq_inner_of_frontier J hr (φ.cycleImage_subset_U hT.isCycleList hT.mem) hfr hb]
  exact ⟨hr, disjoint_compl_right.mono_right (φ.isOpen_of_mem_faces hr).2.2⟩

end PlaneEmbedding

/-! ### Proposition 2.2 -/

/-- Proposition 2.2, the direction from ribs to triangles: a rib with frame `abc` has only the
vertices `a`, `b`, `c`. The image `F` of the frame bounds the outer face and, as the image of a
triangle, an inner face. So the drawing misses both domains of `F`, and every vertex is drawn on one
of the three lines of the frame. A line passes through no vertex but its ends. -/
theorem IsRibOn.eq_three {a b c : V} (h : IsRibOn G R [a, b, c]) : R = {a, b, c} := by
  obtain ⟨hC, hR, φ, hφ⟩ := h
  have hT : IsTriangleOn G R a b c := by
    have h1 := hC.2.2 (a, b) (by simp [List.rotate])
    have h2 := hC.2.2 (b, c) (by simp [List.rotate])
    have h3 := hC.2.2 (c, a) (by simp [List.rotate])
    exact ⟨hR a (by simp), hR b (by simp), hR c (by simp), h1, h2, h3.symm⟩
  have J := isJordanParts (φ.isOArc_cycleImage hC hR).some
  have hout := hφ.disjoint_outer hC hR
  have hin := (hφ.inner_mem_faces hT).2
  refine Subset.antisymm (fun v hv => ?_) (by
    rintro x (rfl | rfl | rfl)
    · exact hT.1
    · exact hT.2.1
    · exact hT.2.2.1)
  have hvU := φ.pt_mem_U hv
  have hvF : φ.pt v ∈ φ.cycleImage [a, b, c] := by
    by_contra hn
    have : φ.pt v ∈ inner (φ.cycleImage [a, b, c]) ∪ outer (φ.cycleImage [a, b, c]) := by
      rw [J.union_eq]; exact hn
    rcases this with h | h
    · exact disjoint_left.mp hin hvU h
    · exact disjoint_left.mp hout hvU h
  rw [φ.cycleImage_three] at hvF
  obtain ⟨ha, hb, hc, hab, hbc, hac⟩ := hT
  rcases hvF with (h | h) | h
  · rcases φ.avoid a ha b hb hab v hv h with rfl | rfl <;> simp
  · rcases φ.avoid b hb c hc hbc v hv h with rfl | rfl <;> simp
  · rcases φ.avoid c hc a ha hac.symm v hv h with rfl | rfl <;> simp

end GraphMinor.HP25
