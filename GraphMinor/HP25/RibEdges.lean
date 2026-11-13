module

public import GraphMinor.HP25.EdgeFaces
import GraphMinor.Surface.SurfaceGraph

/-!
# The triangles at an edge of a rib

In a plane embedding with the faces of a rib with frame `C`, every face is the outer domain of the
image of `C` or the inner domain of the image of a triangle (`IsRibEmbedding.face_cases`). With the
two faces at an edge (`PlaneEmbedding.edge_faces`) this counts the triangles through an edge `xy`,
that is the common neighbours of `x` and `y` (`IsRibEmbedding.common_neighbours`):
* there are at most two;
* if `xy` is an edge of the frame there is exactly one: the outer face is on one side of `xy`;
* otherwise there are two: both faces at `xy` are triangles, and different.

This is the fact "an edge may bound at most two faces" of the proof of Lemma 3.3 of Humeau and Pous
(page 10), and the step "Each consecutive pair of edges bounds a common face" of the proof of
Proposition 2.3 (page 7).
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

/-- An edge `xy` of the triangle `abc` determines the third vertex `z` of the triangle, a common
neighbour of `x` and `y`. -/
theorem IsTriangleOn.third {a b c x y : V} (hT : IsTriangleOn G R a b c)
    (he : PlaneEmbedding.IsCycleEdge [a, b, c] x y) :
    ∃ z, z ∈ R ∧ G.Adj x z ∧ G.Adj y z ∧ ({a, b, c} : Set V) = {x, y, z} := by
  obtain ⟨ha, hb, hc, hab, hbc, hac⟩ := hT
  obtain ⟨q, hq, hqe⟩ : ∃ p ∈ [a, b, c].zip ([a, b, c].rotate 1), s(x, y) = s(p.1, p.2) := he
  have hz : [a, b, c].zip ([a, b, c].rotate 1) = [(a, b), (b, c), (c, a)] := rfl
  rw [hz] at hq
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> rcases Sym2.eq_iff.mp hqe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨c, hc, hac, hbc, rfl⟩
  · exact ⟨c, hc, hbc, hac, by ext; simp; tauto⟩
  · exact ⟨a, ha, hab.symm, hac.symm, by ext; simp; tauto⟩
  · exact ⟨a, ha, hac.symm, hab.symm, by ext; simp; tauto⟩
  · exact ⟨b, hb, hbc.symm, hab, by ext; simp; tauto⟩
  · exact ⟨b, hb, hab, hbc.symm, by ext; simp; tauto⟩

namespace PlaneEmbedding

variable {φ : PlaneEmbedding G R} {C : List V}

/-- In a rib embedding, every face is the outer domain of the frame or the inner domain of a
triangle. -/
theorem IsRibEmbedding.face_cases (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) {f : Set ℂ} (hf : f ∈ φ.faces) :
    f = outer (φ.cycleImage C) ∨
      ∃ a b c, IsTriangleOn G R a b c ∧ f = Surface.inner (φ.cycleImage [a, b, c]) := by
  by_cases hb : Bornology.IsBounded f
  · obtain ⟨a, b, c, hT, hfr⟩ := hφ.2.1 f hf hb
    exact Or.inr ⟨a, b, c, hT, φ.eq_inner_of_frontier
      (isJordanParts (φ.isOArc_cycleImage hT.isCycleList hT.mem).some) hf
      (φ.cycleImage_subset_U hT.isCycleList hT.mem) hfr hb⟩
  · exact Or.inl (φ.eq_outer_of_frontier (isJordanParts (φ.isOArc_cycleImage hC hR).some) hf
      (φ.cycleImage_subset_U hC hR) (hφ.1 f hf hb) hb)

/-- In a rib embedding, the outer domain of the frame is a face. -/
theorem IsRibEmbedding.outer_mem_faces (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) : outer (φ.cycleImage C) ∈ φ.faces := by
  obtain ⟨r, hr, hb⟩ := φ.exists_unbounded_face
  rw [← φ.eq_outer_of_frontier (isJordanParts (φ.isOArc_cycleImage hC hR).some) hr
    (φ.cycleImage_subset_U hC hR) (hφ.1 r hr hb) hb]
  exact hr

/-- **Triangles at an edge of a rib.** For an edge `xy` of a rib with frame `C`, the common
neighbours of `x` and `y` in the rib: at most two; exactly one if `xy` is an edge of `C`; two
otherwise. -/
theorem IsRibEmbedding.common_neighbours (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) {x y : V} (hx : x ∈ R) (hy : y ∈ R) (hxy : G.Adj x y) :
    {z | z ∈ R ∧ G.Adj x z ∧ G.Adj y z}.encard ≤ 2 ∧
      (IsCycleEdge C x y → {z | z ∈ R ∧ G.Adj x z ∧ G.Adj y z}.encard ≤ 1 ∧
        {z | z ∈ R ∧ G.Adj x z ∧ G.Adj y z}.Nonempty) ∧
      (¬ IsCycleEdge C x y → ∃ z₁ z₂, z₁ ≠ z₂ ∧ (z₁ ∈ R ∧ G.Adj x z₁ ∧ G.Adj y z₁) ∧
        (z₂ ∈ R ∧ G.Adj x z₂ ∧ G.Adj y z₂)) := by
  set N := {z | z ∈ R ∧ G.Adj x z ∧ G.Adj y z} with hN
  obtain ⟨f₁, hf₁, f₂, hf₂, hL1, hL2, hall, hdiff⟩ := φ.edge_faces hx hy hxy
  obtain ⟨p, hpL, hp1, hp2⟩ := exists_inner_point (φ.isLine x hx y hy hxy)
  have JF := isJordanParts (φ.isOArc_cycleImage hC hR).some
  have hFU := φ.cycleImage_subset_U hC hR
  -- the triangle face of a common neighbour
  have htri : ∀ z ∈ N, IsTriangleOn G R x y z := fun z hz => ⟨hx, hy, hz.1, hxy, hz.2.2, hz.2.1⟩
  set g : V → Set ℂ := fun z => Surface.inner (φ.cycleImage [x, y, z]) with hg
  have hJ : ∀ z ∈ N, IsJordanParts (φ.cycleImage [x, y, z]) := fun z hz =>
    isJordanParts (φ.isOArc_cycleImage (htri z hz).isCycleList (htri z hz).mem).some
  have hgf : ∀ z ∈ N, g z = f₁ ∨ g z = f₂ := by
    intro z hz
    refine hall _ (hφ.inner_mem_faces (htri z hz)).1 p hpL hp1 hp2 ?_
    have : p ∈ frontier (g z) := by
      rw [(hJ z hz).frontier_inner, φ.cycleImage_three]
      exact Or.inl (Or.inl hpL)
    exact this.1
  have hginj : InjOn g N := by
    intro z hz z' hz' he
    have hT : φ.cycleImage [x, y, z] = φ.cycleImage [x, y, z'] := by
      rw [← (hJ z hz).frontier_inner, ← (hJ z' hz').frontier_inner]
      exact congrArg frontier he
    have hpz : φ.pt z ∈ φ.cycleImage [x, y, z'] := by
      rw [← hT, φ.cycleImage_three]
      exact Or.inl (Or.inr (φ.isLine y hy z hz.1 hz.2.2).right_mem)
    rw [φ.cycleImage_three] at hpz
    rcases hpz with (h | h) | h
    · rcases φ.avoid x hx y hy hxy z hz.1 h with rfl | rfl
      · exact absurd hz.2.1 (G.loopless.irrefl _)
      · exact absurd hz.2.2 (G.loopless.irrefl _)
    · rcases φ.avoid y hy z' hz'.1 hz'.2.2 z hz.1 h with rfl | rfl
      · exact absurd hz.2.2 (G.loopless.irrefl _)
      · rfl
    · rcases φ.avoid z' hz'.1 x hx hz'.2.1.symm z hz.1 h with rfl | rfl
      · rfl
      · exact absurd hz.2.1 (G.loopless.irrefl _)
  have hgb : ∀ z ∈ N, g z ≠ outer (φ.cycleImage C) := fun z hz he =>
    JF.not_isBounded_outer (he ▸ (hJ z hz).isBounded_inner)
  have hcard : ∀ S : Set (Set ℂ), g '' N ⊆ S → N.encard ≤ S.encard := fun S hS => by
    rw [← hginj.encard_image]
    exact encard_le_encard hS
  have hpair : ({f₁, f₂} : Set (Set ℂ)).encard ≤ 2 := by
    refine (encard_insert_le _ _).trans ?_
    rw [encard_singleton]
    norm_num
  -- a bounded face at `xy` gives a common neighbour
  have hthird : ∀ f ∈ φ.faces, f ≠ outer (φ.cycleImage C) → φ.line x y ⊆ frontier f →
      ∃ z ∈ N, f = g z := by
    intro f hf hne hLf
    rcases hφ.face_cases hC hR hf with h | ⟨a, b, c, hT, rfl⟩
    · exact absurd h hne
    · have hJT := isJordanParts (φ.isOArc_cycleImage hT.isCycleList hT.mem).some
      rw [hJT.frontier_inner] at hLf
      have he := (line_subset_cycleImage_iff hT.isCycleList hT.mem hx hy hxy).mp hLf
      obtain ⟨z, hz, hxz, hyz, hset⟩ := hT.third he
      refine ⟨z, ⟨hz, hxz, hyz⟩, ?_⟩
      obtain ⟨-, -, -, hab, hbc, hac⟩ := hT
      simp only [g]
      rw [cycleImage_three_eq hab.ne hbc.ne hac.ne hxy.ne hyz.ne hxz.ne hset]
  -- the two faces at `xy` are different
  have hf12 : f₁ ≠ f₂ := by
    rcases hφ.face_cases hC hR hf₁ with h | ⟨a, b, c, hT, h⟩
    · rw [h, JF.frontier_outer] at hL1
      exact hdiff _ JF hFU hL1
    · have hJT := isJordanParts (φ.isOArc_cycleImage hT.isCycleList hT.mem).some
      rw [h, hJT.frontier_inner] at hL1
      exact hdiff _ hJT (φ.cycleImage_subset_U hT.isCycleList hT.mem) hL1
  refine ⟨hcard _ (fun _ ⟨z, hz, he⟩ => he ▸ hgf z hz) |>.trans hpair, fun hfr => ?_, fun hfr => ?_⟩
  · have hLF := (line_subset_cycleImage_iff (φ := φ) hC hR hx hy hxy).mpr hfr
    have hout : outer (φ.cycleImage C) = f₁ ∨ outer (φ.cycleImage C) = f₂ := by
      refine hall _ (hφ.outer_mem_faces hC hR) p hpL hp1 hp2 ?_
      have : p ∈ frontier (outer (φ.cycleImage C)) := by rw [JF.frontier_outer]; exact hLF hpL
      exact this.1
    rcases hout with h | h
    · refine ⟨hcard {f₂} ?_ |>.trans (by simp), ?_⟩
      · rintro _ ⟨z, hz, rfl⟩
        rcases hgf z hz with h' | h'
        · exact absurd (h'.trans h.symm) (hgb z hz)
        · exact h'
      · obtain ⟨z, hz, -⟩ := hthird f₂ hf₂ (fun h' => hf12 (h.symm.trans h'.symm)) hL2
        exact ⟨z, hz⟩
    · refine ⟨hcard {f₁} ?_ |>.trans (by simp), ?_⟩
      · rintro _ ⟨z, hz, rfl⟩
        rcases hgf z hz with h' | h'
        · exact h'
        · exact absurd (h'.trans h.symm) (hgb z hz)
      · obtain ⟨z, hz, -⟩ := hthird f₁ hf₁ (fun h' => hf12 (h'.trans h)) hL1
        exact ⟨z, hz⟩
  · have hno : ∀ f, φ.line x y ⊆ frontier f → f ≠ outer (φ.cycleImage C) := by
      rintro f hLf rfl
      rw [JF.frontier_outer] at hLf
      exact hfr ((line_subset_cycleImage_iff (φ := φ) hC hR hx hy hxy).mp hLf)
    obtain ⟨z₁, hz₁, he₁⟩ := hthird f₁ hf₁ (hno f₁ hL1) hL1
    obtain ⟨z₂, hz₂, he₂⟩ := hthird f₂ hf₂ (hno f₂ hL2) hL2
    refine ⟨z₁, z₂, fun h => hf12 ?_, hz₁, hz₂⟩
    rw [he₁, he₂, h]

end PlaneEmbedding

end GraphMinor.HP25
