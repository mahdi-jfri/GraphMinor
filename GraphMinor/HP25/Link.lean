module

public import GraphMinor.HP25.RibEdges
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Order.IntermediateValue
import GraphMinor.Surface.SurfaceGraph
import GraphMinor.Surface.TriLocal

/-!
# The link of a vertex of a rib is connected

Humeau and Pous, proof of Proposition 2.3 (pages 6–7): "In the embedding of $R$, the edges going out
from $x$ form a star whose centre is $x$ ... Each consecutive pair of edges bounds a common face".
The paper uses the cyclic order of the edges around `x`. We do not build this order. The part of it
that the proof needs is that the neighbours of `x` cannot split into two groups with no triangle
`x a b` between the groups (`IsRibEmbedding.link_closed`).

The argument. Let `K` be a set of neighbours of `x` that is closed under taking common neighbours
with `x`, and such that no edge `xa` with `a ∈ K` is on the frame. Let `A` be the union of the closed
triangles `x a b` with `a, b ∈ K`. Take a small circle `S` around the point of `x`, which meets only
the lines of edges at `x`. A point of `S` in `A` is an interior point of `A`: it lies in a face of
`A`, or on the line of an edge `xa` with `a ∈ K`, and then both faces at `xa` are triangles of `A`.
So `S ∩ A` is open and closed in `S`. The circle is connected and the line of an edge `xa` with
`a ∈ K` meets it, so `S ⊆ A`. The line of each edge `xw` meets `S`, and a point of `A` on that
line forces `w ∈ K`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface Metric

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

namespace PlaneEmbedding

variable {φ : PlaneEmbedding G R} {C : List V}

/-- A bounded face with the line of `xy` on its frontier is a triangle `xyz`. -/
theorem IsRibEmbedding.eq_triangle_of_frontier (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) {x y : V} (hx : x ∈ R) (hy : y ∈ R) (hxy : G.Adj x y) {f : Set ℂ}
    (hf : f ∈ φ.faces) (hne : f ≠ outer (φ.cycleImage C)) (hLf : φ.line x y ⊆ frontier f) :
    ∃ z, z ∈ R ∧ G.Adj x z ∧ G.Adj y z ∧ f = Surface.inner (φ.cycleImage [x, y, z]) := by
  rcases hφ.face_cases hC hR hf with h | ⟨a, b, c, hT, rfl⟩
  · exact absurd h hne
  · have hJT := isJordanParts (φ.isOArc_cycleImage hT.isCycleList hT.mem).some
    rw [hJT.frontier_inner] at hLf
    have he := (line_subset_cycleImage_iff (φ := φ) hT.isCycleList hT.mem hx hy hxy).mp hLf
    obtain ⟨z, hz, hxz, hyz, hset⟩ := hT.third he
    refine ⟨z, hz, hxz, hyz, ?_⟩
    obtain ⟨-, -, -, hab, hbc, hac⟩ := hT
    rw [cycleImage_three_eq hab.ne hbc.ne hac.ne hxy.ne hyz.ne hxz.ne hset]

/-- At an edge `xy` off the frame, a face whose closure meets the line of `xy` away from its ends is
a triangle `xyz`. -/
theorem IsRibEmbedding.face_at_inner_edge (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) {x y : V} (hx : x ∈ R) (hy : y ∈ R) (hxy : G.Adj x y)
    (hxyC : ¬ IsCycleEdge C x y) {f : Set ℂ} (hf : f ∈ φ.faces) {p : ℂ} (hp : p ∈ φ.line x y)
    (hp1 : p ≠ φ.pt x) (hp2 : p ≠ φ.pt y) (hpf : p ∈ closure f) :
    ∃ z, z ∈ R ∧ G.Adj x z ∧ G.Adj y z ∧ f = Surface.inner (φ.cycleImage [x, y, z]) := by
  obtain ⟨f₁, hf₁, f₂, hf₂, hL1, hL2, hall, -⟩ := φ.edge_faces hx hy hxy
  have JF := isJordanParts (φ.isOArc_cycleImage hC hR).some
  have hno : ∀ g, φ.line x y ⊆ frontier g → g ≠ outer (φ.cycleImage C) := by
    rintro g hLg rfl
    rw [JF.frontier_outer] at hLg
    exact hxyC ((line_subset_cycleImage_iff hC hR hx hy hxy).mp hLg)
  rcases hall f hf p hp hp1 hp2 hpf with rfl | rfl
  · exact hφ.eq_triangle_of_frontier hC hR hx hy hxy hf (hno _ hL1) hL1
  · exact hφ.eq_triangle_of_frontier hC hR hx hy hxy hf (hno _ hL2) hL2

/-- In a rib embedding every vertex has a neighbour. Otherwise a small punctured disc around the point
of `x` misses the drawing, so it lies in one face, and the point of `x` is on the frontier of this
face. This frontier is the image of a cycle, and a vertex on the image of a cycle is a vertex of the
cycle, with neighbours on it. -/
theorem IsRibEmbedding.exists_adj (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) {x : V} (hx : x ∈ R) : ∃ a, a ∈ R ∧ G.Adj x a := by
  by_contra hno
  push Not at hno
  -- the point of `x` is on no line
  have hline : ∀ u ∈ R, ∀ v ∈ R, G.Adj u v → φ.pt x ∉ φ.line u v := by
    intro u hu v hv huv h
    rcases φ.avoid u hu v hv huv x hx h with rfl | rfl
    · exact hno v hv huv
    · exact hno u hu huv.symm
  have hcyc : ∀ L : List V, IsCycleList G L → (∀ y ∈ L, y ∈ R) → φ.pt x ∉ φ.cycleImage L := by
    intro L hL hLR h
    simp only [cycleImage, mem_iUnion] at h
    obtain ⟨q, hq, h⟩ := h
    have h1 := List.of_mem_zip hq
    exact hline _ (hLR _ h1.1) _ (hLR _ (List.mem_rotate.mp h1.2)) (hL.2.2 q hq) h
  set Z : Set ℂ := φ.pt '' (R \ {x}) ∪ ⋃ u ∈ R, ⋃ v ∈ R, ⋃ (_ : G.Adj u v), φ.line u v with hZ
  have hZc : IsClosed Z := (((φ.finite.subset sdiff_subset).image _).isCompact.union
    (φ.finite.isCompact_biUnion fun u hu => φ.finite.isCompact_biUnion fun v hv =>
      isCompact_iUnion fun h => (φ.isLine u hu v hv h).isCompact)).isClosed
  have hxZ : φ.pt x ∉ Z := by
    rintro (⟨v, ⟨hv, hvx⟩, he⟩ | h)
    · exact hvx (φ.injOn hv hx he)
    · simp only [mem_iUnion] at h
      obtain ⟨u, hu, v, hv, huv, h⟩ := h
      exact hline u hu v hv huv h
  obtain ⟨ε, hε, hεZ⟩ := Metric.isOpen_iff.mp hZc.isOpen_compl _ hxZ
  -- a punctured disc around the point of `x`
  set g : ℂ → ℂ := fun z => φ.pt x + ((ε / 2 : ℝ) : ℂ) * z with hg
  have hgc : Continuous g := by fun_prop
  set P := g '' (ball (0 : ℂ) 1 \ {0}) with hP
  have hPc : IsPreconnected P := punctured_unit_ball.image g hgc.continuousOn
  have hPU : P ⊆ φ.Uᶜ := by
    rintro _ ⟨z, ⟨hz1, hz2⟩, rfl⟩ hU
    have hz0 : z ≠ 0 := hz2
    have hB : g z ∈ ball (φ.pt x) ε := by
      rw [mem_ball, dist_eq_norm]
      simp only [hg, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [mem_ball, dist_zero_right] at hz1
      rw [abs_of_pos (by positivity)]
      nlinarith [norm_nonneg z]
    have hne : g z ≠ φ.pt x := by
      intro h
      simp only [hg, add_eq_left, mul_eq_zero, Complex.ofReal_eq_zero] at h
      rcases h with h | h
      · linarith
      · exact hz0 h
    rcases hU with ⟨v, hv, hve⟩ | hU
    · by_cases hvx : v = x
      · rw [hvx] at hve; exact hne hve.symm
      · exact hεZ hB (Or.inl ⟨v, ⟨hv, hvx⟩, hve⟩)
    · exact hεZ hB (Or.inr hU)
  have hxP : φ.pt x ∈ closure P := by
    have h0 : (0 : ℂ) ∈ closure (ball (0 : ℂ) 1 \ {0}) := by
      rw [Set.sdiff_eq]
      exact isOpen_ball.inter_closure ⟨mem_ball_self one_pos, by rw [closure_compl_singleton]; trivial⟩
    exact image_closure_subset_closure_image hgc ⟨0, h0, by simp [hg]⟩
  have hq : g (1 / 2) ∈ P := ⟨1 / 2, ⟨by rw [mem_ball, dist_zero_right]; norm_num, by norm_num⟩, rfl⟩
  obtain ⟨hf, hqf⟩ := φ.mem_faces_of_notMem (hPU hq)
  set f := connectedComponentIn (univ \ φ.U) (g (1 / 2))
  have hfo := φ.isOpen_of_mem_faces hf
  have hPf : P ⊆ f := φ.subset_face hf hPc hPU hq hqf
  have hfr : φ.pt x ∈ frontier f := by
    rw [frontier, hfo.1.interior_eq]
    exact ⟨closure_mono hPf hxP, fun h => hfo.2.2 h (φ.pt_mem_U hx)⟩
  by_cases hb : Bornology.IsBounded f
  · obtain ⟨a, b, c, hT, he⟩ := hφ.2.1 f hf hb
    rw [he] at hfr
    exact hcyc _ hT.isCycleList hT.mem hfr
  · rw [hφ.1 f hf hb] at hfr
    exact hcyc C hC hR hfr

/-- **The link of a vertex is connected.** Let `K` be a nonempty set of neighbours of `x` such that
a neighbour of `x` adjacent to a vertex of `K` is in `K`, and no edge from `x` to `K` is an edge of
the frame. Then every neighbour of `x` is in `K`. -/
theorem IsRibEmbedding.link_closed (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) {x : V} (hx : x ∈ R) {K : Set V} (hKN : ∀ a ∈ K, a ∈ R ∧ G.Adj x a)
    (hKne : K.Nonempty) (hKcl : ∀ a ∈ K, ∀ b ∈ R, G.Adj x b → G.Adj a b → b ∈ K)
    (hKC : ∀ a ∈ K, ¬ IsCycleEdge C x a) {w : V} (hw : w ∈ R) (hxw : G.Adj x w) : w ∈ K := by
  classical
  by_contra hwK
  -- the closed triangles `x a b` with `a, b ∈ K`
  set A : Set ℂ := ⋃ a ∈ K, ⋃ b ∈ K, ⋃ (_ : G.Adj a b),
    closure (Surface.inner (φ.cycleImage [x, a, b])) with hA
  have hKfin : K.Finite := φ.finite.subset fun a ha => (hKN a ha).1
  have hAc : IsClosed A := hKfin.isClosed_biUnion fun a _ => hKfin.isClosed_biUnion fun b _ =>
    isClosed_iUnion_of_finite fun _ => isClosed_closure
  have htri : ∀ a ∈ K, ∀ b ∈ K, G.Adj a b → IsTriangleOn G R x a b := fun a ha b hb hab =>
    ⟨hx, (hKN a ha).1, (hKN b hb).1, (hKN a ha).2, hab, (hKN b hb).2⟩
  -- the drawing away from the point of `x` and the lines at `x`
  set Z : Set ℂ := φ.pt '' (R \ {x}) ∪
    ⋃ u ∈ R, ⋃ v ∈ R, ⋃ (_ : G.Adj u v ∧ u ≠ x ∧ v ≠ x), φ.line u v with hZ
  have hZc : IsClosed Z := (((φ.finite.subset sdiff_subset).image _).isCompact.union
    (φ.finite.isCompact_biUnion fun u hu => φ.finite.isCompact_biUnion fun v hv =>
      isCompact_iUnion fun h => (φ.isLine u hu v hv h.1).isCompact)).isClosed
  have hxZ : φ.pt x ∉ Z := by
    rintro (⟨v, ⟨hv, hvx⟩, he⟩ | h)
    · exact hvx (φ.injOn hv hx he)
    · simp only [mem_iUnion] at h
      obtain ⟨u, hu, v, hv, ⟨huv, hux, hvx⟩, h⟩ := h
      rcases φ.avoid u hu v hv huv x hx h with h | h
      · exact hux h.symm
      · exact hvx h.symm
  obtain ⟨ε, hε, hεZ⟩ := Metric.isOpen_iff.mp hZc.isOpen_compl _ hxZ
  have hptZ : ∀ v ∈ R, v ≠ x → φ.pt v ∈ Z := fun v hv hvx => Or.inl ⟨v, ⟨hv, hvx⟩, rfl⟩
  -- two lines at `x` meet only at the point of `x`
  have hlines : ∀ a a', a ∈ R → a' ∈ R → G.Adj x a → G.Adj x a' → ∀ p, p ∈ φ.line x a →
      p ∈ φ.line x a' → p ≠ φ.pt x → a = a' := by
    intro a a' ha ha' hxa hxa' p hp hp' hpx
    by_contra hne
    have hs : s(x, a) ≠ s(x, a') := fun h => by
      rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h1, h2⟩
      · exact hne h
      · exact hne (h2.trans h1)
    obtain ⟨v, ⟨hv1, hv2⟩, rfl⟩ := φ.inter x hx a ha x hx a' ha' hxa hxa' hs ⟨hp, hp'⟩
    rcases hv1 with rfl | rfl
    · exact hpx rfl
    · rcases hv2 with rfl | rfl
      · exact hpx rfl
      · exact hne rfl
  -- a drawn point near `x` other than `x` lies on a line at `x`
  have hUB : ∀ p ∈ φ.U, p ∈ ball (φ.pt x) ε → p ≠ φ.pt x →
      ∃ a, a ∈ R ∧ G.Adj x a ∧ p ∈ φ.line x a := by
    intro p hpU hpB hpx
    rcases hpU with ⟨v, hv, rfl⟩ | hpU
    · by_cases hvx : v = x
      · exact absurd (congrArg φ.pt hvx) hpx
      · exact absurd (hptZ v hv hvx) (hεZ hpB)
    · simp only [mem_iUnion] at hpU
      obtain ⟨u, hu, v, hv, huv, hp⟩ := hpU
      by_cases hux : u = x
      · subst hux; exact ⟨v, hv, huv, hp⟩
      · by_cases hvx : v = x
        · subst hvx; exact ⟨u, hu, huv.symm, by rwa [φ.line_comm]⟩
        · refine absurd ?_ (hεZ hpB)
          right
          simp only [mem_iUnion]
          exact ⟨u, hu, v, hv, ⟨huv, hux, hvx⟩, hp⟩
  -- a point of `A` near `x` on the line of `xa` forces `a ∈ K`
  have hstar : ∀ p ∈ A, p ∈ ball (φ.pt x) ε → p ≠ φ.pt x → ∀ a', a' ∈ R → G.Adj x a' →
      p ∈ φ.line x a' → a' ∈ K := by
    intro p hpA hpB hpx a' ha' hxa' hp
    simp only [hA, mem_iUnion] at hpA
    obtain ⟨a, ha, b, hb, hab, hpc⟩ := hpA
    have hJ := isJordanParts (φ.isOArc_cycleImage (htri a ha b hb hab).isCycleList
      (htri a ha b hb hab).mem).some
    rw [closure_eq_self_union_frontier, hJ.frontier_inner] at hpc
    have hpU := φ.line_subset_U hx ha' hxa' hp
    rcases hpc with hpi | hpc
    · exact absurd hpi (Set.disjoint_left.mp (hφ.inner_mem_faces (htri a ha b hb hab)).2 hpU)
    rw [φ.cycleImage_three] at hpc
    rcases hpc with (hpl | hpl) | hpl
    · rw [hlines a' a ha' (hKN a ha).1 hxa' (hKN a ha).2 p hp hpl hpx]; exact ha
    · refine absurd ?_ (hεZ hpB)
      right
      simp only [mem_iUnion]
      exact ⟨a, (hKN a ha).1, b, (hKN b hb).1, ⟨hab, (hKN a ha).2.ne.symm, (hKN b hb).2.ne.symm⟩, hpl⟩
    · rw [φ.line_comm] at hpl
      rw [hlines a' b ha' (hKN b hb).1 hxa' (hKN b hb).2 p hp hpl hpx]; exact hb
  -- the line of `xa` with `a ∈ K` lies in `A`
  have hlineA : ∀ a ∈ K, φ.line x a ⊆ A := by
    intro a ha
    obtain ⟨z, -, -, hz, hz'⟩ := (hφ.common_neighbours hC hR hx (hKN a ha).1 (hKN a ha).2).2.2
      (hKC a ha)
    have hzK : z ∈ K := hKcl a ha z hz.1 hz.2.1 hz.2.2
    have hJ := isJordanParts (φ.isOArc_cycleImage (htri a ha z hzK hz.2.2).isCycleList
      (htri a ha z hzK hz.2.2).mem).some
    intro p hp
    simp only [hA, mem_iUnion]
    refine ⟨a, ha, z, hzK, hz.2.2, frontier_subset_closure ?_⟩
    rw [hJ.frontier_inner, φ.cycleImage_three]
    exact Or.inl (Or.inl hp)
  -- a point of `A` near `x`, other than `x`, is an interior point of `A`
  have hint : ∀ p ∈ A, p ∈ ball (φ.pt x) ε → p ≠ φ.pt x → p ∈ interior A := by
    intro p hpA hpB hpx
    by_cases hpU : p ∈ φ.U
    · obtain ⟨a, ha, hxa, hp⟩ := hUB p hpU hpB hpx
      have haK := hstar p hpA hpB hpx a ha hxa hp
      have hpa : p ≠ φ.pt a := by
        rintro rfl
        exact hεZ hpB (hptZ a ha (hxa.ne.symm))
      have hprest : p ∉ φ.rest x a := fun h => by
        rcases φ.line_inter_rest hx ha hxa ⟨hp, h⟩ with h | h
        · exact hpx h
        · exact hpa h
      obtain ⟨δ, hδ, hδr⟩ := Metric.isOpen_iff.mp (φ.isClosed_rest x a).isOpen_compl _ hprest
      refine mem_interior.mpr ⟨ball p δ, fun q hq => ?_, isOpen_ball, mem_ball_self hδ⟩
      have hUeq := φ.U_eq_rest hx ha hxa
      by_cases hqU : q ∈ φ.U
      · rw [hUeq] at hqU
        rcases hqU with h | h
        · exact absurd h (hδr hq)
        · exact hlineA a haK h
      · obtain ⟨hf, hqf⟩ := φ.mem_faces_of_notMem hqU
        set f := connectedComponentIn (univ \ φ.U) q
        have hfo := φ.isOpen_of_mem_faces hf
        -- the ball meets the frontier of the face `f`
        obtain ⟨p', hp'B, hp'c, hp'f⟩ : ∃ p' ∈ ball p δ, p' ∈ closure f ∧ p' ∉ f := by
          by_contra hno
          push Not at hno
          have hsub := isPreconnected_ball.subset_left_of_subset_union hfo.1
            isClosed_closure.isOpen_compl (disjoint_compl_right_iff_subset.mpr subset_closure)
            (fun z hz => by
              by_cases h : z ∈ closure f
              · exact Or.inl (hno z hz h)
              · exact Or.inr h) ⟨q, hq, hqf⟩
          exact hfo.2.2 (hsub (mem_ball_self hδ)) hpU
        have hp'U : p' ∈ φ.U := by
          by_contra hp'U
          obtain ⟨hf', hp'f'⟩ := φ.mem_faces_of_notMem hp'U
          obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hp'c _ (φ.isOpen_of_mem_faces hf').1 hp'f'
          exact hp'f (φ.eq_of_mem_faces hf' hf hz1 hz2 ▸ hp'f')
        rw [hUeq] at hp'U
        rcases hp'U with h | hp'L
        · exact absurd h (hδr hp'B)
        · have h1 : p' ≠ φ.pt x := fun h => hδr hp'B (h ▸ Or.inl ⟨x, hx, rfl⟩)
          have h2 : p' ≠ φ.pt a := fun h => hδr hp'B (h ▸ Or.inl ⟨a, ha, rfl⟩)
          obtain ⟨z, hz, hxz, haz, hfz⟩ := hφ.face_at_inner_edge hC hR hx ha hxa (hKC a haK) hf
            hp'L h1 h2 hp'c
          have hzK : z ∈ K := hKcl a haK z hz hxz haz
          simp only [hA, mem_iUnion]
          exact ⟨a, haK, z, hzK, haz, subset_closure (hfz ▸ hqf)⟩
    · obtain ⟨hf, hpf⟩ := φ.mem_faces_of_notMem hpU
      set f := connectedComponentIn (univ \ φ.U) p
      have hfo := φ.isOpen_of_mem_faces hf
      have hpA' := hpA
      simp only [hA, mem_iUnion] at hpA'
      obtain ⟨a, ha, b, hb, hab, hpc⟩ := hpA'
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hpc _ hfo.1 hpf
      have hfe := φ.eq_of_mem_faces hf (hφ.inner_mem_faces (htri a ha b hb hab)).1 hz1 hz2
      refine mem_interior.mpr ⟨f, fun q hq => ?_, hfo.1, hpf⟩
      simp only [hA, mem_iUnion]
      exact ⟨a, ha, b, hb, hab, subset_closure (hfe ▸ hq)⟩
  -- a small circle around `x`
  set r := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrε : r < ε := by linarith
  have hS : IsConnected (sphere (φ.pt x) r) :=
    isConnected_sphere (by rw [Complex.rank_real_complex]; norm_num) _ hr0.le
  have hSB : ∀ q ∈ sphere (φ.pt x) r, q ∈ ball (φ.pt x) ε ∧ q ≠ φ.pt x := fun q hq => by
    rw [mem_sphere] at hq
    refine ⟨by rw [mem_ball, hq]; exact hrε, fun h => ?_⟩
    rw [h, dist_self] at hq
    exact hr0.ne hq
  -- the line of every edge at `x` meets the circle
  have hmeet : ∀ a, a ∈ R → G.Adj x a → ∃ q ∈ φ.line x a, q ∈ sphere (φ.pt x) r := by
    intro a ha hxa
    obtain ⟨γ, h0, h1⟩ := φ.isLine x hx a ha hxa
    have hcont : Continuous fun t => dist (γ t : ℂ) (φ.pt x) :=
      (continuous_subtype_val.comp γ.continuous).dist continuous_const
    have hfar : ε ≤ dist (φ.pt a) (φ.pt x) := by
      by_contra hlt
      push Not at hlt
      exact hεZ (mem_ball.mpr hlt) (hptZ a ha hxa.ne.symm)
    obtain ⟨t, ht⟩ := intermediate_value_univ 0 1 hcont
      (show r ∈ Icc _ _ by
        simp only [h0, h1, dist_self]
        exact ⟨hr0.le, by linarith⟩)
    exact ⟨γ t, (γ t).2, mem_sphere.mpr ht⟩
  obtain ⟨a₀, ha₀⟩ := hKne
  obtain ⟨q₀, hq₀L, hq₀S⟩ := hmeet a₀ (hKN a₀ ha₀).1 (hKN a₀ ha₀).2
  have hSA : sphere (φ.pt x) r ⊆ interior A := by
    refine hS.isPreconnected.subset_left_of_subset_union isOpen_interior hAc.isOpen_compl
      (disjoint_compl_right_iff_subset.mpr interior_subset) (fun q hq => ?_) ⟨q₀, hq₀S, ?_⟩
    · by_cases h : q ∈ A
      · exact Or.inl (hint q h (hSB q hq).1 (hSB q hq).2)
      · exact Or.inr h
    · exact hint q₀ (hlineA a₀ ha₀ hq₀L) (hSB q₀ hq₀S).1 (hSB q₀ hq₀S).2
  obtain ⟨q, hqL, hqS⟩ := hmeet w hw hxw
  exact hwK (hstar q (interior_subset (hSA hqS)) (hSB q hqS).1 (hSB q hqS).2 w hw hxw hqL)

end PlaneEmbedding

end GraphMinor.HP25
