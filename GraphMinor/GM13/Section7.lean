module

public import GraphMinor.GM13.Section7a
public import GraphMinor.GM13.Section8
public import GraphMinor.GM07.Section11
public import GraphMinor.Surface.ArcTools

/-!
# Graph Minors XIII, Section 7: the distance in a drawn wall, and tools for stars

This file has the basic facts on the plane distance `planeWallDist` of
Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*, J. Combin. Theory
Ser. B **63** (1995), 65–110, page 89:

- `planeWallDist_self`, `DrawnWall.dist_self`: the distance from a point to itself is zero;
- `planeWallDist_comm`, `DrawnWall.dist_comm`: the distance is symmetric;
- `planeWallDist_triangle`, `DrawnWall.dist_triangle`: the triangle inequality for a drawing
  that meets every arc in finitely many points;
- `distGeSub_planeWallDist_of_diff_ncard_le`: deleting a few points changes the distance a little.

It also has three small tools for stars over a wall, used in (7.5) and (7.6):
`exists_substar_avoiding_vertex` (delete the one ray through a given vertex),
`at_most_one_leaf_close`, and the monotonicity lemmas `IsLMStarOver.mono_m` and
`IsExternalLMStarOver.mono_m`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function
open Graph SimpleGraph
open GraphMinor
open GraphMinor.Surface
open GraphMinor.GM07
open GraphMinor.GM09
open GraphMinor.GM16

universe u v

variable {α : Type u} {β : Type v}

/-! ## Distance function of a drawn wall in the plane -/

/-- The plane distance from any point `s` to itself is `0`. -/
@[simp]
theorem planeWallDist_self (U : Set EuclideanPlane) (s : EuclideanPlane) :
    planeWallDist U s s = 0 := by
  simp [planeWallDist]

/-- Symmetry of `planeWallDist`: `d(s, t) = d(t, s)` because every line from `s` to `t`
is also a line from `t` to `s` by `Surface.IsLineWithEnds.symm`. -/
theorem planeWallDist_comm (U : Set EuclideanPlane) (s t : EuclideanPlane) :
    planeWallDist U s t = planeWallDist U t s := by
  by_cases hst : s = t
  · subst hst
    rfl
  · have hts : t ≠ s := Ne.symm hst
    simp only [planeWallDist, hst, hts, ↓reduceIte]
    congr 1
    ext k
    constructor
    · rintro ⟨L, hL, hfin, hcard⟩
      exact ⟨L, hL.symm, hfin, hcard⟩
    · rintro ⟨L, hL, hfin, hcard⟩
      exact ⟨L, hL.symm, hfin, hcard⟩

/-- Reflexivity of vertex distance in a drawn wall: `W.dist u u = 0`. -/
@[simp]
theorem DrawnWall.dist_self (W : DrawnWall α β) (u : α) :
    W.dist u u = 0 := by
  simp [DrawnWall.dist, DrawnWall.planeDist]

/-- Symmetry of vertex distance in a drawn wall: `W.dist u v = W.dist v u`. -/
theorem DrawnWall.dist_comm (W : DrawnWall α β) (u v : α) :
    W.dist u v = W.dist v u :=
  planeWallDist_comm W.drawingU (W.vertexPoint u) (W.vertexPoint v)

/-- A drawn wall `W` is *thinly drawn* in the plane if between any two distinct points `s ≠ t`
of the plane there exists a line `L` with ends `s, t` meeting `W.drawingU` in finitely many
points. Every finite wall drawn in the plane as in Fig. 1 has this property. -/
def IsThinPlaneDrawing (U : Set EuclideanPlane) : Prop :=
  ∀ s t : EuclideanPlane, s ≠ t →
    ∃ L : Set EuclideanPlane, Surface.IsLineWithEnds L s t ∧ (L ∩ U).Finite

/-- When `U` is thinly drawn, for any `s ≠ t` there is a line `L` with ends `s, t` and
`(L ∩ U).Finite` achieving `(L ∩ U).ncard = planeWallDist U s t`. -/
theorem exists_line_ncard_eq_planeWallDist {U : Set EuclideanPlane}
    (hthin : IsThinPlaneDrawing U) {s t : EuclideanPlane} (hst : s ≠ t) :
    ∃ L : Set EuclideanPlane, Surface.IsLineWithEnds L s t ∧
      (L ∩ U).Finite ∧ (L ∩ U).ncard = planeWallDist U s t := by
  obtain ⟨L₀, hL₀, hfin₀⟩ := hthin s t hst
  let S : Set ℕ :=
    {k : ℕ | ∃ L : Set EuclideanPlane,
      Surface.IsLineWithEnds L s t ∧ (L ∩ U).Finite ∧ (L ∩ U).ncard = k}
  have hne : S.Nonempty := ⟨(L₀ ∩ U).ncard, L₀, hL₀, hfin₀, rfl⟩
  have hmem : sInf S ∈ S := Nat.sInf_mem hne
  simpa [planeWallDist, hst, S] using hmem

/-- Any line `L` with ends `s ≠ t` and `(L ∩ U).Finite` has
`planeWallDist U s t ≤ (L ∩ U).ncard`. -/
theorem planeWallDist_le_ncard {U : Set EuclideanPlane} {s t : EuclideanPlane}
    (hst : s ≠ t) {L : Set EuclideanPlane}
    (hL : Surface.IsLineWithEnds L s t) (hfin : (L ∩ U).Finite) :
    planeWallDist U s t ≤ (L ∩ U).ncard := by
  simp only [planeWallDist, hst, ↓reduceIte]
  exact Nat.sInf_le ⟨L, hL, hfin, rfl⟩

/-- Triangle inequality for `planeWallDist` on any thinly drawn set `U`:
for all `s, x, t` in the plane,
`planeWallDist U s t ≤ planeWallDist U s x + planeWallDist U x t`. -/
theorem planeWallDist_triangle {U : Set EuclideanPlane} (hthin : IsThinPlaneDrawing U)
    (s x t : EuclideanPlane) :
    planeWallDist U s t ≤ planeWallDist U s x + planeWallDist U x t := by
  by_cases hst : s = t
  · subst hst
    simp
  · by_cases hsx : s = x
    · subst hsx
      simp
    · by_cases hxt : x = t
      · subst hxt
        simp
      · obtain ⟨L₁, hL₁, hfin₁, hcard₁⟩ := exists_line_ncard_eq_planeWallDist hthin hsx
        obtain ⟨L₂, hL₂, hfin₂, hcard₂⟩ := exists_line_ncard_eq_planeWallDist hthin hxt
        have hs_L₁ : s ∈ L₁ := by
          rcases hL₁ with ⟨f, rfl, _⟩
          exact (f 0).2
        have hx_L₁ : x ∈ L₁ := by
          rcases hL₁ with ⟨f, _, rfl⟩
          exact (f 1).2
        have hx_L₂ : x ∈ L₂ := by
          rcases hL₂ with ⟨f, rfl, _⟩
          exact (f 0).2
        have ht_L₂ : t ∈ L₂ := by
          rcases hL₂ with ⟨f, _, rfl⟩
          exact (f 1).2
        have hj₁ : JoinedIn (L₁ ∪ L₂) s x :=
          (joinedIn_iff_eq_or_exists_isLineWithEnds (Z := L₁ ∪ L₂)
            (mem_union_left L₂ hs_L₁) (mem_union_left L₂ hx_L₁)).mpr
            (Or.inr ⟨L₁, subset_union_left, hL₁⟩)
        have hj₂ : JoinedIn (L₁ ∪ L₂) x t :=
          (joinedIn_iff_eq_or_exists_isLineWithEnds (Z := L₁ ∪ L₂)
            (mem_union_right L₁ hx_L₂) (mem_union_right L₁ ht_L₂)).mpr
            (Or.inr ⟨L₂, subset_union_right, hL₂⟩)
        have hj : JoinedIn (L₁ ∪ L₂) s t := hj₁.trans hj₂
        obtain ⟨L, hLsub, hL⟩ :=
          ((joinedIn_iff_eq_or_exists_isLineWithEnds (Z := L₁ ∪ L₂)
            (mem_union_left L₂ hs_L₁) (mem_union_right L₁ ht_L₂)).mp hj).resolve_left hst
        have hsubU : L ∩ U ⊆ (L₁ ∩ U) ∪ (L₂ ∩ U) := by
          intro z ⟨hzL, hzU⟩
          rcases hLsub hzL with hz₁ | hz₂
          · exact Or.inl ⟨hz₁, hzU⟩
          · exact Or.inr ⟨hz₂, hzU⟩
        have hfin : (L ∩ U).Finite := (hfin₁.union hfin₂).subset hsubU
        have hle₁ : planeWallDist U s t ≤ (L ∩ U).ncard :=
          planeWallDist_le_ncard hst hL hfin
        have hle₂ : (L ∩ U).ncard ≤ ((L₁ ∩ U) ∪ (L₂ ∩ U)).ncard :=
          ncard_le_ncard hsubU (hfin₁.union hfin₂)
        have hle₃ : ((L₁ ∩ U) ∪ (L₂ ∩ U)).ncard ≤ (L₁ ∩ U).ncard + (L₂ ∩ U).ncard :=
          ncard_union_le (L₁ ∩ U) (L₂ ∩ U)
        omega

/-- Triangle inequality for vertex distance in a thinly drawn wall `W`. -/
theorem DrawnWall.dist_triangle {W : DrawnWall α β} (hthin : IsThinPlaneDrawing W.drawingU)
    (u x w : α) :
    W.dist u w ≤ W.dist u x + W.dist x w :=
  planeWallDist_triangle hthin (W.vertexPoint u) (W.vertexPoint x) (W.vertexPoint w)

/-- If `U' ⊆ U` and `U` is thinly drawn, then `U'` is thinly drawn and
`planeWallDist U' s t ≤ planeWallDist U s t`. -/
theorem IsThinPlaneDrawing.mono {U U' : Set EuclideanPlane}
    (hthin : IsThinPlaneDrawing U) (hsub : U' ⊆ U) :
    IsThinPlaneDrawing U' := by
  intro s t hst
  obtain ⟨L, hL, hfin⟩ := hthin s t hst
  exact ⟨L, hL, hfin.subset (inter_subset_inter_right L hsub)⟩

/-- If `(U \ U')` has at most `k` points on some optimal line for `U'`, then
`DistGeSub (planeWallDist U') (planeWallDist U) k`. -/
theorem distGeSub_planeWallDist_of_diff_ncard_le {U U' : Set EuclideanPlane} {k : ℕ}
    (hthin' : IsThinPlaneDrawing U')
    (hcut : ∀ s t : EuclideanPlane, s ≠ t →
      ∃ L : Set EuclideanPlane, Surface.IsLineWithEnds L s t ∧
        (L ∩ U').Finite ∧ (L ∩ U').ncard = planeWallDist U' s t ∧
        (L ∩ (U \ U')).Finite ∧ (L ∩ (U \ U')).ncard ≤ k) :
    DistGeSub (planeWallDist U') (planeWallDist U) k := by
  intro s t
  by_cases hst : s = t
  · subst hst
    simp
  · obtain ⟨L, hL, hfin', hcard', hfindiff, hcarddiff⟩ := hcut s t hst
    have hsub : L ∩ U ⊆ (L ∩ U') ∪ (L ∩ (U \ U')) := by
      intro z ⟨hzL, hzU⟩
      by_cases hzU' : z ∈ U'
      · exact Or.inl ⟨hzL, hzU'⟩
      · exact Or.inr ⟨hzL, hzU, hzU'⟩
    have hfinU : (L ∩ U).Finite := (hfin'.union hfindiff).subset hsub
    have hle₁ : planeWallDist U s t ≤ (L ∩ U).ncard :=
      planeWallDist_le_ncard hst hL hfinU
    have hle₂ : (L ∩ U).ncard ≤ ((L ∩ U') ∪ (L ∩ (U \ U'))).ncard :=
      ncard_le_ncard hsub (hfin'.union hfindiff)
    have hle₃ : ((L ∩ U') ∪ (L ∩ (U \ U'))).ncard ≤ (L ∩ U').ncard + (L ∩ (U \ U')).ncard :=
      ncard_union_le (L ∩ U') (L ∩ (U \ U'))
    have _ := hthin'
    omega

/-! ## Tools for (7.3)–(7.7) -/

/-- Corollary of `(7.3)` with `r = 0`: the punctured wall `H'` does not contain `v` in `V(H'.graph)`,
because `H.dist v v = 0 ≤ 0`. -/
theorem puncture_not_mem_vertexSet {H H' : DrawnWall α β} {v : α}
    (hfar : ∀ u ∈ V(H'.graph), 0 < H.dist u v) :
    v ∉ V(H'.graph) := by
  intro hv
  have hlt := hfar v hv
  rw [DrawnWall.dist_self] at hlt
  exact Nat.lt_irrefl 0 hlt

/-- If `S` is an external `(l + 1, m)`-star over `H` in `G` with center `v` (where `l ≥ 3`), and
`w ≠ v` is any vertex, then because the `l + 1` rays of `S` share only `v`, at most one ray of `S`
contains `w`; deleting that ray yields an external `(l, m)`-star `S' ≤ S` over `H` in `G` with
center `v` and `w ∉ V(S')`. -/
theorem exists_substar_avoiding_vertex {G : Graph α β} {H : DrawnWall α β}
    {l m : ℕ} {S : Graph α β} {v : α} (hl : 3 ≤ l)
    (hstar : IsExternalLMStarOver G H (l + 1) m S v)
    {w : α} (hwv : w ≠ v) :
    ∃ S' : Graph α β, S' ≤ S ∧ w ∉ V(S') ∧ IsExternalLMStarOver G H l m S' v := by
  classical
  rcases hstar with ⟨⟨_, hHG, hvG, P, u, hS_eq, hP_props, hP_disj, hu_dist⟩, hv_not_H⟩
  have hP_le : ∀ A ∈ Set.range P, A ≤ G := by
    rintro A ⟨i, rfl⟩
    exact (hP_props i).1.1
  -- Check whether `w` belongs to `V(P i₀)` for some `i₀ : Fin (l + 1)`
  by_cases hw : ∃ i₀ : Fin (l + 1), w ∈ V(P i₀)
  · rcases hw with ⟨i₀, hwi₀⟩
    let emb : Fin l ↪ Fin (l + 1) := i₀.succAboveEmb
    let P' : Fin l → Graph α β := fun i => P (emb i)
    let u' : Fin l → α := fun i => u (emb i)
    let S' : Graph α β := subgraphSUnion G (Set.range P')
    have hP'_sub : Set.range P' ⊆ Set.range P := by
      rintro A ⟨i, rfl⟩
      exact ⟨emb i, rfl⟩
    have hS'_le_S : S' ≤ S := by
      rw [hS_eq]
      refine (Compatible.of_le_le (subgraphSUnion_le (fun A hA => hP_le A (hP'_sub hA)))
        (subgraphSUnion_le hP_le)).le_iff.mpr ⟨?_, ?_⟩
      · rw [vertexSet_subgraphSUnion, vertexSet_subgraphSUnion]
        intro x hx
        rcases mem_iUnion₂.mp hx with ⟨A, hA, hxA⟩
        exact mem_iUnion₂.mpr ⟨A, hP'_sub hA, hxA⟩
      · rw [edgeSet_subgraphSUnion (fun A hA => hP_le A (hP'_sub hA)),
            edgeSet_subgraphSUnion hP_le]
        intro e he
        rcases mem_iUnion₂.mp he with ⟨A, hA, heA⟩
        exact mem_iUnion₂.mpr ⟨A, hP'_sub hA, heA⟩
    have hw_not_S' : w ∉ V(S') := by
      intro hwS'
      rw [vertexSet_subgraphSUnion] at hwS'
      rcases mem_iUnion₂.mp hwS' with ⟨A, ⟨i, rfl⟩, hwi⟩
      have hne : emb i ≠ i₀ := Fin.succAbove_ne i₀ i
      have hinter := hP_disj (emb i) i₀ hne
      have hw_inter : w ∈ V(P (emb i)) ∩ V(P i₀) := ⟨hwi, hwi₀⟩
      rw [hinter, mem_singleton_iff] at hw_inter
      exact hwv hw_inter
    refine ⟨S', hS'_le_S, hw_not_S', ⟨⟨hl, hHG, hvG, P', u', rfl, ?_, ?_, ?_⟩, hv_not_H⟩⟩
    · intro i
      exact hP_props (emb i)
    · intro i j hij
      exact hP_disj (emb i) (emb j) (emb.injective.ne hij)
    · intro i j hij
      exact hu_dist (emb i) (emb j) (emb.injective.ne hij)
  · push Not at hw
    let emb : Fin l ↪ Fin (l + 1) := Fin.castSuccEmb
    let P' : Fin l → Graph α β := fun i => P (emb i)
    let u' : Fin l → α := fun i => u (emb i)
    let S' : Graph α β := subgraphSUnion G (Set.range P')
    have hP'_sub : Set.range P' ⊆ Set.range P := by
      rintro A ⟨i, rfl⟩
      exact ⟨emb i, rfl⟩
    have hS'_le_S : S' ≤ S := by
      rw [hS_eq]
      refine (Compatible.of_le_le (subgraphSUnion_le (fun A hA => hP_le A (hP'_sub hA)))
        (subgraphSUnion_le hP_le)).le_iff.mpr ⟨?_, ?_⟩
      · rw [vertexSet_subgraphSUnion, vertexSet_subgraphSUnion]
        intro x hx
        rcases mem_iUnion₂.mp hx with ⟨A, hA, hxA⟩
        exact mem_iUnion₂.mpr ⟨A, hP'_sub hA, hxA⟩
      · rw [edgeSet_subgraphSUnion (fun A hA => hP_le A (hP'_sub hA)),
            edgeSet_subgraphSUnion hP_le]
        intro e he
        rcases mem_iUnion₂.mp he with ⟨A, hA, heA⟩
        exact mem_iUnion₂.mpr ⟨A, hP'_sub hA, heA⟩
    have hw_not_S' : w ∉ V(S') := by
      intro hwS'
      rw [vertexSet_subgraphSUnion] at hwS'
      rcases mem_iUnion₂.mp hwS' with ⟨A, ⟨i, rfl⟩, hwi⟩
      exact hw (emb i) hwi
    refine ⟨S', hS'_le_S, hw_not_S', ⟨⟨hl, hHG, hvG, P', u', rfl, ?_, ?_, ?_⟩, hv_not_H⟩⟩
    · intro i
      exact hP_props (emb i)
    · intro i j hij
      exact hP_disj (emb i) (emb j) (emb.injective.ne hij)
    · intro i j hij
      exact hu_dist (emb i) (emb j) (emb.injective.ne hij)

/-- Arithmetic helper for the proof of `(7.5)` (page 91):
for `k ≥ 1`, `2 * k^2 - k + 3 - (k - 1) * (2 * k - 1) ≥ 2 * k`. -/
theorem star_ray_count_ineq (k : ℕ) (hk : 1 ≤ k) :
    2 * k ≤ (2 * k ^ 2 - k + 3) - (k - 1) * (2 * k - 1) := by
  have h1 : k ≤ 2 * k ^ 2 := by nlinarith
  have h2 : 1 ≤ 2 * k := by omega
  refine Nat.le_sub_of_add_le ?_
  zify [hk, h1, h2]
  nlinarith

/-- Triangle inequality uniqueness step in the proof of `(7.5)` (page 92):
"Now for any $x \in \{s_1, t_1, \dots, s_{k - 1}, t_{k - 1}\}$, $d(u_i, x) < \frac{1}{2}m$ for at
most one value of $i$ ($1 \le i \le l$), since $d(u_i, u_{i'}) \ge m$ for $i \ne i'$." -/
theorem at_most_one_leaf_close {H : DrawnWall α β} (hthin : IsThinPlaneDrawing H.drawingU)
    {l r : ℕ} {u : Fin l → α}
    (hu_dist : ∀ i j : Fin l, i ≠ j → 2 * r ≤ H.dist (u i) (u j))
    (x : α) {i i' : Fin l}
    (hi : H.dist (u i) x < r) (hi' : H.dist (u i') x < r) :
    i = i' := by
  by_contra hne
  have hfar : 2 * r ≤ H.dist (u i) (u i') := hu_dist i i' hne
  have htri : H.dist (u i) (u i') ≤ H.dist (u i) x + H.dist x (u i') :=
    H.dist_triangle hthin (u i) x (u i')
  rw [H.dist_comm x (u i')] at htri
  omega

/-- Monotonicity of `IsLMStarOver` in the distance parameter: if `m₁ ≤ m₂`, every `(l, m₂)`-star
over `H` in `G` is also an `(l, m₁)`-star over `H` in `G`. -/
theorem IsLMStarOver.mono_m {G : Graph α β} {H : DrawnWall α β}
    {l m₁ m₂ : ℕ} {S : Graph α β} {v : α}
    (hm : m₁ ≤ m₂) (hstar : IsLMStarOver G H l m₂ S v) :
    IsLMStarOver G H l m₁ S v := by
  rcases hstar with ⟨hl, hHG, hvG, P, u, hS, hP, hdisj, hdist⟩
  refine ⟨hl, hHG, hvG, P, u, hS, hP, hdisj, ?_⟩
  intro i j hij
  exact le_trans hm (hdist i j hij)

/-- Monotonicity of `IsExternalLMStarOver` in the distance parameter `m`. -/
theorem IsExternalLMStarOver.mono_m {G : Graph α β} {H : DrawnWall α β}
    {l m₁ m₂ : ℕ} {S : Graph α β} {v : α}
    (hm : m₁ ≤ m₂) (hstar : IsExternalLMStarOver G H l m₂ S v) :
    IsExternalLMStarOver G H l m₁ S v :=
  ⟨hstar.1.mono_m hm, hstar.2⟩

end GraphMinor.GM13
