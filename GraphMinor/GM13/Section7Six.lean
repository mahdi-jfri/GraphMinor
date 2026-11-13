module

public import GraphMinor.GM13.Section7SixPaths
public import GraphMinor.GM13.Section7FourProof
public import GraphMinor.GM13.Parallel
import GraphMinor.GM09.Basic

/-!
# Graph Minors XIII, (7.6) and (7.7)

(7.6) moves stars over a wall `H` to external stars over a smaller wall `H' ≤ H`, by applying
(7.3) with `r = 0` once for each centre. We follow the paper's proof, with two changes.

* We prove the paper's claim (1) once, for the last wall `H_k`, instead of once per step: the
  paths `Q_j` go from `u_j` straight to `H_k`. All centres are out of `H_k`, so each new leg ends
  at a vertex other than its centre. Once per step, a later centre may lie on the next wall and be
  the end of `Q_j`, and then `P_j ∪ Q_j` is not a leg (see the correction to the proof of (7.6)
  in `corrections/GM13.md`).
* The paper's claim (1) assumes that the centre `v` is not on the paths `Q_j`. It may be on one
  of them when `v ∈ V(H)`; then the new leg is the part of that `Q_j` from `v`
  (`exists_new_leg`).

We also check two steps the paper leaves out: the new ends are at distance at least that of the
old ends (`planeWallDist_le_of_paths`), and the height is large enough for `k` steps, because two
vertices of a wall of height `h` are at distance at most `2h + 2`.

The wall `H'` has "the drawing of $H'$ obtained from the given drawing of $H$" (page 90):
`DrawnWall.induced`.

(7.7) follows from (7.6) and (7.5). To apply (7.5) to `H'`, we draw `H'` as in Fig. 1. This does
not change the distances between its vertices, since both drawings are drawings on cells
(`DrawnOnCells.planeWallDist_eq`).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM09

universe u v

variable {α : Type u} {β : Type v}

/-! ## The drawn wall `H'` with the drawing it gets from `H` -/

/-- A wall `W' ≤ H` with the drawing obtained from the given drawing of `H` (Graph Minors XIII,
Section 7, page 90: "using the drawing of $H'$ obtained from the given drawing of $H$"): its point
set is the image under `φ` of the points of its vertices and edges in `Γ`, and its vertices keep
their points. Here `φ` and `Γ` show that `H` is drawn as in Fig. 1. -/
noncomputable def DrawnWall.induced (H : DrawnWall α β) (φ : EuclideanPlane ≃ₜ EuclideanPlane)
    (Γ : GraphDrawing H.graph EuclideanPlane)
    (hP : ∀ (u : α) (hu : u ∈ V(H.graph)), H.vertexPoint u = φ (Γ.iso.vertexEquiv ⟨u, hu⟩).1)
    (W' : Wall α β) (hle : W'.graph ≤ H.graph) : DrawnWall α β :=
  { W' with
    drawingU := φ '' indU Γ W'
    vertexPoint := H.vertexPoint
    vertexPoint_mem := fun u hu => by
      rw [hP u (hle.vertexSet_mono hu), ← ptV_of_mem Γ (hle.vertexSet_mono hu)]
      exact ⟨ptV Γ u, Or.inl ⟨u, hu, rfl⟩, rfl⟩
    vertexPoint_injOn := H.vertexPoint_injOn.mono hle.vertexSet_mono }

section Induced

variable (H : DrawnWall α β) {φ : EuclideanPlane ≃ₜ EuclideanPlane}
  {Γ : GraphDrawing H.graph EuclideanPlane}
  (hP : ∀ (u : α) (hu : u ∈ V(H.graph)), H.vertexPoint u = φ (Γ.iso.vertexEquiv ⟨u, hu⟩).1)
  {W' : Wall α β} (hle : W'.graph ≤ H.graph)
include hP

theorem DrawnWall.vertexPoint_eq {u : α} (hu : u ∈ V(H.graph)) :
    H.vertexPoint u = φ (ptV Γ u) := by
  rw [hP u hu, ptV_of_mem Γ hu]

/-- The distance of two vertices of `H` in the drawing of `W'` obtained from `H`. -/
theorem DrawnWall.induced_dist {x y : α} (hx : x ∈ V(H.graph)) (hy : y ∈ V(H.graph)) :
    (H.induced φ Γ hP W' hle).dist x y = planeWallDist (indU Γ W') (ptV Γ x) (ptV Γ y) := by
  change planeWallDist (φ '' indU Γ W') (H.vertexPoint x) (H.vertexPoint y) = _
  rw [H.vertexPoint_eq hP hx, H.vertexPoint_eq hP hy, planeWallDist_image_homeomorph]

/-- The distance of two vertices of `H` drawn as in Fig. 1. -/
theorem DrawnWall.dist_eq_fig1 (hΓ : IsFigure1CoordDrawing H.toWall Γ)
    (hU : H.drawingU = φ '' Γ.drawing.U) {x y : α} (hx : x ∈ V(H.graph))
    (hy : y ∈ V(H.graph)) :
    H.dist x y = planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells H.height))
      (ptV Γ x) (ptV Γ y) := by
  rw [DrawnWall.dist, DrawnWall.planeDist, H.vertexPoint_eq hP hx, H.vertexPoint_eq hP hy, hU,
    planeWallDist_image_homeomorph, hΓ.drawing_U_eq, fig1WallSet_eq_cellSet]

end Induced

/-! ## The new legs -/

/-- A path of a subgraph `Q` whose only vertex in a wall `W'` is its end `b` has no edge in `W'`:
the two distinct ends of such an edge would both be `b`. -/
theorem not_mem_edgeSet_of_path {G Q : Graph α β} {a b : α} (hQ : IsGraphPathWithEnds G Q a b)
    {W' : Wall α β} (hW' : W'.graph ≤ G) (hX : V(Q) ∩ V(W'.graph) ⊆ {b}) {f : β}
    (hf : f ∈ E(Q)) : f ∉ E(W'.graph) := by
  intro hg
  obtain ⟨x, y, hlP⟩ := exists_isLink_of_mem_edgeSet hf
  obtain ⟨x', y', hlW⟩ := exists_isLink_of_mem_edgeSet hg
  have hxy := hQ.ne_of_isLink hlP
  have hG := hQ.le.isLink_mono hlP
  have hG' := hW'.isLink_mono hlW
  have h1 : x = b := by
    rcases G.eq_or_eq_of_isLink_of_isLink hG hG' with e | e
    · exact hX ⟨hlP.left_mem, e ▸ hlW.left_mem⟩
    · exact hX ⟨hlP.left_mem, e ▸ hlW.right_mem⟩
  have h2 : y = b := by
    rcases G.eq_or_eq_of_isLink_of_isLink hG.symm hG' with e | e
    · exact hX ⟨hlP.right_mem, e ▸ hlW.left_mem⟩
    · exact hX ⟨hlP.right_mem, e ▸ hlW.right_mem⟩
  exact hxy (h1.trans h2.symm)

/-- **The new leg** (proof of (7.6), claim (1)). Let `P` be a leg from the centre `c` to `u`, with
no vertex in the wall `H` other than `c` and `u`, and let `Q` be a path of `H` from `u` to `w`. If
`c` is not on `Q`, then `P ∪ Q` is a path from `c` to `w`. If `c` is on `Q`, the part of `Q` from
`c` to `w` is such a path. Either way the new leg uses only vertices and edges of `P` and `Q`. -/
theorem exists_new_leg {G : Graph α β} {H : Graph α β} (hHG : H ≤ G) {P Q : Graph α β}
    {c x w : α} (hP : IsGraphPathWithEnds G P c x) (hPH : V(P) ∩ V(H) ⊆ {c, x})
    (hQ : IsGraphPathWithEnds H Q x w) :
    ∃ R : Graph α β, IsGraphPathWithEnds G R c w ∧ V(R) ⊆ V(P) ∪ V(Q) ∧
      E(R) ⊆ E(P) ∪ E(Q) := by
  by_cases hc : c ∈ V(Q)
  · obtain ⟨-, Q₂, -, hQ₂Q, -, hQ₂, -⟩ := hQ.exists_split_at hc
    exact ⟨Q₂, hQ₂.mono (hQ.le.trans hHG), fun y hy => Or.inr (hQ₂Q.vertexSet_mono hy),
      fun f hf => Or.inr (hQ₂Q.edgeSet_mono hf)⟩
  · have hV : V(P) ∩ V(Q) = {x} := by
      refine Subset.antisymm ?_ ?_
      · rintro y ⟨hyP, hyQ⟩
        rcases hPH ⟨hyP, hQ.le.vertexSet_mono hyQ⟩ with rfl | rfl
        · exact absurd hyQ hc
        · rfl
      · rintro y rfl
        exact ⟨hP.right_mem, hQ.left_mem⟩
    exact ⟨subgraphUnion G P Q, hP.subgraphUnion (hQ.mono hHG) hV, subset_rfl,
      edgeSet_subgraphUnion_subset G P Q⟩

/-! ## (7.6) -/

/-- **Claim (1) in the proof of (7.6)** (page 92), for the last wall `H_k`: "*If $v \in V(G)$ is
the center of an $(l, m + 4(k - i + 1))$-star over $H_{i - 1}$, then $v$ is
the center of an $(l, m + 4(k - i))$-star over $H_i$, for $1 \le i \le k$.*" We prove it in one
step from `H` to the wall `W'` with
`d' ≥ d - 4k` on the vertices of `H`, for a centre `c` that is not in `W'`; then the star is
external. Each leg `P_j` is extended by a minimal path `Q_j` of `H` from its end `u_j` to `W'`
(`Wall.exists_path_to_subwall`). Since `d'(u_j, u_{j'}) ≥ m ≥ 3`, the paths `Q_j` are disjoint
(`disjoint_of_three_le_planeWallDist`), and their ends are at distance `≥ m`
(`planeWallDist_le_of_paths`). -/
theorem lemma_7_6_claim_1 {G : Graph α β} (H : DrawnWall α β)
    {φ : EuclideanPlane ≃ₜ EuclideanPlane} {Γ : GraphDrawing H.graph EuclideanPlane}
    (hP : ∀ (u : α) (hu : u ∈ V(H.graph)), H.vertexPoint u = φ (Γ.iso.vertexEquiv ⟨u, hu⟩).1)
    (hHG' : H.graph ≤ G) {W' : Wall α β} (hle : W'.graph ≤ H.graph) {C' : CellWall W'.height}
    (hD' : DrawnOnCells Γ W' C') {k l m : ℕ} (hm : 3 ≤ m)
    (hd : ∀ x ∈ V(H.graph), ∀ y ∈ V(H.graph),
      H.dist x y ≤ planeWallDist (indU Γ W') (ptV Γ x) (ptV Γ y) + 4 * k)
    {S : Graph α β} {c : α} (hS : IsLMStarOver G H l (m + 4 * k) S c) (hc : c ∉ V(W'.graph)) :
    ∃ S' : Graph α β, IsExternalLMStarOver G (H.induced φ Γ hP W' hle) l m S' c := by
  obtain ⟨hl3, -, hvG, ⟨P, u, -, hleg, hPP, hfar⟩⟩ := hS
  have huH : ∀ j, u j ∈ V(H.graph) := fun j => (hleg j).2.2.1
  -- `Q_j`: a minimal path of `H` from `u_j` to `H_k`, with ends `u_j, w_j`
  choose w Q hQ hQX using fun j => H.toWall.exists_path_to_subwall W' hle (huH j)
  have hX : ∀ j, V(Q j) ∩ V(W'.graph) ⊆ {w j} := fun j => (hQX j).le
  have hwW : ∀ j, w j ∈ V(W'.graph) := fun j => by
    have : w j ∈ V(Q j) ∩ V(W'.graph) := by rw [hQX j]; rfl
    exact this.2
  -- `d_k(u_j, u_{j'}) ≥ d(u_j, u_{j'}) - 4k ≥ m ≥ 3`
  have hfar' : ∀ i j, i ≠ j → m ≤ planeWallDist (indU Γ W') (ptV Γ (u i)) (ptV Γ (u j)) := by
    intro i j hij
    have := hfar i j hij
    have := hd _ (huH i) _ (huH j)
    omega
  -- so `Q_j` and `Q_{j'}` are vertex-disjoint
  have hdisj : ∀ i j, i ≠ j → Disjoint V(Q i) V(Q j) := fun i j hij =>
    disjoint_of_three_le_planeWallDist (Γ := Γ) (hQ i) (hQ j) hle (hX i) (hX j)
      (by have := hfar' i j hij; omega)
  -- the new legs `P_j ∪ Q_j`
  choose R hR hRV hRE using fun j => exists_new_leg hHG' (hleg j).1 (hleg j).2.2.2.1 (hQ j)
  refine ⟨subgraphSUnion G (range R),
    ⟨hl3, hle.trans hHG', hvG, R, w, rfl, fun j => ⟨hR j, ?_, hwW j, ?_, ?_⟩, ?_, ?_⟩, hc⟩
  · exact fun e => hc (e ▸ hwW j)
  · rintro x ⟨hxR, hxW⟩
    rcases hRV j hxR with hxP | hxQ
    · rcases (hleg j).2.2.2.1 ⟨hxP, hle.vertexSet_mono hxW⟩ with rfl | hxu
      · exact Or.inl rfl
      · rw [mem_singleton_iff.mp hxu] at hxW ⊢
        exact Or.inr (hX j ⟨(hQ j).left_mem, hxW⟩)
    · exact Or.inr (hX j ⟨hxQ, hxW⟩)
  · rw [Set.disjoint_left]
    intro f hfR hfW
    rcases hRE j hfR with hfP | hfQ
    · exact disjoint_left.mp (hleg j).2.2.2.2 hfP (hle.edgeSet_mono hfW)
    · exact not_mem_edgeSet_of_path (hQ j) hle (hX j) hfQ hfW
  · intro i j hij
    have hPQ : ∀ i j, i ≠ j → ∀ x, x ∈ V(P i) → x ∈ V(Q j) → x = c := by
      intro i j hij x hxP hxQ
      rcases (hleg i).2.2.2.1 ⟨hxP, (hQ j).le.vertexSet_mono hxQ⟩ with rfl | hxu
      · rfl
      · rw [mem_singleton_iff.mp hxu] at hxQ
        exact absurd hxQ (disjoint_left.mp (hdisj i j hij) (hQ i).left_mem)
    ext x
    constructor
    · rintro ⟨hxi, hxj⟩
      rcases hRV i hxi with hPi | hQi <;> rcases hRV j hxj with hPj | hQj
      · exact (Set.ext_iff.mp (hPP i j hij) x).mp ⟨hPi, hPj⟩
      · exact hPQ i j hij x hPi hQj
      · exact hPQ j i (Ne.symm hij) x hPj hQi
      · exact absurd hQj (disjoint_left.mp (hdisj i j hij) hQi)
    · rintro rfl
      exact ⟨(hR i).left_mem, (hR j).left_mem⟩
  · intro i j hij
    rw [H.induced_dist hP hle (hle.vertexSet_mono (hwW i)) (hle.vertexSet_mono (hwW j))]
    have h1 := hfar' i j hij
    have h2 := planeWallDist_le_of_paths (hQ i) (hQ j) hle (hwW i) (hwW j) (hX i) (hX j)
      (hdisj i j hij) C'.naming.not_square hD'.indU_eq
    omega

/-- **(7.6) on cells.** The statement of (7.6) for a wall `H` drawn as in Fig. 1 by `φ` and `Γ`,
with the new wall `W'` drawn on the cells of a cell wall `C'`; (7.7) uses this cell wall. -/
theorem theorem_7_6_cells (G : Graph α β) (H : DrawnWall α β)
    {φ : EuclideanPlane ≃ₜ EuclideanPlane} {Γ : GraphDrawing H.graph EuclideanPlane}
    (hΓ : IsFigure1CoordDrawing H.toWall Γ) (hU : H.drawingU = φ '' Γ.drawing.U)
    (hP : ∀ (u : α) (hu : u ∈ V(H.graph)), H.vertexPoint u = φ (Γ.iso.vertexEquiv ⟨u, hu⟩).1)
    (hHG : IsWallIn G H.toWall) {k l m : ℕ} (hm : 3 ≤ m) (S : Fin k → Graph α β)
    (v : Fin k → α) (hS : ∀ a, IsLMStarOver G H l (m + 4 * k) (S a) (v a)) :
    ∃ (W' : Wall α β) (hle : W'.graph ≤ H.graph) (C' : CellWall W'.height),
      DrawnOnCells Γ W' C' ∧ ∃ S' : Fin k → Graph α β,
        ∀ a, IsExternalLMStarOver G (H.induced φ Γ hP W' hle) l m (S' a) (v a) := by
  have hF : H.IsFigure1 := ⟨φ, Γ, hΓ, hU, hP⟩
  have hHG' : H.graph ≤ G := hHG
  -- the height is at least `2k + 2`, since two ends of a star are at distance `≥ 3 + 4k`, and
  -- vertices of a wall of height `h` are at distance `≤ 2h + 2`
  have hh : 2 * k + 2 ≤ H.height := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · have := H.two_le_height
      omega
    · obtain ⟨hl3, -, -, ⟨P, u, -, hleg, -, hfar⟩⟩ := hS ⟨0, hk⟩
      have h01 : (⟨0, by omega⟩ : Fin l) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
      have h1 := hfar _ _ h01
      have h2 := hF.dist_le (hleg ⟨0, by omega⟩).2.2.1 (hleg ⟨1, by omega⟩).2.2.1
      obtain ⟨t, ht⟩ := H.even_height
      omega
  have hh1 : 1 ≤ H.height := by omega
  -- `k` applications of (7.3) with `r = 0`, one for each centre
  obtain ⟨W', C', hle, hD', hL, hdist⟩ :=
    (drawnOnCells_fig1 hΓ hh1 H.even_height).exists_iter (List.ofFn v) (by simpa using hh)
  have hvW : ∀ a, v a ∉ V(W'.graph) := fun a => hL (v a) (List.mem_ofFn.mpr ⟨a, rfl⟩)
  -- `d_k ≥ d - 4k` on the vertices of `H`
  have hd : ∀ x ∈ V(H.graph), ∀ y ∈ V(H.graph),
      H.dist x y ≤ planeWallDist (indU Γ W') (ptV Γ x) (ptV Γ y) + 4 * k := by
    intro x hx y hy
    rw [H.dist_eq_fig1 hP hΓ hU hx hy, hD'.indU_eq]
    have := hdist (ptV Γ x) (ptV Γ y)
    simp only [List.length_ofFn] at this
    exact this
  refine ⟨W', hle, C', hD', ?_⟩
  -- claim (1), for each star
  have key : ∀ a, ∃ S' : Graph α β,
      IsExternalLMStarOver G (H.induced φ Γ hP W' hle) l m S' (v a) := fun a =>
    lemma_7_6_claim_1 H hP hHG' hle hD' hm hd (hS a) (hvW a)
  choose S' hS' using key
  exact ⟨S', hS'⟩

/-- **Graph Minors XIII, (7.6)** (Section 7, page 92): "Let $H$ be a wall in a graph $G$. Suppose
there are $k$ $(l, m + 4k)$-stars in $G$ over $H$ with distinct centers $v_1, \dots, v_k$, where
$m \ge 3$. Then there is a wall $H' \subseteq H$ with $k$ external $(l, m)$-stars over $H'$, with
centers $v_1, \dots, v_k$." The wall `H` is drawn as in Fig. 1, and `H'` has "the drawing of
$H'$ obtained from the given drawing of $H$" (page 90): its point set is the image under `φ` of
the points of its vertices and edges in `Γ`, and its vertices keep their points. -/
theorem theorem_7_6_proof (G : Graph α β) (H : DrawnWall α β) (hF : H.IsFigure1)
    (hHG : IsWallIn G H.toWall) (k l m : ℕ) (hm : 3 ≤ m) (S : Fin k → Graph α β)
    (v : Fin k → α) (hS : ∀ a, IsLMStarOver G H l (m + 4 * k) (S a) (v a))
    (_hv : Injective v) :
    ∃ H' : DrawnWall α β, H'.graph ≤ H.graph ∧ H'.vertexPoint = H.vertexPoint ∧
      (∃ (φ : EuclideanPlane ≃ₜ EuclideanPlane) (Γ : GraphDrawing H.graph EuclideanPlane),
        IsFigure1CoordDrawing H.toWall Γ ∧ H.drawingU = φ '' Γ.drawing.U ∧
        (∀ (u : α) (hu : u ∈ V(H.graph)), H.vertexPoint u = φ (Γ.iso.vertexEquiv ⟨u, hu⟩).1) ∧
        H'.drawingU = φ '' indU Γ H'.toWall) ∧
      ∃ S' : Fin k → Graph α β, ∀ a, IsExternalLMStarOver G H' l m (S' a) (v a) := by
  obtain ⟨φ, Γ, hΓ, hU, hP⟩ := hF
  obtain ⟨W', hle, C', -, S', hS'⟩ := theorem_7_6_cells G H hΓ hU hP hHG hm S v hS
  exact ⟨H.induced φ Γ hP W' hle, hle, rfl, ⟨φ, Γ, hΓ, hU, hP, rfl⟩, S', hS'⟩

/-! ## (7.7) -/

/-- **Graph Minors XIII, (7.7)**, first assertion (Section 7, page 93): "For any $p \ge 2$ there
are integers $l \ge 3$, $m \ge 0$ with the following property. Let $G$ be a graph and let $H$ be
a wall in $G$, so that there are $\binom{p}{2}$ $(l, m)$-stars over $H$, with distinct centers;
then $G$ has a $K_p$-minor." "The first assertion is clear from (7.5) and (7.6)." By (7.6) there
is a wall `H' ≤ H` with external stars. To apply (7.5), we draw `H'` as in Fig. 1 itself; its
distances do not change, since both drawings are drawings on cells
(`DrawnOnCells.planeWallDist_eq`). -/
theorem theorem_7_7_proof : GM13Theorem77Statement.{u, v} := by
  intro p _
  obtain ⟨m₅, h75⟩ := theorem_7_5_proof.{u, v} p
  refine ⟨2 * p.choose 2 ^ 2 - p.choose 2 + 3, max m₅ 3 + 4 * p.choose 2, by omega, ?_⟩
  intro α β G H hF hHG S v hS hv
  obtain ⟨φ, Γ, hΓ, hU, hP⟩ := hF
  obtain ⟨W', hle, C', hD', S', hS'⟩ :=
    theorem_7_6_cells G H hΓ hU hP hHG (le_max_right m₅ 3) S v hS
  -- draw `H'` as in Fig. 1
  obtain ⟨Γ₂, hΓ₂⟩ := W'.exists_isFigure1CoordDrawing
  let D : DrawnWall α β :=
    { W' with
      drawingU := Γ₂.drawing.U
      vertexPoint := ptV Γ₂
      vertexPoint_mem := fun u hu => Γ₂.drawing.V_subset_U (ptV_mem_V Γ₂ hu)
      vertexPoint_injOn := ptV_injOn Γ₂ }
  have hDF : D.IsFigure1 :=
    ⟨Homeomorph.refl _, Γ₂, hΓ₂, by simp [D], fun u hu => ptV_of_mem Γ₂ hu⟩
  have hD₂ := drawnOnCells_fig1 hΓ₂ (by have := W'.two_le_height; omega) W'.even_height
  -- the two drawings of `H'` give the same distances between distinct vertices
  have hdist : ∀ x ∈ V(W'.graph), ∀ y ∈ V(W'.graph), x ≠ y →
      D.dist x y = (H.induced φ Γ hP W' hle).dist x y := by
    intro x hx y hy hxy
    rw [H.induced_dist hP hle (hle.vertexSet_mono hx) (hle.vertexSet_mono hy), hD'.indU_eq]
    change planeWallDist Γ₂.drawing.U (ptV Γ₂ x) (ptV Γ₂ y) = _
    rw [hΓ₂.drawing_U_eq, fig1WallSet_eq_cellSet]
    exact hD₂.planeWallDist_eq hD' le_rfl hle hx hy hxy
  refine h75 G D hDF (hle.trans hHG) S' v (fun a => ?_) hv
  obtain ⟨⟨hl3, hwle, hvG, P, u, hSeq, hleg, hPP, hfar⟩, hvn⟩ := hS' a
  refine ⟨⟨hl3, hwle, hvG, P, u, hSeq, hleg, hPP, fun i j hij => ?_⟩, hvn⟩
  have h1 := hfar i j hij
  have hne : u i ≠ u j := fun e => by
    rw [e, DrawnWall.dist_self] at h1
    omega
  rw [hdist _ (hleg i).2.2.1 _ (hleg j).2.2.1 hne]
  omega

/-- **Graph Minors XIII, (7.4)**, first assertion, in the form `GM13Theorem74Statement` (Section 7,
page 90): "For any $p \ge 2$ there exists $r \ge 0$ such that the following holds. Let $H$ be a
wall in a graph $G$. Let $P_1, \dots, P_{\binom{p}{2}}$ be mutually vertex-disjoint $H$-paths in
$G$, with their $p(p - 1)$ ends mutually at distance $\ge r$. Then $G$ has a minor isomorphic to
$K_p$." This is `theorem_7_4_proof`, which gives one `r` for every `p`. -/
theorem theorem_7_4_statement : GM13Theorem74Statement.{u, v} := by
  intro p _
  obtain ⟨r, hr⟩ := theorem_7_4_proof.{u, v} p
  exact ⟨r, fun G H hH hHG P s t hP hPd hfar hst => hr G H hH hHG P s t hP hPd hfar hst⟩

end GraphMinor.GM13
