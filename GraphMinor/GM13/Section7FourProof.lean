module

public import GraphMinor.GM13.Section7FourWalk
public import GraphMinor.GM13.Section7Five
import GraphMinor.GM07.Bridge
import GraphMinor.GM07.CuffSlide
import GraphMinor.GM07.Section35
import GraphMinor.GM07.Section7
import GraphMinor.GM09.Basic
import GraphMinor.GM09.RuralAdd
import GraphMinor.GM12.Section4Theorem44
import GraphMinor.GM16.Metric
import GraphMinor.GM16.Section3
import GraphMinor.GM16.SphereRespectful

/-!
# Graph Minors XIII, (7.4) and (7.5)

(7.4), page 90: "For any $p \ge 2$ there exists $r \ge 0$ such that the following holds. Let $H$
be a wall in a graph $G$. Let $P_1, \dots, P_{\binom{p}{2}}$ be mutually vertex-disjoint $H$-paths
in $G$, with their $p(p - 1)$ ends mutually at distance $\ge r$. Then $G$ has a minor isomorphic
to $K_p$. ..." The algorithm in the rest of (7.4) is not part of this file.

The paper's proof: "This follows from the main theorem of [16], or more directly from Theorem
(4.4) of [20], taking $\mathcal{T}$ to be the set of all separations $(A, B)$ of $H$ of order
$< r$ such that $A$ contains no horizontal path of $H$, taking $\Sigma$ to be a sphere, and
taking $\Gamma = H$."

The proof here follows that line.
- The wall `H` and the paths lie in a finite subgraph `G₀` of `G` (`exists_finite_le`).
- `H` is drawn in the sphere in the coordinates of Fig. 1
  (`DrawnWall.IsFigure1.exists_fig1Coords`). The tangle of `H` with no row on a small side
  gives a controlling tangle in `G₀` (`Wall.exists_controlled_tangle`). On the sphere it is
  respectful (XVI, `GM16.drawing_tangle_isRespectful_of_isSphere`) and has a metric `d`
  (`GM16.exists_tangleMetric`).
- XII (4.4) (`GM12.theorem_4_4_span`) gives a number `N` for `p`. We take `r = 4N + 5`. If the
  wall has height at least `2N + 2`, ends at distance at least `r` in `H` are at least `N`
  apart in `d` (`wallDist_le_of_tangleMetric_lt`), and XII (4.4) gives the minor. If the wall is
  lower, any two vertices are at distance at most `4N + 4 < r` (`DrawnWall.IsFigure1.dist_le`),
  so there are no paths as in (7.4) once `p ≥ 2`.

(7.5) then follows from the reduction `theorem_7_5_of_theorem_7_4` of `Section7Five.lean`.
-/

public section

namespace GraphMinor.GM13

open Set Function
open Graph
open GraphMinor
open GraphMinor.Surface
open GraphMinor.GM14

universe u v

variable {α : Type u} {β : Type v}

/-! ## Graph facts -/

/-- A model in a subgraph is a model in the graph. -/
theorem HasGraphModel.mono {α' β' : Type*} {L : Graph α' β'} {G₀ G : Graph α β}
    (h : HasGraphModel L G₀) (hle : G₀ ≤ G) : HasGraphModel L G := by
  obtain ⟨vMap, eMap, hm⟩ := h
  refine ⟨vMap, eMap, ⟨fun v hv => (hm.sub_of_mem hv).trans hle, hm.nonempty_of_mem,
    hm.connected_of_mem, hm.disjoint_of_ne, fun e he => hle.edgeSet_mono (hm.edge_mem he), ?_, ?_,
    hm.eMap_injOn⟩⟩
  · intro e u v huv hne
    obtain ⟨x, hx, y, hy, hl⟩ := hm.link_ends_of_ne huv hne
    exact ⟨x, hx, y, hy, hl.mono hle⟩
  · intro e u huu
    obtain ⟨h1, x, hx, y, hy, hl⟩ := hm.loop_ends huu
    exact ⟨h1, x, hx, y, hy, hl.mono hle⟩

/-- `K_p` has a model in any graph with a vertex, when `p ≤ 1`. -/
theorem hasGraphModel_completeGraph_of_le_one {G : Graph α β} {a : α}
    (ha : a ∈ V(G)) {p : ℕ} (hp : p ≤ 1) : HasGraphModel (GM16.completeGraph p) G := by
  have hnoE : ∀ i j : Fin p, i ≠ j → False := fun i j hij => hij (Fin.ext (by omega))
  have hE (e : E(GM16.completeGraph p)) : False := by
    obtain ⟨x, y, hxy, -⟩ := e.property
    exact hnoE x y hxy
  refine ⟨fun _ => Graph.noEdge {a} β, fun e => (hE e).elim, ⟨?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩⟩
  · intro _ _
    exact Graph.noEdge_le_iff.mpr (singleton_subset_iff.mpr ha)
  · intro _ _
    exact ⟨a, rfl⟩
  · intro _ _ x hx y hy
    have hx' : x = a := hx
    have hy' : y = a := hy
    subst hx' hy'
    exact ⟨GraphWalk.nil rfl⟩
  · intro u v _ _ huv
    exact (hnoE u v huv).elim
  · rintro e ⟨x, y, hxy, -⟩
    exact (hnoE x y hxy).elim
  · intro e u v _ huv
    exact (hnoE u v huv).elim
  · intro e u huu
    exact (huu.1 rfl).elim
  · intro e
    exact (hE e).elim

/-- A finite family of finite subgraphs of `G` lies in one finite subgraph of `G`. -/
theorem exists_finite_le {ι : Type*} [Finite ι] {G : Graph α β} (K : ι → Graph α β)
    (hK : ∀ i, K i ≤ G) (hV : ∀ i, V(K i).Finite) (hE : ∀ i, E(K i).Finite) :
    ∃ G₀ : Graph α β, G₀ ≤ G ∧ V(G₀).Finite ∧ E(G₀).Finite ∧ ∀ i, K i ≤ G₀ := by
  let V₀ : Set α := ⋃ i, V(K i)
  let E₀ : Set β := ⋃ i, E(K i)
  have hV₀ : V₀ ⊆ V(G) := iUnion_subset fun i => (hK i).vertexSet_mono
  refine ⟨(G.induce V₀).restrict E₀, (Graph.restrict_le).trans (Graph.induce_le hV₀),
    finite_iUnion hV, (finite_iUnion hE).subset inter_subset_right, fun i => ⟨?_, ?_⟩⟩
  · exact subset_iUnion (fun i => V(K i)) i
  · intro e x y hl
    exact ⟨mem_iUnion.mpr ⟨i, hl.edge_mem⟩, hl.mono (hK i),
      mem_iUnion.mpr ⟨i, hl.left_mem⟩, mem_iUnion.mpr ⟨i, hl.right_mem⟩⟩

/-- An `H`-path of `G` inside a subgraph `G₀` that contains `H` is an `H`-path of `G₀`. -/
theorem IsHPathWithEnds.of_le {G G₀ H P : Graph α β} {a b : α}
    (h : IsHPathWithEnds G H P a b) (hH : H ≤ G₀) (hP : P ≤ G₀) :
    IsHPathWithEnds G₀ H P a b :=
  ⟨hH, ⟨hP, h.2.1.2⟩, h.2.2⟩

theorem IsGraphPathWithEnds.vertexSet_finite {G P : Graph α β} {a b : α}
    (h : GM09.IsGraphPathWithEnds G P a b) : V(P).Finite := by
  obtain ⟨-, W, -, hV, -⟩ := h
  rw [hV]
  exact W.support.finite_toSet

theorem IsGraphPathWithEnds.edgeSet_finite {G P : Graph α β} {a b : α}
    (h : GM09.IsGraphPathWithEnds G P a b) : E(P).Finite := by
  obtain ⟨-, W, -, -, hE⟩ := h
  rw [hE]
  exact W.edges.finite_toSet

/-- A walk between two distinct vertices has an edge. -/
theorem GraphWalk.nonempty_edge_of_ne {G : Graph α β} {a b : α} (W : GraphWalk G a b)
    (hab : a ≠ b) : Nonempty β := by
  cases W with
  | nil _ => exact (hab rfl).elim
  | @cons _ _ _ e _ _ => exact ⟨e⟩

/-- A wall has a vertex and an edge. -/
theorem Wall.nonempty_types (W : Wall α β) : Nonempty α ∧ Nonempty β := by
  have h2 := W.two_le_height
  have hp : ((1 : ℕ), (0 : ℕ)) ∈ elementaryWallVerts W.height := by
    refine ⟨by omega, by omega, by simp, ?_⟩
    simp only [ne_eq, Prod.mk.injEq, not_and]
    omega
  have hq : ((2 : ℕ), (0 : ℕ)) ∈ elementaryWallVerts W.height := by
    refine ⟨by omega, by omega, by simp, ?_⟩
    simp only [ne_eq, Prod.mk.injEq, not_and]
    omega
  have hadj : elementaryWallAdj W.height (1, 0) (2, 0) := ⟨hp, hq, Or.inl ⟨rfl, Or.inl rfl⟩⟩
  exact ⟨⟨W.branchVertex _ hp⟩, ⟨W.baseEdge hadj⟩⟩

/-! ## A bound on the distance in a low wall -/

/-- **Two vertices of a wall drawn as in Fig. 1 are at distance at most `2h + 2`.** Every vertex
lies on a brick, and two bricks are at most `2h` steps apart. -/
theorem DrawnWall.IsFigure1.dist_le {W : DrawnWall α β} (hW : W.IsFigure1) {u v : α}
    (hu : u ∈ V(W.graph)) (hv : v ∈ V(W.graph)) : W.dist u v ≤ 2 * W.height + 2 := by
  obtain ⟨φ, pos, Γ, hpos, -, hdist, -⟩ := hW.exists_fig1Coords
  have he : Even W.height := W.toWall.even_height
  have hh2 : 2 ≤ W.height := W.toWall.two_le_height
  obtain ⟨x, y, hb, hxb⟩ := exists_fig1Brick_of_mem_fig1Set hh2 he (hpos u hu)
  obtain ⟨x', y', hb', hxb'⟩ := exists_fig1Brick_of_mem_fig1Set hh2 he (hpos v hv)
  have h1 := planeWallDist_le_of_mem_fig1Brick (by omega) he hb hb' hxb hxb'
  obtain ⟨-, hx2, hy1⟩ := hb
  obtain ⟨-, hx2', hy1'⟩ := hb'
  have h2 : hexDist ((x : ℤ) + 1, (y : ℤ)) ((x' : ℤ) + 1, (y' : ℤ)) ≤ 2 * (W.height : ℤ) := by
    simp only [hexDist]
    have : (x : ℤ) + 2 ≤ 2 * W.height + 1 := by exact_mod_cast hx2
    have : (x' : ℤ) + 2 ≤ 2 * W.height + 1 := by exact_mod_cast hx2'
    have : (y : ℤ) + 1 ≤ W.height := by exact_mod_cast hy1
    have : (y' : ℤ) + 1 ≤ W.height := by exact_mod_cast hy1'
    simp only [max_def]
    split_ifs <;> omega
  rw [hdist u hu v hv]
  omega

/-! ## (7.4) -/

/-- **(7.4)** (page 90). For every `p` there is `r` such that, for every graph `G` with a wall
`H` drawn as in Fig. 1, `C(p, 2)` mutually vertex-disjoint `H`-paths of `G` whose ends are
mutually at distance at least `r` give a model of `K_p` in `G`. -/
theorem theorem_7_4_proof (p : ℕ) : ∃ r : ℕ, ∀ {α : Type u} {β : Type v},
    Theorem74For (α := α) (β := β) p r := by
  classical
  obtain ⟨N, -, hspan⟩ := GM12.theorem_4_4_span GM09.isClosedSurface_sphere p
  refine ⟨4 * N + 5, fun {α β} G H hH hHG P s t hP hPdisj hfar hst => ?_⟩
  have hαβ := H.toWall.nonempty_types
  haveI := hαβ.1
  haveI := hαβ.2
  -- the case `p ≤ 1`: no paths are needed
  by_cases hp : p ≤ 1
  · have hb := H.toWall.branchVertex_mem_graph (1, 0) (by
      have h2 := H.toWall.two_le_height
      refine ⟨by omega, by omega, by simp, ?_⟩
      simp only [ne_eq, Prod.mk.injEq, not_and]
      omega)
    exact hasGraphModel_completeGraph_of_le_one (hHG.vertexSet_mono hb) hp
  have hC : 0 < p.choose 2 := Nat.choose_pos (by omega)
  have hsH : ∀ i, s i ∈ V(H.graph) := fun i => (hP i).2.2.2.1
  have htH : ∀ i, t i ∈ V(H.graph) := fun i => (hP i).2.2.2.2.1
  -- the wall is high: otherwise any two vertices are closer than `r`
  have hhigh : 2 * N + 2 ≤ H.height := by
    by_contra hlow
    have h1 := hst ⟨0, hC⟩
    have h2 := hH.dist_le (hsH ⟨0, hC⟩) (htH ⟨0, hC⟩)
    omega
  -- a finite part `G₀` of `G` holding the wall and the paths
  obtain ⟨G₀, hG₀G, hV₀, hE₀, hK⟩ :=
    exists_finite_le (G := G) (fun o : Option (Fin (p.choose 2)) => o.elim H.graph P)
      (by rintro (_ | i); exacts [hHG, (hP i).2.1.1])
      (by rintro (_ | i); exacts [H.toWall.vertexSet_finite,
        IsGraphPathWithEnds.vertexSet_finite (hP i).2.1])
      (by rintro (_ | i); exacts [H.toWall.edgeSet_finite,
        IsGraphPathWithEnds.edgeSet_finite (hP i).2.1])
  have hHG₀ : H.graph ≤ G₀ := hK none
  have hPG₀ : ∀ i, P i ≤ G₀ := fun i => hK (some i)
  -- the sphere drawing, the tangle and its metric
  obtain ⟨φ, pos, Γ, hpos, hinj, hdist, hΓU, hΓv, hΓe, h2cell⟩ := hH.exists_fig1Coords
  obtain ⟨η, Tstar, T, hηim, hηv, hCtrl, hrow⟩ :=
    H.toWall.exists_controlled_tangle hHG₀ hV₀ hE₀ Γ
  have hS := GM09.isClosedSurface_sphere
  have hSphere : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hresp := GM16.drawing_tangle_isRespectful_of_isSphere hS hSphere Γ.drawing
    hCtrl.isTangle_H
  obtain ⟨d, hd⟩ := GM16.exists_tangleMetric hS ⟨h2cell, hCtrl.isTangle_H, hresp⟩
  -- the points of the vertices
  let pt : α → OnePoint EuclideanPlane := fun x => fig1Sph φ (pos x)
  have hptV : ∀ x ∈ V(H.graph), pt x ∈ Γ.drawing.V := fun x hx => by
    have := (Γ.iso.vertexEquiv ⟨x, hx⟩).2
    rwa [hΓv] at this
  have hptη : ∀ x ∈ V(H.graph), η.vMap (pt x) = x := fun x hx => by
    have := hηv ⟨x, hx⟩
    rwa [hΓv] at this
  have hptinj : ∀ x ∈ V(H.graph), ∀ y ∈ V(H.graph), pt x = pt y → x = y :=
    fun x hx y hy hxy => hinj hx hy ((isOpenEmbedding_fig1Sph φ).injective hxy)
  -- the ends of the paths
  have hsP : ∀ i, s i ∈ V(P i) := fun i => (hP i).2.1.left_mem
  have htP : ∀ i, t i ∈ V(P i) := fun i => (hP i).2.1.right_mem
  have hsame : ∀ i j, ∀ x ∈ V(P i), x ∈ V(P j) → i = j := by
    intro i j x hxi hxj
    by_contra hij
    exact disjoint_left.mp (hPdisj hij) hxi hxj
  have hends : ∀ x ∈ range s ∪ range t, ∀ y ∈ range s ∪ range t, x ≠ y →
      4 * N + 5 ≤ H.dist x y := by
    have key : ∀ i j x y, x ∈ ({s i, t i} : Set α) → y ∈ ({s j, t j} : Set α) → x ≠ y →
        4 * N + 5 ≤ H.dist x y := by
      intro i j x y hx hy hxy
      by_cases hij : i = j
      · subst hij
        rcases hx with rfl | hx <;> rcases hy with rfl | hy
        · exact (hxy rfl).elim
        · rw [mem_singleton_iff] at hy; subst hy; exact hst i
        · rw [mem_singleton_iff] at hx; subst hx; rw [H.dist_comm]; exact hst i
        · rw [mem_singleton_iff] at hx hy; subst hx hy; exact (hxy rfl).elim
      · obtain ⟨h1, h2, h3, h4⟩ := hfar i j hij
        rcases hx with rfl | hx <;> rcases hy with rfl | hy
        · exact h1
        · rw [mem_singleton_iff] at hy; subst hy; exact h2
        · rw [mem_singleton_iff] at hx; subst hx; exact h3
        · rw [mem_singleton_iff] at hx hy; subst hx hy; exact h4
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩) y (⟨j, rfl⟩ | ⟨j, rfl⟩) hxy
    · exact key i j _ _ (Or.inl rfl) (Or.inl rfl) hxy
    · exact key i j _ _ (Or.inl rfl) (Or.inr rfl) hxy
    · exact key i j _ _ (Or.inr rfl) (Or.inl rfl) hxy
    · exact key i j _ _ (Or.inr rfl) (Or.inr rfl) hxy
  have hendsH : ∀ x ∈ range s ∪ range t, x ∈ V(H.graph) := by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    exacts [hsH i, htH i]
  -- the indices of XII (4.4)
  have hcard : p * (p - 1) / 2 = p.choose 2 := (Nat.choose_two_right p).symm
  let c : Fin (p * (p - 1) / 2) → Fin (p.choose 2) := Fin.cast hcard
  have hc : Injective c := Fin.cast_injective hcard
  let s' : Fin (p * (p - 1) / 2) → OnePoint EuclideanPlane := fun i => pt (s (c i))
  let t' : Fin (p * (p - 1) / 2) → OnePoint EuclideanPlane := fun i => pt (t (c i))
  have hcm := hspan G₀ H.height H.height Tstar Γ.drawing η T d s' t' (fun i => P (c i)) hCtrl hd
    (by omega)
    (fun i => ⟨hptV _ (hsH _), hptV _ (htH _), fun h =>
      (hP (c i)).2.2.1 (hptinj _ (hsH _) _ (htH _) h)⟩)
    (fun i j h => hc (hsame _ _ _ (hsP (c i))
      ((hptinj _ (hsH _) _ (hsH _) h) ▸ hsP (c j))))
    (fun i j h => hc (hsame _ _ _ (htP (c i))
      ((hptinj _ (htH _) _ (htH _) h) ▸ htP (c j))))
    (by
      refine disjoint_left.mpr ?_
      rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
      have hst' : s (c i) = t (c j) := hptinj _ (hsH _) _ (htH _) hj.symm
      have hij : c i = c j := hsame _ _ _ (hsP (c i)) (hst' ▸ htP (c j))
      rw [hij] at hst'
      exact (hP (c j)).2.2.1 hst')
    (by
      have hpair : ∀ a ∈ range s ∪ range t, ∀ b ∈ range s ∪ range t, pt a ≠ pt b →
          N ≤ d {pt a} {pt b} := by
        intro a ha b hb hab
        by_contra hlt
        push Not at hlt
        have h1 := wallDist_le_of_tangleMetric_lt hpos hdist hΓU hΓv hΓe hrow hd hhigh
          (hendsH a ha) (hendsH b hb) hlt
        have h2 := hends a ha b hb (fun h => hab (by rw [h]))
        omega
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩) _ (⟨j, rfl⟩ | ⟨j, rfl⟩) hxy
      · exact hpair _ (Or.inl ⟨_, rfl⟩) _ (Or.inl ⟨_, rfl⟩) hxy
      · exact hpair _ (Or.inl ⟨_, rfl⟩) _ (Or.inr ⟨_, rfl⟩) hxy
      · exact hpair _ (Or.inr ⟨_, rfl⟩) _ (Or.inl ⟨_, rfl⟩) hxy
      · exact hpair _ (Or.inr ⟨_, rfl⟩) _ (Or.inr ⟨_, rfl⟩) hxy)
    (fun i => by
      rw [hηim, hptη _ (hsH _), hptη _ (htH _)]
      exact IsHPathWithEnds.of_le (hP (c i)) hHG₀ (hPG₀ _))
    (fun i j hij => hPdisj (fun h => hij (hc h)))
  exact (hasGraphModel_of_controlsMinor (GM16.controlsMinor_of_gm12 hcm)).mono hG₀G

/-! ## (7.5) -/

/-- **(7.5)** (page 91). For every `p` there are `l = 2C(p,2)² - C(p,2) + 3` and `m` such that,
for every graph `G` with a wall `H` drawn as in Fig. 1, `C(p, 2)` external `(l, m)`-stars over
`H` with distinct centers give a model of `K_p` in `G`. -/
theorem theorem_7_5_proof (p : ℕ) : ∃ m : ℕ, ∀ {α : Type u} {β : Type v} (G : Graph α β)
    (H : DrawnWall α β), H.IsFigure1 → IsWallIn G H.toWall →
    ∀ (S : Fin (p.choose 2) → Graph α β) (v : Fin (p.choose 2) → α),
      (∀ a, IsExternalLMStarOver G H (2 * p.choose 2 ^ 2 - p.choose 2 + 3) m (S a) (v a)) →
      Injective v → HasGraphModel (GM16.completeGraph p) G := by
  obtain ⟨r, hr⟩ := theorem_7_4_proof.{u, v} p
  exact ⟨2 * r, fun G H hH hHG S v hS hv => theorem_7_5_of_theorem_7_4 hr G H hH hHG S v hS hv⟩

end GraphMinor.GM13
