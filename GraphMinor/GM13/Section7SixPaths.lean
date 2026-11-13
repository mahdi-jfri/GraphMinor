module

public import GraphMinor.GM13.Section7SixCells
public import GraphMinor.GM13.Section7
import GraphMinor.GM11.Walks

/-!
# Graph Minors XIII, (7.6): moving the legs of a star onto a subwall

In the proof of (7.6), each leg `P_j` of a star over `H` ends at a vertex `u_j` of `H`, and is
extended by a path `Q_j` of `H` from `u_j` to the smaller wall `H'`, chosen minimal, so that its
only vertex in `H'` is its end `w_j`. This file proves what is needed about these paths.

* A wall is connected (`Wall.exists_walk`), so the path `Q_j` exists
  (`Wall.exists_path_to_subwall`).
* The points of `Q_j` in the drawing join the points of `u_j` and `w_j`
  (`joinedIn_subPts`), and meet the drawing of `H'` only at the point of `w_j`
  (`subPts_inter_indU_subset`).
* So if `d'(u_j, u_{j'}) ≥ 3`, then `Q_j` and `Q_{j'}` are disjoint
  (`disjoint_of_three_le_planeWallDist`): this is the paper's "$u_j$ and $u_{j'}$ do not belong
  to the closure of the same region of $H_i$, and hence $Q_j$ and $Q_{j'}$ are vertex-disjoint".
* And `d'(u_j, u_{j'}) ≤ d'(w_j, w_{j'})` (`planeWallDist_le_of_paths`), so the new ends are as
  far apart as the old ones. The paper uses this step without comment.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM09

universe u v

variable {α : Type u} {β : Type v}

/-! ## Walks and paths -/

/-- A walk that ends in a set `X` has a first vertex in `X`: the part of the walk up to it is a
walk whose only vertex in `X` is its last one. -/
theorem _root_.GraphMinor.Surface.GraphWalk.exists_prefix_mem {G : Graph α β} (X : Set α) :
    ∀ {a b : α} (w : GraphWalk G a b), b ∈ X →
      ∃ c ∈ X, ∃ w' : GraphWalk G a c, (∀ x ∈ w'.support, x ∈ w.support) ∧
        ∀ x ∈ w'.support, x ∈ X → x = c
  | a, _, .nil ha, hb => ⟨a, hb, .nil ha, fun x hx => hx, fun x hx _ => by
      simpa [GraphWalk.support] using hx⟩
  | a, b, .cons hl rest, hb => by
    by_cases haX : a ∈ X
    · refine ⟨a, haX, .nil hl.left_mem, fun x hx => ?_, fun x hx _ => by
        simpa [GraphWalk.support] using hx⟩
      simp only [GraphWalk.support, List.mem_singleton] at hx
      simp [GraphWalk.support, hx]
    · obtain ⟨c, hc, w', hsub, hfirst⟩ := exists_prefix_mem X rest hb
      refine ⟨c, hc, .cons hl w', fun x hx => ?_, fun x hx hxX => ?_⟩
      · simp only [GraphWalk.support, List.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (hsub x hx)
      · simp only [GraphWalk.support, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd hxX haX
        · exact hfirst x hx hxX

/-- If a walk from `a` ends in `X`, there is a path from `a` to a vertex `c ∈ X` whose only
vertex in `X` is `c`. -/
theorem exists_path_to_set {G : Graph α β} (X : Set α) {a b : α} (w : GraphWalk G a b)
    (hb : b ∈ X) :
    ∃ c, ∃ P : Graph α β, IsGraphPathWithEnds G P a c ∧ V(P) ∩ X = {c} := by
  obtain ⟨c, hc, w', -, hfirst⟩ := w.exists_prefix_mem X hb
  obtain ⟨P, hP, hPV, -⟩ := exists_isGraphPathWithEnds_of_walk w'
  refine ⟨c, P, hP, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxP, hxX⟩
    exact hfirst x (hPV hxP) hxX
  · rintro x rfl
    exact ⟨hP.right_mem, hc⟩

/-- An edge of a simple walk joins two distinct vertices. -/
theorem _root_.GraphMinor.Surface.GraphWalk.exists_isLink_ne_of_mem_edges {G : Graph α β} :
    ∀ {a b : α} (w : GraphWalk G a b), w.IsSimple → ∀ {f : β}, f ∈ w.edges →
      ∃ x y, x ≠ y ∧ G.IsLink f x y
  | _, _, .nil _, _, _, hf => by simp [GraphWalk.edges] at hf
  | a, _, .cons (v := v) (e := e) hl rest, hw, f, hf => by
    have hnd : a ∉ rest.support ∧ rest.support.Nodup := by
      simpa [GraphWalk.IsSimple, GraphWalk.support] using hw
    simp only [GraphWalk.edges, List.mem_cons] at hf
    rcases hf with rfl | hf
    · refine ⟨a, v, fun h => hnd.1 ?_, hl⟩
      rw [h]
      exact rest.start_mem_support
    · exact exists_isLink_ne_of_mem_edges rest hnd.2 hf

/-- A path has no loop: the two ends of each of its edges are distinct. -/
theorem _root_.GraphMinor.GM09.IsGraphPathWithEnds.ne_of_isLink {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) {f : β} {x y : α} (hl : P.IsLink f x y) : x ≠ y := by
  obtain ⟨-, w, hw, -, hE⟩ := hP
  have hf : f ∈ w.edges := by
    have := hl.edge_mem
    rw [hE] at this
    exact this
  obtain ⟨x', y', hne, hl'⟩ := w.exists_isLink_ne_of_mem_edges hw hf
  rintro rfl
  rcases P.eq_or_eq_of_isLink_of_isLink hl' hl with h1 | h1 <;>
  rcases P.eq_or_eq_of_isLink_of_isLink hl'.symm hl with h2 | h2 <;>
  exact hne (h1.trans h2.symm)

/-! ## A wall is connected -/

/-- A walk of a subgraph `H ≤ G` is a walk of `G`. -/
def walkOfLE {G H : Graph α β} (hle : H ≤ G) : ∀ {a b : α}, GraphWalk H a b → GraphWalk G a b
  | _, _, .nil ha => .nil (hle.vertexSet_mono ha)
  | _, _, .cons hl rest => .cons (hle.isLink_mono hl) (walkOfLE hle rest)

/-- In the elementary wall, the row `y` holds a walk from `(x, y)` to `(x + n, y)` when all the
points between are vertices. -/
theorem elementaryWall_row_walk {h y : ℕ} :
    ∀ (n x : ℕ), (∀ i ≤ n, (x + i, y) ∈ elementaryWallVerts h) →
      Nonempty (GraphWalk (elementaryWall h) (x, y) (x + n, y))
  | 0, x, hv => ⟨.nil (hv 0 le_rfl)⟩
  | n + 1, x, hv => by
    have hadj : elementaryWallAdj h (x, y) (x + 1, y) :=
      ⟨by simpa using hv 0 (by omega), hv 1 (by omega), Or.inl ⟨rfl, Or.inl rfl⟩⟩
    obtain ⟨w⟩ := elementaryWall_row_walk n (x + 1) (fun i hi => by
      have := hv (i + 1) (by omega)
      rwa [show x + (i + 1) = x + 1 + i by omega] at this)
    rw [show x + (n + 1) = x + 1 + n by omega]
    exact ⟨.cons (e := s((x, y), (x + 1, y))) ⟨hadj, rfl⟩ w⟩

/-- Every vertex of the elementary wall of height `h ≥ 1` is joined to `(1, 0)` by a walk: go
along its row to column `1` or `2`, down one row, and repeat. -/
theorem elementaryWall_walk_one_zero {h : ℕ} (hh : 1 ≤ h) :
    ∀ (y x : ℕ), (x, y) ∈ elementaryWallVerts h →
      Nonempty (GraphWalk (elementaryWall h) (x, y) (1, 0)) := by
  have hrow : ∀ {x c y : ℕ}, (x, y) ∈ elementaryWallVerts h → (c, y) ∈ elementaryWallVerts h →
      Nonempty (GraphWalk (elementaryWall h) (x, y) (c, y)) := by
    intro x c y hx hc
    have hmid : ∀ i, min x c ≤ i → i ≤ max x c → (i, y) ∈ elementaryWallVerts h := by
      intro i h1 h2
      simp only [elementaryWallVerts, mem_ofPred_eq, ne_eq, Prod.mk.injEq] at hx hc ⊢
      omega
    rcases le_total x c with hxc | hxc
    · obtain ⟨w⟩ := elementaryWall_row_walk (h := h) (y := y) (c - x) x
        (fun i hi => hmid _ (by omega) (by omega))
      rw [show x + (c - x) = c by omega] at w
      exact ⟨w⟩
    · obtain ⟨w⟩ := elementaryWall_row_walk (h := h) (y := y) (x - c) c
        (fun i hi => hmid _ (by omega) (by omega))
      rw [show c + (x - c) = x by omega] at w
      exact ⟨w.reverse⟩
  intro y
  induction y with
  | zero =>
    intro x hx
    exact hrow hx ⟨by omega, by omega, by simp, by simp; omega⟩
  | succ y ih =>
    intro x hx
    -- the column `c` with a vertical edge from row `y` to row `y + 1`
    obtain ⟨c, hc1, hc2, hodd⟩ : ∃ c, 1 ≤ c ∧ c ≤ 2 ∧ Odd (c + y) := by
      rcases Nat.even_or_odd y with hy | hy
      · exact ⟨1, le_rfl, by omega, by rw [add_comm]; exact hy.add_one⟩
      · exact ⟨2, by omega, le_rfl, by
          obtain ⟨k, hk⟩ := hy
          exact ⟨k + 1, by omega⟩⟩
    have hv : ∀ y' ≤ h, (c, y') ∈ elementaryWallVerts h := by
      intro y' hy'
      simp only [elementaryWallVerts, mem_ofPred_eq, ne_eq, Prod.mk.injEq]
      omega
    have hy1 : y + 1 ≤ h := by
      simp only [elementaryWallVerts, mem_ofPred_eq] at hx
      omega
    obtain ⟨w₁⟩ := hrow hx (hv (y + 1) hy1)
    have hadj : elementaryWallAdj h (c, y + 1) (c, y) :=
      ⟨hv _ hy1, hv _ (by omega), Or.inr ⟨rfl, Or.inr ⟨rfl, hodd⟩⟩⟩
    obtain ⟨w₂⟩ := ih c (hv y (by omega))
    exact ⟨w₁.append (.cons (e := s((c, y + 1), (c, y))) ⟨hadj, rfl⟩ w₂)⟩

/-- A walk of the elementary wall lifts to a walk of the wall between the branch vertices of its
ends, through the paths that subdivide its edges. -/
theorem Wall.walk_of_elementary (W : Wall α β) :
    ∀ {p q : ℕ × ℕ} (_w : GraphWalk (elementaryWall W.height) p q)
      (hp : p ∈ elementaryWallVerts W.height) (hq : q ∈ elementaryWallVerts W.height),
      Nonempty (GraphWalk W.graph (W.branchVertex p hp) (W.branchVertex q hq))
  | _, _, .nil _, hp, _ => ⟨.nil (W.branchVertex_mem_graph _ hp)⟩
  | _, _, .cons hl rest, hp, hq => by
    obtain ⟨hle, w₀, -⟩ := W.isGraphPathWithEnds_baseEdge hl.1
    obtain ⟨w₁⟩ := W.walk_of_elementary rest hl.1.2.1 hq
    exact ⟨(walkOfLE hle w₀).append w₁⟩

theorem Wall.one_zero_mem (W : Wall α β) : ((1, 0) : ℕ × ℕ) ∈ elementaryWallVerts W.height := by
  have := W.two_le_height
  simp only [elementaryWallVerts, mem_ofPred_eq, ne_eq, Prod.mk.injEq]
  omega

/-- Every vertex of a wall is joined by a walk to the branch vertex `(1, 0)`. -/
theorem Wall.exists_walk_one_zero (W : Wall α β) {x : α} (hx : x ∈ V(W.graph)) :
    Nonempty (GraphWalk W.graph x (W.branchVertex (1, 0) W.one_zero_mem)) := by
  have hh : 1 ≤ W.height := by have := W.two_le_height; omega
  have hlift : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      Nonempty (GraphWalk W.graph (W.branchVertex p hp) (W.branchVertex (1, 0) W.one_zero_mem)) := by
    intro p hp
    obtain ⟨w⟩ := elementaryWall_walk_one_zero hh p.2 p.1 hp
    exact W.walk_of_elementary w hp _
  by_cases hxB : x ∈ V(W.baseGraph)
  · obtain ⟨p, hp, rfl⟩ := W.exists_branchVertex_eq hxB
    exact hlift p hp
  · rw [W.vertexSet_eq] at hx
    rcases hx with hx | hx
    · exact absurd hx hxB
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      obtain ⟨p, q, hadj, rfl⟩ := W.exists_baseEdge_eq he
      obtain ⟨hle, w, -, hV, -⟩ := W.isGraphPathWithEnds_baseEdge hadj
      rw [hV] at hxe
      obtain ⟨-, w₂, -⟩ := w.exists_append_of_mem hxe
      obtain ⟨w₃⟩ := hlift q hadj.2.1
      exact ⟨(walkOfLE hle w₂).append w₃⟩

/-- **A wall is connected.** Any two vertices of a wall are joined by a walk. -/
theorem Wall.exists_walk (W : Wall α β) {x y : α} (hx : x ∈ V(W.graph)) (hy : y ∈ V(W.graph)) :
    Nonempty (GraphWalk W.graph x y) := by
  obtain ⟨w₁⟩ := W.exists_walk_one_zero hx
  obtain ⟨w₂⟩ := W.exists_walk_one_zero hy
  exact ⟨w₁.append w₂.reverse⟩

/-- **A minimal path to a subwall.** For a vertex `u` of a wall `H` and a wall `H' ≤ H`, there is
a path of `H` from `u` to a vertex `w` of `H'` whose only vertex in `H'` is `w`. -/
theorem Wall.exists_path_to_subwall (H H' : Wall α β) (hle : H'.graph ≤ H.graph) {u : α}
    (hu : u ∈ V(H.graph)) :
    ∃ w, ∃ Q : Graph α β, IsGraphPathWithEnds H.graph Q u w ∧ V(Q) ∩ V(H'.graph) = {w} := by
  have hb := H'.branchVertex_mem_graph (1, 0) H'.one_zero_mem
  obtain ⟨w⟩ := H.exists_walk hu (hle.vertexSet_mono hb)
  exact exists_path_to_set V(H'.graph) w hb

/-! ## The points of a path, and a path that meets a subwall only at its end -/

theorem lineEnds_left_mem {L : Set EuclideanPlane} {s t : EuclideanPlane}
    (hL : IsLineWithEnds L s t) : s ∈ L := by
  obtain ⟨f, h0, -⟩ := hL
  exact h0 ▸ (f 0).2

theorem lineEnds_right_mem {L : Set EuclideanPlane} {s t : EuclideanPlane}
    (hL : IsLineWithEnds L s t) : t ∈ L := by
  obtain ⟨f, -, h1⟩ := hL
  exact h1 ▸ (f 1).2


section Points

variable {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane)

/-- The points of a subgraph `P` in the drawing `Γ`: the points of its vertices and edges. -/
noncomputable def subPts (P : Graph α β) : Set EuclideanPlane :=
  ptV Γ '' V(P) ∪ ⋃ f ∈ E(P), arcE Γ f

theorem subPts_mono {P Q : Graph α β} (hPQ : P ≤ Q) : subPts Γ P ⊆ subPts Γ Q :=
  union_subset_union (image_mono hPQ.vertexSet_mono)
    (biUnion_subset_biUnion_left hPQ.edgeSet_mono)

/-- Distinct edges have disjoint points, since they are distinct arc components of `U \ V`. -/
theorem eq_of_mem_arcE {f g : β} (hf : f ∈ E(G)) (hg : g ∈ E(G)) {z : EuclideanPlane}
    (hzf : z ∈ arcE Γ f) (hzg : z ∈ arcE Γ g) : f = g := by
  have e := Γ.drawing.edge_eq_of_mem (arcE_mem_E Γ hf) (arcE_mem_E Γ hg) hzf hzg
  rw [arcE_of_mem Γ hf, arcE_of_mem Γ hg] at e
  exact congrArg Subtype.val (Γ.iso.edgeEquiv.injective (Subtype.ext e))

/-- The closure of an edge with distinct ends is a line between the points of its ends. -/
theorem isLineWithEnds_closure_arcE {f : β} {x y : α} (hl : G.IsLink f x y) (hxy : x ≠ y) :
    IsLineWithEnds (closure (arcE Γ f)) (ptV Γ x) (ptV Γ y) := by
  have hne : ptV Γ x ≠ ptV Γ y := fun e => hxy (ptV_injOn Γ hl.left_mem hl.right_mem e)
  have hl' := (Γ.iso.isLink_iff ⟨f, hl.edge_mem⟩ ⟨x, hl.left_mem⟩ ⟨y, hl.right_mem⟩).mp hl
  obtain ⟨he, -, -, hcap⟩ := hl'
  rw [ptV_of_mem Γ hl.left_mem, ptV_of_mem Γ hl.right_mem] at hne
  rw [arcE_of_mem Γ hl.edge_mem, ptV_of_mem Γ hl.left_mem, ptV_of_mem Γ hl.right_mem]
  rcases Γ.drawing.edge_cond _ he with ⟨u, w, -, hc, hL⟩ | ⟨u, hc, -⟩
  · rw [hc] at hcap
    rcases Set.pair_eq_pair_iff.mp hcap with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]; exact hL
    · rw [← h1, ← h2]; exact hL.symm
  · rw [hc] at hcap
    have hx : (Γ.iso.vertexEquiv ⟨x, hl.left_mem⟩ : EuclideanPlane) ∈ ({u} : Set EuclideanPlane) := by
      rw [hcap]; exact mem_insert _ _
    have hy : (Γ.iso.vertexEquiv ⟨y, hl.right_mem⟩ : EuclideanPlane) ∈ ({u} : Set EuclideanPlane) := by
      rw [hcap]; exact mem_insert_of_mem _ rfl
    exact absurd ((mem_singleton_iff.mp hx).trans (mem_singleton_iff.mp hy).symm) hne

/-- The points of a path join the points of its ends. -/
theorem joinedIn_subPts {P : Graph α β} {a b : α} (hP : IsGraphPathWithEnds G P a b) :
    JoinedIn (subPts Γ P) (ptV Γ a) (ptV Γ b) := by
  obtain ⟨hle, w, hw, hV, hE⟩ := hP
  have key : ∀ {x y : α} (w' : GraphWalk P x y), w'.IsSimple →
      (∀ z ∈ w'.support, z ∈ V(P)) → JoinedIn (subPts Γ P) (ptV Γ x) (ptV Γ y) := by
    intro x y w'
    induction w' with
    | nil hx => exact fun _ _ => JoinedIn.refl (Or.inl ⟨_, hx, rfl⟩)
    | @cons x' v' y' e hl rest ih =>
      intro hs hsub
      have hnd : x' ∉ rest.support ∧ rest.support.Nodup := by
        simpa [GraphWalk.IsSimple, GraphWalk.support] using hs
      have hxv : x' ≠ v' := fun h => hnd.1 (h ▸ rest.start_mem_support)
      have h1 : JoinedIn (subPts Γ P) (ptV Γ x') (ptV Γ v') := by
        have hL := isLineWithEnds_closure_arcE Γ (hle.isLink_mono hl) hxv
        have hsubset : closure (arcE Γ e) ⊆ subPts Γ P := by
          rw [closure_arcE Γ (hle.isLink_mono hl)]
          rintro z (hz | rfl | rfl)
          · exact Or.inr (mem_iUnion₂.mpr ⟨e, hl.edge_mem, hz⟩)
          · exact Or.inl ⟨x', hl.left_mem, rfl⟩
          · exact Or.inl ⟨v', hl.right_mem, rfl⟩
        exact ((GM07.joinedIn_iff_eq_or_exists_isLineWithEnds (hsubset (lineEnds_left_mem hL))
          (hsubset (lineEnds_right_mem hL))).mpr (Or.inr ⟨_, hsubset, hL⟩))
      exact h1.trans (ih hnd.2 (fun z hz => hsub z (by
        simp only [GraphWalk.support, List.mem_cons]; exact Or.inr hz)))
  exact key w hw (fun z hz => by rw [hV]; exact hz)

/-- The points of a path whose only vertex in a wall `W'` is its end `b` meet the drawing of
`W'` only at the point of `b`. A vertex point on the drawing of `W'` is a vertex of `W'`; an edge
on it is an edge of `W'`, whose two distinct ends would both be `b`. -/
theorem subPts_inter_indU_subset {P : Graph α β} {a b : α} (hP : IsGraphPathWithEnds G P a b)
    {W' : Wall α β} (hW' : W'.graph ≤ G) (hX : V(P) ∩ V(W'.graph) ⊆ {b}) :
    subPts Γ P ∩ indU Γ W' ⊆ {ptV Γ b} := by
  have hPV : V(P) ⊆ V(G) := hP.le.vertexSet_mono
  rintro z ⟨⟨x, hx, rfl⟩ | hz, hz' | hz'⟩
  · obtain ⟨y, hy, e⟩ := hz'
    have hxy := ptV_injOn Γ (hW'.vertexSet_mono hy) (hPV hx) e
    rw [hX ⟨hx, hxy ▸ hy⟩]
    rfl
  · obtain ⟨g, hg, hzg⟩ := mem_iUnion₂.mp hz'
    exact absurd hzg (ptV_not_mem_arcE Γ (hPV hx) g)
  · obtain ⟨f, hf, hzf⟩ := mem_iUnion₂.mp hz
    obtain ⟨y, hy, rfl⟩ := hz'
    exact absurd hzf (ptV_not_mem_arcE Γ (hW'.vertexSet_mono hy) f)
  · obtain ⟨f, hf, hzf⟩ := mem_iUnion₂.mp hz
    obtain ⟨g, hg, hzg⟩ := mem_iUnion₂.mp hz'
    have hfg := eq_of_mem_arcE Γ (hP.le.edgeSet_mono hf) (hW'.edgeSet_mono hg) hzf hzg
    subst hfg
    obtain ⟨x, y, hlP⟩ := exists_isLink_of_mem_edgeSet hf
    obtain ⟨x', y', hlW⟩ := exists_isLink_of_mem_edgeSet hg
    have hxy := hP.ne_of_isLink hlP
    have hG := hP.le.isLink_mono hlP
    have hG' := hW'.isLink_mono hlW
    have h1 : x = b := by
      rcases G.eq_or_eq_of_isLink_of_isLink hG hG' with e | e
      · exact hX ⟨hlP.left_mem, e ▸ hlW.left_mem⟩
      · exact hX ⟨hlP.left_mem, e ▸ hlW.right_mem⟩
    have h2 : y = b := by
      rcases G.eq_or_eq_of_isLink_of_isLink hG.symm hG' with e | e
      · exact hX ⟨hlP.right_mem, e ▸ hlW.left_mem⟩
      · exact hX ⟨hlP.right_mem, e ▸ hlW.right_mem⟩
    exact absurd (h1.trans h2.symm) hxy

end Points

/-- A set that joins `s` to `t` and meets `U` in finitely many points gives
`d(s, t) ≤ |Z ∩ U|`: it contains a line from `s` to `t`. -/
theorem planeWallDist_le_of_joinedIn {U Z : Set EuclideanPlane} {s t : EuclideanPlane}
    (hj : JoinedIn Z s t) (hfin : (Z ∩ U).Finite) : planeWallDist U s t ≤ (Z ∩ U).ncard := by
  by_cases hst : s = t
  · subst hst; rw [planeWallDist_self]; exact Nat.zero_le _
  obtain ⟨L, hLZ, hL⟩ := ((GM07.joinedIn_iff_eq_or_exists_isLineWithEnds hj.mem.1 hj.mem.2).mp
    hj).resolve_left hst
  have hsub : L ∩ U ⊆ Z ∩ U := inter_subset_inter_left _ hLZ
  exact (planeWallDist_le_ncard hst hL (hfin.subset hsub)).trans (ncard_le_ncard hsub hfin)

/-! ## Moving the ends of a star onto a subwall -/

section Reroute

variable {G : Graph α β} {Γ : GraphDrawing G EuclideanPlane} {W' : Wall α β}

/-- **The paths `Q_j` are disjoint** (proof of (7.6), claim (1): "$u_j$ and $u_{j'}$ do not belong
to the closure of the same region of $H_i$, and hence $Q_j$ and $Q_{j'}$ are vertex-disjoint").
Let `Q₁, Q₂` be paths from `a₁, a₂` whose only vertices in the wall `W'` are their ends `b₁, b₂`.
If they share a vertex `x`, the points of `Q₁` and `Q₂` join the points of `a₁` and `a₂` through
the point of `x`, and meet the drawing of `W'` at most in the points of `b₁` and `b₂`. So
`d'(a₁, a₂) ≤ 2`. -/
theorem disjoint_of_three_le_planeWallDist {Q₁ Q₂ : Graph α β} {a₁ b₁ a₂ b₂ : α}
    (hQ₁ : IsGraphPathWithEnds G Q₁ a₁ b₁) (hQ₂ : IsGraphPathWithEnds G Q₂ a₂ b₂)
    (hW' : W'.graph ≤ G) (hX₁ : V(Q₁) ∩ V(W'.graph) ⊆ {b₁})
    (hX₂ : V(Q₂) ∩ V(W'.graph) ⊆ {b₂})
    (h3 : 3 ≤ planeWallDist (indU Γ W') (ptV Γ a₁) (ptV Γ a₂)) : Disjoint V(Q₁) V(Q₂) := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  obtain ⟨P₁, -, hP₁Q, -, hP₁, -⟩ := hQ₁.exists_split_at hx₁
  obtain ⟨P₂, -, hP₂Q, -, hP₂, -⟩ := hQ₂.exists_split_at hx₂
  have J₁ := (joinedIn_subPts Γ (hP₁.mono hQ₁.le)).mono (subPts_mono Γ hP₁Q)
  have J₂ := (joinedIn_subPts Γ (hP₂.mono hQ₂.le)).mono (subPts_mono Γ hP₂Q)
  have J := (J₁.mono (subset_union_left (t := subPts Γ Q₂))).trans
    (J₂.mono (subset_union_right (s := subPts Γ Q₁))).symm
  have hsub : (subPts Γ Q₁ ∪ subPts Γ Q₂) ∩ indU Γ W' ⊆ {ptV Γ b₁, ptV Γ b₂} := by
    rw [union_inter_distrib_right]
    refine union_subset ?_ ?_
    · exact (subPts_inter_indU_subset Γ hQ₁ hW' hX₁).trans (by simp)
    · exact (subPts_inter_indU_subset Γ hQ₂ hW' hX₂).trans (by simp)
  have hfin : ((subPts Γ Q₁ ∪ subPts Γ Q₂) ∩ indU Γ W').Finite := (toFinite _).subset hsub
  have h1 := planeWallDist_le_of_joinedIn J hfin
  have h2 := ncard_le_ncard hsub (toFinite _)
  have h3' : ({ptV Γ b₁, ptV Γ b₂} : Set EuclideanPlane).ncard ≤ 2 :=
    (ncard_insert_le _ _).trans (by rw [ncard_singleton])
  omega

/-- **The ends move apart, not closer** (proof of (7.6), claim (1)). Let `Q₁, Q₂` be disjoint
paths from `a₁, a₂` to vertices `b₁, b₂` of the wall `W'`, with no other vertex in `W'`. Then
`d'(a₁, a₂) ≤ d'(b₁, b₂)`: a line `F` from `b₁` to `b₂` that attains `d'(b₁, b₂)`, with `Q₁` and
`Q₂` added at its two ends, joins `a₁` to `a₂` and meets the drawing of `W'` only in `F`. -/
theorem planeWallDist_le_of_paths {Q₁ Q₂ : Graph α β} {a₁ b₁ a₂ b₂ : α}
    (hQ₁ : IsGraphPathWithEnds G Q₁ a₁ b₁) (hQ₂ : IsGraphPathWithEnds G Q₂ a₂ b₂)
    (hW' : W'.graph ≤ G) (hb₁ : b₁ ∈ V(W'.graph)) (hb₂ : b₂ ∈ V(W'.graph))
    (hX₁ : V(Q₁) ∩ V(W'.graph) ⊆ {b₁}) (hX₂ : V(Q₂) ∩ V(W'.graph) ⊆ {b₂})
    (hdisj : Disjoint V(Q₁) V(Q₂)) {𝒰 : Set (ℤ × ℤ)} (h𝒰 : ∀ c ∈ 𝒰, ¬ IsSquareCell c)
    (hU : indU Γ W' = fig1PlaneEquiv '' cellSet 𝒰) :
    planeWallDist (indU Γ W') (ptV Γ a₁) (ptV Γ a₂) ≤
      planeWallDist (indU Γ W') (ptV Γ b₁) (ptV Γ b₂) := by
  have hne : ptV Γ b₁ ≠ ptV Γ b₂ := fun e =>
    disjoint_left.mp hdisj hQ₁.right_mem
      (ptV_injOn Γ (hQ₁.le.vertexSet_mono hQ₁.right_mem) (hQ₂.le.vertexSet_mono hQ₂.right_mem) e ▸
        hQ₂.right_mem)
  obtain ⟨F, hF, hFfin, hFcard⟩ := exists_line_ncard_eq_planeWallDist_cellSet h𝒰 hne
  rw [← hU] at hFfin hFcard
  have JF : JoinedIn F (ptV Γ b₁) (ptV Γ b₂) :=
    (GM07.joinedIn_iff_eq_or_exists_isLineWithEnds (lineEnds_left_mem hF) (lineEnds_right_mem hF)).mpr
      (Or.inr ⟨F, subset_rfl, hF⟩)
  set Z := subPts Γ Q₁ ∪ F ∪ subPts Γ Q₂
  have J : JoinedIn Z (ptV Γ a₁) (ptV Γ a₂) :=
    (((joinedIn_subPts Γ hQ₁).mono (fun z hz => Or.inl (Or.inl hz))).trans
      (JF.mono (fun z hz => Or.inl (Or.inr hz)))).trans
      ((joinedIn_subPts Γ hQ₂).symm.mono (fun z hz => Or.inr hz))
  have hb : ∀ {b : α}, b ∈ V(W'.graph) → ptV Γ b ∈ F → ptV Γ b ∈ F ∩ indU Γ W' :=
    fun hb hbF => ⟨hbF, Or.inl ⟨_, hb, rfl⟩⟩
  have hsub : Z ∩ indU Γ W' ⊆ F ∩ indU Γ W' := by
    rintro z ⟨(hz | hz) | hz, hzU⟩
    · rw [subPts_inter_indU_subset Γ hQ₁ hW' hX₁ ⟨hz, hzU⟩]
      exact hb hb₁ (lineEnds_left_mem hF)
    · exact ⟨hz, hzU⟩
    · rw [subPts_inter_indU_subset Γ hQ₂ hW' hX₂ ⟨hz, hzU⟩]
      exact hb hb₂ (lineEnds_right_mem hF)
  have h1 := planeWallDist_le_of_joinedIn J (hFfin.subset hsub)
  have h2 := ncard_le_ncard hsub hFfin
  omega

end Reroute

end GraphMinor.GM13
