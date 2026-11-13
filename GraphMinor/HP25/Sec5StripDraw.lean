module

public import GraphMinor.HP25.PlaneStrip
public import GraphMinor.HP25.Sec5StripTools
public import GraphMinor.HP25.Alternate
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.HP25.Prop32
import GraphMinor.HP25.Lemma43Reroute
import GraphMinor.Surface.Crossing
import GraphMinor.Surface.PlaneDisc

/-!
# The drawing steps of the strip argument for Lemma 5.4

This file holds the steps of the proof of the strip lemma (`Sec5Strip.lean`) that take place in a
web `H` with rib `R`, drawn by a rib embedding `φ`, and cut by the image of a path `l` of the rib
into the sides `F₁` and `F₂` (`IsTheta`).

* Clique vertices: `WebData.mem_tri_of_chain_cons`, `WebData.exists_rib_near` (the first rib vertex
  of a walk from a clique vertex lies on its triangle), `WebData.exists_tri_of_mem` (two vertices of a
  triangle of the rib determine the third), `WebData.adj_of_mem_stretch` (the vertices of a stretch of
  a walk through one clique are pairwise adjacent).
* Step 5 (`far_of_reachesOff`): a vertex joined to an arc `A₁` of the frame by a walk that misses the
  cut is drawn off the closed side `F₂`, and so is a rib vertex on the triangle of a clique vertex.
* Step 8, drawing part (`false_of_spoke`): such a vertex cannot sit on a stretch through a spoke
  `σ w` whose triangles are all on the side `F₂`.
* Step 6 (`end_tri`): the triangle of a clique vertex on a run of the cut, with a neighbour drawn off
  the closed side `F₁`, is the triangle at the run on the side `F₂`.
* Step 9 (`pairsCrossOn_of_alternate`, `false_of_joinedIn`): alternating ends on the frame cannot be
  joined by two disjoint connected sets in the closed disc (`Surface.disc_crossing`).
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface

variable {V : Type*}

/-- `ReachesOff` passes to a larger graph. -/
theorem ReachesOff.mono {G H : SimpleGraph V} {L T : List V} {x : V} (h : ReachesOff G L T x)
    (hle : G ≤ H) : ReachesOff H L T x := by
  obtain ⟨t, ht, p, hp⟩ := h
  exact ⟨t, ht, p.mapLe hle, by simpa [support_mapLe] using hp⟩

namespace WebData

variable {H : SimpleGraph V} {S : Set V} {C : List V} {R : Set V} {tri : V → Set V}

/-- A rib vertex followed in a walk by clique vertices lies on their triangle. -/
theorem mem_tri_of_chain_cons (W : WebData H S C R tri) {x : V} :
    ∀ {K : List V}, (x :: K).IsChain H.Adj → x ∈ R → (∀ k ∈ K, k ∉ R) → ∀ k ∈ K, x ∈ tri k
  | [], _, _, _, k, hk => by simp at hk
  | k₀ :: K, hc, hx, hK, k, hk => by
    have h1 := List.isChain_cons_cons.mp hc
    have hx₀ : x ∈ tri k₀ := W.mem_tri_of_adj (hK k₀ (by simp)) hx h1.1.symm
    rw [W.tri_eq_head h1.2 hK k hk]
    exact hx₀

/-- **The first rib vertex of a walk.** In a walk `w L` that meets the rib, the first rib vertex `x`
is `w`, or `w` is a clique vertex and `x` lies on its triangle. -/
theorem exists_rib_near (W : WebData H S C R tri) {w : V} {L : List V}
    (hc : (w :: L).IsChain H.Adj) (hex : ∃ t ∈ w :: L, t ∈ R) :
    ∃ α x β, w :: L = α ++ x :: β ∧ x ∈ R ∧ (x = w ∨ (w ∉ R ∧ x ∈ tri w)) := by
  obtain ⟨α, x, β, he, hx, hα⟩ := exists_first_mem (Z := R) (w :: L) hex
  refine ⟨α, x, β, he, hx, ?_⟩
  rcases α with _ | ⟨k₀, α⟩
  · left
    simp only [List.nil_append, List.cons.injEq] at he
    exact he.1.symm
  · right
    have hk₀ : k₀ = w := by
      simp only [List.cons_append, List.cons.injEq] at he
      exact he.1.symm
    subst hk₀
    refine ⟨hα k₀ (by simp), ?_⟩
    have hc' : (k₀ :: α ++ [x]).IsChain H.Adj := by
      refine hc.infix ⟨[], β, ?_⟩
      rw [he]; simp
    have hrev : (x :: (k₀ :: α).reverse).IsChain H.Adj := by
      have := List.isChain_reverse.mpr (hc'.imp fun _ _ h => h.symm)
      simpa using this
    exact W.mem_tri_of_chain_cons hrev hx (fun k hk => hα k (List.mem_reverse.mp hk)) k₀
      (by simp)

/-- **Two vertices of a triangle of the rib determine the third.** -/
theorem exists_tri_of_mem (W : WebData H S C R tri) {x : V} (hx : x ∈ S \ R) {u v : V}
    (hu : u ∈ tri x) (hv : v ∈ tri x) (huv : u ≠ v) :
    ∃ t, IsTriangleOn H R u v t ∧ tri x = {u, v, t} := by
  obtain ⟨a, b, c, hT, he⟩ := W.tri_spec x hx
  have key : ∀ {a' b' c' : V}, IsTriangleOn H R a' b' c' → tri x = {a', b', c'} → u = a' →
      v = b' → ∃ t, IsTriangleOn H R u v t ∧ tri x = {u, v, t} := by
    rintro a' b' c' hT' he' rfl rfl
    exact ⟨c', hT', he'⟩
  have hperm : ∀ {p q r : V}, ({p, q, r} : Set V) = {a, b, c} → tri x = {p, q, r} :=
    fun h => he.trans h.symm
  rw [he] at hu hv
  simp only [mem_insert_iff, mem_singleton_iff] at hu hv
  rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv
  · exact absurd (hu.trans hv.symm) huv
  · exact key hT he hu hv
  · exact key hT.swap₂₃ (hperm (by ext; simp only [mem_insert_iff, mem_singleton_iff]; tauto)) hu hv
  · exact key hT.swap₁₂ (hperm (by ext; simp only [mem_insert_iff, mem_singleton_iff]; tauto)) hu hv
  · exact absurd (hu.trans hv.symm) huv
  · exact key hT.swap₁₂.swap₂₃
      (hperm (by ext; simp only [mem_insert_iff, mem_singleton_iff]; tauto)) hu hv
  · exact key hT.swap₂₃.swap₁₂
      (hperm (by ext; simp only [mem_insert_iff, mem_singleton_iff]; tauto)) hu hv
  · exact key hT.swap₁₂.swap₂₃.swap₁₂
      (hperm (by ext; simp only [mem_insert_iff, mem_singleton_iff]; tauto)) hu hv
  · exact absurd (hu.trans hv.symm) huv

/-- **A stretch through one clique.** In a walk `u K v` of a web between rib vertices whose inner
vertices are clique vertices, any two distinct vertices are adjacent: `u` and `v` lie on the
triangle of the clique (`adj_of_stretch`). -/
theorem adj_of_mem_stretch (W : WebData H univ C R tri) {u v : V} {K : List V}
    (hc : (u :: K ++ [v]).IsChain H.Adj) (hnd : (u :: K ++ [v]).Nodup) (hu : u ∈ R) (hv : v ∈ R)
    (hK : ∀ k ∈ K, k ∉ R) {x x' : V} (hx : x ∈ u :: K ++ [v]) (hx' : x' ∈ u :: K ++ [v])
    (hne : x ≠ x') : H.Adj x x' := by
  have huv : u ≠ v := fun h => by subst h; simp at hnd
  obtain ⟨hadj, htri⟩ := W.adj_of_stretch hc hu hv huv hK
  have hKK : ∀ k ∈ K, ∀ k' ∈ K, k ≠ k' → H.Adj k k' := by
    intro k hk k' hk' hkk'
    rcases K with _ | ⟨k₀, K⟩
    · simp at hk
    have hcK : (k₀ :: K).IsChain H.Adj := hc.infix ⟨[u], [v], by simp⟩
    have h1 := W.tri_eq_head hcK hK k hk
    have h2 := W.tri_eq_head hcK hK k' hk'
    exact (W.adj_iff k ⟨trivial, hK k hk⟩ k').mpr
      (Or.inr ⟨⟨trivial, hK k' hk'⟩, Ne.symm hkk', h2.trans h1.symm⟩)
  have hKu : ∀ k ∈ K, ∀ z, (z = u ∨ z = v) → H.Adj k z := by
    rintro k hk z (rfl | rfl)
    · exact (W.adj_iff k ⟨trivial, hK k hk⟩ z).mpr (Or.inl (htri k hk).1)
    · exact (W.adj_iff k ⟨trivial, hK k hk⟩ z).mpr (Or.inl (htri k hk).2)
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx hx'
  rcases hx with rfl | hx | rfl <;> rcases hx' with rfl | hx' | rfl
  · exact absurd rfl hne
  · exact (hKu x' hx' _ (Or.inl rfl)).symm
  · exact hadj
  · exact hKu x hx _ (Or.inl rfl)
  · exact hKK x hx x' hx' hne
  · exact hKu x hx _ (Or.inr rfl)
  · exact hadj.symm
  · exact (hKu x' hx' _ (Or.inr rfl)).symm
  · exact absurd rfl hne

end WebData

namespace PlaneEmbedding

variable {H : SimpleGraph V} {C : List V} {R : Set V} {tri : V → Set V} {φ : PlaneEmbedding H R}
  {F₁ F₂ A₁ A₂ : Set ℂ} {l : List V} {p q : ℂ}

/-- **Step 5: where a vertex joined to `A₁` off the cut is drawn.** Let `w` be joined to an entry of
`T` by a walk of the web that misses `L`, where the entries of `T` are drawn on the open arc `A₁`
and `L` contains the cut `l`. The first rib vertex `x` of the walk is `w` or lies on the triangle of
`w` (`WebData.exists_rib_near`), and it is drawn off the closed side of `F₂`: the rib vertices of the
rest of the walk form a path of the rib from `x` to `A₁` that misses the cut (`pt_not_mem_side`). -/
theorem far_of_reachesOff (W : WebData H univ C R tri)
    (hθ : IsTheta (φ.cycleImage C) F₁ F₂ A₁ A₂ (φ.pathImage l) p q)
    (hUF : φ.U ⊆ Surface.inner (φ.cycleImage C) ∪ φ.cycleImage C) (hl : IsPathList H R l)
    {L T : List V} (hlL : ∀ v ∈ l, v ∈ L) (hT : ∀ t ∈ T, t ∈ R ∧ φ.pt t ∈ A₁ \ {p, q})
    {w : V} (hw : ReachesOff H L T w) :
    ∃ x, x ∈ R ∧ (x = w ∨ (w ∉ R ∧ x ∈ tri w)) ∧ φ.pt x ∉ Surface.inner F₂ ∪ F₂ := by
  classical
  obtain ⟨t, ht, pw, hpw⟩ := hw
  have hc : (w :: pw.support.tail).IsChain H.Adj := by
    rw [Walk.cons_tail_support]; exact pw.isChain_adj_support
  obtain ⟨α, x, β, he, hx, hxw⟩ := W.exists_rib_near hc
    ⟨t, by rw [Walk.cons_tail_support]; exact pw.end_mem_support, (hT t ht).1⟩
  have hxp : x ∈ pw.support := by rw [← Walk.cons_tail_support, he]; simp
  obtain ⟨q', hq', hq'R⟩ := W.exists_rib_path (pw.dropUntil x hxp) hx (hT t ht).1
  refine ⟨x, hx, hxw, pt_not_mem_side hθ hUF hl (isPathList_support hq' fun z hz => (hq'R z hz).1)
    (fun z hz1 hz2 => hpw z (pw.support_dropUntil_subset_support hxp (hq'R z hz1).2) (hlL z hz2))
    q'.start_mem_support q'.end_mem_support (hT t ht).2⟩

/-- **Step 8, drawing part.** Let `σ w` be an edge of the rib with `σ` off the frame, whose
triangles all lie on the side `F₂`, and let `σ K w` be a walk of the web through clique vertices. No
vertex `x` of `K w` can have a rib vertex `x'`, equal to `x` or on the triangle of `x`, drawn off the
closed side of `F₂`. If `x' = x = w`, then `w` is a vertex of a triangle at `σ w`; otherwise `x'` is
a vertex of the triangle of `x`, which is a triangle at `σ w` (`WebData.adj_of_stretch`). Either
way `x'` is drawn on the closed side of `F₂`. -/
theorem false_of_spoke (W : WebData H univ C R tri) (hφ : φ.IsRibEmbedding C)
    (hC : IsCycleList H C) (hR : ∀ x ∈ C, x ∈ R)
    (hθ : IsTheta (φ.cycleImage C) F₁ F₂ A₁ A₂ (φ.pathImage l) p q) {σ w : V} (hσC : σ ∉ C)
    (hσ : σ ∈ R) (hw : w ∈ R) (hadj : H.Adj σ w)
    (hall : ∀ x, IsTriangleOn H R σ w x →
      Surface.inner (φ.cycleImage [σ, w, x]) ⊆ Surface.inner F₂)
    {K : List V} (hc : (σ :: K ++ [w]).IsChain H.Adj) (hnd : (σ :: K ++ [w]).Nodup)
    (hK : ∀ k ∈ K, k ∉ R) {x x' : V} (hx : x ∈ K ++ [w]) (hx'R : x' ∈ R)
    (hxx' : x' = x ∨ (x ∉ R ∧ x' ∈ tri x)) (hfar : φ.pt x' ∉ Surface.inner F₂ ∪ F₂) : False := by
  have hσw : σ ≠ w := fun h => by subst h; simp at hnd
  rcases hxx' with rfl | ⟨hxR, hx'⟩
  · have hxw : x' = w := by
      rcases List.mem_append.mp hx with h | h
      · exact absurd hx'R (hK x' h)
      · exact List.mem_singleton.mp h
    subst hxw
    obtain ⟨z, -, -, hT, -, -⟩ := hφ.two_tris hC hR hσ hw hadj hσC
    exact hfar (pt_mem_side_of_tri hθ.parts₂ hT (hall z hT) (by simp))
  · have hxK : x ∈ K := by
      rcases List.mem_append.mp hx with h | h
      · exact h
      · exact absurd (List.mem_singleton.mp h ▸ hw) hxR
    obtain ⟨-, htri⟩ := W.adj_of_stretch hc hσ hw hσw hK
    obtain ⟨t, hT, he⟩ := W.exists_tri_of_mem ⟨trivial, hxR⟩ (htri x hxK).1 (htri x hxK).2 hσw
    rw [he] at hx'
    refine hfar (pt_mem_side_of_tri hθ.parts₂ hT (hall t hT) ?_)
    simp only [mem_insert_iff, mem_singleton_iff] at hx'
    rcases hx' with rfl | rfl | rfl <;> simp

/-- **Step 6: the triangle at an end.** Let `u K v` be a walk of the web through clique vertices
between two rib vertices, with `y ∈ K`, and let `y` have a neighbour `w` with a rib vertex `x`,
equal to `w` or on the triangle of `w`, drawn off the closed side of `F₁`. Then the triangle of `y`
is a triangle `u v t` whose face lies on the side `F₂`. The vertices `u`, `v` lie on the triangle of
`y` (`WebData.adj_of_stretch`), and so does `x`; the face is on one side (`tri_side`), and not on
the side `F₁`, which would put `x` on its closed side. -/
theorem end_tri (W : WebData H univ C R tri) (hφ : φ.IsRibEmbedding C) (hC : IsCycleList H C)
    (hR : ∀ x ∈ C, x ∈ R) (hθ : IsTheta (φ.cycleImage C) F₁ F₂ A₁ A₂ (φ.pathImage l) p q)
    (hl : IsPathList H R l) {u v : V} {K : List V} (hc : (u :: K ++ [v]).IsChain H.Adj)
    (hnd : (u :: K ++ [v]).Nodup) (hu : u ∈ R) (hv : v ∈ R) (hK : ∀ k ∈ K, k ∉ R) {y : V}
    (hy : y ∈ K) {w x : V} (hyw : H.Adj y w) (hxR : x ∈ R) (hxw : x = w ∨ (w ∉ R ∧ x ∈ tri w))
    (hfar : φ.pt x ∉ Surface.inner F₁ ∪ F₁) :
    ∃ t, t ∈ φ.sideTris F₂ u v ∧ tri y = {u, v, t} := by
  have huv : u ≠ v := fun h => by subst h; simp at hnd
  have hyR := hK y hy
  obtain ⟨-, htri⟩ := W.adj_of_stretch hc hu hv huv hK
  obtain ⟨t, hT, he⟩ := W.exists_tri_of_mem ⟨trivial, hyR⟩ (htri y hy).1 (htri y hy).2 huv
  have hxy : x ∈ tri y := by
    rcases hxw with rfl | ⟨hwR, hxw⟩
    · exact W.mem_tri_of_adj hyR hxR hyw
    · rcases (W.adj_iff y ⟨trivial, hyR⟩ w).mp hyw with h | ⟨-, -, h⟩
      · exact absurd (W.tri_subset ⟨trivial, hyR⟩ h) hwR
      · rw [← h]; exact hxw
  refine ⟨t, ⟨hT, ?_⟩, he⟩
  rcases hφ.tri_side hC hR hθ hl hT with h | h
  · exfalso
    rw [he] at hxy
    refine hfar (pt_mem_side_of_tri hθ.parts₁ hT h ?_)
    simp only [mem_insert_iff, mem_singleton_iff] at hxy
    rcases hxy with rfl | rfl | rfl <;> simp
  · exact h

/-- The image of a path of the rib, with the points of its vertices, joins the points of any two
of its vertices. -/
theorem joinedIn_pts {r : List V} (hr : IsPathList H R r) {u v : V} (hu : u ∈ r) (hv : v ∈ r) :
    JoinedIn (φ.pathImage r ∪ φ.pt '' {x | x ∈ r}) (φ.pt u) (φ.pt v) := by
  by_cases h2 : 2 ≤ r.length
  · exact ((φ.isPathConnected_pathImage hr h2).joinedIn _ (φ.pt_mem_pathImage hr h2 hu) _
      (φ.pt_mem_pathImage hr h2 hv)).mono subset_union_left
  · have hlen : r.length = 1 := by
      have := List.length_pos_of_mem hu
      omega
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
    rw [List.mem_singleton] at hu hv
    subst hu hv
    exact JoinedIn.refl (Or.inr ⟨_, List.mem_singleton_self _, rfl⟩)

/-- The image of a path of the rib, with the points of its vertices, misses the image of a
disjoint path. -/
theorem disjoint_pts {r r' : List V} (hr : IsPathList H R r) (hr' : IsPathList H R r')
    (hd : r.Disjoint r') : Disjoint (φ.pathImage r ∪ φ.pt '' {x | x ∈ r}) (φ.pathImage r') := by
  refine Set.disjoint_union_left.mpr ⟨φ.disjoint_pathImage hr hr' hd, ?_⟩
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ hxr
  exact hd hx (φ.mem_of_pt_mem_pathImage hr' (hr.2.2 x hx) hxr)

/-- The image of a path of the rib, with the points of its vertices, is part of the drawing. -/
theorem pts_subset_U {r : List V} (hr : IsPathList H R r) :
    φ.pathImage r ∪ φ.pt '' {x | x ∈ r} ⊆ φ.U :=
  union_subset (φ.pathImage_subset_U hr) (by rintro _ ⟨x, hx, rfl⟩; exact φ.pt_mem_U (hr.2.2 x hx))

/-- The ends of two alternating pairs of vertices of the frame alternate on its image. -/
theorem pairsCrossOn_of_alternate (φ : PlaneEmbedding H R) (hC : IsCycleList H C)
    (hR : ∀ x ∈ C, x ∈ R) {a b c d : V} (h : Alternate C a b c d) :
    PairsCrossOn (φ.cycleImage C) (φ.pt a) (φ.pt b) (φ.pt c) (φ.pt d) := by
  obtain ⟨k, L₁, L₂, hrot, hc, hd⟩ := h
  have hC' : IsCycleList H (a :: L₁ ++ b :: L₂) := by rw [← hrot]; exact hC.rotate k
  have hR' : ∀ x ∈ a :: L₁ ++ b :: L₂, x ∈ R := fun x hx =>
    hR x (List.mem_rotate.mp (by rw [hrot]; exact hx))
  have hF : φ.cycleImage C = φ.cycleImage (a :: L₁ ++ b :: L₂) := by
    rw [← hrot, φ.cycleImage_rotate]
  rw [hF]
  obtain ⟨i₁, hi₁, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨i₂, hi₂, rfl⟩ := List.getElem_of_mem hd
  have := φ.pairsCrossOn_cycleImage hC' hR' (i := 0) (r := i₁ + 1) (j := L₁.length + 1)
    (s := L₁.length + 2 + i₂) (by omega) (by omega) (by omega) (by simp; omega)
  have e1 : (a :: L₁ ++ b :: L₂)[i₁ + 1]'(by simp; omega) = L₁[i₁] := by
    simp [List.getElem_append_left hi₁]
  have e2 : (a :: L₁ ++ b :: L₂)[L₁.length + 1]'(by simp) = b := by
    simp
  have e3 : (a :: L₁ ++ b :: L₂)[L₁.length + 2 + i₂]'(by simp; omega) = L₂[i₂] := by
    simp only [show L₁.length + 2 + i₂ = (L₁.length + 1 + i₂) + 1 by omega, List.cons_append,
      List.getElem_cons_succ]
    rw [List.getElem_append_right (by omega)]
    simp [show L₁.length + 1 + i₂ - L₁.length = i₂ + 1 by omega]
  rw [e1, e2, e3] at this
  exact this

/-- **Step 9: the contradiction.** Two points `z₁`, `z₂` joined in a set `S` of the closed disc
cannot alternate on the frame with the ends `c`, `d` of a path `r` of the rib whose image misses
`S` (`Surface.disc_crossing`). -/
theorem false_of_joinedIn (hC : IsCycleList H C) (hR : ∀ x ∈ C, x ∈ R)
    (hUF : φ.U ⊆ Surface.inner (φ.cycleImage C) ∪ φ.cycleImage C) {S : Set ℂ}
    (hS : S ⊆ Surface.inner (φ.cycleImage C) ∪ φ.cycleImage C) {z₁ z₂ : ℂ} (hj : JoinedIn S z₁ z₂)
    {r : List V} (hr : IsPathList H R r) {c d : V} (hc : c ∈ r) (hd : d ∈ r) (hcd : c ≠ d)
    (hdisj : Disjoint S (φ.pathImage r))
    (hcross : PairsCrossOn (φ.cycleImage C) z₁ z₂ (φ.pt c) (φ.pt d)) : False := by
  obtain ⟨hD, hDb⟩ := isClosedDisc_closedInner (φ.isOArc_cycleImage hC hR)
  have h2 : 2 ≤ r.length := by
    rcases r with _ | ⟨x, _ | ⟨x', r⟩⟩
    · simp at hc
    · simp only [List.mem_singleton] at hc hd
      exact absurd (hc.trans hd.symm) hcd
    · simp
  rw [← hDb] at hcross
  obtain ⟨z, hzA, hzr⟩ := disc_crossing.of_isPathConnected (closedInner (φ.cycleImage C))
    (pathComponentIn S z₁) (φ.pathImage r) z₁ z₂ (φ.pt c) (φ.pt d) hD
    (pathComponentIn_subset.trans hS) ((φ.pathImage_subset_U hr).trans hUF)
    (isPathConnected_pathComponentIn hj.source_mem) (φ.isPathConnected_pathImage hr h2)
    (mem_pathComponentIn_self hj.source_mem) hj (φ.pt_mem_pathImage hr h2 hc)
    (φ.pt_mem_pathImage hr h2 hd) hcross
  exact Set.disjoint_left.mp hdisj (pathComponentIn_subset hzA) hzr

end PlaneEmbedding

end GraphMinor.HP25
