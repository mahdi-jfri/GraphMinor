module

public import GraphMinor.HP25.Link
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Proposition 2.3: wheels and fans

Humeau and Pous, arXiv:2505.16431v2, Proposition 2.3 (page 6): "Let $x$ be a vertex in a rib $R$
with frame $C$. The subgraph of $R$ induced by $x$ and $N_R(x)$ is:
- a wheel graph when $x$ is not in $C$, or
- a fan graph when $x$ is in $C$."

A wheel is a cycle plus a vertex adjacent to all its vertices, and a fan is a path plus such a
vertex. Since `x` is adjacent to all of `N_R(x)`, the statement is about the graph on `N_R(x)`: it
is a cycle (`IsRibOn.wheel`) or a path between the two neighbours of `x` on `C` (`IsRibOn.fan`). We
state "the graph on `N_R(x)` is the walk `p`" as: the vertices of `p` are the neighbours of `x`,
and two neighbours of `x` are adjacent exactly when they are consecutive on `p`.

The proof in the paper (page 7): "Each consecutive pair of edges bounds a common face ... Either all
such faces are inner, meaning are triangles, and $H$ is a wheel graph ..., or some of these faces are
the outer face. The outer face being bounded by a cycle $C$, at most two edges incident to $x$ may
bound the outer face. In this case $x$ is in $C$ and $H$ is a fan graph."

We follow it without the cyclic order of the edges at `x`. The link graph of `x` has an edge `ab`
when `xab` is a triangle. A neighbour `a` of `x` has two neighbours in the link graph, or one when
`xa` is an edge of the frame: the triangles at `xa` are the bounded faces at `xa`
(`IsRibEmbedding.common_neighbours`). The link graph is connected (`IsRibEmbedding.link_closed`).
So it is a cycle when `x` is not on `C`. When `x` is on `C`, adding the edge between the two
neighbours `d`, `d'` of `x` on `C` gives a cycle through `dd'`, so `d` and `d'` are joined in the
link graph, and the link graph is a path from `d` to `d'`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface PlaneEmbedding

variable {V : Type*} {G : SimpleGraph V} {R : Set V} {C : List V}

/-! ### The two neighbours of a vertex on a cycle -/

theorem isCycleEdge_rotate (C : List V) (k : ℕ) (x a : V) :
    IsCycleEdge (C.rotate k) x a ↔ IsCycleEdge C x a := by
  unfold IsCycleEdge
  rw [zip_rotate_rotate]
  simp only [List.mem_rotate]

theorem PlaneEmbedding.IsCycleEdge.mem_left {x a : V} (h : IsCycleEdge C x a) : x ∈ C := by
  obtain ⟨p, hp, he⟩ := h
  have h1 := List.of_mem_zip hp
  rcases Sym2.eq_iff.mp he with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact h1.1
  · exact List.mem_rotate.mp h1.2

theorem PlaneEmbedding.IsCycleEdge.symm {x a : V} (h : IsCycleEdge C x a) : IsCycleEdge C a x := by
  obtain ⟨p, hp, he⟩ := h
  exact ⟨p, hp, by rw [Sym2.eq_swap]; exact he⟩

theorem PlaneEmbedding.IsCycleEdge.adj {x a : V} (hC : IsCycleList G C) (h : IsCycleEdge C x a) : G.Adj x a := by
  obtain ⟨p, hp, he⟩ := h
  have := hC.2.2 p hp
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact this
  · exact this.symm

/-- A vertex `x` of the cycle `x :: t` has two neighbours on it: the first and the last entries of
`t`. -/
theorem IsCycleList.frame_neighbours_cons {x : V} {t : List V} (hC : IsCycleList G (x :: t)) :
    ∃ d d', d ≠ d' ∧ IsCycleEdge (x :: t) x d ∧ IsCycleEdge (x :: t) x d' ∧
      ∀ a, IsCycleEdge (x :: t) x a → a = d ∨ a = d' := by
  obtain ⟨h3, hnd, -⟩ := hC
  have hn : 2 ≤ t.length := by simp at h3; omega
  have hrot : (x :: t).rotate 1 = t ++ [x] := by simp
  have hnd' : (t ++ [x]).Nodup := by
    rw [List.nodup_append_comm]
    exact hnd
  have hlen : (x :: t).length = (t ++ [x]).length := by simp
  have h0 : 0 < t.length := by omega
  have hl : t.length - 1 < t.length := by omega
  refine ⟨t[0], t[t.length - 1], fun h => ?_, ?_, ?_, ?_⟩
  · have := (List.Nodup.getElem_inj_iff (List.nodup_cons.mp hnd).2).mp h
    omega
  · refine ⟨(x, t[0]), ?_, rfl⟩
    rw [hrot]
    have hi : 0 < ((x :: t).zip (t ++ [x])).length := by simp
    have := List.getElem_mem hi
    simpa [List.getElem_zip, List.getElem_append_left h0] using this
  · refine ⟨(t[t.length - 1], x), ?_, Sym2.eq_swap⟩
    rw [hrot]
    have hi : t.length < ((x :: t).zip (t ++ [x])).length := by simp
    have := List.getElem_mem hi
    have e1 : (x :: t)[t.length]'(by simp) = t[t.length - 1] := by
      simp [List.getElem_cons, show t.length ≠ 0 by omega]
    simpa [List.getElem_zip, e1] using this
  · rintro a ⟨p, hp, he⟩
    rw [hrot] at hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    rw [List.getElem_zip] at he
    have hi1 : i < (x :: t).length := by simp at hi ⊢; omega
    have hi2 : i < (t ++ [x]).length := by simp at hi ⊢; omega
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- `x` is the first entry of the pair
      have hx0 : (x :: t)[0] = (x :: t)[i] := by simpa using h1
      have := (List.Nodup.getElem_inj_iff hnd).mp hx0
      subst this
      left
      rw [h2]
      simp [List.getElem_append_left h0]
    · -- `x` is the second entry of the pair
      have hxl : (t ++ [x])[t.length]'(by simp) = (t ++ [x])[i] := by simpa using h1
      have := (List.Nodup.getElem_inj_iff hnd').mp hxl
      subst this
      right
      rw [h2]
      simp [List.getElem_cons, show t.length ≠ 0 by omega]

/-- A vertex of a cycle has two neighbours on it, and all its cycle edges go to them. -/
theorem IsCycleList.frame_neighbours (hC : IsCycleList G C) {x : V} (hx : x ∈ C) :
    ∃ d d', d ≠ d' ∧ IsCycleEdge C x d ∧ IsCycleEdge C x d' ∧
      ∀ a, IsCycleEdge C x a → a = d ∨ a = d' := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx
  have hrot : (l₁ ++ x :: l₂).rotate l₁.length = x :: (l₂ ++ l₁) :=
    List.rotate_append_length_eq l₁ (x :: l₂) |>.trans (by simp)
  have hC' := hC.rotate l₁.length
  rw [hrot] at hC'
  obtain ⟨d, d', hne, hd, hd', hall⟩ := hC'.frame_neighbours_cons
  simp only [← hrot, isCycleEdge_rotate] at hd hd' hall
  exact ⟨d, d', hne, hd, hd', hall⟩

/-- In a cycle `x :: t` of length at least four, the first and last entries of `t` are not
consecutive. -/
theorem IsCycleList.not_isCycleEdge_ends_cons {x : V} {t : List V} (hC : IsCycleList G (x :: t))
    (h4 : 4 ≤ (x :: t).length) (h0 : 0 < t.length) :
    ¬ IsCycleEdge (x :: t) t[0] (t[t.length - 1]'(by omega)) := by
  obtain ⟨-, hnd, -⟩ := hC
  have hn : 3 ≤ t.length := by simp at h4; omega
  have hrot : (x :: t).rotate 1 = t ++ [x] := by simp
  have hnd' : (t ++ [x]).Nodup := by
    rw [List.nodup_append_comm]
    exact hnd
  rintro ⟨p, hp, he⟩
  rw [hrot] at hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  rw [List.getElem_zip] at he
  have hi1 : i < (x :: t).length := by simp at hi ⊢; omega
  have hi2 : i < (t ++ [x]).length := by simp at hi ⊢; omega
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : (x :: t)[1]'(by simp; omega) = (x :: t)[i] := by simpa using h1
    have := (List.Nodup.getElem_inj_iff hnd).mp e1
    subst this
    have e2 : (t ++ [x])[t.length - 1]'(by simp) = (t ++ [x])[1]'(by simp; omega) := by
      simpa [List.getElem_append_left (show t.length - 1 < t.length by omega),
        List.getElem_append_left (show 1 < t.length by omega)] using h2
    have := (List.Nodup.getElem_inj_iff hnd').mp e2
    omega
  · have e1 : (x :: t)[t.length]'(by simp) = (x :: t)[i] := by
      simpa [List.getElem_cons, show t.length ≠ 0 by omega] using h2
    have := (List.Nodup.getElem_inj_iff hnd).mp e1
    subst this
    have e2 : (t ++ [x])[0]'(by simp) = (t ++ [x])[t.length]'(by simp) := by
      simpa [List.getElem_append_left h0] using h1
    have := (List.Nodup.getElem_inj_iff hnd').mp e2
    omega

/-- In a cycle of length at least four, the two neighbours of a vertex are not consecutive. -/
theorem IsCycleList.not_isCycleEdge_frame_neighbours (hC : IsCycleList G C) (h4 : 4 ≤ C.length)
    {x d d' : V} (hne : d ≠ d') (hd : IsCycleEdge C x d) (hd' : IsCycleEdge C x d') :
    ¬ IsCycleEdge C d d' := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hd.mem_left
  have hrot : (l₁ ++ x :: l₂).rotate l₁.length = x :: (l₂ ++ l₁) :=
    List.rotate_append_length_eq l₁ (x :: l₂) |>.trans (by simp)
  have hC' := hC.rotate l₁.length
  rw [hrot] at hC'
  rw [← isCycleEdge_rotate _ l₁.length, hrot] at hd hd' ⊢
  set t := l₂ ++ l₁
  have h4' : 4 ≤ (x :: t).length := by
    rw [← hrot, List.length_rotate]; exact h4
  have h0 : 0 < t.length := by simp at h4'; omega
  have hends := hC'.not_isCycleEdge_ends_cons h4' h0
  obtain ⟨-, hnd, -⟩ := hC'
  -- the neighbours of `x` on `x :: t` are the ends of `t`
  have hall : ∀ a, IsCycleEdge (x :: t) x a → a = t[0] ∨ a = t[t.length - 1]'(by omega) := by
    rintro a ⟨p, hp, he⟩
    have hrot1 : (x :: t).rotate 1 = t ++ [x] := by simp
    have hnd' : (t ++ [x]).Nodup := by
      rw [List.nodup_append_comm]
      exact hnd
    rw [hrot1] at hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    rw [List.getElem_zip] at he
    have hi1 : i < (x :: t).length := by simp at hi ⊢; omega
    have hi2 : i < (t ++ [x]).length := by simp at hi ⊢; omega
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hx0 : (x :: t)[0] = (x :: t)[i] := by simpa using h1
      have := (List.Nodup.getElem_inj_iff hnd).mp hx0
      subst this
      left
      rw [h2]
      simp [List.getElem_append_left h0]
    · have hxl : (t ++ [x])[t.length]'(by simp) = (t ++ [x])[i] := by simpa using h1
      have := (List.Nodup.getElem_inj_iff hnd').mp hxl
      subst this
      right
      rw [h2]
      simp [List.getElem_cons, show t.length ≠ 0 by omega]
  intro hdd
  rcases hall d hd with rfl | rfl <;> rcases hall d' hd' with rfl | rfl
  · exact hne rfl
  · exact hends hdd
  · exact hends hdd.symm
  · exact hne rfl

/-! ### The link graph -/

/-- The link graph of `x`, on the vertices of `R`: `a` and `b` are adjacent when `x a b` is a
triangle. -/
@[expose] def linkGraph (G : SimpleGraph V) (R : Set V) (x : V) : SimpleGraph R where
  Adj a b := G.Adj x a ∧ G.Adj x b ∧ G.Adj a b
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.2.2⟩

/-- The link graph maps into `G`. -/
@[expose] def linkHom (G : SimpleGraph V) (R : Set V) (x : V) : linkGraph G R x →g G where
  toFun := Subtype.val
  map_rel' h := h.2.2

@[simp] theorem linkHom_apply (x : V) (a : R) : linkHom G R x a = a.1 := rfl

/-- A set of vertices closed under adjacency contains every vertex of a walk that starts in it. -/
theorem mem_of_walk {W : Type*} {H : SimpleGraph W} {S : Set W}
    (hS : ∀ b ∈ S, ∀ c, H.Adj b c → c ∈ S) :
    ∀ {u v : W} (w : H.Walk u v), u ∈ S → ∀ b ∈ w.support, b ∈ S
  | _, _, .nil, hu, b, hb => by simp at hb; exact hb ▸ hu
  | _, _, .cons h p, hu, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hu
    · exact mem_of_walk hS p (hS _ hu _ h) b hb

/-- A neighbour set inside another one of at most the same finite size is equal to it. -/
theorem nbr_eq {W : Type*} {s t : Set W} (hst : s ⊆ t) (ht : t.Finite) (hs : t.ncard ≤ s.ncard) :
    s = t :=
  Set.eq_of_subset_of_ncard_le hst hs ht

section Rib

variable {φ : PlaneEmbedding G R} (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
  (hR : ∀ x ∈ C, x ∈ R)
include hφ hC hR

omit hφ hC hR in
/-- The neighbours of a neighbour `a` of `x` in the link graph of `x` are the common neighbours of
`x` and `a`. -/
theorem linkGraph_neighborSet {x : V} (a : R) (hxa : G.Adj x a) :
    (linkGraph G R x).neighborSet a = Subtype.val ⁻¹' {z | z ∈ R ∧ G.Adj x z ∧ G.Adj a z} := by
  ext b
  simp only [mem_neighborSet, linkGraph, mem_preimage, mem_ofPred_eq]
  exact ⟨fun h => ⟨b.2, h.2.1, h.2.2⟩, fun h => ⟨hxa, h.2.1, h.2.2⟩⟩

omit hφ hC hR in
theorem encard_val_preimage (S : Set V) (hS : S ⊆ R) :
    (Subtype.val ⁻¹' S : Set R).encard = S.encard :=
  encard_preimage_of_injective_subset_range Subtype.val_injective (by rwa [Subtype.range_coe])

/-- In the link graph, a neighbour `a` of `x` with `xa` off the frame has two neighbours. -/
theorem link_ncard_two {x : V} (hx : x ∈ R) (a : R) (hxa : G.Adj x a)
    (haC : ¬ IsCycleEdge C x a) : ((linkGraph G R x).neighborSet a).ncard = 2 := by
  obtain ⟨hle, -, htwo⟩ := hφ.common_neighbours hC hR hx a.2 hxa
  obtain ⟨z₁, z₂, hne, hz₁, hz₂⟩ := htwo haC
  rw [linkGraph_neighborSet a hxa, Set.ncard_def, encard_val_preimage _ (fun z hz => hz.1)]
  have h2 : 2 ≤ {z | z ∈ R ∧ G.Adj x z ∧ G.Adj a z}.encard := by
    rw [← encard_pair hne]
    exact encard_le_encard (by rintro z (rfl | rfl) <;> assumption)
  rw [le_antisymm hle h2]
  rfl

/-- In the link graph, every vertex has at most two neighbours. -/
theorem link_ncard_le {x : V} (hx : x ∈ R) (a : R) :
    ((linkGraph G R x).neighborSet a).encard ≤ 2 := by
  by_cases hxa : G.Adj x a
  · rw [linkGraph_neighborSet a hxa, encard_val_preimage _ (fun z hz => hz.1)]
    exact (hφ.common_neighbours hC hR hx a.2 hxa).1
  · have : (linkGraph G R x).neighborSet a = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun b hb => hxa hb.1
    rw [this]
    simp

/-- In the link graph, a neighbour `a` of `x` with `xa` on the frame has one neighbour. -/
theorem link_frame {x : V} (hx : x ∈ R) (a : R) (hxa : G.Adj x a) (haC : IsCycleEdge C x a) :
    ((linkGraph G R x).neighborSet a).Subsingleton ∧
      ((linkGraph G R x).neighborSet a).Nonempty := by
  obtain ⟨-, hone, -⟩ := hφ.common_neighbours hC hR hx a.2 hxa
  obtain ⟨hle, z, hz⟩ := hone haC
  rw [linkGraph_neighborSet a hxa]
  refine ⟨?_, ⟨⟨z, hz.1⟩, hz⟩⟩
  rw [← encard_le_one_iff_subsingleton, encard_val_preimage _ (fun z hz => hz.1)]
  exact hle

end Rib

/-- The vertices and edges of `p.map (linkHom G R x)`. -/
theorem link_map_spec {x : V} {a b : R} (p : (linkGraph G R x).Walk a b)
    (hsupp : ∀ v : R, v ∈ p.support ↔ G.Adj x v)
    (hsat : ∀ u ∈ p.support, ∀ v, (linkGraph G R x).Adj u v → s(u, v) ∈ p.edges) :
    (∀ v, v ∈ (p.map (linkHom G R x)).support ↔ v ∈ R ∧ G.Adj x v) ∧
      ∀ u v, u ∈ R → G.Adj x u → v ∈ R → G.Adj x v →
        (G.Adj u v ↔ s(u, v) ∈ (p.map (linkHom G R x)).edges) := by
  refine ⟨fun v => ?_, fun u v hu hxu hv hxv => ⟨fun huv => ?_, fun h => ?_⟩⟩
  · rw [Walk.support_map, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, (hsupp w).mp hw⟩
    · rintro ⟨hv, hxv⟩
      exact ⟨⟨v, hv⟩, (hsupp _).mpr hxv, rfl⟩
  · rw [Walk.edges_map]
    have := List.mem_map_of_mem (f := Sym2.map (linkHom G R x))
      (hsat ⟨u, hu⟩ ((hsupp _).mpr hxu) ⟨v, hv⟩ ⟨hxu, hxv, huv⟩)
    simpa using this
  · exact (p.map (linkHom G R x)).adj_of_mem_edges h

/-- **Proposition 2.3, wheel case.** For a vertex `x` of a rib off the frame, the graph on the
neighbours of `x` is a cycle: there is a cycle `p` whose vertices are the neighbours of `x`, and two
neighbours of `x` are adjacent exactly when they are consecutive on `p`. -/
theorem IsRibOn.wheel (h : IsRibOn G R C) {x : V} (hx : x ∈ R) (hxC : x ∉ C) :
    ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ (∀ v, v ∈ p.support ↔ v ∈ R ∧ G.Adj x v) ∧
      ∀ u v, u ∈ R → G.Adj x u → v ∈ R → G.Adj x v → (G.Adj u v ↔ s(u, v) ∈ p.edges) := by
  classical
  obtain ⟨hC, hR, φ, hφ⟩ := h
  have : Finite R := φ.finite.to_subtype
  set L := linkGraph G R x with hL
  have hnC : ∀ a, ¬ IsCycleEdge C x a := fun a ha => hxC ha.mem_left
  have hcyc : L.IsCycles := fun a ⟨b, hb⟩ => link_ncard_two hφ hC hR hx a hb.1 (hnC a)
  obtain ⟨a₀, ha₀R, hxa₀⟩ := hφ.exists_adj hC hR hx
  set A₀ : R := ⟨a₀, ha₀R⟩
  -- every neighbour of `x` is reachable from `a₀` in the link graph
  have hreach : ∀ v (hv : v ∈ R), G.Adj x v → L.Reachable A₀ ⟨v, hv⟩ := by
    intro v hv hxv
    obtain ⟨_, _, hr⟩ := hφ.link_closed hC hR hx
      (K := {b | ∃ hb : b ∈ R, G.Adj x b ∧ L.Reachable A₀ ⟨b, hb⟩})
      (fun b ⟨hb, hxb, _⟩ => ⟨hb, hxb⟩) ⟨a₀, ha₀R, hxa₀, Reachable.refl _⟩
      (fun b ⟨hb, hxb, hr⟩ c hc hxc hbc => ⟨hc, hxc, hr.trans (Adj.reachable ⟨hxb, hxc, hbc⟩)⟩)
      (fun b _ => hnC b) hv hxv
    exact hr
  have hxL : ∀ b : R, L.Reachable A₀ b → G.Adj x b := by
    rintro b ⟨w⟩
    exact mem_of_walk (H := L) (S := {b : R | G.Adj x b}) (fun b _ c h => h.2.1) w hxa₀ b w.end_mem_support
  have hnb : (L.neighborSet A₀).Nonempty := Set.nonempty_of_ncard_ne_zero (by
    rw [link_ncard_two hφ hC hR hx A₀ hxa₀ (hnC a₀)]; norm_num)
  obtain ⟨p, hp, hpv⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := L.connectedComponentMk A₀) rfl hnb
  have hsupp : ∀ v : R, v ∈ p.support ↔ G.Adj x v := by
    intro v
    rw [← Walk.mem_verts_toSubgraph, hpv, ConnectedComponent.mem_supp_iff,
      ConnectedComponent.eq]
    exact ⟨fun h => hxL v h.symm, fun h => (hreach v v.2 h).symm⟩
  have hsat : ∀ u ∈ p.support, ∀ v, L.Adj u v → s(u, v) ∈ p.edges := by
    intro u hu v huv
    have heq := nbr_eq (p.toSubgraph.neighborSet_subset u) (toFinite _) (by
      rw [hp.ncard_neighborSet_toSubgraph_eq_two hu, link_ncard_two hφ hC hR hx u huv.1 (hnC u)])
    have : v ∈ p.toSubgraph.neighborSet u := heq ▸ huv
    exact Walk.adj_toSubgraph_iff_mem_edges.mp this
  exact ⟨_, p.map (linkHom G R x), hp.map Subtype.val_injective, link_map_spec p hsupp hsat⟩

/-- **Proposition 2.3, fan case.** For a vertex `x` of the frame `C` of a rib, with neighbours `d`
and `d'` on `C`, the graph on the neighbours of `x` is a path from `d` to `d'`: there is a path `p`
from `d` to `d'` whose vertices are the neighbours of `x`, and two neighbours of `x` are adjacent
exactly when they are consecutive on `p`. -/
theorem IsRibOn.fan (h : IsRibOn G R C) {x d d' : V} (hne : d ≠ d') (hd : IsCycleEdge C x d)
    (hd' : IsCycleEdge C x d') :
    ∃ p : G.Walk d d', p.IsPath ∧ (∀ v, v ∈ p.support ↔ v ∈ R ∧ G.Adj x v) ∧
      ∀ u v, u ∈ R → G.Adj x u → v ∈ R → G.Adj x v → (G.Adj u v ↔ s(u, v) ∈ p.edges) := by
  classical
  obtain ⟨hC, hR, φ, hφ⟩ := h
  have : Finite R := φ.finite.to_subtype
  have hxC := hd.mem_left
  have hx := hR x hxC
  have hdR : d ∈ R := hR d hd.symm.mem_left
  have hd'R : d' ∈ R := hR d' hd'.symm.mem_left
  have hxd := hd.adj hC
  have hxd' := hd'.adj hC
  set L := linkGraph G R x with hL
  set D : R := ⟨d, hdR⟩ with hD
  set D' : R := ⟨d', hd'R⟩ with hD'
  have hDD : D ≠ D' := fun h => hne (congrArg Subtype.val h)
  -- the frame edges at `x` go to `d` and `d'`
  have hframe : ∀ a, IsCycleEdge C x a → a = d ∨ a = d' := by
    obtain ⟨e, e', hee, -, -, hall⟩ := hC.frame_neighbours hxC
    intro a ha
    rcases hall a ha with h1 | h1 <;> rcases hall d hd with h2 | h2 <;>
      rcases hall d' hd' with h3 | h3
    all_goals first
      | exact Or.inl (h1.trans h2.symm)
      | exact Or.inr (h1.trans h3.symm)
      | exact absurd (h2.trans h3.symm) hne
  have hframe' : ∀ b : R, IsCycleEdge C x b → b = D ∨ b = D' := fun b hb =>
    (hframe b hb).imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)
  have hxL : ∀ b : R, L.Reachable D b → G.Adj x b := by
    rintro b ⟨w⟩
    exact mem_of_walk (H := L) (S := {b : R | G.Adj x b}) (fun b _ c h => h.2.1) w hxd b w.end_mem_support
  -- `d` and `d'` are joined in the link graph
  have hDD' : L.Reachable D D' := by
    by_cases hG : G.Adj d d'
    · exact Adj.reachable ⟨hxd, hxd', hG⟩
    obtain ⟨hsD, e, he⟩ := link_frame hφ hC hR hx D hxd hd
    obtain ⟨hsD', e', he'⟩ := link_frame hφ hC hR hx D' hxd' hd'
    have hLD : L.neighborSet D = {e} := hsD.eq_singleton_of_mem he
    have hLD' : L.neighborSet D' = {e'} := hsD'.eq_singleton_of_mem he'
    have heD' : e ≠ D' := by
      rintro rfl
      exact hG he.2.2
    have heD : e' ≠ D := by
      rintro rfl
      exact hG he'.2.2.symm
    set H := L ⊔ edge D D' with hH
    have hEn : ∀ v, (edge D D').neighborSet v =
        (if v = D then {D'} else if v = D' then {D} else ∅) := by
      intro v
      ext w
      simp only [mem_neighborSet, edge_adj]
      split_ifs with h1 h2
      · subst h1; simp only [mem_singleton_iff]
        constructor
        · rintro ⟨(⟨-, rfl⟩ | ⟨h, -⟩), -⟩
          · rfl
          · exact absurd h hDD
        · rintro rfl; simp [hDD]
      · subst h2; simp only [mem_singleton_iff]
        constructor
        · rintro ⟨(⟨h, -⟩ | ⟨-, rfl⟩), -⟩
          · exact absurd h.symm hDD
          · rfl
        · rintro rfl; simpa [hDD] using h1
      · simp only [mem_empty_iff_false, iff_false]
        rintro ⟨(⟨rfl, -⟩ | ⟨rfl, -⟩), -⟩
        · exact h1 rfl
        · exact h2 rfl
    have hHD : H.neighborSet D = {e, D'} := by
      rw [hH, neighborSet_sup, hLD, hEn, ite_eq_left rfl]; rfl
    have hcyc : H.IsCycles := by
      intro v hv
      rw [hH, neighborSet_sup, hEn] at hv ⊢
      by_cases h1 : v = D
      · subst h1
        rw [ite_eq_left rfl, hLD]
        exact ncard_pair heD'
      · by_cases h2 : v = D'
        · subst h2
          rw [ite_eq_right h1, ite_eq_left rfl, hLD', show ({e'} ∪ {D} : Set R) = {e', D} from rfl]
          exact ncard_pair heD
        · rw [ite_eq_right h1, ite_eq_right h2, union_empty] at hv ⊢
          obtain ⟨b, hb⟩ := hv
          have hxv : G.Adj x v := hb.1
          refine link_ncard_two hφ hC hR hx v hxv fun hvC => ?_
          rcases hframe' v hvC with h | h
          · exact h1 h
          · exact h2 h
    have hDnb : (H.neighborSet D).Nonempty := ⟨D', by rw [hHD]; exact Or.inr rfl⟩
    obtain ⟨p, hp, -⟩ := hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := H.connectedComponentMk D) rfl hDnb
    have hDp : D ∈ p.support := p.start_mem_support
    have heq := nbr_eq (p.toSubgraph.neighborSet_subset D) (toFinite _) (by
      rw [hp.ncard_neighborSet_toSubgraph_eq_two hDp, hcyc hDnb])
    have hmem : s(D, D') ∈ p.edges := by
      have : D' ∈ p.toSubgraph.neighborSet D := by rw [heq, hHD]; exact Or.inr rfl
      exact Walk.adj_toSubgraph_iff_mem_edges.mp this
    have hr := (adj_and_reachable_delete_edges_iff_exists_cycle.mpr ⟨D, p, hp, hmem⟩).2
    refine hr.mono fun a b hab => ?_
    rw [deleteEdges_adj, hH, sup_adj, edge_adj] at hab
    rcases hab with ⟨h | ⟨h, -⟩, hn⟩
    · exact h
    · refine absurd ?_ hn
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
  -- every neighbour of `x` is reachable from `d` in the link graph
  have hreach : ∀ v (hv : v ∈ R), G.Adj x v → L.Reachable D ⟨v, hv⟩ := by
    intro v hv hxv
    by_contra hnr
    obtain ⟨_, _, hr⟩ := hφ.link_closed hC hR hx
      (K := {b | ∃ hb : b ∈ R, G.Adj x b ∧ L.Reachable ⟨v, hv⟩ ⟨b, hb⟩})
      (fun b ⟨hb, hxb, _⟩ => ⟨hb, hxb⟩) ⟨v, hv, hxv, Reachable.refl _⟩
      (fun b ⟨hb, hxb, hr⟩ c hc hxc hbc => ⟨hc, hxc, hr.trans (Adj.reachable ⟨hxb, hxc, hbc⟩)⟩)
      (fun b ⟨hb, hxb, hr⟩ hbC => by
        rcases hframe' ⟨b, hb⟩ hbC with h | h
        · rw [h] at hr; exact hnr hr.symm
        · rw [h] at hr; exact hnr (hDD'.trans hr.symm))
      hdR hxd
    exact hnr hr.symm
  -- a path from `d` to `d'` in the link graph
  obtain ⟨w⟩ := hDD'
  set P := w.toPath with hP
  have hPp : P.1.IsPath := P.2
  have hnil : ¬ P.1.Nil := Walk.not_nil_of_ne hDD
  have hsat : ∀ u ∈ P.1.support, ∀ v, L.Adj u v → s(u, v) ∈ P.1.edges := by
    intro u hu v huv
    rw [← Walk.adj_toSubgraph_iff_mem_edges]
    by_cases h1 : u = D
    · subst h1
      have hs := hPp.neighborSet_toSubgraph_startpoint hnil
      have hsnd : P.1.snd ∈ L.neighborSet D :=
        P.1.toSubgraph.neighborSet_subset D (by rw [hs]; rfl)
      have := (link_frame hφ hC hR hx D hxd hd).1 huv hsnd
      show v ∈ P.1.toSubgraph.neighborSet D
      rw [hs, this]; rfl
    · by_cases h2 : u = D'
      · subst h2
        have hs := hPp.neighborSet_toSubgraph_endpoint hnil
        have hpen : P.1.penultimate ∈ L.neighborSet D' :=
          P.1.toSubgraph.neighborSet_subset D' (by rw [hs]; rfl)
        have := (link_frame hφ hC hR hx D' hxd' hd').1 huv hpen
        show v ∈ P.1.toSubgraph.neighborSet D'
        rw [hs, this]; rfl
      · obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hu
        have hi0 : i ≠ 0 := by rintro rfl; exact h1 P.1.getVert_zero
        have hil : i < P.1.length := lt_of_le_of_ne hi (by rintro rfl; exact h2 P.1.getVert_length)
        have hnC : ¬ IsCycleEdge C x (P.1.getVert i) := fun hC' => by
          rcases hframe' _ hC' with h | h
          · exact h1 h
          · exact h2 h
        have heq := nbr_eq (P.1.toSubgraph.neighborSet_subset _) (toFinite _) (by
          rw [hPp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hil,
            link_ncard_two hφ hC hR hx _ huv.1 hnC])
        show v ∈ P.1.toSubgraph.neighborSet _
        rw [heq]; exact huv
  have hsupp : ∀ v : R, v ∈ P.1.support ↔ G.Adj x v := by
    intro v
    constructor
    · intro hv
      exact mem_of_walk (H := L) (S := {b : R | G.Adj x b}) (fun b _ c h => h.2.1) P.1 hxd v hv
    · intro hxv
      obtain ⟨u⟩ := hreach v v.2 hxv
      refine mem_of_walk (H := L) (S := {b : R | b ∈ P.1.support}) (fun b hb c hbc => ?_) u
        P.1.start_mem_support v u.end_mem_support
      have := hsat b hb c hbc
      exact P.1.snd_mem_support_of_mem_edges this
  exact ⟨P.1.map (linkHom G R x), hPp.map Subtype.val_injective, link_map_spec P.1 hsupp hsat⟩

end GraphMinor.HP25
