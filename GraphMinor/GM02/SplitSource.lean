module

public import GraphMinor.GM02.VertexSplit

/-!
# Contracting branch trees gives a split

This file does the last step of II (4.8). We start from a graph `J` with a
model `ν` of `H` in which every edge that does not represent an edge of `H`
lies inside one branch set, and each branch set `ν u` has fewer such edges
than vertices. So each branch set spans a tree. We also ask that every vertex
in a branch set with at least two vertices has valency at least three
(`IsSplitSource H J ν ηe 3`).

Then `J` is a split of `H` (`isSplitOf_of_isSplitSource`). If some branch set
has two vertices, it has an edge `f` with two distinct ends, and both ends
have valency at least three. Contracting `f` gives a graph of the same kind
with one vertex fewer (`IsSplitSource.merge`), and `J` comes from it by one
split. If every branch set is a single vertex, then every edge of `J`
represents an edge of `H`, and `J` is isomorphic to `H`.

The weaker condition `IsSplitSource H J ν ηe 2` is the one that the earlier
steps of (4.8) produce and keep.
-/

@[expose] public section

namespace GraphMinor.GM02

open Graph Set Classical

universe u v u' v'

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}

/-- The edges of `J` that do not represent an edge of `H` and have all their
ends in the branch set `ν u`. -/
def branchEdges (H : Graph α' β') (J : Graph α β) (ν : α' → Set α) (ηe : β' → β)
    (u : α') : Set β :=
  {e | e ∈ E(J) ∧ e ∉ ηe '' E(H) ∧ ∀ x, J.Inc e x → x ∈ ν u}

/-- A model `ν` of `H` in `J` whose branch sets cover `J` and span trees, and
whose other edges lie inside branch sets. Every vertex in a branch set with
at least two vertices has valency at least `k`. -/
structure IsSplitSource (H : Graph α' β') (J : Graph α β) (ν : α' → Set α)
    (ηe : β' → β) (k : ℕ) : Prop where
  model : IsMinorModel H J ν ηe
  cover : ∀ x ∈ V(J), ∃ u ∈ V(H), x ∈ ν u
  internal : ∀ e ∈ E(J), e ∉ ηe '' E(H) → ∃ u ∈ V(H), ∀ x, J.Inc e x → x ∈ ν u
  count : ∀ u ∈ V(H), (branchEdges H J ν ηe u).ncard + 1 ≤ (ν u).ncard
  high : ∀ u ∈ V(H), ∀ x ∈ ν u, 2 ≤ (ν u).ncard → k ≤ valency J x

/-- A walk between two distinct vertices has a first step to a different
vertex. -/
theorem exists_step_ne_of_reflTransGen {γ : Type*} {r : γ → γ → Prop} {a b : γ}
    (h : Relation.ReflTransGen r a b) (hab : a ≠ b) : ∃ c, r a c ∧ a ≠ c := by
  induction h with
  | refl => exact absurd rfl hab
  | @tail c d _ hcd ih =>
    by_cases hc : a = c
    · subst hc
      exact ⟨d, hcd, hab⟩
    · exact ih hc

/-- A branch set of a model with two vertices has an edge with two distinct
ends in it that does not represent an edge of `H`. It comes from the first
step of a walk inside the branch set between two of its vertices. -/
theorem IsMinorModel.exists_branch_edge {H : Graph α' β'} {J : Graph α β}
    {ν : α' → Set α} {ηe : β' → β} (hm : IsMinorModel H J ν ηe) {u : α'}
    (hu : u ∈ V(H)) (hfin : (ν u).Finite) (h2 : 2 ≤ (ν u).ncard) :
    ∃ f c c', J.IsLink f c c' ∧ c ≠ c' ∧ f ∉ ηe '' E(H) ∧ c ∈ ν u ∧ c' ∈ ν u := by
  obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff hfin).1 (by omega)
  obtain ⟨K, hK, hKv, hconn⟩ := hm.connected u hu
  obtain ⟨c, ⟨f, hf⟩, hac⟩ :=
    exists_step_ne_of_reflTransGen (hconn.2 a (hKv ▸ ha) b (hKv ▸ hb)) hab
  have hG := hK.isLink_mono hf
  rw [deleteEdges_isLink] at hG
  exact ⟨f, a, c, hG.1, hac, hG.2, ha, hKv ▸ hf.right_mem⟩

section Merge

variable {H : Graph α' β'} {J : Graph α β} {ν : α' → Set α} {ηe : β' → β}

/-- Contracting an edge inside a branch set keeps the conditions of
`IsSplitSource` with bound three. The branch set loses the second end of the
edge, and the first end has valency `d(c) + d(c') - 2 ≥ 4`. -/
theorem IsSplitSource.merge (hs : IsSplitSource H J ν ηe 3)
    (hVJ : V(J).Finite) (hEJ : E(J).Finite) {u : α'} (hu : u ∈ V(H))
    {f : β} {c c' : α} (hf : J.IsLink f c c') (hcc : c ≠ c')
    (hfF : f ∉ ηe '' E(H)) (hc : c ∈ ν u) (hc' : c' ∈ ν u) :
    IsSplitSource H (mergeEdge J f c c') (fun w => ν w \ {c'}) ηe 3 := by
  have hm := hs.model
  have hVM : V((mergeEdge J f c c')) = V(J) \ {c'} := mergeEdge_vertexSet hf hcc
  have hEM : E((mergeEdge J f c c')) = E(J) \ {f} := mergeEdge_edgeSet J f c c'
  -- A vertex of `ν u` lies in no other branch set.
  have honly : ∀ w ∈ V(H), ∀ y ∈ ν u, y ∈ ν w → w = u := by
    intro w hw y hy hyw
    by_contra hne
    exact Set.disjoint_left.1 (hm.vertex_disjoint w hw u hu hne) hyw hy
  -- The contraction map sends `ν w` into `ν w \ {c'}`, and nothing else.
  have hmap : ∀ w ∈ V(H), ∀ y, mergeMap c c' y ∈ ν w \ {c'} ↔ y ∈ ν w := by
    intro w hw y
    by_cases hy : y = c'
    · subst hy
      rw [mergeMap_right]
      constructor
      · intro h
        have hwu := honly w hw c hc h.1
        exact hwu ▸ hc'
      · intro h
        have hwu := honly w hw y hc' h
        exact ⟨hwu ▸ hc, hcc⟩
    · rw [mergeMap_of_ne hy]
      exact ⟨fun h => h.1, fun h => ⟨h, hy⟩⟩
  have hnotF : ∀ e ∈ E(H), ηe e ≠ f := fun e he h => hfF ⟨e, he, h⟩
  have hmodel : IsMinorModel H (mergeEdge J f c c') (fun w => ν w \ {c'}) ηe := by
    refine ⟨?_, ?_, ?_, ?_, hm.edge_injOn, ?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨y, hy⟩ := hm.vertex_nonempty w hw
      exact ⟨mergeMap c c' y, (hmap w hw y).2 hy⟩
    · intro w hw y hy
      rw [hVM]
      exact ⟨hm.vertex_subset w hw hy.1, hy.2⟩
    · intro e he
      rw [hEM]
      exact ⟨hm.edge_mem e he, hnotF e he⟩
    · intro a ha b hb hab
      exact (hm.vertex_disjoint a ha b hb hab).mono sdiff_subset sdiff_subset
    · intro w hw e he
      rw [hm.inc_iff w hw e he]
      constructor
      · rintro ⟨y, hy, hinc⟩
        exact ⟨mergeMap c c' y, (hmap w hw y).2 hy, mergeEdge_inc.2 ⟨hnotF e he, y, hinc, rfl⟩⟩
      · rintro ⟨y, hy, hinc⟩
        obtain ⟨-, y₀, h₀, rfl⟩ := mergeEdge_inc.1 hinc
        exact ⟨y₀, (hmap w hw y₀).1 hy, h₀⟩
    · intro w hw e he
      rw [hm.isLoopAt_iff w hw e he]
      constructor
      · intro hall y hy
        obtain ⟨-, y₀, h₀, rfl⟩ := mergeEdge_inc.1 hy
        exact (hmap w hw y₀).2 (hall y₀ h₀)
      · intro hall y₀ h₀
        exact (hmap w hw y₀).1 (hall _ (mergeEdge_inc.2 ⟨hnotF e he, y₀, h₀, rfl⟩))
    · intro w hw
      obtain ⟨K, hK, hKv, hconn⟩ := hm.connected w hw
      have hsub : ν w \ {c'} ⊆ V((mergeEdge J f c c').deleteEdges (ηe '' E(H))) := by
        intro y hy
        rw [vertexSet_deleteEdges, hVM]
        exact ⟨hm.vertex_subset w hw hy.1, hy.2⟩
      let L := ((mergeEdge J f c c').deleteEdges (ηe '' E(H))).induce (ν w \ {c'})
      refine ⟨L, Graph.induce_le hsub, rfl, ?_⟩
      have hstep : ∀ {a b}, K.Adj a b →
          Relation.ReflTransGen L.Adj (mergeMap c c' a) (mergeMap c c' b) := by
        rintro a b ⟨e, hab⟩
        have hG := hK.isLink_mono hab
        rw [deleteEdges_isLink] at hG
        by_cases hef : e = f
        · subst hef
          have heq := hG.1.isLink_iff_sym2_eq.1 hf
          rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [mergeMap_of_ne hcc, mergeMap_right]
          · rw [mergeMap_of_ne hcc, mergeMap_right]
        · have ha : a ∈ ν w := hKv ▸ hab.left_mem
          have hb : b ∈ ν w := hKv ▸ hab.right_mem
          exact Relation.ReflTransGen.single ⟨e, ⟨mergeEdge_isLink.2 ⟨hef, a, b, hG.1, rfl, rfl⟩,
            hG.2⟩, (hmap w hw a).2 ha, (hmap w hw b).2 hb⟩
      have hwalk : ∀ {a b}, Relation.ReflTransGen K.Adj a b →
          Relation.ReflTransGen L.Adj (mergeMap c c' a) (mergeMap c c' b) := by
        intro a b h
        induction h with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hab ih => exact ih.trans (hstep hab)
      obtain ⟨y, hy⟩ := hm.vertex_nonempty w hw
      refine ⟨⟨mergeMap c c' y, (hmap w hw y).2 hy⟩, ?_⟩
      intro a ha b hb
      have h := hwalk (hconn.2 a (hKv ▸ ha.1) b (hKv ▸ hb.1))
      rwa [mergeMap_of_ne ha.2, mergeMap_of_ne hb.2] at h
  have hbranch : ∀ w ∈ V(H),
      branchEdges H (mergeEdge J f c c') (fun w => ν w \ {c'}) ηe w ⊆ branchEdges H J ν ηe w \ {f} := by
    intro w hw e ⟨he, hnot, hall⟩
    rw [hEM] at he
    refine ⟨⟨he.1, hnot, fun y₀ h₀ => (hmap w hw y₀).1 (hall _ ?_)⟩, he.2⟩
    exact mergeEdge_inc.2 ⟨he.2, y₀, h₀, rfl⟩
  have hfJ : f ∈ branchEdges H J ν ηe u := by
    refine ⟨hf.edge_mem, hfF, fun y hy => ?_⟩
    rcases hy.eq_or_eq_of_isLink hf with rfl | rfl
    · exact hc
    · exact hc'
  have hνfin : ∀ w ∈ V(H), (ν w).Finite := fun w hw => hVJ.subset (hm.vertex_subset w hw)
  have hBfin : ∀ w, (branchEdges H J ν ηe w).Finite := fun w => hEJ.subset fun e he => he.1
  refine ⟨hmodel, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [hVM] at hy
    obtain ⟨w, hw, hyw⟩ := hs.cover y hy.1
    exact ⟨w, hw, hyw, hy.2⟩
  · intro e he hnot
    rw [hEM] at he
    obtain ⟨w, hw, hall⟩ := hs.internal e he.1 hnot
    refine ⟨w, hw, fun y hy => ?_⟩
    obtain ⟨-, y₀, h₀, rfl⟩ := mergeEdge_inc.1 hy
    exact (hmap w hw y₀).2 (hall y₀ h₀)
  · intro w hw
    have hle := Set.ncard_le_ncard (hbranch w hw) ((hBfin w).sdiff)
    have hcount := hs.count w hw
    show (branchEdges H (mergeEdge J f c c') (fun w => ν w \ {c'}) ηe w).ncard + 1 ≤
      (ν w \ {c'}).ncard
    by_cases hwu : w = u
    · subst hwu
      have h1 := Set.ncard_sdiff_singleton_add_one hfJ (hBfin w)
      have h2 := Set.ncard_sdiff_singleton_add_one hc' (hνfin w hw)
      omega
    · have hc'w : c' ∉ ν w := fun h => hwu (honly w hw c' hc' h)
      have h1 := Set.ncard_le_ncard (sdiff_subset (t := {f})) (hBfin w)
      change _ + 1 ≤ (ν w \ {c'}).ncard
      rw [Set.sdiff_singleton_eq_self hc'w]
      omega
  · intro w hw y hy h2
    have h2' : 2 ≤ (ν w).ncard :=
      h2.trans (Set.ncard_le_ncard sdiff_subset (hνfin w hw))
    by_cases hyc : y = c
    · subst hyc
      have hwu := honly w hw y hc hy.1
      subst hwu
      have hself := valency_mergeEdge_self hEJ hf hcc
      have h1 := hs.high w hw y hc h2'
      have h2 := hs.high w hw c' hc' h2'
      change 3 ≤ valency (mergeEdge J f y c') y
      omega
    · change 3 ≤ valency (mergeEdge J f c c') y
      rw [valency_mergeEdge_of_ne hEJ hf hyc hy.2]
      exact hs.high w hw y hy.1 h2'

end Merge

/-- An edge joins `x` and `y` when it is incident with both, and, if
`x = y`, it has no other end. -/
theorem isLink_iff_inc_and_loop (G : Graph α β) (e : β) (x y : α) :
    G.IsLink e x y ↔ G.Inc e x ∧ G.Inc e y ∧ (x = y → ∀ z, G.Inc e z → z = x) := by
  constructor
  · intro h
    refine ⟨h.inc_left, h.inc_right, fun hxy z hz => ?_⟩
    rcases hz.eq_or_eq_of_isLink h with rfl | rfl
    · rfl
    · exact hxy.symm
  · rintro ⟨⟨w, hxw⟩, hy, h3⟩
    rcases hy.eq_or_eq_of_isLink hxw with rfl | rfl
    · have hw := h3 rfl w hxw.inc_right
      subst hw
      exact hxw
    · exact hxw

/-- If every branch set of a model is a single vertex and the tree condition
holds, then `J` is isomorphic to `H`. Each branch set spans no edge, so every
edge of `J` represents an edge of `H`. The isomorphism sends a vertex `u` to
the vertex of `ν u`, and an edge `e` to `ηe e`. -/
theorem IsSplitSource.iso_of_singletons {H : Graph α' β'} {J : Graph α β}
    {ν : α' → Set α} {ηe : β' → β} {k : ℕ} (hs : IsSplitSource H J ν ηe k)
    (hVJ : V(J).Finite) (hEJ : E(J).Finite)
    (hone : ∀ u ∈ V(H), (ν u).ncard ≤ 1) : Nonempty (Iso H J) := by
  have hm := hs.model
  have hνfin : ∀ w ∈ V(H), (ν w).Finite := fun w hw => hVJ.subset (hm.vertex_subset w hw)
  let g : V(H) → α := fun u => (hm.vertex_nonempty u.1 u.2).some
  have hg : ∀ u : V(H), g u ∈ ν u.1 := fun u => (hm.vertex_nonempty u.1 u.2).some_mem
  have hgeq : ∀ u : V(H), ∀ y ∈ ν u.1, y = g u := fun u y hy =>
    (Set.ncard_le_one (hνfin u.1 u.2)).1 (hone u.1 u.2) y hy (g u) (hg u)
  have hginj : Function.Injective g := by
    intro a b hab
    by_contra hne
    exact Set.disjoint_left.1
      (hm.vertex_disjoint a.1 a.2 b.1 b.2 (fun h => hne (Subtype.ext h))) (hg a) (hab ▸ hg b)
  let fv : V(H) → V(J) := fun u => ⟨g u, hm.vertex_subset u.1 u.2 (hg u)⟩
  have hfv : Function.Bijective fv := by
    refine ⟨fun a b hab => hginj (congrArg Subtype.val hab), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨u, hu, hyu⟩ := hs.cover y hy
    exact ⟨⟨u, hu⟩, Subtype.ext (hgeq ⟨u, hu⟩ y hyu).symm⟩
  -- Every edge of `J` represents an edge of `H`, since branch sets span no edges.
  have hEeq : E(J) = ηe '' E(H) := by
    apply Set.Subset.antisymm
    · intro e he
      by_contra hnot
      obtain ⟨u, hu, hall⟩ := hs.internal e he hnot
      have hmem : e ∈ branchEdges H J ν ηe u := ⟨he, hnot, hall⟩
      have hpos : 0 < (branchEdges H J ν ηe u).ncard :=
        Set.ncard_pos (hEJ.subset fun e he => he.1) |>.2 ⟨e, hmem⟩
      have := hs.count u hu
      have := hone u hu
      omega
    · rintro _ ⟨e, he, rfl⟩
      exact hm.edge_mem e he
  let fe : E(H) → E(J) := fun e => ⟨ηe e, hm.edge_mem e.1 e.2⟩
  have hfe : Function.Bijective fe := by
    refine ⟨fun a b hab => Subtype.ext (hm.edge_injOn a.2 b.2 (congrArg Subtype.val hab)), ?_⟩
    rintro ⟨f, hf⟩
    rw [hEeq] at hf
    obtain ⟨e, he, rfl⟩ := hf
    exact ⟨⟨e, he⟩, rfl⟩
  have hinc : ∀ (e : E(H)) (u : V(H)), H.Inc e.1 u.1 ↔ J.Inc (ηe e.1) (g u) := by
    intro e u
    rw [hm.inc_iff u.1 u.2 e.1 e.2]
    constructor
    · rintro ⟨y, hy, h⟩
      rwa [hgeq u y hy] at h
    · exact fun h => ⟨g u, hg u, h⟩
  have hloop : ∀ (e : E(H)) (u : V(H)), H.Inc e.1 u.1 →
      ((∀ z, H.Inc e.1 z → z = u.1) ↔ ∀ z, J.Inc (ηe e.1) z → z = g u) := by
    intro e u hu
    have hL := hm.isLoopAt_iff u.1 u.2 e.1 e.2
    have hH : H.IsLoopAt e.1 u.1 ↔ ∀ z, H.Inc e.1 z → z = u.1 := by
      change H.IsLink e.1 u.1 u.1 ↔ _
      rw [isLink_iff_inc_and_loop]
      exact ⟨fun h => h.2.2 rfl, fun h => ⟨hu, hu, fun _ => h⟩⟩
    rw [← hH, hL]
    exact ⟨fun h z hz => hgeq u z (h z hz), fun h z hz => h z hz ▸ hg u⟩
  refine ⟨⟨Equiv.ofBijective fv hfv, Equiv.ofBijective fe hfe, ?_⟩⟩
  intro e x y
  change H.IsLink e.1 x.1 y.1 ↔ J.IsLink (ηe e.1) (g x) (g y)
  rw [isLink_iff_inc_and_loop, isLink_iff_inc_and_loop]
  constructor
  · rintro ⟨hx, hy, h3⟩
    refine ⟨(hinc e x).1 hx, (hinc e y).1 hy, fun hgxy => ?_⟩
    exact (hloop e x hx).1 (h3 (congrArg Subtype.val (hginj hgxy)))
  · rintro ⟨hx, hy, h3⟩
    refine ⟨(hinc e x).2 hx, (hinc e y).2 hy, fun hxy => ?_⟩
    exact (hloop e x ((hinc e x).2 hx)).2 (h3 (congrArg g (Subtype.ext hxy)))

/-- A graph with a model of `H` whose branch sets span trees, and whose
vertices in branch sets of size at least two have valency at least three, is a
split of `H`. Contract the branch trees one edge at a time. -/
theorem IsSplitSource.isSplitOf {H : Graph α' β'} {J : Graph α β}
    {ν : α' → Set α} {ηe : β' → β} (hs : IsSplitSource H J ν ηe 3)
    (hVJ : V(J).Finite) (hEJ : E(J).Finite) :
    IsSplitOf H J := by
  generalize hn : V(J).ncard = n
  induction n using Nat.strong_induction_on generalizing J ν with
  | h n ih =>
    by_cases hbig : ∃ u ∈ V(H), 2 ≤ (ν u).ncard
    · obtain ⟨u, hu, h2⟩ := hbig
      have hνfin : (ν u).Finite := hVJ.subset (hs.model.vertex_subset u hu)
      obtain ⟨f, c, c', hf, hcc, hfF, hc, hc'⟩ := GraphMinor.GM02.IsMinorModel.exists_branch_edge hs.model hu hνfin h2
      have hs' := hs.merge hVJ hEJ hu hf hcc hfF hc hc'
      have hVM : V(mergeEdge J f c c') = V(J) \ {c'} := mergeEdge_vertexSet hf hcc
      have hEM : E(mergeEdge J f c c') = E(J) \ {f} := mergeEdge_edgeSet J f c c'
      have hVMf : V(mergeEdge J f c c').Finite := hVM ▸ hVJ.sdiff
      have hEMf : E(mergeEdge J f c c').Finite := hEM ▸ hEJ.sdiff
      have hlt : V(mergeEdge J f c c').ncard < n := by
        rw [hVM]
        have := Set.ncard_sdiff_singleton_add_one hf.right_mem hVJ
        omega
      obtain ⟨J₀, hJ₀, hchain⟩ := ih _ hlt hs' hVMf hEMf rfl
      refine ⟨J₀, hJ₀, hchain.tail ⟨f, c, c', hf, hcc, ?_, ?_, ⟨Iso.refl _⟩⟩⟩
      · exact hs.high u hu c hc h2
      · exact hs.high u hu c' hc' h2
    · simp only [not_exists, not_and, not_le] at hbig
      refine ⟨J, hs.iso_of_singletons hVJ hEJ fun u hu => ?_, Relation.ReflTransGen.refl⟩
      have := hbig u hu
      omega

end GraphMinor.GM02
