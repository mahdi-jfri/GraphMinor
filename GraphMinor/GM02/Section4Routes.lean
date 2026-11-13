module

public import GraphMinor.GM02.Section4Suppression

/-!
# Routes of the edges of a suppressed graph

Graph Minors II, page 319, proves (4.5) by comparing topological containment
with disjoint paths. In one direction we need this: if `L` comes from `K` by
suppressions, then each edge of `L` is the trace of a walk in `K` between its
ends. The inner vertices of these walks are vertices of `K` that were
suppressed. Each walk has no repeated inner vertex, and two edges of `L` have
walks with no common inner vertex.

A route is a start, a list of inner vertices and a finish. We prove the claim
by induction on the number of suppressions. When a vertex `x` is suppressed,
the walk of the new edge is the walk of the first removed edge, then `x`, then
the walk of the second removed edge.

The file also defines consecutive pairs in a list, used for the converse
direction in `Section4Subdivision.lean`.
-/

@[expose] public section

namespace GraphMinor.GM02

open Graph Set Relation

universe u v

variable {α : Type u} {β : Type v}

/-- A walk given by its first vertex, its inner vertices and its last vertex. -/
structure Route (α : Type u) where
  /-- The first vertex. -/
  start : α
  /-- The inner vertices, in order. -/
  inner : List α
  /-- The last vertex. -/
  finish : α

/-- All vertices of a route, in order. -/
def Route.list (r : Route α) : List α := r.start :: (r.inner ++ [r.finish])

/-- The same route traversed backwards. -/
def Route.reverse (r : Route α) : Route α := ⟨r.finish, r.inner.reverse, r.start⟩

theorem Route.list_reverse (r : Route α) : r.reverse.list = r.list.reverse := by
  simp [Route.list, Route.reverse]

/-! ### Consecutive vertices of a list -/

/-- `Consec l x y` says that `y` follows `x` directly in the list `l`. -/
def Consec : List α → α → α → Prop
  | a :: b :: l, x, y => (x = a ∧ y = b) ∨ Consec (b :: l) x y
  | _, _, _ => False

theorem consec_cons_cons {a b x y : α} {l : List α} :
    Consec (a :: b :: l) x y ↔ (x = a ∧ y = b) ∨ Consec (b :: l) x y := Iff.rfl

theorem not_consec_nil {x y : α} : ¬ Consec [] x y := id

theorem not_consec_singleton {a x y : α} : ¬ Consec [a] x y := id

theorem Consec.mem {l : List α} {x y : α} (h : Consec l x y) : x ∈ l ∧ y ∈ l := by
  induction l with
  | nil => exact h.elim
  | cons a l ih =>
    cases l with
    | nil => exact h.elim
    | cons b l =>
      rcases h with ⟨rfl, rfl⟩ | h
      · exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
      · obtain ⟨hx, hy⟩ := ih h
        exact ⟨List.mem_cons_of_mem _ hx, List.mem_cons_of_mem _ hy⟩

/-- A chain is a list whose consecutive pairs are related. -/
theorem isChain_iff_consec {R : α → α → Prop} {l : List α} :
    l.IsChain R ↔ ∀ x y, Consec l x y → R x y := by
  induction l with
  | nil => exact ⟨fun _ _ _ h => h.elim, fun _ => List.IsChain.nil⟩
  | cons a l ih =>
    cases l with
    | nil => exact ⟨fun _ _ _ h => h.elim, fun _ => List.IsChain.singleton a⟩
    | cons b l =>
      rw [List.isChain_cons_cons, ih]
      constructor
      · rintro ⟨hab, h⟩ x y (⟨rfl, rfl⟩ | hxy)
        · exact hab
        · exact h x y hxy
      · intro h
        exact ⟨h a b (Or.inl ⟨rfl, rfl⟩), fun x y hxy => h x y (Or.inr hxy)⟩

/-- Two chains on the same list combine. -/
theorem isChain_and {R S : α → α → Prop} {l : List α} (hR : l.IsChain R) (hS : l.IsChain S) :
    l.IsChain fun a b => R a b ∧ S a b := by
  rw [isChain_iff_consec] at hR hS ⊢
  exact fun x y h => ⟨hR x y h, hS x y h⟩

/-- In a list without repetitions, consecutive vertices differ. -/
theorem Consec.ne {l : List α} (hl : l.Nodup) {x y : α} (h : Consec l x y) : x ≠ y := by
  have hc : l.IsChain (· ≠ ·) := List.Pairwise.isChain hl
  exact isChain_iff_consec.1 hc x y h

/-! ### Routes along a sequence of suppressions -/

/-- The route conditions of one edge `f` of `M`, with walks in `K`. -/
def RouteOK (K M : Graph α β) (r : Route α) (f : β) : Prop :=
  M.IsLink f r.start r.finish ∧ r.list.IsChain K.Adj ∧ r.inner.Nodup ∧
    ∀ y ∈ r.inner, y ∈ V(K) ∧ y ∉ V(M)

/-- A route for every edge of `M`, with pairwise disjoint inner vertices. -/
def IsRouteSystem (K M : Graph α β) (r : β → Route α) : Prop :=
  (∀ f ∈ E(M), RouteOK K M (r f) f) ∧
    ∀ f ∈ E(M), ∀ g ∈ E(M), f ≠ g → ∀ y ∈ (r f).inner, y ∉ (r g).inner

private theorem isChain_adj_reverse {K : Graph α β} {l : List α} (h : l.IsChain K.Adj) :
    l.reverse.IsChain K.Adj :=
  List.isChain_reverse.2 (h.imp fun _ _ h => h.symm)

/-- Reversing a route keeps the route conditions. -/
theorem RouteOK.reverse {K M : Graph α β} {r : Route α} {f : β} (h : RouteOK K M r f) :
    RouteOK K M r.reverse f := by
  obtain ⟨hl, hc, hn, hi⟩ := h
  refine ⟨hl.symm, ?_, List.nodup_reverse.2 hn, fun y hy => hi y (List.mem_reverse.1 hy)⟩
  rw [Route.list_reverse]
  exact isChain_adj_reverse hc

/-- Turn a route so that it starts at a given end of its edge. -/
noncomputable def Route.orient (r : Route α) (p : α) : Route α := by
  classical
  exact if r.start = p then r else r.reverse

theorem Route.mem_inner_orient {r : Route α} {p y : α} : y ∈ (r.orient p).inner ↔ y ∈ r.inner := by
  classical
  unfold Route.orient
  split_ifs
  · rfl
  · exact List.mem_reverse

theorem RouteOK.orient {K M : Graph α β} {r : Route α} {f : β} (h : RouteOK K M r f) (p : α) :
    RouteOK K M (r.orient p) f := by
  classical
  unfold Route.orient
  split_ifs
  · exact h
  · exact h.reverse

/-- After orienting, a route of an edge with ends `p` and `q` starts at `p` and
ends at `q`. -/
theorem RouteOK.orient_ends {K M : Graph α β} {r : Route α} {f : β} (h : RouteOK K M r f)
    {p q : α} (hpq : M.IsLink f p q) : (r.orient p).start = p ∧ (r.orient p).finish = q := by
  classical
  unfold Route.orient
  rcases h.1.eq_and_eq_or_eq_and_eq hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [show (if r.start = p then r else r.reverse) = r from by simp [h1]]
    exact ⟨h1, h2⟩
  · by_cases hs : r.start = p
    · rw [show (if r.start = p then r else r.reverse) = r from by simp [hs]]
      exact ⟨hs, h2.trans (hs.symm.trans h1)⟩
    · rw [show (if r.start = p then r else r.reverse) = r.reverse from by simp [hs]]
      exact ⟨h2, h1⟩

/-- Chains glue at a common vertex. -/
private theorem isChain_glue {R : α → α → Prop} {l₁ l₂ : List α} {x : α}
    (h₁ : (l₁ ++ [x]).IsChain R) (h₂ : (x :: l₂).IsChain R) : (l₁ ++ x :: l₂).IsChain R := by
  have h := List.IsChain.append_overlap (l₁ := l₁) (l₂ := [x]) (l₃ := l₂) h₁ h₂ (by simp)
  simpa using h

/-- One suppression keeps a route system, with the glued route for the new edge. -/
theorem IsRouteSystem.suppress {K M : Graph α β} {r : β → Route α}
    (hr : IsRouteSystem K M r) (hKM : V(M) ⊆ V(K)) (d : SuppressionData M) :
    ∃ r' : β → Route α, IsRouteSystem K d.result r' := by
  classical
  obtain ⟨hok, hdisj⟩ := hr
  have h1 : d.first ∈ E(M) := d.first_link.edge_mem
  have h2 : d.second ∈ E(M) := d.second_link.edge_mem
  have hx : d.vertex ∈ V(M) := d.first_link.left_mem
  set r₁ := (r d.first).orient d.left with hr₁
  set r₂ := (r d.second).orient d.vertex with hr₂
  have hok₁ : RouteOK K M r₁ d.first := (hok _ h1).orient _
  have hok₂ : RouteOK K M r₂ d.second := (hok _ h2).orient _
  obtain ⟨hs₁, hf₁⟩ := (hok _ h1).orient_ends d.first_link.symm
  obtain ⟨hs₂, hf₂⟩ := (hok _ h2).orient_ends d.second_link
  let glued : Route α := ⟨d.left, r₁.inner ++ d.vertex :: r₂.inner, d.right⟩
  refine ⟨fun f => if f = d.fresh then glued else r f, ?_, ?_⟩
  · intro f hf
    by_cases hff : f = d.fresh
    · simp only [hff, ite_true]
      refine ⟨(d.fresh_isLink_iff _ _).2 (Or.inl ⟨rfl, rfl⟩), ?_, ?_, ?_⟩
      · -- Glue the two walks at the suppressed vertex.
        have hc₁ := hok₁.2.1
        have hc₂ := hok₂.2.1
        rw [Route.list, hs₁, hf₁] at hc₁
        rw [Route.list, hs₂, hf₂] at hc₂
        have h := isChain_glue (l₁ := d.left :: r₁.inner) (l₂ := r₂.inner ++ [d.right])
          (by simpa using hc₁) hc₂
        simpa [Route.list, glued] using h
      · rw [List.nodup_append]
        refine ⟨hok₁.2.2.1, List.nodup_cons.2 ⟨fun h => (hok₂.2.2.2 _ h).2 hx, hok₂.2.2.1⟩, ?_⟩
        intro y hy z hz hyz
        subst hyz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact (hok₁.2.2.2 _ hy).2 hx
        · exact hdisj _ h1 _ h2 d.first_ne_second y (Route.mem_inner_orient.1 hy)
            (Route.mem_inner_orient.1 hz)
      · intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · obtain ⟨hyK, hyM⟩ := hok₁.2.2.2 y hy
          exact ⟨hyK, fun h => hyM h.1⟩
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact ⟨hKM hx, fun h => h.2 rfl⟩
          · obtain ⟨hyK, hyM⟩ := hok₂.2.2.2 y hy
            exact ⟨hyK, fun h => hyM h.1⟩
    · simp only [hff, ite_false]
      have hmem : f ∈ E(M) ∧ f ≠ d.first ∧ f ≠ d.second := by
        rcases hf with ⟨hf, hne⟩ | hf
        · exact ⟨hf, fun h => hne (Or.inl h), fun h => hne (Or.inr h)⟩
        · exact (hff (Set.mem_singleton_iff.1 hf)).elim
      obtain ⟨hl, hc, hn, hi⟩ := hok f hmem.1
      exact ⟨(d.retained_isLink_iff hff _ _).2 ⟨hl, hmem.2⟩, hc, hn,
        fun y hy => ⟨(hi y hy).1, fun h => (hi y hy).2 h.1⟩⟩
  · have hret : ∀ f ∈ E(d.result), f ≠ d.fresh → f ∈ E(M) ∧ f ≠ d.first ∧ f ≠ d.second := by
      rintro f (⟨hf, hne⟩ | hf) hff
      · exact ⟨hf, fun h => hne (Or.inl h), fun h => hne (Or.inr h)⟩
      · exact (hff (Set.mem_singleton_iff.1 hf)).elim
    -- An inner vertex of the glued route is not inner for any kept edge.
    have hglued : ∀ g ∈ E(d.result), g ≠ d.fresh → ∀ y ∈ glued.inner, y ∉ (r g).inner := by
      intro g hg hgf y hy hyg
      obtain ⟨hgM, hg1, hg2⟩ := hret g hg hgf
      rcases List.mem_append.1 hy with hy | hy
      · exact hdisj _ h1 _ hgM (Ne.symm hg1) y (Route.mem_inner_orient.1 hy) hyg
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact ((hok g hgM).2.2.2 _ hyg).2 hx
        · exact hdisj _ h2 _ hgM (Ne.symm hg2) y (Route.mem_inner_orient.1 hy) hyg
    intro f hf g hg hfg y hy hyg
    by_cases hff : f = d.fresh <;> by_cases hgf : g = d.fresh
    · exact hfg (hff.trans hgf.symm)
    · simp only [hff, hgf, ite_true, ite_false] at hy hyg
      exact hglued g hg hgf y hy hyg
    · simp only [hff, hgf, ite_true, ite_false] at hy hyg
      exact hglued f hf hff y hyg hy
    · simp only [hff, hgf, ite_false] at hy hyg
      exact hdisj f (hret f hf hff).1 g (hret g hg hgf).1 hfg y hy hyg

/-- Graph Minors II, Section 4: if `L` is obtained from `K` by suppressions,
then the edges of `L` have routes in `K` with pairwise disjoint inner
vertices, and these inner vertices are not vertices of `L`. -/
theorem exists_routeSystem [Nonempty α] {K L : Graph α β} (h : ReflTransGen IsSuppression K L) :
    ∃ r : β → Route α, IsRouteSystem K L r := by
  classical
  induction h with
  | refl =>
    refine ⟨fun f => if hf : f ∈ E(K) then
      ⟨(K.exists_isLink_of_mem_edgeSet hf).choose, [],
        (K.exists_isLink_of_mem_edgeSet hf).choose_spec.choose⟩
      else ⟨Classical.arbitrary α, [], Classical.arbitrary α⟩, ?_, ?_⟩
    · intro f hf
      simp only [hf, ↓reduceDIte]
      have hl := (K.exists_isLink_of_mem_edgeSet hf).choose_spec.choose_spec
      refine ⟨hl, ?_, List.nodup_nil, fun y hy => (List.not_mem_nil hy).elim⟩
      exact List.isChain_pair.2 ⟨f, hl⟩
    · intro f hf g _ _ y hy
      simp only [hf, ↓reduceDIte] at hy
      exact (List.not_mem_nil hy).elim
  | @tail M _ hKM hstep ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨d, rfl⟩ := hstep
    exact hr.suppress (vertexSet_subset_of_reflTransGen hKM) d

end GraphMinor.GM02
