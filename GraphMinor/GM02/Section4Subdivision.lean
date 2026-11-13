module

public import GraphMinor.GM02.Section4Routes

/-!
# A union of disjoint paths suppresses to `H`

This is the converse step of Graph Minors II, (4.5), page 319. Let `H` have no
two edges with the same ends. Suppose that each edge `f` of `H` has a path in
`K` between its ends, with no repeated vertex (so `f` is not a loop), that the inner vertices of these paths are
outside `V(H)` and pairwise disjoint, and that `K` is exactly the union of
these paths and `V(H)`, with one edge for each consecutive pair. Then
suppressing the inner vertices one by one turns `K` into `H`.

The proof is by induction on the number of inner vertices. Take an edge `f`
whose path `a, x, z, …` has an inner vertex `x`. In `K` the vertex `x` lies
only on this path, so it has exactly two edges, one to `a` and one to `z`.
Suppressing `x` joins `a` to `z` directly, and the other paths stay as they
were. The one thing to check is that `K` has no other edge between `a` and `z`.
Such an edge would be on a path through `a` and `z`. As `x` lies between them
on the path of `f`, this path is another path. Then `a` and `z` are both ends
of `f` and of this other edge of `H`, so `H` would have two edges with the same
ends. When no inner vertex is left, every path is a single edge, and the map
from each edge of `H` to the edge of its path is an isomorphism.
-/

@[expose] public section

namespace GraphMinor.GM02

open Graph Set Relation

universe u v

variable {α : Type u} {β : Type v}

theorem Route.mem_list {r : Route α} {y : α} :
    y ∈ r.list ↔ y = r.start ∨ y ∈ r.inner ∨ y = r.finish := by
  simp only [Route.list, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false]

/-- The paths of the edges of `H` cover `K` exactly, as described above. -/
structure SubdivisionRoutes (K H : Graph α β) (r : β → Route α) : Prop where
  vertex_subset : V(H) ⊆ V(K)
  link : ∀ f ∈ E(H), H.IsLink f (r f).start (r f).finish
  nodup : ∀ f ∈ E(H), (r f).list.Nodup
  chain : ∀ f ∈ E(H), (r f).list.IsChain K.Adj
  inner_notMem : ∀ f ∈ E(H), ∀ y ∈ (r f).inner, y ∉ V(H)
  disjoint : ∀ f ∈ E(H), ∀ g ∈ E(H), f ≠ g → ∀ y ∈ (r f).inner, y ∉ (r g).inner
  cover : ∀ y ∈ V(K), y ∈ V(H) ∨ ∃ f ∈ E(H), y ∈ (r f).inner
  edge_consec : ∀ e p q, K.IsLink e p q →
    ∃ f ∈ E(H), Consec (r f).list p q ∨ Consec (r f).list q p
  unique : ∀ e e' p q, K.IsLink e p q → K.IsLink e' p q → e = e'

/-- A vertex outside `V(H)` on the path of `g` is an inner vertex of `g`. -/
theorem SubdivisionRoutes.mem_inner_of_mem_list {K H : Graph α β} {r : β → Route α}
    (hs : SubdivisionRoutes K H r) {g : β} (hg : g ∈ E(H)) {y : α} (hy : y ∈ (r g).list)
    (hyH : y ∉ V(H)) : y ∈ (r g).inner := by
  rcases Route.mem_list.1 hy with rfl | hy | rfl
  · exact (hyH (hs.link g hg).left_mem).elim
  · exact hy
  · exact (hyH (hs.link g hg).right_mem).elim

/-- A vertex of `V(H)` on the path of `g` is one of its ends. -/
theorem SubdivisionRoutes.eq_end_of_mem_list {K H : Graph α β} {r : β → Route α}
    (hs : SubdivisionRoutes K H r) {g : β} (hg : g ∈ E(H)) {y : α} (hy : y ∈ (r g).list)
    (hyH : y ∈ V(H)) : y = (r g).start ∨ y = (r g).finish := by
  rcases Route.mem_list.1 hy with h | h | h
  · exact Or.inl h
  · exact (hs.inner_notMem g hg y h hyH).elim
  · exact Or.inr h

/-! ### One suppression -/

/-- In `a :: x :: m` without repetitions, a consecutive pair containing `x` is
`(a, x)` or `(x, head of m)`. -/
private theorem consec_of_mem_pair {a x z : α} {l : List α} (hn : (a :: x :: z :: l).Nodup)
    {p q : α} (h : Consec (a :: x :: z :: l) p q) (hx : p = x ∨ q = x) :
    (p = a ∧ q = x) ∨ (p = x ∧ q = z) := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · have hxl : x ∉ z :: l := (List.nodup_cons.1 (List.nodup_cons.1 hn).2).1
    rcases hx with rfl | rfl
    · exact (hxl h.mem.1).elim
    · exact (hxl h.mem.2).elim

private theorem consec_drop {a x z : α} {l : List α} {p q : α}
    (h : Consec (a :: x :: z :: l) p q) (h1 : ¬ (p = a ∧ q = x)) (h2 : ¬ (p = x ∧ q = z)) :
    Consec (a :: z :: l) p q := by
  rcases h with h | h | h
  · exact (h1 h).elim
  · exact (h2 h).elim
  · exact Or.inr h

private theorem consec_undrop {a x z : α} {l : List α} {p q : α}
    (h : Consec (a :: z :: l) p q) : (p = a ∧ q = z) ∨ Consec (a :: x :: z :: l) p q := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))

/-- One inner vertex can be suppressed, and the shortened paths again cover the
result exactly. -/
theorem SubdivisionRoutes.step {K H : Graph α β} {r : β → Route α}
    (hpar : ∀ f g a b, H.IsLink f a b → H.IsLink g a b → f = g)
    (hs : SubdivisionRoutes K H r) {f : β} (hf : f ∈ E(H)) {x : α} {rest : List α}
    (hin : (r f).inner = x :: rest) :
    ∃ d : SuppressionData K, d.vertex = x ∧ x ∉ V(H) ∧
      ∃ r' : β → Route α, SubdivisionRoutes d.result H r' := by
  classical
  set a := (r f).start with ha
  set b := (r f).finish with hb
  obtain ⟨z, l, hm⟩ : ∃ z l, rest ++ [b] = z :: l := by
    cases h : rest ++ [b] with
    | nil => simp at h
    | cons z l => exact ⟨z, l, rfl⟩
  have hlist : (r f).list = a :: x :: z :: l := by
    simp only [Route.list, hin, List.cons_append]
    rw [← hb, hm]
  have hn : (a :: x :: z :: l).Nodup := hlist ▸ hs.nodup f hf
  have hax : a ≠ x := fun h => (List.nodup_cons.1 hn).1 (h ▸ List.mem_cons_self)
  have haz : a ≠ z := fun h =>
    (List.nodup_cons.1 hn).1 (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
  have hxz : x ≠ z := fun h => (List.nodup_cons.1 (List.nodup_cons.1 hn).2).1
    (h ▸ List.mem_cons_self)
  have hxH : x ∉ V(H) := hs.inner_notMem f hf x (hin ▸ List.mem_cons_self)
  have hchain := hlist ▸ hs.chain f hf
  have hadj : ∀ p q, Consec (a :: x :: z :: l) p q → K.Adj p q :=
    isChain_iff_consec.1 hchain
  obtain ⟨e₁, he₁⟩ := hadj a x (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨e₂, he₂⟩ := hadj x z (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have he₁₂ : e₁ ≠ e₂ := by
    intro h
    rw [h] at he₁
    rcases he₁.eq_and_eq_or_eq_and_eq he₂ with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hax h1
    · exact haz h1
  -- The vertex `x` lies on no other path.
  have hxg : ∀ g ∈ E(H), g ≠ f → x ∉ (r g).list := by
    intro g hg hgf hx
    exact hs.disjoint f hf g hg (Ne.symm hgf) x (hin ▸ List.mem_cons_self)
      (hs.mem_inner_of_mem_list hg hx hxH)
  -- Every edge at `x` is `e₁` or `e₂`.
  have hinc : ∀ g, K.Inc g x → g = e₁ ∨ g = e₂ := by
    rintro g ⟨w, hw⟩
    obtain ⟨h, hh, hc⟩ := hs.edge_consec g x w hw
    have hhf : h = f := by
      by_contra hhf
      rcases hc with hc | hc
      · exact hxg h hh hhf hc.mem.1
      · exact hxg h hh hhf hc.mem.2
    subst hhf
    rw [hlist] at hc
    rcases hc with hc | hc
    · rcases consec_of_mem_pair hn hc (Or.inl rfl) with ⟨h1, _⟩ | ⟨_, rfl⟩
      · exact (hax h1.symm).elim
      · exact Or.inr (hs.unique _ _ _ _ hw he₂)
    · rcases consec_of_mem_pair hn hc (Or.inr rfl) with ⟨rfl, _⟩ | ⟨_, h1⟩
      · exact Or.inl (hs.unique _ _ _ _ hw.symm he₁)
      · exact (hxz h1).elim
  let d : SuppressionData K :=
    { vertex := x
      left := a
      right := z
      first := e₁
      second := e₂
      fresh := e₁
      first_ne_second := he₁₂
      first_link := he₁.symm
      second_link := he₂
      vertex_ne_left := Ne.symm hax
      vertex_ne_right := hxz
      incident := hinc
      fresh_notMem := fun h => h.2 (Or.inl rfl) }
  refine ⟨d, rfl, hxH, fun g => if g = f then ⟨a, rest, b⟩ else r g, ?_⟩
  -- Facts about the new graph.
  have hnew : (⟨a, rest, b⟩ : Route α).list = a :: z :: l := by
    simp only [Route.list, hm]
  have hrf : ∀ g, g = f → (if g = f then (⟨a, rest, b⟩ : Route α) else r g).list = a :: z :: l :=
    fun g hg => by simp only [hg, ite_true, hnew]
  have hrg : ∀ g, g ≠ f → (if g = f then (⟨a, rest, b⟩ : Route α) else r g) = r g :=
    fun g hg => by simp only [hg, ite_false]
  -- An edge of `K` whose ends avoid `x` is kept.
  have hkeep : ∀ g p q, K.IsLink g p q → p ≠ x → q ≠ x → d.result.IsLink g p q := by
    intro g p q hl hp hq
    have hg1 : g ≠ e₁ := by
      rintro rfl
      rcases hl.eq_and_eq_or_eq_and_eq he₁ with ⟨_, h⟩ | ⟨h, _⟩
      · exact hq h
      · exact hp h
    have hg2 : g ≠ e₂ := by
      rintro rfl
      rcases hl.eq_and_eq_or_eq_and_eq he₂ with ⟨h, _⟩ | ⟨_, h⟩
      · exact hp h
      · exact hq h
    exact (d.retained_isLink_iff hg1 p q).2 ⟨hl, hg1, hg2⟩
  have hfresh : d.result.IsLink e₁ a z := (d.fresh_isLink_iff a z).2 (Or.inl ⟨rfl, rfl⟩)
  -- No edge of `K` joins `a` and `z`.
  have hnoaz : ∀ g, ¬ K.IsLink g a z := by
    intro g hg
    obtain ⟨h, hh, hc⟩ := hs.edge_consec g a z hg
    by_cases hhf : h = f
    · subst hhf
      rw [hlist] at hc
      have hal : a ∉ z :: l := fun h' =>
        (List.nodup_cons.1 hn).1 (List.mem_cons_of_mem _ h')
      rcases hc with ((⟨_, h1⟩ | ⟨h1, _⟩ | hc) | (⟨h1, _⟩ | ⟨h1, _⟩ | hc))
      · exact hxz h1.symm
      · exact hax h1
      · exact hal hc.mem.1
      · exact haz h1.symm
      · exact hxz h1.symm
      · exact hal hc.mem.2
    · have haH : a ∈ V(H) := (hs.link f hf).left_mem
      have hz : z ∈ (r f).list := hlist ▸ List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)
      have hzh : z ∈ (r h).list := by
        rcases hc with hc | hc
        · exact hc.mem.2
        · exact hc.mem.1
      have hah : a ∈ (r h).list := by
        rcases hc with hc | hc
        · exact hc.mem.1
        · exact hc.mem.2
      have hzH : z ∈ V(H) := by
        by_contra hzH
        exact hs.disjoint f hf h hh (Ne.symm hhf) z (hs.mem_inner_of_mem_list hf hz hzH)
          (hs.mem_inner_of_mem_list hh hzh hzH)
      have hzb : z = b := by
        rcases hs.eq_end_of_mem_list hf hz hzH with h1 | h1
        · exact (haz h1.symm).elim
        · exact h1
      have hlh : H.IsLink h a z := by
        have hl := hs.link h hh
        rcases hs.eq_end_of_mem_list hh hah haH with h1 | h1 <;>
          rcases hs.eq_end_of_mem_list hh hzh hzH with h2 | h2
        · exact (haz (h1.trans h2.symm)).elim
        · rw [h1, h2]
          exact hl
        · rw [h1, h2]
          exact hl.symm
        · exact (haz (h1.trans h2.symm)).elim
      have hlf : H.IsLink f a z := hzb ▸ hs.link f hf
      exact hhf (hpar h f a z hlh hlf)
  -- A kept edge of the result is an edge of `K` other than `e₁` and `e₂`.
  have hret : ∀ g p q, d.result.IsLink g p q → g ≠ e₁ →
      K.IsLink g p q ∧ g ≠ e₁ ∧ g ≠ e₂ :=
    fun g p q h hg => (d.retained_isLink_iff hg p q).1 h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    refine ⟨hs.vertex_subset hy, fun h => ?_⟩
    have hyx : y = x := Set.mem_singleton_iff.1 h
    exact hxH (hyx ▸ hy)
  · intro g hg
    by_cases hgf : g = f
    · simp only [hgf, ite_true]
      exact hs.link f hf
    · rw [hrg g hgf]
      exact hs.link g hg
  · intro g hg
    by_cases hgf : g = f
    · rw [hrf g hgf]
      exact (List.nodup_cons.2 ⟨fun h => (List.nodup_cons.1 hn).1 (List.mem_cons_of_mem _ h),
        (List.nodup_cons.1 (List.nodup_cons.1 hn).2).2⟩)
    · rw [hrg g hgf]
      exact hs.nodup g hg
  · intro g hg
    rw [isChain_iff_consec]
    intro p q hpq
    by_cases hgf : g = f
    · rw [hrf g hgf] at hpq
      rcases consec_undrop (x := x) hpq with ⟨rfl, rfl⟩ | hpq'
      · exact ⟨e₁, hfresh⟩
      · obtain ⟨g', hg'⟩ := hadj p q hpq'
        have hxl : x ∉ z :: l := (List.nodup_cons.1 (List.nodup_cons.1 hn).2).1
        rcases hpq with ⟨rfl, rfl⟩ | hpq
        · exact ⟨e₁, hfresh⟩
        · exact ⟨g', hkeep g' p q hg' (fun h => hxl (h ▸ hpq.mem.1))
            (fun h => hxl (h ▸ hpq.mem.2))⟩
    · rw [hrg g hgf] at hpq
      obtain ⟨g', hg'⟩ := isChain_iff_consec.1 (hs.chain g hg) p q hpq
      exact ⟨g', hkeep g' p q hg' (fun h => hxg g hg hgf (h ▸ hpq.mem.1))
        (fun h => hxg g hg hgf (h ▸ hpq.mem.2))⟩
  · intro g hg y hy
    by_cases hgf : g = f
    · simp only [hgf, ite_true] at hy
      exact hs.inner_notMem f hf y (hin ▸ List.mem_cons_of_mem _ hy)
    · rw [hrg g hgf] at hy
      exact hs.inner_notMem g hg y hy
  · have hsub : ∀ g, ∀ y ∈ (if g = f then (⟨a, rest, b⟩ : Route α) else r g).inner,
        y ∈ (r g).inner := by
      intro g y hy
      by_cases hgf : g = f
      · simp only [hgf, ite_true] at hy
        rw [hgf, hin]
        exact List.mem_cons_of_mem _ hy
      · rwa [hrg g hgf] at hy
    intro g hg g' hg' hgg' y hy hy'
    exact hs.disjoint g hg g' hg' hgg' y (hsub g y hy) (hsub g' y hy')
  · intro y hy
    rcases hs.cover y hy.1 with h | ⟨g, hg, hyg⟩
    · exact Or.inl h
    · refine Or.inr ⟨g, hg, ?_⟩
      by_cases hgf : g = f
      · simp only [hgf, ite_true]
        subst hgf
        rw [hin] at hyg
        rcases List.mem_cons.1 hyg with rfl | h
        · exact (hy.2 rfl).elim
        · exact h
      · rwa [hrg g hgf]
  · intro g p q hl
    by_cases hg1 : g = e₁
    · subst hg1
      refine ⟨f, hf, ?_⟩
      rw [hrf f rfl]
      rcases (d.fresh_isLink_iff p q).1 hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · obtain ⟨hK, _, hg2⟩ := hret g p q hl hg1
      obtain ⟨h, hh, hc⟩ := hs.edge_consec g p q hK
      refine ⟨h, hh, ?_⟩
      by_cases hhf : h = f
      · rw [hrf h hhf]
        subst hhf
        rw [hlist] at hc
        have hne1 : ∀ s t, K.IsLink g s t → ¬ (s = a ∧ t = x) := by
          rintro s t hst ⟨rfl, rfl⟩
          exact hg1 (hs.unique _ _ _ _ hst he₁)
        have hne2 : ∀ s t, K.IsLink g s t → ¬ (s = x ∧ t = z) := by
          rintro s t hst ⟨rfl, rfl⟩
          exact hg2 (hs.unique _ _ _ _ hst he₂)
        rcases hc with hc | hc
        · exact Or.inl (consec_drop hc (hne1 p q hK) (hne2 p q hK))
        · exact Or.inr (consec_drop hc (hne1 q p hK.symm) (hne2 q p hK.symm))
      · rwa [hrg h hhf]
  · intro g g' p q hl hl'
    by_cases hg1 : g = e₁ <;> by_cases hg1' : g' = e₁
    · rw [hg1, hg1']
    · subst hg1
      obtain ⟨hK', _, _⟩ := hret g' p q hl' hg1'
      rcases (d.fresh_isLink_iff p q).1 hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (hnoaz g' hK').elim
      · exact (hnoaz g' hK'.symm).elim
    · subst hg1'
      obtain ⟨hK, _, _⟩ := hret g p q hl hg1
      rcases (d.fresh_isLink_iff p q).1 hl' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (hnoaz g hK).elim
      · exact (hnoaz g hK.symm).elim
    · exact hs.unique g g' p q (hret g p q hl hg1).1 (hret g' p q hl' hg1').1

/-! ### No inner vertices left -/

/-- When every path is a single edge, `K` is isomorphic to `H` by the map that
sends each edge of `H` to the edge of its path. -/
theorem SubdivisionRoutes.isoFix_of_inner_eq_nil {K H : Graph α β} {r : β → Route α}
    (hpar : ∀ f g a b, H.IsLink f a b → H.IsLink g a b → f = g)
    (hs : SubdivisionRoutes K H r) (hnil : ∀ f ∈ E(H), (r f).inner = []) : IsoFix H K := by
  classical
  have hpair : ∀ f ∈ E(H), (r f).list = [(r f).start, (r f).finish] := by
    intro f hf
    simp [Route.list, hnil f hf]
  have hex : ∀ f ∈ E(H), ∃ e, K.IsLink e (r f).start (r f).finish := by
    intro f hf
    have h := hs.chain f hf
    rw [hpair f hf, List.isChain_pair] at h
    exact h
  let σ : β → β := fun f => if h : ∃ e, K.IsLink e (r f).start (r f).finish then h.choose else f
  have hσ : ∀ f ∈ E(H), K.IsLink (σ f) (r f).start (r f).finish := by
    intro f hf
    simp only [σ, hex f hf, ↓reduceDIte]
    exact (hex f hf).choose_spec
  have hV : V(H) = V(K) := by
    refine Set.Subset.antisymm hs.vertex_subset fun y hy => ?_
    rcases hs.cover y hy with h | ⟨f, hf, hyf⟩
    · exact h
    · rw [hnil f hf] at hyf
      exact (List.not_mem_nil hyf).elim
  refine ⟨σ, hV, ⟨fun f hf => (hσ f hf).edge_mem, ?_, ?_⟩, ?_⟩
  · intro f hf g hg hfg
    have h1 := hσ f hf
    have h2 := hσ g hg
    rw [hfg] at h1
    rcases h2.eq_and_eq_or_eq_and_eq h1 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · have := hs.link g hg
      rw [h3, h4] at this
      exact hpar f g _ _ (hs.link f hf) this
    · have := (hs.link g hg).symm
      rw [h3, h4] at this
      exact hpar f g _ _ (hs.link f hf) this
  · intro e he
    obtain ⟨p, q, hl⟩ := K.exists_isLink_of_mem_edgeSet he
    obtain ⟨f, hf, hc⟩ := hs.edge_consec e p q hl
    refine ⟨f, hf, ?_⟩
    rw [hpair f hf] at hc
    rcases hc with (⟨rfl, rfl⟩ | hc) | (⟨rfl, rfl⟩ | hc)
    · exact hs.unique _ _ _ _ (hσ f hf) hl
    · exact hc.elim
    · exact hs.unique _ _ _ _ (hσ f hf) hl.symm
    · exact hc.elim
  · intro f hf p q
    rw [(hs.link f hf).isLink_iff, (hσ f hf).isLink_iff]

/-! ### The induction -/

/-- If paths for the edges of `H` cover `K` exactly, then `K` suppresses to `H`.
Here `H` has no two edges with the same ends. -/
theorem SubdivisionRoutes.exists_reflTransGen {K H : Graph α β} {r : β → Route α}
    (hpar : ∀ f g a b, H.IsLink f a b → H.IsLink g a b → f = g)
    (hs : SubdivisionRoutes K H r) (hfin : (V(K) \ V(H)).Finite) :
    ∃ L, ReflTransGen IsSuppression K L ∧ IsoFix H L := by
  induction hn : (V(K) \ V(H)).ncard using Nat.strong_induction_on generalizing K r with
  | _ n ih =>
    by_cases hex : ∃ f ∈ E(H), (r f).inner ≠ []
    · obtain ⟨f, hf, hne⟩ := hex
      obtain ⟨x, rest, hin⟩ := List.exists_cons_of_ne_nil hne
      obtain ⟨d, rfl, hxH, r', hs'⟩ := hs.step hpar hf hin
      have hxK : d.vertex ∈ V(K) := d.first_link.left_mem
      have heq : V(d.result) \ V(H) = (V(K) \ V(H)) \ {d.vertex} := by
        ext y
        simp only [Set.mem_sdiff, Set.mem_singleton_iff]
        change (y ∈ V(K) ∧ y ∉ ({d.vertex} : Set α)) ∧ y ∉ V(H) ↔ _
        simp only [Set.mem_singleton_iff]
        tauto
      have hfin' : (V(d.result) \ V(H)).Finite := heq ▸ hfin.subset Set.sdiff_subset
      have hlt : (V(d.result) \ V(H)).ncard < n := by
        rw [heq, ← hn]
        exact Set.ncard_sdiff_singleton_lt_of_mem ⟨hxK, hxH⟩ hfin
      obtain ⟨L, hsL, hiso⟩ := ih _ hlt hs' hfin' rfl
      exact ⟨L, ReflTransGen.head ⟨d, rfl⟩ hsL, hiso⟩
    · push Not at hex
      exact ⟨K, ReflTransGen.refl, hs.isoFix_of_inner_eq_nil hpar hex⟩

end GraphMinor.GM02
