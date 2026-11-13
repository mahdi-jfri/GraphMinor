module

public import GraphMinor.GM02.Section4FeasibleForward
public import GraphMinor.GM02.Section4Subdivision

/-!
# Graph Minors II, (4.5)

Page 319 of Graph Minors II says that it is "easy to see" that `G`
topologically contains `H` if and only if `(G', 𝒜)` is feasible. The forward
direction is in `Section4FeasibleForward.lean`.

For the converse, take disjoint paths of `G'` from `sᵢ` to `tᵢ`. Their inner
vertices lie in `Y = V(G) - V(H)`, because the other new vertices are ends of
other paths. Applying `g` to the `i`-th path gives a path of `G` from `uᵢ` to
`vᵢ` whose inner vertices avoid `V(H)`. For each pair of consecutive vertices
we pick one edge of `G` joining them. The union of these paths is a subgraph
`K` of `G`, and `Section4Subdivision.lean` shows that suppressing the inner
vertices turns `K` into `H`.

The converse is false as printed (see the correction to (4.5) in `corrections/GM02.md`). If `H` has
two edges with the same ends `u, v`, both paths may be the single edges `s₁t₁` and `s₂t₂` of `G'`,
which use the same edge `uv` of `G` twice. If `H` has a loop at `u`, its path may be `s₁, y, t₁`,
which uses the same edge `uy` of `G` twice. So we add the hypotheses that `H` has no loops and no
two edges with the same ends. These are exactly what makes the picked edges distinct.
-/

@[expose] public section

namespace GraphMinor.GM02

open Graph Set Relation SimpleGraph Classical

universe u v

variable {α : Type u} {β : Type v}

/-- Every vertex after the first one in a list has a predecessor. -/
theorem exists_consec_of_mem {a y : α} {l : List α} (hy : y ∈ l) : ∃ w, Consec (a :: l) w y := by
  induction l generalizing a with
  | nil => exact (List.not_mem_nil hy).elim
  | cons c l ih =>
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨a, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨w, hw⟩ := ih (a := c) hy
      exact ⟨w, Or.inr hw⟩

/-- The support of a walk between distinct vertices, split into its ends and
its inner vertices. -/
theorem Walk.exists_support_eq {V : Type*} {F : SimpleGraph V} {a b : V} (w : F.Walk a b)
    (hab : a ≠ b) : ∃ m : List V, w.support = a :: (m ++ [b]) := by
  cases w with
  | nil => exact (hab rfl).elim
  | cons h w' =>
    refine ⟨w'.support.dropLast, ?_⟩
    have := List.dropLast_append_getLast (Walk.support_ne_nil w')
    rw [Walk.getLast_support] at this
    rw [Walk.support_cons, this]

/-- A path joining `a` and `b`, as a list starting at `a`. -/
theorem PairPath.exists_list {V : Type*} {F : SimpleGraph V} {a b : V} (P : PairPath F s(a, b))
    (hab : a ≠ b) : ∃ m : List V, (a :: (m ++ [b])).Nodup ∧ (a :: (m ++ [b])).IsChain F.Adj ∧
      ∀ y, y ∈ a :: (m ++ [b]) ↔ y ∈ P.vertices := by
  rcases Sym2.eq_iff.1 P.ends_eq with ⟨hs, hf⟩ | ⟨hs, hf⟩
  · obtain ⟨m, hm⟩ := Walk.exists_support_eq (P.walk.copy hs hf) hab
    rw [Walk.support_copy] at hm
    refine ⟨m, ?_, ?_, fun y => ?_⟩
    · rw [← hm]
      exact P.isPath.support_nodup
    · rw [← hm]
      exact P.walk.isChain_adj_support
    · change _ ↔ y ∈ P.walk.support
      rw [hm]
  · obtain ⟨m, hm⟩ := Walk.exists_support_eq (P.walk.copy hs hf) hab.symm
    rw [Walk.support_copy] at hm
    have hrev : a :: (m.reverse ++ [b]) = P.walk.support.reverse := by
      rw [hm]
      simp
    refine ⟨m.reverse, ?_, ?_, fun y => ?_⟩
    · rw [hrev]
      exact List.nodup_reverse.2 P.isPath.support_nodup
    · rw [hrev]
      exact List.isChain_reverse.2 (P.walk.isChain_adj_support.imp fun _ _ h => h.symm)
    · change _ ↔ y ∈ P.walk.support
      rw [hrev, List.mem_reverse]

/-- The pair `(sᵢ, tᵢ)` as an element of the termination. -/
def splitPair (G H : Graph α β) {k : ℕ} (edge : Fin k ≃ E(H)) (i : Fin k) :
    {p // p ∈ (splitTermination G H edge).pairs} :=
  ⟨s(splitS i, splitT i), Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩

/-- An edge of `G` joining the two vertices of an unordered pair, if one exists. -/
noncomputable def pickEdge (G : Graph α β) (z : Sym2 α) : Option β :=
  if h : ∃ e, ∃ p q, z = s(p, q) ∧ G.IsLink e p q then some h.choose else none

theorem pickEdge_spec {G : Graph α β} {p q : α} {e : β} (h : pickEdge G s(p, q) = some e) :
    G.IsLink e p q := by
  unfold pickEdge at h
  split_ifs at h with hex
  · cases h
    obtain ⟨p', q', hpq, hl⟩ := hex.choose_spec
    rcases Sym2.eq_iff.1 hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hl
    · exact hl.symm

theorem pickEdge_exists {G : Graph α β} {p q : α} (h : G.Adj p q) :
    ∃ e, pickEdge G s(p, q) = some e := by
  unfold pickEdge
  obtain ⟨e, he⟩ := h
  have hex : ∃ e, ∃ p' q', s(p, q) = s(p', q') ∧ G.IsLink e p' q' := ⟨e, p, q, rfl, he⟩
  exact ⟨hex.choose, by simp only [hex, ↓reduceDIte]⟩

/-- The converse direction of Graph Minors II, (4.5), page 319, for `H` with no
loops and no two edges with the same ends. -/
theorem topologicallyContains_of_splitFeasible {G H : Graph α β} {k : ℕ} (edge : Fin k ≃ E(H))
    (hVH : V(H) ⊆ V(G)) (hloop : ∀ f a, ¬ H.IsLoopAt f a)
    (hpar : ∀ f g a b, H.IsLink f a b → H.IsLink g a b → f = g)
    (hF : (splitTermination G H edge).Feasible (splitGraph G H edge)) :
    TopologicallyContains G H := by
  by_cases hα : Nonempty α
  swap
  · exact topologicallyContains_of_le ⟨hVH, fun _ x _ _ => (hα ⟨x⟩).elim⟩
  obtain ⟨P, hPd⟩ := hF
  set g := splitMap H edge with hg
  have hpair : ∀ i j, i ≠ j → splitPair G H edge i ≠ splitPair G H edge j := by
    intro i j hij h
    have h' := congrArg Subtype.val h
    simp only [splitPair, Sym2.eq_iff, splitS, splitT, Sum.inr.injEq, Prod.mk.injEq,
      reduceCtorEq, and_false, or_false, Bool.false_eq_true] at h'
    exact hij h'.1.1
  have hst : ∀ i : Fin k, (splitS i : α ⊕ (Fin k × Bool)) ≠ splitT i := by
    intro i h
    simp [splitS, splitT] at h
  -- The path of the `i`-th pair as a list.
  have hlist := fun i => (P (splitPair G H edge i)).exists_list (hst i)
  choose m hmn hmc hmv using hlist
  have hsplitMem : ∀ i, ∀ c, c ∈ splitS i :: (m i ++ [splitT i]) →
      c ∈ (P (splitPair G H edge i)).vertices := fun i c hc => (hmv i c).1 hc
  -- Inner vertices of the paths are old vertices outside `V(H)`.
  have hinl : ∀ i, ∀ c ∈ m i, ∃ y, c = Sum.inl y ∧ y ∈ V(G) ∧ y ∉ V(H) := by
    intro i c hc
    have hct : c ∈ m i ++ [splitT i] := List.mem_append_left _ hc
    obtain ⟨w, hw⟩ := exists_consec_of_mem (a := splitS i) hct
    have hadj := isChain_iff_consec.1 (hmc i) w c hw
    have hcV := ((splitGraph_adj_iff G H edge w c).1 hadj.1).2.1
    rcases hcV with ⟨y, hy, rfl⟩ | ⟨⟨j, bb⟩, rfl⟩
    · exact ⟨y, rfl, hy⟩
    · exfalso
      have hci : Sum.inr (j, bb) ∈ (P (splitPair G H edge i)).vertices :=
        hsplitMem i _ (List.mem_cons_of_mem _ hct)
      by_cases hji : j = i
      · subst hji
        have hnd := hmn j
        rw [List.nodup_cons, List.nodup_append] at hnd
        cases bb
        · exact hnd.1 (List.mem_append_left _ hc)
        · exact hnd.2.2.2 _ hc _ List.mem_cons_self rfl
      · have hcj : Sum.inr (j, bb) ∈ (P (splitPair G H edge j)).vertices := by
          apply PairPath.endpoint_mem
          cases bb
          · exact Sym2.mem_mk_left _ _
          · exact Sym2.mem_mk_right _ _
        exact Set.disjoint_left.1 (hPd _ _ (hpair i j (Ne.symm hji))) hci hcj
  let ys : Fin k → List α := fun i => (m i).map g
  have hm_eq : ∀ i, m i = (ys i).map Sum.inl := by
    intro i
    simp only [ys, List.map_map]
    conv_lhs => rw [← List.map_id (m i)]
    apply List.map_congr_left
    intro c hc
    obtain ⟨y, rfl, -⟩ := hinl i c hc
    rfl
  have hysV : ∀ i, ∀ y ∈ ys i, y ∈ V(G) ∧ y ∉ V(H) := by
    intro i y hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
    obtain ⟨y', rfl, hy'⟩ := hinl i c hc
    exact hy'
  let ρ : Fin k → Route α := fun i => ⟨(splitEnds H edge i).1, ys i, (splitEnds H edge i).2⟩
  have hρlist : ∀ i, (ρ i).list = (splitList i (ys i)).map g := fun i =>
    (map_splitList H edge i (ys i)).symm
  have hsl : ∀ i, splitList i (ys i) = splitS i :: (m i ++ [splitT i]) := by
    intro i
    rw [hm_eq i]
    rfl
  -- The paths of `G`.
  have hchainG : ∀ i, (ρ i).list.IsChain G.Adj := by
    intro i
    rw [hρlist i, List.isChain_map, hsl i]
    exact (hmc i).imp fun a b h => ((splitGraph_adj_iff G H edge a b).1 h.1).2.2.2
  have huv : ∀ i, (splitEnds H edge i).1 ≠ (splitEnds H edge i).2 := by
    intro i h
    have hl := splitEnds_isLink H edge i
    rw [← h] at hl
    exact hloop _ _ hl
  have hnodup : ∀ i, (ρ i).list.Nodup := by
    intro i
    rw [hρlist i]
    refine List.Nodup.map_on ?_ (hsl i ▸ hmn i)
    have hl := splitEnds_isLink H edge i
    intro a ha b hb hab
    rcases mem_splitList.1 ha with rfl | ⟨y, hy, rfl⟩ | rfl <;>
      rcases mem_splitList.1 hb with rfl | ⟨z, hz, rfl⟩ | rfl
    · rfl
    · have h : (splitEnds H edge i).1 = z := hab
      exact ((hysV i z hz).2 (h ▸ hl.left_mem)).elim
    · exact (huv i hab).elim
    · have h : y = (splitEnds H edge i).1 := hab
      exact ((hysV i y hy).2 (h ▸ hl.left_mem)).elim
    · exact congrArg Sum.inl hab
    · have h : y = (splitEnds H edge i).2 := hab
      exact ((hysV i y hy).2 (h ▸ hl.right_mem)).elim
    · exact (huv i hab.symm).elim
    · have h : (splitEnds H edge i).2 = z := hab
      exact ((hysV i z hz).2 (h ▸ hl.right_mem)).elim
    · rfl
  have hdisj : ∀ i j, i ≠ j → ∀ y ∈ ys i, y ∉ ys j := by
    intro i j hij y hyi hyj
    have hi : Sum.inl y ∈ (P (splitPair G H edge i)).vertices :=
      hsplitMem i _ (hsl i ▸ mem_splitList.2 (Or.inr (Or.inl ⟨y, hyi, rfl⟩)))
    have hj : Sum.inl y ∈ (P (splitPair G H edge j)).vertices :=
      hsplitMem j _ (hsl j ▸ mem_splitList.2 (Or.inr (Or.inl ⟨y, hyj, rfl⟩)))
    exact Set.disjoint_left.1 (hPd _ _ (hpair i j hij)) hi hj
  -- The routes, indexed by edges of `H`.
  let r : β → Route α := fun e => if he : e ∈ E(H) then ρ (edge.symm ⟨e, he⟩)
    else ⟨Classical.arbitrary α, [], Classical.arbitrary α⟩
  have hr : ∀ i, r (edge i) = ρ i := by
    intro i
    simp only [r, (edge i).2, ↓reduceDIte, Subtype.coe_eta, Equiv.symm_apply_apply]
  have hidx : ∀ f ∈ E(H), ∃ i, (edge i).val = f :=
    fun f hf => ⟨edge.symm ⟨f, hf⟩, by simp⟩
  -- The subgraph `K` of `G`.
  let W : Set α := V(H) ∪ {y | ∃ i, y ∈ ys i}
  let F : Set β := {e | ∃ i p q, Consec (ρ i).list p q ∧ pickEdge G s(p, q) = some e}
  let K : Graph α β := (G.induce W).restrict F
  have hKlink : ∀ e p q, K.IsLink e p q ↔ e ∈ F ∧ G.IsLink e p q ∧ p ∈ W ∧ q ∈ W :=
    fun _ _ _ => Iff.rfl
  have hWG : W ⊆ V(G) := by
    rintro y (hy | ⟨i, hy⟩)
    · exact hVH hy
    · exact (hysV i y hy).1
  have hρW : ∀ i, ∀ y ∈ (ρ i).list, y ∈ W := by
    intro i y hy
    rcases Route.mem_list.1 hy with rfl | hy | rfl
    · exact Or.inl (splitEnds_isLink H edge i).left_mem
    · exact Or.inr ⟨i, hy⟩
    · exact Or.inl (splitEnds_isLink H edge i).right_mem
  have hF_link : ∀ e ∈ F, ∀ p q, G.IsLink e p q →
      ∃ i p' q', Consec (ρ i).list p' q' ∧ pickEdge G s(p', q') = some e ∧
        s(p', q') = s(p, q) := by
    rintro e ⟨i, p', q', hc, hpick⟩ p q hl
    refine ⟨i, p', q', hc, hpick, ?_⟩
    rcases (pickEdge_spec hpick).eq_and_eq_or_eq_and_eq hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap
  have hs : SubdivisionRoutes K H r := by
    refine ⟨Set.subset_union_left, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro f hf
      obtain ⟨i, rfl⟩ := hidx f hf
      rw [hr i]
      exact splitEnds_isLink H edge i
    · intro f hf
      obtain ⟨i, rfl⟩ := hidx f hf
      rw [hr i]
      exact hnodup i
    · intro f hf
      obtain ⟨i, rfl⟩ := hidx f hf
      rw [hr i, isChain_iff_consec]
      intro p q hpq
      obtain ⟨e, he⟩ := pickEdge_exists (isChain_iff_consec.1 (hchainG i) p q hpq)
      exact ⟨e, (hKlink e p q).2 ⟨⟨i, p, q, hpq, he⟩, pickEdge_spec he,
        hρW i p hpq.mem.1, hρW i q hpq.mem.2⟩⟩
    · intro f hf y hy
      obtain ⟨i, rfl⟩ := hidx f hf
      rw [hr i] at hy
      exact (hysV i y hy).2
    · intro f hf f' hf' hff' y hy hy'
      obtain ⟨i, rfl⟩ := hidx f hf
      obtain ⟨j, rfl⟩ := hidx f' hf'
      rw [hr i] at hy
      rw [hr j] at hy'
      exact hdisj i j (fun h => hff' (h ▸ rfl)) y hy hy'
    · rintro y (hy | ⟨i, hy⟩)
      · exact Or.inl hy
      · exact Or.inr ⟨edge i, (edge i).2, by rw [hr i]; exact hy⟩
    · intro e p q hl
      obtain ⟨hF, hlG, -, -⟩ := (hKlink e p q).1 hl
      obtain ⟨i, p', q', hc, -, heq⟩ := hF_link e hF p q hlG
      refine ⟨edge i, (edge i).2, ?_⟩
      rw [hr i]
      rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl hc
      · exact Or.inr hc
    · intro e e' p q hl hl'
      obtain ⟨hF, hlG, -, -⟩ := (hKlink e p q).1 hl
      obtain ⟨hF', hlG', -, -⟩ := (hKlink e' p q).1 hl'
      obtain ⟨_, p₁, q₁, -, hpick, heq⟩ := hF_link e hF p q hlG
      obtain ⟨_, p₂, q₂, -, hpick', heq'⟩ := hF_link e' hF' p q hlG'
      rw [heq] at hpick
      rw [heq'] at hpick'
      exact Option.some_injective _ (hpick.symm.trans hpick')
  have hfin : (V(K) \ V(H)).Finite := by
    apply (Set.finite_iUnion fun i => (ys i).finite_toSet).subset
    rintro y ⟨hy | ⟨i, hy⟩, hyH⟩
    · exact (hyH hy).elim
    · exact Set.mem_iUnion.2 ⟨i, hy⟩
  obtain ⟨L, hsL, hiso⟩ := hs.exists_reflTransGen hpar hfin
  exact topologicallyContains_iff_isoFix.2
    ⟨K, Graph.restrict_le.trans (Graph.induce_le hWG), L, hsL, hiso⟩

/-- Graph Minors II, (4.5), page 319:
"*$G$ topologically contains $H$ if and only if $(G', \mathcal{A})$ is feasible.*"

Here `(G', 𝒜)` is `splitGraph G H edge` with `splitTermination G H edge`, built in
`Section4Split.lean` from the enumeration `edge` of the edges of `H`. The paper says the result is
"easy to see". As printed it is false when `H` has a loop or two edges with the same ends (see the
correction to (4.5) in `corrections/GM02.md`), so we add the hypotheses `hHloop` and `hHpar`. The
hypotheses printed before (4.4) are `hVH` and `_hGloop`. The forward direction uses none of them.
The converse uses `hVH`, `hHloop` and `hHpar`, but not `_hGloop`. -/
theorem theorem_4_5_proof {G H : Graph α β} {k : ℕ} (edge : Fin k ≃ E(H)) (hVH : V(H) ⊆ V(G))
    (_hGloop : ∀ e a, a ∈ V(H) → ¬ G.IsLoopAt e a)
    (hHloop : ∀ f a, ¬ H.IsLoopAt f a)
    (hHpar : ∀ f g a b, H.IsLink f a b → H.IsLink g a b → f = g) :
    TopologicallyContains G H ↔ (splitTermination G H edge).Feasible (splitGraph G H edge) :=
  ⟨splitFeasible_of_topologicallyContains edge,
    topologicallyContains_of_splitFeasible edge hVH hHloop hHpar⟩

end GraphMinor.GM02
