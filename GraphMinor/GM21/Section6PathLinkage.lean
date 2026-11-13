module

public import GraphMinor.GM21.Section6Separation
import GraphMinor.GM21.NestedSeparations
import GraphMinor.GM21.LinkagePaths

/-!
# Graph Minors XXI, proof of (6.4): disjoint paths give a linkage

Claim (3) of the proof of (6.4) (page 25 of the preprint) gives "$|X(F)|$ mutually
vertex-disjoint paths of $B(F) \cap A(F')$ between $X(F)$ and $X(F')$", and (2.6) asks for a
linkage `M` in `B ∩ A'` whose pattern consists of the pairs of ends of these paths. This file
turns `k` mutually vertex-disjoint paths of the skeleton of a graph `K` into such a linkage
(`exists_linkage_of_hasDisjointPaths`): for each step of each path we keep one edge of `K`
joining the two vertices, and the union of the paths is the linkage.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Hypergraph GraphMinor.GM10

universe u v

variable {α : Type u} {β : Type v}

/-- The skeleton of `subOn K W F` grows with `W` and `F`. -/
theorem skeleton_subOn_mono {K : Hypergraph α β} {W W' : Set α} {F F' : Set β} (hW : W ⊆ W')
    (hF : F ⊆ F') : (subOn K W F).skeleton ≤ (subOn K W' F').skeleton := by
  rintro x y ⟨hne, e, hx, hy⟩
  exact ⟨hne, e, ⟨hx.1, hF hx.2.1, hW hx.2.2⟩, ⟨hy.1, hF hy.2.1, hW hy.2.2⟩⟩

/-- An edge of a graph with two different ends `a, c` has exactly the ends `a, c`. -/
theorem ends_eq_pair {K : Hypergraph α β} (hK : K.IsGraph) {e : β} (he : e ∈ K.edgeSet)
    {a c : α} (hac : a ≠ c) (ha : K.Inc e a) (hc : K.Inc e c) : K.ends e = {a, c} := by
  symm
  apply eq_of_subset_of_ncard_le
  · rintro x (rfl | rfl)
    exacts [ha, hc]
  · rw [ncard_pair hac]
    exact (hK e he).2
  · exact K.vertexSet_finite.subset fun x hx => K.vertex_mem_of_inc hx

open Classical in
/-- **One path.** For a path `w` of the skeleton of a graph `K` from `a` to `b`, there is a set
`E` of edges of `K`, one for each step of `w`, such that each edge of `E` has two ends, both on
`w`; each vertex `v` of `w` is incident with `[v ≠ a] + [v ≠ b]` edges of `E`; and every vertex
of `w` is reachable from `a` in the subgraph formed by `w` and `E`. -/
theorem exists_edges_of_isPath {K : Hypergraph α β} (hK : K.IsGraph) {a b : α}
    (w : K.skeleton.Walk a b) (hw : w.IsPath) :
    ∃ E : Set β, E ⊆ K.edgeSet ∧ (∀ e ∈ E, K.ends e ⊆ {x | x ∈ w.support}) ∧
      (∀ e ∈ E, (K.ends e).ncard = 2) ∧
      (∀ v ∈ w.support, {e ∈ E | K.Inc e v}.ncard =
        (if v = a then 0 else 1) + (if v = b then 0 else 1)) ∧
      ∀ v ∈ w.support, (subOn K {x | x ∈ w.support} E).skeleton.Reachable a v := by
  classical
  induction w with
  | nil =>
    refine ⟨∅, empty_subset _, fun e he => he.elim, fun e he => he.elim, ?_, ?_⟩
    · intro v hv
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
      subst hv
      simp
    · intro v hv
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
      subst hv
      exact SimpleGraph.Reachable.refl _
  | @cons a c b hadj w' ih =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hw
    obtain ⟨E', hE'K, hE'ends, hE'two, hE'deg, hE'reach⟩ := ih hw.1
    obtain ⟨hac, e, hea, hec⟩ := id hadj
    have heK : e ∈ K.edgeSet := K.edge_mem_of_inc hea
    have hends : K.ends e = {a, c} := ends_eq_pair hK heK hac hea hec
    have haw' : a ∉ w'.support := hw.2
    have heE' : e ∉ E' := fun h => haw' (hE'ends e h hea)
    have hsupp : {x | x ∈ (SimpleGraph.Walk.cons hadj w').support} =
        insert a {x | x ∈ w'.support} := by
      ext x
      simp
    refine ⟨insert e E', insert_subset heK hE'K, ?_, ?_, ?_, ?_⟩
    · rw [hsupp]
      rintro f (rfl | hf)
      · rw [hends]
        exact insert_subset_insert (singleton_subset_iff.2 w'.start_mem_support)
      · exact (hE'ends f hf).trans (subset_insert _ _)
    · rintro f (rfl | hf)
      · rw [hends, ncard_pair hac]
      · exact hE'two f hf
    · intro v hv
      have hbw' : b ∈ w'.support := w'.end_mem_support
      have hab : a ≠ b := fun h => haw' (h ▸ hbw')
      have hset : {f ∈ insert e E' | K.Inc f v} =
          (if K.Inc e v then insert e {f ∈ E' | K.Inc f v} else {f ∈ E' | K.Inc f v}) := by
        ext f
        split_ifs with h
        · simp only [mem_ofPred_eq, mem_insert_iff]
          constructor
          · rintro ⟨rfl | hf, hfv⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hf, hfv⟩
          · rintro (rfl | ⟨hf, hfv⟩)
            · exact ⟨Or.inl rfl, h⟩
            · exact ⟨Or.inr hf, hfv⟩
        · simp only [mem_ofPred_eq, mem_insert_iff]
          constructor
          · rintro ⟨rfl | hf, hfv⟩
            · exact absurd hfv h
            · exact ⟨hf, hfv⟩
          · rintro ⟨hf, hfv⟩
            exact ⟨Or.inr hf, hfv⟩
      have hfin : {f ∈ E' | K.Inc f v}.Finite :=
        K.edgeSet_finite.subset fun f hf => hE'K hf.1
      have hnot : e ∉ {f ∈ E' | K.Inc f v} := fun h => heE' h.1
      rw [hset]
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · have hinc : K.Inc e v := hea
        rw [ite_eq_left hinc, ncard_insert_of_notMem hnot hfin]
        have hempty : {f ∈ E' | K.Inc f v} = ∅ := by
          ext f
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
          exact fun hf hfv => haw' (hE'ends f hf hfv)
        rw [hempty, ncard_empty, ite_eq_left rfl, ite_eq_right hab]
      · have hva : v ≠ a := fun h => haw' (h ▸ hv)
        rw [ite_eq_right hva]
        by_cases hvc : v = c
        · subst hvc
          rw [ite_eq_left hec, ncard_insert_of_notMem hnot hfin, hE'deg v hv, ite_eq_left rfl]
          omega
        · have hinc : ¬ K.Inc e v := by
            intro h
            have : v ∈ K.ends e := h
            rw [hends] at this
            rcases this with h' | h'
            exacts [hva h', hvc h']
          rw [ite_eq_right hinc, hE'deg v hv, ite_eq_right hvc]
    · intro v hv
      have hle := skeleton_subOn_mono (K := K) (subset_insert a {x | x ∈ w'.support})
        (subset_insert e E')
      have hadj' : (subOn K (insert a {x | x ∈ w'.support}) (insert e E')).skeleton.Adj a c :=
        ⟨hac, e, ⟨hea, Or.inl rfl, Or.inl rfl⟩, ⟨hec, Or.inl rfl, Or.inr w'.start_mem_support⟩⟩
      rw [hsupp]
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact SimpleGraph.Reachable.refl _
      · exact hadj'.reachable.trans ((hE'reach v hv).mono hle)

/-- **Disjoint paths give a linkage.** If a graph `K` has `k` mutually vertex-disjoint paths of
its skeleton from `X ⊆ V(K)` to `Y`, then there is a linkage `M` in `K` with `k` components, each
with pattern block `{u, w}` for some `u ∈ X` and `w ∈ Y`. -/
theorem exists_linkage_of_hasDisjointPaths {K : Hypergraph α β} (hK : K.IsGraph) {X Y : Set α}
    (hX : X ⊆ K.vertexSet) {k : ℕ} (h : HasDisjointPaths K.skeleton X Y k) :
    ∃ M : Hypergraph α β, IsLinkage K M ∧ (linkagePattern M).ncard = k ∧
      ∀ P ∈ linkagePattern M, ∃ u ∈ X, ∃ w ∈ Y, P = {u, w} := by
  classical
  obtain ⟨P, hdisj⟩ := h
  choose E hEK hEends hEtwo hEdeg hEreach using fun i => exists_edges_of_isPath hK (P i).walk
    (P i).isPath
  set supp : Fin k → Set α := fun i => {x | x ∈ (P i).walk.support} with hsupp_def
  have hsuppK : ∀ i, supp i ⊆ K.vertexSet := fun i x hx =>
    mem_vertexSet_of_mem_walk_support (hX (P i).first_mem) (P i).walk hx
  set M := subOn K (⋃ i, supp i) (⋃ i, E i) with hM_def
  have hEW : ∀ e ∈ ⋃ i, E i, e ∈ K.edgeSet → K.ends e ⊆ ⋃ i, supp i := by
    intro e he _
    obtain ⟨i, hi⟩ := mem_iUnion.1 he
    exact (hEends i e hi).trans (subset_iUnion supp i)
  have hMK : M ≤ K := subOn_le hEW
  -- The edges of `M` at a vertex of the `i`th path are the edges of `E i` there.
  have hunique : ∀ i j, ∀ v ∈ supp i, ∀ e ∈ E j, K.Inc e v → j = i := by
    intro i j v hv e he hev
    by_contra hji
    exact Set.disjoint_left.mp (hdisj hji) (hEends j e he hev) hv
  have hinc : ∀ i, ∀ v ∈ supp i, incidentEdges M v = {e ∈ E i | K.Inc e v} := by
    intro i v hv
    ext e
    simp only [incidentEdges, hM_def, subOn, mem_ofPred_eq, mem_inter_iff, mem_iUnion]
    constructor
    · rintro ⟨-, hev, ⟨j, hj⟩, -⟩
      obtain rfl := hunique i j v hv e hj hev
      exact ⟨hj, hev⟩
    · rintro ⟨he, hev⟩
      exact ⟨⟨⟨i, he⟩, hEK i he⟩, hev, ⟨i, he⟩, ⟨i, hv⟩⟩
  have hdeg : ∀ i, ∀ v ∈ supp i, (incidentEdges M v).ncard =
      (if v = (P i).first then 0 else 1) + (if v = (P i).last then 0 else 1) := by
    intro i v hv
    rw [hinc i v hv]
    exact hEdeg i v hv
  have hMV : ∀ v ∈ M.vertexSet, ∃ i, v ∈ supp i := fun v hv => mem_iUnion.1 hv.1
  have hends2 : ∀ e ∈ M.edgeSet, (M.ends e).ncard = 2 := by
    intro e he
    rw [← hMK.ends_eq e he]
    obtain ⟨i, hi⟩ := mem_iUnion.1 he.1
    exact hEtwo i e hi
  have hMgraph : M.IsGraph := by
    intro e he
    have h2 := hends2 e he
    exact ⟨nonempty_of_ncard_ne_zero (by omega), by omega⟩
  have hreach : ∀ i, ∀ v ∈ supp i, M.skeleton.Reachable (P i).first v := fun i v hv =>
    (hEreach i v hv).mono (skeleton_subOn_mono (subset_iUnion supp i) (subset_iUnion E i))
  have hfirst : ∀ i, (P i).first ∈ supp i := fun i => (P i).walk.start_mem_support
  have hlast : ∀ i, (P i).last ∈ supp i := fun i => (P i).walk.end_mem_support
  have hmemM : ∀ i, ∀ v ∈ supp i, v ∈ M.vertexSet := fun i v hv =>
    ⟨mem_iUnion.2 ⟨i, hv⟩, hsuppK i hv⟩
  have hL : IsLinkage K M := by
    apply isLinkage_of_deg_le_two_of_reachable_deg_le_one hMK hends2
    · intro v hv
      obtain ⟨i, hi⟩ := hMV v hv
      rw [hdeg i v hi]
      split_ifs <;> omega
    · intro v hv
      obtain ⟨i, hi⟩ := hMV v hv
      refine ⟨(P i).first, hmemM i _ (hfirst i), (hreach i v hi).symm, ?_⟩
      rw [hdeg i _ (hfirst i), ite_eq_left rfl]
      split_ifs <;> omega
  -- The vertices reachable from a vertex of the `i`th path are those of the `i`th path.
  have hreachSet : ∀ i, ∀ w ∈ supp i, reachSet M w = supp i := by
    intro i w hw
    apply Subset.antisymm
    · rintro x ⟨-, ⟨p⟩⟩
      have key : ∀ {a b : α} (q : M.skeleton.Walk a b), a ∈ supp i → b ∈ supp i := by
        intro a b q
        induction q with
        | nil => exact id
        | @cons a c b hadj q' ih =>
          intro ha
          obtain ⟨-, e, hea, hec⟩ := hadj
          have heE : e ∈ E i := by
            have : e ∈ incidentEdges M a := ⟨M.edge_mem_of_inc hea, hea⟩
            rw [hinc i a ha] at this
            exact this.1
          exact ih (hEends i e heE hec.1)
      exact key p hw
    · intro x hx
      exact ⟨hmemM i x hx, (hreach i w hw).symm.trans (hreach i x hx)⟩
  -- The terminals of `M` on the `i`th path are its two ends.
  have hterm : ∀ i, terminals M ∩ supp i = {(P i).first, (P i).last} := by
    intro i
    ext v
    simp only [terminals, IsTerminal, mem_inter_iff, mem_ofPred_eq, mem_insert_iff,
      mem_singleton_iff]
    have hvd : ∀ v ∈ supp i, vertexDegree M v = (incidentEdges M v).ncard := by
      intro v _
      unfold vertexDegree
      have hemp : {e ∈ incidentEdges M v | (M.ends e).Subsingleton} = ∅ := by
        ext e
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro he hsub
        have h2 := hends2 e he.1
        rcases hsub.eq_empty_or_singleton with h0 | ⟨a, ha⟩
        · rw [h0, ncard_empty] at h2
          omega
        · rw [ha, ncard_singleton] at h2
          omega
      rw [hemp, ncard_empty, add_zero]
    constructor
    · rintro ⟨⟨-, hle⟩, hv⟩
      rw [hvd v hv, hdeg i v hv] at hle
      by_contra hne
      push Not at hne
      rw [ite_eq_right hne.1, ite_eq_right hne.2] at hle
      omega
    · rintro (rfl | rfl)
      · refine ⟨⟨hmemM i _ (hfirst i), ?_⟩, hfirst i⟩
        rw [hvd _ (hfirst i), hdeg i _ (hfirst i), ite_eq_left rfl]
        split_ifs <;> omega
      · refine ⟨⟨hmemM i _ (hlast i), ?_⟩, hlast i⟩
        rw [hvd _ (hlast i), hdeg i _ (hlast i), ite_eq_left rfl]
        split_ifs <;> omega
  have hpattern : linkagePattern M = range fun i => ({(P i).first, (P i).last} : Set α) := by
    ext B
    constructor
    · rintro ⟨C, hC, rfl⟩
      obtain ⟨w, hw⟩ := hC.2.1
      obtain ⟨i, hi⟩ := hMV w (hC.1.vertexSet_subset hw)
      refine ⟨i, ?_⟩
      rw [eq_componentOf_of_isComponentOf hMgraph hC hw]
      show _ = terminals M ∩ reachSet M w
      rw [hreachSet i w hi, hterm i]
    · rintro ⟨i, rfl⟩
      refine ⟨componentOf M (P i).first,
        (isComponentOf_componentOf hMgraph (hmemM i _ (hfirst i))).1, ?_⟩
      show _ = terminals M ∩ reachSet M (P i).first
      rw [hreachSet i _ (hfirst i), hterm i]
  refine ⟨M, hL, ?_, ?_⟩
  · rw [hpattern, ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
    intro i j hij
    by_contra hne
    have : (P i).first ∈ ({(P j).first, (P j).last} : Set α) := by
      have hij' : ({(P i).first, (P i).last} : Set α) = {(P j).first, (P j).last} := hij
      rw [← hij']
      exact Or.inl rfl
    have hj : (P i).first ∈ supp j := by
      rcases this with h | h
      · rw [h]; exact hfirst j
      · rw [h]; exact hlast j
    exact Set.disjoint_left.mp (hdisj hne) (hfirst i) hj
  · rw [hpattern]
    rintro B ⟨i, rfl⟩
    exact ⟨(P i).first, (P i).first_mem, (P i).last, (P i).last_mem, rfl⟩

end GM21
end GraphMinor
