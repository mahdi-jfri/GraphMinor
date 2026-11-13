module

public import GraphMinor.Compute.MultiDigraph
public import GraphMinor.Compute.BranchDecomp
public import GraphMinor.Compute.Algorithm33
public import GraphMinor.Compute.Algorithm41Comb

/-!
# Combinatorial Reductions for GM XIII Algorithm (3.3) on Multigraphs

This file formalizes the combinatorial reductions needed to extend Algorithm (3.3) of
Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem* (pages 72–75) from simple
graphs to general multigraphs (`MultiDigraph n`), and provides the branch-decomposition encoding
definitions shared with `Join2.lean`:

1. **Multigraph-to-`ComputeDigraph` bridge and `IsValidBranchDecompCode`:**
   - `MultiDigraph.edgeListWithMult`, `MultiDigraph.edgeEndpoints`, `MultiDigraph.toMultiComputeDigraph`,
     `MultiDigraph.toMultiComputeRootedDigraph`.
   - `IsMultiBranchDecompOfWidthLe`, `encBranchDecomp`, `bdNumTreeVerts`, `bdNumGraphEdges`,
     `bdParent`, `bdTree`, `bdTau`, `IsValidBranchDecompCode`, `IsAlg33HighWidthCase`.
2. **High-branch-width subgraph lifting (`H₃ ≠ H₁`):**
   - `liftSimpleSubgraph G H` selects one directed edge of `G` for each undirected edge of a simple
     subgraph `H ≤ G.toSimpleGraph`, satisfying `liftSimpleSubgraph G H ≤ G`,
     `(liftSimpleSubgraph G H).toSimpleGraph = H`, and preserving branch-decompositions of width
     `≤ 3ω`.
3. **Branch-decomposition conversion (`H₂ = H₁`, `G' = G`):**
   - Formalizes the paper's last step (page 73): "If $H_2 = H_1$, we convert our
     branch-decomposition to one for $G$, set $G' = G$, and stop", by expanding each simple-edge
     leaf into a binary subtree for its parallel edges and attached loops while preserving width
     `≤ 3ω` (for `ω ≥ 2`) and tree size `|V(T)| ≤ 2|E(G)|`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 3: High-Branch-Width Subgraph Lifting (`H₃ ≠ H₁`) -/

/-- Lift a simple subgraph `H ≤ G.toSimpleGraph` to a subgraph `liftSimpleSubgraph G H ≤ G` by
selecting one directed edge `(u, v)` or `(v, u)` of `G` for each simple edge `{u, v}` of `H`. -/
def liftSimpleSubgraph {n : ℕ} (G : MultiDigraph n) (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] : MultiDigraph n where
  edgeMult u v :=
    if H.Adj u v then
      if u.1 < v.1 then
        if 0 < G.edgeMult u v then 1 else 0
      else if v.1 < u.1 then
        if 0 < G.edgeMult v u then 0 else if 0 < G.edgeMult u v then 1 else 0
      else 0
    else 0

theorem liftSimpleSubgraph_le {n : ℕ} (G : MultiDigraph n) (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] :
    liftSimpleSubgraph G H ≤ G := by
  intro u v
  unfold liftSimpleSubgraph
  dsimp only
  split_ifs <;> omega

theorem liftSimpleSubgraph_edgeMult_self {n : ℕ} (G : MultiDigraph n) (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] (u : Fin n) :
    (liftSimpleSubgraph G H).edgeMult u u = 0 := by
  simp [liftSimpleSubgraph]

theorem liftSimpleSubgraph_edgeMult_add_eq {n : ℕ} (G : MultiDigraph n) (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] (hsub : H ≤ G.toSimpleGraph) (u v : Fin n) :
    (liftSimpleSubgraph G H).edgeMult u v + (liftSimpleSubgraph G H).edgeMult v u =
      if H.Adj u v then 1 else 0 := by
  by_cases hadj : H.Adj u v
  · have hadj_symm : H.Adj v u := hadj.symm
    have hG : G.toSimpleGraph.Adj u v := hsub hadj
    rw [G.toSimpleGraph_adj] at hG
    rcases hG with ⟨hne, hpos⟩
    have hne_val : u.1 ≠ v.1 := Fin.val_ne_of_ne hne
    unfold liftSimpleSubgraph
    dsimp only
    simp only [hadj, hadj_symm, ↓reduceIte]
    rcases Nat.lt_or_gt_of_ne hne_val with hlt | hgt
    · have hnot_gt : ¬ v.1 < u.1 := by omega
      simp only [hlt, hnot_gt, ↓reduceIte]
      rcases hpos with h1 | h2 <;> split_ifs <;> omega
    · have hnot_lt : ¬ u.1 < v.1 := by omega
      simp only [hgt, hnot_lt, ↓reduceIte]
      rcases hpos with h1 | h2 <;> split_ifs <;> omega
  · have hadj_symm : ¬ H.Adj v u := fun h => hadj h.symm
    simp [liftSimpleSubgraph, hadj, hadj_symm]

theorem liftSimpleSubgraph_edgeMult_add_le_one {n : ℕ} (G : MultiDigraph n)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (hsub : H ≤ G.toSimpleGraph) (u v : Fin n) :
    (liftSimpleSubgraph G H).edgeMult u v + (liftSimpleSubgraph G H).edgeMult v u ≤ 1 := by
  rw [liftSimpleSubgraph_edgeMult_add_eq G H hsub u v]
  split_ifs <;> omega

@[simp]
theorem toSimpleGraph_liftSimpleSubgraph {n : ℕ} (G : MultiDigraph n) (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] (hsub : H ≤ G.toSimpleGraph) :
    (liftSimpleSubgraph G H).toSimpleGraph = H := by
  ext u v
  rw [MultiDigraph.toSimpleGraph_adj]
  have hsum := liftSimpleSubgraph_edgeMult_add_eq G H hsub u v
  by_cases hadj : H.Adj u v
  · rw [ite_eq_left_iff.mpr fun h => absurd hadj h] at hsum
    exact ⟨fun _ => hadj, fun _ => ⟨H.ne_of_adj hadj, by omega⟩⟩
  · rw [ite_eq_right_iff.mpr fun h => absurd h hadj] at hsum
    exact ⟨fun ⟨_, h⟩ => by omega, fun h => absurd h hadj⟩

/-- Directed edge chosen in `G` for an upper-triangular simple edge `e = (u, v)` (`u.1 < v.1`). -/
def liftEdgeDir {n : ℕ} (G : MultiDigraph n) (e : Fin n × Fin n) : Fin n × Fin n :=
  if 0 < G.edgeMult e.1 e.2 then (e.1, e.2) else (e.2, e.1)

@[simp]
theorem sym2_liftEdgeDir {n : ℕ} (G : MultiDigraph n) (e : Fin n × Fin n) :
    s((liftEdgeDir G e).1, (liftEdgeDir G e).2) = s(e.1, e.2) := by
  unfold liftEdgeDir
  split_ifs <;> simp [Sym2.eq_swap]

/-- Two sublists of a `Nodup` list with the same membership are equal. -/
theorem sublist_eq_of_nodup_of_mem_iff {α : Type*} {M L₁ L₂ : List α}
    (hM : M.Nodup) (h₁ : List.Sublist L₁ M) (h₂ : List.Sublist L₂ M)
    (hmem : ∀ x, x ∈ L₁ ↔ x ∈ L₂) :
    L₁ = L₂ := by
  induction M generalizing L₁ L₂ with
  | nil =>
    rw [List.sublist_nil.mp h₁, List.sublist_nil.mp h₂]
  | cons a M ih =>
    rcases List.nodup_cons.mp hM with ⟨ha_not, hM_nodup⟩
    cases h₁ with
    | cons _ h₁' =>
      cases h₂ with
      | cons _ h₂' =>
        exact ih hM_nodup h₁' h₂' hmem
      | cons_cons _ h₂' =>
        exfalso
        exact ha_not (h₁'.subset ((hmem a).mpr List.mem_cons_self))
    | cons_cons _ h₁' =>
      cases h₂ with
      | cons _ h₂' =>
        exfalso
        exact ha_not (h₂'.subset ((hmem a).mp List.mem_cons_self))
      | cons_cons _ h₂' =>
        congr 1
        refine ih hM_nodup h₁' h₂' fun x => ?_
        constructor
        · intro hx₁
          have hne : x ≠ a := fun h => ha_not (h ▸ h₁'.subset hx₁)
          exact (List.mem_cons.mp ((hmem x).mp (List.mem_cons_of_mem a hx₁))).resolve_left hne
        · intro hx₂
          have hne : x ≠ a := fun h => ha_not (h ▸ h₂'.subset hx₂)
          exact (List.mem_cons.mp ((hmem x).mpr (List.mem_cons_of_mem a hx₂))).resolve_left hne

theorem filter_map_eq_flatMap {α β : Type*} (l : List α) (p : α → Bool) (f : α → β) :
    (l.filter p).map f = l.flatMap (fun x => if p x then [f x] else []) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases h : p x
    · simp only [List.filter_cons, h, Bool.false_eq_true, ↓reduceIte, List.flatMap_cons,
        List.nil_append, ih]
    · simp only [List.filter_cons, h, ↓reduceIte, List.map_cons, List.flatMap_cons,
        List.singleton_append, ih]

theorem flatMap_replicate_eq_self {α : Type*} (l : List α) (f : α → ℕ)
    (hf : ∀ x ∈ l, f x = 1) :
    l.flatMap (fun x => List.replicate (f x) x) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, hf x List.mem_cons_self, List.replicate_one,
      List.singleton_append]
    congr 1
    exact ih (fun y hy => hf y (List.mem_cons_of_mem x hy))

theorem activePairsList_liftSimpleSubgraph {n : ℕ} (G : MultiDigraph n)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (hsub : H ≤ G.toSimpleGraph) :
    (liftSimpleSubgraph G H).activePairsList = (edgeListOf H).map (liftEdgeDir G) := by
  have h1 : (liftSimpleSubgraph G H).activePairsList =
      (upperPairs n).flatMap (fun e =>
        ((if e.1 = e.2 then [(e.1, e.1)] else [(e.1, e.2), (e.2, e.1)]).filter
          (fun p => decide (0 < (liftSimpleSubgraph G H).edgeMult p.1 p.2)))) := by
    unfold MultiDigraph.activePairsList allDirectedPairs
    rw [List.filter_flatMap]
  have h2 : (edgeListOf H).map (liftEdgeDir G) =
      (upperPairs n).flatMap (fun e =>
        if decide (e.1.1 < e.2.1 ∧ H.Adj e.1 e.2) then [liftEdgeDir G e] else []) := by
    have hed : edgeListOf H = (upperPairs n).filter (fun e => decide (e.1.1 < e.2.1 ∧ H.Adj e.1 e.2)) := by
      unfold edgeListOf upperPairs
      rw [List.filter_filter]
      congr 1
      funext e
      rw [← Bool.decide_and]
      exact decide_eq_decide.mpr ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, h2⟩, Nat.le_of_lt h1⟩, fun ⟨⟨h1, h2⟩, _⟩ => ⟨h1, h2⟩⟩
    rw [hed, filter_map_eq_flatMap]
  rw [h1, h2]
  refine List.flatMap_congr fun ⟨u, v⟩ huv => ?_
  rw [mem_upperPairs] at huv
  dsimp only at huv ⊢
  by_cases heq : u = v
  · subst heq
    simp only [↓reduceIte, List.filter, liftSimpleSubgraph_edgeMult_self, Nat.lt_irrefl,
      false_and, decide_false, Bool.false_eq_true]
  · have hlt : u.1 < v.1 := Nat.lt_of_le_of_ne huv (Fin.val_ne_of_ne heq)
    have hnot_gt : ¬ v.1 < u.1 := by omega
    by_cases hadj : H.Adj u v
    · have hadj_symm : H.Adj v u := hadj.symm
      have hG : G.toSimpleGraph.Adj u v := hsub hadj
      rw [G.toSimpleGraph_adj] at hG
      rcases hG with ⟨_, hpos⟩
      by_cases hmult : 0 < G.edgeMult u v
      · have h_uv : (liftSimpleSubgraph G H).edgeMult u v = 1 := by
          unfold liftSimpleSubgraph; dsimp only
          simp only [hadj, hlt, hmult, ↓reduceIte]
        have h_vu : (liftSimpleSubgraph G H).edgeMult v u = 0 := by
          unfold liftSimpleSubgraph; dsimp only
          simp only [hadj_symm, hnot_gt, hlt, hmult, ↓reduceIte]
        simp [heq, hlt, hadj, liftEdgeDir, hmult, h_uv, h_vu]
      · have hmult_vu : 0 < G.edgeMult v u := hpos.resolve_left hmult
        have h_uv : (liftSimpleSubgraph G H).edgeMult u v = 0 := by
          unfold liftSimpleSubgraph; dsimp only
          simp only [hadj, hlt, hmult, ↓reduceIte]
        have h_vu : (liftSimpleSubgraph G H).edgeMult v u = 1 := by
          unfold liftSimpleSubgraph; dsimp only
          simp only [hadj_symm, hnot_gt, hlt, hmult, hmult_vu, ↓reduceIte]
        simp [heq, hlt, hadj, liftEdgeDir, hmult, h_uv, h_vu]
    · have hadj_symm : ¬ H.Adj v u := fun h => hadj h.symm
      have h_uv : (liftSimpleSubgraph G H).edgeMult u v = 0 := by
        unfold liftSimpleSubgraph; dsimp only; simp only [hadj, ↓reduceIte]
      have h_vu : (liftSimpleSubgraph G H).edgeMult v u = 0 := by
        unfold liftSimpleSubgraph; dsimp only; simp only [hadj_symm, ↓reduceIte]
      simp [heq, hlt, hadj, h_uv, h_vu]

theorem edgeMult_eq_one_of_mem_activePairsList_liftSimpleSubgraph {n : ℕ} (G : MultiDigraph n)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (hsub : H ≤ G.toSimpleGraph)
    {p : Fin n × Fin n} (hp : p ∈ (liftSimpleSubgraph G H).activePairsList) :
    (liftSimpleSubgraph G H).edgeMult p.1 p.2 = 1 := by
  have hpos := ((liftSimpleSubgraph G H).mem_activePairsList p).mp hp
  have hle := liftSimpleSubgraph_edgeMult_add_le_one G H hsub p.1 p.2
  omega

theorem edgeListWithMult_liftSimpleSubgraph {n : ℕ} (G : MultiDigraph n)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (hsub : H ≤ G.toSimpleGraph) :
    (liftSimpleSubgraph G H).edgeListWithMult = (edgeListOf H).map (liftEdgeDir G) := by
  have hact : (liftSimpleSubgraph G H).edgeListWithMult =
      (liftSimpleSubgraph G H).activePairsList := by
    unfold MultiDigraph.edgeListWithMult
    exact flatMap_replicate_eq_self _ _ fun p hp =>
      edgeMult_eq_one_of_mem_activePairsList_liftSimpleSubgraph G H hsub hp
  rw [hact, activePairsList_liftSimpleSubgraph G H hsub]

theorem numEdges_liftSimpleSubgraph {n : ℕ} (G : MultiDigraph n)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (hsub : H ≤ G.toSimpleGraph) :
    (liftSimpleSubgraph G H).numEdges = (edgeListOf H).length := by
  rw [← (liftSimpleSubgraph G H).length_edgeListWithMult,
      edgeListWithMult_liftSimpleSubgraph G H hsub, List.length_map]

theorem card_edgeFinset_toSimpleGraph_le_numEdges {n : ℕ} (G : MultiDigraph n) :
    (edgeListOf G.toSimpleGraph).length ≤ G.numEdges := by
  rw [← numEdges_liftSimpleSubgraph G G.toSimpleGraph (le_refl _)]
  exact MultiDigraph.numEdges_mono (liftSimpleSubgraph_le G G.toSimpleGraph)

/-- Enumeration of the alive edge indices `< k` in `edges₂`. -/
def aliveIndicesUpTo {m₂ : ℕ} (aliveSet : Finset (Fin m₂)) (k : ℕ) : List (Fin m₂) :=
  (List.finRange m₂).filter (fun j => decide (j.1 < k ∧ j ∈ aliveSet))

theorem aliveIndicesUpTo_self {m₂ : ℕ} (aliveSet : Finset (Fin m₂)) :
    aliveIndicesUpTo aliveSet m₂ = (List.finRange m₂).filter (· ∈ aliveSet) := by
  unfold aliveIndicesUpTo
  congr 1
  funext j
  simp [j.2]

theorem mem_aliveIndicesUpTo {m₂ : ℕ} (aliveSet : Finset (Fin m₂)) (k : ℕ) (j : Fin m₂) :
    j ∈ aliveIndicesUpTo aliveSet k ↔ j.1 < k ∧ j ∈ aliveSet := by
  simp [aliveIndicesUpTo]

theorem nodup_aliveIndicesUpTo {m₂ : ℕ} (aliveSet : Finset (Fin m₂)) (k : ℕ) :
    (aliveIndicesUpTo aliveSet k).Nodup :=
  (List.nodup_finRange m₂).filter _

theorem length_aliveIndicesUpTo_self {m₂ : ℕ} (aliveSet : Finset (Fin m₂)) :
    (aliveIndicesUpTo aliveSet m₂).length = aliveSet.card := by
  have h1 : (aliveIndicesUpTo aliveSet m₂).toFinset = aliveSet := by
    ext j
    simp [mem_aliveIndicesUpTo, j.2]
  rw [← List.toFinset_card_of_nodup (nodup_aliveIndicesUpTo aliveSet m₂), h1]

/-- For `H₃ = graphOfAlive edges₂ hloop₂ aliveSet` where `edges₂ = (edgeListOf H₁).take m₂`,
`edgeListOf H₃` is directly the sublist of `edges₂` at `aliveIndicesUpTo aliveSet edges₂.length`. -/
theorem edgeListOf_graphOfAlive_eq {n : ℕ} (H₁ : SimpleGraph (Fin n)) [DecidableRel H₁.Adj]
    (m₂ : ℕ)
    (aliveSet : Finset (Fin ((edgeListOf H₁).take m₂).length)) :
    let edges₂ := (edgeListOf H₁).take m₂
    let hloop₂ := take_loopless_of_isSimpleEdgeList (isSimpleEdgeList_edgeListOf H₁) m₂
    edgeListOf (graphOfAlive edges₂ hloop₂ aliveSet) =
      (aliveIndicesUpTo aliveSet edges₂.length).map (fun j => edges₂[j.1]'j.2) := by
  intro edges₂ hloop₂
  apply sublist_eq_of_nodup_of_mem_iff (nodup_allPairs n)
  · exact List.filter_sublist
  · have hmap : edges₂ = (List.finRange edges₂.length).map (fun j => edges₂[j.1]'j.2) := by
      apply List.ext_getElem (by simp)
      intro i hi1 hi2
      simp
    have hsub0 : List.Sublist (aliveIndicesUpTo aliveSet edges₂.length) (List.finRange edges₂.length) :=
      List.filter_sublist
    have hsub1 : List.Sublist
        ((aliveIndicesUpTo aliveSet edges₂.length).map (fun j => edges₂[j.1]'j.2))
        ((List.finRange edges₂.length).map (fun j => edges₂[j.1]'j.2)) :=
      hsub0.map _
    rw [← hmap] at hsub1
    exact hsub1.trans ((List.take_sublist _ _).trans List.filter_sublist)
  · intro ⟨u, v⟩
    rw [mem_edgeListOf, List.mem_map]
    constructor
    · rintro ⟨hlt, k, hk_al, ⟨rfl, rfl⟩ | ⟨hu_eq, hv_eq⟩⟩
      · exact ⟨k, (mem_aliveIndicesUpTo aliveSet edges₂.length k).mpr ⟨k.2, hk_al⟩, rfl⟩
      · exfalso
        have hmem_e1 : edges₂[k.1]'k.2 ∈ edgeListOf H₁ :=
          List.mem_of_mem_take (List.getElem_mem k.2)
        rw [mem_edgeListOf] at hmem_e1
        have hlt_k : (edges₂[k.1]'k.2).1.1 < (edges₂[k.1]'k.2).2.1 := hmem_e1.1
        rw [hu_eq, hv_eq] at hlt_k
        omega
    · rintro ⟨k, hk, heq⟩
      rw [mem_aliveIndicesUpTo] at hk
      have hmem_e1 : edges₂[k.1]'k.2 ∈ edgeListOf H₁ :=
        List.mem_of_mem_take (List.getElem_mem k.2)
      rw [mem_edgeListOf] at hmem_e1
      rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      exact ⟨hmem_e1.1, k, hk.2, Or.inl ⟨rfl, rfl⟩⟩

/-- Branch-decomposition equivalence between `H₃ = graphOfAlive edges₂ hloop₂ aliveSet` and
`G' = liftSimpleSubgraph G H₃`. -/
theorem isMultiBranchDecompOfWidthLe_liftSimpleSubgraph {n t : ℕ} (ω : ℕ)
    (G : MultiDigraph n) (m₂ : ℕ) (ht_pos : 0 < t)
    (aliveSet : Finset (Fin ((edgeListOf G.toSimpleGraph).take m₂).length))
    (f_tau : Fin ((edgeListOf G.toSimpleGraph).take m₂).length → Fin t)
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj]
    (hbd : IsBranchDecompOfWidthLe ω
      (graphOfAlive ((edgeListOf G.toSimpleGraph).take m₂)
        (take_loopless_of_isSimpleEdgeList (isSimpleEdgeList_edgeListOf G.toSimpleGraph) m₂)
        aliveSet)
      T
      (tauOfArr ((edgeListOf G.toSimpleGraph).take m₂) t ht_pos f_tau)) :
    let edges₂ := (edgeListOf G.toSimpleGraph).take m₂
    let hloop₂ := take_loopless_of_isSimpleEdgeList (isSimpleEdgeList_edgeListOf G.toSimpleGraph) m₂
    let H₃ := graphOfAlive edges₂ hloop₂ aliveSet
    let G' := liftSimpleSubgraph G H₃
    let idxList := aliveIndicesUpTo aliveSet edges₂.length
    have hlen : G'.numEdges = idxList.length := by
      rw [numEdges_liftSimpleSubgraph G H₃
            ((graphOfAlive_le_graphOfEdgeList edges₂ hloop₂ aliveSet).trans
              (graphOfEdgeList_take_le (isSimpleEdgeList_edgeListOf G.toSimpleGraph) m₂)),
          edgeListOf_graphOfAlive_eq, List.length_map]
    IsMultiBranchDecompOfWidthLe ω G' T
      (fun e : Fin G'.numEdges => f_tau (idxList[e.1]'(by rw [← hlen]; exact e.2))) := by
  intro edges₂ hloop₂ H₃ G' idxList hlen
  have hedges₁ : IsSimpleEdgeList G.toSimpleGraph (edgeListOf G.toSimpleGraph) :=
    isSimpleEdgeList_edgeListOf G.toSimpleGraph
  have hedges₂ : IsSimpleEdgeList (graphOfEdgeList edges₂ hloop₂) edges₂ :=
    isSimpleEdgeList_take hedges₁ m₂
  have hH₃_le : H₃ ≤ G.toSimpleGraph :=
    (graphOfAlive_le_graphOfEdgeList edges₂ hloop₂ aliveSet).trans
      (graphOfEdgeList_take_le hedges₁ m₂)
  have hed_G' : G'.edgeListWithMult =
      idxList.map (fun j => liftEdgeDir G (edges₂[j.1]'j.2)) := by
    rw [edgeListWithMult_liftSimpleSubgraph G H₃ hH₃_le,
        edgeListOf_graphOfAlive_eq G.toSimpleGraph m₂ aliveSet, List.map_map]
    rfl
  let τ' : Fin G'.numEdges → Fin t :=
    fun e => f_tau (idxList[e.1]'(by rw [← hlen]; exact e.2))
  let τ_H : Sym2 (Fin n) → Fin t := tauOfArr edges₂ t ht_pos f_tau
  change IsDigraphBranchDecompOfWidthLe ω G'.toMultiComputeDigraph T τ'
  have hsym_eq : ∀ e : Fin G'.numEdges,
      s((G'.edgeEndpoints e).1, (G'.edgeEndpoints e).2) =
        symEdgeAt edges₂ (idxList[e.1]'(by rw [← hlen]; exact e.2)) := by
    intro e
    have hget : G'.edgeEndpoints e =
        liftEdgeDir G (edges₂[(idxList[e.1]'(by rw [← hlen]; exact e.2)).1]'
          (idxList[e.1]'(by rw [← hlen]; exact e.2)).2) := by
      unfold MultiDigraph.edgeEndpoints
      simp [hed_G']
    rw [hget, sym2_liftEdgeDir, symEdgeAt]
  have htau_eq : ∀ e : Fin G'.numEdges,
      τ' e = τ_H (s((G'.edgeEndpoints e).1, (G'.edgeEndpoints e).2)) := by
    intro e
    dsimp only [τ', τ_H]
    rw [hsym_eq e, tauOfArr_symEdgeAt hedges₂]
  have hinc_iff : ∀ (w : Fin n) (e : Fin G'.numEdges),
      digraphIncident G'.toMultiComputeDigraph w e ↔
        w ∈ s((G'.edgeEndpoints e).1, (G'.edgeEndpoints e).2) := by
    intro w e
    unfold digraphIncident
    dsimp [MultiDigraph.toMultiComputeDigraph]
    rw [Sym2.mem_iff, or_comm]
    exact ⟨fun h => h.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm),
           fun h => h.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm)⟩
  have hmem_H₃ : ∀ e : Fin G'.numEdges,
      s((G'.edgeEndpoints e).1, (G'.edgeEndpoints e).2) ∈ H₃.edgeFinset := by
    intro e
    rw [hsym_eq e, mem_edgeFinset_graphOfAlive_iff hedges₂]
    have hmem : idxList[e.1]'(by rw [← hlen]; exact e.2) ∈ idxList := List.getElem_mem _
    rw [mem_aliveIndicesUpTo] at hmem
    exact ⟨idxList[e.1]'(by rw [← hlen]; exact e.2), hmem.2, rfl⟩
  have hsurj_H₃ : ∀ g ∈ H₃.edgeFinset,
      ∃ e : Fin G'.numEdges, s((G'.edgeEndpoints e).1, (G'.edgeEndpoints e).2) = g := by
    intro g hg
    rw [mem_edgeFinset_graphOfAlive_iff hedges₂] at hg
    rcases hg with ⟨j, hj_al, rfl⟩
    have hj_mem : j ∈ idxList := (mem_aliveIndicesUpTo aliveSet edges₂.length j).mpr ⟨j.2, hj_al⟩
    rcases List.mem_iff_getElem.mp hj_mem with ⟨i, hi, hij⟩
    refine ⟨⟨i, by rw [hlen]; exact hi⟩, ?_⟩
    rw [hsym_eq]
    dsimp only
    rw [hij]
  rcases hbd with ⟨hcub, ⟨hmaps, hinj, hsurj⟩, hord⟩
  refine ⟨hcub, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro e _
    rw [htau_eq e]
    exact hmaps (hmem_H₃ e)
  · intro e₁ _ e₂ _ heq
    rw [htau_eq e₁, htau_eq e₂] at heq
    have hsym12 := hinj (hmem_H₃ e₁) (hmem_H₃ e₂) heq
    rw [hsym_eq e₁, hsym_eq e₂] at hsym12
    have hidx_eq : idxList[e₁.1]'(by rw [← hlen]; exact e₁.2) =
        idxList[e₂.1]'(by rw [← hlen]; exact e₂.2) :=
      symEdgeAt_injective hedges₂ hsym12
    exact Fin.ext (((nodup_aliveIndicesUpTo aliveSet edges₂.length).getElem_inj_iff).mp hidx_eq)
  · intro v hv
    rcases hsurj hv with ⟨g, hg_mem, rfl⟩
    rcases hsurj_H₃ g hg_mem with ⟨e, rfl⟩
    exact ⟨e, Set.mem_univ e, htau_eq e⟩
  · intro f hf
    have hcut_eq : digraphTreeEdgeCutVerts G'.toMultiComputeDigraph T τ' f =
        treeEdgeCutVerts H₃ T τ_H f := by
      ext w
      simp only [digraphTreeEdgeCutVerts, treeEdgeCutVerts, Finset.mem_filter, Finset.mem_univ,
        true_and, SimpleGraph.mem_edgeFinset]
      constructor
      · rintro ⟨e₁, e₂, hw₁, hw₂, hnr⟩
        rw [hinc_iff] at hw₁ hw₂
        rw [htau_eq e₁, htau_eq e₂] at hnr
        exact ⟨_, SimpleGraph.mem_edgeFinset.mp (hmem_H₃ e₁),
               _, SimpleGraph.mem_edgeFinset.mp (hmem_H₃ e₂), hw₁, hw₂, hnr⟩
      · rintro ⟨g₁, hg₁, g₂, hg₂, hw₁, hw₂, hnr⟩
        rcases hsurj_H₃ g₁ (SimpleGraph.mem_edgeFinset.mpr hg₁) with ⟨e₁, rfl⟩
        rcases hsurj_H₃ g₂ (SimpleGraph.mem_edgeFinset.mpr hg₂) with ⟨e₂, rfl⟩
        rw [← hinc_iff] at hw₁ hw₂
        rw [← htau_eq e₁, ← htau_eq e₂] at hnr
        exact ⟨e₁, e₂, hw₁, hw₂, hnr⟩
    unfold digraphTreeEdgeOrder treeEdgeOrder at *
    rw [hcut_eq]
    exact hord f hf

/-- When `H₃ ≠ G.toSimpleGraph`, `G' = liftSimpleSubgraph G H₃` satisfies `G' ≠ G` and
`IsAlg33HighWidthCase ω G G'`. -/
theorem isAlg33HighWidthCase_liftSimpleSubgraph {n : ℕ} (ω : ℕ) (G : MultiDigraph n)
    (H₃ G_step6 : SimpleGraph (Fin n)) [DecidableRel H₃.Adj] [DecidableRel G_step6.Adj]
    (g : Sym2 (Fin n)) (Z : Finset (Fin n))
    (hH₃_le : H₃ ≤ G.toSimpleGraph)
    (hne : H₃ ≠ G.toSimpleGraph)
    (hcase :
      H₃ = G.toSimpleGraph ∨
      (H₃ ≠ G.toSimpleGraph ∧
       (H₃.edgeFinset.card : ℚ) ≤ ((3 : ℚ) / 2 * (ω : ℚ) - 1) * (n : ℚ) + 1 ∧
       (H₃.edgeFinset.card : ℚ) > ((3 : ℚ) / 2 * (ω : ℚ) - 1) * (n : ℚ)) ∨
      (G_step6 ≤ G.toSimpleGraph ∧
       g ∈ G_step6.edgeFinset ∧
       Z.card = 3 * ω ∧
       H₃ ≤ G_step6.deleteEdges {g} ∧
       H₃ = G_step6.deleteEdges {g} ∧
       ∀ sep : GraphSeparation G_step6, sep.order ≤ ω → ¬ sep.IsBalancedQ Z)) :
    liftSimpleSubgraph G H₃ ≠ G ∧ IsAlg33HighWidthCase ω G (liftSimpleSubgraph G H₃) := by
  have hG'_sim : (liftSimpleSubgraph G H₃).toSimpleGraph = H₃ :=
    toSimpleGraph_liftSimpleSubgraph G H₃ hH₃_le
  have hG'_ne : liftSimpleSubgraph G H₃ ≠ G := by
    intro heq
    apply hne
    rw [← hG'_sim, heq]
  refine ⟨hG'_ne, liftSimpleSubgraph_edgeMult_self G H₃,
    liftSimpleSubgraph_edgeMult_add_le_one G H₃ hH₃_le, ?_⟩
  rcases hcase with heq | ⟨_, hle_q, hgt_q⟩ | ⟨hG6_le, hg_mem, hZ_card, hle_del, heq_del, hsep⟩
  · exact False.elim (hne heq)
  · left
    refine ⟨?_, ?_⟩
    · convert hle_q using 2
      congr 1
      ext e
      simp [SimpleGraph.mem_edgeFinset, hG'_sim]
    · convert hgt_q using 2
      congr 1
      ext e
      simp [SimpleGraph.mem_edgeFinset, hG'_sim]
  · right
    refine ⟨G_step6, g, Z, hG6_le, ?_, hZ_card, ?_, ?_, hsep⟩
    · convert hg_mem
    · rw [hG'_sim]; exact hle_del
    · rw [hG'_sim]; exact heq_del

/-! ### Section 4: Branch-Decomposition Expansion when `G' = G` -/

/-- Partial branch-decomposition invariant for a digraph `G : ComputeDigraph` (GM XIII (3.3),
pages 73–75):
(i) `T` is a tree in which every vertex has valency 1 or 3;
(ii) `τ` maps `Fin G.numEdges` surjectively onto `treeLeaves T`;
(iii) every edge `f ∈ T.edgeFinset` has `digraphTreeEdgeOrder G T τ f ≤ 3 * ω`. -/
def IsPartialDigraphBranchDecomp (ω : ℕ) {t : ℕ} (G : ComputeDigraph)
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] (τ : Fin G.numEdges → Fin t) : Prop :=
  IsCubicOrLeafTree T ∧
  (∀ e : Fin G.numEdges, τ e ∈ treeLeaves T) ∧
  (∀ v ∈ treeLeaves T, ∃ e : Fin G.numEdges, τ e = v) ∧
  (∀ f ∈ T.edgeFinset, digraphTreeEdgeOrder G T τ f ≤ 3 * ω)

/-- Any `IsPartialDigraphBranchDecomp` has `(treeLeaves T).card ≤ G.numEdges`. -/
theorem IsPartialDigraphBranchDecomp.card_treeLeaves_le {ω t : ℕ} {G : ComputeDigraph}
    {T : SimpleGraph (Fin t)} [DecidableRel T.Adj] {τ : Fin G.numEdges → Fin t}
    (hpart : IsPartialDigraphBranchDecomp ω G T τ) :
    (treeLeaves T).card ≤ G.numEdges := by
  have hsub : treeLeaves T ⊆ Finset.univ.image τ := by
    intro v hv
    rcases hpart.2.2.1 v hv with ⟨e, rfl⟩
    exact Finset.mem_image_of_mem τ (Finset.mem_univ e)
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

/-- When `τ` is injective, `IsPartialDigraphBranchDecomp ω G T τ` gives
`IsDigraphBranchDecompOfWidthLe (3 * ω) G T τ`. -/
theorem IsPartialDigraphBranchDecomp.to_isDigraphBranchDecompOfWidthLe {ω t : ℕ}
    {G : ComputeDigraph} {T : SimpleGraph (Fin t)} [DecidableRel T.Adj]
    {τ : Fin G.numEdges → Fin t}
    (hpart : IsPartialDigraphBranchDecomp ω G T τ)
    (hinj : Function.Injective τ) :
    IsDigraphBranchDecompOfWidthLe (3 * ω) G T τ := by
  refine ⟨hpart.1, ⟨fun e _ => hpart.2.1 e, fun e₁ _ e₂ _ h => hinj h, ?_⟩, hpart.2.2.2⟩
  intro v hv
  rcases hpart.2.2.1 v hv with ⟨e, rfl⟩
  exact ⟨e, Set.mem_univ e, rfl⟩

/-- The set of vertices of `G : ComputeDigraph` incident with both an edge mapped to `v` and an
edge not mapped to `v`. -/
def digraphLeafCutVerts {t : ℕ} (G : ComputeDigraph)
    (τ : Fin G.numEdges → Fin t) (v : Fin t) : Finset (Fin G.numVerts) :=
  Finset.univ.filter (fun w : Fin G.numVerts =>
    (∃ e₁ : Fin G.numEdges, digraphIncident G w e₁ ∧ τ e₁ = v) ∧
    (∃ e₂ : Fin G.numEdges, digraphIncident G w e₂ ∧ τ e₂ ≠ v))

@[simp]
theorem mem_digraphLeafCutVerts {t : ℕ} (G : ComputeDigraph)
    (τ : Fin G.numEdges → Fin t) (v : Fin t) (w : Fin G.numVerts) :
    w ∈ digraphLeafCutVerts G τ v ↔
      (∃ e₁ : Fin G.numEdges, digraphIncident G w e₁ ∧ τ e₁ = v) ∧
      (∃ e₂ : Fin G.numEdges, digraphIncident G w e₂ ∧ τ e₂ ≠ v) := by
  simp [digraphLeafCutVerts]

/-- For any leaf `v` of a connected graph `T` and its incident edge `s(u, v)`,
`digraphTreeEdgeCutVerts G T τ s(u, v) = digraphLeafCutVerts G τ v`. -/
theorem digraphTreeEdgeCutVerts_leaf_eq {t : ℕ} (G : ComputeDigraph)
    {T : SimpleGraph (Fin t)} [DecidableRel T.Adj] (hconn : T.Connected)
    (τ : Fin G.numEdges → Fin t) {u v : Fin t} (hdeg : T.degree v = 1) (hadj_uv : T.Adj u v) :
    digraphTreeEdgeCutVerts G T τ s(u, v) = digraphLeafCutVerts G τ v := by
  ext w
  rw [mem_digraphTreeEdgeCutVerts, mem_digraphLeafCutVerts]
  constructor
  · rintro ⟨e₁, e₂, hw₁, hw₂, hnr⟩
    rw [deleteEdges_leaf_reachable_iff hconn hdeg hadj_uv] at hnr
    by_cases h1 : τ e₁ = v
    · have h2 : τ e₂ ≠ v := fun h => hnr ⟨fun _ => h, fun _ => h1⟩
      exact ⟨⟨e₁, hw₁, h1⟩, ⟨e₂, hw₂, h2⟩⟩
    · have h2 : τ e₂ = v := by
        by_contra h2'
        exact hnr ⟨fun h => False.elim (h1 h), fun h => False.elim (h2' h)⟩
      exact ⟨⟨e₂, hw₂, h2⟩, ⟨e₁, hw₁, h1⟩⟩
  · rintro ⟨⟨e₁, hw₁, h1⟩, ⟨e₂, hw₂, h2⟩⟩
    refine ⟨e₁, e₂, hw₁, hw₂, ?_⟩
    rw [deleteEdges_leaf_reachable_iff hconn hdeg hadj_uv]
    intro hiff
    exact h2 (hiff.mp h1)

/-- Splitting a leaf `v` of `parentTree t p` into `⟨t, _⟩` and `⟨t + 1, _⟩` preserves
`IsPartialDigraphBranchDecomp`. -/
theorem isPartialDigraphBranchDecomp_splitLeaf {t ω : ℕ}
    {G : ComputeDigraph}
    {p : ℕ → ℕ} (ht : 0 < t) (hp : ∀ z, 0 < z → z < t → p z < z)
    {τ : Fin G.numEdges → Fin t}
    (hpart : IsPartialDigraphBranchDecomp ω G (parentTree t p) τ)
    {v : Fin t} (hv : v ∈ treeLeaves (parentTree t p))
    {τ' : Fin G.numEdges → Fin (t + 2)}
    (hτ'_ne : ∀ e : Fin G.numEdges, τ e ≠ v → (τ' e).1 = (τ e).1)
    (hτ'_eq : ∀ e : Fin G.numEdges, τ e = v → (τ' e).1 = t ∨ (τ' e).1 = t + 1)
    (hsurj_left : ∃ e : Fin G.numEdges, τ' e = ⟨t, by omega⟩)
    (hsurj_right : ∃ e : Fin G.numEdges, τ' e = ⟨t + 1, by omega⟩)
    (hord_left : (digraphLeafCutVerts G τ' ⟨t, by omega⟩).card ≤ 3 * ω)
    (hord_right : (digraphLeafCutVerts G τ' ⟨t + 1, by omega⟩).card ≤ 3 * ω) :
    IsPartialDigraphBranchDecomp ω G (parentTree (t + 2) (splitLeafParent p t v.1)) τ' := by
  let p' := splitLeafParent p t v.1
  have hp' : ∀ z, 0 < z → z < t + 2 → p' z < z := splitLeafParent_lt hp v.2
  have hcub' : IsCubicOrLeafTree (parentTree (t + 2) p') :=
    isCubicOrLeafTree_splitLeafParent hp ht hpart.1 hv
  refine ⟨hcub', ?_, ?_, ?_⟩
  · intro e
    rw [mem_treeLeaves_splitLeafParent_iff hp ht hv]
    by_cases hev : τ e = v
    · rcases hτ'_eq e hev with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
    · right; right
      have hval := hτ'_ne e hev
      refine ⟨by rw [hval]; exact (τ e).2, ?_, ?_⟩
      · have h_eq : (⟨(τ' e).1, by rw [hval]; exact (τ e).2⟩ : Fin t) = τ e := Fin.ext hval
        rw [h_eq]
        exact hpart.2.1 e
      · rw [hval]
        exact fun h => hev (Fin.ext h)
  · intro w hw
    rw [mem_treeLeaves_splitLeafParent_iff hp ht hv] at hw
    rcases hw with hwt | hwt1 | ⟨hw_lt, hw_leaf, hw_ne⟩
    · rcases hsurj_left with ⟨e, he_eq⟩
      exact ⟨e, he_eq.trans (Fin.ext hwt.symm)⟩
    · rcases hsurj_right with ⟨e, he_eq⟩
      exact ⟨e, he_eq.trans (Fin.ext hwt1.symm)⟩
    · rcases hpart.2.2.1 ⟨w.1, hw_lt⟩ hw_leaf with ⟨e, he_eq⟩
      have hev : τ e ≠ v := by
        intro h
        apply hw_ne
        exact congrArg Fin.val (he_eq.symm.trans h)
      refine ⟨e, Fin.ext ?_⟩
      rw [hτ'_ne e hev, congrArg Fin.val he_eq]
  · intro f hf
    rcases exists_pos_of_mem_edgeFinset_parentTree hp' hf with ⟨x, hx_pos, hf_eq⟩
    by_cases hx_lt : x.1 < t
    · let x₀ : Fin t := ⟨x.1, hx_lt⟩
      have hx₀_pos : 0 < x₀.1 := hx_pos
      have hsub_eq : ∀ e : Fin G.numEdges,
          inSubtree p' x.1 (τ' e).1 = inSubtree p x₀.1 (τ e).1 := by
        intro e
        by_cases hev : τ e = v
        · rcases hτ'_eq e hev with h1 | h2
          · rw [h1, inSubtree_splitLeafParent_left hp ht v.2 hx_lt, hev]
          · rw [h2, inSubtree_splitLeafParent_right hp v.2 hx_lt, hev]
        · rw [hτ'_ne e hev]
          exact inSubtree_splitLeafParent_of_lt hp v.2 hx_lt (τ e).1 (τ e).2
      let px₀ : Fin t := ⟨p x₀.1, Nat.lt_trans (hp x₀.1 hx₀_pos x₀.2) x₀.2⟩
      have hf₀_mem : s(px₀, x₀) ∈ (parentTree t p).edgeFinset := by
        rw [mem_edgeFinset, mem_edgeSet, parentTree_adj_of_lt hp]
        exact Or.inr ⟨hx₀_pos, rfl⟩
      have hcut_eq :
          digraphTreeEdgeCutVerts G (parentTree (t + 2) p') τ'
            s(⟨p' x.1, Nat.lt_trans (hp' x.1 hx_pos x.2) x.2⟩, x) =
          digraphTreeEdgeCutVerts G (parentTree t p) τ s(px₀, x₀) := by
        ext w
        rw [mem_digraphTreeEdgeCutVerts, mem_digraphTreeEdgeCutVerts]
        constructor
        · rintro ⟨e₁, e₂, hw₁, hw₂, hnr⟩
          rw [parentTree_deleteEdge_reachable_iff (by omega) hp' hx_pos] at hnr
          rw [hsub_eq e₁, hsub_eq e₂] at hnr
          rw [← parentTree_deleteEdge_reachable_iff ht hp hx₀_pos] at hnr
          exact ⟨e₁, e₂, hw₁, hw₂, hnr⟩
        · rintro ⟨e₁, e₂, hw₁, hw₂, hnr⟩
          rw [parentTree_deleteEdge_reachable_iff ht hp hx₀_pos] at hnr
          rw [← hsub_eq e₁, ← hsub_eq e₂] at hnr
          rw [← parentTree_deleteEdge_reachable_iff (by omega) hp' hx_pos] at hnr
          exact ⟨e₁, e₂, hw₁, hw₂, hnr⟩
      rw [hf_eq]
      unfold digraphTreeEdgeOrder
      rw [hcut_eq]
      exact hpart.2.2.2 s(px₀, x₀) hf₀_mem
    · have hconn' : (parentTree (t + 2) p').Connected :=
        parentTree_connected (by omega) hp'
      have hx_lt2 : x.1 < t + 2 := x.2
      rcases (by omega : x.1 = t ∨ x.1 = t + 1) with hxt | hxt1
      · have hx_eq : x = ⟨t, by omega⟩ := Fin.ext hxt
        have hdeg_t : (parentTree (t + 2) p').degree ⟨t, by omega⟩ = 1 :=
          degree_splitLeafParent_left hp ht v
        let pt : Fin (t + 2) := ⟨p' t, Nat.lt_trans (hp' t ht (by omega)) (by omega)⟩
        have hadj_t : (parentTree (t + 2) p').Adj pt ⟨t, by omega⟩ := by
          rw [parentTree_adj_of_lt hp']
          exact Or.inr ⟨ht, rfl⟩
        have hf_eq_t : f = s(pt, ⟨t, by omega⟩) := by
          rw [hf_eq]
          exact congrArg₂ (fun a b => s(a, b)) (Fin.ext (by simp [pt, hxt])) hx_eq
        rw [hf_eq_t]
        unfold digraphTreeEdgeOrder
        rw [digraphTreeEdgeCutVerts_leaf_eq G hconn' τ' hdeg_t hadj_t]
        exact hord_left
      · have hx_eq : x = ⟨t + 1, by omega⟩ := Fin.ext hxt1
        have hdeg_t1 : (parentTree (t + 2) p').degree ⟨t + 1, by omega⟩ = 1 :=
          degree_splitLeafParent_right hp v
        let pt1 : Fin (t + 2) :=
          ⟨p' (t + 1), Nat.lt_trans (hp' (t + 1) (by omega) (by omega)) (by omega)⟩
        have hadj_t1 : (parentTree (t + 2) p').Adj pt1 ⟨t + 1, by omega⟩ := by
          rw [parentTree_adj_of_lt hp']
          exact Or.inr ⟨by omega, rfl⟩
        have hf_eq_t1 : f = s(pt1, ⟨t + 1, by omega⟩) := by
          rw [hf_eq]
          exact congrArg₂ (fun a b => s(a, b)) (Fin.ext (by simp [pt1, hxt1])) hx_eq
        rw [hf_eq_t1]
        unfold digraphTreeEdgeOrder
        rw [digraphTreeEdgeCutVerts_leaf_eq G hconn' τ' hdeg_t1 hadj_t1]
        exact hord_right

/-- Number of edges `e : Fin m` with `k ≤ e.1` and `σ₀ e = l`. -/
def remAfter {m t₀ : ℕ} (σ₀ : Fin m → Fin t₀) (k : ℕ) (l : Fin t₀) : ℕ :=
  (Finset.univ.filter (fun e : Fin m => k ≤ e.1 ∧ σ₀ e = l)).card

theorem remAfter_pos_of_eq {m t₀ : ℕ} (σ₀ : Fin m → Fin t₀) {k : ℕ} (hk : k < m) :
    0 < remAfter σ₀ k (σ₀ ⟨k, hk⟩) := by
  unfold remAfter
  exact Finset.card_pos.mpr ⟨⟨k, hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, rfl⟩⟩

theorem remAfter_step_eq {m t₀ : ℕ} (σ₀ : Fin m → Fin t₀) {k : ℕ} (hk : k < m) :
    remAfter σ₀ k (σ₀ ⟨k, hk⟩) = remAfter σ₀ (k + 1) (σ₀ ⟨k, hk⟩) + 1 := by
  unfold remAfter
  let ek : Fin m := ⟨k, hk⟩
  have heq :
      Finset.univ.filter (fun e : Fin m => k ≤ e.1 ∧ σ₀ e = σ₀ ek) =
      insert ek (Finset.univ.filter (fun e : Fin m => k + 1 ≤ e.1 ∧ σ₀ e = σ₀ ek)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    constructor
    · rintro ⟨hle, hσ⟩
      rcases eq_or_lt_of_le hle with heq_k | hlt_k
      · exact Or.inl heq_k.symm
      · exact Or.inr ⟨hlt_k, hσ⟩
    · rintro (rfl | ⟨hle, hσ⟩)
      · exact ⟨le_rfl, rfl⟩
      · exact ⟨by omega, hσ⟩
  have hnot : ek ∉ Finset.univ.filter (fun e : Fin m => k + 1 ≤ e.1 ∧ σ₀ e = σ₀ ek) := by
    simp [ek]
  rw [heq, Finset.card_insert_of_notMem hnot]

theorem remAfter_step_ne {m t₀ : ℕ} (σ₀ : Fin m → Fin t₀) {k : ℕ} (hk : k < m)
    {l : Fin t₀} (hne : l ≠ σ₀ ⟨k, hk⟩) :
    remAfter σ₀ (k + 1) l = remAfter σ₀ k l := by
  unfold remAfter
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hle, hσ⟩
    exact ⟨by omega, hσ⟩
  · rintro ⟨hle, hσ⟩
    refine ⟨?_, hσ⟩
    rcases eq_or_lt_of_le hle with heq_k | hlt_k
    · have he : e = ⟨k, hk⟩ := Fin.ext heq_k.symm
      subst he
      exact False.elim (hne hσ.symm)
    · exact hlt_k

theorem sigma_ne_of_remAfter_le_one {m t₀ : ℕ} (σ₀ : Fin m → Fin t₀) {k : ℕ} (hk : k < m)
    (hrem : remAfter σ₀ k (σ₀ ⟨k, hk⟩) ≤ 1)
    {e : Fin m} (he : k < e.1) :
    σ₀ e ≠ σ₀ ⟨k, hk⟩ := by
  intro hσ
  have hlt : 1 < remAfter σ₀ k (σ₀ ⟨k, hk⟩) := by
    unfold remAfter
    rw [Finset.one_lt_card_iff]
    refine ⟨⟨k, hk⟩, e, ?_, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, hσ⟩
    · intro h
      have hval : k = e.1 := congrArg Fin.val h
      omega
  omega

theorem exists_gt_of_one_lt_remAfter {m t₀ : ℕ} (σ₀ : Fin m → Fin t₀) {k : ℕ} (hk : k < m)
    (hrem : 1 < remAfter σ₀ k (σ₀ ⟨k, hk⟩)) :
    ∃ e : Fin m, k < e.1 ∧ σ₀ e = σ₀ ⟨k, hk⟩ := by
  rw [remAfter_step_eq σ₀ hk] at hrem
  have hpos : 0 < remAfter σ₀ (k + 1) (σ₀ ⟨k, hk⟩) := by omega
  rcases Finset.card_pos.mp hpos with ⟨e, he⟩
  rcases Finset.mem_filter.mp he with ⟨_, hle, hσ⟩
  exact ⟨e, hle, hσ⟩

/-- Characterization of `digraphIncident G.toMultiComputeDigraph w e` in terms of `G.edgeEndpoints e`. -/
theorem digraphIncident_toComputeDigraph_iff {n : ℕ} (G : MultiDigraph n)
    (w : Fin n) (e : Fin G.numEdges) :
    digraphIncident G.toMultiComputeDigraph w e ↔
      w = (G.edgeEndpoints e).1 ∨ w = (G.edgeEndpoints e).2 := by
  unfold digraphIncident MultiDigraph.toMultiComputeDigraph
  dsimp
  tauto

/-- If `e` is incident with `w` and `(G.edgeEndpoints e).1 = (G.edgeEndpoints e).2`, then
`G.edgeEndpoints e = (w, w)`. -/
theorem edgeEndpoints_eq_loop_of_incident {n : ℕ} (G : MultiDigraph n)
    {w : Fin n} {e : Fin G.numEdges}
    (hinc : digraphIncident G.toMultiComputeDigraph w e)
    (heq : (G.edgeEndpoints e).1 = (G.edgeEndpoints e).2) :
    G.edgeEndpoints e = (w, w) := by
  rcases (digraphIncident_toComputeDigraph_iff G w e).mp hinc with h1 | h2
  · exact Prod.ext h1.symm (heq.symm.trans h1.symm)
  · exact Prod.ext (heq.trans h2.symm) h2.symm

/-- If `e` is a non-loop edge of `G` incident with `w`, then `w` has a neighbor in
`G.toSimpleGraph`. -/
theorem exists_adj_of_incident_of_ne {n : ℕ} (G : MultiDigraph n)
    {w : Fin n} {e : Fin G.numEdges}
    (hinc : digraphIncident G.toMultiComputeDigraph w e)
    (hne : (G.edgeEndpoints e).1 ≠ (G.edgeEndpoints e).2) :
    ∃ y : Fin n, G.toSimpleGraph.Adj w y := by
  have hadj := G.toSimpleGraph_adj_edgeEndpoints e hne
  rcases (digraphIncident_toComputeDigraph_iff G w e).mp hinc with rfl | rfl
  · exact ⟨(G.edgeEndpoints e).2, hadj⟩
  · exact ⟨(G.edgeEndpoints e).1, hadj.symm⟩

/-- Effective leaf map at step `k` of Pass 2: edges `e.1 < k` use `tauDone e`, while edges
`e.1 ≥ k` use `cur (σ₀ e)`. -/
def sigmaAtStep {m t₀ t : ℕ} (σ₀ : Fin m → Fin t₀) (k : ℕ)
    (cur : Fin t₀ → Fin t) (tauDone : Fin m → Fin t) (e : Fin m) : Fin t :=
  if e.1 < k then tauDone e else cur (σ₀ e)

/-- Endpoint condition on `(σ₀, pairOfLeaf)` guaranteeing that splitting any leaf `cur l`
in Pass 2 produces new leaf cuts of order `≤ 3`. -/
def HasValidLeafPairs {n t₀ : ℕ} (G : MultiDigraph n)
    (σ₀ : Fin G.numEdges → Fin t₀) (pairOfLeaf : Fin t₀ → Fin n × Fin n) : Prop :=
  ∀ (e : Fin G.numEdges) (w : Fin n),
    digraphIncident G.toMultiComputeDigraph w e →
      (w = (pairOfLeaf (σ₀ e)).1 ∨ w = (pairOfLeaf (σ₀ e)).2) ∨
      (∀ e' : Fin G.numEdges, digraphIncident G.toMultiComputeDigraph w e' →
        G.edgeEndpoints e' = (w, w) ∧ (e'.1 = 0 ∨ σ₀ e' = σ₀ e))

/-- Combinatorial invariant at step `k ≤ G.numEdges` of Pass 2. -/
structure Pass2CombInv {n t₀ : ℕ} (ω : ℕ) (G : MultiDigraph n)
    (σ₀ : Fin G.numEdges → Fin t₀) (pairOfLeaf : Fin t₀ → Fin n × Fin n)
    (k t : ℕ) (p : ℕ → ℕ) (cur : Fin t₀ → Fin t) (tauDone : Fin G.numEdges → Fin t) : Prop where
  hω : 1 ≤ ω
  ht : 2 ≤ t
  hp0 : p 0 = 0
  hp : ∀ z, 0 < z → z < t → p z < z
  ht_leaves : t ≤ 2 * (treeLeaves (parentTree t p)).card - 2
  hpart : IsPartialDigraphBranchDecomp ω G.toMultiComputeDigraph (parentTree t p)
    (sigmaAtStep σ₀ k cur tauDone)
  hvalid_pairs : HasValidLeafPairs G σ₀ pairOfLeaf
  hsep_lt : ∀ e₁ e₂ : Fin G.numEdges, e₁.1 < k → e₁.1 < e₂.1 →
    sigmaAtStep σ₀ k cur tauDone e₁ ≠ sigmaAtStep σ₀ k cur tauDone e₂
  hge_iff : ∀ e₁ e₂ : Fin G.numEdges, k ≤ e₁.1 → k ≤ e₂.1 →
    (sigmaAtStep σ₀ k cur tauDone e₁ = sigmaAtStep σ₀ k cur tauDone e₂ ↔ σ₀ e₁ = σ₀ e₂)

/-- Every `Pass2CombInv` state has `t ≤ 2 * G.numEdges - 2`. -/
theorem Pass2CombInv.t_le {n t₀ ω : ℕ} {G : MultiDigraph n}
    {σ₀ : Fin G.numEdges → Fin t₀} {pairOfLeaf : Fin t₀ → Fin n × Fin n}
    {k t : ℕ} {p : ℕ → ℕ} {cur : Fin t₀ → Fin t} {tauDone : Fin G.numEdges → Fin t}
    (hinv : Pass2CombInv ω G σ₀ pairOfLeaf k t p cur tauDone) :
    t ≤ 2 * G.numEdges - 2 := by
  have hcard : (treeLeaves (parentTree t p)).card ≤ G.numEdges := hinv.hpart.card_treeLeaves_le
  have hleaves := hinv.ht_leaves
  omega

/-- Step `k → k + 1` of `Pass2CombInv` when `remAfter σ₀ k (σ₀ ⟨k, hk⟩) ≤ 1`:
setting `tauDone' ⟨k, hk⟩ = cur (σ₀ ⟨k, hk⟩)` and leaving `t, p, cur` unchanged preserves
`sigmaAtStep` pointwise, hence preserves `Pass2CombInv`. -/
theorem Pass2CombInv.step_le_one {n t₀ ω : ℕ} {G : MultiDigraph n}
    {σ₀ : Fin G.numEdges → Fin t₀} {pairOfLeaf : Fin t₀ → Fin n × Fin n}
    {k t : ℕ} {p : ℕ → ℕ} {cur : Fin t₀ → Fin t} {tauDone : Fin G.numEdges → Fin t}
    (hinv : Pass2CombInv ω G σ₀ pairOfLeaf k t p cur tauDone)
    (hk : k < G.numEdges)
    (hrem : remAfter σ₀ k (σ₀ ⟨k, hk⟩) ≤ 1)
    {tauDone' : Fin G.numEdges → Fin t}
    (htau_lt : ∀ e : Fin G.numEdges, e.1 < k → tauDone' e = tauDone e)
    (htau_k : tauDone' ⟨k, hk⟩ = cur (σ₀ ⟨k, hk⟩)) :
    Pass2CombInv ω G σ₀ pairOfLeaf (k + 1) t p cur tauDone' := by
  have hσ_eq : sigmaAtStep σ₀ (k + 1) cur tauDone' = sigmaAtStep σ₀ k cur tauDone := by
    funext e
    unfold sigmaAtStep
    by_cases hlt : e.1 < k
    · have hlt1 : e.1 < k + 1 := by omega
      simp [hlt1, hlt, htau_lt e hlt]
    · by_cases hek : e.1 = k
      · have he_eq : e = ⟨k, hk⟩ := Fin.ext hek
        subst he_eq
        have hlt1 : k < k + 1 := by omega
        simp [hlt1, htau_k]
      · have hnot1 : ¬ e.1 < k + 1 := by omega
        simp [hnot1, hlt]
  refine {
    hω := hinv.hω
    ht := hinv.ht
    hp0 := hinv.hp0
    hp := hinv.hp
    ht_leaves := hinv.ht_leaves
    hpart := hσ_eq ▸ hinv.hpart
    hvalid_pairs := hinv.hvalid_pairs
    hsep_lt := ?_
    hge_iff := ?_
  }
  · intro e₁ e₂ he₁ he₁₂
    rw [hσ_eq]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ he₁) with hlt₁ | heq₁
    · exact hinv.hsep_lt e₁ e₂ hlt₁ he₁₂
    · have he₁_eq : e₁ = ⟨k, hk⟩ := Fin.ext heq₁
      subst he₁_eq
      intro h_eq
      have hσ₀_eq := (hinv.hge_iff ⟨k, hk⟩ e₂ le_rfl (by omega)).mp h_eq
      exact sigma_ne_of_remAfter_le_one σ₀ hk hrem he₁₂ hσ₀_eq.symm
  · intro e₁ e₂ he₁ he₂
    rw [hσ_eq]
    exact hinv.hge_iff e₁ e₂ (by omega) (by omega)

/-- Endpoint bound for the left child leaf `⟨t, _⟩` when splitting `ek = ⟨k, hk⟩`. -/
theorem card_digraphLeafCutVerts_left_le {n t : ℕ} (G : MultiDigraph n)
    (ek : Fin G.numEdges) (σ' : Fin G.numEdges → Fin (t + 2))
    (huniq : ∀ e : Fin G.numEdges, σ' e = ⟨t, by omega⟩ → e = ek) :
    (digraphLeafCutVerts G.toMultiComputeDigraph σ' ⟨t, by omega⟩).card ≤ 2 := by
  have hsub : digraphLeafCutVerts G.toMultiComputeDigraph σ' ⟨t, by omega⟩ ⊆
      {(G.edgeEndpoints ek).1, (G.edgeEndpoints ek).2} := by
    intro w hw
    rw [mem_digraphLeafCutVerts] at hw
    rcases hw with ⟨⟨e₁, hw₁, h1⟩, _⟩
    have he₁ : e₁ = ek := huniq e₁ h1
    subst he₁
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact (digraphIncident_toComputeDigraph_iff G w e₁).mp hw₁
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

/-- Endpoint bound for the right child leaf `⟨t + 1, _⟩` when splitting `ek = ⟨k, hk⟩`. -/
theorem card_digraphLeafCutVerts_right_le {n t₀ t : ℕ} (G : MultiDigraph n)
    {σ₀ : Fin G.numEdges → Fin t₀} {pairOfLeaf : Fin t₀ → Fin n × Fin n}
    (hvalid : HasValidLeafPairs G σ₀ pairOfLeaf)
    {k : ℕ} (hk : k < G.numEdges)
    (σ' : Fin G.numEdges → Fin (t + 2))
    (hright_iff : ∀ e : Fin G.numEdges,
      σ' e = ⟨t + 1, by omega⟩ ↔ k < e.1 ∧ σ₀ e = σ₀ ⟨k, hk⟩) :
    (digraphLeafCutVerts G.toMultiComputeDigraph σ' ⟨t + 1, by omega⟩).card ≤ 3 := by
  let ek : Fin G.numEdges := ⟨k, hk⟩
  let l : Fin t₀ := σ₀ ek
  have hsub : digraphLeafCutVerts G.toMultiComputeDigraph σ' ⟨t + 1, by omega⟩ ⊆
      {(pairOfLeaf l).1, (pairOfLeaf l).2, (G.edgeEndpoints ek).1} := by
    intro w hw
    rw [mem_digraphLeafCutVerts] at hw
    rcases hw with ⟨⟨e₁, hw₁, h1⟩, ⟨e₂, hw₂, h2⟩⟩
    rcases (hright_iff e₁).mp h1 with ⟨he₁_gt, he₁_l⟩
    have he₂_not : ¬ (k < e₂.1 ∧ σ₀ e₂ = l) := fun h => h2 ((hright_iff e₂).mpr h)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hvalid e₁ w hw₁ with (hw_p1 | hw_p2) | hloop
    · rw [he₁_l] at hw_p1; exact Or.inl hw_p1
    · rw [he₁_l] at hw_p2; exact Or.inr (Or.inl hw_p2)
    · right; right
      have hend₁ : G.edgeEndpoints e₁ = (w, w) := (hloop e₁ hw₁).1
      rcases hloop e₂ hw₂ with ⟨hend₂, he₂_0 | he₂_l⟩
      · have hek_end := G.edgeEndpoints_contiguous (e₂ := ek)
          (by change e₂.1 ≤ k; omega) (by change k ≤ e₁.1; omega) (hend₂.trans hend₁.symm)
        rw [hek_end, hend₂]
      · rw [he₁_l] at he₂_l
        have he₂_le : e₂.1 ≤ k := by
          by_contra hnot
          exact he₂_not ⟨by omega, he₂_l⟩
        have hek_end := G.edgeEndpoints_contiguous (e₂ := ek)
          (by change e₂.1 ≤ k; omega) (by change k ≤ e₁.1; omega) (hend₂.trans hend₁.symm)
        rw [hek_end, hend₂]
  have hcard3 : ({(pairOfLeaf l).1, (pairOfLeaf l).2, (G.edgeEndpoints ek).1} :
      Finset (Fin n)).card ≤ 3 := by
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_le_two 1)
  exact (Finset.card_le_card hsub).trans hcard3

/-- Step `k → k + 1` of `Pass2CombInv` when `1 < remAfter σ₀ k (σ₀ ⟨k, hk⟩)`:
splitting leaf `v = cur (σ₀ ⟨k, hk⟩)` into `⟨t, _⟩` (for `⟨k, hk⟩`) and `⟨t + 1, _⟩` (for
remaining edges in `σ₀⁻¹(σ₀ ⟨k, hk⟩)`) preserves `Pass2CombInv`. -/
theorem Pass2CombInv.step_gt_one {n t₀ ω : ℕ} {G : MultiDigraph n}
    {σ₀ : Fin G.numEdges → Fin t₀} {pairOfLeaf : Fin t₀ → Fin n × Fin n}
    {k t : ℕ} {p : ℕ → ℕ} {cur : Fin t₀ → Fin t} {tauDone : Fin G.numEdges → Fin t}
    (hinv : Pass2CombInv ω G σ₀ pairOfLeaf k t p cur tauDone)
    (hk : k < G.numEdges)
    (hrem : 1 < remAfter σ₀ k (σ₀ ⟨k, hk⟩))
    {cur' : Fin t₀ → Fin (t + 2)}
    {tauDone' : Fin G.numEdges → Fin (t + 2)}
    (hcur'_eq : cur' (σ₀ ⟨k, hk⟩) = ⟨t + 1, by omega⟩)
    (hcur'_ne : ∀ l : Fin t₀, l ≠ σ₀ ⟨k, hk⟩ → (cur' l).1 = (cur l).1)
    (htau_lt : ∀ e : Fin G.numEdges, e.1 < k → (tauDone' e).1 = (tauDone e).1)
    (htau_k : tauDone' ⟨k, hk⟩ = ⟨t, by omega⟩) :
    Pass2CombInv ω G σ₀ pairOfLeaf (k + 1) (t + 2)
      (splitLeafParent p t (cur (σ₀ ⟨k, hk⟩)).1) cur' tauDone' := by
  let ek : Fin G.numEdges := ⟨k, hk⟩
  let l₀ : Fin t₀ := σ₀ ek
  let v : Fin t := cur l₀
  let σ := sigmaAtStep σ₀ k cur tauDone
  let σ' := sigmaAtStep σ₀ (k + 1) cur' tauDone'
  have hσ_ek : σ ek = v := by
    dsimp [σ, sigmaAtStep, ek, v, l₀]
    simp
  have hv_leaf : v ∈ treeLeaves (parentTree t p) := by
    rw [← hσ_ek]
    exact hinv.hpart.2.1 ek
  have ht_pos : 0 < t := by have := hinv.ht; omega
  -- Characterize `σ' e` in terms of `e` and `σ e`:
  have hσ'_lt : ∀ e : Fin G.numEdges, e.1 < k → (σ' e).1 = (σ e).1 := by
    intro e he
    have he1 : e.1 < k + 1 := by omega
    dsimp [σ', σ, sigmaAtStep]
    simp [he1, he, htau_lt e he]
  have hσ'_ek : σ' ek = ⟨t, by omega⟩ := by
    have hk1 : k < k + 1 := by omega
    dsimp [σ', sigmaAtStep, ek]
    simp [hk1, htau_k]
  have hσ'_gt_eq : ∀ e : Fin G.numEdges, k < e.1 → σ₀ e = l₀ → σ' e = ⟨t + 1, by omega⟩ := by
    intro e he hσ₀
    have hnot : ¬ e.1 < k + 1 := by omega
    dsimp [σ', sigmaAtStep]
    rw [ite_eq_right_iff.mpr (fun h => False.elim (hnot h)), hσ₀, hcur'_eq]
  have hσ'_gt_ne : ∀ e : Fin G.numEdges, k < e.1 → σ₀ e ≠ l₀ → (σ' e).1 = (σ e).1 := by
    intro e he hσ₀
    have hnot1 : ¬ e.1 < k + 1 := by omega
    have hnot0 : ¬ e.1 < k := by omega
    dsimp [σ', σ, sigmaAtStep]
    simp [hnot1, hnot0, hcur'_ne (σ₀ e) hσ₀]
  have hσ'_ne_v : ∀ e : Fin G.numEdges, σ e ≠ v → (σ' e).1 = (σ e).1 := by
    intro e hev
    rcases lt_trichotomy e.1 k with hlt | heq | hgt
    · exact hσ'_lt e hlt
    · have he_eq : e = ek := Fin.ext heq
      subst he_eq
      exact False.elim (hev hσ_ek)
    · have hσ₀_ne : σ₀ e ≠ l₀ := by
        intro h
        apply hev
        rw [← hσ_ek]
        exact (hinv.hge_iff e ek (by omega) le_rfl).mpr h
      exact hσ'_gt_ne e hgt hσ₀_ne
  have hσ'_eq_v : ∀ e : Fin G.numEdges, σ e = v → (σ' e).1 = t ∨ (σ' e).1 = t + 1 := by
    intro e hev
    rcases lt_trichotomy e.1 k with hlt | heq | hgt
    · exfalso
      exact hinv.hsep_lt e ek hlt hlt (hev.trans hσ_ek.symm)
    · have he_eq : e = ek := Fin.ext heq
      subst he_eq
      exact Or.inl (congrArg Fin.val hσ'_ek)
    · have hσ₀_eq : σ₀ e = l₀ := by
        rw [← hσ_ek] at hev
        exact (hinv.hge_iff e ek (by omega) le_rfl).mp hev
      exact Or.inr (congrArg Fin.val (hσ'_gt_eq e hgt hσ₀_eq))
  have huniq_t : ∀ e : Fin G.numEdges, σ' e = ⟨t, by omega⟩ → e = ek := by
    intro e he_t
    rcases lt_trichotomy e.1 k with hlt | heq | hgt
    · have h1 := hσ'_lt e hlt
      have h2 := (σ e).2
      have h3 : (σ' e).1 = t := congrArg Fin.val he_t
      omega
    · exact Fin.ext heq
    · by_cases hσ₀ : σ₀ e = l₀
      · have h1 : (σ' e).1 = t + 1 := congrArg Fin.val (hσ'_gt_eq e hgt hσ₀)
        have h3 : (σ' e).1 = t := congrArg Fin.val he_t
        omega
      · have h1 := hσ'_gt_ne e hgt hσ₀
        have h2 := (σ e).2
        have h3 : (σ' e).1 = t := congrArg Fin.val he_t
        omega
  have hright_iff : ∀ e : Fin G.numEdges,
      σ' e = ⟨t + 1, by omega⟩ ↔ k < e.1 ∧ σ₀ e = l₀ := by
    intro e
    constructor
    · intro he_t1
      have hval : (σ' e).1 = t + 1 := congrArg Fin.val he_t1
      rcases lt_trichotomy e.1 k with hlt | heq | hgt
      · have h1 := hσ'_lt e hlt
        have h2 := (σ e).2
        omega
      · have he_eq : e = ek := Fin.ext heq
        subst he_eq
        have h1 : (σ' ek).1 = t := congrArg Fin.val hσ'_ek
        omega
      · refine ⟨hgt, ?_⟩
        by_contra hσ₀
        have h1 := hσ'_gt_ne e hgt hσ₀
        have h2 := (σ e).2
        omega
    · rintro ⟨hgt, hσ₀⟩
      exact hσ'_gt_eq e hgt hσ₀
  rcases exists_gt_of_one_lt_remAfter σ₀ hk hrem with ⟨e_right, he_right_gt, he_right_l⟩
  have hω : 1 ≤ ω := hinv.hω
  have hord_left : (digraphLeafCutVerts G.toMultiComputeDigraph σ' ⟨t, by omega⟩).card ≤ 3 * ω := by
    have h2 := card_digraphLeafCutVerts_left_le G ek σ' huniq_t
    omega
  have hord_right :
      (digraphLeafCutVerts G.toMultiComputeDigraph σ' ⟨t + 1, by omega⟩).card ≤ 3 * ω := by
    have h3 := card_digraphLeafCutVerts_right_le G hinv.hvalid_pairs hk σ' hright_iff
    omega
  have hpart' : IsPartialDigraphBranchDecomp ω G.toMultiComputeDigraph
      (parentTree (t + 2) (splitLeafParent p t v.1)) σ' :=
    isPartialDigraphBranchDecomp_splitLeaf ht_pos hinv.hp hinv.hpart hv_leaf
      hσ'_ne_v hσ'_eq_v ⟨ek, hσ'_ek⟩
      ⟨e_right, hσ'_gt_eq e_right he_right_gt he_right_l⟩
      hord_left hord_right
  have hcard_leaves' :
      (treeLeaves (parentTree (t + 2) (splitLeafParent p t (cur (σ₀ ⟨k, hk⟩)).1))).card =
        (treeLeaves (parentTree t p)).card + 1 :=
    card_treeLeaves_splitLeafParent hinv.hp ht_pos hv_leaf
  have hp0 : p 0 = 0 := hinv.hp0
  refine {
    hω := hinv.hω
    ht := by omega
    hp0 := by
      rw [splitLeafParent, ite_eq_right_iff.mpr (by omega)]
      exact hp0
    hp := splitLeafParent_lt hinv.hp v.2
    ht_leaves := by
      have := hinv.ht_leaves
      omega
    hpart := hpart'
    hvalid_pairs := hinv.hvalid_pairs
    hsep_lt := ?_
    hge_iff := ?_
  }
  · intro e₁ e₂ he₁ he₁₂
    change σ' e₁ ≠ σ' e₂
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ he₁) with hlt₁ | heq₁
    · have h1 := hσ'_lt e₁ hlt₁
      have h1_lt : (σ' e₁).1 < t := by rw [h1]; exact (σ e₁).2
      rcases lt_trichotomy e₂.1 k with hlt₂ | heq₂ | hgt₂
      · intro h_eq
        have h2 := hσ'_lt e₂ hlt₂
        apply hinv.hsep_lt e₁ e₂ hlt₁ he₁₂
        exact Fin.ext (by rw [← h1, ← h2, congrArg Fin.val h_eq])
      · have he₂_eq : e₂ = ek := Fin.ext heq₂
        subst he₂_eq
        intro h_eq
        have h2 : (σ' ek).1 = t := congrArg Fin.val hσ'_ek
        omega
      · by_cases hσ₀ : σ₀ e₂ = l₀
        · intro h_eq
          have h2 : (σ' e₂).1 = t + 1 := congrArg Fin.val (hσ'_gt_eq e₂ hgt₂ hσ₀)
          omega
        · intro h_eq
          have h2 := hσ'_gt_ne e₂ hgt₂ hσ₀
          apply hinv.hsep_lt e₁ e₂ hlt₁ he₁₂
          exact Fin.ext (by rw [← h1, ← h2, congrArg Fin.val h_eq])
    · have he₁_eq : e₁ = ek := Fin.ext heq₁
      subst he₁_eq
      intro h_eq
      have hne := huniq_t e₂ (h_eq.symm.trans hσ'_ek)
      subst hne
      exact Nat.lt_irrefl k he₁₂
  · intro e₁ e₂ he₁ he₂
    change σ' e₁ = σ' e₂ ↔ σ₀ e₁ = σ₀ e₂
    have hgt₁ : k < e₁.1 := he₁
    have hgt₂ : k < e₂.1 := he₂
    by_cases h1 : σ₀ e₁ = l₀ <;> by_cases h2 : σ₀ e₂ = l₀
    · rw [hσ'_gt_eq e₁ hgt₁ h1, hσ'_gt_eq e₂ hgt₂ h2, h1, h2]
      simp
    · constructor
      · intro heq
        have hv1 : (σ' e₁).1 = t + 1 := congrArg Fin.val (hσ'_gt_eq e₁ hgt₁ h1)
        have hv2 : (σ' e₂).1 < t := by rw [hσ'_gt_ne e₂ hgt₂ h2]; exact (σ e₂).2
        omega
      · intro hσ₀
        exact False.elim (h2 (hσ₀.symm.trans h1))
    · constructor
      · intro heq
        have hv1 : (σ' e₁).1 < t := by rw [hσ'_gt_ne e₁ hgt₁ h1]; exact (σ e₁).2
        have hv2 : (σ' e₂).1 = t + 1 := congrArg Fin.val (hσ'_gt_eq e₂ hgt₂ h2)
        omega
      · intro hσ₀
        exact False.elim (h1 (hσ₀.trans h2))
    · constructor
      · intro heq
        have hv1 := hσ'_gt_ne e₁ hgt₁ h1
        have hv2 := hσ'_gt_ne e₂ hgt₂ h2
        have hσ_eq : σ e₁ = σ e₂ := Fin.ext (by rw [← hv1, ← hv2, congrArg Fin.val heq])
        exact (hinv.hge_iff e₁ e₂ (by omega) (by omega)).mp hσ_eq
      · intro hσ₀
        have hσ_eq : σ e₁ = σ e₂ := (hinv.hge_iff e₁ e₂ (by omega) (by omega)).mpr hσ₀
        have hv1 := hσ'_gt_ne e₁ hgt₁ h1
        have hv2 := hσ'_gt_ne e₂ hgt₂ h2
        exact Fin.ext (by rw [hv1, hv2, congrArg Fin.val hσ_eq])

/-- At the end of Pass 2 (`k = G.numEdges`), `Pass2CombInv` yields a valid
`IsMultiBranchDecompOfWidthLe (3 * ω) G (parentTree t p) tauDone` with `t ≤ 2 * G.numEdges - 2`. -/
theorem Pass2CombInv.to_branchDecomp_at_end {n t₀ ω : ℕ} {G : MultiDigraph n}
    {σ₀ : Fin G.numEdges → Fin t₀} {pairOfLeaf : Fin t₀ → Fin n × Fin n}
    {t : ℕ} {p : ℕ → ℕ} {cur : Fin t₀ → Fin t} {tauDone : Fin G.numEdges → Fin t}
    (hinv : Pass2CombInv ω G σ₀ pairOfLeaf G.numEdges t p cur tauDone) :
    IsMultiBranchDecompOfWidthLe (3 * ω) G (parentTree t p) tauDone ∧
      t ≤ 2 * G.numEdges - 2 := by
  have hσ_eq : sigmaAtStep σ₀ G.numEdges cur tauDone = tauDone := by
    funext e
    unfold sigmaAtStep
    simp [e.2]
  have hinj : Function.Injective tauDone := by
    intro e₁ e₂ h
    rcases lt_trichotomy e₁.1 e₂.1 with hlt | heq | hgt
    · exfalso
      apply hinv.hsep_lt e₁ e₂ e₁.2 hlt
      rw [hσ_eq, h]
    · exact Fin.ext heq
    · exfalso
      apply hinv.hsep_lt e₂ e₁ e₂.2 hgt
      rw [hσ_eq, h]
  have hpart_tau : IsPartialDigraphBranchDecomp ω G.toMultiComputeDigraph (parentTree t p) tauDone :=
    hσ_eq ▸ hinv.hpart
  exact ⟨hpart_tau.to_isDigraphBranchDecompOfWidthLe hinj, hinv.t_le⟩

/-- Initial leaf map for the small-simple-graph case (`G.toSimpleGraph.edgeFinset.card ≤ 1` and
`2 ≤ G.numEdges`): edge `0` maps to leaf `0`, and all edges `e.1 ≥ 1` map to leaf `1`. -/
def smallInitSigma (m : ℕ) (e : Fin m) : Fin 2 :=
  if e.1 = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩

/-- Initial `Pass2CombInv` at `k = 0` when `G.toSimpleGraph.edgeFinset.card ≤ 1` and
`2 ≤ G.numEdges`. -/
theorem pass2CombInv_init_small {n ω : ℕ} (hω : 1 ≤ ω) (G : MultiDigraph n)
    (hcard_sim : G.toSimpleGraph.edgeFinset.card ≤ 1)
    (hm : 2 ≤ G.numEdges) :
    ∃ pairOfLeaf : Fin 2 → Fin n × Fin n,
      Pass2CombInv ω G (smallInitSigma G.numEdges) pairOfLeaf
        0 2 (fun _ => 0) id (smallInitSigma G.numEdges) := by
  classical
  let e₀ : Fin G.numEdges := ⟨0, by omega⟩
  let e₁ : Fin G.numEdges := ⟨1, by omega⟩
  let p1 : Fin n × Fin n :=
    if hnl : ∃ e : Fin G.numEdges, (G.edgeEndpoints e).1 ≠ (G.edgeEndpoints e).2 then
      G.edgeEndpoints (Classical.choose hnl)
    else
      G.edgeEndpoints e₀
  let pairOfLeaf : Fin 2 → Fin n × Fin n :=
    fun l => if l.1 = 0 then G.edgeEndpoints e₀ else p1
  refine ⟨pairOfLeaf, ?_⟩
  have hσ_eq : sigmaAtStep (smallInitSigma G.numEdges) 0 id (smallInitSigma G.numEdges) =
      smallInitSigma G.numEdges := by
    funext e
    unfold sigmaAtStep
    simp
  refine {
    hω := hω
    ht := le_rfl
    hp0 := rfl
    hp := fun z hz _ => hz
    ht_leaves := by rw [treeLeaves_parentTree_two]; simp
    hpart := ?_
    hvalid_pairs := ?_
    hsep_lt := fun _ _ h => False.elim (Nat.not_lt_zero _ h)
    hge_iff := fun e₁ e₂ _ _ => by rw [hσ_eq]
  }
  · rw [hσ_eq]
    refine ⟨isCubicOrLeafTree_parentTree_two, ?_, ?_, ?_⟩
    · intro e
      rw [treeLeaves_parentTree_two]
      exact Finset.mem_univ _
    · intro v _
      fin_cases v
      · exact ⟨e₀, by simp [smallInitSigma, e₀]⟩
      · exact ⟨e₁, by simp [smallInitSigma, e₁]⟩
    · intro f hf
      have hp : ∀ z, 0 < z → z < 2 → (fun _ => 0) z < z := fun z hz _ => hz
      rcases exists_pos_of_mem_edgeFinset_parentTree hp hf with ⟨x, hx_pos, hf_eq⟩
      have hx_lt2 : x.1 < 2 := x.2
      have hx1 : x = ⟨1, by decide⟩ := Fin.ext (by change x.1 = 1; omega)
      have hf_eq01 : f = s(⟨0, by decide⟩, ⟨1, by decide⟩) := by
        rw [hf_eq]
        exact congrArg₂ (fun a b => s(a, b)) (Fin.ext rfl) hx1
      rw [hf_eq01]
      have hdeg1 : (parentTree 2 (fun _ => 0)).degree ⟨1, by decide⟩ = 1 :=
        degree_parentTree_two ⟨1, by decide⟩
      have hadj01 : (parentTree 2 (fun _ => 0)).Adj ⟨0, by decide⟩ ⟨1, by decide⟩ := by
        rw [parentTree_adj_of_lt hp]
        exact Or.inr ⟨by decide, rfl⟩
      have hconn : (parentTree 2 (fun _ => 0)).Connected :=
        parentTree_connected (by omega) hp
      unfold digraphTreeEdgeOrder
      rw [digraphTreeEdgeCutVerts_leaf_eq G.toMultiComputeDigraph hconn (smallInitSigma G.numEdges)
        hdeg1 hadj01]
      have hsub : digraphLeafCutVerts G.toMultiComputeDigraph (smallInitSigma G.numEdges) ⟨1, by decide⟩ ⊆
          {(G.edgeEndpoints e₀).1, (G.edgeEndpoints e₀).2} := by
        intro w hw
        rw [mem_digraphLeafCutVerts] at hw
        rcases hw with ⟨_, ⟨e₂, hw₂, hne1⟩⟩
        have he₂_0 : e₂ = e₀ := by
          by_contra hne0
          have hval0 : e₂.1 ≠ 0 := fun h => hne0 (Fin.ext h)
          apply hne1
          simp [smallInitSigma, hval0]
        subst he₂_0
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact (digraphIncident_toComputeDigraph_iff G w e₀).mp hw₂
      have hcard := (Finset.card_le_card hsub).trans Finset.card_le_two
      omega
  · intro e w hw
    by_cases he0 : e.1 = 0
    · have he_eq : e = e₀ := Fin.ext he0
      subst he_eq
      left
      simpa [pairOfLeaf, smallInitSigma, e₀] using (digraphIncident_toComputeDigraph_iff G w e₀).mp hw
    · have hσ_e : smallInitSigma G.numEdges e = ⟨1, by decide⟩ := by
        simp [smallInitSigma, he0]
      rw [hσ_e]
      change (w = p1.1 ∨ w = p1.2) ∨ _
      by_cases hnl : ∃ e' : Fin G.numEdges, (G.edgeEndpoints e').1 ≠ (G.edgeEndpoints e').2
      · have hp1 : p1 = G.edgeEndpoints (Classical.choose hnl) := by simp [p1, hnl]
        let enl := Classical.choose hnl
        have henl_ne : (G.edgeEndpoints enl).1 ≠ (G.edgeEndpoints enl).2 :=
          Classical.choose_spec hnl
        by_cases hw_p1 : w = p1.1 ∨ w = p1.2
        · exact Or.inl hw_p1
        · right
          intro e' hw'
          refine ⟨?_, ?_⟩
          · by_cases he'_nl : (G.edgeEndpoints e').1 = (G.edgeEndpoints e').2
            · exact edgeEndpoints_eq_loop_of_incident G hw' he'_nl
            · exfalso
              have hadj1 : G.toSimpleGraph.Adj (G.edgeEndpoints enl).1 (G.edgeEndpoints enl).2 :=
                G.toSimpleGraph_adj_edgeEndpoints enl henl_ne
              have hadj2 : G.toSimpleGraph.Adj (G.edgeEndpoints e').1 (G.edgeEndpoints e').2 :=
                G.toSimpleGraph_adj_edgeEndpoints e' he'_nl
              have hmem1 : s((G.edgeEndpoints enl).1, (G.edgeEndpoints enl).2) ∈
                  G.toSimpleGraph.edgeFinset :=
                SimpleGraph.mem_edgeFinset.mpr hadj1
              have hmem2 : s((G.edgeEndpoints e').1, (G.edgeEndpoints e').2) ∈
                  G.toSimpleGraph.edgeFinset :=
                SimpleGraph.mem_edgeFinset.mpr hadj2
              have hsym_eq : s((G.edgeEndpoints e').1, (G.edgeEndpoints e').2) =
                  s((G.edgeEndpoints enl).1, (G.edgeEndpoints enl).2) := by
                by_contra hne_sym
                have hgt1 : 1 < G.toSimpleGraph.edgeFinset.card :=
                  Finset.one_lt_card_iff.mpr ⟨_, _, hmem2, hmem1, hne_sym⟩
                omega
              have hw_in : w ∈ s((G.edgeEndpoints e').1, (G.edgeEndpoints e').2) := by
                rw [Sym2.mem_iff]
                exact (digraphIncident_toComputeDigraph_iff G w e').mp hw'
              rw [hsym_eq, Sym2.mem_iff, ← hp1] at hw_in
              exact hw_p1 hw_in
          · by_cases he'0 : e'.1 = 0
            · exact Or.inl he'0
            · right; simp [smallInitSigma, he'0]
      · right
        intro e' hw'
        have he'_eq : (G.edgeEndpoints e').1 = (G.edgeEndpoints e').2 := by
          by_contra hne
          exact hnl ⟨e', hne⟩
        refine ⟨edgeEndpoints_eq_loop_of_incident G hw' he'_eq, ?_⟩
        by_cases he'0 : e'.1 = 0
        · exact Or.inl he'0
        · right; simp [smallInitSigma, he'0]

/-- Specification of the `n × n` leaf-lookup matrix `lmat` constructed by `buildLeafMatProg`
from the simple graph `G.toSimpleGraph` and its branch-decomposition `(T₀, τ₀)`:
1. For every adjacent pair `(u, v)`, `lmat u v = τ₀ s(u, v)`.
2. For every vertex `u` that has at least one neighbor in `G.toSimpleGraph`, `lmat u u = τ₀ s(u, y)`
   for some neighbor `y` of `u`.
3. Every diagonal entry `lmat u u` equals `τ₀ g` for some `g ∈ G.toSimpleGraph.edgeFinset`. -/
def IsValidLeafLookupMat {n t₀ : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (τ₀ : Sym2 (Fin n) → Fin t₀) (lmat : Fin n → Fin n → Fin t₀) : Prop :=
  (∀ u v : Fin n, H.Adj u v → lmat u v = τ₀ s(u, v)) ∧
  (∀ u : Fin n, (∃ y : Fin n, H.Adj u y) → ∃ y : Fin n, H.Adj u y ∧ lmat u u = τ₀ s(u, y)) ∧
  (∀ u : Fin n, ∃ g ∈ H.edgeFinset, lmat u u = τ₀ g)

/-- Initial leaf map `σ₀ e = lmat (G.edgeEndpoints e).1 (G.edgeEndpoints e).2` from `lmat`. -/
def sigmaFromLeafMat {n t₀ : ℕ} (G : MultiDigraph n) (lmat : Fin n → Fin n → Fin t₀)
    (e : Fin G.numEdges) : Fin t₀ :=
  lmat (G.edgeEndpoints e).1 (G.edgeEndpoints e).2

/-- Initial `Pass2CombInv` at `k = 0` from a branch-decomposition `(parentTree t₀ p₀, τ₀)` of
`G.toSimpleGraph` (when `2 ≤ G.toSimpleGraph.edgeFinset.card`) and a valid leaf-lookup matrix
`lmat`. -/
theorem pass2CombInv_init_from_simple {n t₀ ω : ℕ} (hω : 1 ≤ ω) (G : MultiDigraph n)
    (hm : 2 ≤ G.numEdges)
    {p₀ : ℕ → ℕ} (ht₀ : 2 ≤ t₀) (hp₀_0 : p₀ 0 = 0)
    (hp₀ : ∀ z, 0 < z → z < t₀ → p₀ z < z)
    (ht₀_le : t₀ ≤ 2 * G.toSimpleGraph.edgeFinset.card - 2)
    {τ₀ : Sym2 (Fin n) → Fin t₀}
    (hbd₀ : IsBranchDecompOfWidthLe (3 * ω) G.toSimpleGraph (parentTree t₀ p₀) τ₀)
    {lmat : Fin n → Fin n → Fin t₀}
    (hlmat : IsValidLeafLookupMat G.toSimpleGraph τ₀ lmat) :
    ∃ pairOfLeaf : Fin t₀ → Fin n × Fin n,
      Pass2CombInv ω G (sigmaFromLeafMat G lmat) pairOfLeaf
        0 t₀ p₀ id (sigmaFromLeafMat G lmat) := by
  classical
  let z₀ : Fin n := (G.edgeEndpoints ⟨0, by omega⟩).1
  let pairOfLeaf (l : Fin t₀) : Fin n × Fin n :=
    if hex : ∃ u v : Fin n, G.toSimpleGraph.Adj u v ∧ τ₀ s(u, v) = l then
      let u := Classical.choose hex
      let v := Classical.choose (Classical.choose_spec hex)
      (u, v)
    else
      (z₀, z₀)
  refine ⟨pairOfLeaf, ?_⟩
  let σ₀ := sigmaFromLeafMat G lmat
  have hσ_eq : sigmaAtStep σ₀ 0 id σ₀ = σ₀ := by
    funext e
    unfold sigmaAtStep
    simp
  have hcard_leaves :
      G.toSimpleGraph.edgeFinset.card = (treeLeaves (parentTree t₀ p₀)).card :=
    Finset.card_bij (fun e _ => τ₀ e)
      (fun e he => hbd₀.2.1.1 he)
      (fun e₁ he₁ e₂ he₂ h => hbd₀.2.1.2.1 he₁ he₂ h)
      (fun v hv => by
        rcases hbd₀.2.1.2.2 hv with ⟨e, he, rfl⟩
        exact ⟨e, he, rfl⟩)
  refine {
    hω := hω
    ht := ht₀
    hp0 := hp₀_0
    hp := hp₀
    ht_leaves := by omega
    hpart := ?_
    hvalid_pairs := ?_
    hsep_lt := fun _ _ h => False.elim (Nat.not_lt_zero _ h)
    hge_iff := fun e₁ e₂ _ _ => by rw [hσ_eq]
  }
  · rw [hσ_eq]
    refine ⟨hbd₀.1, ?_, ?_, ?_⟩
    · intro e
      dsimp [σ₀, sigmaFromLeafMat]
      by_cases hne : (G.edgeEndpoints e).1 = (G.edgeEndpoints e).2
      · rw [hne]
        rcases hlmat.2.2 (G.edgeEndpoints e).2 with ⟨g, hg, hval⟩
        rw [hval]
        exact hbd₀.2.1.1 hg
      · have hadj : G.toSimpleGraph.Adj (G.edgeEndpoints e).1 (G.edgeEndpoints e).2 :=
          G.toSimpleGraph_adj_edgeEndpoints e hne
        rw [hlmat.1 _ _ hadj]
        exact hbd₀.2.1.1 (SimpleGraph.mem_edgeFinset.mpr hadj)
    · intro v hv
      rcases hbd₀.2.1.2.2 hv with ⟨g, hg, rfl⟩
      induction g using Sym2.ind with
      | _ x y =>
        have hadj : G.toSimpleGraph.Adj x y := SimpleGraph.mem_edgeFinset.mp hg
        rcases hadj with ⟨hne_xy, hpos⟩
        have hpos' : 0 < G.edgeMult x y ∨ 0 < G.edgeMult y x := by omega
        rcases hpos' with hxy | hyx
        · rcases G.exists_edgeEndpoints_of_edgeMult_pos hxy with ⟨e, he⟩
          refine ⟨e, ?_⟩
          dsimp [σ₀, sigmaFromLeafMat]
          rw [he, hlmat.1 x y ⟨hne_xy, by omega⟩]
        · rcases G.exists_edgeEndpoints_of_edgeMult_pos hyx with ⟨e, he⟩
          refine ⟨e, ?_⟩
          dsimp [σ₀, sigmaFromLeafMat]
          rw [he, hlmat.1 y x ⟨hne_xy.symm, by omega⟩, Sym2.eq_swap]
    · intro f hf
      have hsub : digraphTreeEdgeCutVerts G.toMultiComputeDigraph (parentTree t₀ p₀) σ₀ f ⊆
          treeEdgeCutVerts G.toSimpleGraph (parentTree t₀ p₀) τ₀ f := by
        intro w hw
        rw [mem_digraphTreeEdgeCutVerts] at hw
        rw [mem_treeEdgeCutVerts]
        rcases hw with ⟨e₁, e₂, hw₁, hw₂, hnr⟩
        have hσ_ne : σ₀ e₁ ≠ σ₀ e₂ := fun h => hnr (h ▸ SimpleGraph.Reachable.refl _)
        have hex_nb : ∃ y : Fin n, G.toSimpleGraph.Adj w y := by
          by_contra hno
          have hloop : ∀ e : Fin G.numEdges, digraphIncident G.toMultiComputeDigraph w e →
              G.edgeEndpoints e = (w, w) := by
            intro e he_inc
            by_cases hne : (G.edgeEndpoints e).1 = (G.edgeEndpoints e).2
            · exact edgeEndpoints_eq_loop_of_incident G he_inc hne
            · exact False.elim (hno (exists_adj_of_incident_of_ne G he_inc hne))
          have hend1 := hloop e₁ hw₁
          have hend2 := hloop e₂ hw₂
          apply hσ_ne
          dsimp [σ₀, sigmaFromLeafMat]
          rw [hend1, hend2]
        have hex_sim : ∀ e : Fin G.numEdges, digraphIncident G.toMultiComputeDigraph w e →
            ∃ g ∈ G.toSimpleGraph.edgeFinset, w ∈ g ∧ σ₀ e = τ₀ g := by
          intro e he_inc
          by_cases hne : (G.edgeEndpoints e).1 = (G.edgeEndpoints e).2
          · have hend : G.edgeEndpoints e = (w, w) :=
              edgeEndpoints_eq_loop_of_incident G he_inc hne
            rcases hlmat.2.1 w hex_nb with ⟨y, hadj_wy, hlmat_ww⟩
            refine ⟨s(w, y), SimpleGraph.mem_edgeFinset.mpr hadj_wy,
              Sym2.mem_iff.mpr (Or.inl rfl), ?_⟩
            dsimp [σ₀, sigmaFromLeafMat]
            rw [hend, hlmat_ww]
          · have hadj := G.toSimpleGraph_adj_edgeEndpoints e hne
            refine ⟨s((G.edgeEndpoints e).1, (G.edgeEndpoints e).2),
              SimpleGraph.mem_edgeFinset.mpr hadj,
              Sym2.mem_iff.mpr ((digraphIncident_toComputeDigraph_iff G w e).mp he_inc), ?_⟩
            dsimp [σ₀, sigmaFromLeafMat]
            exact hlmat.1 _ _ hadj
        rcases hex_sim e₁ hw₁ with ⟨g₁, hg₁, hw_g₁, hσ₁⟩
        rcases hex_sim e₂ hw₂ with ⟨g₂, hg₂, hw_g₂, hσ₂⟩
        rw [hσ₁, hσ₂] at hnr
        exact ⟨g₁, hg₁, g₂, hg₂, hw_g₁, hw_g₂, hnr⟩
      unfold digraphTreeEdgeOrder
      exact (Finset.card_le_card hsub).trans (hbd₀.2.2 f hf)
  · intro e w hw
    have hpair_eq : ∀ u v : Fin n, G.toSimpleGraph.Adj u v →
        s((pairOfLeaf (τ₀ s(u, v))).1, (pairOfLeaf (τ₀ s(u, v))).2) = s(u, v) := by
      intro u v hadj
      have hex : ∃ u' v' : Fin n, G.toSimpleGraph.Adj u' v' ∧ τ₀ s(u', v') = τ₀ s(u, v) :=
        ⟨u, v, hadj, rfl⟩
      let u' := Classical.choose hex
      let v' := Classical.choose (Classical.choose_spec hex)
      have hspec : G.toSimpleGraph.Adj u' v' ∧ τ₀ s(u', v') = τ₀ s(u, v) :=
        Classical.choose_spec (Classical.choose_spec hex)
      have hpair : pairOfLeaf (τ₀ s(u, v)) = (u', v') := dite_eq_left_of_eq_true (eq_true hex)
      rw [hpair]
      exact hbd₀.2.1.2.1 (SimpleGraph.mem_edgeFinset.mpr hspec.1)
        (SimpleGraph.mem_edgeFinset.mpr hadj) hspec.2
    by_cases hne : (G.edgeEndpoints e).1 = (G.edgeEndpoints e).2
    · have hend : G.edgeEndpoints e = (w, w) := edgeEndpoints_eq_loop_of_incident G hw hne
      by_cases hex_nb : ∃ y : Fin n, G.toSimpleGraph.Adj w y
      · rcases hlmat.2.1 w hex_nb with ⟨y, hadj_wy, hlmat_ww⟩
        left
        have hσ_e : sigmaFromLeafMat G lmat e = τ₀ s(w, y) := by
          dsimp [sigmaFromLeafMat]
          rw [hend, hlmat_ww]
        rw [hσ_e, ← Sym2.mem_iff, hpair_eq w y hadj_wy, Sym2.mem_iff]
        exact Or.inl rfl
      · right
        intro e' hw'
        have hend' : G.edgeEndpoints e' = (w, w) := by
          by_cases hne' : (G.edgeEndpoints e').1 = (G.edgeEndpoints e').2
          · exact edgeEndpoints_eq_loop_of_incident G hw' hne'
          · exact False.elim (hex_nb (exists_adj_of_incident_of_ne G hw' hne'))
        refine ⟨hend', Or.inr ?_⟩
        dsimp [sigmaFromLeafMat]
        rw [hend', hend]
    · left
      have hadj := G.toSimpleGraph_adj_edgeEndpoints e hne
      have hσ_e : sigmaFromLeafMat G lmat e = τ₀ s((G.edgeEndpoints e).1, (G.edgeEndpoints e).2) := by
        dsimp [sigmaFromLeafMat]
        exact hlmat.1 _ _ hadj
      rw [hσ_e, ← Sym2.mem_iff, hpair_eq _ _ hadj, Sym2.mem_iff]
      exact (digraphIncident_toComputeDigraph_iff G w e).mp hw

end GraphMinor.Compute
