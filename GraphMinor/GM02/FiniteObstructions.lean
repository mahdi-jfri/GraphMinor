module

public import GraphMinor.GM02.TreeDecomposition
public import GraphMinor.Minor.Basic
import GraphMinor.GM02.MinorWidth
import GraphMinor.GM04.Main
import GraphMinor.GM13.Section4
import GraphMinor.GM10.Section4Contraction

/-!
# Finiteness consequences in Graph Minors II

IV (1.5) rules out an infinite antichain of bounded tree-width. To apply it,
convert II's bags through the GM10 width bound and the existing branch-width
to GM04 conversion. This gives (5.1).

For (5.2) the paper (page 321) looks at the graphs of tree-width more than `w`
that are minimal under taking minors. Each has tree-width at most `w + 1`,
since deleting one vertex leaves tree-width at most `w`, and putting the
vertex back into every bag raises the width by at most one. So (5.1) with
`w + 1` shows that there are finitely many of them, up to isomorphism.
-/

public section

namespace GraphMinor.GM02

open Graph Set

universe u v

/-- IV (1.5) for II's bags: a sequence of finite graphs of tree-width at most `w`
has two terms, the earlier one isomorphic to a minor of the later one. The width
conversions give a uniform width bound in IV's sense. -/
theorem exists_isIsoMinor_of_treeWidthLE {α : Type u} {β : Type v} (w : ℕ)
    (G : ℕ → Graph α β) (hVG : ∀ n, V(G n).Finite) (hEG : ∀ n, E(G n).Finite)
    (hwidth : ∀ n, TreeWidthLE (G n) w) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) := by
  have htw : ∀ n, GM04.TreeWidthLE
      (Hypergraph.ofGraph (G n) (hVG n) (hEG n)).toRooted (max (3 * (w + 1) / 2) 2) := by
    intro n
    apply GM13.treeWidthLE_gm04_of_graphBranchWidthLE (hVG n) (hEG n)
    apply (GM13.graphBranchWidthLE_iff_branchWidth_le (G n) (hVG n) (hEG n) (w + 1)).2
    exact (GM10.branchWidth_le_treeWidthPlusOne _).trans
      ((treeWidthLE_iff (G n) (hVG n) (hEG n) w).1 (hwidth n))
  exact GM04.theorem_1_5_proved _ G hVG hEG htw

/-- Graph Minors II, (5.1), page 320:
"Let $w$ be a number, and let $\mathcal{C}$ be a set of graphs each with
tree-width $\le w$. Suppose that no member of $\mathcal{C}$ is isomorphic to a
minor of another member. Then $\mathcal{C}$ is finite."

Apply the proved IV (1.5) (`exists_isIsoMinor_of_treeWidthLE`) to a sequence of
distinct members if the class were infinite. The comparable pair it gives
contradicts the antichain. -/
theorem theorem_5_1_proof {α : Type u} {β : Type v} (w : ℕ) (C : Set (Graph α β))
    (hV : ∀ G ∈ C, V(G).Finite) (hE : ∀ G ∈ C, E(G).Finite)
    (hwidth : ∀ G ∈ C, TreeWidthLE G w)
    (hanti : ∀ G ∈ C, ∀ H ∈ C, G ≠ H → ¬ IsIsoMinor G H) : C.Finite := by
  classical
  by_contra hinf
  let f : ℕ ↪ C := Set.Infinite.natEmbedding C hinf
  let G : ℕ → Graph α β := fun n => (f n).val
  obtain ⟨i, j, hij, hm⟩ := exists_isIsoMinor_of_treeWidthLE w G
    (fun n => hV _ (f n).property) (fun n => hE _ (f n).property)
    (fun n => hwidth _ (f n).property)
  apply hanti (G i) (f i).property (G j) (f j).property ?_ hm
  intro heq
  exact hij.ne (f.injective (Subtype.ext heq))

/-- A graph with no vertices has tree-width zero: one empty bag. -/
theorem treeWidthLE_of_vertexSet_eq_empty {α : Type u} {β : Type v} {G : Graph α β}
    (hG : V(G) = ∅) (w : ℕ) : TreeWidthLE G w := by
  refine ⟨Unit, inferInstance, ⊥, fun _ => ∅, ⟨SimpleGraph.IsTree.of_subsingleton, ?_, ?_, ?_⟩, ?_⟩
  · simp [hG]
  · intro e a b hab
    exact absurd (hG ▸ hab.left_mem) (Set.notMem_empty a)
  · intro i j k _
    simp
  · intro i
    simp

/-- Putting a vertex `a` back into every bag of a tree-decomposition of
`G - a` gives a tree-decomposition of `G`. Its bags grow by at most one. -/
theorem treeWidthLE_succ_of_deleteVerts {α : Type u} {β : Type v} {G : Graph α β}
    {a : α} (ha : a ∈ V(G)) {w : ℕ} (h : TreeWidthLE (G.deleteVerts {a}) w) :
    TreeWidthLE G (w + 1) := by
  obtain ⟨ι, hι, T, X, hD, hw⟩ := h
  have hne : Nonempty ι := hD.isTree.connected.nonempty
  have hcover : ∀ y ∈ V(G), y ≠ a → ∃ i, y ∈ X i := by
    intro y hy hya
    have : y ∈ V(G.deleteVerts {a}) := by simp [hy, hya]
    rw [← hD.iUnion_eq] at this
    exact Set.mem_iUnion.1 this
  refine ⟨ι, hι, T, fun i => insert a (X i), ⟨hD.isTree, ?_, ?_, ?_⟩, ?_⟩
  · ext y
    simp only [Set.mem_iUnion, Set.mem_insert_iff]
    constructor
    · rintro ⟨i, rfl | hy⟩
      · exact ha
      · have : y ∈ V(G.deleteVerts {a}) := hD.iUnion_eq ▸ Set.mem_iUnion.2 ⟨i, hy⟩
        exact (by simpa using this : y ∈ V(G) ∧ ¬y = a).1
    · intro hy
      by_cases hya : y = a
      · exact ⟨Classical.arbitrary ι, Or.inl hya⟩
      · obtain ⟨i, hi⟩ := hcover y hy hya
        exact ⟨i, Or.inr hi⟩
  · intro e x y hxy
    by_cases hx : x = a
    · by_cases hy : y = a
      · exact ⟨Classical.arbitrary ι, Or.inl hx, Or.inl hy⟩
      · obtain ⟨i, hi⟩ := hcover y hxy.right_mem hy
        exact ⟨i, Or.inl hx, Or.inr hi⟩
    · by_cases hy : y = a
      · obtain ⟨i, hi⟩ := hcover x hxy.left_mem hx
        exact ⟨i, Or.inr hi, Or.inl hy⟩
      · have hlink : (G.deleteVerts {a}).IsLink e x y := by simp [hxy, hx, hy]
        obtain ⟨i, hxi, hyi⟩ := hD.edge_mem hlink
        exact ⟨i, Or.inr hxi, Or.inr hyi⟩
  · intro i j k hp z hz
    rcases hz with ⟨rfl | hzi, hzk⟩
    · exact Or.inl rfl
    · rcases hzk with rfl | hzk
      · exact Or.inl rfl
      · exact Or.inr (hD.inter_subset hp ⟨hzi, hzk⟩)
  · intro i
    exact (Set.ncard_insert_le a (X i)).trans (Nat.add_le_add_right (hw i) 1)

/-- A finite graph of tree-width more than `w` has a subgraph of tree-width more
than `w` and at most `w + 1`. Delete vertices one at a time while the tree-width
stays above `w`. When this has to stop, deleting any one vertex brings the
tree-width down to at most `w`, so `treeWidthLE_succ_of_deleteVerts` applies. -/
theorem exists_le_treeWidth_eq_succ {α : Type u} {β : Type v} (w : ℕ) :
    ∀ (n : ℕ) (G : Graph α β), V(G).Finite → V(G).ncard = n → ¬ TreeWidthLE G w →
      ∃ M ≤ G, ¬ TreeWidthLE M w ∧ TreeWidthLE M (w + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G hV hn hG
    obtain ⟨a, ha⟩ : V(G).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      exact fun h => hG (treeWidthLE_of_vertexSet_eq_empty h w)
    by_cases hdel : TreeWidthLE (G.deleteVerts {a}) w
    · exact ⟨G, le_rfl, hG, treeWidthLE_succ_of_deleteVerts ha hdel⟩
    · have hVdel : V(G.deleteVerts {a}).Finite := hV.subset (by simp)
      have hlt : V(G.deleteVerts {a}).ncard < n := by
        rw [← hn, Graph.vertexSet_deleteVerts]
        exact Set.ncard_sdiff_singleton_lt_of_mem ha hV
      obtain ⟨M, hM, hMw⟩ := ih _ hlt (G.deleteVerts {a}) hVdel rfl hdel
      exact ⟨M, hM.trans Graph.deleteVerts_le, hMw⟩

/-- Graph Minors II, (5.2), pages 320–321:
"For any fixed number $w$, there is a finite set of graphs $H_1, \dots, H_r$
such that for any graph $G$, $G$ has tree-width $> w$ if and only if $G$ has a
minor isomorphic to one of $H_1, \dots, H_r$."

The proof is the paper's (page 321). Every graph of tree-width more than `w`
contains, as a subgraph, one of tree-width exactly `w + 1`
(`exists_le_treeWidth_eq_succ`). Graphs of tree-width at most `w + 1` have no
infinite antichain by IV (1.5), as in (5.1), so finitely many of them cover all
others. Transferring bags along minor models proves that no graph of width at
most `w` contains one of these graphs. -/
theorem theorem_5_2_proof (w : ℕ) :
    ∃ B : Finset (Graph ℕ (ℕ × ℕ × ℕ)),
      (∀ H ∈ B, V(H).Finite ∧ E(H).Finite ∧ ¬ TreeWidthLE H w) ∧
      ∀ G : Graph ℕ (ℕ × ℕ × ℕ), V(G).Finite → E(G).Finite →
        (¬ TreeWidthLE G w ↔ ∃ H ∈ B, IsIsoMinor H G) := by
  classical
  let S : Set (Graph ℕ (ℕ × ℕ × ℕ)) :=
    {G | V(G).Finite ∧ E(G).Finite ∧ TreeWidthLE G (w + 1)}
  let C : Set (Graph ℕ (ℕ × ℕ × ℕ)) := {G | G ∈ S ∧ ¬ TreeWidthLE G w}
  have hseq : ∀ f : ℕ → Graph ℕ (ℕ × ℕ × ℕ),
      (∀ n, f n ∈ S) → ∃ i j, i < j ∧ IsIsoMinor (f i) (f j) := fun f hf =>
    exists_isIsoMinor_of_treeWidthLE (w + 1) f (fun n => (hf n).1) (fun n => (hf n).2.1)
      (fun n => (hf n).2.2)
  obtain ⟨B, hB, hbasis⟩ := GM13.exists_finset_basis_of_forall_seq
    (S := S) (T := C) (fun _ h => h.1) hseq
  refine ⟨B, ?_, ?_⟩
  · intro H hH
    exact ⟨(hB hH).1.1, (hB hH).1.2.1, (hB hH).2⟩
  · intro G hVG hEG
    constructor
    · intro hwidth
      obtain ⟨M, hMG, hMw, hMw1⟩ :=
        exists_le_treeWidth_eq_succ w _ G hVG rfl hwidth
      have hMC : M ∈ C := ⟨⟨hVG.subset (hMG.vertexSet_mono),
        hEG.subset (hMG.edgeSet_mono), hMw1⟩, hMw⟩
      obtain ⟨H, hH, hHM⟩ := hbasis M hMC
      exact ⟨H, hH, hHM.trans (GM10.isIsoMinor_of_le hMG)⟩
    · rintro ⟨H, hH, hm⟩ hwidth
      exact (hB hH).2 (hwidth.of_isIsoMinor hVG hEG hm)

end GraphMinor.GM02
