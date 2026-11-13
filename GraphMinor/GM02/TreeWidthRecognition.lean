module

public import GraphMinor.GM02.MultiMinorScan
import GraphMinor.GM02.FiniteObstructions
import GraphMinor.GM02.MinorWidth
import GraphMinor.GM10.Section4Contraction
import GraphMinor.GM13.Section4

/-!
# Fixed tree-width recognition in Graph Minors II

The paper (page 321) proves (5.3) by running the program of (4.9) for each graph
of the finite set of (5.2), and (1.2) is the same statement. For (5.4) it leaves
the details to the reader: the minimal graphs outside the class have tree-width
at most `w + 1`, so (5.1) leaves finitely many of them, and the program of (4.9)
for these graphs decides membership.

The input is the multigraph encoding `x.G.enc`. The programs first cap the
multiplicities and write out the edge list (`exists_multiMinorScan`). Their time
is polynomial in `(n + 1)²`, where `n` is the number of vertices.
-/

public section

namespace GraphMinor.GM02

open Graph GraphMinor.Compute Set Classical

universe u v

/-- Increasing the width bound preserves a tree-decomposition. -/
theorem TreeWidthLE.mono {α β : Type*} {G : Graph α β} {k w : ℕ}
    (h : TreeWidthLE G k) (hkw : k ≤ w) : TreeWidthLE G w := by
  obtain ⟨ι, _, T, X, hD, hw⟩ := h
  exact ⟨ι, inferInstance, T, X, hD,
    fun i => (hw i).trans (Nat.add_le_add_right hkw 1)⟩

/-- The program that answers zero, in constant time. -/
theorem computesRelInTime_answer_zero {α : Type*} (size : α → ℕ) (In : α → State → Prop) :
    ComputesRelInTime size In (fun _ s => s.regs outReg = 0)
      (.assign outReg (.const 0)) (fun n => (n + 1) ^ 1) := by
  refine ⟨2, 1, by norm_num, le_rfl, fun x s _ => ⟨s.setReg outReg 0, 2,
    .assign (by simp [Expr.eval, checkWord]), ?_, by simp⟩⟩
  simp only [pow_one]
  omega

/-- Graph Minors II, (5.3), page 321:
"For any fixed number $w$, there is a polynomial algorithm which, given a
graph $G$, decides if $G$ has tree-width $> w$."

The proof is the paper's: run the program of (4.9) for each graph of the finite
set of (5.2) (`exists_multiMinorScan`). If one is a minor, or the program finds
tree-width above `w`, the tree-width is above `w`. Otherwise it is at most `w`
by (5.2). The program returns zero exactly when the graph has tree-width above
`w`, and one otherwise. A negative `w` is allowed: then no graph qualifies, and
the program answers zero. -/
theorem algorithm_5_3_proof (w : ℤ) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime alg44Size (fun x s => s.arrs inArr = x.G.enc)
        (fun x s => s.regs outReg = if (∃ k : ℕ, (k : ℤ) ≤ w ∧
          TreeWidthLE x.G.toGMDigraph.toGraph k) then 1 else 0)
        P (fun n => (n + 1) ^ c) := by
  rcases lt_or_ge w 0 with hw | hw
  · refine ⟨.assign outReg (.const 0), 1, ?_⟩
    obtain ⟨C, c, hC, hc, run⟩ := computesRelInTime_answer_zero alg44Size
      (fun x s => s.arrs inArr = x.G.enc)
    refine ⟨C, c, hC, hc, fun x s hs => ?_⟩
    obtain ⟨s', t, he, ht, hout⟩ := run x s hs
    refine ⟨s', t, he, ht, ?_⟩
    show s'.regs outReg = _
    rw [hout, ite_eq_right]
    rintro ⟨k, hk, -⟩
    omega
  · obtain ⟨B, hB, hchar⟩ := theorem_5_2_proof w.toNat
    obtain ⟨P, c, hP⟩ := exists_multiMinorScan B (fun H hH => ⟨(hB H hH).1, (hB H hH).2.1⟩) w
    obtain ⟨C, cw, hC, hcw, run⟩ := ComputesRelInTime.seq_isZero hP (by
      rintro x s (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> omega)
    refine ⟨.seq P isZeroOutProg, c, C, cw, hC, hcw, fun x s hs => ?_⟩
    · obtain ⟨s', t, he, ht, s₀, hout, hval⟩ := run x s hs
      refine ⟨s', t, he, ht, ?_⟩
      have hfin := x.G.isFinite_toGMDigraph
      have hiff := hchar x.G.toGMDigraph.toGraph hfin.finite_V hfin.finite_E
      show s'.regs outReg = _
      rw [hval]
      rcases hout with ⟨h1, hm⟩ | ⟨h0, hno⟩ | ⟨h2, hlt⟩
      · rw [ite_eq_right (by omega), ite_eq_right]
        rintro ⟨k, hk, htw⟩
        exact hiff.2 hm (htw.mono (by omega))
      · rw [ite_eq_left h0, ite_eq_left]
        refine ⟨w.toNat, by omega, ?_⟩
        by_contra hnot
        obtain ⟨H, hH, hm⟩ := hiff.1 hnot
        exact hno H hH hm
      · rw [ite_eq_right (by omega), ite_eq_right]
        rintro ⟨k, hk, htw⟩
        exact hlt k hk htw

/-- Graph Minors II, (1.2), page 310:
"For any fixed integer $w$, there is a polynomial algorithm to decide if the
input graph has tree-width $\le w$."

This is (5.3) (`algorithm_5_3`), as in the paper. The program returns one for
tree-width at most `w` and zero otherwise. -/
theorem algorithm_1_2_proof (w : ℤ) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime alg44Size (fun x s => s.arrs inArr = x.G.enc)
        (fun x s => s.regs outReg = if (∃ k : ℕ, (k : ℤ) ≤ w ∧
          TreeWidthLE x.G.toGMDigraph.toGraph k) then 1 else 0)
        P (fun n => (n + 1) ^ c) :=
  algorithm_5_3_proof w

/-- Deleting vertices one at a time while a property holds ends in a subgraph
that has the property, while deleting any one of its vertices destroys it. -/
theorem exists_le_minimal_deleteVerts {α : Type u} {β : Type v} (Prop' : Graph α β → Prop) :
    ∀ (n : ℕ) (G : Graph α β), V(G).Finite → V(G).ncard = n → Prop' G →
      ∃ M ≤ G, Prop' M ∧ ∀ a ∈ V(M), ¬ Prop' (M.deleteVerts {a}) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G hV hn hG
    by_cases hall : ∀ a ∈ V(G), ¬ Prop' (G.deleteVerts {a})
    · exact ⟨G, le_rfl, hG, hall⟩
    · push Not at hall
      obtain ⟨a, ha, hdel⟩ := hall
      have hVdel : V(G.deleteVerts {a}).Finite := hV.subset (by simp)
      have hlt : V(G.deleteVerts {a}).ncard < n := by
        rw [← hn, Graph.vertexSet_deleteVerts]
        exact Set.ncard_sdiff_singleton_lt_of_mem ha hV
      obtain ⟨M, hM, hMP⟩ := ih _ hlt (G.deleteVerts {a}) hVdel rfl hdel
      exact ⟨M, hM.trans Graph.deleteVerts_le, hMP⟩

/-- For (5.4): a minor-closed class whose members have tree-width at most `w` is
described by finitely many excluded minors. A minimal graph outside the class
has tree-width at most `w + 1`: deleting a vertex gives a member, of tree-width
at most `w`, and putting the vertex back into every bag adds one. By IV (1.5)
the graphs of tree-width at most `w + 1` have no infinite antichain, as in
(5.1), so finitely many of them cover all graphs outside the class. -/
theorem exists_excluded_minors_of_treeWidthLE
    (ℱ : Set (Graph ℕ (ℕ × ℕ × ℕ)))
    (hclosed : ∀ ⦃G₁ G₂ : Graph ℕ (ℕ × ℕ × ℕ)⦄,
      V(G₁).Finite → E(G₁).Finite → V(G₂).Finite → E(G₂).Finite →
      IsIsoMinor G₁ G₂ → G₂ ∈ ℱ → G₁ ∈ ℱ)
    (w : ℕ)
    (hwidth : ∀ G ∈ ℱ, V(G).Finite → E(G).Finite → TreeWidthLE G w) :
    ∃ B : Finset (Graph ℕ (ℕ × ℕ × ℕ)),
      (∀ H ∈ B, V(H).Finite ∧ E(H).Finite ∧ H ∉ ℱ) ∧
      ∀ G : Graph ℕ (ℕ × ℕ × ℕ), V(G).Finite → E(G).Finite →
        (G ∈ ℱ ↔ ∀ H ∈ B, ¬ IsIsoMinor H G) := by
  let S : Set (Graph ℕ (ℕ × ℕ × ℕ)) :=
    {G | V(G).Finite ∧ E(G).Finite ∧ TreeWidthLE G (w + 1)}
  let T : Set (Graph ℕ (ℕ × ℕ × ℕ)) := {G | G ∈ S ∧ G ∉ ℱ}
  have hseq : ∀ f : ℕ → Graph ℕ (ℕ × ℕ × ℕ),
      (∀ n, f n ∈ S) → ∃ i j, i < j ∧ IsIsoMinor (f i) (f j) := fun f hf =>
    exists_isIsoMinor_of_treeWidthLE (w + 1) f (fun n => (hf n).1) (fun n => (hf n).2.1)
      (fun n => (hf n).2.2)
  obtain ⟨B, hB, hbasis⟩ := GM13.exists_finset_basis_of_forall_seq
    (S := S) (T := T) (fun _ h => h.1) hseq
  refine ⟨B, fun H hH => ⟨(hB hH).1.1, (hB hH).1.2.1, (hB hH).2⟩, fun G hVG hEG => ⟨?_, ?_⟩⟩
  · intro hG H hH hm
    exact (hB hH).2 (hclosed (hB hH).1.1 (hB hH).1.2.1 hVG hEG hm hG)
  · intro hall
    by_contra hG
    obtain ⟨M, hMG, hM, hmin⟩ :=
      exists_le_minimal_deleteVerts (fun M => M ∉ ℱ) _ G hVG rfl hG
    have hVM : V(M).Finite := hVG.subset hMG.vertexSet_mono
    have hEM : E(M).Finite := hEG.subset hMG.edgeSet_mono
    have hMw : TreeWidthLE M (w + 1) := by
      by_cases hne : V(M).Nonempty
      · obtain ⟨a, ha⟩ := hne
        have hdel : M.deleteVerts {a} ∈ ℱ := not_not.1 (hmin a ha)
        exact treeWidthLE_succ_of_deleteVerts ha (hwidth _ hdel (hVM.subset (by simp))
          (hEM.subset (Graph.deleteVerts_le (G := M)).edgeSet_mono))
      · exact treeWidthLE_of_vertexSet_eq_empty (Set.not_nonempty_iff_eq_empty.1 hne) _
    obtain ⟨H, hH, hHM⟩ := hbasis M ⟨⟨hVM, hEM, hMw⟩, hM⟩
    exact hall H hH (hHM.trans (GM10.isIsoMinor_of_le hMG))

/-- Graph Minors II, (5.4), page 321:
"Let $\mathcal{F}$ be a set of graphs, such that for any two graphs $G$, $G'$,
if $G \in \mathcal{F}$ and $G'$ is isomorphic to a minor of $G$ then
$G' \in \mathcal{F}$. Suppose that there is a number $w$ such that all members
of $\mathcal{F}$ have tree-width $\le w$. Then there is a polynomial algorithm
to test if an arbitrary graph is in $\mathcal{F}$."

The paper leaves the proof to the reader as an extension of (5.3). The minimal
graphs outside the class form a finite set
(`exists_excluded_minors_of_treeWidthLE`), and the program of (4.9) for these
graphs decides membership: a graph with one of them as a minor, or of
tree-width above `w`, is outside the class. The program returns one for
members and zero otherwise. -/
theorem algorithm_5_4_proof
    (ℱ : Set (Graph ℕ (ℕ × ℕ × ℕ)))
    (hclosed : ∀ ⦃G₁ G₂ : Graph ℕ (ℕ × ℕ × ℕ)⦄,
      V(G₁).Finite → E(G₁).Finite → V(G₂).Finite → E(G₂).Finite →
      IsIsoMinor G₁ G₂ → G₂ ∈ ℱ → G₁ ∈ ℱ)
    (w : ℕ)
    (hwidth : ∀ G ∈ ℱ, V(G).Finite → E(G).Finite → TreeWidthLE G w) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime alg44Size (fun x s => s.arrs inArr = x.G.enc)
        (fun x s => s.regs outReg = if x.G.toGMDigraph.toGraph ∈ ℱ then 1 else 0)
        P (fun n => (n + 1) ^ c) := by
  obtain ⟨B, hB, hchar⟩ := exists_excluded_minors_of_treeWidthLE ℱ hclosed w hwidth
  obtain ⟨P, c, hP⟩ := exists_multiMinorScan B (fun H hH => ⟨(hB H hH).1, (hB H hH).2.1⟩) w
  obtain ⟨C, cw, hC, hcw, run⟩ := ComputesRelInTime.seq_isZero hP (by
    rintro x s (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> omega)
  refine ⟨.seq P isZeroOutProg, c, C, cw, hC, hcw, fun x s hs => ?_⟩
  obtain ⟨s', t, he, ht, s₀, hout, hval⟩ := run x s hs
  refine ⟨s', t, he, ht, ?_⟩
  have hfin := x.G.isFinite_toGMDigraph
  have hiff := hchar x.G.toGMDigraph.toGraph hfin.finite_V hfin.finite_E
  show s'.regs outReg = _
  rw [hval]
  rcases hout with ⟨h1, H, hH, hm⟩ | ⟨h0, hno⟩ | ⟨h2, hlt⟩
  · rw [ite_eq_right (by omega), ite_eq_right]
    exact fun hmem => hiff.1 hmem H hH hm
  · rw [ite_eq_left h0, ite_eq_left (hiff.2 hno)]
  · rw [ite_eq_right (by omega), ite_eq_right]
    exact fun hmem => hlt w le_rfl (hwidth _ hmem hfin.finite_V hfin.finite_E)

end GraphMinor.GM02
