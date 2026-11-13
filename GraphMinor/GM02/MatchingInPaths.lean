module

public import GraphMinor.GM02.TerminationGraph
public import GraphMinor.GM02.ListEdgeGraph
import GraphMinor.GM02.DisjointPathCycles

/-!
# Matching uniqueness in disjoint paths

Two matchings with the same support differ by a graph of cycles. If both
lie in a disjoint union of paths, that graph is empty by leaf removal.
This recovers the actual termination pairs from their supports and the
path graph in the counting proof of II (2.8).
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
open scoped symmDiff
universe u t

/-- Inside a disjoint union of path lists, the support determines a
termination matching uniquely. -/
theorem Termination.eq_of_support_in_paths {α : Type u} {I : Type t}
    {vertices : Set α} (A B : Termination vertices) {F : SimpleGraph α}
    (P : I → List α) (hP : ∀ i, (P i).Nodup)
    (hdis : ∀ i j, i ≠ j → Disjoint {a | a ∈ P i} {a | a ∈ P j})
    (hcover : ∀ a b, F.Adj a b → ∃ i, (listEdgeGraph (P i)).Adj a b)
    (hAF : A.pairGraph ≤ F) (hBF : B.pairGraph ≤ F) (hS : A.support = B.support) : A = B := by
  have hdiff : A.pairGraph ∆ B.pairGraph ≤ F := by
    intro a b hab
    change (A.pairGraph.Adj a b ∧ ¬B.pairGraph.Adj a b) ∨
      (B.pairGraph.Adj a b ∧ ¬A.pairGraph.Adj a b) at hab
    exact hab.elim (fun h => hAF h.1) (fun h => hBF h.1)
  have hempty := cycles_eq_bot_of_disjoint_list_cover P hP hdis hcover hdiff
    (A.symmDiff_isCycles B hS)
  have hgraphs : A.pairGraph = B.pairGraph := symmDiff_eq_bot.1 hempty
  apply Termination.ext_pairs
  apply Finset.ext
  intro p
  induction p using Sym2.inductionOn with
  | hf a b =>
    rw [← A.pairGraph_adj_iff, ← B.pairGraph_adj_iff, hgraphs]

end GraphMinor.GM02
