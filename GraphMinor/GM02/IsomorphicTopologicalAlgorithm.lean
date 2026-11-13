module

public import GraphMinor.Compute.GM02Algorithm47
import GraphMinor.Compute.GM02FiniteEdgeListPresentation

/-!
# Isomorphic topological containment: Graph Minors II (4.7)

Follow the paper's injection search. Number the fixed target once,
then let the RAM enumerate vertex injections, construct each labelled
input, and execute (4.6). The proved bounds give polynomial time from
the plain host encoding. The target isomorphism transfers both the
positive and negative answers back to the original fixed graph.
-/

public section
namespace GraphMinor.GM02
open Graph Set GraphMinor.Compute

private theorem correct_of_iso {A B A' B' : Type*} {H : Graph A B} {J : Graph A' B'}
    (φ : Iso H J) (w : ℤ) (G : GM02EdgeListInput) (s : State)
    (h : gm02IsomorphicTopologicalCorrect J w G s) : gm02IsomorphicTopologicalCorrect H w G s := by
  rcases h with ⟨hf, L, ht, ⟨ψ⟩⟩ | ⟨hf, hn⟩ | h
  · exact Or.inl ⟨hf, L, ht, ⟨φ.trans ψ⟩⟩
  · refine Or.inr (Or.inl ⟨hf, ?_⟩)
    rintro ⟨L, ht, ⟨ψ⟩⟩
    exact hn ⟨L, ht, ⟨φ.symm.trans ψ⟩⟩
  · exact Or.inr (Or.inr h)

/-- Graph Minors II, (4.7), page 319, with its proof on page 320:
"For any fixed graph $H$ and fixed integer $w$, there is a polynomial algorithm which has input a graph $G$, and which has output one of"

"(i) there is a graph isomorphic to $H$ topologically contained by $G$, or"
"(ii) there is no such graph, or"
"(iii) $G$ has tree-width $> w$."

Enumerate vertex injections as in the paper and run the complete (4.6)
program on each constructed labelled input. The fixed graph is numbered
once, and the host input contains only its original edge-list encoding. -/
theorem algorithm_4_7_proof {A B : Type*} (H : Graph A B)
    (hV : V(H).Finite) (hE : E(H).Finite) (w : ℤ) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime GM02EdgeListInput.size (fun G s => s.arrs inArr = G.enc)
        (fun G s => gm02IsomorphicTopologicalCorrect H w G s) P (fun n => (n + 1) ^ c) := by
  obtain ⟨J, ⟨φ⟩⟩ := exists_gm02EdgeListPresentation H hV hE
  let q := max w.toNat 2 + 2 * J.edges.length + 1
  obtain ⟨C, c, hC, hc, hex⟩ := gm02Algorithm47_computes J w
  refine ⟨gm02InjectionDecisionProg J q, gm02InjectionPolynomialExponent q J,
    C, c, hC, hc, ?_⟩
  intro G s hsrc
  obtain ⟨s', t, he, ht, hout⟩ := hex G s hsrc
  exact ⟨s', t, he, ht, correct_of_iso φ w G s' hout⟩

end GraphMinor.GM02
