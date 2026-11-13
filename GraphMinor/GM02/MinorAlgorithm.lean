module

public import GraphMinor.Compute.GM02MinorPatternScan
import GraphMinor.Compute.GM02MinorPatternList

/-!
# Minor recognition with a width alternative: Graph Minors II (4.9)

Follow the paper's finite-pattern proof. Obtain the fixed family from
(4.8), number its members once, and execute the complete (4.7) programs
in order. A successful topological test gives the desired minor, while
exclusion of every pattern rules it out. The scan's time is polynomial
in the original host size and its input is only the host edge list.
-/

public section
namespace GraphMinor.GM02
open Graph Set GraphMinor.Compute

/-- Graph Minors II, (4.9), page 320:
"For any fixed graph $H$ and fixed number $w$, there is a polynomial algorithm which has input a graph $G$, and has output either"

"(i) $G$ has a minor isomorphic to $H$, or"
"(ii) $G$ has no minor isomorphic to $H$, or"
"(iii) $G$ has tree-width $> w$."

Apply the complete (4.7) program to the fixed finite pattern family of
(4.8), in order, exactly as in the paper's proof. Each pattern's input
is constructed from the ordinary host encoding by the RAM. -/
theorem algorithm_4_9_proof {A B : Type*} (H : Graph A B)
    (hV : V(H).Finite) (hE : E(H).Finite) (w : ℤ) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime GM02EdgeListInput.size (fun G s => s.arrs inArr = G.enc)
        (fun G s => (s.regs outReg = 1 ∧ IsIsoMinor H G.graph) ∨
          (s.regs outReg = 0 ∧ ¬IsIsoMinor H G.graph) ∨
          (s.regs outReg = 2 ∧ w < (treeWidth G.graph G.finite_vertices G.finite_edges : ℕ)))
        P (fun n => (n + 1) ^ c) := by
  obtain ⟨ps, hp⟩ := exists_gm02MinorPatternList H hV hE
  obtain ⟨C, c, hC, hc, hex⟩ := gm02MinorPatternScan_computes ps w
  refine ⟨gm02MinorPatternScanProg ps w, gm02PatternListExponent ps w, C, c, hC, hc, ?_⟩
  intro G s hsrc
  obtain ⟨s', t, he, ht, hout⟩ := hex G s hsrc
  refine ⟨s', t, he, ht, ?_⟩
  rcases hout with ⟨hf, hcontains⟩ | ⟨hf, hnone⟩ | hout
  · exact Or.inl ⟨hf, (hp G).2 hcontains⟩
  · exact Or.inr (Or.inl ⟨hf, fun hm => hnone ((hp G).1 hm)⟩)
  · exact Or.inr (Or.inr hout)

end GraphMinor.GM02
