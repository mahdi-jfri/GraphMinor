module

public import GraphMinor.GM13.Section10a
import GraphMinor.GM21.Final
import GraphMinor.GM22.Join21
import GraphMinor.GM22.Section8To13

/-!
# The proof of Graph Minors XIII, (10.2)

Combine XXII's derivation of XIII (10.2) with the proved XXI (1.1).
Keeping this proof separate lets Section 10 use it without importing its own
later corollaries.
-/

public section

namespace GraphMinor.GM13

universe u v

/-- **Graph Minors XIII, (10.2)** (Section 10, page 107), proved in Graph Minors XXII, Section 8
(page 563) and instantiated at `GM21.theorem_1_1_proof`:
“(10.2) *For any $q$, $\delta \ge 0$ and $h \ge 2$, even, there exists $f(h) \ge h$, even, such
that under Hypothesis C, if $H' \subseteq H$ is an $h$-homogeneous subwall of height $f(h)$ then
both middle vertices of $H'$ are irrelevant to the $\delta$-folio of $G$ relative to $X$.*” -/
theorem theorem_10_2_proof : GM13Theorem102Statement.{u, v} :=
  GM22.gm13_theorem_10_2.{u, v}
    (GM22.gm21Theorem11Statement_iff_gm21.mpr GM21.theorem_1_1_proof.{u, v})

end GraphMinor.GM13
