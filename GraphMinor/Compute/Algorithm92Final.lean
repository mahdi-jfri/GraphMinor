module

public import GraphMinor.Compute.Algorithm92Main
public import GraphMinor.Compute.F92Program

/-!
# Graph Minors XIII, (9.2): the algorithm (`Algorithm92Final.lean`)

**(9.2)** (page 99 of Graph Minors XIII). The program that finds `F` is proved to meet
`F92ProgClaim` (`f92ProgClaim_proved`, `F92Program.lean`), and `algorithm_9_2_of_F92`
(`Algorithm92Main.lean`) gives the rest of the algorithm. Together they prove
`Algorithm92Statement` with no hypothesis.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- **The algorithm of Graph Minors XIII, (9.2) (page 99)** on the Word RAM. -/
theorem gm13_algorithm_9_2 : Algorithm92Statement :=
  algorithm_9_2_of_F92 f92ProgClaim_proved

end GraphMinor.Compute.Alg92
