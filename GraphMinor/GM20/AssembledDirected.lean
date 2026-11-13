module

public import GraphMinor.GM07.Bridge
public import GraphMinor.GM07.CuffSlide
public import GraphMinor.GM07.Section35
public import GraphMinor.GM07.Defs
public import GraphMinor.GM07.Open
public import GraphMinor.GM07.Section7
public import GraphMinor.GM07.Section9
public import GraphMinor.GM09.Bridge
public import GraphMinor.GM11.Cited
public import GraphMinor.GM12.Bridge
public import GraphMinor.GM12.Cited
public import GraphMinor.GM12.Section5Final
public import GraphMinor.GM12.Section6
public import GraphMinor.GM12.Section710
public import GraphMinor.GM12.Section76
public import GraphMinor.GM12.Section77
public import GraphMinor.GM14.Adapted
public import GraphMinor.GM14.Bridge
public import GraphMinor.GM14.Cited
public import GraphMinor.GM14.Section8Core
public import GraphMinor.GM14.Section9a
public import GraphMinor.GM14.Section9b
public import GraphMinor.GM14.Whitney
public import GraphMinor.GM12.Section75Proof
public import GraphMinor.GM15.Cited
public import GraphMinor.GM15.Section3
public import GraphMinor.GM15.Section3Crosscap
public import GraphMinor.GM15.Section3Handle
public import GraphMinor.GM15.Section3Parallel
public import GraphMinor.GM15.Section4
public import GraphMinor.GM16.Cited
public import GraphMinor.GM16.Defs
public import GraphMinor.GM16.MainProof
public import GraphMinor.GM16.Section4
public import GraphMinor.GM16.Section4Proof
public import GraphMinor.GM16.Section5
public import GraphMinor.GM16.Section5Five
public import GraphMinor.GM16.Theorem35Bridge
public import GraphMinor.GM16.Tower
public import GraphMinor.GM17.Bridge
public import GraphMinor.GM17.PushNode
public import GraphMinor.GM17.RegionBoundary
public import GraphMinor.GM17.RegionDisc
public import GraphMinor.GM17.Section5
public import GraphMinor.GM17.Section8
public import GraphMinor.GM19.Cited
public import GraphMinor.GM19.Conditional
public import GraphMinor.GM19.Conditional2
public import GraphMinor.GM19.FeatureCount
public import GraphMinor.GM19.FragmentForm
public import GraphMinor.GM19.FragmentOrient
public import GraphMinor.GM19.FragmentSimpler
public import GraphMinor.GM19.Section10f
public import GraphMinor.GM19.Section10s
public import GraphMinor.GM19.Section10t
public import GraphMinor.GM19.Section11g
public import GraphMinor.GM19.Section14ah
public import GraphMinor.GM19.Section15b
public import GraphMinor.GM19.Section15q
public import GraphMinor.GM19.Section2
public import GraphMinor.GM19.Section5o
public import GraphMinor.GM19.Section5r
public import GraphMinor.GM19.Section6a
public import GraphMinor.GM19.Section6Five
public import GraphMinor.GM19.Section6Six
public import GraphMinor.GM19.Section6Two
public import GraphMinor.GM19.Thinning
public import GraphMinor.GM20.Cited
public import GraphMinor.GM20.Main
public import GraphMinor.Surface.Cuffs
public import GraphMinor.Surface.TopologyStatements

import GraphMinor.GM16.InductionsProved

import GraphMinor.GM17.Section8Proved

import GraphMinor.GM19.Section2Proved

import GraphMinor.GM19.Section5oProved

import GraphMinor.GM19.Section6aProved

/-!
# The directed graph minor theorem, assembled

`GM20.theorem_10_5_assembled` proves (10.5) of Graph Minors XX for directed graphs at all universes,
with no hypotheses, discharging every cited statement along the same chain as
`GM20.graph_minor_theorem_assembled` in `GraphMinor/GM20/Assembled.lean`.
-/

@[expose] public section

namespace GraphMinor.GM20

open Graph

/-- Graph Minors XX, (10.5) (page 355), assembled with no hypotheses:
"**10.5.** *Let* $G_i$ $(i = 1, 2, \dots)$ *be a countable sequence of directed graphs. Then there exist* $j > i \ge 1$ *such that* $G_i$ *is isomorphic to a minor of* $G_j$." -/
theorem theorem_10_5_assembled
    {α β : Type*} (G : ℕ → Digraph α β) (hV : ∀ n, V((G n).toGraph).Finite)
    (hE : ∀ n, E((G n).toGraph).Finite) :
    ∃ i j, i < j ∧ (G i).IsIsoMinor (G j) := by
  exact theorem_10_5_proof G hV hE

end GraphMinor.GM20
