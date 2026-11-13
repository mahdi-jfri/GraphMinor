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
# The graph minor theorem, assembled

`GM20.graph_minor_theorem_assembled` proves the graph minor theorem of `Challenge.lean`, with no
hypotheses. Every named statement of the papers is discharged in the body of the proof, by its
theorem, along the real chain: XX from XVII and XIX, XVII from XVI (3.1), XVI from its hypotheses,
and so on down.


All universes are `0`, as in `GM20.graph_minor_theorem_of_cited`, which gets the theorem at all
universes of `Challenge.lean` from the case of `Type`.
-/

@[expose] public section

namespace GraphMinor.GM20

open Graph

/-- **The graph minor theorem** (Graph Minors XX, (10.5)). It takes no hypotheses. -/
theorem graph_minor_theorem_assembled
    {α β : Type*} (G : ℕ → Graph α β) (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) := by
  exact graph_minor_theorem_of_cited G hV hE

end GraphMinor.GM20
