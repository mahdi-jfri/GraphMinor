module

public import GraphMinor.Wagner.K33Wagner
public import GraphMinor.Wagner.CliqueSumMinor

/-!
# Graph Minors XVI, (1.2): Wagner's theorem

This file states and proves (1.2) of N. Robertson and P. D. Seymour, *Graph Minors. XVI. Excluding
a non-planar graph*, J. Combin. Theory Ser. B 89 (2003) 43–76, which quotes Wagner (1937): a finite
graph has no `K_5` minor if and only if it is a tree-structure over the class of graphs that are
planar or isomorphic to `V_8` (`GM16.theorem_1_2_proof`).

Edges of the pieces of a tree-structure come from `β ⊕ ℕ`, since clique-sums add new edges. So the
statement is about `liftEdgeInl G`, the copy of `G` with edges `Sum.inl e`.

* The "if" direction is `Wagner.not_isIsoMinor_completeGraph_five_of_hasTreeStructureOver`:
  planar graphs and `V_8` have no `K_5` minor, and clique-sums of at most three vertices keep this.
* The "only if" direction reduces to simple graphs on `Fin N`
  (`Wagner.hasTreeStructureOver_of_finSimple_step`), and then to internally `4`-connected graphs
  (`Wagner.finSimple_dichotomy_of_internally4Conn`). These are planar or isomorphic to `V_8` by
  `Wagner.planar_or_v8_of_internally4Conn`.

The small cases agree with the statement as written: the null graph, one vertex with a loop, `K_4`
and `V_8` satisfy both sides (`Wagner.smallCase_bot`, `Wagner.smallCase_single_loop`,
`Wagner.smallCase_K4`, `Wagner.smallCase_V8`).
-/

@[expose] public section

namespace GraphMinor.GM16

open Set Graph

variable {α : Type*} {β : Type*}

/-- **Graph Minors XVI, (1.2)** (Wagner).

"**1.2.** *A graph $G$ has no $K_5$ minor if and only if $G$ is a tree-structure over the class of
all graphs which are either planar or isomorphic to $V_8$.*" -/
theorem theorem_1_2_proof (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) :
    ¬ IsIsoMinor (completeGraph 5) G ↔
      HasTreeStructureOver
        {H : Graph α (β ⊕ ℕ) | IsPlanar H ∨ Nonempty (Iso H wagnerGraphV8)} (liftEdgeInl G) :=
  ⟨fun h => Wagner.hasTreeStructureOver_of_finSimple_step
      (fun N hN K hK => Wagner.finSimple_dichotomy_of_internally4Conn
        (fun _ _ hi hK5 => Wagner.planar_or_v8_of_internally4Conn hi hK5) N hN K hK) hV hE h,
    Wagner.not_isIsoMinor_completeGraph_five_of_hasTreeStructureOver hV hE⟩

end GraphMinor.GM16
