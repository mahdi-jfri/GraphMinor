module

public import GraphMinor.Compute.Case3StepsEncodedComponents

/-!
# Component searches from the retained multigraph

The (8.6) call may overwrite its input. The compact multigraph is retained,
so the program reconstructs its simple encoding before computing the
outside-component rows. Parallel edges and loops remain in the retained
multigraph for the later member encoding.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- The underlying simple graph has at most one entry per active multigraph pair. -/
theorem case3InputEdges_length_le (x : Alg81Input) (D : MultiDigraph x.n)
    (hDG : D.toSimpleGraph = x.G) :
    (case3InputEdges x).length ≤ D.numActivePairs := by
  have ht := length_toSimplePairsAux_le x.n x.n D.activePairsList
  rw [MultiDigraph.toSimplePairsAux_activePairsList] at ht
  simpa only [case3InputEdges, hDG, MultiDigraph.numActivePairs] using ht

/-- Read the compact multigraph from array 3 and its core bitset from array 10.
The component table is written to array 12. -/
def case3MultigraphComponentsProg : Cmd :=
  .seq (toSimpleGraphEdgeListProg 3 14 16 32) case3EncodedComponentsProg

/-- Reconstructing the simple encoding and computing components preserves the
compact multigraph, the original rank array, and every array below 10. -/
theorem case3MultigraphComponentsProg_exec {w : ℕ} (x : Alg81Input)
    (D : MultiDigraph x.n) (hDG : D.toSimpleGraph = x.G)
    (Z : Finset (Fin x.n)) (hw : 3 < 2 ^ w)
    (hn : x.n + 1 < 2 ^ w) (hsq : x.n * x.n < 2 ^ w)
    (hm : 2 + 3 * D.numActivePairs < 2 ^ w)
    {s : State} (hD : s.arrs 3 = D.enc) (hZ : IsBitSet Z 10 s) :
    ∃ s' t, Exec w case3MultigraphComponentsProg s s' t ∧
      t ≤ x.n * x.n + x.n * (38 * x.n + 52 * D.numActivePairs + 47) +
        64 * x.n + 236 * D.numActivePairs + 139 ∧
      s'.arrs 12 = case3ComponentRows x Z ∧ s'.arrs 10 = bitSetList Z ∧
      (∀ a < 10, s'.arrs a = s.arrs a) ∧
      IsAdjList x.G 19 20 21 (edgeNeighbors (edgeListOf x.G)) s' ∧
      (s'.arrs 21).length = 2 * (edgeListOf x.G).length ∧ s'.regs 14 = x.n := by
  have hnw : x.n < 2 ^ w := by romega
  have hsimp : (edgeListOf x.G).length ≤ D.numActivePairs := by
    have ht := length_toSimplePairsAux_le x.n x.n D.activePairsList
    rw [MultiDigraph.toSimplePairsAux_activePairsList] at ht
    simpa only [hDG, MultiDigraph.numActivePairs] using ht
  obtain ⟨s₁, t₁, hex₁, ht₁, henc₁, _, _, harr₁, _⟩ :=
    toSimpleGraphEdgeListProg_exec D [] 3 14 16 32 (by decide) (by decide)
      hw hnw hm (by simpa only [List.append_nil] using hD)
  have hinput : s₁.arrs 16 = encGraph x.G := by simpa only [hDG] using henc₁
  obtain ⟨s₂, t₂, hex₂, ht₂, hdst₂, hZ₂, harr₂, hadj₂, hlen₂, hr14₂⟩ :=
    case3EncodedComponentsProg_exec x Z (by romega) hn hsq (by romega) hinput
      (hZ.of_arr_eq (harr₁ 10 (by decide) (by decide)))
  have hmul := Nat.mul_le_mul_left x.n (show
      38 * x.n + 52 * (edgeListOf x.G).length + 47 ≤
        38 * x.n + 52 * D.numActivePairs + 47 by romega)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by romega, hdst₂, hZ₂, ?_, hadj₂, hlen₂, hr14₂⟩
  intro a ha
  rw [harr₂ a ha]
  exact harr₁ a (by romega) (by romega)

end GraphMinor.Compute
