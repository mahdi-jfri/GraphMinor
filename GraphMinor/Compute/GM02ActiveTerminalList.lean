module

public import GraphMinor.Compute.GM02FullPortIncidence
public import GraphMinor.Compute.GM02CanonicalEdgeOrder

/-!
# The ordered list of active numeric terminal pairs

Scan original pattern edge positions in their supplied order and keep
those whose flags are one. Each retained position contributes its two
fixed terminal slots. Both slot names increase with the position, so the
resulting pair list has strictly increasing row-major rank.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Original supplied pattern positions whose active flags are one. -/
def gm02ActivePatternPositions (x : GM02TopologicalInput) (hflags : List ℕ) : List (Fin x.edges.length) :=
  (List.finRange x.edges.length).filter (fun f => decide (hflags[f.val]? = some 1))

/-- The increasing pair of terminal slots for one original pattern position. -/
def gm02PatternTerminalPair (x : GM02TopologicalInput) (K : ℕ) (hK : x.edges.length ≤ K)
    (f : Fin x.edges.length) : Fin (gm02FullPortSize x K) × Fin (gm02FullPortSize x K) :=
  (gm02FullPortPatternTerminal x K hK (f, false), gm02FullPortPatternTerminal x K hK (f, true))

/-- The terminal pairs in the original active pattern-position order. -/
def gm02ActiveTerminalList (x : GM02TopologicalInput) (hflags : List ℕ) (K : ℕ) (hK : x.edges.length ≤ K) :
    List (Fin (gm02FullPortSize x K) × Fin (gm02FullPortSize x K)) :=
  (gm02ActivePatternPositions x hflags).map (gm02PatternTerminalPair x K hK)

/-- An original position occurs in the active list exactly when its supplied flag is one. -/
theorem gm02ActivePatternPositions_mem (x : GM02TopologicalInput) (hflags : List ℕ)
    (f : Fin x.edges.length) : f ∈ gm02ActivePatternPositions x hflags ↔ hflags[f.val]? = some 1 := by
  simp only [gm02ActivePatternPositions, List.mem_filter, List.mem_finRange, decide_eq_true_eq, true_and]

/-- The first terminal of supplied edge `f` occupies its even slot. -/
theorem gm02PatternTerminalPair_fst_val (x : GM02TopologicalInput) (K : ℕ) (hK : x.edges.length ≤ K)
    (f : Fin x.edges.length) : (gm02PatternTerminalPair x K hK f).1.val =
      x.G.n + x.G.edges.length + 2 * f.val := by
  simp only [gm02PatternTerminalPair, gm02FullPortPatternTerminal, gm02FullPortTerminal,
    gm02PortSlotEquiv_val, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

/-- The second terminal of supplied edge `f` occupies the following odd slot. -/
theorem gm02PatternTerminalPair_snd_val (x : GM02TopologicalInput) (K : ℕ) (hK : x.edges.length ≤ K)
    (f : Fin x.edges.length) : (gm02PatternTerminalPair x K hK f).2.val =
      x.G.n + x.G.edges.length + 2 * f.val + 1 := by
  simp only [gm02PatternTerminalPair, gm02FullPortPatternTerminal, gm02FullPortTerminal,
    gm02PortSlotEquiv_val, ↓reduceIte, Nat.add_assoc]

/-- Every supplied terminal pair is increasing. -/
theorem gm02PatternTerminalPair_increasing (x : GM02TopologicalInput) (K : ℕ)
    (hK : x.edges.length ≤ K) (f : Fin x.edges.length) :
    (gm02PatternTerminalPair x K hK f).1.val < (gm02PatternTerminalPair x K hK f).2.val := by
  rw [gm02PatternTerminalPair_fst_val, gm02PatternTerminalPair_snd_val]
  omega

/-- The active terminal list has strictly increasing canonical pair ranks. -/
theorem gm02ActiveTerminalList_pairwise_rank (x : GM02TopologicalInput) (hflags : List ℕ)
    (K : ℕ) (hK : x.edges.length ≤ K) :
    (gm02ActiveTerminalList x hflags K hK).Pairwise
      (fun p q => (finProdFinEquiv p).val < (finProdFinEquiv q).val) := by
  have hpos : (gm02ActivePatternPositions x hflags).Pairwise (fun f g => f.val < g.val) := by
    apply List.Pairwise.filter
    change (List.ofFn (fun f : Fin x.edges.length => f)).Pairwise (fun f g => f.val < g.val)
    rw [List.pairwise_ofFn]
    exact fun _ _ h => h
  rw [gm02ActiveTerminalList, List.pairwise_map]
  apply hpos.imp
  intro f g hfg
  change (gm02PatternTerminalPair x K hK f).2.val + gm02FullPortSize x K * (gm02PatternTerminalPair x K hK f).1.val <
    (gm02PatternTerminalPair x K hK g).2.val + gm02FullPortSize x K * (gm02PatternTerminalPair x K hK g).1.val
  rw [gm02PatternTerminalPair_fst_val, gm02PatternTerminalPair_fst_val,
    gm02PatternTerminalPair_snd_val, gm02PatternTerminalPair_snd_val]
  apply Nat.add_lt_add_of_lt_of_le (by omega)
  exact Nat.mul_le_mul_left _ (by omega)

end GraphMinor.Compute
