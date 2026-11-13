module

public import GraphMinor.Compute.GM02InjectedPattern

/-!
# The fixed endpoint-register list of an injected pattern

Every edge of the fixed pattern names two fixed pattern vertices.
Their decoded registers contain the injected endpoints. List both
registers for every edge in the original order, retaining repeated
pairs and loops exactly.
-/

public section
namespace GraphMinor.Compute

/-- The decoded registers for the fixed pattern's successive edge ends. -/
@[expose] def gm02InjectedEdgeRegisters (H : GM02EdgeListInput) : List Reg :=
  H.edges.flatMap (fun e => [200 + e.1.val, 200 + e.2.val])

/-- There are two endpoint registers per actual pattern edge. -/
theorem gm02InjectedEdgeRegisters_length (H : GM02EdgeListInput) :
    (gm02InjectedEdgeRegisters H).length = 2 * H.edges.length := by
  unfold gm02InjectedEdgeRegisters
  induction H.edges with
  | nil => rfl
  | cons e es ih => simp only [List.flatMap_cons, List.length_append,
      List.length_cons, List.length_nil] at *; omega

/-- Reading the listed registers yields exactly the flat edge words of the injected pattern. -/
theorem gm02InjectedEdgeRegisters_words (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) (s : State)
    (hslots : ∀ i : Fin H.n, s.regs (200 + i.val) = (f i).val) :
    (gm02InjectedEdgeRegisters H).map s.regs = flatEdges (gm02InjectedPattern G H f).edges := by
  simp only [gm02InjectedEdgeRegisters, gm02InjectedPattern, flatEdges,
    List.map_flatMap, List.flatMap_map, List.map_cons, List.map_nil, hslots]

/-- Every selected endpoint word is a host vertex number. -/
theorem gm02InjectedEdgeRegisters_word_lt (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) (s : State)
    (hslots : ∀ i : Fin H.n, s.regs (200 + i.val) = (f i).val) :
    ∀ r ∈ gm02InjectedEdgeRegisters H, s.regs r < G.n := by
  intro r hr
  obtain ⟨e, _, hr⟩ := List.mem_flatMap.1 hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hslots]; exact (f e.1).isLt
  · rw [hslots]; exact (f e.2).isLt

end GraphMinor.Compute
