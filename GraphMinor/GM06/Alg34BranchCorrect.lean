module

public import GraphMinor.GM06.Alg34ComponentsCorrect
public import GraphMinor.Compute.GM06Alg34BranchProg

/-!
# Correctness of the computed component branch queue

The emitted records are exactly the finite component input list. The
proved component partition equivalence says that the original division
is feasible exactly when every input in that list is feasible. Together
with the concrete RAM execution, this verifies the branching phase of
VI (3.4) using (3.3)(iv).
-/

public section
namespace GraphMinor.Compute

open Set Surface GM06

/-- The canonical queue consists exactly of length-prefixed component input words. -/
theorem gm06ComponentQueueWords_eq_inputs (x : GM06DrawingData) :
    gm06ComponentQueueWords x (List.finRange x.n) =
      x.componentInputs.flatMap (fun y => GM06DrawingData.listWords y.words) := by
  simp only [gm06ComponentQueueWords, GM06DrawingData.componentInputs,
    GM06DrawingData.componentRoots, List.flatMap_map, gm06ComponentRecordWords]
  rfl

namespace GM06DrawingRep

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- The computed component input list has exactly the conjunction of
feasibility answers prescribed by VI (3.3)(iv). -/
theorem componentInputs_list_feasible_iff (h : GM06DrawingRep x G Δ)
    (hs : x.hasSplitBlock = false) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ = G.V ∩ bd S) (hk : 2 ≤ x.componentRoots.length) :
    IsFeasible x.graph x.divisionSet ↔
      ∀ y ∈ x.componentInputs, IsFeasible y.graph y.divisionSet := by
  rw [h.componentInputs_feasible_iff hs hD hbd hk]
  constructor
  · intro hf y hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
    exact hi ▸ hf i
  · intro hf i
    exact hf _ (List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩)

/-- The concrete branching phase of (3.4) emits exactly the component
input list in polynomial time, and its branch answers determine the
feasibility of the represented parent by (3.3)(iv). -/
theorem branchProg_correct (h : GM06DrawingRep x G Δ)
    (hs : x.hasSplitBlock = false) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ = G.V ∩ bd S) (hk : 2 ≤ x.componentRoots.length)
    {c : ℕ} (hc : 5 ≤ c) {s : State} (hinput : s.arrs 0 = x.words) :
    ∃ s' t cap, Exec (wordSize c x.size) gm06BranchProg s s' t ∧
      t ≤ 2000 * (x.size + 2) ^ 5 ∧
      IsPrefixBuffer 42 (x.componentInputs.flatMap (fun y => GM06DrawingData.listWords y.words)) cap s' ∧
      s'.regs 5002 = (x.componentInputs.flatMap (fun y => GM06DrawingData.listWords y.words)).length ∧
      (IsFeasible G.toGraph Δ ↔ ∀ y ∈ x.componentInputs, IsFeasible y.graph y.divisionSet) := by
  obtain ⟨s', t, hex, ht, hb, hp, _, _⟩ := gm06BranchProg_exec x hc hinput
  exact ⟨s', t, _, hex, ht, gm06ComponentQueueWords_eq_inputs x ▸ hb,
    gm06ComponentQueueWords_eq_inputs x ▸ hp,
    (h.feasible_iff hD).trans (h.componentInputs_list_feasible_iff hs hD hbd hk)⟩

end GM06DrawingRep
end GraphMinor.Compute
