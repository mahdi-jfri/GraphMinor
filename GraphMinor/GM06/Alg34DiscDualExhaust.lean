module

public import GraphMinor.GM06.Alg34DiscDualInvariant
public import GraphMinor.GM06.Alg34DiscDualBounds
public import GraphMinor.GM06.Alg34SingletonInvariant
public import GraphMinor.GM06.Alg34SingletonSectionBounds
public import GraphMinor.Compute.GM06Alg34ReductionWork

/-!
# The complete dual branch followed by singleton exhaustion

The dual update preserves feasibility and all geometric conditions.
At a stuck non-null state its singleton search succeeds by VI (2.3).
The first deletion loses an edge and strictly lowers the queue charge.
Further singleton deletions cannot increase that charge. Counts and
separate section bounds survive the whole branch.
-/

public section
namespace GraphMinor.Compute.GM06GapInputRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {X : GM06GapInput} {G : Drawing S} {Δ : Set (Set S)}

/-- The complete dual/singleton branch strictly lowers its queue charge. -/
theorem discDualExhaust_workWeight_lt (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hp : G.IsProper) (hc : IsGraphConnected G.toGraph)
    (hD : IsDivision Δ) (hbd : divisionUnion Δ = G.V ∩ bd S) (hn : 0 < X.drawing.n)
    (hI : X.drawing.findInteriorComponent = none)
    (hSing : gm06FindSingleton X.drawing.division = none)
    (M : ℕ) (hM : X.drawing.n + X.drawing.regions.length ≤ M) :
    (gm06GapReduceSingletons X.discDualData).drawing.workWeight (M + 1) < X.drawing.workWeight (M + 1) := by
  obtain ⟨v, hf⟩ := h.discDualData_findSingleton_exists hS hp hc hD hbd hn hI hSing
  rw [gm06GapReduceSingletons, hf]
  exact (gm06GapReduceSingletons_workWeight_le (M + 1) _).trans_lt
    (h.discDualData_singleton_workWeight_lt hS hp hc hbd hn hI hSing M hM v)

/-- The full dual branch returns a proper represented disc input with a
valid cross-free division covering the boundary. It preserves the finite
answer, retains fixed count and section bounds, and strictly lowers work. -/
theorem discDualExhaust_correct (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hp : G.IsProper) (hc : IsGraphConnected G.toGraph)
    (hD : IsDivision Δ) (hbd : divisionUnion Δ = G.V ∩ bd S) (hCF : IsCrossFree (bd S) Δ)
    (hn : 0 < X.drawing.n) (hI : X.drawing.findInteriorComponent = none)
    (hSing : gm06FindSingleton X.drawing.division = none)
    (M Q : ℕ) (hM : X.drawing.n + X.drawing.regions.length ≤ M) (hQ : X.drawing.cellCount ≤ Q) :
    let Y := gm06GapReduceSingletons X.discDualData
    ∃ (G' : Drawing S) (Δ' : Set (Set S)), Nonempty (GM06GapInputRep Y G' Δ') ∧
      G'.IsProper ∧ IsDivision Δ' ∧ divisionUnion Δ' = G'.V ∩ bd S ∧ IsCrossFree (bd S) Δ' ∧
      (IsFeasible X.drawing.graph X.drawing.divisionSet ↔ IsFeasible Y.drawing.graph Y.drawing.divisionSet) ∧
      Y.drawing.n + Y.drawing.regions.length ≤ M ∧ Y.drawing.ends.length ≤ X.drawing.ends.length ∧
      Y.drawing.cellCount ≤ Q ∧ Y.drawing.regionWords.length ≤ gm06SectionCap Q ∧
      Y.drawing.cuffWords.length ≤ gm06SectionCap Q ∧ Y.drawing.divisionWords.length ≤ gm06SectionCap Q ∧
      Y.drawing.workWeight (M + 1) < X.drawing.workWeight (M + 1) := by
  have hR := h.drawing.regions_pos_of_vertices hS hp hn
  obtain ⟨D, Λ, ⟨hy⟩, hpY, hDY, hbY, hcfY, hfY⟩ :=
    h.discDualData_crossFree_correct hS hp hc hR hD hbd hCF
  obtain ⟨hYN, hYR, hYE⟩ := h.discDualData_counts hS hR
  have hYQ : X.discDualData.drawing.cellCount ≤ Q := by
    unfold GM06DrawingData.cellCount at hQ ⊢
    omega
  obtain ⟨hrY, hcY, hdY⟩ := h.discDualData_sections_le hS Q hQ hR
  obtain ⟨hnZ, heZ, hrZ⟩ := hy.reduceSingletons_counts_le hS hpY hDY
  obtain ⟨hrS, hcS, hdS⟩ := hy.reduceSingletons_sections_le hS hpY hDY Q hYQ hrY hcY hdY
  obtain ⟨G', Δ', hr, hp', hD', hb', hcf', hf⟩ :=
    hy.reduceSingletons_crossFree_correct hS hpY hDY hbY hcfY
  refine ⟨G', Δ', hr, hp', hD', hb', hcf', hfY.trans hf, ?_, ?_, ?_, hrS, hcS, hdS,
    h.discDualExhaust_workWeight_lt hS hp hc hD hbd hn hI hSing M hM⟩
  · omega
  · omega
  · unfold GM06DrawingData.cellCount at hYQ ⊢
    omega

end GraphMinor.Compute.GM06GapInputRep
