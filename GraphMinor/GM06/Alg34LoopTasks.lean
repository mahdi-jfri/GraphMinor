module

public import GraphMinor.GM06.Alg34LoopRestrictions
public import GraphMinor.GM06.Alg34LoopFacts
public import GraphMinor.Compute.GM06Alg34TaskLayout
import GraphMinor.GM06.Alg34GapTasksCorrect

/-!
# Every appended component task satisfies the loop conditions

Each saved record names the same finite parent input and one of its
canonical roots. Component restriction supplies an intended child with
the fixed bounds. The original parent layout and the uniform record
bound supply the decoder conditions. VI (3.3)(iv) identifies the parent
answer with the conjunction of all saved task answers.
-/

public section
namespace GraphMinor.Compute

open Set Surface GM06
universe u

/-- Every appended component record has the required finite layout and
an intended bounded target, derived from its current parent. -/
theorem gm06LoopInstance_tasks {X : GM06GapInput} (hX : gm06LoopInstance.{u} X)
    {M E Q : ℕ} (hB : gm06LoopBounds M E Q X)
    (R : List (Fin X.drawing.regions.length)) (hgroups : X.gapRegions = [R]) :
    ∀ T ∈ gm06GapComponentTasks X.drawing R,
      gm06TaskLayout Q T ∧ gm06LoopInstance.{u} T.target ∧ gm06LoopBounds M E Q T.target := by
  obtain ⟨L, R', hL, hR', hlen, _⟩ := gm06LoopInstance_layout hX
  have hRR : R' = R := (List.cons.inj (hR'.symm.trans hgroups)).1
  have hlenR : R.length = L.length := hRR ▸ hlen
  have hs := gm06LoopBounds_size hB
  have hgap := gm06LoopInstance_gap_length hX
  rw [X.discGapWords_singleton R hgroups, List.length_map] at hgap
  have hn : X.drawing.n ≤ Q := by
    have hh := hB.2.2.1
    unfold GM06DrawingData.cellCount at hh
    omega
  intro T hT
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hT
  have htarget : (⟨X.drawing, [R]⟩ : GM06GapInput).componentGapData a = X.componentGapData a :=
    congrArg (fun gs => (⟨X.drawing, gs⟩ : GM06GapInput).componentGapData a) hgroups.symm
  have hc := gm06LoopInstance_component hX hB a
  refine ⟨gm06TaskLayout_mk Q X.drawing L R a hL hlenR hs (hgap.trans hn), ?_, ?_⟩
  · change gm06LoopInstance.{u} ((⟨X.drawing, [R]⟩ : GM06GapInput).componentGapData a)
    rw [htarget]
    exact hc.1
  · change gm06LoopBounds M E Q ((⟨X.drawing, [R]⟩ : GM06GapInput).componentGapData a)
    rw [htarget]
    exact hc.2

/-- The task answers form exactly the parent answer when the split test passes. -/
theorem gm06LoopInstance_tasks_feasible_iff {X : GM06GapInput} (hX : gm06LoopInstance.{u} X)
    (R : List (Fin X.drawing.regions.length)) (hgroups : X.gapRegions = [R])
    (hs : X.drawing.hasSplitBlock = false) (hk : 2 ≤ X.drawing.componentRoots.length) :
    IsFeasible X.drawing.graph X.drawing.divisionSet ↔
      ∀ T ∈ gm06GapComponentTasks X.drawing R,
        IsFeasible T.target.drawing.graph T.target.drawing.divisionSet := by
  obtain ⟨I, ⟨h⟩, _⟩ := hX
  haveI : T2Space I.S := t2Space_of_isClosedDiscSpace I.hDisc
  have hparent : X = (⟨X.drawing, [R]⟩ : GM06GapInput) :=
    congrArg (GM06GapInput.mk X.drawing) hgroups
  have hrep : GM06GapInputRep ⟨X.drawing, [R]⟩ I.G I.Δ := hparent ▸ h
  exact hrep.componentTasks_feasible_iff hs I.hΔ I.hΔ_eq hk

end GraphMinor.Compute
