module

public import GraphMinor.Compute.GM06Alg511TraceProg
public import GraphMinor.Compute.GM06Alg511FinishIndex
public import GraphMinor.Compute.GM06Alg511ChosenTurn
import GraphMinor.Compute.GM06Alg511TurnBounds
import Mathlib.Tactic

/-!
# Computing a stored linkage path's turn from raw flow

For VI (5.11), page 134, traverse one source in the raw maximum-flow
output and save its endpoint. Read the directed edge choices already
made for the full linkage and sum their signed turns. The computed
integer is the turn of that same finite labelled path.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Surface

/-- Traverse a source path, save its endpoint, and sum its stored
linkage edge turns. -/
def gm06Alg511TraceChosenTurnProg : Cmd :=
  .seq gm06Alg511TraceProg (.seq gm06Alg511SaveFinishProg gm06Alg511ChosenTurnProg)

/-- The stored linkage path's winding numerator is computed from raw
flow and choice words, preserving every input and linkage array. -/
theorem gm06Alg511TraceChosenTurnProg_exec {w : ℕ} (x : GM06Alg511Input)
    {α β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G)
    (turns : List ℤ) (hturnlen : turns.length = rep.pairs.length)
    (out choices : List ℕ)
    (hsys : IsValidPathSystem x.flowGraph x.flowInput.A x.flowInput.B
      (decUsed x.vertexCount out) (decPred x.vertexCount out) (decSucc x.vertexCount out))
    (u : Fin x.vertexCount)
    (hu : u ∈ pathStarts (decUsed x.vertexCount out) (decPred x.vertexCount out))
    (W : GraphWalk (gm06Alg511LabelGraph rep.pairs) u (abWalkOfStart hsys u hu).finish)
    (hsupport : W.support = (abWalkOfStart hsys u hu).walk.support)
    (hdarts : gm06Alg511LabelWalkDarts rep.pairs W = gm06Alg511ChosenDarts x choices W.support)
    (s : State) (hw : 2 < 2 ^ w) (hword : 1 + 3 * x.vertexCount < 2 ^ w)
    (hends : 2 * turns.length < 2 ^ w)
    (hproduct : x.vertexCount * (gm06Alg511TurnWords turns).sum < 2 ^ w)
    (hchoiceLen : choices.length = x.vertexCount) (hchoiceWords : ∀ d ∈ choices, d < 2 ^ w)
    (hlen : out.length = 1 + 3 * x.vertexCount)
    (hout : s.arrs outArr = out) (hchoices : s.arrs 1300 = choices)
    (hwords : s.arrs 11 = gm06Alg511TurnWords turns)
    (hcur : s.regs 40 = u.val) (hN : s.regs 41 = x.vertexCount) :
    ∃ s' t, Exec w gm06Alg511TraceChosenTurnProg s s' t ∧
      t ≤ 36 + 76 * x.vertexCount ∧
      (∀ arr, arr ≠ 12 → arr ≠ 13 → s'.arrs arr = s.arrs arr) ∧
      s'.regs 45 = (abWalkOfStart hsys u hu).finish.val ∧
      s'.arrs 12 = gm06Alg511LabelWalkDarts rep.pairs W ∧
      (s'.regs 21 : ℤ) - (s'.regs 22 : ℤ) = gm06Alg511LabelWalkTurn rep.pairs turns W := by
  let p := abWalkOfStart hsys u hu
  have hn : x.vertexCount < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hbuf₁, _, harr₁⟩ :=
    gm06Alg511TraceProg_exec out hsys u hu s (by omega) hword hlen hout hcur hN
  have htrace : gm06Alg511SuccVertices x.vertexCount out x.vertexCount u.val =
      p.walk.support.map Fin.val := gm06Alg511SuccVertices_eq_traceWalk out hsys _ u
  rw [htrace] at hbuf₁
  obtain ⟨s₂, he₂, hfinish₂, hk₂⟩ := gm06Alg511SaveFinishProg_exec p.walk.support s₁
    (by omega) hn p.walk.support_ne_nil hbuf₁
  have hlastOpt : (p.walk.support.map Fin.val).getLast? = some p.finish.val := by
    rw [List.getLast?_map, List.getLast?_eq_some_getLast p.walk.support_ne_nil,
      p.walk.getLast_support]
    rfl
  have hlast : (p.walk.support.map Fin.val).getD (p.walk.support.length - 1) 0 = p.finish.val := by
    have hh := congrArg (fun o : Option ℕ => o.getD 0) hlastOpt
    rw [List.getLast?_eq_getElem?] at hh
    simpa only [List.getD_eq_getElem?_getD, List.length_map, Option.getD_some] using hh
  rw [hlast] at hfinish₂
  have hbuf₂ : IsBufPrefix s₂ 12 42 x.vertexCount (p.walk.support.map Fin.val) :=
    hbuf₁.of_preserve (hk₂.2 12 (by decide)) (hk₂.1 42 (by decide))
  have hdarts' : gm06Alg511LabelWalkDarts rep.pairs W =
      gm06Alg511ChosenDarts x choices p.walk.support :=
    hdarts.trans (congrArg (gm06Alg511ChosenDarts x choices) hsupport)
  have hvalid : ∀ d ∈ gm06Alg511ChosenDarts x choices p.walk.support, d < 2 * turns.length := by
    rw [← hdarts', hturnlen]
    exact gm06Alg511LabelWalkDarts_lt rep.pairs W
  obtain ⟨s₃, t₃, he₃, ht₃, harr₃, hpath, hsum⟩ := gm06Alg511ChosenTurnProg_exec
    x turns choices p.walk.support s₂ hw hn hends hchoiceLen hchoiceWords hvalid hproduct
    ((hk₂.2 1300 (by decide)).trans ((harr₁ 1300 (by decide)).trans hchoices))
    ((hk₂.2 11 (by decide)).trans ((harr₁ 11 (by decide)).trans hwords)) hbuf₂
  have hdlen : p.walk.support.length - 1 ≤ x.vertexCount :=
    (Nat.sub_le _ _).trans (by simpa only [List.length_map] using hbuf₁.2.2.1)
  refine ⟨s₃, t₁ + (5 + t₃), .seq he₁ (.seq he₂ he₃), ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · intro arr ha₁ ha₂
    rw [harr₃ arr ha₁ ha₂, hk₂.2 arr (by simp), harr₁ arr ha₁]
  · exact (he₃.regs_eq_of_not_mem_writtenRegs (by decide)).trans hfinish₂
  · rw [hdarts']
    exact hpath
  · rw [gm06Alg511LabelWalkTurn_eq_dartSum rep.pairs turns hturnlen W, hdarts']
    exact hsum

end GraphMinor.Compute
