module

public import GraphMinor.Compute.GM06Alg511TraceProg
public import GraphMinor.Compute.GM06Alg511Flow
public import GraphMinor.Compute.GM06Alg511FinishIndex
public import GraphMinor.Compute.GM06Alg511PathTurn
import Mathlib.Data.List.Chain
import Mathlib.Tactic

/-!
# Computing turns directly from the maximum-flow successor output

For VI (5.11), page 134, follow a prescribed source through the
successful flow output, save its final vertex, select its directed
edges and sum their signed turns. The path and dart buffers are
produced by the program. The execution theorem uses the valid path
system already proved by maximum flow, rather than supplied paths.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Surface

/-- Materialize a flow trace, save its endpoint and compute its signed
edge turn. Input registers 40/41 give the source and vertex count. -/
def gm06Alg511TraceTurnsProg : Cmd :=
  .seq gm06Alg511TraceProg (.seq gm06Alg511SaveFinishProg gm06Alg511PathTurnProg)

/-- Compute the initial path turn and then locate its saved endpoint
in the supplied ordered outer cuff row in array 1006. -/
def gm06Alg511WindingIndexProg : Cmd :=
  .seq gm06Alg511TraceTurnsProg gm06Alg511FinishIndexProg

/-- The trace-and-turn program starts from raw flow successor words
and returns an edge-labelled simple path turn with its saved endpoint.
All drawing and flow arrays are preserved. -/
theorem gm06Alg511TraceTurnsProg_exec {w : ℕ} (x : GM06Alg511Input)
    {α β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G)
    (turns : List ℤ) (hturnlen : turns.length = rep.pairs.length)
    (out : List ℕ)
    (hsys : IsValidPathSystem x.flowGraph x.flowInput.A x.flowInput.B
      (decUsed x.vertexCount out) (decPred x.vertexCount out) (decSucc x.vertexCount out))
    (u : Fin x.vertexCount)
    (hu : u ∈ pathStarts (decUsed x.vertexCount out) (decPred x.vertexCount out))
    (s : State) (hw : 2 < 2 ^ w) (hword : 1 + 3 * x.vertexCount < 2 ^ w)
    (hsquare : x.vertexCount * x.vertexCount < 2 ^ w)
    (hends : x.endpoints.length < 2 ^ w)
    (hproduct : x.vertexCount * (gm06Alg511TurnWords turns).sum < 2 ^ w)
    (hlen : out.length = 1 + 3 * x.vertexCount) (hout : s.arrs outArr = out)
    (hkeys : s.arrs 1100 = gm06Alg511DartKeys x)
    (hwords : s.arrs 11 = gm06Alg511TurnWords turns)
    (hcur : s.regs 40 = u.val) (hN : s.regs 41 = x.vertexCount) :
    ∃ s' t, Exec w gm06Alg511TraceTurnsProg s s' t ∧
      t ≤ 40 + x.vertexCount * (109 + 13 * x.endpoints.length) ∧
      (∀ arr, arr ≠ 12 → arr ≠ 13 → s'.arrs arr = s.arrs arr) ∧
      s'.regs 45 = (abWalkOfStart hsys u hu).finish.val ∧
      ∃ (b : Fin x.vertexCount) (W : GraphWalk (gm06Alg511LabelGraph rep.pairs) u b),
        W.support = (abWalkOfStart hsys u hu).walk.support ∧ W.IsSimple ∧
        (s'.regs 21 : ℤ) - (s'.regs 22 : ℤ) = gm06Alg511LabelWalkTurn rep.pairs turns W := by
  let p := abWalkOfStart hsys u hu
  have hp : p.walk.IsPath := abWalkOfStart_isPath hsys u hu
  have hcons : u :: p.walk.support.tail = p.walk.support := p.walk.cons_tail_support
  have hn : x.vertexCount < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hbuf₁, _, harr₁⟩ :=
    gm06Alg511TraceProg_exec out hsys u hu s (by omega) hword hlen hout hcur hN
  have htrace : gm06Alg511SuccVertices x.vertexCount out x.vertexCount u.val =
      p.walk.support.map Fin.val := gm06Alg511SuccVertices_eq_traceWalk out hsys _ u
  rw [htrace] at hbuf₁
  obtain ⟨s₂, he₂, hfinish₂, hk₂⟩ := gm06Alg511SaveFinishProg_exec p.walk.support s₁
    (by omega) hn p.walk.support_ne_nil hbuf₁
  have hlast : (p.walk.support.map Fin.val).getLast? = some p.finish.val := by
    rw [List.getLast?_map, List.getLast?_eq_some_getLast p.walk.support_ne_nil,
      p.walk.getLast_support]
    rfl
  have hlastval : (p.walk.support.map Fin.val).getD (p.walk.support.length - 1) 0 = p.finish.val := by
    have hh := congrArg (fun o : Option ℕ => o.getD 0) hlast
    rw [List.getLast?_eq_getElem?] at hh
    simpa only [List.getD_eq_getElem?_getD, List.length_map, Option.getD_some] using hh
  rw [hlastval] at hfinish₂
  have hbuf₂ : IsBufPrefix s₂ 12 42 x.vertexCount (p.walk.support.map Fin.val) :=
    hbuf₁.of_preserve (hk₂.2 12 (by decide)) (hk₂.1 42 (by decide))
  have hN₁ : s₁.regs 41 = x.vertexCount :=
    (he₁.regs_eq_of_not_mem_writtenRegs (by decide)).trans hN
  have hnd : (u :: p.walk.support.tail).Nodup := by
    change (p.start :: p.walk.support.tail).Nodup
    simpa only [p.walk.cons_tail_support] using hp.support_nodup
  have hadj : ∀ i (hi : i + 1 < (u :: p.walk.support.tail).length),
      x.flowGraph.Adj (u :: p.walk.support.tail)[i] (u :: p.walk.support.tail)[i + 1] := by
    change ∀ i (hi : i + 1 < (p.start :: p.walk.support.tail).length),
      x.flowGraph.Adj (p.start :: p.walk.support.tail)[i] (p.start :: p.walk.support.tail)[i + 1]
    simpa only [p.walk.cons_tail_support] using List.isChain_iff_getElem.mp p.walk.isChain_adj_support
  obtain ⟨s₃, t₃, he₃, ht₃, harr₃, b, W, hsupport, hs, hturn⟩ :=
    gm06Alg511PathTurnProg_exec x rep turns hturnlen u p.walk.support.tail hnd hadj s₂ hw hn
      hsquare hends hproduct
      ((hk₂.2 1100 (by decide)).trans ((harr₁ 1100 (by decide)).trans hkeys))
      ((hk₂.2 11 (by decide)).trans ((harr₁ 11 (by decide)).trans hwords))
      ((hk₂.1 41 (by decide)).trans hN₁)
      (by rw [hcons]; exact hbuf₂)
  refine ⟨s₃, t₁ + (5 + t₃), .seq he₁ (.seq he₂ he₃), ?_, ?_, ?_,
    b, W, ?_, hs, hturn⟩
  · nlinarith [ht₁, ht₃]
  · intro arr ha₁ ha₂
    rw [harr₃ arr ha₁ ha₂, hk₂.2 arr (by simp), harr₁ arr ha₁]
  · exact (he₃.regs_eq_of_not_mem_writtenRegs (by decide)).trans hfinish₂
  · rw [hcons] at hsupport
    exact hsupport

end GraphMinor.Compute
