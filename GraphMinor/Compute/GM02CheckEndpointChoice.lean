module

public import GraphMinor.Compute.GM02CheckChoice
public import GraphMinor.Compute.GM02ChoiceSlotExpr
public import GraphMinor.Compute.GM02PatternEndpointExpr
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Checking one pattern endpoint's decoded choice

Read the candidate digit and the supplied pattern endpoint, then run the
bounds-checked active incidence command. The resulting bit is exactly
the incidence condition in the split choice. Every array and the pattern
position register survive the command.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Check one end of pattern position 43 using its decoded candidate slot. -/
@[expose] def gm02CheckEndpointChoiceProg (src : Arr) (side : Bool) : Cmd :=
  .seq (.assign 32 (gm02ChoiceSlotExpr side))
    (.seq (.assign 45 (gm02PatternEndpointExpr src side)) (gm02CheckChoiceProg src))

/-- The endpoint command tests exactly the chosen active incidence in at most 52 steps. -/
theorem gm02CheckEndpointChoiceProg_exec {w K code : ℕ} (x : GM02TopologicalInput)
    (s : State) (src : Arr) (flags : List ℕ) (f : Fin x.edges.length) (side : Bool)
    (hK : x.edges.length ≤ K) (hsrc : s.arrs src = x.enc)
    (harr : s.arrs 23 = List.ofFn (fun i : Fin (2 * K) => gm02SeparatorDigit x.G.edges.length code i.val))
    (hflags : s.arrs 20 = flags) (hlen : flags.length = x.G.edges.length)
    (hbits : ∀ b ∈ flags, b ≤ 1) (hf : s.regs 43 = f.val)
    (hoff : s.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card)
    (hm : s.regs 11 = x.G.edges.length)
    (hw : 2 < 2 ^ w) (hn : x.G.n < 2 ^ w) (hKw : 2 * K < 2 ^ w)
    (hmw : x.G.edges.length + 1 < 2 ^ w) (henc : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w (gm02CheckEndpointChoiceProg src side) s s' t ∧ t ≤ 52 ∧
      s'.regs 46 = (if (gm02ActiveGraph x.G.graph flags).Inc
        (gm02PortAssignmentOfCode x code (f, side)).val
        (if side then (x.ends f).2 else (x.ends f).1) then 1 else 0) ∧
      s'.regs 32 = (gm02PortAssignmentOfCode x code (f, side)).val ∧
      s'.regs 45 = (if side then (x.ends f).2 else (x.ends f).1) ∧
      s'.arrs = s.arrs ∧
      (∀ r, r ≠ 32 → r ≠ 42 → r ≠ 44 → r ≠ 45 → r ≠ 46 → s'.regs r = s.regs r) := by
  let e := (gm02PortAssignmentOfCode x code (f, side)).val
  let v := if side then (x.ends f).2 else (x.ends f).1
  let s₁ := s.setReg 32 e
  have he₁ : Exec w (.assign 32 (gm02ChoiceSlotExpr side)) s s₁ 7 :=
    .assign (gm02ChoiceSlotExpr_eval x s f side hK harr hf hw hKw hmw)
  have heval := gm02PatternEndpointExpr_eval x s₁ src f side hsrc
    ((State.setReg_regs_ne s e (by decide : (16 : Reg) ≠ 32)).trans hoff)
    ((State.setReg_regs_ne s e (by decide : (43 : Reg) ≠ 32)).trans hf) hw hn henc
  let s₂ := s₁.setReg 45 v
  have he₂ : Exec w (.assign 45 (gm02PatternEndpointExpr src side)) s₁ s₂ 9 := .assign heval
  have hew : e < 2 ^ w :=
    (gm02PortAssignmentOfCode x code (f, side)).isLt.trans hmw
  have hvw : v < 2 ^ w := by
    have hl : (x.ends f).1 < x.G.n := (x.edges[f.val]'f.isLt).1.isLt
    have hr : (x.ends f).2 < x.G.n := (x.edges[f.val]'f.isLt).2.isLt
    cases side
    · exact hl.trans hn
    · exact hr.trans hn
  obtain ⟨s₃, t₃, he₃, ht₃, hout, ha₃, hr₃⟩ :=
    gm02CheckChoiceProg_exec x s₂ src flags e v hsrc hflags hlen hbits
      (by simp [s₂, s₁]) (by simpa [s₂, s₁] using hm)
      (State.setReg_regs_self ..) hw hn (by omega) hew hvw henc
  refine ⟨s₃, 7 + (9 + t₃), .seq he₁ (.seq he₂ he₃), by omega, hout, ?_, ?_, ha₃, ?_⟩
  · exact (hr₃ 32 (by decide) (by decide) (by decide)).trans (by simp [s₂, s₁, e])
  · exact (hr₃ 45 (by decide) (by decide) (by decide)).trans (State.setReg_regs_self ..)
  · intro r hr32 hr42 hr44 hr45 hr46
    exact (hr₃ r hr42 hr44 hr46).trans
      ((State.setReg_regs_ne s₁ v hr45).trans (State.setReg_regs_ne s e hr32))

end GraphMinor.Compute
