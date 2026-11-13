module

public import GraphMinor.Compute.GM06Alg511FindDart
public import GraphMinor.Compute.Algorithm77Prog
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# One edge-selection step along a returned path

The winding phase of VI (5.11), page 134, reads two consecutive
vertices, scans the supplied edge keys and appends the selected dart
to a buffer. The output dart has exactly those directed endpoints.
This step preserves the vertex trace, edge table and signed turns.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Select an edge for the pair at positions 51 and 51+1 of vertex
buffer 12. Append its dart to buffer 13 with length register 49. -/
def gm06Alg511DartBody : Cmd :=
  .seq (.assign 43 (.read 12 (.reg 51)))
    (.seq (.assign 44 (.read 12 (.op .add (.reg 51) (.const 1))))
      (.seq gm06Alg511FindDartProg (pushBufCmd 13 49 (.reg 47))))

/-- A pair of adjacent vertices yields a genuine directed edge and
one additional buffer entry, with a linear edge-scan bound. -/
theorem gm06Alg511DartBody_exec {w : ℕ} (x : GM06Alg511Input)
    {α β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G)
    (a b : Fin x.vertexCount) (hadj : x.flowGraph.Adj a b)
    (i : ℕ) (darts : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : x.vertexCount < 2 ^ w)
    (hsquare : x.vertexCount * x.vertexCount < 2 ^ w)
    (hends : x.endpoints.length < 2 ^ w)
    (hkeys : s.arrs 1100 = gm06Alg511DartKeys x)
    (hN : s.regs 41 = x.vertexCount) (hI : s.regs 51 = i)
    (hcap : (s.arrs 12).length = x.vertexCount) (hi : i + 1 < x.vertexCount)
    (hleft : (s.arrs 12)[i]'(by omega) = a.val)
    (hright : (s.arrs 12)[i + 1]'(by omega) = b.val)
    (hbuf : IsBufPrefix s 13 49 x.vertexCount darts)
    (hspace : darts.length + 1 ≤ x.vertexCount) :
    ∃ s' t, Exec w gm06Alg511DartBody s s' t ∧
      t ≤ 28 + 13 * x.endpoints.length ∧
      Keeps [43, 44, 48, 20, 47, 49] [13] s s' ∧
      ∃ d, d < x.endpoints.length ∧
        IsBufPrefix s' 13 49 x.vertexCount (darts ++ [d]) ∧
        s'.regs 47 = d ∧ x.endpoints.getD d 0 = a.val ∧
        x.endpoints.getD (gm06DartMate d) 0 = b.val := by
  let s₁ := s.setReg 43 a.val
  let s₂ := s₁.setReg 44 b.val
  have he₁ : Exec w (.assign 43 (.read 12 (.reg 51))) s s₁ 3 := by
    apply Exec.assign
    simpa only [hleft] using Crossing.eval_read
      (a := 12) (Crossing.eval_reg hI (by omega)) (by omega)
      (by rw [hleft]; exact a.isLt.trans hn)
  have he₂ : Exec w (.assign 44 (.read 12 (.op .add (.reg 51) (.const 1)))) s₁ s₂ 5 := by
    apply Exec.assign
    have hidx := Crossing.eval_add
      (Crossing.eval_reg (show s₁.regs 51 = i by simpa [s₁] using hI) (by omega))
      (Crossing.eval_const hw) (show i + 1 < 2 ^ w by omega)
    have hi₁ : i + 1 < (s₁.arrs 12).length := by
      simpa [s₁] using (show i + 1 < (s.arrs 12).length by omega)
    have hread := Crossing.eval_read (a := 12) hidx hi₁
      (show (s₁.arrs 12)[i + 1] < 2 ^ w by simpa only [s₁, State.setReg_arrs, hright] using b.isLt.trans hn)
    simpa only [s₁, State.setReg_arrs, hright] using hread
  have hk₂ : Keeps [43, 44, 48, 20, 47, 49] [13] s s₂ :=
    ((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, d, hd, hreg, hkey⟩ :=
    gm06Alg511FindDartProg_exec (gm06Alg511DartKeys x) x.vertexCount a.val b.val s₂
      hw hn a.isLt b.isLt hsquare (by simpa only [gm06Alg511DartKeys_length] using hends)
      (fun v hv => (gm06Alg511DartKeys_lt x rep v hv).trans hsquare)
      (gm06Alg511DartKeys_mem_of_adj x rep a b hadj)
      (by simpa [s₂, s₁] using hkeys)
      (by simpa [s₂, s₁] using hN) (by simp [s₂, s₁]) (by simp [s₂])
  have hk₃' : Keeps [43, 44, 48, 20, 47, 49] [13] s s₃ :=
    hk₂.trans hk₃ (by simp) (by simp)
  have hbuf₃ : IsBufPrefix s₃ 13 49 x.vertexCount darts :=
    hbuf.of_preserve
      (by simpa only [s₂, s₁, State.setReg_arrs] using hk₃.2 13 (by simp))
      (by simpa [s₂, s₁] using hk₃.1 49 (by decide))
  obtain ⟨s₄, t₄, he₄, ht₄, hbuf₄, hregs₄, harr₄⟩ := pushBufCmd_exec
    13 49 (.reg 47) x.vertexCount darts d hw hn hbuf₃ hspace
    (Crossing.eval_reg hreg (hd.trans (by simpa only [gm06Alg511DartKeys_length] using hends)))
  have hk₄ : Keeps [49] [13] s₃ s₄ :=
    ⟨fun r hr => hregs₄ r (by simpa using hr), fun a ha => harr₄ a (by simpa using ha)⟩
  have hd' : d < x.endpoints.length := by simpa only [gm06Alg511DartKeys_length] using hd
  have hlen : x.endpoints.length = 2 * G.edgeSet.ncard := rep.endpoints_length
  have hm : gm06DartMate d < x.endpoints.length := by
    rw [hlen] at hd' ⊢
    exact gm06DartMate_lt hd'
  have hmatch := gm06Alg511DartKeys_match x a.val b.val d b.isLt hd
    (gm06Alg511Endpoint_getD_lt x rep _ hm) hkey
  refine ⟨s₄, 3 + (5 + (t₃ + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)), ?_,
    hk₃'.trans hk₄ (by simp) (by simp), d, hd', hbuf₄,
    (hregs₄ 47 (by decide)).trans hreg, hmatch⟩
  simp only [gm06Alg511DartKeys_length] at ht₃
  simp only [Expr.cost] at ht₄
  omega

end GraphMinor.Compute
