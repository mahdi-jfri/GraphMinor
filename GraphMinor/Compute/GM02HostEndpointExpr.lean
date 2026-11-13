module

public import GraphMinor.Compute.GM02HostEndpointWords
import GraphMinor.Compute.CrossingOpsBasic

/-!
# The host endpoint reads in the outer loop

Read the two supplied words for host edge position 32. Each read has
constant cost, uses the original input array, and returns a vertex below
the supplied host count. The two assignments save the endpoints in
registers 42 and 44 without changing any array or other register.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Read one original endpoint of the host edge at position 32. -/
def gm02HostEndpointExpr (src : Arr) (side : Bool) : Expr :=
  .read src (.op .add (.const (if side then 3 else 2)) (.op .mul (.const 2) (.reg 32)))

/-- The host endpoint expression has constant cost. -/
theorem gm02HostEndpointExpr_cost (src : Arr) (side : Bool) : (gm02HostEndpointExpr src side).cost = 6 := rfl

/-- The actual host endpoint read is justified by the supplied edge list. -/
theorem gm02HostEndpointExpr_eval {w : ℕ} (x : GM02TopologicalInput) (s : State)
    (src : Arr) (e : Fin x.G.edges.length) (side : Bool)
    (hsrc : s.arrs src = x.enc) (he : s.regs 32 = e.val)
    (hw : 2 < 2 ^ w) (hn : x.G.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    (gm02HostEndpointExpr src side).eval w s =
      some (if side then (x.G.edges[e.val]'e.isLt).2.val else (x.G.edges[e.val]'e.isLt).1.val) := by
  let d : ℕ := if side then 3 else 2
  have hd : d ≤ 3 := by cases side <;> decide
  have hLen := x.enc_length
  have heLen := e.isLt
  have hdw : d < 2 ^ w := by omega
  have hew : e.val < 2 ^ w := by omega
  have h2ew : 2 * e.val < 2 ^ w := by omega
  have haddr : d + 2 * e.val < 2 ^ w := by omega
  have hidx : (Expr.op .add (.const d) (.op .mul (.const 2) (.reg 32))).eval w s = some (d + 2 * e.val) :=
    eval_add (eval_const hdw) (eval_mul (eval_const hw) (eval_reg he hew) h2ew) haddr
  have hget : (s.arrs src)[d + 2 * e.val]? =
      some (if side then (x.G.edges[e.val]'e.isLt).2.val else (x.G.edges[e.val]'e.isLt).1.val) := by
    cases side
    · simpa only [hsrc, d, Bool.false_eq_true, ↓reduceIte] using x.enc_host_fst e
    · simpa only [hsrc, d, ↓reduceIte] using x.enc_host_snd e
  have hval : (if side then (x.G.edges[e.val]'e.isLt).2.val else (x.G.edges[e.val]'e.isLt).1.val) < 2 ^ w := by
    cases side
    · exact (x.G.edges[e.val]'e.isLt).1.isLt.trans hn
    · exact (x.G.edges[e.val]'e.isLt).2.isLt.trans hn
  obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.1 hget
  simpa only [gm02HostEndpointExpr, d, heq] using eval_read hidx hi (heq ▸ hval)

/-- Save the two original host endpoints without changing the input. -/
def gm02ReadHostEndsProg (src : Arr) : Cmd :=
  .seq (.assign 42 (gm02HostEndpointExpr src false)) (.assign 44 (gm02HostEndpointExpr src true))

/-- Both host endpoints are saved in exactly fourteen actual RAM steps. -/
theorem gm02ReadHostEndsProg_exec {w : ℕ} (x : GM02TopologicalInput) (s : State)
    (src : Arr) (e : Fin x.G.edges.length) (hsrc : s.arrs src = x.enc) (he : s.regs 32 = e.val)
    (hw : 2 < 2 ^ w) (hn : x.G.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    ∃ s', Exec w (gm02ReadHostEndsProg src) s s' 14 ∧
      s'.regs 42 = (x.G.edges[e.val]'e.isLt).1.val ∧ s'.regs 44 = (x.G.edges[e.val]'e.isLt).2.val ∧
      s'.arrs = s.arrs ∧ (∀ r, r ≠ 42 → r ≠ 44 → s'.regs r = s.regs r) := by
  let s₁ := s.setReg 42 (x.G.edges[e.val]'e.isLt).1.val
  have he₁ : Exec w (.assign 42 (gm02HostEndpointExpr src false)) s s₁ 7 :=
    .assign (gm02HostEndpointExpr_eval x s src e false hsrc he hw hn hlen)
  let s₂ := s₁.setReg 44 (x.G.edges[e.val]'e.isLt).2.val
  have he₂ : Exec w (.assign 44 (gm02HostEndpointExpr src true)) s₁ s₂ 7 :=
    .assign (gm02HostEndpointExpr_eval x s₁ src e true hsrc
      (by simpa [s₁, State.setReg] using he) hw hn hlen)
  refine ⟨s₂, .seq he₁ he₂, ?_, by simp [s₂], rfl, ?_⟩
  · simp [s₂, s₁]
  · intro r hr42 hr44
    simp only [s₂, s₁, State.setReg_regs_ne _ _ hr42, State.setReg_regs_ne _ _ hr44]

end GraphMinor.Compute
