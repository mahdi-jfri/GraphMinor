module

public import GraphMinor.Compute.GM02TopologicalEndpointWords
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Reading a pattern endpoint in the loop-search body

The pattern endpoint prefix and edge position are stored in registers.
Read either endpoint directly at its even or odd offset in the supplied
array. The encoding identities prove the value and all intermediate
word bounds needed for the actual RAM expression.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Read one supplied endpoint of edge position 43, using prefix offset 16. -/
def gm02PatternEndpointExpr (src : Arr) (side : Bool) : Expr :=
  .read src (.op .add (.op .add (.reg 16) (.op .mul (.const 2) (.reg 43)))
    (.const (if side then 1 else 0)))

/-- The endpoint expression has fixed cost. -/
theorem gm02PatternEndpointExpr_cost (src : Arr) (side : Bool) :
    (gm02PatternEndpointExpr src side).cost = 8 := rfl

/-- The expression reads exactly the supplied endpoint and all index arithmetic fits a word. -/
theorem gm02PatternEndpointExpr_eval {w : ℕ} (x : GM02TopologicalInput) (s : State)
    (src : Arr) (f : Fin x.edges.length) (side : Bool)
    (hsrc : s.arrs src = x.enc)
    (hoff : s.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card) (hf : s.regs 43 = f.val)
    (hw : 2 < 2 ^ w) (hn : x.G.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    (gm02PatternEndpointExpr src side).eval w s = some (if side then (x.ends f).2 else (x.ends f).1) := by
  let d : ℕ := if side then 1 else 0
  have hd : d ≤ 1 := by cases side <;> decide
  have hdw : d < 2 ^ w := by omega
  have hLen := x.enc_length
  have hfLen := f.isLt
  have hfw : f.val < 2 ^ w := by omega
  have h2fw : 2 * f.val < 2 ^ w := by omega
  have hoffw : 4 + 2 * x.G.edges.length + x.vertices.card < 2 ^ w := by omega
  have hsumw : 4 + 2 * x.G.edges.length + x.vertices.card + 2 * f.val < 2 ^ w := by omega
  have haddrw : 4 + 2 * x.G.edges.length + x.vertices.card + 2 * f.val + d < 2 ^ w := by omega
  have hidx : (Expr.op .add (.op .add (.reg 16) (.op .mul (.const 2) (.reg 43))) (.const d)).eval w s =
      some (4 + 2 * x.G.edges.length + x.vertices.card + 2 * f.val + d) :=
    eval_add (eval_add (eval_reg hoff hoffw) (eval_mul (eval_const hw) (eval_reg hf hfw) h2fw) hsumw)
      (eval_const hdw) haddrw
  have hget : (s.arrs src)[4 + 2 * x.G.edges.length + x.vertices.card + 2 * f.val + d]? =
      some (if side then (x.ends f).2 else (x.ends f).1) := by
    cases side
    · simpa only [hsrc, d, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using x.enc_pattern_fst f
    · simpa only [hsrc, d, ↓reduceIte] using x.enc_pattern_snd f
  have hval : (if side then (x.ends f).2 else (x.ends f).1) < 2 ^ w := by
    have hleft : (x.ends f).1 < x.G.n := (x.edges[f.val]'f.isLt).1.isLt
    have hright : (x.ends f).2 < x.G.n := (x.edges[f.val]'f.isLt).2.isLt
    cases side
    · exact hleft.trans hn
    · exact hright.trans hn
  obtain ⟨hi, heq⟩ := List.getElem?_eq_some_iff.1 hget
  simpa only [gm02PatternEndpointExpr, d, heq] using eval_read hidx hi (heq ▸ hval)

end GraphMinor.Compute
