module

public import GraphMinor.Compute.Join13Write72
public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Writing the edge labels of society paths

The output loops write a word expression at every position of a fresh
array. A direction bit selects the tail or head of an actual edge. Only
the loop counter and the destination array change.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths
open GraphMinor.Compute.Crossing

/-- Fill a fresh array with the values of an expression at successive indices. -/
def gm13TabulateProg (r : Reg) (count value : Expr) (dst : Arr) : Cmd :=
  .seq (.alloc dst count) (fillModelPart72Prog r count (.const 0) value dst)

/-- The array-writing loop keeps all its source data and writes exactly the
specified words. Its cost is linear in the number of output words. -/
theorem gm13TabulateProg_exec {w : ℕ} (r : Reg) (count value : Expr) (dst : Arr)
    (words : List ℕ) (s : State) (hw : 1 < 2 ^ w) (hlen : words.length < 2 ^ w)
    (hcount : ∀ st, Keeps [r] [dst] s st → count.eval w st = some words.length)
    (hvalue : ∀ st i (hi : i < words.length), Keeps [r] [dst] s st →
      st.regs r = i → value.eval w st = some words[i]) :
    ∃ s' t, Exec w (gm13TabulateProg r count value dst) s s' t ∧
      t ≤ 4 + 2 * count.cost + words.length * (count.cost + value.cost + 11) ∧
      Keeps [r] [dst] s s' ∧ s'.arrs dst = words := by
  let s₁ := s.setArr dst (List.replicate words.length 0)
  have hk₁ : Keeps [r] [dst] s s₁ := (Keeps.refl _ _ s).setArr (by simp) _
  have he₁ : Exec w (.alloc dst count) s s₁ (count.cost + words.length) :=
    .alloc (hcount s (Keeps.refl _ _ s))
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂, _⟩ :=
    fillModelPart72Prog_exec r count (.const 0) value dst words [] words.length s₁ hw
      le_rfl (by simpa using hlen)
      (fun st hk => hcount st (hk₁.trans hk (fun _ h => h) (fun _ h => h)))
      (fun _ _ => eval_const (by omega))
      (fun st i hi hk hr => hvalue st i hi
        (hk₁.trans hk (fun _ h => h) (fun _ h => h)) hr)
      (by simp [s₁])
  refine ⟨s₂, count.cost + words.length + t₂, .seq he₁ he₂, ?_,
    hk₁.trans hk₂ (fun _ h => h) (fun _ h => h), ?_⟩
  · simp only [Expr.cost_const] at ht₂
    have heq : words.length * (count.cost + value.cost + 11) =
        words.length * (count.cost + 1 + value.cost + 9) + words.length := by ring
    omega
  · simpa only [List.length_nil, List.nil_append, Nat.sub_self, List.replicate_zero,
      List.append_nil] using hd₂

/-- Select `u` when the direction bit is one, and `v` when it is zero. -/
def gm13SelectExpr (bit u v : Expr) : Expr :=
  .op .add (.op .mul bit u) (.op .mul (.op .sub (.const 1) bit) v)

/-- A zero/one direction flag selects exactly one endpoint, without changing
or searching the source graph. -/
theorem gm13SelectExpr_eval {w u v : ℕ} {s : State} {P : Prop} [Decidable P]
    {bit U V : Expr} (hw : 1 < 2 ^ w)
    (hb : bit.eval w s = some (if P then 1 else 0))
    (hu : U.eval w s = some u) (hv : V.eval w s = some v) :
    (gm13SelectExpr bit U V).eval w s = some (if P then u else v) := by
  have huw := Expr.eval_lt hu
  have hvw := Expr.eval_lt hv
  by_cases hp : P
  · simp only [hp, ↓reduceIte] at hb ⊢
    have hleft := eval_mul hb hu (show 1 * u < 2 ^ w by omega)
    have hsub := eval_sub (eval_const hw) hb
    have hright := eval_mul hsub hv (show (1 - 1) * v < 2 ^ w by omega)
    simpa only [gm13SelectExpr, Nat.one_mul, Nat.sub_self, Nat.zero_mul,
      Nat.add_zero] using eval_add hleft hright (by omega)
  · simp only [hp, ↓reduceIte] at hb ⊢
    have hleft := eval_mul hb hu (show 0 * u < 2 ^ w by omega)
    have hsub := eval_sub (eval_const hw) hb
    have hright := eval_mul hsub hv (show (1 - 0) * v < 2 ^ w by omega)
    simpa only [gm13SelectExpr, Nat.zero_mul, Nat.sub_zero, Nat.one_mul,
      Nat.zero_add] using eval_add hleft hright (by omega)

end GraphMinor.Compute
