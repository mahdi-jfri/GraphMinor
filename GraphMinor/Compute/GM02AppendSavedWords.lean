module

public import GraphMinor.Compute.Algorithm101Stream
public import GraphMinor.Compute.TwoPathsCyc

/-!
# Writing saved-frame header words

A saved frame has a fixed list of header expressions: array lengths
and loop-state registers. Append their values one by one. The proof
requires the expressions to retain their values while only the buffer
and cursor change, and records the exact resulting prefix and cost.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Append the values of a fixed expression list to the saved-frame buffer. -/
def gm02AppendSavedWordsProg (stack : Arr) (r_pos : Reg) : List Expr → Cmd
  | [] => .skip
  | e :: es => .seq (appendWordProg stack r_pos e) (gm02AppendSavedWordsProg stack r_pos es)

/-- A fixed header-expression list writes exactly its values in order. -/
theorem gm02AppendSavedWordsProg_exec {w cap : ℕ} (stack : Arr) (r_pos : Reg)
    (es : List Expr) (words pref : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hlen : pref.length + words.length < 2 ^ w)
    (hstack : IsPrefixBuffer stack pref (words.length + cap) s)
    (hpos : s.regs r_pos = pref.length)
    (hvalues : ∀ st, Keeps [r_pos] [stack] s st →
      List.Forall₂ (fun e v => e.eval w st = some v) es words) :
    ∃ s' t, Exec w (gm02AppendSavedWordsProg stack r_pos es) s s' t ∧
      t ≤ (es.map Expr.cost).sum + 6 * words.length + 1 ∧
      IsPrefixBuffer stack (pref ++ words) cap s' ∧
      s'.regs r_pos = (pref ++ words).length ∧ Keeps [r_pos] [stack] s s' := by
  induction es generalizing words pref s with
  | nil =>
    have hh := hvalues s (Keeps.refl _ _ s)
    cases words with
    | nil => exact ⟨s, 1, Exec.skip s, by simp, by simpa using hstack,
        by simpa using hpos, Keeps.refl _ _ s⟩
    | cons v vs => cases hh
  | cons e es ih =>
    have hh := hvalues s (Keeps.refl _ _ s)
    cases words with
    | nil => cases hh
    | cons v vs =>
      cases hh with
      | cons hv _ =>
        obtain ⟨s₁, t₁, he₁, ht₁, hstack₁, hpos₁, ha₁, hr₁⟩ :=
          appendWordProg_exec (cap := vs.length + cap) stack r_pos e hw
            (by simp only [List.length_cons] at hlen; omega)
            (by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstack)
            hpos hv
        have hk₁ : Keeps [r_pos] [stack] s s₁ := by
          constructor
          · intro r hr
            exact hr₁ r (by simpa only [List.mem_singleton] using hr)
          · intro a ha
            exact ha₁ a (by simpa only [List.mem_singleton] using ha)
        obtain ⟨s₂, t₂, he₂, ht₂, hstack₂, hpos₂, hk₂⟩ :=
          ih vs (pref ++ [v]) s₁
            (by simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢; omega)
            hstack₁ hpos₁ (fun st hk => by
              have hvv := hvalues st (hk₁.trans hk (fun _ h => h) (fun _ h => h))
              cases hvv with | cons _ ht => exact ht)
        refine ⟨s₂, t₁ + t₂, Exec.seq he₁ he₂, ?_, ?_, ?_,
          hk₁.trans hk₂ (fun _ h => h) (fun _ h => h)⟩
        · simp only [List.map_cons, List.sum_cons, List.length_cons] at ht₂ ⊢
          omega
        · simpa only [List.append_assoc, List.singleton_append] using hstack₂
        · simpa only [List.append_assoc, List.singleton_append] using hpos₂

end GraphMinor.Compute
