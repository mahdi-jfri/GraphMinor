module

public import GraphMinor.Compute.GM02StoreSlots
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Decoding a candidate into an array

Allocate a fixed-length array, decode the candidate's base digits into
registers, and copy those registers into the array. This supplies the
edge choices for the split-graph search in Graph Minors II (4.6), page
319. The proof composes the decoder and copy commands and retains their
frames and polynomial time bounds.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Decode a fixed number of base digits into an array. -/
@[expose] def gm02DecodeDigitsArrayProg (dst : Arr) (k : ℕ) : Cmd :=
  .seq (.alloc dst (.const k))
    (.seq (gm02DecodeSlots k) (gm02StoreSlotsProg dst k))

/-- The array decoder computes the exact digit list and preserves all unrelated arrays
and all registers outside the decoder's slot interval. -/
theorem gm02DecodeDigitsArrayProg_exec {w n code : ℕ} (dst : Arr) (k : ℕ) (s : State)
    (hrn : s.regs 40 = n) (hcode : s.regs 190 = code)
    (hb : n + 1 < 2 ^ w) (hc : code < 2 ^ w) (hp : (n + 1) ^ k < 2 ^ w)
    (hk : k < 2 ^ w) :
    ∃ s' t, Exec w (gm02DecodeDigitsArrayProg dst k) s s' t ∧
      t ≤ 3 + k * (12 + 4 * k) ∧
      s'.arrs dst = List.ofFn (fun i : Fin k => gm02SeparatorDigit n code i.val) ∧
      (∀ r : Reg, r < 200 ∨ 200 + k ≤ r → s'.regs r = s.regs r) ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) := by
  let s₀ := s.setArr dst (List.replicate k 0)
  have he₀ : Exec w (.alloc dst (.const k)) s s₀ (1 + k) := .alloc (eval_const hk)
  obtain ⟨s₁, t₁, he₁, ht₁, hslots, hregs, harr⟩ :=
    gm02DecodeSlots_exec k s₀ hrn hcode hb hc hp
  have hinit : s₁.arrs dst = List.replicate k 0 := by
    rw [harr]
    exact State.setArr_arrs_self ..
  obtain ⟨s₂, t₂, he₂, ht₂, hout, hr₂, ha₂⟩ :=
    gm02StoreSlotsProg_exec dst (fun i : Fin k => gm02SeparatorDigit n code i.val)
      s₁ hinit hslots hk (fun i => (gm02SeparatorDigit_le n code i.val).trans_lt (by omega))
  refine ⟨s₂, (1 + k) + (t₁ + t₂), .seq he₀ (.seq he₁ he₂), ?_, hout, ?_, ?_⟩
  · simp only [Nat.mul_add] at ht₁ ⊢
    omega
  · intro r hr
    exact (congrFun hr₂ r).trans (hregs r hr)
  · intro a ha
    exact (ha₂ a ha).trans ((congrFun harr a).trans (State.setArr_arrs_ne s _ ha))

end GraphMinor.Compute
