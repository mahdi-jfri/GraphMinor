module

public import GraphMinor.Compute.GM02EmitTemplateWords
public import GraphMinor.Compute.GM02TemplateBits

/-!
# Emitting the endpoint fields of a fixed scheme template

A fixed list of boundary endpoints supplies both the pair words and
their support. Emit the parent endpoint names and mark exactly their
image set. These two fields share the same input-derived old-name table
and are the data used to construct an induced recursive termination.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.Compute.Crossing TwoPaths

/-- Emit endpoint words and support bits from one fixed boundary list. -/
def gm02TemplatePairFieldsProg (orig block words support : Arr) (indices : List ℕ) : Cmd :=
  .seq (gm02EmitTemplateWordsProg orig block words indices)
    (gm02TemplateBitsProg orig support indices)

/-- Both emitted fields describe precisely the same expanded endpoint list. -/
theorem gm02TemplatePairFieldsProg_exec {n b w : ℕ} (f : Fin b → Fin n)
    (indices : List (Fin b)) (orig block words support : Arr)
    (hob : orig ≠ block) (how : orig ≠ words) (hos : orig ≠ support)
    (hbw : block ≠ words) (hws : words ≠ support) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hb : b < 2 ^ w)
    (hlen : indices.length < 2 ^ w)
    (horig : s.arrs orig = List.ofFn (fun i => (f i).val)) (hcount : s.regs 40 = n) :
    ∃ s' t, Exec w (gm02TemplatePairFieldsProg orig block words support
      (indices.map Fin.val)) s s' t ∧
      t ≤ 16 + 21 * indices.length + n * (15 + 7 * indices.length) ∧
      s'.arrs words = indices.map (fun i => (f i).val) ∧
      s'.arrs support = bitSetList (indices.toFinset.image f) ∧
      Keeps [343, 342, 340] [block, words, support] s s' := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hwords⟩ :=
    gm02EmitTemplateWordsProg_exec f indices orig block words hob how hbw s hw hn hb hlen horig
  have horig₁ : s₁.arrs orig = List.ofFn (fun i => (f i).val) :=
    (hk₁.2 orig (by simp [hob, how])).trans horig
  have hn₁ : s₁.regs 40 = n := (hk₁.1 40 (by decide)).trans hcount
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hsupport⟩ :=
    gm02TemplateBitsProg_exec f indices orig support hos s₁ hw hn hb horig₁ hn₁
  refine ⟨s₂, t₁ + t₂, Exec.seq he₁ he₂, by omega, ?_, hsupport, ?_⟩
  · exact (hk₂.2 words (by simpa only [List.mem_singleton] using hws)).trans hwords
  · constructor
    · intro r hr
      have hrs : r ≠ 343 ∧ r ≠ 342 ∧ r ≠ 340 := by simpa using hr
      exact (hk₂.1 r (by simp [hrs.2.2])).trans (hk₁.1 r (by simp [hrs.1, hrs.2.1]))
    · intro a ha
      have has : a ≠ block ∧ a ≠ words ∧ a ≠ support := by simpa using ha
      exact (hk₂.2 a (by simp [has.2.2])).trans (hk₁.2 a (by simp [has.1, has.2.1]))

end GraphMinor.Compute
