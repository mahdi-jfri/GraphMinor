module

public import GraphMinor.Compute.GM02LookupTemplateWords
public import GraphMinor.Compute.Algorithm101Stream

/-!
# Emitting endpoint words for a fixed catalogue branch

Write the branch's fixed boundary indices to a scratch array, then look
them up in the stored old-name array. The constants belong to the
program, while every parent vertex name comes from its input-derived
numbering table. Both operations preserve the parent input.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.Compute.Crossing TwoPaths

/-- Emit a fixed endpoint-index template in original parent names. -/
def gm02EmitTemplateWordsProg (orig block dst : Arr) (indices : List ℕ) : Cmd :=
  .seq (writeConstListProg block 343 indices) (gm02LookupTemplateWordsProg block orig dst)

/-- A fixed template is expanded exactly, with cost bounded by its fixed length. -/
theorem gm02EmitTemplateWordsProg_exec {n b w : ℕ} (f : Fin b → Fin n)
    (indices : List (Fin b)) (orig block dst : Arr)
    (hob : orig ≠ block) (hod : orig ≠ dst) (hbd : block ≠ dst) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hb : b < 2 ^ w)
    (hlen : indices.length < 2 ^ w)
    (horig : s.arrs orig = List.ofFn (fun i => (f i).val)) :
    ∃ s' t, Exec w (gm02EmitTemplateWordsProg orig block dst (indices.map Fin.val)) s s' t ∧
      t ≤ 10 + 21 * indices.length ∧ Keeps [343, 342] [block, dst] s s' ∧
      s'.arrs dst = indices.map (fun i => (f i).val) := by
  obtain ⟨s₁, t₁, he₁, ht₁, harr₁, ha₁, hr₁⟩ :=
    writeConstListProg_exec block 343 (indices.map Fin.val) hw
      (by simpa only [List.length_map] using hlen)
      (by
        intro i hi
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
        exact j.isLt.trans hb) s
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hout⟩ :=
    gm02LookupTemplateWordsProg_exec f indices block orig dst hbd hod s₁ hw hn hb hlen
      harr₁ ((ha₁ orig hob).trans horig)
  refine ⟨s₂, t₁ + t₂, Exec.seq he₁ he₂, ?_, ?_, hout⟩
  · simp only [List.length_map] at ht₁
    omega
  · constructor
    · intro r hr
      have hrs : r ≠ 343 ∧ r ≠ 342 := by
        simpa using hr
      have hr343 := hrs.1
      have hr342 := hrs.2
      exact (hk₂.1 r (by simpa only [List.mem_singleton] using hr342)).trans (hr₁ r hr343)
    · intro a ha
      have hab : a ≠ block := by
        intro h
        exact ha (by simp [h])
      have had : a ≠ dst := by
        intro h
        exact ha (by simp [h])
      exact (hk₂.2 a (by simpa only [List.mem_singleton] using had)).trans (ha₁ a hab)

end GraphMinor.Compute
