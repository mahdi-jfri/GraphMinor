module

public import GraphMinor.Compute.GM06Alg511PackedCall
import Mathlib.Tactic

/-!
# Preserving binary loop rows across the packed successor call

The successor program reads only the original drawing fields and
the current linkage. VI (5.11) also retains its binary current value,
target, increment and loop metadata. Save those four rows together
with the drawing fields, pack the ordinary six-field successor
input, run the supplied command and restore all retained rows.
The result bit and ordinary path output remain exactly as returned.
The overhead is linear in the successor code and retained binary
row lengths. No callee frame on these rows is assumed.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The retained binary current value, target, positive increment
and loop metadata occupy four arrays outside the drawing fields. -/
def gm06Alg511BinaryLoopArrays : List ℕ := [2800, 2801, 2802, 2803]

/-- Both original drawing fields and binary loop rows survive a call. -/
def gm06Alg511BinarySuccessorArrays : List ℕ :=
  gm06Alg511RetainedSuccessorArrays ++ gm06Alg511BinaryLoopArrays

/-- Pack the exact current successor input and protect all binary
loop rows and drawing fields across the supplied successor command. -/
def gm06Alg511BinaryPackedSuccessorCall (callee : Cmd) : Cmd :=
  gm06Alg511PreserveSuccessorCall (gm06Alg511PackAndCall callee) gm06Alg511BinarySuccessorArrays

private theorem retained_field (a : ℕ) (ha : a ∈ gm06Alg511RetainedSuccessorArrays) :
    ∃ i : Fin 6, gm06Alg511SuccessorFieldSources i = a := by
  simp only [gm06Alg511RetainedSuccessorArrays, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩

private theorem source_below_base (callee : Cmd) (i : Fin 6) :
    gm06Alg511SuccessorFieldSources i <
      gm06Alg511CallArrayBase (gm06Alg511PackAndCall callee) gm06Alg511BinarySuccessorArrays := by
  have hb : 1601 ≤ gm06Alg511CallArrayBase (gm06Alg511PackAndCall callee) gm06Alg511BinarySuccessorArrays := by
    dsimp only [gm06Alg511CallArrayBase]
    omega
  have hi : gm06Alg511SuccessorFieldSources i < 1601 := by fin_cases i <;> decide
  exact hi.trans_le hb

/-- The packed successor call retains every original drawing field
and all four binary rows, with exactly the returned bit and path
array. This composes an ordinary array-zero program contract with
actual packing and preservation. It is not a numbered algorithm. -/
theorem gm06Alg511BinaryPackedSuccessorCall_exec {w B : ℕ}
    (callee : Cmd) (x : GM06SuccessorInput) (s : State) (hw : 1 < 2 ^ w)
    (hfit : (gm06EncodeSuccessorInput x).length < 2 ^ w)
    (hwords : ∀ d ∈ gm06EncodeSuccessorInput x, d < 2 ^ w)
    (hfields : ∀ i : Fin 6, s.arrs (gm06Alg511SuccessorFieldSources i) =
      (gm06SuccessorRows x)[i.val]'(by simp [gm06SuccessorRows]))
    (hbinary : ∀ a ∈ gm06Alg511BinaryLoopArrays, (s.arrs a).length < 2 ^ w ∧
      ∀ d ∈ s.arrs a, d < 2 ^ w)
    (hregs : ∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], s.regs j < 2 ^ w)
    (post : State → Prop)
    (hcall : ∀ ss, ss.arrs 0 = gm06EncodeSuccessorInput x →
      ∃ raw u, Exec w callee ss raw u ∧ u ≤ B ∧ post raw) :
    ∃ t raw u, Exec w (gm06Alg511BinaryPackedSuccessorCall callee) s t u ∧
      u ≤ B + 185 + 68 * (gm06EncodeSuccessorInput x).length +
        24 * (gm06Alg511BinaryLoopArrays.map (fun a => (s.arrs a).length)).sum ∧
      post raw ∧ t.regs 0 = raw.regs 0 ∧ t.arrs 8 = raw.arrs 8 ∧
      (∀ a ∈ gm06Alg511BinarySuccessorArrays, t.arrs a = s.arrs a) ∧
      ∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], t.regs j = s.regs j := by
  have hfield_words (i : Fin 6) : (s.arrs (gm06Alg511SuccessorFieldSources i)).length < 2 ^ w ∧
      ∀ d ∈ s.arrs (gm06Alg511SuccessorFieldSources i), d < 2 ^ w := by
    rw [hfields i]
    have hm : (gm06SuccessorRows x)[i.val]'(by simp [gm06SuccessorRows]) ∈ gm06SuccessorRows x :=
      List.getElem_mem (by simp [gm06SuccessorRows])
    exact ⟨(gm06Alg511_encoded_row_length_le hm).trans_lt hfit,
      fun d hd => hwords d (gm06Alg511_mem_encoded_row hm hd)⟩
  have hall (a : ℕ) (ha : a ∈ gm06Alg511BinarySuccessorArrays) :
      (s.arrs a).length < 2 ^ w ∧ ∀ d ∈ s.arrs a, d < 2 ^ w := by
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, rfl⟩ := retained_field a ha
      exact hfield_words i
    · exact hbinary a ha
  obtain ⟨t, raw, u, he, ht, hp, hbit, hpath, hretained, hloop⟩ :=
    gm06Alg511PreserveSuccessorCall_exec
      (B := B + 45 + 44 * (gm06EncodeSuccessorInput x).length)
      (gm06Alg511PackAndCall callee) gm06Alg511BinarySuccessorArrays (by decide) (by decide) s hw
      (fun a ha => (hall a ha).1) (fun a ha => (hall a ha).2) hregs post (by
        intro ss harr _
        have hss (i : Fin 6) : ss.arrs (gm06Alg511SuccessorFieldSources i) =
            (gm06SuccessorRows x)[i.val]'(by simp [gm06SuccessorRows]) :=
          (harr _ (source_below_base callee i)).trans (hfields i)
        obtain ⟨sp, up, hep, htp, h0, _, _⟩ := gm06Alg511PackSuccessorInput_exec x
          gm06Alg511SuccessorFieldSources (by intro i; fin_cases i <;> decide) ss hw hfit hwords hss
        obtain ⟨raw, uraw, heraw, htraw, hp⟩ := hcall sp h0
        exact ⟨raw, up + uraw, .seq hep heraw, by omega, hp⟩)
  have hlen : gm06Alg511BinarySuccessorArrays.length = 9 := rfl
  have hsum : (gm06Alg511BinarySuccessorArrays.map (fun a => (s.arrs a).length)).sum =
      (gm06Alg511RetainedSuccessorArrays.map (fun a => (s.arrs a).length)).sum +
        (gm06Alg511BinaryLoopArrays.map (fun a => (s.arrs a).length)).sum := by
    rw [gm06Alg511BinarySuccessorArrays, List.map_append, List.sum_append]
  rw [hlen, hsum] at ht
  have hsize := gm06Alg511RetainedFields_length_le x s hfields
  exact ⟨t, raw, u, he, by omega, hp, hbit, hpath, hretained, hloop⟩

end GraphMinor.Compute
