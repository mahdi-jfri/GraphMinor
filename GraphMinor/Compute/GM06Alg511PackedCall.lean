module

public import GraphMinor.Compute.GM06Alg511CallArrays
public import GraphMinor.Compute.GM06Alg511PrepareFields
import GraphMinor.Compute.GM06Alg511SelectField
import Mathlib.Tactic

/-!
# The packed successor call in the feasibility loop

VI (5.11), page 134, reuses the same original drawing at every
successor call and replaces only the current path rows. Pack its
five retained structural fields and the computed path table, call
the supplied command on that exact input, and restore the original
fields and all seven winding-loop registers. Array 8 and the result
bit are left exactly as the command returned them. This file proves
the operational composition, including its linear packing overhead.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The original graph, rotations and cuffs survive every call.
The current path table in array 8 is replaced by the callee. -/
def gm06Alg511RetainedSuccessorArrays : List ℕ := [1500, 1230, 1231, 1210, 1211]

/-- Pack the six fields immediately before running the supplied
successor command on its ordinary input array. -/
def gm06Alg511PackAndCall (callee : Cmd) : Cmd :=
  .seq (gm06Alg511PackSuccessorProg (List.ofFn gm06Alg511SuccessorFieldSources)) callee

/-- One loop call packs the current linkage and retains the
original drawing and scalar loop words across the computation. -/
def gm06Alg511PackedSuccessorCall (callee : Cmd) : Cmd :=
  gm06Alg511PreserveSuccessorCall (gm06Alg511PackAndCall callee) gm06Alg511RetainedSuccessorArrays

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
      gm06Alg511CallArrayBase (gm06Alg511PackAndCall callee) gm06Alg511RetainedSuccessorArrays := by
  have hbase : 1601 ≤ gm06Alg511CallArrayBase (gm06Alg511PackAndCall callee)
      gm06Alg511RetainedSuccessorArrays := by
    dsimp only [gm06Alg511CallArrayBase]
    omega
  have hi : gm06Alg511SuccessorFieldSources i < 1601 := by fin_cases i <;> decide
  exact hi.trans_le hbase

/-- The retained fields occupy fewer words than their complete
six-field successor input, including its current path table. -/
theorem gm06Alg511RetainedFields_length_le (x : GM06SuccessorInput) (s : State)
    (hfields : ∀ i : Fin 6, s.arrs (gm06Alg511SuccessorFieldSources i) =
      (gm06SuccessorRows x)[i.val]'(by simp [gm06SuccessorRows])) :
    (gm06Alg511RetainedSuccessorArrays.map (fun a => (s.arrs a).length)).sum ≤
      (gm06EncodeSuccessorInput x).length := by
  have hV : s.arrs 1500 = [x.vertexCount] := hfields 0
  have hE : s.arrs 1230 = x.endpoints := hfields 1
  have hR : s.arrs 1231 = gm06EncodeRows x.rotations := hfields 2
  have hI : s.arrs 1210 = x.innerCuff := hfields 3
  have hO : s.arrs 1211 = x.outerCuff := hfields 4
  simp only [gm06Alg511RetainedSuccessorArrays, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, hV, hE, hR, hI, hO, List.length_singleton]
  simp only [gm06EncodeSuccessorInput, gm06SuccessorRows, gm06EncodeRows,
    gm06EncodeRowsPayload, gm06EncodeNatList, List.flatMap_cons, List.flatMap_nil,
    List.length_cons, List.length_append, List.length_nil]
  omega

/-- Given execution of a command from the ordinary successor input,
the packed loop call runs it with no original-register or array frame
assumption. The returned bit and path array are exactly its outputs,
and the five retained fields and seven scalar loop words survive.
This is a composition theorem for a command, not theorem (5.11). -/
theorem gm06Alg511PackedSuccessorCall_exec {w B : ℕ}
    (callee : Cmd) (x : GM06SuccessorInput) (s : State) (hw : 1 < 2 ^ w)
    (hfit : (gm06EncodeSuccessorInput x).length < 2 ^ w)
    (hwords : ∀ d ∈ gm06EncodeSuccessorInput x, d < 2 ^ w)
    (hfields : ∀ i : Fin 6, s.arrs (gm06Alg511SuccessorFieldSources i) =
      (gm06SuccessorRows x)[i.val]'(by simp [gm06SuccessorRows]))
    (hregs : ∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], s.regs j < 2 ^ w)
    (post : State → Prop)
    (hcall : ∀ ss, ss.arrs 0 = gm06EncodeSuccessorInput x →
      ∃ raw u, Exec w callee ss raw u ∧ u ≤ B ∧ post raw) :
    ∃ t raw u, Exec w (gm06Alg511PackedSuccessorCall callee) s t u ∧
      u ≤ B + 137 + 68 * (gm06EncodeSuccessorInput x).length ∧
      post raw ∧ t.regs 0 = raw.regs 0 ∧ t.arrs 8 = raw.arrs 8 ∧
      (∀ a ∈ gm06Alg511RetainedSuccessorArrays, t.arrs a = s.arrs a) ∧
      ∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], t.regs j = s.regs j := by
  have hfield_words (i : Fin 6) : (s.arrs (gm06Alg511SuccessorFieldSources i)).length < 2 ^ w ∧
      ∀ d ∈ s.arrs (gm06Alg511SuccessorFieldSources i), d < 2 ^ w := by
    rw [hfields i]
    have hm : (gm06SuccessorRows x)[i.val]'(by simp [gm06SuccessorRows]) ∈ gm06SuccessorRows x :=
      List.getElem_mem (by simp [gm06SuccessorRows])
    exact ⟨(gm06Alg511_encoded_row_length_le hm).trans_lt hfit,
      fun d hd => hwords d (gm06Alg511_mem_encoded_row hm hd)⟩
  obtain ⟨t, raw, u, he, ht, hp, hbit, hpath, hretained, hloop⟩ :=
    gm06Alg511PreserveSuccessorCall_exec
      (B := B + 45 + 44 * (gm06EncodeSuccessorInput x).length)
      (gm06Alg511PackAndCall callee) gm06Alg511RetainedSuccessorArrays
      (by decide) (by decide) s hw
      (by
        intro a ha
        obtain ⟨i, rfl⟩ := retained_field a ha
        exact (hfield_words i).1)
      (by
        intro a ha
        obtain ⟨i, rfl⟩ := retained_field a ha
        exact (hfield_words i).2)
      hregs post (by
        intro ss harr _
        have hss (i : Fin 6) : ss.arrs (gm06Alg511SuccessorFieldSources i) =
            (gm06SuccessorRows x)[i.val]'(by simp [gm06SuccessorRows]) :=
          (harr _ (source_below_base callee i)).trans (hfields i)
        obtain ⟨sp, up, hep, htp, h0, _, _⟩ := gm06Alg511PackSuccessorInput_exec x
          gm06Alg511SuccessorFieldSources (by intro i; fin_cases i <;> decide)
          ss hw hfit hwords hss
        obtain ⟨raw, uraw, heraw, htraw, hp⟩ := hcall sp h0
        exact ⟨raw, up + uraw, .seq hep heraw, by omega, hp⟩)
  have hlen : gm06Alg511RetainedSuccessorArrays.length = 5 := rfl
  rw [hlen] at ht
  have hsize := gm06Alg511RetainedFields_length_le x s hfields
  exact ⟨t, raw, u, he, by omega, hp, hbit, hpath, hretained, hloop⟩

end GraphMinor.Compute
