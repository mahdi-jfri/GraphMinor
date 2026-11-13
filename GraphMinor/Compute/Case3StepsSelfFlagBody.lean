module

public import GraphMinor.Compute.Logic

/-!
# A self-label flag scan

The group selector compares a stored owner label with its own numeric label.
The output is a normalized zero-or-one word. An offset permits the same scan
to write the component and core-edge blocks of the selected-group bitset.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Flags testing whether each label is its own offset index. -/
def case3SelfFlagList (labels : List ℕ) (off : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin labels.length => if labels[i.1] = off + i.1 then 1 else 0)

/-- The flags and source labels have the same length. -/
theorem case3SelfFlagList_length (labels : List ℕ) (off : ℕ) :
    (case3SelfFlagList labels off).length = labels.length := by
  simp only [case3SelfFlagList, List.length_ofFn]

/-- Each flag is the corresponding self-label test. -/
theorem getElem_case3SelfFlagList (labels : List ℕ) (off k : ℕ) (hk : k < labels.length) :
    (case3SelfFlagList labels off)[k]'(by rw [case3SelfFlagList_length]; exact hk) =
      if labels[k] = off + k then 1 else 0 := by
  simp only [case3SelfFlagList, List.getElem_ofFn]

/-- Compare one source label with its offset index and write its flag. -/
def case3SelfFlagBody (a_src a_dst r_off r_i : ℕ) : Cmd :=
  .write a_dst (.op .add (.reg r_off) (.reg r_i))
    (.op .eq (.read a_src (.reg r_i)) (.op .add (.reg r_off) (.reg r_i)))

/-- One self-label flag takes ten steps, with every address and value checked
against the word bound. -/
theorem case3SelfFlagBody_exec {w : ℕ} (labels : List ℕ) (off k : ℕ)
    (hk : k < labels.length) (a_src a_dst r_off r_i : ℕ)
    (hw : 1 < 2 ^ w) (hsize : off + labels.length < 2 ^ w)
    (hwords : ∀ z ∈ labels, z < 2 ^ w) {s : State}
    (hsrc : s.arrs a_src = labels) (hdst : off + labels.length ≤ (s.arrs a_dst).length)
    (hroff : s.regs r_off = off) (hri : s.regs r_i = k) :
    Exec w (case3SelfFlagBody a_src a_dst r_off r_i) s
      (s.writeArr a_dst (off + k) (if labels[k] = off + k then 1 else 0)) 10 := by
  have h0 : 0 < 2 ^ w := by omega
  have hoffw : off < 2 ^ w := by omega
  have hkw : k < 2 ^ w := by omega
  have hidxw : off + k < 2 ^ w := by omega
  have hidx : k < (s.arrs a_src).length := by rw [hsrc]; exact hk
  have hget : (s.arrs a_src)[k]'hidx = labels[k] := by simp only [hsrc]
  have hz : labels[k] < 2 ^ w := hwords _ (List.getElem_mem hk)
  have hi : (Expr.op .add (.reg r_off) (.reg r_i)).eval w s = some (off + k) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hroff, hri, hoffw, hkw, hidxw]
  have hv : (Expr.op .eq (.read a_src (.reg r_i))
      (.op .add (.reg r_off) (.reg r_i))).eval w s = some (if labels[k] = off + k then 1 else 0) := by
    by_cases heq : labels[k] = off + k <;>
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hroff, hri, hoffw, hkw, hidxw,
        hidx, hget, hz, heq, hw, h0]
  exact .write hi hv (by omega)

end GraphMinor.Compute
