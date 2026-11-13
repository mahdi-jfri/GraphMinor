module

public import GraphMinor.Compute.GM06Alg34DualGapClassRecord
public import GraphMinor.Compute.GM06Alg34DualDivisionWords

/-!
# Selecting canonical dual division records

Read the retained root flag of a source gap. A root contributes its
computed mapped class record. A nonroot contributes no words. The
fixed root mask survives each record query and remains available for
the following source positions.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Emit the selected source class only when its retained root flag is set. -/
def gm06DualDivisionCandidateProg : Cmd :=
  .ite (.read 45 (.reg 7600)) gm06DualGapClassRecordProg .skip

/-- One canonical-root test emits exactly its selected finite class record. -/
theorem gm06DualDivisionCandidateProg_exec {w cap : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (hLN : L.Nodup) (hDiv : GM06.IsDivision x.divisionSet)
    (g : Fin L.length → Fin x.regions.length) (i : Fin L.length)
    {pre : List ℕ} {s : State} (hw : 2 < 2 ^ w) (hspan : L.length + 2 < 2 ^ w)
    (hdouble : 2 * L.length + 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w) (hrw : x.regions.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length) (hi : s.regs 7600 = i.val)
    (hregions : s.arrs 47 = List.ofFn (fun j => (g j).val))
    (hsource : s.arrs 53 = List.range L.length) (hmask : s.arrs 45 = gm06GapRootMask x L)
    (hbuf : IsPrefixBuffer 55 pre ((gm06DualSelectedClassWords x L g i).length + cap) s)
    (hpos : s.regs 7804 = pre.length)
    (hfit : pre.length + (gm06DualSelectedClassWords x L g i).length < 2 ^ w) :
    ∃ s' t, Exec w gm06DualDivisionCandidateProg s s' t ∧ t ≤ 500 * (L.length + 1) ^ 3 + 3 ∧
      IsPrefixBuffer 55 (pre ++ gm06DualSelectedClassWords x L g i) cap s' ∧
      s'.regs 7804 = (pre ++ gm06DualSelectedClassWords x L g i).length ∧
      (∀ A : ℕ, A ≠ 43 → A ≠ 54 → A ≠ 55 → A ≠ 56 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q < 7820 → q < 120 ∨ 126 ≤ q → q ≠ 0 →
        q < 7601 ∨ 7605 < q → q ≠ 7804 → s'.regs q = s.regs q) := by
  have hk : L.length < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hbit : (Expr.read 45 (.reg 7600)).eval w s =
      some (if gm06GapIsRoot x L i then 1 else 0) := by
    have hlen : i.val < (s.arrs 45).length := by rw [hmask]; simpa only [gm06GapRootMask, List.length_ofFn] using i.isLt
    have hget : (s.arrs 45)[i.val] = if gm06GapIsRoot x L i then 1 else 0 := by
      simp only [hmask, gm06GapRootMask, List.getElem_ofFn]
    cases hh : gm06GapIsRoot x L i <;>
      simp [Expr.eval, checkWord, hi, i.isLt.trans hk, hlen, hget, hh, hw1, Nat.zero_lt_of_lt hw]
  cases hroot : gm06GapIsRoot x L i with
  | false =>
    have hsel : gm06DualSelectedClassWords x L g i = [] := by simp only [gm06DualSelectedClassWords, hroot, Bool.false_eq_true, ↓reduceIte]
    refine ⟨s, 3, .ite_false (by simpa only [hroot, Bool.false_eq_true, ↓reduceIte] using hbit) (.skip s),
      by omega, ?_, ?_, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
    · simpa only [hsel, List.length_nil, Nat.zero_add, List.append_nil] using hbuf
    · simpa only [hsel, List.append_nil] using hpos
  | true =>
    have hsel : gm06DualSelectedClassWords x L g i =
        GM06DrawingData.listWords (gm06DualGapClassWords x L g i) := by
      simp only [gm06DualSelectedClassWords, hroot, ↓reduceIte]
    have hlen : (gm06DualSelectedClassWords x L g i).length =
        1 + (gm06DualGapClassWords x L g i).length := by
      simp only [hsel, GM06DrawingData.listWords, List.length_cons]; omega
    obtain ⟨s', t, he, ht, hb, hp, ha, hg⟩ :=
      gm06DualGapClassRecordProg_exec x L hLN hDiv g i hw hspan hdouble hn hd hrw
        hL hD hbound hi hregions hsource (by simpa only [hlen] using hbuf) hpos (by omega)
    refine ⟨s', 2 + t, .ite_true (by simpa only [hroot, ↓reduceIte] using hbit) (by decide) he,
      by omega, ?_, ?_, ha, hg⟩
    · simpa only [hsel] using hb
    · simpa only [hsel] using hp

end GraphMinor.Compute
