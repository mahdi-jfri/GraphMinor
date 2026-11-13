module

public import GraphMinor.Compute.Algorithm101Stream
public import GraphMinor.Compute.Algorithm94Unpack
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Marking the labels in one encoded linkage row

The given linkage in VI (5.7), page 133, is stored as length-prefixed
rows of directed edge labels. Read one row length, mark its labels
in a working bitset, and advance to the following row. Repeated
labels cause repeated marks and do not change the resulting set.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Mark one length-prefixed label row, advancing cursor 280 past its payload. -/
def gm06MarkLabelRowProg (src dst : Arr) : Cmd :=
  .seq (readStreamWordProg src 280 281)
    (.seq (markSliceGenProg src dst 280 281 282)
      (.assign 280 (.op .add (.reg 280) (.reg 281))))

/-- One encoded row contributes exactly its supplied labels to the
working bitset, in linear row time, without changing the input words. -/
theorem gm06MarkLabelRowProg_exec {w N off : ℕ} (src dst : Arr) (hne : src ≠ dst)
    (L : List (Fin N)) (tail : List ℕ) (S : Finset (Fin N))
    (hw : 1 < 2 ^ w) (hN : N < 2 ^ w) (hoff : off + 1 + L.length < 2 ^ w)
    {s : State} (hs : AtStream src off (L.length :: (L.map Fin.val ++ tail)) s)
    (hp : s.regs 280 = off) (hbits : s.arrs dst = bitSetList S) :
    ∃ s' t, Exec w (gm06MarkLabelRowProg src dst) s s' t ∧ t ≤ 17 + 14 * L.length ∧
      s'.arrs dst = bitSetList (S ∪ L.toFinset) ∧ s'.regs 280 = off + 1 + L.length ∧
      AtStream src (off + 1 + L.length) tail s' ∧
      (∀ a : ℕ, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 280 → q ≠ 281 → q ≠ 282 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hlen₁, hp₁, hs₁, ha₁, hg₁⟩ :=
    readStreamWordProg_exec 280 281 (by decide) hw (by omega) (by omega) hs hp
  have hs₁copy := hs₁
  obtain ⟨pre, hpre, hsrc⟩ := hs₁copy
  obtain ⟨s₂, t₂, he₂, ht₂, hbits₂, ha₂, hg₂⟩ := markSliceGenProg_exec
    (r_start := 280) (r_len := 281) (r_idx := 282) src dst hne (by decide) (by decide)
    pre L tail S hw hN (by simp only [List.length_append, List.length_map, hpre]; exact hoff)
    (by simpa only [List.append_assoc] using hsrc) (hp₁.trans hpre.symm) hlen₁
    ((ha₁ dst).trans hbits)
  have hp₂ : s₂.regs 280 = off + 1 := (hg₂ 280 (by decide)).trans hp₁
  have hlen₂ : s₂.regs 281 = L.length := (hg₂ 281 (by decide)).trans hlen₁
  let s₃ := s₂.setReg 280 (off + 1 + L.length)
  have he₃ : Exec w (.assign 280 (.op .add (.reg 280) (.reg 281))) s₂ s₃ 4 :=
    .assign (eval_add (eval_reg hp₂ (by omega)) (eval_reg hlen₂ (by omega)) hoff)
  have hs₂ : AtStream src (off + 1 + L.length) tail s₂ := by
    have hh := hs₁.append_advance
    have hh' : AtStream src (off + 1 + L.length) tail s₁ := by
      simpa only [List.length_map] using hh
    exact hh'.of_arr_eq (ha₂ src hne)
  refine ⟨s₃, t₁ + (t₂ + 4), .seq he₁ (.seq he₂ he₃), by omega,
    hbits₂, by simp [s₃], hs₂, ?_, ?_⟩
  · intro a ha
    exact (ha₂ a ha).trans (ha₁ a)
  · intro q h280 h281 h282
    exact (State.setReg_regs_ne _ _ h280).trans ((hg₂ q h282).trans (hg₁ q h280 h281))

end GraphMinor.Compute
