module

public import GraphMinor.Compute.GM06SelectRow
public import GraphMinor.Compute.GM06RotationSector
import GraphMinor.Compute.GM06SuccessorDegreeScan

/-!
# Querying a sector in an indexed rotation

Select the supplied vertex's rotation row, then locate the three
supplied directed labels and compute their cyclic-sector flag. The
vertex index and labels are register values. The same RAM program
handles every finite input, and preserves the coded source rotations.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Select a rotation row by register 31 and query its labels in registers 36--38. -/
def gm06RotationRowSectorProg (src work : Arr) : Cmd :=
  .seq (gm06SelectRowProg src work) (gm06RotationSectorProg work)

/-- The combined row and sector query computes the supplied rotation's cyclic-order flag. -/
theorem gm06RotationRowSectorProg_exec {w : ℕ} (src work : ℕ) (hne : src ≠ work)
    (rows : List (List ℕ)) (i : ℕ) (hi : i < rows.length) (p q r : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (ha : s.arrs src = gm06EncodeRows rows)
    (hn : (gm06EncodeRows rows).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06EncodeRows rows, v < 2 ^ w)
    (hnd : rows[i].Nodup) (hp : p ∈ rows[i]) (hq : q ∈ rows[i]) (hr : r ∈ rows[i])
    (h31 : s.regs 31 = i) (h36 : s.regs 36 = p) (h37 : s.regs 37 = q) (h38 : s.regs 38 = r) :
    ∃ s' t, Exec w (gm06RotationRowSectorProg src work) s s' t ∧
      t ≤ 50 + 17 * i + 61 * rows[i].length ∧ s'.arrs src = s.arrs src ∧
      s'.regs 43 = (if GM06DrawingData.cyclicBetween
        (rows[i].idxOf p) (rows[i].idxOf q) (rows[i].idxOf r) then 1 else 0) ∧
      Keeps [7, 8, 9, 11, 31, 50, 40, 41, 42, 43] [work] s s' ∧ s'.arrs work = rows[i] := by
  obtain ⟨s₁, t₁, he₁, ht₁, hd₁, _, hs₁, hk₁⟩ :=
    gm06SelectRowProg_exec src work hne rows i hi s (by omega) ha hn hwords h31
  have hbound := gm06Row_word_bounds (List.getElem_mem hi) hwords
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hf⟩ := gm06RotationSectorProg_exec work rows[i]
    p q r s₁ hw hbound.1 hbound.2 hnd hp hq hr hd₁
    ((hk₁.1 36 (by decide)).trans h36) ((hk₁.1 37 (by decide)).trans h37)
    ((hk₁.1 38 (by decide)).trans h38)
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, by omega, ?_, hf, ⟨?_, ?_⟩, ?_⟩
  · exact (hk₂.2 src (by simp)).trans hs₁
  · intro j hj
    have h1 : j ∉ [7, 8, 9, 11, 31] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj ⊢
      tauto
    have h2 : j ∉ [50, 40, 41, 42, 43] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj ⊢
      tauto
    exact (hk₂.1 j h2).trans (hk₁.1 j h1)
  · intro a ha'
    exact (hk₂.2 a (by simp)).trans (hk₁.2 a ha')
  · exact (hk₂.2 work (by simp)).trans hd₁

end GraphMinor.Compute
