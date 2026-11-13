module

public import GraphMinor.Compute.Case3StepsPlaceholderDataProg
public import GraphMinor.Compute.Case3StepsSerializeRecordProg

/-!
# Serializing a noninterior member record

The placeholder sections are serialized in the same original-label format
as the interior branch records. The one-vertex tree and zero leaf list
satisfy the record parser's size conditions for every member edge count.
The serialization has linear vertex, pair, and full-copy cost.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Write all sections and serialize one prescribed noninterior record. -/
def case3WritePlaceholderRecordProg : Cmd :=
  .seq case3PlaceholderRecordDataProg case3SerializeRecordProg

/-- Noninterior record writing preserves the scan inputs and counters,
with the same linear record-size bound as the interior writer. -/
theorem case3WritePlaceholderRecordProg_exec {w n N : ℕ} (G : MultiDigraph n)
    (orig : Fin n → Fin N) (hinj : Function.Injective orig)
    (hw : 3 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * G.numActivePairs < 2 ^ w) (hsize : n + 6 * G.numEdges + 4 < 2 ^ w)
    {s : State} (hG : s.arrs 38 = G.enc)
    (hlabels : s.arrs 47 = List.ofFn (fun u : Fin n => (orig u).1)) :
    ∃ s' t, Exec w case3WritePlaceholderRecordProg s s' t ∧
      t ≤ 1200 * (n + G.numEdges + G.numActivePairs + 1) ∧
      let r := case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj)
        (case3PlaceholderCode G.numEdges)
      s'.arrs 51 = r.enc ∧ r.enc.length ≤ n + 6 * G.numEdges + 4 ∧
      (∀ z ∈ s'.arrs 51, z < 2 ^ w) ∧
      (∀ a, a ≠ 48 → a ≠ 49 → a ≠ 50 → a ≠ 51 → a ≠ 52 → a ≠ 53 → s'.arrs a = s.arrs a) ∧
      (∀ r < 101, s'.regs r = s.regs r) := by
  let code := case3PlaceholderCode G.numEdges
  let r := case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code
  have he : G.numEdges < 2 ^ w := by omega
  have hlen : r.enc.length ≤ n + 6 * G.numEdges + 4 := by
    have hlen := case3BranchRecord_placeholder_length G (origVertexEmb orig hinj) (origEdgeEmb orig hinj)
    change r.enc.length = n + 4 * G.numEdges + 4 at hlen
    omega
  have hwords : ∀ z ∈ r.enc, z < 2 ^ w :=
    case3BranchRecord_enc_words_lt G orig hinj code (by omega) hn hN he (case3PlaceholderCode_words he)
  obtain ⟨s₁, t₁, hex₁, ht₁, hv₁, he₁, hp₁, htau₁, htree₁, hm₁, harr₁, hreg₁⟩ :=
    case3PlaceholderRecordDataProg_exec G orig hinj hw hn hN hA (by omega) hG hlabels
  have hshape := case3BranchRecord_lengths G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code
  have hfields := case3BranchRecord_placeholder_fields G (origVertexEmb orig hinj) (origEdgeEmb orig hinj)
  have hm : r.eList.length = G.numEdges := by simp only [r, case3BranchRecord, List.length_map, G.length_multiEdgeTriples]
  have hv : r.vList.length = n := by simp only [r, case3BranchRecord, List.length_map, List.length_finRange]
  have htree : r.t_len ≤ 2 * r.eList.length + 1 := by
    have htone : r.t_len = 1 := hfields.1
    rw [htone, hm]
    omega
  obtain ⟨s₂, t₂, hex₂, ht₂, hout, harr₂, hreg₂⟩ := case3SerializeRecordProg_exec r
    hshape.1 hshape.2 htree (by omega) (by omega) hwords hv₁ he₁ hp₁ htau₁ htree₁ (by rw [hm]; exact hm₁)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, hout, hlen, ?_, ?_, ?_⟩
  · rw [hv, hm] at ht₂
    omega
  · rw [hout]
    exact hwords
  · intro a h48 h49 h50 h51 h52 h53
    exact (harr₂ a h51 h52 h53).trans (harr₁ a h48 h49 h50)
  · intro q hq
    exact (hreg₂ q hq).trans (hreg₁ q (by romega))

end GraphMinor.Compute
