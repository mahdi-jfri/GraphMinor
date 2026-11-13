module

public import GraphMinor.Compute.Case3StepsBranchRecordWords
public import GraphMinor.Compute.Case3StepsSerializeRecordProg

/-!
# Writing the branch result of one member call

The supplied branch code is converted to the exact original-label record
and serialized. Count preservation, code validity, and checked code words
supply every size and word bound needed by the writing program. This is
the branch-output part of XIII (9.9), step 6, pp. 105–106.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Compute and serialize one original-label branch member record. -/
def case3WriteBranchRecordProg : Cmd := .seq case3BranchRecordDataProg case3SerializeRecordProg

/-- A valid returned branch code writes its exact member record with
linear vertex and edge work and bounded output words. -/
theorem case3WriteBranchRecordProg_exec {w n N B : ℕ} (G : MultiDigraph n)
    (orig : Fin n → Fin N) (hinj : Function.Injective orig) (code : List ℕ)
    (hcode : IsValidBranchDecompCode B G code) (hw : 3 < 2 ^ w)
    (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * G.numActivePairs < 2 ^ w) (hsize : n + 6 * G.numEdges + 4 < 2 ^ w)
    (hlen : (0 :: code).length < 2 ^ w) (hwords : ∀ x ∈ code, x < 2 ^ w)
    {s : State} (hcodearr : s.arrs 129 = 0 :: code) (hG : s.arrs 38 = G.enc)
    (hlabels : s.arrs 47 = List.ofFn (fun u : Fin n => (orig u).1)) :
    ∃ s' t, Exec w case3WriteBranchRecordProg s s' t ∧
      t ≤ 1200 * (n + G.numEdges + G.numActivePairs + 1) ∧
      let r := case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code
      s'.arrs 51 = r.enc ∧ r.enc.length ≤ n + 6 * G.numEdges + 4 ∧
      (∀ x ∈ s'.arrs 51, x < 2 ^ w) ∧
      (∀ a, a ≠ 48 → a ≠ 49 → a ≠ 50 → a ≠ 51 → a ≠ 52 → a ≠ 53 → s'.arrs a = s.arrs a) ∧
      (∀ r < 101, s'.regs r = s.regs r) := by
  let r := case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code
  have hrlen : r.enc.length ≤ n + 6 * G.numEdges + 4 := case3BranchRecord_enc_length_le G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code hcode
  have hrwords : ∀ x ∈ r.enc, x < 2 ^ w :=
    case3BranchRecord_enc_words_lt G orig hinj code (by omega) hn hN (by omega) hwords
  obtain ⟨s₁, t₁, hex₁, ht₁, hv₁, he₁, hp₁, htau₁, htree₁, hm₁, harr₁, hreg₁⟩ :=
    case3BranchRecordDataProg_exec G orig hinj code hcode hw hn hN hA (by omega) hlen hwords hcodearr hG hlabels
  have hshape : r.parList.length = r.t_len ∧ r.tauList.length = r.eList.length := case3BranchRecord_lengths G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code
  have htree : r.t_len ≤ 2 * r.eList.length + 1 := (case3BranchRecord_tree_bounds G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code hcode).2.1
  have hm : r.eList.length = G.numEdges := by simp only [r, case3BranchRecord, List.length_map, G.length_multiEdgeTriples]
  have hvlen : r.vList.length = n := by simp only [r, case3BranchRecord, List.length_map, List.length_finRange]
  have hr111 : s₁.regs 111 = r.eList.length := by
    rw [hm]
    exact hm₁
  obtain ⟨s₂, t₂, hex₂, ht₂, hrec₂, harr₂, hreg₂⟩ := case3SerializeRecordProg_exec r hshape.1 hshape.2 htree
    (by omega) (by omega) hrwords hv₁ he₁ hp₁ htau₁ htree₁ hr111
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, hrec₂, hrlen, ?_, ?_, ?_⟩
  · rw [hvlen, hm] at ht₂
    omega
  · rw [hrec₂]
    exact hrwords
  · intro a h48 h49 h50 h51 h52 h53
    exact (harr₂ a h51 h52 h53).trans (harr₁ a h48 h49 h50)
  · intro r hr
    rw [hreg₂ r hr, hreg₁ r (by romega)]

end GraphMinor.Compute
