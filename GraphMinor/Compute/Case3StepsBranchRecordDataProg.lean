module

public import GraphMinor.Compute.Case3StepsBranchTreeProg
public import GraphMinor.Compute.Case3StepsExpandedEdgesProg
import Mathlib.Data.List.FinRange

/-!
# Computing all sections of a branch member record

The original vertex list is retained, the returned branch code supplies the
tree sections, and the saved compact graph supplies the expanded edge list.
Their exact correspondence proves that the resulting arrays are the data
of one `Case3MemberRecord`, in linear edge time after vertex renaming.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- The original vertex list used by the record is its ordered inverse list. -/
theorem case3BranchRecord_orig_vList {n N : ℕ} (G : MultiDigraph n)
    (orig : Fin n → Fin N) (hinj : Function.Injective orig) (code : List ℕ) :
    (case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code).vList =
      List.ofFn (fun u : Fin n => (orig u).1) := by
  simp only [case3BranchRecord, origVertexEmb_apply_val]
  exact List.ofFn_eq_map.symm

/-- Compute the tree sections and expanded edge list of a branch record. -/
def case3BranchRecordDataProg : Cmd := .seq case3BranchTreeProg case3ExpandedEdgesProg

/-- The retained inverse list and computed arrays are exactly the four
lists of the renamed branch record, with its normalized tree size. -/
theorem case3BranchRecordDataProg_exec {w n N B : ℕ} (G : MultiDigraph n)
    (orig : Fin n → Fin N) (hinj : Function.Injective orig) (code : List ℕ)
    (hcode : IsValidBranchDecompCode B G code) (hw : 3 < 2 ^ w)
    (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * G.numActivePairs < 2 ^ w) (he : 3 * G.numEdges + 1 < 2 ^ w)
    (hlen : (0 :: code).length < 2 ^ w) (hwords : ∀ x ∈ code, x < 2 ^ w)
    {s : State} (hcodearr : s.arrs 129 = 0 :: code) (hG : s.arrs 38 = G.enc)
    (hlabels : s.arrs 47 = List.ofFn (fun u : Fin n => (orig u).1)) :
    ∃ s' t, Exec w case3BranchRecordDataProg s s' t ∧
      t ≤ 83 * G.numEdges + 41 * G.numActivePairs + 52 ∧
      let r := case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code
      s'.arrs 47 = r.vList ∧ s'.arrs 50 = encEdgeTriples r.eList ∧
      s'.arrs 48 = r.parList ∧ s'.arrs 49 = r.tauList ∧
      s'.regs 102 = r.t_len ∧ s'.regs 111 = G.numEdges ∧
      (∀ a, a ≠ 48 → a ≠ 49 → a ≠ 50 → s'.arrs a = s.arrs a) ∧
      (∀ r < 102, s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hpar₁, htau₁, htree₁, hm₁, harr₁, hreg₁⟩ :=
    case3BranchTreeProg_exec G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code
      hcode hw hlen hwords hcodearr
  obtain ⟨s₂, t₂, hex₂, ht₂, hedges₂, harr₂, hreg₂⟩ :=
    case3ExpandedEdgesProg_exec G orig hinj hw hn hN hA he
      ((harr₁ 38 (by decide) (by decide)).trans hG)
      ((harr₁ 47 (by decide) (by decide)).trans hlabels) hm₁
  have hex : Exec w case3BranchRecordDataProg s s₂ (t₁ + t₂) := .seq hex₁ hex₂
  refine ⟨s₂, t₁ + t₂, hex, by omega, ?_, hedges₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [harr₂ 47 (by decide), harr₁ 47 (by decide) (by decide), hlabels,
      case3BranchRecord_orig_vList G orig hinj code]
  · exact (harr₂ 48 (by decide)).trans hpar₁
  · exact (harr₂ 49 (by decide)).trans htau₁
  · exact (hreg₂ 102 (by decide)).trans htree₁
  · rw [hex₂.regs_eq_of_not_mem_writtenRegs (by
      simp [case3ExpandedEdgesProg, forUp, case3ExpandPairProg, case3ReadMappedPairProg,
        readTripleEndpoints, case3ExpandCopiesProg, case3WriteCopyProg, Cmd.writtenRegs])]
    exact hm₁
  · intro a h48 h49 h50
    exact (harr₂ a h50).trans (harr₁ a h48 h49)
  · intro r hr
    rw [hreg₂ r (by dsimp only [Reg] at *; omega), hreg₁ r hr]

end GraphMinor.Compute
