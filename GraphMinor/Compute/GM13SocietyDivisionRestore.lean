module

public import GraphMinor.Compute.GM13SocietyDivisionCall
public import GraphMinor.Compute.GM13SocietyDivisionRead
public import GraphMinor.Compute.GM13SocietyRuralOwners
public import GraphMinor.Compute.GM13SocietyCorrectness

/-!
# The complete rural-division restoration stage

The simple program's explicit merged records are read in order. The RAM
writes the loop-owner table, and the reader restores all original parallel
classes and the assigned loops. Rurality follows from the simple division
and the proved edge lift. The member-count bound makes the restoration
linear in the Section 8 size of the original multigraph.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph GM13

/-- Recover the vertex count from the original input and restore the division. -/
def gm13DivisionRestoreProg : Cmd :=
  .seq (.assign 0 (.read 0 (.const 0))) gm13RuralOwnersProg

/-- The full restoration runs in O(vε) time. The absence of a cross is the
local result of the caller's cross test, not an extra input to (8.6). -/
theorem gm13DivisionRestoreProg_computes :
    ComputesRelInTime GM13SocietyInput.size
      (fun x s => GM13SimpleDivisionData x.simple (s.arrs 65) ∧
        ¬ GM13.HasCross x.society ∧ s.arrs 0 = x.enc)
      GM13ActualRuralOutput gm13DivisionRestoreProg (fun s => s) := by
  refine ⟨1000, 4, by decide, by decide, ?_⟩
  intro x s hin
  dsimp only
  obtain ⟨Z, C, edges, htrace, h4, he, hcode⟩ := hin.1
  let m := (edgeListOf x.simple.G).length
  let raw := alg86RawPairList x.simple.G Z x.simple.omega.toFinset (edgeListOf x.simple.G)
  let div := alg86DivPairList x.simple.G Z x.simple.omega.toFinset (edgeListOf x.simple.G)
  let padding := List.replicate
    (12 * alg81Size x.simple - (gm13DivisionPrefix x.simple Z edges).length) 0
  have hsize : x.G.numEdges + x.n + 1 ≤ x.size :=
    (Nat.one_mul _).symm.trans_le
      (Nat.mul_le_mul_right _ (show 1 ≤ x.n + 1 by omega))
  have hm : m ≤ x.G.numEdges := card_edgeFinset_toSimpleGraph_le_numEdges x.G
  have hsq : x.n * x.n ≤ x.size :=
    Nat.mul_le_mul (show x.n ≤ x.n + 1 by omega) (by omega)
  have hnm : x.n * m ≤ x.size :=
    Nat.mul_le_mul (show x.n ≤ x.n + 1 by omega) (by omega)
  have hpref : (gm13DivisionPrefix x.simple Z edges).length ≤ 12 * x.size :=
    (gm13DivisionPrefix_length_le x.simple Z edges he).trans
      (Nat.mul_le_mul_left 12 x.simple_size_le)
  have hraw : raw.length ≤ m + 2 * x.n :=
    (length_encAlg86PairList_raw_le x.simple.G Z x.simple.omega.toFinset (edgeListOf x.simple.G)).2
  have hdiv : div.length ≤ m + 2 * x.n :=
    (length_encAlg86PairList_div_le x.simple.G Z x.simple.omega.toFinset (edgeListOf x.simple.G)).2
  have hw := gm13_section8_word_bound x.size (by omega)
  have h0 : 0 < 2 ^ wordSize 4 x.size := by omega
  have hn : x.n < 2 ^ wordSize 4 x.size := by omega
  have hget : (s.arrs 0)[0]? = some x.n := by
    obtain ⟨hi, hv⟩ := enc_getElem_zero x.G (x.omega.length :: x.omega.map Fin.val) hin.2.2
    exact List.getElem?_eq_some_iff.mpr ⟨hi, hv⟩
  let s₁ := s.setReg 0 x.n
  have he₁ : Exec (wordSize 4 x.size) (.assign 0 (.read 0 (.const 0))) s s₁ 3 :=
    .assign (gm13_read_eval (Crossing.eval_const h0) hget hn)
  have hcode' : s₁.arrs 65 = [0] ++ encAlg86Subgraph Z edges ++
      encAlg86PairList raw ++ encAlg86PairList div ++ padding := hcode
  obtain ⟨s₂, t₂, he₂, ht₂, howners, ha₂⟩ := gm13RuralOwnersProg_exec
    (w := wordSize 4 x.size) (s := s₁) (Z, edges) raw div padding
    (show (gm13DivisionPrefix x.simple Z edges).length < 2 ^ wordSize 4 x.size by omega)
    hn (by omega) (by omega) (by omega) hcode' (by change s₁.regs 0 = x.n; simp [s₁])
  change t₂ ≤ 24 * raw.length + x.n * (32 * div.length + 20) + 48 at ht₂
  have htprod : x.n * (32 * div.length + 20) ≤
      32 * (x.n * m) + 64 * (x.n * x.n) + 20 * x.n := by
    calc x.n * (32 * div.length + 20) ≤ x.n * (32 * (m + 2 * x.n) + 20) :=
        Nat.mul_le_mul_left x.n (by omega)
      _ = _ := by ring
  have hno : ¬ HasCrossInSociety x.simple.G x.simple.omega := by
    intro hc
    exact hin.2.1 (x.hasCross_iff.mp ((hasCrossInSociety_iff_hasCross x.simple).mp hc))
  have hR := isRuralDivision_image_alg86Division x.simple htrace h4 hno
  have hfamily : gm13RecordFamily x.G div = alg86Division x.simple Z :=
    setOf_mem_map_alg86DivPairList x.simple htrace h4
  rw [← hfamily] at hR
  have hlift := gm13RecordedDivision_isRural x.G x.omega x.nodup_omega div hR
  refine ⟨s₂, 3 + t₂, .seq he₁ he₂, by omega, ?_⟩
  unfold GM13ActualRuralOutput
  rw [ha₂ 65 (by decide), hcode', howners]
  have hread := gm13ReadSimpleMembers_code x (Z, edges) raw div padding
  have heq := (congrArg (fun members => gm13ReadRecordedDivision x.G members
    (gm13LoopOwnerTable div)) hread).trans
      (gm13ReadRecordedDivision_map x.G div (gm13LoopOwnerTable div))
  exact heq.symm ▸ hlift

/-- The division call and restoration, when the cross test has returned no,
form one uniform O(vε) RAM computation from the original plain input. -/
theorem gm13SocietyRuralProgram :
    ∃ P : Cmd, ComputesRelInTime GM13SocietyInput.size
      (fun x s => s.arrs 0 = x.enc ∧ ¬ GM13.HasCross x.society)
      GM13ActualRuralOutput P (fun s => s) := by
  obtain ⟨C, c, hC, hc, hrun⟩ := gm13SocietyDivisionCall
  have hcall : ComputesRelInTime GM13SocietyInput.size
      (fun x s => s.arrs 0 = x.enc ∧ ¬ GM13.HasCross x.society)
      (fun x s => GM13SimpleDivisionData x.simple (s.arrs 65) ∧
        ¬ GM13.HasCross x.society ∧ s.arrs 0 = x.enc)
      (gm13SocietyRunProg alg86DivisionsProg) (fun s => s) := by
    refine ⟨C, c, hC, hc, ?_⟩
    intro x s hin
    obtain ⟨s', t, hex, ht, hd, ho⟩ := hrun x s hin.1
    exact ⟨s', t, hex, ht, hd, hin.2, ho⟩
  have hseq := hcall.seq_same gm13DivisionRestoreProg_computes
    (T := fun s => 2 * s) (fun _ => by omega)
  exact ⟨.seq (gm13SocietyRunProg alg86DivisionsProg) gm13DivisionRestoreProg,
    hseq.mono_time (K := 2) (by decide) (fun _ => le_rfl)⟩

end GraphMinor.Compute
