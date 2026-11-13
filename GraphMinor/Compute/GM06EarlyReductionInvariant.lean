module

public import GraphMinor.Compute.GM06EarlyReductionProgram
public import GraphMinor.GM06.Alg57CurrentUndo
public import GraphMinor.GM06.Alg57ReductionMeasure

/-!
# The chronological invariant through the early RAM branches

For Lemmas 18 and 19 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`)
the actual early driver extends both the mathematical reduction
history and the inverse history. Its new reference linkage has the
original winding, and its next-feasibility question is equivalent
to the original one. The literal array-9 writes encode exactly the
extended inverse history. The actual mask measure strictly falls.

If all early scans fail, the zero-bit invariant forces bit one.
This is the situation in which the loop calls the Reduction 4 phase.
All history hypotheses here concern the already reached state;
no future reduction or phase-correctness assertion is assumed.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- The concrete early driver preserves the chronological loop
invariant and decreases the actual RAM measure on every success.
A failed driver returns bit one and excludes the three early types. -/
theorem gm06EarlyReductionsProg_invariant
    {w k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder} {θ : ℝ}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hvinj : Function.Injective rep.vertex)
    (X : Alg57DrawingState k) (hX : IsCylinderSection5Drawing k X.drawing)
    (hx : X.bit = true) (hθX : X.linkage.HasTheta θ)
    (b : Bool) {d r : ℕ} (run : Alg57ReductionRun X ⟨G, L, b⟩ d r)
    (original : GM06UndoState x.vertexCount) (records : List (Option (ℕ × ℕ)))
    (trace : GM06UndoTrace x.vertexCount k original rep.undoState records)
    (tail : List ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsquare : x.vertexCount * x.vertexCount < 2 ^ w)
    (hcap : 4 * (1 + x.vertexCount + 2 * rep.tagged.length + 4 * k) < 2 ^ w)
    (hbits : ∀ p ∈ rep.tagged, p.2 ≤ 1)
    (hhist : (gm06ContractionHistoryWords (records.filterMap id) ++ tail).length < 2 ^ w)
    (hroom : 2 * (records.filterMap id).length + 1 <
      (gm06ContractionHistoryWords (records.filterMap id) ++ tail).length)
    (h2 : s.arrs 2 = [x.vertexCount]) (h3 : s.arrs 3 = x.endpoints)
    (h4 : s.arrs 4 = gm06EncodeRows x.rotations) (h6 : s.arrs 6 = x.innerCuff)
    (h7 : s.arrs 7 = x.outerCuff) (h8 : s.arrs 8 = gm06EncodeRows x.linkage)
    (h9 : s.arrs 9 = gm06ContractionHistoryWords (records.filterMap id) ++ tail)
    (h12 : s.arrs 12 = rep.tagged.map Prod.snd) (h14 : s.arrs 14 = gm02VertexBits rep.live)
    (h309 : s.regs 309 = (records.filterMap id).length) (h329 : s.regs 329 = b.toNat) :
    ∃ sf t, Exec w gm06EarlyReductionsProg s sf t ∧
      t ≤ gm06EarlyReductionsCost x.vertexCount rep.tagged.length k
        (gm06EncodeRows x.rotations).length (gm06EncodeRows x.linkage).length x.linkage.flatten.length ∧
      (∀ a ∈ [2, 6, 7], sf.arrs a = s.arrs a) ∧ sf.regs 900 = s.regs 900 ∧
      ((sf.regs 901 = 0 ∧ sf.regs 329 = 1 ∧ b = true ∧
          sf.regs 309 = (records.filterMap id).length ∧
          (∀ a ∈ [3, 4, 8, 9, 12, 14], sf.arrs a = s.arrs a) ∧
          ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage k H),
            ¬ Section5Reduction1Step k G L H M ∧
            ¬ Section5Reduction2Step k G L H M ∧
            ¬ Section5Reduction3Step k G L H M) ∨
       ∃ (ends : List ℕ) (rots paths : List (List ℕ))
         (H : Drawing ClosedCylinder) (M : CylinderLinkage k H)
         (cur : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := paths} H M)
         (record : Option (ℕ × ℕ)) (newTail : List ℕ),
         sf.regs 901 ∈ [1, 2, 3] ∧ sf.regs 329 = 1 ∧
         sf.arrs 3 = ends ∧ sf.arrs 4 = gm06EncodeRows rots ∧ sf.arrs 8 = gm06EncodeRows paths ∧
         sf.arrs 12 = cur.tagged.map Prod.snd ∧ sf.arrs 14 = gm02VertexBits cur.live ∧
         Function.Injective cur.vertex ∧ cur.tagged.length = rep.tagged.length ∧
         (∀ p ∈ cur.tagged, p.2 ≤ 1) ∧ IsCylinderSection5Drawing k H ∧
         Alg57ReductionRun X ⟨H, M, true⟩ (d + 1) r ∧
         GM06UndoTrace x.vertexCount k original cur.undoState (records ++ [record]) ∧
         M.HasTheta θ ∧
         (IsThetaFeasible k H (θ + 1 / (k : ℝ)) ↔
           IsThetaFeasible k X.drawing (θ + 1 / (k : ℝ))) ∧
         gm06LoopMeasure sf < gm06LoopMeasure s ∧
         sf.regs 309 = ((records ++ [record]).filterMap id).length ∧
         sf.arrs 9 = gm06ContractionHistoryWords ((records ++ [record]).filterMap id) ++ newTail ∧
         (sf.arrs 9).length = (s.arrs 9).length) := by
  obtain ⟨hG, hθ, _⟩ := run.invariant hX hθX
  obtain ⟨sf, t, he, ht, hfields, hcounter, hout⟩ := gm06EarlyReductionsProg_exec rep hvinj hG hθ b
    (gm06ContractionHistoryWords (records.filterMap id) ++ tail) (records.filterMap id).length s
    hw hsquare hcap hbits hhist hroom h2 h3 h4 h6 h7 h8 h9 h12 h14 h309
  refine ⟨sf, t, he, ht, hfields, hcounter, ?_⟩
  rcases hout with ⟨hflag, hbit, hcount, hsame, hno⟩ |
      ⟨ends, rots, paths, H, M, cur, record, hflag, hbit, h3', h4', h8', h12', h14',
        hinj, hlen, hbits', hH, step, undo, hcount, hhistory⟩
  · have hb : b = true := run.bit_eq_true_of_no_early hX hx hno
    exact Or.inl ⟨hflag, by simpa only [h329, hb, Bool.toNat_true] using hbit, hb, hcount, hsame, hno⟩
  · have run' := run.snoc_shrink step
    have trace' := trace.snoc undo
    obtain ⟨_, hθ', hfeas⟩ := run'.invariant hX hθX
    obtain ⟨newTail, hwords, _⟩ := gm06UndoHistoryWords_snoc records tail record hroom
    have hhistory' : sf.arrs 9 = gm06ContractionHistoryWords ((records ++ [record]).filterMap id) ++ newTail :=
      hhistory.trans hwords
    have hcount' : sf.regs 309 = ((records ++ [record]).filterMap id).length := by
      rw [hcount]
      cases record <;> simp
    have hsize : (sf.arrs 9).length = (s.arrs 9).length := by
      rw [h9, hhistory]
      cases record with
      | none => rfl
      | some p => simp only [List.length_set]
    have hmeasure : gm06LoopMeasure sf < gm06LoopMeasure s := by
      rw [cur.ram_measure_eq sf true h12' h14' hbit, rep.ram_measure_eq s b h12 h14 h329]
      exact step.measure_lt
    exact Or.inr ⟨ends, rots, paths, H, M, cur, record, newTail, hflag, hbit, h3', h4', h8', h12', h14',
      hinj, hlen, hbits', hH, run', trace', hθ', hfeas, hmeasure, hcount', hhistory', hsize⟩

end GraphMinor.Compute
