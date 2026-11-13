module

public import GraphMinor.Compute.GM06Alg511WindingFields
public import GraphMinor.Compute.GM06Alg511BuildKeys
public import GraphMinor.Compute.GM06Alg511LoadTurns
public import GraphMinor.Compute.GM06Alg511TraceTurns
import Mathlib.Tactic

/-!
# Preparing the winding phase from the retained drawing

For VI (5.11), page 134, load the ordinary graph fields, construct
the directed edge search keys and flatten the supplied signed turns.
The flow output is retained. The first source and all winding scratch
tables are computed from the original drawing words.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Load counts and cuffs, compute edge keys and read signed turns. -/
def gm06Alg511WindingSetupProg : Cmd :=
  .seq gm06Alg511WindingFieldsProg (.seq gm06Alg511BuildKeysProg gm06Alg511LoadTurnsProg)

/-- Prepare all winding data from the retained input, then compute
the first source path's signed turn and terminal cuff index. -/
def gm06Alg511InitialWindingProg : Cmd :=
  .seq gm06Alg511WindingSetupProg gm06Alg511WindingIndexProg

/-- The complete preparation of the winding phase uses only the
retained drawing words and preserves the maximum-flow output. -/
theorem gm06Alg511WindingSetupProg_exec {w : ℕ} (x : GM06Alg511WindingInput)
    {α β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.drawing.withLinkage []) G)
    (s : State) (hw : 3 < 2 ^ w) (hinner : x.drawing.innerCuff ≠ [])
    (ha : s.arrs 1000 = gm06Alg511WindingWords x)
    (hn : (gm06Alg511WindingWords x).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06Alg511WindingWords x, v < 2 ^ w)
    (hnfit : x.drawing.vertexCount < 2 ^ w)
    (hsquare : x.drawing.vertexCount * x.drawing.vertexCount < 2 ^ w) :
    ∃ s' t, Exec w gm06Alg511WindingSetupProg s s' t ∧
      t ≤ 610 + 88 * (gm06Alg511Words x.drawing).length +
        25 * x.drawing.endpoints.length + 116 * x.edgeTurns.length ∧
      s'.arrs 1100 = gm06Alg511DartKeys x.drawing ∧
      s'.arrs 11 = gm06Alg511TurnWords x.edgeTurns ∧ s'.arrs 1006 = x.drawing.outerCuff ∧
      s'.arrs 1004 = x.drawing.innerCuff ∧ s'.arrs 3 = x.drawing.endpoints ∧
      s'.regs 41 = x.drawing.vertexCount ∧ s'.regs 40 = x.drawing.innerCuff.getD 0 0 ∧
      s'.regs 52 = x.drawing.pathCount ∧ s'.regs 53 = 0 ∧
      ∀ a, a ∉ [1002, 1007, 1004, 1006, 1008, 3, 1100, 1005, 11] → s'.arrs a = s.arrs a := by
  obtain ⟨s₁, t₁, he₁, ht₁, hends, houter, hinnerRow, hN, hsource, hk, hi, harr₁⟩ :=
    gm06Alg511WindingFieldsProg_exec x s (by omega) hinner ha hn hwords
  have hbaselen : (gm06Alg511Words x.drawing).length ≤ (gm06Alg511WindingWords x).length :=
    gm06Alg511_encoded_row_length_le (by simp)
  have hendslen : x.drawing.endpoints.length ≤ (gm06Alg511Words x.drawing).length :=
    gm06Alg511_encoded_row_length_le (rows := gm06Alg511Rows x.drawing) (by simp [gm06Alg511Rows])
  have hefit : x.drawing.endpoints.length < 2 ^ w :=
    (hendslen.trans hbaselen).trans_lt hn
  obtain ⟨s₂, t₂, he₂, ht₂, hkeep₂, hkeys⟩ := gm06Alg511BuildKeysProg_exec x.drawing rep s₁
    (by omega) hefit hnfit hsquare hends hN
  have hinput₂ : s₂.arrs 1000 = gm06Alg511WindingWords x :=
    (hkeep₂.2 1000 (by decide)).trans ((harr₁ 1000 (by decide)).trans ha)
  obtain ⟨s₃, t₃, he₃, ht₃, hturns, harr₃⟩ :=
    gm06Alg511LoadTurnsProg_exec x s₂ hw hinput₂ hn hwords
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq he₁ (.seq he₂ he₃), by omega,
    (harr₃ 1100 (by decide) (by decide)).trans hkeys, hturns,
    (harr₃ 1006 (by decide) (by decide)).trans ((hkeep₂.2 1006 (by decide)).trans houter),
    (harr₃ 1004 (by decide) (by decide)).trans ((hkeep₂.2 1004 (by decide)).trans hinnerRow),
    (harr₃ 3 (by decide) (by decide)).trans ((hkeep₂.2 3 (by decide)).trans hends),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact (he₃.regs_eq_of_not_mem_writtenRegs (by decide)).trans ((hkeep₂.1 41 (by decide)).trans hN)
  · exact (he₃.regs_eq_of_not_mem_writtenRegs (by decide)).trans ((hkeep₂.1 40 (by decide)).trans hsource)
  · exact (he₃.regs_eq_of_not_mem_writtenRegs (by decide)).trans ((hkeep₂.1 52 (by decide)).trans hk)
  · exact (he₃.regs_eq_of_not_mem_writtenRegs (by decide)).trans ((hkeep₂.1 53 (by decide)).trans hi)
  · intro a ha'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha'
    obtain ⟨ha2, ha7, ha4, ha6, ha8, ha3, hak, hat, haw⟩ := ha'
    rw [harr₃ a hat haw, hkeep₂.2 a (by simpa using hak)]
    apply harr₁ a
    simp [ha2, ha7, ha4, ha6, ha8, ha3]

end GraphMinor.Compute
