module

public import GraphMinor.Compute.GM06Alg511BinarySearchInput
public import GraphMinor.Compute.GM06Alg511BuildKeys
public import GraphMinor.Compute.GM06Alg511LinkageEdges
import Mathlib.Tactic

/-!
# Preparing the ordinary graph workspace from binary input

After the initial checks, copy only the supplied ordinary endpoint
and outer-cuff rows, read the vertex count and compute the directed
edge keys used by the verified path-edge selector. The target and
turn integers remain in their binary input rows. In particular this
preparation does not run the earlier one-word winding loader.

The key values are bounded by the square of the graph vertex count.
This is a graph-size word bound, independent of all large integer
magnitudes. The program and its linear row cost prepare the stored
initial linkage phase of VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Prepare endpoint and outer-cuff rows, the vertex count and the
directed-edge key table from the supplied binary input fields. -/
def gm06Alg511BinaryGraphSetupProg : Cmd :=
  .seq (gm06Alg511CopyRowProg 1230 3)
    (.seq (gm06Alg511CopyRowProg 1211 1006)
      (.seq (.assign 41 (.read 1500 (.const 0))) gm06Alg511BuildKeysProg))

/-- Graph preparation retains all binary rows and every original
supplied field. It computes only graph-bounded directed-edge keys. -/
theorem gm06Alg511BinaryGraphSetupProg_exec {w : ℕ} (x : GM06Alg511BinaryInput)
    {α β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.toWindingInput.drawing.withLinkage []) G)
    (s : State) (hw : 2 < 2 ^ w) (hn : x.vertexCount < 2 ^ w)
    (hsquare : x.vertexCount * x.vertexCount < 2 ^ w)
    (hends : x.endpoints.length < 2 ^ w) (hcuff : x.outerCuff.length < 2 ^ w)
    (houterWords : ∀ v ∈ x.outerCuff, v < 2 ^ w)
    (htables : gm06Alg511BinaryLoadedTables x s) :
    ∃ t u, Exec w gm06Alg511BinaryGraphSetupProg s t u ∧
      u ≤ 30 + 37 * x.endpoints.length + 12 * x.outerCuff.length ∧
      Keeps [20, 41] [3, 1006, 1100] s t ∧
      t.arrs 3 = x.endpoints ∧ t.arrs 1006 = x.outerCuff ∧
      t.arrs 1100 = gm06Alg511DartKeys x.toWindingInput.drawing ∧ t.regs 41 = x.vertexCount := by
  have hE : s.arrs 1230 = x.endpoints := htables.1 ⟨1, by decide⟩
  have hO : s.arrs 1211 = x.outerCuff := htables.1 ⟨4, by decide⟩
  have hV : s.arrs 1500 = [x.vertexCount] := htables.1 ⟨0, by decide⟩
  have hEWords : ∀ v ∈ x.endpoints, v < 2 ^ w := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
    have hval : x.endpoints.getD i 0 = x.endpoints[i] := by simp [hi]
    have hh := gm06Alg511Endpoint_getD_lt x.toWindingInput.drawing rep i hi
    change x.endpoints.getD i 0 < x.vertexCount at hh
    exact (by simpa only [hval] using hh : x.endpoints[i] < x.vertexCount).trans hn
  obtain ⟨s₁, u₁, he₁, ht₁, hk₁, hends₁⟩ := gm06Alg511CopyRowProg_exec (w := w) 1230 3 (by decide)
    x.endpoints s (by omega) hends hEWords hE
  obtain ⟨s₂, u₂, he₂, ht₂, hk₂, hcuff₂⟩ := gm06Alg511CopyRowProg_exec (w := w) 1211 1006 (by decide)
    x.outerCuff s₁ (by omega) hcuff houterWords ((hk₁.2 1211 (by decide)).trans hO)
  have hV₂ : s₂.arrs 1500 = [x.vertexCount] :=
    (hk₂.2 1500 (by decide)).trans ((hk₁.2 1500 (by decide)).trans hV)
  let s₃ := s₂.setReg 41 x.vertexCount
  have he₃ : Exec w (.assign 41 (.read 1500 (.const 0))) s₂ s₃ 3 :=
    .assign ((Crossing.eval_read (a := 1500) (Crossing.eval_const (Nat.two_pow_pos w))
      (by rw [hV₂]; simp) (by simpa only [hV₂, List.getElem_cons_zero] using hn)).trans (by simp [hV₂]))
  obtain ⟨t, u₄, he₄, ht₄, hk₄, hkeys₄⟩ := gm06Alg511BuildKeysProg_exec x.toWindingInput.drawing rep s₃
    hw hends hn hsquare ((hk₂.2 3 (by decide)).trans hends₁) (by change s₃.regs 41 = x.vertexCount; simp [s₃])
  change u₄ ≤ 6 + 25 * x.endpoints.length at ht₄
  have hkeep₃ : Keeps [20, 41] [3, 1006, 1100] s s₃ :=
    ((hk₁.mono (by simp) (by simp)).trans hk₂ (by simp) (by simp)).setReg (by simp) _
  have hkeep : Keeps [20, 41] [3, 1006, 1100] s t := hkeep₃.trans hk₄ (by simp) (by simp)
  refine ⟨t, u₁ + (u₂ + (3 + u₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)), by omega, hkeep,
    (hk₄.2 3 (by decide)).trans ((hk₂.2 3 (by decide)).trans hends₁),
    (hk₄.2 1006 (by decide)).trans hcuff₂, hkeys₄, (hk₄.1 41 (by decide)).trans (by simp [s₃])⟩

/-- The setup also retains the full supplied table interpretation. -/
theorem gm06Alg511BinaryGraphSetupProg_tables {w u : ℕ} {x : GM06Alg511BinaryInput} {s t : State}
    (h : gm06Alg511BinaryLoadedTables x s) (he : Exec w gm06Alg511BinaryGraphSetupProg s t u) :
    gm06Alg511BinaryLoadedTables x t := by
  apply h.frame
  · intro i
    apply he.arrs_eq_of_not_mem_writtenArrs
    fin_cases i <;> decide
  · exact he.arrs_eq_of_not_mem_writtenArrs (by decide)
  · exact he.arrs_eq_of_not_mem_writtenArrs (by decide)

/-- Select the edge used at each raw-flow successor after preparing
its ordinary graph keys. All selections are computed from the input. -/
def gm06Alg511BinaryLinkageEdgesProg : Cmd :=
  .seq gm06Alg511BinaryGraphSetupProg gm06Alg511LinkageEdgesProg

/-- The actual binary-input preparation and edge selector retain
the full input tables and return exact ordinary directed edges for
every nonterminal successor in the verified raw flow system. -/
theorem gm06Alg511BinaryLinkageEdgesProg_exec {w : ℕ} (x : GM06Alg511BinaryInput)
    {α β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.toWindingInput.drawing.withLinkage []) G)
    (out : List ℕ)
    (hsys : IsValidPathSystem x.toWindingInput.drawing.flowGraph
      x.toWindingInput.drawing.flowInput.A x.toWindingInput.drawing.flowInput.B
      (decUsed x.vertexCount out) (decPred x.vertexCount out) (decSucc x.vertexCount out))
    (s : State) (hw : 2 < 2 ^ w) (hword : 1 + 3 * x.vertexCount < 2 ^ w)
    (hsquare : x.vertexCount * x.vertexCount < 2 ^ w)
    (hends : x.endpoints.length < 2 ^ w) (hcuff : x.outerCuff.length < 2 ^ w)
    (houterWords : ∀ v ∈ x.outerCuff, v < 2 ^ w)
    (hlen : out.length = 1 + 3 * x.vertexCount) (hout : s.arrs outArr = out)
    (htables : gm06Alg511BinaryLoadedTables x s) :
    ∃ t u, Exec w gm06Alg511BinaryLinkageEdgesProg s t u ∧
      u ≤ 36 + 37 * x.endpoints.length + 12 * x.outerCuff.length +
        x.vertexCount * (38 + 13 * x.endpoints.length) ∧
      Keeps [20, 41, 80, 43, 44, 48, 47] [3, 1006, 1100, 1300] s t ∧
      gm06Alg511BinaryLoadedTables x t ∧ t.regs 41 = x.vertexCount ∧
      t.arrs 1006 = x.outerCuff ∧ (t.arrs 1300).length = x.vertexCount ∧
      ∀ a : Fin x.vertexCount,
        let dart := (t.arrs 1300).getD a.val x.endpoints.length
        if decSucc x.vertexCount out a < x.vertexCount then
          dart < x.endpoints.length ∧ x.endpoints.getD dart 0 = a.val ∧
            x.endpoints.getD (gm06DartMate dart) 0 = decSucc x.vertexCount out a
        else dart = x.endpoints.length := by
  obtain ⟨s₁, u₁, he₁, ht₁, hk₁, _, houter₁, hkeys₁, hcount₁⟩ := gm06Alg511BinaryGraphSetupProg_exec x rep s hw
    (by omega) hsquare hends hcuff houterWords htables
  obtain ⟨t, u₂, he₂, ht₂, hk₂, hlen₂, hchoice₂⟩ := gm06Alg511LinkageEdgesProg_exec x.toWindingInput.drawing rep out hsys s₁
    (by omega) hword hsquare hends hlen ((hk₁.2 outArr (by decide)).trans hout) hkeys₁ hcount₁
  have hkeep : Keeps [20, 41, 80, 43, 44, 48, 47] [3, 1006, 1100, 1300] s t :=
    (hk₁.mono (by simp) (by simp)).trans hk₂ (by simp) (by simp)
  have hTables₁ := gm06Alg511BinaryGraphSetupProg_tables htables he₁
  have hTables₂ : gm06Alg511BinaryLoadedTables x t := hTables₁.frame
    (by intro i; apply hk₂.2; fin_cases i <;> decide) (hk₂.2 1000 (by decide)) (hk₂.2 1001 (by decide))
  change u₂ ≤ 6 + x.vertexCount * (38 + 13 * x.endpoints.length) at ht₂
  exact ⟨t, u₁ + u₂, .seq he₁ he₂, by omega, hkeep, hTables₂,
    (hk₂.1 41 (by decide)).trans hcount₁, (hk₂.2 1006 (by decide)).trans houter₁, hlen₂, hchoice₂⟩

end GraphMinor.Compute
