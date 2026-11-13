module

public import GraphMinor.Compute.GM06Alg511TraceProg
public import GraphMinor.Compute.GM06Alg511ReadChosenDarts
public import GraphMinor.Compute.GM06Alg511CopyRow
public import GraphMinor.Compute.GM06RestorePathWord
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Materializing an initial linkage path in successor format

VI (5.11), page 134, retains the linkage found by maximum flow.
Follow its computed successor words, read the already chosen edge
at each nonfinal vertex, and install that ordinary-dart row in the
successor path table. The program uses the supplied cuff order for
its source and makes no new edge selection. The pure output row
is defined directly from the flow and choice arrays. The execution
proof connects that row to the actual finite source path, including
its exact edge order, and preserves the other path rows.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Surface TwoPaths

/-- Ordinary directed words read from the stored choices along
the computed source trace, omitting the final vertex. -/
def gm06Alg511StoredPathRow (x : GM06Alg511Input) (out choices : List ℕ) (source : ℕ) : List ℕ :=
  let trace := gm06Alg511SuccVertices x.vertexCount out x.vertexCount source
  (trace.take (trace.length - 1)).map (fun v => choices.getD v x.endpoints.length)

/-- For a genuine flow source, the numeric materialized row is
exactly the chosen edge list of its actual finite source path. -/
theorem gm06Alg511StoredPathRow_eq_chosen (x : GM06Alg511Input) (out choices : List ℕ)
    (hsys : IsValidPathSystem x.flowGraph x.flowInput.A x.flowInput.B
      (decUsed x.vertexCount out) (decPred x.vertexCount out) (decSucc x.vertexCount out))
    (u : Fin x.vertexCount)
    (hu : u ∈ pathStarts (decUsed x.vertexCount out) (decPred x.vertexCount out)) :
    gm06Alg511StoredPathRow x out choices u.val =
      gm06Alg511ChosenDarts x choices (abWalkOfStart hsys u hu).walk.support := by
  have htrace : gm06Alg511SuccVertices x.vertexCount out x.vertexCount u.val =
      (abWalkOfStart hsys u hu).walk.support.map Fin.val :=
    gm06Alg511SuccVertices_eq_traceWalk out hsys _ u
  simp only [gm06Alg511StoredPathRow, htrace, gm06Alg511ChosenDarts,
    List.length_map, ← List.map_take, List.map_map, Function.comp_def]

/-- Every materialized source row fits in the graph's vertex bound,
and every word is one of the already supplied choice words. -/
theorem gm06Alg511StoredPathRow_bounds {w : ℕ} (x : GM06Alg511Input) (out choices : List ℕ)
    (hsys : IsValidPathSystem x.flowGraph x.flowInput.A x.flowInput.B
      (decUsed x.vertexCount out) (decPred x.vertexCount out) (decSucc x.vertexCount out))
    (u : Fin x.vertexCount)
    (hu : u ∈ pathStarts (decUsed x.vertexCount out) (decPred x.vertexCount out))
    (hchoiceLen : choices.length = x.vertexCount) (hchoiceWords : ∀ d ∈ choices, d < 2 ^ w) :
    (gm06Alg511StoredPathRow x out choices u.val).length ≤ x.vertexCount ∧
      ∀ d ∈ gm06Alg511StoredPathRow x out choices u.val, d < 2 ^ w := by
  have hlen := (gm06Alg511SuccVertices_nodup_length out hsys u hu).2
  constructor
  · simp only [gm06Alg511StoredPathRow, List.length_map, List.length_take]
    exact (min_le_right _ _).trans hlen
  · rw [gm06Alg511StoredPathRow_eq_chosen x out choices hsys u hu]
    intro d hd
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hd
    have hv : v.val < choices.length := hchoiceLen.symm ▸ v.isLt
    exact hchoiceWords _ (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv, Option.getD_some]
      exact List.getElem_mem hv)

/-- Materialize source row 1601 from cuff array 1210, then replace
that row of the ordinary path table in array 8. -/
def gm06Alg511StoreSourcePathProg : Cmd :=
  .seq (.assign 40 (.read 1210 (.reg 1601)))
    (.seq gm06Alg511TraceProg
      (.seq gm06Alg511ReadChosenDartsProg
        (.seq (gm06Alg511CopyRowProg 13 27)
          (.seq (.assign 31 (.reg 1601)) gm06ReplacePathRowProg))))

/-- One materialized source row is installed with its exact stored
edge choices. The remaining path rows, raw flow, source order and
choice table are preserved. Its bound includes the encoded-row write. -/
theorem gm06Alg511StoreSourcePathProg_exec {w : ℕ} (x : GM06Alg511Input)
    (out choices : List ℕ)
    (hsys : IsValidPathSystem x.flowGraph x.flowInput.A x.flowInput.B
      (decUsed x.vertexCount out) (decPred x.vertexCount out) (decSucc x.vertexCount out))
    (rows : List (List ℕ)) (i : ℕ) (hi : i < rows.length)
    (u : Fin x.vertexCount)
    (hu : u ∈ pathStarts (decUsed x.vertexCount out) (decPred x.vertexCount out))
    (s : State) (hw : 1 < 2 ^ w) (hword : 1 + 3 * x.vertexCount < 2 ^ w)
    (hchoiceLen : choices.length = x.vertexCount) (hchoiceWords : ∀ d ∈ choices, d < 2 ^ w)
    (hlen : out.length = 1 + 3 * x.vertexCount)
    (hout : s.arrs outArr = out) (hchoices : s.arrs 1300 = choices)
    (hN : s.regs 41 = x.vertexCount) (hindex : s.regs 1601 = i)
    (hsrc : i < (s.arrs 1210).length) (hsource : (s.arrs 1210)[i] = u.val)
    (h8 : s.arrs 8 = gm06EncodeRows rows)
    (hcode : (gm06EncodeRows rows).length < 2 ^ w)
    (hnewcode : (gm06EncodeRows (rows.set i (gm06Alg511StoredPathRow x out choices u.val))).length < 2 ^ w)
    (hwords : ∀ d ∈ gm06EncodeRows rows, d < 2 ^ w) :
    ∃ s' t, Exec w gm06Alg511StoreSourcePathProg s s' t ∧
      t ≤ 180 + 130 * x.vertexCount + 17 * i + 22 * rows[i].length + 80 * (gm06EncodeRows rows).length ∧
      Keeps [40, 42, 20, 31, 7, 4, 9, 11, 323, 324, 313, 98] [12, 13, 27, 25, 8, 28] s s' ∧
      s'.arrs 8 = gm06EncodeRows (rows.set i (gm06Alg511StoredPathRow x out choices u.val)) := by
  have hn : x.vertexCount < 2 ^ w := by omega
  have hcount : rows.length < 2 ^ w := hwords _ (by simp [gm06EncodeRows])
  have hiw := hi.trans hcount
  have hufit := u.isLt.trans hn
  have hread := Crossing.eval_read (Crossing.eval_reg hindex hiw) hsrc
    (hsource ▸ hufit)
  let s₀ := s.setReg 40 u.val
  have he₀ : Exec w (.assign 40 (.read 1210 (.reg 1601))) s s₀ 3 :=
    .assign (hread.trans (congrArg some hsource))
  obtain ⟨s₁, t₁, he₁, ht₁, hbuf, _, ha₁⟩ := gm06Alg511TraceProg_exec out hsys u hu s₀ hw hword hlen
    (by simpa [s₀] using hout) (by simp [s₀]) (by simpa [s₀] using hN)
  have htrace : gm06Alg511SuccVertices x.vertexCount out x.vertexCount u.val =
      (abWalkOfStart hsys u hu).walk.support.map Fin.val :=
    gm06Alg511SuccVertices_eq_traceWalk out hsys _ u
  rw [htrace] at hbuf
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, h13⟩ := gm06Alg511ReadChosenDartsProg_exec
    x choices (abWalkOfStart hsys u hu).walk.support s₁ hw hn hchoiceLen hchoiceWords
    ((ha₁ 1300 (by decide)).trans (by simpa [s₀] using hchoices)) hbuf
  let row := gm06Alg511StoredPathRow x out choices u.val
  have h13' : s₂.arrs 13 = row := h13.trans (gm06Alg511StoredPathRow_eq_chosen x out choices hsys u hu).symm
  obtain ⟨hrowlen, hrowwords⟩ := gm06Alg511StoredPathRow_bounds x out choices hsys u hu hchoiceLen hchoiceWords
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, h27⟩ := gm06Alg511CopyRowProg_exec 13 27 (by decide)
    row s₂ hw (hrowlen.trans_lt hn) hrowwords h13'
  let R := [40, 42, 20, 31, 7, 4, 9, 11, 323, 324, 313, 98]
  let A := [12, 13, 27, 25, 8, 28]
  have hk₀ : Keeps R A s s₀ := (Keeps.refl _ _ s).setReg (by simp [R]) _
  have hk₁ : Keeps R A s₀ s₁ := by
    constructor
    · intro r hr
      apply he₁.regs_eq_of_not_mem_writtenRegs
      intro hm
      have hsub : gm06Alg511TraceProg.writtenRegs ⊆ R.toFinset := by decide
      exact hr (List.mem_toFinset.mp (hsub hm))
    · intro a ha
      exact ha₁ a (by intro h; subst a; exact ha (by simp [A]))
  have hk₁' := hk₀.trans hk₁ (by simp [R]) (by simp [A])
  have hk₂' : Keeps R A s s₂ := hk₁'.trans hk₂ (by simp [R]) (by simp [A])
  have hk₃' : Keeps R A s s₃ := hk₂'.trans hk₃ (by simp [R]) (by simp [A])
  have hi₃ : s₃.regs 1601 = i := (hk₃'.1 1601 (by decide)).trans hindex
  let s₄ := s₃.setReg 31 i
  have he₄ : Exec w (.assign 31 (.reg 1601)) s₃ s₄ 2 := .assign (Crossing.eval_reg hi₃ hiw)
  have h8₃ : s₃.arrs 8 = gm06EncodeRows rows :=
    (hk₃.2 8 (by decide)).trans ((hk₂.2 8 (by decide)).trans
      ((ha₁ 8 (by decide)).trans (by simpa [s₀] using h8)))
  obtain ⟨s₅, t₅, he₅, ht₅, hk₅, h8', _⟩ := gm06ReplacePathRowProg_exec rows i hi row s₄
    hw hcode hnewcode hwords hrowwords
    (by simpa [s₄] using h8₃)
    (by simpa [s₄] using h27) (by simp [s₄])
  have hk₄ : Keeps R A s s₄ := hk₃'.setReg (by simp [R]) _
  have htraceLen : (abWalkOfStart hsys u hu).walk.support.length ≤ x.vertexCount :=
    by simpa only [List.length_map] using hbuf.2.2.1
  refine ⟨s₅, 3 + (t₁ + (t₂ + (t₃ + (2 + t₅)))),
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ he₅)))), ?_,
    hk₄.trans hk₅ (by simp [R]) (by simp [A]), h8'⟩
  dsimp only [row] at *
  omega

end GraphMinor.Compute
