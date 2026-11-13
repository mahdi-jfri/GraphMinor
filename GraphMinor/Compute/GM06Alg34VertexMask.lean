module

public import GraphMinor.Compute.GM06Alg34Singleton
public import GraphMinor.Compute.Basic
public import Mathlib.Data.List.FinRange

/-!
# Active vertices for singleton deletion

Keep vertex labels fixed while reductions remove vertices. An array of
zero-one entries records the active labels, and the current graph is
induced on them. Deleting a singleton vertex changes exactly its mask
entry to zero. This avoids relabelling surviving endpoints and keeps the
RAM update constant time. Region data are handled separately.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The zero-one array of active vertex labels. -/
def gm06VertexMask {n : ℕ} (vs : List (Fin n)) : List ℕ :=
  List.ofFn (fun a => if a ∈ vs then 1 else 0)

/-- Every vertex label has exactly one mask entry. -/
theorem gm06VertexMask_length {n : ℕ} (vs : List (Fin n)) :
    (gm06VertexMask vs).length = n := by simp [gm06VertexMask]

/-- Deleting a vertex is exactly one zero write in the active mask. -/
theorem gm06VertexMask_erase {n : ℕ} (vs : List (Fin n)) (v : Fin n) :
    gm06VertexMask (gm06EraseVertex vs v) = (gm06VertexMask vs).set v.val 0 := by
  apply List.ext_getElem (by simp [gm06VertexMask_length])
  intro i hi hi'
  rw [List.getElem_set hi']
  simp only [gm06VertexMask, List.getElem_ofFn]
  by_cases hv : v.val = i
  · simp [gm06EraseVertex, Fin.ext_iff, hv]
  · have hv' : i ≠ v.val := Ne.symm hv
    simp [gm06EraseVertex, Fin.ext_iff, hv, hv']

/-- Initially every supplied label is active, so the mask consists of ones. -/
theorem gm06VertexMask_all (n : ℕ) :
    gm06VertexMask (List.finRange n) = List.replicate n 1 := by
  simp only [gm06VertexMask, List.mem_finRange, ↓reduceIte, List.ofFn_const]

/-- The constant-time mask update for the selected singleton label in register 114. -/
def gm06DeleteVertexProg : Cmd := .write 4 (.reg 114) (.const 0)

/-- The RAM vertex deletion changes exactly the selected mask entry and
therefore represents the finite vertex-list update of (3.3)(i). -/
theorem gm06DeleteVertexProg_exec {w n : ℕ} (vs : List (Fin n)) (v : Fin n)
    (hn : n < 2 ^ w) {s : State} (hmask : s.arrs 4 = gm06VertexMask vs)
    (hlabel : s.regs 114 = v.val) :
    ∃ s', Exec w gm06DeleteVertexProg s s' 3 ∧
      s'.arrs 4 = gm06VertexMask (gm06EraseVertex vs v) ∧
      (∀ a : ℕ, a ≠ 4 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, s'.regs q = s.regs q) := by
  have hvw : v.val < 2 ^ w := v.isLt.trans hn
  have h0 : 0 < 2 ^ w := by omega
  have hvlen : v.val < (s.arrs 4).length := by rw [hmask, gm06VertexMask_length]; exact v.isLt
  let s' := s.writeArr 4 v.val 0
  have hex : Exec w gm06DeleteVertexProg s s' 3 :=
    .write (by simp [Expr.eval, checkWord, hlabel, hvw])
      (by simp [Expr.eval, checkWord, h0]) hvlen
  refine ⟨s', hex, ?_, ?_, fun _ => rfl⟩
  · rw [gm06VertexMask_erase]
    exact congrArg (fun xs => xs.set v.val 0) hmask
  · intro a ha
    exact State.writeArr_arrs_ne _ _ _ ha

end GraphMinor.Compute
