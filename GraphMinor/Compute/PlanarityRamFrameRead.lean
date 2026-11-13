module

public import GraphMinor.Compute.PlanarityRamFrames

/-!
# Reading and advancing the top DFS frame

The frame loop reads the vertex and next-adjacency index in its last live
array slot. Advancing that index changes one word. These commands do not
move any lower frame or any search record.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- Read a live prefix through an expression whose index has been evaluated. -/
theorem PrefixAt.read_expr_eval {s : State} {a capacity w i : ℕ} {xs : List ℕ}
    (h : PrefixAt s a capacity xs) (hi : i < xs.length) (index : Expr)
    (hindex : index.eval w s = some i) (hval : xs[i] < 2 ^ w) :
    (Expr.read a index).eval w s = some xs[i] := by
  have hb := h.index_lt hi
  have he : (s.arrs a)[i] = xs[i] := by
    have hh := h.getElem? hi
    simpa only [List.getElem?_eq_getElem hb, List.getElem?_eq_getElem hi,
      Option.some.injEq] using hh
  rw [Expr.eval, hindex]
  simpa only [hb, ↓reduceDIte, he] using checkWord_of_lt hval

/-- Array index of the last live frame. -/
def topFrameIndex : Expr := .op .sub (.reg 38) (.const 1)

/-- Load the top vertex and next index into registers 41 and 42. -/
def loadFrameProg : Cmd :=
  .seq (.assign 41 (.read Field.frameVertex.array topFrameIndex))
    (.assign 42 (.read Field.frameNext.array topFrameIndex))

/-- Advance the already-loaded next index in register 42. -/
def advanceFrameProg : Cmd :=
  .write Field.frameNext.array topFrameIndex (.op .add (.reg 42) (.const 1))

/-- Top-frame indexing is valid when the nonzero stack length fits in a word. -/
theorem topFrameIndex_eval {N w : ℕ} {s : State} {stack : List Frame} {f : Frame}
    (h : FramesAt N s (f :: stack)) (hc : stack.length + 1 < 2 ^ w) :
    topFrameIndex.eval w s = some stack.length := by
  have hcount : s.regs 38 = stack.length + 1 := by simpa using h.1
  have hone : 1 < 2 ^ w := by omega
  have hi : stack.length < 2 ^ w := by omega
  simp [topFrameIndex, Expr.eval, hcount, BinOp.eval, BinOp.raw,
    checkWord_of_lt hc, checkWord_of_lt hone, checkWord_of_lt hi]

/-- Changing scratch registers 41 and 42 leaves the frame representation fixed. -/
theorem FramesAt.setReg {N : ℕ} {s : State} {stack : List Frame}
    (h : FramesAt N s stack) (r value : ℕ) (hr : r ≠ 38) :
    FramesAt N (s.setReg r value) stack := by
  simpa only [FramesAt, PrefixAt, State.setReg_arrs,
    State.setReg_regs_ne s value (Ne.symm hr)] using h

/-- Loading the top frame takes ten steps and preserves both representations. -/
theorem loadFrameProg_refines {N M w : ℕ} {s : State} {search : Search}
    {stack : List Frame} {f : Frame} (h : FramesAt N s (f :: stack))
    (hs : SearchAt N M s search) (hc : stack.length + 1 < 2 ^ w)
    (hv : f.vertex < 2 ^ w) (hn : f.next < 2 ^ w) :
    ∃ s', Exec w loadFrameProg s s' 10 ∧ FramesAt N s' (f :: stack) ∧
      SearchAt N M s' search ∧ s'.regs 41 = f.vertex ∧ s'.regs 42 = f.next := by
  let s1 := s.setReg 41 f.vertex
  let s2 := s1.setReg 42 f.next
  have h1 : FramesAt N s1 (f :: stack) := h.setReg 41 _ (by decide)
  have hvindex : stack.length < ((f :: stack).reverse.map Frame.vertex).length := by simp
  have hnindex : stack.length < ((f :: stack).reverse.map Frame.next).length := by simp
  have hvread := h.2.1.read_expr_eval hvindex topFrameIndex (topFrameIndex_eval h hc)
    (by simpa using hv)
  have hnread := h1.2.2.read_expr_eval hnindex topFrameIndex (topFrameIndex_eval h1 hc)
    (by simpa using hn)
  have hx1 : Exec w (.assign 41 (.read Field.frameVertex.array topFrameIndex)) s s1 5 := by
    apply Exec.assign
    simpa using hvread
  have hx2 : Exec w (.assign 42 (.read Field.frameNext.array topFrameIndex)) s1 s2 5 := by
    apply Exec.assign
    simpa using hnread
  refine ⟨s2, Exec.seq hx1 hx2, h1.setReg 42 _ (by decide),
    (hs.setReg 41 _ (by decide) (by decide)).setReg 42 _ (by decide) (by decide), ?_, ?_⟩
  · simp [s2, s1]
  · simp [s2]

/-- A single next-index write represents advancing the top frame. -/
theorem FramesAt.advance {N : ℕ} {s : State} {stack : List Frame} {f : Frame}
    (h : FramesAt N s (f :: stack)) :
    FramesAt N (s.writeArr Field.frameNext.array stack.length (f.next + 1))
      ({ f with next := f.next + 1 } :: stack) := by
  obtain ⟨hc, hv, hn⟩ := h
  refine ⟨hc, ?_, ?_⟩
  · simpa using hv.of_arr_eq (s' := s.writeArr Field.frameNext.array stack.length (f.next + 1))
      (by simp [Field.array])
  · have hh := hn.write_existing stack.length (f.next + 1)
    simpa using hh

/-- Advancing a loaded top frame takes seven steps. -/
theorem advanceFrameProg_refines {N M w : ℕ} {s : State} {search : Search}
    {stack : List Frame} {f : Frame} (h : FramesAt N s (f :: stack))
    (hs : SearchAt N M s search) (hr : s.regs 42 = f.next)
    (hc : stack.length + 1 < 2 ^ w) (hn : f.next + 1 < 2 ^ w) :
    ∃ s', Exec w advanceFrameProg s s' 7 ∧
      FramesAt N s' ({ f with next := f.next + 1 } :: stack) ∧ SearchAt N M s' search := by
  have hone : 1 < 2 ^ w := by omega
  have hn' : f.next < 2 ^ w := by omega
  have hslot : stack.length < (s.arrs Field.frameNext.array).length :=
    h.2.2.index_lt (by simp)
  let s1 := s.writeArr Field.frameNext.array stack.length (f.next + 1)
  have hx : Exec w advanceFrameProg s s1 7 := by
    apply Exec.write (topFrameIndex_eval h hc)
    · simp [Expr.eval, hr, BinOp.eval, BinOp.raw, checkWord_of_lt hn',
        checkWord_of_lt hone, checkWord_of_lt hn]
    · exact hslot
  exact ⟨s1, hx, h.advance, hs.write_frame .frameNext (Or.inr rfl) _ _⟩

end GraphMinor.Compute.PlanarityRam
