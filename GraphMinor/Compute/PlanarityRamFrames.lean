module

public import GraphMinor.Compute.PlanarityRamPrefix

/-!
# The explicit DFS frame stack

Part I, Section 1 stores a vertex and its next adjacency index in each
frame. The arrays store the bottom frame first, while `searchFrames` uses
a top-first list. Pushing appends two words in fixed-capacity arrays.
Popping decreases the live length and does not copy the remaining frames.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- Any initial part of a represented prefix is represented in the same arena. -/
theorem PrefixAt.take {s : State} {a capacity : ℕ} {xs : List ℕ}
    (h : PrefixAt s a capacity xs) (k : ℕ) : PrefixAt s a capacity (xs.take k) := by
  obtain ⟨hlen, hle, htake⟩ := h
  refine ⟨hlen, by simp only [List.length_take]; omega, ?_⟩
  calc
    (s.arrs a).take (xs.take k).length = ((s.arrs a).take xs.length).take k := by
      simp [List.take_take]
    _ = xs.take k := congrArg (List.take k) htake

/-- Changing a frame column does not change the represented search. -/
theorem SearchAt.write_frame {N M : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (f : Field) (hf : f = .frameVertex ∨ f = .frameNext)
    (i value : ℕ) : SearchAt N M (s.writeArr f.array i value) search := by
  rcases hf with rfl | rfl <;>
    simpa [SearchAt, PrefixAt, State.writeArr, State.setArr, Field.array] using h

/-- A new frame is stored at the next free position of the stack. -/
def pushFrameProg : Cmd :=
  .seq (.write Field.frameVertex.array (.reg 38) (.reg 43))
    (.seq (.write Field.frameNext.array (.reg 38) (.const 0))
      (.assign 38 (.op .add (.reg 38) (.const 1))))

/-- Pop only the frame counter. The unused array slots need not be cleared. -/
def popFrameProg : Cmd := .assign 38 (.op .sub (.reg 38) (.const 1))

/-- Appending two words and advancing the live length represents a push. -/
theorem FramesAt.push {N : ℕ} {s : State} {stack : List Frame}
    (h : FramesAt N s stack) (hfree : stack.length < N) (v : ℕ) :
    FramesAt N
      (((s.writeArr Field.frameVertex.array stack.length v).writeArr
        Field.frameNext.array stack.length 0).setReg 38 (stack.length + 1))
      (⟨v, 0⟩ :: stack) := by
  obtain ⟨hc, hv, hn⟩ := h
  refine ⟨by simp, ?_, ?_⟩
  · have hh := (hv.write_end (by simpa using hfree) v).of_arr_eq
      (s' := ((s.writeArr Field.frameVertex.array stack.length v).writeArr
        Field.frameNext.array stack.length 0).setReg 38 (stack.length + 1))
      (by simp [Field.array])
    simpa using hh
  · have hh := (hn.of_arr_eq (s' := s.writeArr Field.frameVertex.array stack.length v)
      (by simp [Field.array])).write_end (by simpa using hfree) 0
    simpa [PrefixAt] using hh

/-- Popping a nonempty stack keeps the represented prefix of its two arrays. -/
theorem FramesAt.pop {N : ℕ} {s : State} {stack : List Frame} {f : Frame}
    (h : FramesAt N s (f :: stack)) : FramesAt N (s.setReg 38 stack.length) stack := by
  obtain ⟨hc, hv, hn⟩ := h
  refine ⟨by simp, ?_, ?_⟩
  · have hh := hv.take stack.length
    simpa [PrefixAt] using hh
  · have hh := hn.take stack.length
    simpa [PrefixAt] using hh

/-- A frame push takes ten steps and preserves the search representation. -/
theorem pushFrameProg_refines {N M w : ℕ} {s : State} {search : Search} {stack : List Frame}
    (h : FramesAt N s stack) (hsearch : SearchAt N M s search)
    (hfree : stack.length < N) (v : ℕ) (hr : s.regs 43 = v)
    (hcount : stack.length + 1 < 2 ^ w) (hv : v < 2 ^ w) :
    ∃ s', Exec w pushFrameProg s s' 10 ∧ FramesAt N s' (⟨v, 0⟩ :: stack) ∧
      SearchAt N M s' search := by
  let s1 := s.writeArr Field.frameVertex.array stack.length v
  let s2 := s1.writeArr Field.frameNext.array stack.length 0
  let s3 := s2.setReg 38 (stack.length + 1)
  have hiw : stack.length < 2 ^ w := by omega
  have hzero : 0 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hslotv' : stack.length < (s.arrs Field.frameVertex.array).length := by
    rw [h.2.1.1]
    exact hfree
  have hslotn' : stack.length < (s1.arrs Field.frameNext.array).length := by
    have heq : s1.arrs Field.frameNext.array = s.arrs Field.frameNext.array := by
      simp [s1, Field.array]
    rw [heq, h.2.2.1]
    exact hfree
  have hx1 : Exec w (.write Field.frameVertex.array (.reg 38) (.reg 43)) s s1 3 :=
    Exec.write (by simpa [Expr.eval, h.1] using checkWord_of_lt hiw)
      (by simpa [Expr.eval, hr] using checkWord_of_lt hv) hslotv'
  have hx2 : Exec w (.write Field.frameNext.array (.reg 38) (.const 0)) s1 s2 3 :=
    Exec.write (by simpa [Expr.eval, s1, h.1] using checkWord_of_lt hiw)
      (checkWord_of_lt hzero) hslotn'
  have hx3 : Exec w (.assign 38 (.op .add (.reg 38) (.const 1))) s2 s3 4 := by
    apply Exec.assign
    simp [Expr.eval, s2, s1, h.1, BinOp.eval, BinOp.raw,
      checkWord_of_lt hiw, checkWord_of_lt hone, checkWord_of_lt hcount]
  refine ⟨s3, Exec.seq hx1 (Exec.seq hx2 hx3), h.push hfree v, ?_⟩
  exact ((hsearch.write_frame .frameVertex (Or.inl rfl) stack.length v).write_frame
    .frameNext (Or.inr rfl) stack.length 0).setReg 38 _ (by decide) (by decide)

/-- A nonempty frame pop takes four steps and preserves the search. -/
theorem popFrameProg_refines {N M w : ℕ} {s : State} {search : Search}
    {stack : List Frame} {f : Frame} (h : FramesAt N s (f :: stack))
    (hsearch : SearchAt N M s search) (hcount : stack.length + 1 < 2 ^ w) :
    Exec w popFrameProg s (s.setReg 38 stack.length) 4 ∧
      FramesAt N (s.setReg 38 stack.length) stack ∧
      SearchAt N M (s.setReg 38 stack.length) search := by
  have hz : 1 < 2 ^ w := by omega
  have hc : s.regs 38 = stack.length + 1 := by simpa using h.1
  refine ⟨?_, h.pop, hsearch.setReg 38 _ (by decide) (by decide)⟩
  apply Exec.assign
  simp [Expr.eval, hc, BinOp.eval, BinOp.raw, checkWord_of_lt hcount,
    checkWord_of_lt hz, checkWord_of_lt (show stack.length < 2 ^ w by omega)]

end GraphMinor.Compute.PlanarityRam
