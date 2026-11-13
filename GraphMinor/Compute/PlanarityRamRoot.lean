module

public import GraphMinor.Compute.PlanarityRamSearchProg

/-!
# Starting one DFS component

A fresh root gets depth zero and one frame with next index zero. The root
program writes the depth tag and pushes the frame in constant time. The
proof preserves all search fields except the root depth.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- A write to the depth column leaves the frame arrays and live length fixed. -/
theorem FramesAt.write_depth {N : ℕ} {s : State} {stack : List Frame}
    (h : FramesAt N s stack) (i value : ℕ) :
    FramesAt N (s.writeArr Field.depth.array i value) stack := by
  simpa [FramesAt, PrefixAt, State.writeArr, State.setArr, Field.array] using h

/-- Starting a root takes fifteen steps. The stack is initially empty, the
root is in range and in register 40, and its label and the depth tag fit
in a word. The execution theorem itself does not require freshness. -/
theorem startRootProg_refines {N M w : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (hframes : FramesAt N s [])
    (root : ℕ) (hroot : root < N) (hr : s.regs 40 = root)
    (hw : 1 < 2 ^ w) (hrw : root < 2 ^ w) :
    ∃ s', Exec w startRootProg s s' 15 ∧ FramesAt N s' [⟨root, 0⟩] ∧
      SearchAt N M s' { search with depth := search.depth.set! root (some 0) } := by
  let s1 := s.setReg 43 root
  let s2 := s1.writeArr Field.depth.array root 1
  have h1 : SearchAt N M s1 search := h.setReg 43 root (by decide) (by decide)
  have h2 : SearchAt N M s2 { search with depth := search.depth.set! root (some 0) } :=
    h1.write_depth root (some 0)
  have hf : FramesAt N s2 [] := (hframes.setReg 43 root (by decide)).write_depth root 1
  have hslot : root < (s1.arrs Field.depth.array).length := by
    rw [h1.2.2.2.2.2.1.1]
    exact hroot
  have hx1 : Exec w (.assign 43 (.reg 40)) s s1 2 :=
    Exec.assign (by simpa [Expr.eval, hr] using checkWord_of_lt hrw)
  have hx2 : Exec w (.write Field.depth.array (.reg 40) (.const 1)) s1 s2 3 :=
    Exec.write (by simpa [Expr.eval, s1, hr] using checkWord_of_lt hrw)
      (checkWord_of_lt hw) hslot
  obtain ⟨s3, hx3, hf3, hs3⟩ := pushFrameProg_refines hf h2 (Nat.lt_of_le_of_lt (Nat.zero_le root) hroot)
    root (by simp [s2, s1]) (by simpa using hw) hrw
  exact ⟨s3, Exec.seq hx1 (Exec.seq hx2 hx3), hf3, hs3⟩

end GraphMinor.Compute.PlanarityRam
