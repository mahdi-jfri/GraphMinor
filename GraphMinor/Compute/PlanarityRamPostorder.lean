module

public import GraphMinor.Compute.PlanarityRamFinish

/-!
# Appending vertex completions

The functional frame search prepends completed vertices and reverses that
list at the end. The RAM instead appends each completed vertex to an array.
`DfsSearchAt` relates these two orders during the search. Its final view is
already the postorder returned by `depthFirstSearch`.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- View a functional search with its completion list reversed. -/
def reversePostorder (search : Search) : Search :=
  { search with postorder := search.postorder.reverse }

/-- During DFS the array stores the reverse of the top-first completion list. -/
def DfsSearchAt (N M : ℕ) (s : State) (search : Search) : Prop :=
  SearchAt N M s (reversePostorder search)

/-- Creating a record commutes with the completion-list view. -/
theorem reversePostorder_addEdge (search : Search) (v u : ℕ) (tree : Bool) :
    reversePostorder (addEdge search v u tree).1 =
      (addEdge (reversePostorder search) v u tree).1 := by rfl

/-- Finishing a record commutes with the completion-list view. -/
theorem reversePostorder_finishEdge (search : Search) (i : ℕ) :
    reversePostorder (finishEdge search i) = finishEdge (reversePostorder search) i := by
  cases hpar : search.parentEdge[search.edges[i]!.source]?.join <;>
    simp [finishEdge_eq, reversePostorder, setEdgeKey, setEdgePair, finishedKey, hpar]

/-- Appending a completed vertex writes one word and advances the live count. -/
def appendPostorderProg : Cmd :=
  .seq (.write Field.postorder.array (.reg 39) (.reg 41))
    (.assign 39 (.op .add (.reg 39) (.const 1)))

/-- One append preserves all search data and extends its postorder prefix. -/
theorem SearchAt.append_postorder {N M : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (v : ℕ) (hfree : search.postorder.length < N) :
    SearchAt N M
      ((s.writeArr Field.postorder.array search.postorder.length v).setReg 39
        (search.postorder.length + 1))
      { search with postorder := search.postorder ++ [v] } := by
  obtain ⟨hd, hp, hpe, hc, hpost, hdepth, hparent, hparentEdge,
    htail, hhead, htree, hlow, hlow2, hkey, horder⟩ := h
  refine ⟨hd, hp, hpe, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hc
  · simp
  · exact hdepth.of_arr_eq (by simp [Field.array])
  · exact hparent.of_arr_eq (by simp [Field.array])
  · exact hparentEdge.of_arr_eq (by simp [Field.array])
  · exact htail.of_arr_eq (by simp [Field.array])
  · exact hhead.of_arr_eq (by simp [Field.array])
  · exact htree.of_arr_eq (by simp [Field.array])
  · exact hlow.of_arr_eq (by simp [Field.array])
  · exact hlow2.of_arr_eq (by simp [Field.array])
  · exact hkey.of_arr_eq (by simp [Field.array])
  · simpa [PrefixAt] using horder.write_end hfree v

/-- A seven-step RAM append represents prepending a functional completion.
The completion array must have a free slot and the value and next live
count must fit in a word. -/
theorem appendPostorderProg_refines {N M w : ℕ} {s : State} {search : Search}
    (h : DfsSearchAt N M s search) (v : ℕ) (hr : s.regs 41 = v)
    (hfree : search.postorder.length < N) (hv : v < 2 ^ w)
    (hc : search.postorder.length + 1 < 2 ^ w) :
    ∃ s', Exec w appendPostorderProg s s' 7 ∧
      DfsSearchAt N M s' { search with postorder := v :: search.postorder } := by
  have hcount : s.regs 39 = search.postorder.length := by
    simpa [reversePostorder] using h.2.2.2.2.1
  have hiw : search.postorder.length < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  let s1 := s.writeArr Field.postorder.array search.postorder.length v
  let s2 := s1.setReg 39 (search.postorder.length + 1)
  have hslot : search.postorder.length < (s.arrs Field.postorder.array).length := by
    rw [h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    exact hfree
  have hx1 : Exec w (.write Field.postorder.array (.reg 39) (.reg 41)) s s1 3 :=
    Exec.write (by simpa [Expr.eval, hcount] using checkWord_of_lt hiw)
      (by simpa [Expr.eval, hr] using checkWord_of_lt hv) hslot
  have hx2 : Exec w (.assign 39 (.op .add (.reg 39) (.const 1))) s1 s2 4 := by
    apply Exec.assign
    simp [Expr.eval, s1, hcount, BinOp.eval, BinOp.raw,
      checkWord_of_lt hiw, checkWord_of_lt hone, checkWord_of_lt hc]
  refine ⟨s2, Exec.seq hx1 hx2, ?_⟩
  have hout := h.append_postorder v (by simpa [reversePostorder] using hfree)
  simpa [DfsSearchAt, reversePostorder] using hout

end GraphMinor.Compute.PlanarityRam
