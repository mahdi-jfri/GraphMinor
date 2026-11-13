module

public import GraphMinor.Compute.PlanarityRamPrefix

/-!
# Creating oriented records in search memory

Part I, Section 1 creates one record in six parallel arrays. Writing the
next free slot in each array preserves the other search data and extends
all six live prefixes. This file proves the representation update without
changing any array length.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- Store an edge in the six search columns without allocating. -/
def writeEdgeState (s : State) (i : ℕ) (e : EdgeRecord) : State :=
  ((((((s.writeArr Field.tail.array i (e.source)).writeArr Field.head.array i (e.target)).writeArr Field.tree.array i (e.tree.toNat)).writeArr Field.low.array i (e.pair.low)).writeArr Field.low2.array i (e.pair.second)).writeArr Field.key.array i (e.key))

/-- Each edge-column update is a single write. Other fields are preserved. -/
theorem writeEdgeState_arrs (s : State) (i : ℕ) (e : EdgeRecord) (f : Field) :
    (writeEdgeState s i e).arrs f.array =
      match f with
      | .tail => (s.arrs f.array).set i (e.source)
      | .head => (s.arrs f.array).set i (e.target)
      | .tree => (s.arrs f.array).set i (e.tree.toNat)
      | .low => (s.arrs f.array).set i (e.pair.low)
      | .low2 => (s.arrs f.array).set i (e.pair.second)
      | .key => (s.arrs f.array).set i (e.key)
      | _ => s.arrs f.array := by
  cases f <;> simp [writeEdgeState, State.writeArr, State.setArr, Field.array]

/-- Writing edge columns preserves all registers. -/
theorem writeEdgeState_regs (s : State) (i : ℕ) (e : EdgeRecord) :
    (writeEdgeState s i e).regs = s.regs := by rfl

/-- Creating one oriented record extends exactly the functional edge array.
The hypothesis asks for a free slot, not for a precomputed refinement step. -/
theorem SearchAt.push {N M : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (hfree : search.edges.size < M) (e : EdgeRecord) :
    SearchAt N M
      ((writeEdgeState s search.edges.size e).setReg 37 (search.edges.size + 1))
      { search with edges := search.edges.push e } := by
  obtain ⟨hd, hp, hpe, hc, hpost, hdepth, hparent, hparentEdge,
    htail, hhead, htree, hlow, hlow2, hkey, horder⟩ := h
  refine ⟨hd, hp, hpe, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simpa [writeEdgeState_regs] using hpost
  · exact hdepth.of_arr_eq (by simp [writeEdgeState_arrs])
  · exact hparent.of_arr_eq (by simp [writeEdgeState_arrs])
  · exact hparentEdge.of_arr_eq (by simp [writeEdgeState_arrs])
  · have hw := htail.write_end (by simpa using hfree) (e.source)
    simpa only [PrefixAt, State.setReg_arrs, writeEdgeState_arrs,
      State.writeArr_arrs_self, Array.toList_push, List.map_append,
      List.map_cons, List.map_nil, List.length_map, Array.length_toList] using hw
  · have hw := hhead.write_end (by simpa using hfree) (e.target)
    simpa only [PrefixAt, State.setReg_arrs, writeEdgeState_arrs,
      State.writeArr_arrs_self, Array.toList_push, List.map_append,
      List.map_cons, List.map_nil, List.length_map, Array.length_toList] using hw
  · have hw := htree.write_end (by simpa using hfree) (e.tree.toNat)
    simpa only [PrefixAt, State.setReg_arrs, writeEdgeState_arrs,
      State.writeArr_arrs_self, Array.toList_push, List.map_append,
      List.map_cons, List.map_nil, List.length_map, Array.length_toList] using hw
  · have hw := hlow.write_end (by simpa using hfree) (e.pair.low)
    simpa only [PrefixAt, State.setReg_arrs, writeEdgeState_arrs,
      State.writeArr_arrs_self, Array.toList_push, List.map_append,
      List.map_cons, List.map_nil, List.length_map, Array.length_toList] using hw
  · have hw := hlow2.write_end (by simpa using hfree) (e.pair.second)
    simpa only [PrefixAt, State.setReg_arrs, writeEdgeState_arrs,
      State.writeArr_arrs_self, Array.toList_push, List.map_append,
      List.map_cons, List.map_nil, List.length_map, Array.length_toList] using hw
  · have hw := hkey.write_end (by simpa using hfree) (e.key)
    simpa only [PrefixAt, State.setReg_arrs, writeEdgeState_arrs,
      State.writeArr_arrs_self, Array.toList_push, List.map_append,
      List.map_cons, List.map_nil, List.length_map, Array.length_toList] using hw
  · exact horder.of_arr_eq (by simp [writeEdgeState_arrs])

/-- Store the prepared record and advance its live counter. The fields are
in registers 41 (tail), 43 (head), 44 (tree flag), 47 (low), and 48 (low2).
New records start with key zero, as in `addEdge`. -/
def storeEdgeProg : Cmd :=
  (.seq (.write Field.tail.array (.reg 37) (.reg 41)) (.seq (.write Field.head.array (.reg 37) (.reg 43)) (.seq (.write Field.tree.array (.reg 37) (.reg 44)) (.seq (.write Field.low.array (.reg 37) (.reg 47)) (.seq (.write Field.low2.array (.reg 37) (.reg 48)) (.seq (.write Field.key.array (.reg 37) (.const 0)) (.assign 37 (.op .add (.reg 37) (.const 1)))))))))

/-- A prepared record is stored in twenty-two steps. The hypotheses give
only the input words, available slots, and word bounds for this local call. -/
theorem storeEdgeProg_exec (s : State) (e : EdgeRecord) (i w : ℕ)
    (hi : s.regs 37 = i) (hsource : s.regs 41 = e.source)
    (htarget : s.regs 43 = e.target) (htree : s.regs 44 = e.tree.toNat)
    (hlow : s.regs 47 = e.pair.low) (hlow2 : s.regs 48 = e.pair.second)
    (hkey : e.key = 0) (hiw : i + 1 < 2 ^ w)
    (hsourcew : e.source < 2 ^ w) (htargetw : e.target < 2 ^ w)
    (hloww : e.pair.low < 2 ^ w) (hlow2w : e.pair.second < 2 ^ w)
    (htailSlot : i < (s.arrs Field.tail.array).length)
    (hheadSlot : i < (s.arrs Field.head.array).length)
    (htreeSlot : i < (s.arrs Field.tree.array).length)
    (hlowSlot : i < (s.arrs Field.low.array).length)
    (hlow2Slot : i < (s.arrs Field.low2.array).length)
    (hkeySlot : i < (s.arrs Field.key.array).length) :
    Exec w storeEdgeProg s ((writeEdgeState s i e).setReg 37 (i + 1)) 22 := by
  have hiw' : i < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hzero : 0 < 2 ^ w := by omega
  have htreew : e.tree.toNat < 2 ^ w := by cases e.tree <;> simp_all
  let s1 := s.writeArr Field.tail.array i (e.source)
  have hx1 : Exec w (.write Field.tail.array (.reg 37) (.reg 41)) s s1 3 := by
    apply Exec.write
    · simp [Expr.eval, hi, checkWord_of_lt hiw']
    · simp [Expr.eval, hsource, checkWord_of_lt hsourcew]
    · simpa [State.writeArr, State.setArr, Field.array] using htailSlot
  let s2 := s1.writeArr Field.head.array i (e.target)
  have hx2 : Exec w (.write Field.head.array (.reg 37) (.reg 43)) s1 s2 3 := by
    apply Exec.write
    · simp [s1, Expr.eval, hi, State.writeArr, State.setArr, checkWord_of_lt hiw']
    · simp [s1, Expr.eval, State.writeArr, State.setArr, htarget, checkWord_of_lt htargetw]
    · simpa [s1, State.writeArr, State.setArr, Field.array] using hheadSlot
  let s3 := s2.writeArr Field.tree.array i (e.tree.toNat)
  have hx3 : Exec w (.write Field.tree.array (.reg 37) (.reg 44)) s2 s3 3 := by
    apply Exec.write
    · simp [s1, s2, Expr.eval, hi, State.writeArr, State.setArr, checkWord_of_lt hiw']
    · simp [s1, s2, Expr.eval, State.writeArr, State.setArr, htree, checkWord_of_lt htreew]
    · simpa [s1, s2, State.writeArr, State.setArr, Field.array] using htreeSlot
  let s4 := s3.writeArr Field.low.array i (e.pair.low)
  have hx4 : Exec w (.write Field.low.array (.reg 37) (.reg 47)) s3 s4 3 := by
    apply Exec.write
    · simp [s1, s2, s3, Expr.eval, hi, State.writeArr, State.setArr, checkWord_of_lt hiw']
    · simp [s1, s2, s3, Expr.eval, State.writeArr, State.setArr, hlow, checkWord_of_lt hloww]
    · simpa [s1, s2, s3, State.writeArr, State.setArr, Field.array] using hlowSlot
  let s5 := s4.writeArr Field.low2.array i (e.pair.second)
  have hx5 : Exec w (.write Field.low2.array (.reg 37) (.reg 48)) s4 s5 3 := by
    apply Exec.write
    · simp [s1, s2, s3, s4, Expr.eval, hi, State.writeArr, State.setArr, checkWord_of_lt hiw']
    · simp [s1, s2, s3, s4, Expr.eval, State.writeArr, State.setArr, hlow2, checkWord_of_lt hlow2w]
    · simpa [s1, s2, s3, s4, State.writeArr, State.setArr, Field.array] using hlow2Slot
  let s6 := s5.writeArr Field.key.array i (e.key)
  have hx6 : Exec w (.write Field.key.array (.reg 37) (.const 0)) s5 s6 3 := by
    apply Exec.write
    · simp [s1, s2, s3, s4, s5, Expr.eval, hi, State.writeArr, State.setArr, checkWord_of_lt hiw']
    · simp [Expr.eval, hkey, checkWord_of_lt hzero]
    · simpa [s1, s2, s3, s4, s5, State.writeArr, State.setArr, Field.array] using hkeySlot
  have hinc : Exec w (.assign 37 (.op .add (.reg 37) (.const 1))) s6
      (s6.setReg 37 (i + 1)) 4 := by
    apply Exec.assign
    simp [s1, s2, s3, s4, s5, s6, Expr.eval, hi, State.writeArr, State.setArr,
      checkWord_of_lt hiw', checkWord_of_lt hone, BinOp.eval, BinOp.raw, checkWord_of_lt hiw]
  exact (Exec.seq hx1 (Exec.seq hx2 (Exec.seq hx3 (Exec.seq hx4 (Exec.seq hx5 (Exec.seq hx6 hinc))))))

/-- The constant-time store extends a represented search by its prepared
record. This is the storage part of `addEdge`; computing the prepared
lowpoint words is a separate operation. -/
theorem storeEdgeProg_refines {N M w : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (hfree : search.edges.size < M) (e : EdgeRecord)
    (hsource : s.regs 41 = e.source) (htarget : s.regs 43 = e.target)
    (htree : s.regs 44 = e.tree.toNat) (hlow : s.regs 47 = e.pair.low)
    (hlow2 : s.regs 48 = e.pair.second) (hkey : e.key = 0)
    (hiw : search.edges.size + 1 < 2 ^ w)
    (hsourcew : e.source < 2 ^ w) (htargetw : e.target < 2 ^ w)
    (hloww : e.pair.low < 2 ^ w) (hlow2w : e.pair.second < 2 ^ w) :
    ∃ s', Exec w storeEdgeProg s s' 22 ∧
      SearchAt N M s' { search with edges := search.edges.push e } := by
  have hrep := h.push hfree e
  obtain ⟨_, _, _, hc, _, _, _, _, htail, hhead, htr, hlo, hlo2, hk, _⟩ := h
  refine ⟨_, storeEdgeProg_exec s e search.edges.size w hc hsource htarget htree hlow hlow2
    hkey hiw hsourcew htargetw hloww hlow2w ?_ ?_ ?_ ?_ ?_ ?_, hrep⟩
  · rw [htail.1]; exact hfree
  · rw [hhead.1]; exact hfree
  · rw [htr.1]; exact hfree
  · rw [hlo.1]; exact hfree
  · rw [hlo2.1]; exact hfree
  · rw [hk.1]; exact hfree

end GraphMinor.Compute.PlanarityRam
