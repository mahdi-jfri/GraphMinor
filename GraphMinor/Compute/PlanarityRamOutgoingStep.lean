module

public import GraphMinor.Compute.PlanarityRamOutgoingProg

/-!
# Reading a source header and appending one edge

The command reads the edge's source and the two outgoing header words,
then performs the constant-size append. All word and slot bounds follow
from the search and outgoing-chain representations. Freshness is the
ownership condition discharged by the global traversal invariant.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- The two header words address only allocated edge-link slots. A
nonempty chain has a positive last pointer. -/
theorem OutgoingReadyAt.header_bounds {N M : ℕ} {s : State} {outgoing : Array (List ℕ)}
    (h : OutgoingReadyAt N M s outgoing) {v p q : ℕ} (hv : v < N)
    (hp : (s.arrs Field.outgoingFirst.array)[v]? = some p)
    (hq : (s.arrs Field.outgoingLast.array)[v]? = some q) :
    p ≤ M ∧ q ≤ M ∧ (p ≠ 0 → 0 < q) := by
  obtain ⟨first, hfirst, hlast, hc, hnd⟩ := h.2.2.2.2 v hv
  have hpf : first = p := Option.some.inj (hfirst.symm.trans hp)
  subst first
  have hqval : q = optionWord outgoing[v]!.head? := Option.some.inj (hq.symm.trans hlast)
  have hpb : p ≤ M := hc.pointer_le (by
    intro i hi
    have hb := hc.member_slot hi
    rwa [h.2.2.2.1] at hb)
  refine ⟨hpb, ?_, ?_⟩
  · cases hxs : outgoing[v]! with
    | nil => simp [hqval, hxs, optionWord]
    | cons last rest =>
      have hmem : last ∈ outgoing[v]!.reverse := by simp [hxs]
      have hb := hc.member_slot hmem
      rw [h.2.2.2.1] at hb
      simpa [hqval, hxs, optionWord] using Nat.succ_le_of_lt hb
  · intro hpnonzero
    cases hxs : outgoing[v]! with
    | nil => exact False.elim (hpnonzero (hc.null_iff.mpr (by simp [hxs])))
    | cons last rest => simp [hqval, hxs, optionWord]

/-- Read the source and both header words before the pointer writes. -/
def appendOutgoingProg : Cmd :=
  .seq (.assign 52 (.read Field.tail.array (.reg 51)))
    (.seq (.assign 53 (.read Field.outgoingFirst.array (.reg 52)))
      (.seq (.assign 54 (.read Field.outgoingLast.array (.reg 52))) appendOutgoingLinksProg))

/-- One complete outgoing append refines functional source prepending in
at most twenty-five steps. The assumptions are current search/list data,
a valid fresh edge in register 51, source ownership, and word capacity. -/
theorem appendOutgoingProg_refines {N M w : ℕ} {s : State} {search : Search}
    {outgoing : Array (List ℕ)} {i : ℕ}
    (hs : SearchAt N M s search) (hb : SearchBounded N search)
    (ho : OutgoingReadyAt N M s outgoing) (howned : SourceOwned search.edges outgoing)
    (hi : i < search.edges.size) (hiM : i < M) (hr : s.regs 51 = i)
    (hfresh : ∀ v < N, i ∉ outgoing[v]!)
    (hw : 2 * (N + M + 1) < 2 ^ w) :
    ∃ s' t, Exec w appendOutgoingProg s s' t ∧ t ≤ 25 ∧
      SearchAt N M s' search ∧ OutgoingReadyAt N M s' (prependSource search.edges outgoing i) := by
  let v := search.edges[i]!.source
  have hv : v < N := (hb.2.2.2.2.2.2 i hi).1
  have hvi : search.edges[i].source = v := by simp only [v, getElem!_pos search.edges i hi]
  have hvw : v < 2 ^ w := by omega
  have hiw : i < 2 ^ w := by omega
  obtain ⟨p, hp, hq, hc, hnd⟩ := ho.2.2.2.2 v hv
  let q := optionWord outgoing[v]!.head?
  obtain ⟨hpM, hqM, hqpos⟩ := ho.header_bounds hv hp hq
  have hpw : p < 2 ^ w := by omega
  have hqw : q < 2 ^ w := by dsimp only [q]; omega
  let s1 := s.setReg 52 v
  let s2 := s1.setReg 53 p
  let s3 := s2.setReg 54 q
  have hx1 : Exec w (.assign 52 (.read Field.tail.array (.reg 51))) s s1 3 := by
    apply Exec.assign
    simpa only [hvi] using hs.read_tail hi hr hiw (hvi.symm ▸ hvw)
  have hx2 : Exec w (.assign 53 (.read Field.outgoingFirst.array (.reg 52))) s1 s2 3 :=
    Exec.assign (read_reg_of_getElem? hp (by simp [s1]) hvw hpw)
  have hx3 : Exec w (.assign 54 (.read Field.outgoingLast.array (.reg 52))) s2 s3 3 :=
    Exec.assign (read_reg_of_getElem? hq (by simp [s2, s1]) hvw hqw)
  have ho3 : OutgoingReadyAt N M s3 outgoing := ((ho.setReg 52 v).setReg 53 p).setReg 54 q
  obtain ⟨t, hx4, ht⟩ := appendOutgoingLinksProg_exec s3 i v p q hiM hv hpM hqM hqpos
    (by simpa [s3, s2, s1] using hr) (by simp [s3, s2, s1]) (by simp [s3, s2])
    (by simp [s3]) ho3.2.1 ho3.2.2.1 ho3.2.2.2.1 hw
  let s4 := appendOutgoingState s3 v i p q
  have hout : OutgoingReadyAt N M s4 (prependSource search.edges outgoing i) :=
    ho3.prepend howned hiM hv hfresh hp hq
  refine ⟨s4, 3 + (3 + (3 + t)), Exec.seq hx1 (Exec.seq hx2 (Exec.seq hx3 hx4)), by omega, ?_, hout⟩
  apply hs.of_memory_eq
  · unfold s4 appendOutgoingState
    split <;> simp [s3, s2, s1]
  · unfold s4 appendOutgoingState
    split <;> simp [s3, s2, s1]
  · intro a ha
    have h47 : a ≠ Field.outgoingFirst.array := Nat.ne_of_lt (Nat.lt_of_lt_of_le ha (by decide))
    have h48 : a ≠ Field.outgoingLast.array := Nat.ne_of_lt (Nat.lt_of_lt_of_le ha (by decide))
    have h49 : a ≠ Field.outgoingNext.array := Nat.ne_of_lt (Nat.lt_of_lt_of_le ha (by decide))
    unfold s4 appendOutgoingState
    split <;> simp [s3, s2, s1, h47, h48, h49]

end GraphMinor.Compute.PlanarityRam
