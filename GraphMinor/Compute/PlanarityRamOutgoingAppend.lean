module

public import GraphMinor.Compute.PlanarityRamOutgoing

/-!
# Updating an outgoing list through its two header words

One append clears the new edge's next word, updates either the first
header or the old tail's link, and writes the new tail header. Source
ownership ensures the old tail cannot belong to another vertex's list.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- The append writes, with the old first and last pointer words supplied. -/
def appendOutgoingState (s : State) (v i first last : ℕ) : State :=
  let cleared := s.writeArr Field.outgoingNext.array i 0
  let linked := if first = 0 then cleared.writeArr Field.outgoingFirst.array v (i + 1)
    else cleared.writeArr Field.outgoingNext.array (last - 1) (i + 1)
  linked.writeArr Field.outgoingLast.array v (i + 1)

/-- A chain has a null pointer exactly when its represented list is empty. -/
theorem EdgeChain.null_iff {s : State} {a p : ℕ} {xs : List ℕ}
    (h : EdgeChain s a p xs) : p = 0 ↔ xs = [] := by
  cases h with
  | nil => simp
  | cons hn ht => simp

/-- Appending to one source list preserves all outgoing chains. The
hypotheses give the current representation and source ownership, a valid
new edge, its freshness, and the two exact header words read by the RAM. -/
theorem OutgoingReadyAt.prepend {N M : ℕ} {s : State} {edges : Array EdgeRecord}
    {outgoing : Array (List ℕ)} {i p q : ℕ}
    (h : OutgoingReadyAt N M s outgoing) (howned : SourceOwned edges outgoing)
    (hi : i < M) (hv : edges[i]!.source < N)
    (hfresh : ∀ u < N, i ∉ outgoing[u]!)
    (hp : (s.arrs Field.outgoingFirst.array)[edges[i]!.source]? = some p)
    (hq : (s.arrs Field.outgoingLast.array)[edges[i]!.source]? = some q) :
    OutgoingReadyAt N M (appendOutgoingState s edges[i]!.source i p q)
      (prependSource edges outgoing i) := by
  let v := edges[i]!.source
  change OutgoingReadyAt N M (appendOutgoingState s v i p q) (prependSource edges outgoing i)
  have hfv : v < (s.arrs 47).length := by
    change v < (s.arrs Field.outgoingFirst.array).length
    rw [h.2.1]; exact hv
  have hlv : v < (s.arrs 48).length := by
    change v < (s.arrs Field.outgoingLast.array).length
    rw [h.2.2.1]; exact hv
  have hvs : v < outgoing.size := by rw [h.1]; exact hv
  obtain ⟨first, hfirst, hlast, hchain, hnd⟩ := h.2.2.2.2 v hv
  have hpfirst : p = first := Option.some.inj (hp.symm.trans hfirst)
  subst first
  have hqlast : q = optionWord outgoing[v]!.head? := Option.some.inj (hq.symm.trans hlast)
  have hislot : i < (s.arrs Field.outgoingNext.array).length := by rw [h.2.2.2.1]; exact hi
  have hcapFirst : ((appendOutgoingState s v i p q).arrs Field.outgoingFirst.array).length = N := by
    unfold appendOutgoingState
    split <;> simpa [Field.array] using h.2.1
  have hcapLast : ((appendOutgoingState s v i p q).arrs Field.outgoingLast.array).length = N := by
    unfold appendOutgoingState
    split <;> simpa [Field.array] using h.2.2.1
  have hcapNext : ((appendOutgoingState s v i p q).arrs Field.outgoingNext.array).length = M := by
    unfold appendOutgoingState
    split <;> simpa [Field.array] using h.2.2.2.1
  refine ⟨by simpa [prependSource] using h.1, hcapFirst, hcapLast, hcapNext, ?_⟩
  intro u hu
  by_cases huv : u = v
  · subst u
    have hnewList : (prependSource edges outgoing i)[v]! = i :: outgoing[v]! :=
      Array.getElem!_set!_self outgoing v (i :: outgoing[v]!) hvs
    rw [hnewList]
    cases hxs : outgoing[v]! with
    | nil =>
      have hpzero : p = 0 := hchain.null_iff.mpr (by simp [hxs])
      have hqzero : q = 0 := by simpa [hxs, optionWord] using hqlast
      refine ⟨i + 1, ?_, ?_, ?_, ?_⟩
      · simp [appendOutgoingState, hpzero, Field.array, hfv]
      · simp [appendOutgoingState, hpzero, Field.array, hlv, optionWord]
      · simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
        refine .cons ?_ .nil
        simpa [appendOutgoingState, hpzero, Field.array] using
          (show ((s.arrs Field.outgoingNext.array).set i 0)[i]? = some 0 by simp [hislot])
      · simp
    | cons last rest =>
      have hpnonzero : p ≠ 0 := by
        intro he
        have hh := hchain.null_iff.mp he
        simp [hxs] at hh
      have hqval : q = last + 1 := by simpa [hxs, optionWord] using hqlast
      have hlastRev : outgoing[v]!.reverse.getLast? = some last := by simp [hxs]
      have hc := hchain.append (List.nodup_reverse.mpr hnd) hlastRev
        (by simpa only [List.mem_reverse] using hfresh v hv) hislot
      refine ⟨p, ?_, ?_, ?_, ?_⟩
      · simpa [appendOutgoingState, hpnonzero, Field.array] using hp
      · simp [appendOutgoingState, hpnonzero, Field.array,
          hlv, optionWord]
      · have hc' := hc.of_arr_eq (show
          (appendOutgoingState s v i p q).arrs Field.outgoingNext.array =
          (appendLinkState s Field.outgoingNext.array last i).arrs Field.outgoingNext.array by
            simp [appendOutgoingState, hpnonzero, hqval, appendLinkState, Field.array])
        simpa only [hxs, List.reverse_cons] using hc'
      · simpa only [hxs] using List.nodup_cons.mpr ⟨hfresh v hv, hnd⟩
  · have hnewList : (prependSource edges outgoing i)[u]! = outgoing[u]! :=
      Array.getElem!_set!_ne outgoing v u (i :: outgoing[v]!) (Ne.symm huv)
    rw [hnewList]
    obtain ⟨first, hfirst, hlast, hc, hnd⟩ := h.2.2.2.2 u hu
    have hcleared := hc.write_other (x := 0) (by simpa only [List.mem_reverse] using hfresh u hu)
    have hcnew : EdgeChain (appendOutgoingState s v i p q)
        Field.outgoingNext.array first outgoing[u]!.reverse := by
      by_cases hpzero : p = 0
      · apply hcleared.of_arr_eq
        simp [appendOutgoingState, hpzero, Field.array]
      · cases hxs : outgoing[v]! with
        | nil => exact False.elim (hpzero (hchain.null_iff.mpr (by simp [hxs])))
        | cons last rest =>
          have hqval : q = last + 1 := by simpa [hxs, optionWord] using hqlast
          have hlastMember : last ∈ outgoing[v]! := by simp [hxs]
          have hlastFresh : last ∉ outgoing[u]!.reverse := by
            intro hm
            have hsrcv := howned v hvs last hlastMember
            have hsrcu := howned u (by rw [h.1]; exact hu) last (List.mem_reverse.mp hm)
            exact huv (hsrcu.symm.trans hsrcv)
          apply (hcleared.write_other (x := i + 1) hlastFresh).of_arr_eq
          simp [appendOutgoingState, hpzero, hqval, Field.array]
    refine ⟨first, ?_, ?_, hcnew, hnd⟩
    · unfold appendOutgoingState
      split <;> simpa [Field.array, List.getElem?_set, Ne.symm huv] using hfirst
    · unfold appendOutgoingState
      split <;> simpa [Field.array, List.getElem?_set, Ne.symm huv] using hlast

end GraphMinor.Compute.PlanarityRam
