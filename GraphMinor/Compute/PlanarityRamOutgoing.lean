module

public import GraphMinor.Compute.PlanarityRamBucketAppend
public import GraphMinor.Compute.PlanarityRamBucketFunction

/-!
# Outgoing heads, tails and source ownership

During the outgoing pass, the specification prepends identifiers and the
RAM appends them. The representation therefore stores the reverse of each
functional list, with its first functional member at the RAM tail. Source
ownership separates the chains belonging to different vertices.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- Heads and tails of the reversed functional lists, with their fixed
capacities and unique edge identifiers in each list. -/
def OutgoingReadyAt (N M : ℕ) (s : State) (outgoing : Array (List ℕ)) : Prop :=
  outgoing.size = N ∧
  (s.arrs Field.outgoingFirst.array).length = N ∧
  (s.arrs Field.outgoingLast.array).length = N ∧
  (s.arrs Field.outgoingNext.array).length = M ∧
  ∀ v < N, ∃ p,
    (s.arrs Field.outgoingFirst.array)[v]? = some p ∧
    (s.arrs Field.outgoingLast.array)[v]? = some (optionWord outgoing[v]!.head?) ∧
    EdgeChain s Field.outgoingNext.array p outgoing[v]!.reverse ∧ outgoing[v]!.Nodup

/-- Every source list owns only edges with that source. -/
def SourceOwned (edges : Array EdgeRecord) (outgoing : Array (List ℕ)) : Prop :=
  ∀ v < outgoing.size, ∀ i ∈ outgoing[v]!, edges[i]!.source = v

/-- Only the three outgoing arrays determine their representation. -/
theorem OutgoingReadyAt.of_memory_eq {N M : ℕ} {s s' : State} {outgoing : Array (List ℕ)}
    (h : OutgoingReadyAt N M s outgoing)
    (hf : s'.arrs Field.outgoingFirst.array = s.arrs Field.outgoingFirst.array)
    (hl : s'.arrs Field.outgoingLast.array = s.arrs Field.outgoingLast.array)
    (hn : s'.arrs Field.outgoingNext.array = s.arrs Field.outgoingNext.array) :
    OutgoingReadyAt N M s' outgoing := by
  refine ⟨h.1, by simpa only [hf] using h.2.1,
    by simpa only [hl] using h.2.2.1, by simpa only [hn] using h.2.2.2.1, ?_⟩
  intro v hv
  obtain ⟨p, hp, hlast, hc, hnd⟩ := h.2.2.2.2 v hv
  exact ⟨p, by simpa only [hf] using hp, by simpa only [hl] using hlast,
    hc.of_arr_eq hn, hnd⟩

/-- Registers have no effect on outgoing-list representation. -/
theorem OutgoingReadyAt.setReg {N M : ℕ} {s : State} {outgoing : Array (List ℕ)}
    (h : OutgoingReadyAt N M s outgoing) (r v : ℕ) :
    OutgoingReadyAt N M (s.setReg r v) outgoing := h.of_memory_eq rfl rfl rfl

/-- Allocated zero fields represent all the empty functional source lists. -/
theorem EmptyOutgoingAt.ready {N M : ℕ} {s : State} (h : EmptyOutgoingAt N M s) :
    OutgoingReadyAt N M s (Array.replicate N []) := by
  refine ⟨by simp, by simp [h.1], by simp [h.2.1], by simp [h.2.2], ?_⟩
  intro v hv
  refine ⟨0, by simp [h.1, hv], ?_, ?_, ?_⟩
  · simp [h.2.1, getElem!_pos, hv, optionWord]
  · simpa [getElem!_pos, hv] using (EdgeChain.nil : EdgeChain s Field.outgoingNext.array 0 [])
  · simp [getElem!_pos, hv]

/-- The completed representation gives exactly the outgoing chains expected
by the solver, after reversing the functional lists. -/
theorem OutgoingReadyAt.outgoingAt {N M : ℕ} {s : State} {outgoing : Array (List ℕ)}
    (h : OutgoingReadyAt N M s outgoing) : OutgoingAt N s (outgoing.map List.reverse) := by
  intro v hv
  obtain ⟨p, hp, hl, hc, hnd⟩ := h.2.2.2.2 v hv
  have hvs : v < outgoing.size := by rw [h.1]; exact hv
  refine ⟨p, hp, ?_⟩
  have heq : (outgoing.map List.reverse)[v]! = outgoing[v]!.reverse := by
    simp [getElem!_pos, hvs]
  rw [heq]
  exact edgeChain_outgoing_iff.mp hc

/-- Empty source lists have no ownership conflicts. -/
theorem SourceOwned.empty (edges : Array EdgeRecord) (N : ℕ) :
    SourceOwned edges (Array.replicate N []) := by
  intro v hv i hi
  have hv' : v < N := by simpa using hv
  simp [getElem!_pos, hv'] at hi

/-- Source prepending preserves source ownership. -/
theorem SourceOwned.prepend {edges : Array EdgeRecord} {outgoing : Array (List ℕ)}
    (h : SourceOwned edges outgoing) (i : ℕ) (hi : edges[i]!.source < outgoing.size) :
    SourceOwned edges (prependSource edges outgoing i) := by
  intro v hv e he
  have hv' : v < outgoing.size := by simpa [prependSource] using hv
  by_cases hsame : edges[i]!.source = v
  · subst v
    rw [prependSource, Array.getElem!_set!_self outgoing _ _ hi] at he
    rcases List.mem_cons.mp he with rfl | he
    · rfl
    · exact h _ hi _ he
  · rw [prependSource, Array.getElem!_set!_ne outgoing _ _ _ hsame] at he
    exact h v hv' e he

/-- An edge in a represented chain has an allocated link word. -/
theorem EdgeChain.member_slot {s : State} {a p i : ℕ} {xs : List ℕ}
    (h : EdgeChain s a p xs) (hi : i ∈ xs) : i < (s.arrs a).length := by
  induction h with
  | nil => simp at hi
  | @cons j q rest hn ht ih =>
    rcases List.mem_cons.mp hi with rfl | hm
    · exact (List.getElem?_eq_some_iff.mp hn).1
    · exact ih hm

end GraphMinor.Compute.PlanarityRam
