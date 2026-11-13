module

public import GraphMinor.Compute.PlanarityRamOutgoingStep

/-!
# Freshness across the outgoing traversal

The remaining bucket traversal is a list of distinct edge identifiers.
When its first identifier is appended, every later identifier stays
outside the outgoing chains. This is the ownership step for the inner
bucket loop and for the transition to the next global bucket.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

/-- The pending edge identifiers do not occur in any source list. -/
def OutgoingFresh (N : ℕ) (pending : List ℕ) (outgoing : Array (List ℕ)) : Prop :=
  ∀ i ∈ pending, ∀ v < N, i ∉ outgoing[v]!

/-- Restrict freshness to any subset of pending identifiers. -/
theorem OutgoingFresh.mono {N : ℕ} {pending rest : List ℕ} {outgoing : Array (List ℕ)}
    (h : OutgoingFresh N pending outgoing) (hsub : rest ⊆ pending) :
    OutgoingFresh N rest outgoing := fun i hi => h i (hsub hi)

/-- Empty outgoing lists are fresh for every pending sequence. -/
theorem OutgoingFresh.empty (N : ℕ) (pending : List ℕ) :
    OutgoingFresh N pending (Array.replicate N []) := by
  intro i hi v hv
  simp [getElem!_pos, hv]

/-- Consuming the first distinct pending identifier preserves freshness of
all the others. The source need only be a valid array index. -/
theorem OutgoingFresh.prepend {N : ℕ} {edges : Array LRPlanarity.EdgeRecord}
    {i : ℕ} {rest : List ℕ} {outgoing : Array (List ℕ)}
    (h : OutgoingFresh N (i :: rest) outgoing) (hnd : (i :: rest).Nodup)
    (hv : edges[i]!.source < outgoing.size) :
    OutgoingFresh N rest (prependSource edges outgoing i) := by
  intro j hj v hvN
  have hji : j ≠ i := by intro he; exact (List.nodup_cons.mp hnd).1 (he ▸ hj)
  by_cases hsource : edges[i]!.source = v
  · subst v
    rw [prependSource, Array.getElem!_set!_self outgoing _ _ hv]
    simp only [List.mem_cons, not_or]
    exact ⟨hji, h j (by simp [hj]) _ hvN⟩
  · rw [prependSource, Array.getElem!_set!_ne outgoing _ _ _ hsource]
    exact h j (by simp [hj]) v hvN

/-- The pending empty list imposes no condition. -/
theorem OutgoingFresh.nil (N : ℕ) (outgoing : Array (List ℕ)) :
    OutgoingFresh N [] outgoing := by intro i hi; simp at hi

end GraphMinor.Compute.PlanarityRam
