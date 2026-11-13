module

public import GraphMinor.Compute.PlanarityRamSolveClaim
public import GraphMinor.Compute.PlanarityRamPrefix

/-!
# Edge-pointer chains for the global buckets

The bucket and outgoing links store tagged edge identifiers. Changing the
link of an edge outside a chain leaves that chain intact. This is the
ownership fact needed when prepending a new bucket member and appending
one edge to an outgoing list, as in lines 222–241 of `docs/planarity/planarity_linear.py`.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

/-- A null-terminated list of edge identifiers through one link array.
The edge identifier itself is the address of its link word. -/
inductive EdgeChain (s : State) (links : ℕ) : ℕ → List ℕ → Prop where
  | nil : EdgeChain s links 0 []
  | cons {i q : ℕ} {rest : List ℕ}
      (next : (s.arrs links)[i]? = some q)
      (tail : EdgeChain s links q rest) : EdgeChain s links (i + 1) (i :: rest)

/-- Only the link array determines the chain. -/
theorem EdgeChain.of_arr_eq {s s' : State} {a p : ℕ} {xs : List ℕ}
    (h : EdgeChain s a p xs) (ha : s'.arrs a = s.arrs a) : EdgeChain s' a p xs := by
  induction h with
  | nil => exact .nil
  | cons hn ht ih => exact .cons (by simpa only [ha] using hn) ih

/-- A chain is not changed by writing a link at an edge it does not own. -/
theorem EdgeChain.write_other {s : State} {a p i x : ℕ} {xs : List ℕ}
    (h : EdgeChain s a p xs) (hi : i ∉ xs) :
    EdgeChain (s.writeArr a i x) a p xs := by
  induction h with
  | nil => exact .nil
  | @cons j q rest hn ht ih =>
    have hne : j ≠ i := by intro he; exact hi (by simp [he])
    refine .cons ?_ (ih (fun hm => hi (by simp [hm])))
    simpa only [State.writeArr_arrs_self, List.getElem?_set, ite_eq_right (Ne.symm hne)] using hn

/-- Prepending needs one link write, provided the new edge is not already
in the chain and its allocated link slot exists. -/
theorem EdgeChain.prepend {s : State} {a p i : ℕ} {xs : List ℕ}
    (h : EdgeChain s a p xs) (hi : i ∉ xs) (hslot : i < (s.arrs a).length) :
    EdgeChain (s.writeArr a i p) a (i + 1) (i :: xs) := by
  refine .cons ?_ (h.write_other hi)
  simp [State.writeArr_arrs_self, hslot]

/-- A nonempty chain exposes its first edge and its next pointer. -/
theorem EdgeChain.cons_iff {s : State} {a p i : ℕ} {xs : List ℕ} :
    EdgeChain s a p (i :: xs) ↔ p = i + 1 ∧
      ∃ q, (s.arrs a)[i]? = some q ∧ EdgeChain s a q xs := by
  constructor
  · intro h
    cases h with
    | cons hn ht => exact ⟨rfl, _, hn, ht⟩
  · rintro ⟨rfl, q, hn, ht⟩
    exact .cons hn ht

/-- The empty list has exactly the null pointer. -/
theorem EdgeChain.nil_iff {s : State} {a p : ℕ} :
    EdgeChain s a p [] ↔ p = 0 := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

/-- The generic outgoing-link chain is exactly the solver's chain. -/
theorem edgeChain_outgoing_iff {s : State} {p : ℕ} {xs : List ℕ} :
    EdgeChain s Field.outgoingNext.array p xs ↔ OutgoingChain s p xs := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | cons hn ht ih => exact .cons hn ih
  · intro h
    induction h with
    | nil => exact .nil
    | cons hn ht ih => exact .cons hn ih

end GraphMinor.Compute.PlanarityRam
