module

public import GraphMinor.GM02.SeparatorCandidates

/-!
# Vertex sets represented by numeric separator slots

The RAM enumerates vertex numbers with the vertex count as an empty
slot. Interpreting a numeric slot outside the vertex range as empty
recovers the optional-tuple enumeration. Its represented vertex set has
the required size bound, and every small separator has a representation
whose words are at most the vertex count.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.GM02 Classical

/-- Interpret a numeric slot, using out-of-range values as empty slots. -/
def gm02SlotOption {n : ℕ} (v : ℕ) : Option (Fin n) :=
  if h : v < n then some ⟨v, h⟩ else none

/-- Vertices appearing among numeric candidate slots. -/
def gm02SlotVertices {n k : ℕ} (f : Fin k → ℕ) : Finset (Fin n) :=
  separatorOfTuple (fun i => gm02SlotOption (n := n) (f i))

/-- A vertex is represented exactly when one slot has its number. -/
theorem mem_gm02SlotVertices {n k : ℕ} (f : Fin k → ℕ) (v : Fin n) :
    v ∈ gm02SlotVertices f ↔ ∃ i, f i = v.val := by
  simp only [gm02SlotVertices, separatorOfTuple, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Option.mem_toFinset, Option.mem_def]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    unfold gm02SlotOption at hi
    split at hi
    · exact congrArg Fin.val (Option.some.inj hi)
    · contradiction
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simp only [gm02SlotOption, hi, dite_eq_left v.isLt, Fin.eta]

/-- Numeric slots represent no more vertices than the number of slots. -/
theorem gm02SlotVertices_card_le {n k : ℕ} (f : Fin k → ℕ) :
    (gm02SlotVertices (n := n) f).card ≤ k := separatorOfTuple_card_le _

/-- Every permitted separator has a numeric representation with an empty
slot represented by `n`, so all slot values are at most `n`. -/
theorem exists_gm02SlotVertices {n k : ℕ} (X : Finset (Fin n)) (hX : X.card ≤ k) :
    ∃ f : Fin k → ℕ, (∀ i, f i ≤ n) ∧ gm02SlotVertices f = X := by
  obtain ⟨g, hg⟩ := exists_separator_tuple X hX
  let f : Fin k → ℕ := fun i => (g i).elim n Fin.val
  refine ⟨f, ?_, ?_⟩
  · intro i
    cases h : g i with
    | none => simp only [f, h, Option.elim_none, le_refl]
    | some v => simpa only [f, h, Option.elim_some] using Nat.le_of_lt v.isLt
  · have he : ∀ i, gm02SlotOption (n := n) (f i) = g i := by
      intro i
      cases h : g i with
      | none => simp only [f, h, Option.elim_none, gm02SlotOption, Nat.lt_irrefl, dite_eq_right, not_false_eq_true]
      | some v => simp only [f, h, Option.elim_some, gm02SlotOption, dite_eq_left v.isLt, Fin.eta]
    unfold gm02SlotVertices
    simp only [he]
    exact hg

end GraphMinor.Compute
