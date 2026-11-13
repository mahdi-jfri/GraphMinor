module

public import GraphMinor.GM01.MengerSeparators
import GraphMinor.GM01.Separators

/-!
# A small separator from many disjoint connected separators

Graph Minors I, (4.2), pages 55–56, uses Menger's theorem and (2.7).
If there were no small separator, Menger would supply `θ²/2` disjoint
paths. The `θ^(2θ)` disjoint connected separators contradict (2.7).
Applying the proved strict form of the Menger separator lemma gives the
required separator of size strictly less than `θ²/2`.
-/

public section

namespace GraphMinor.GM01

open Set SimpleGraph

/-- The Menger and (2.7) argument used in Graph Minors I, (4.2), pages
55–56, for the existing simple-graph representation of Section 2. -/
theorem exists_small_separator_of_many_disjoint_separators {α : Type*} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) {G : (⊤ : SimpleGraph α).Subgraph}
    (hfin : G.verts.Finite) (hG : G ∈ 𝓕 θ) {A B : Set α}
    (hA : A ⊆ G.verts) (hB : B ⊆ G.verts)
    (K : Fin (θ ^ (2 * θ)) → (⊤ : SimpleGraph α).Subgraph)
    (hKle : ∀ i, K i ≤ G) (hKconn : ∀ i, (K i).Connected)
    (hKdisj : Pairwise fun i j ↦ Disjoint (K i).verts (K j).verts)
    (hKsep : ∀ i, Separates G (K i).verts A B) :
    ∃ X ⊆ G.verts, X.ncard < θ ^ 2 / 2 ∧ Separates G X A B := by
  have hNo : ¬ ∃ P : Fin (θ ^ 2 / 2) → Path α,
      IsDisjointPathFamily G A B P ∧ ∀ k, (P k).Avoids ∅ := by
    rintro ⟨P, hP, _⟩
    rcases theorem_2_7_simple hθ heven hfin hG hA hB P hP K hKle hKconn hKdisj hKsep with h | h
    · exact (Nat.lt_irrefl _) h
    · exact (Nat.lt_irrefl _) h
  obtain ⟨X, hX, hcard, hsep⟩ := exists_separator_of_no_disjoint_paths hfin ∅ A B hNo
  exact ⟨X, hX, hcard, by simpa only [empty_union] using hsep⟩

end GraphMinor.GM01
