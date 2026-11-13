module

public import GraphMinor.Thomason.DominatingSets
public import Mathlib.Data.Nat.Log
import GraphMinor.Thomason.HalfDomination
import Lean.Elab.Tactic.Omega

/-!
# Small sets that dominate a chosen vertex set

Repeatedly choose a vertex which dominates at least half of the vertices
still uncovered. The number of uncovered vertices halves at every step,
so at most `floor(log₂ |X|)+1` chosen vertices suffice. This is the
halving argument in Thomason's Lemma 4 (1984), page 263.
-/

public section

namespace GraphMinor.Thomason

open SimpleGraph Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The halving part of Thomason's Lemma 4, p. 263. In a graph of order
at least three and minimum degree at least half the order, every chosen
set is dominated by at most `floor(log₂ |X|)+1` vertices. -/
theorem exists_small_dominating_set
    (hsize : 3 ≤ Fintype.card V)
    (hdeg : ∀ v : V, Fintype.card V ≤ 2 * G.degree v) (X : Finset V) :
    ∃ Y : Finset V, Y.card ≤ Nat.log 2 X.card + 1 ∧ X ⊆ dominatedVertices G Y := by
  suffices hmain : ∀ k : ℕ, ∀ X : Finset V, X.card = k →
      ∃ Y : Finset V, Y.card ≤ Nat.log 2 k + 1 ∧ X ⊆ dominatedVertices G Y from
    hmain X.card X rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro X hk
    by_cases hX : X = ∅
    · subst X
      exact ⟨∅, by simp, fun x h => (Finset.notMem_empty x h).elim⟩
    have hkpos : 0 < k := by
      have h := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hX)
      omega
    have hcount := card_verticesDominatingHalf G 0 (by simpa using hsize)
      (fun v => by simpa using hdeg v) X
    have hgood : (verticesDominatingHalf G X).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨v, hv⟩ := hgood
    let R := X \ dominatedVertices G {v}
    have hRle : R.card ≤ k / 2 := by
      have hhalf : 2 * (X ∩ undominatedVertices G {v}).card ≤ X.card :=
        (Finset.mem_filter.mp hv).2
      have heq : X ∩ undominatedVertices G {v} = R := by
        ext x
        simp only [R, undominatedVertices, mem_inter, mem_sdiff, mem_univ, true_and]
      rw [heq, hk] at hhalf
      omega
    have hRlt : R.card < k := by omega
    by_cases hR : R = ∅
    · refine ⟨{v}, by simp, ?_⟩
      intro x hx
      by_contra hn
      have hr : x ∈ R := Finset.mem_sdiff.mpr ⟨hx, hn⟩
      rw [hR] at hr
      exact Finset.notMem_empty x hr
    · obtain ⟨Y, hY, hdom⟩ := ih R.card hRlt R rfl
      refine ⟨insert v Y, ?_, ?_⟩
      · have hlog := Nat.log_mono_right (b := 2) hRle
        rw [Nat.log_div_base] at hlog
        have hk2 : 2 ≤ k := by
          have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hR)
          omega
        have hlogpos : 0 < Nat.log 2 k := Nat.log_pos (by omega) hk2
        have hins := Finset.card_insert_le v Y
        omega
      · intro x hx
        rw [dominatedVertices_insert]
        by_cases hvx : x ∈ dominatedVertices G {v}
        · exact Finset.mem_union_right _ (by rwa [← dominatedVertices_singleton])
        · exact Finset.mem_union_left _ (hdom (Finset.mem_sdiff.mpr ⟨hx, hvx⟩))

end GraphMinor.Thomason
