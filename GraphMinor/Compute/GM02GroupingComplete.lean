module

public import GraphMinor.Compute.GM02GroupingInvariants
public import GraphMinor.Compute.GM02ClosedSideSeparation

/-!
# The grouping scan always produces a balanced side

If the scan finished without reaching one third, every remaining vertex
would already be selected. Its terminal count would then be the whole
remaining total, contradicting the strict one-third bound. Thus the
finished state is ready and gives the balanced separation used in the
successful output of II (3.1), page 316.
-/

public section
namespace GraphMinor.Compute
open Graph Set Classical

/-- After every vertex has been scanned, the selected side is a balanced
union of whole components. -/
theorem gm02GroupingState_complete {n : ℕ} (G : SimpleGraph (Fin n))
    (Q X : Finset (Fin n))
    (hcomp : ∀ a ∉ X, 3 * (gm02FiniteComponent G X a ∩ Q).card ≤ 2 * (Q \ X).card) :
    let st := gm02GroupingState G Q X n
    st.2 = true ∧ Disjoint X st.1 ∧
      (∀ a ∈ st.1, gm02FiniteComponent G X a ⊆ st.1) ∧
      (Q \ X).card ≤ 3 * (st.1 ∩ Q).card ∧
      3 * (st.1 ∩ Q).card ≤ 2 * (Q \ X).card := by
  obtain ⟨hdis, hclosed, hready, hnotready, hcover⟩ := gm02GroupingState_invariants G Q X hcomp n le_rfl
  let st := gm02GroupingState G Q X n
  have hr : st.2 = true := by
    cases he : st.2 with
    | true => rfl
    | false =>
      have hy : st.1 = Finset.univ \ X := by
        ext v
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact ⟨fun hv hx => Finset.disjoint_left.1 hdis hx hv,
          fun hv => hcover he v v.isLt hv⟩
      have hcount : (st.1 ∩ Q).card = (Q \ X).card := by
        rw [hy]
        congr 1
        ext v
        simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact and_comm
      have hbad := hnotready he
      rw [hcount] at hbad
      omega
  exact ⟨hr, hdis, hclosed, (hready hr).1, (hready hr).2⟩

/-- The finished greedy grouping gives exactly the two output sides of a
balanced separation, by the edge-partition construction of II (2.6). -/
theorem gm02GroupingState_separation {n : ℕ} (G : SimpleGraph (Fin n))
    (Q X : Finset (Fin n))
    (hcomp : ∀ a ∉ X, 3 * (gm02FiniteComponent G X a ∩ Q).card ≤ 2 * (Q \ X).card) :
    let Y := (gm02GroupingState G Q X n).1
    ∃ H H' : Graph (Fin n) (Sym2 (Fin n)),
      GM02.IsSeparation (Graph.ofSimpleGraph G) H H' ∧
      V(H) = (↑(X ∪ Y) : Set (Fin n)) ∧ V(H') = (↑(Finset.univ \ Y) : Set (Fin n)) ∧
      V(H) ∩ V(H') = (X : Set (Fin n)) ∧
      3 * ((V(H) \ V(H')) ∩ (Q : Set (Fin n))).ncard ≤
        2 * ((Q : Set (Fin n)) \ (V(H) ∩ V(H'))).ncard ∧
      3 * ((V(H') \ V(H)) ∩ (Q : Set (Fin n))).ncard ≤
        2 * ((Q : Set (Fin n)) \ (V(H) ∩ V(H'))).ncard := by
  obtain ⟨_, hdis, hclosed, hlo, hhi⟩ := gm02GroupingState_complete G Q X hcomp
  exact gm02BalancedSeparation_of_closed_side G Q X _ hdis hclosed hlo hhi

end GraphMinor.Compute
