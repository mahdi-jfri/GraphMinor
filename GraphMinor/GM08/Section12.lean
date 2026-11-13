module

public import GraphMinor.GM08.Defs
public import GraphMinor.Surface.Defs
import GraphMinor.GM08.Section4
import GraphMinor.GM08.Section9Conclusion
import GraphMinor.GM08.Section10
import GraphMinor.GM08.Section11b
import GraphMinor.GM08.Section12Cellular
import GraphMinor.GM08.Section12Derived
import GraphMinor.GM08.Section12Labels
import GraphMinor.GM08.Section12RootOrder
import GraphMinor.GM08.Section12Truncation
import GraphMinor.GM08.Section12Foundation

/-!
# Graph Minors VIII, Section 12: conclusion of the disc case

Induct on the bound on the graft index. By (4.2) it remains to handle
one fixed index. If the first graft is simulated in a later one we
are done. Otherwise (9.4) bounds the widths of all later truncations.
Construct their derived portraits. The smaller rooted labels form a
well-quasi-order by induction and (4.3), so (10.1) compares two portraits.
Then (11.2) compares the rooted graphs. Forget their root orders to
obtain the required graft simulation.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u v w

/-- Graph Minors VIII, Section 12, page 274: the class of all grafts
with index at most `k` which embed in a disc is well-rooted. The proof
is the paper's induction on the index, using (4.2), (4.3), (9.4),
(10.1), (11.1), and (11.2). -/
theorem theorem_6_1_disc {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] (hS : IsClosedDisc (univ : Set S)) (k : ℕ) :
    IsWellRootedGraftClass {X : Graft α β | X.index ≤ k ∧ EmbedsGraft S X} := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hSmall : IsWellRootedGraftClass
        {X : Graft α β | X.index < k ∧ EmbedsGraft S X} := by
      intro X hX
      by_cases hk : k = 0
      · have h := (hX 0).1
        omega
      · apply ih (k - 1) (by omega) X
        intro n
        exact ⟨by have h := (hX n).1; omega, (hX n).2⟩
    have hA : IsWellRootedRootedGraphClass
        (discRootedClassA (α := α) (β := β) S ((k : ℤ) - 1)) := by
      cases k with
      | zero => exact isWellRooted_discRootedClassA_negative (by omega)
      | succ m =>
        have heq : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by omega
        rw [heq]
        exact isWellRooted_discRootedClassA m (ih m (Nat.lt_succ_self m))
    have hQ := isWellQuasiOrder_qkLE ((k : ℤ) - 1) hA
    have hExact : IsWellRootedGraftClass
        {X : Graft α β | X.index = k ∧ EmbedsGraft S X} := by
      intro X hX
      by_cases hfirst : ∃ j, 0 < j ∧ IsGraftSimulatedIn (X 0) (X j)
      · obtain ⟨j, hj, hsim⟩ := hfirst
        exact ⟨0, j, hj, hsim⟩
      have hnot : ∀ n, ¬ IsGraftSimulatedIn (X 0) (X (n + 1)) := by
        intro n hn
        exact hfirst ⟨n + 1, Nat.zero_lt_succ n, hn⟩
      obtain ⟨width, hwidth⟩ := theorem_9_4_proof (α' := α) (β' := β) hS (X 0) (hX 0).2
      choose R hRX hRn hRk using fun n => exists_root_order (X (n + 1))
      have hRA : ∀ n, R n ∈ discRootedClassA S k := by
        intro n
        refine ⟨?_, ?_, hRn n⟩
        · rw [hRk n, (hX (n + 1)).1]
        · rw [hRX n]
          exact (hX (n + 1)).2
      have hRindex : ∀ n, (R n).index = k := fun n =>
        (hRk n).trans (hX (n + 1)).1
      choose gd hcell using fun n =>
        exists_cellular_graftDrawing hS (R n).toGraft (hRA n).2.1
      choose t F hF using fun n => exists_foundation hS (gd n).drawing (gd n).isProper
      choose P hP using fun n => exists_derived_portrait_via hS
        (R n) (hRA n) (hRindex n) (gd n) (hcell n) (hF n)
      choose Dstar hD using fun n => exists_truncation_induced_by hS (gd n).isProper (hF n)
      have hW : ∀ n, DrawingTreeWidthLE (Dstar n) width := by
        intro n
        apply hwidth (R n).toGraft
        · rw [hRX n, (hX (n + 1)).1, (hX 0).1]
        · rw [hRX n]
          exact hnot n
        · exact ⟨t n, F n, hD n⟩
      have hPW : ∀ n, PortraitTreeWidthLE (P n) width := fun n =>
        theorem_11_1_proof hS (hP n) (hD n) (hW n)
      have hPI : ∀ n, (P n).index = k := by
        intro n
        change ((P n).painting.U ∩ bd S).ncard = k
        rw [← (P n).α_set]
        have hset : {x | x ∈ (P n).α} = ((P n).α.toFinset : Set S) := by ext x; simp
        rw [hset, ncard_coe_finset, List.toFinset_card_of_nodup (P n).α_nodup]
        exact ((hP n).2.2.2.2.1).trans (hRindex n)
      obtain ⟨i, j, hij, hsim⟩ := theorem_10_1_proof hQ hS k width P hPI hPW
      have hr := theorem_11_2_proof hS (hRA i) (hRA j) (hRindex i) (hRindex j)
        ⟨gd i, t i, F i, hP i⟩ ⟨gd j, t j, F j, hP j⟩ hsim
      have hg := isGraftSimulatedIn_of_root_order (hRn i) (hRn j) hr
      rw [hRX i, hRX j] at hg
      exact ⟨i + 1, j + 1, Nat.add_lt_add_right hij 1, hg⟩
    have hUnion := theorem_4_2_proof hSmall hExact
    intro X hX
    apply hUnion X
    intro n
    by_cases heq : (X n).index = k
    · exact .inr ⟨heq, (hX n).2⟩
    · exact .inl ⟨lt_of_le_of_ne (hX n).1 heq, (hX n).2⟩

end GraphMinor.GM08
