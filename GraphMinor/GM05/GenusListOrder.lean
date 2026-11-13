module

public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Order.WellFounded

/-!
# The strict order on component genus lists

Graph Minors V, page 112, compares nonincreasing finite genus lists at
their first unequal entries. A proper prefix is not smaller in this
order. At a strict decrease, remove the common prefix: every entry of
the new tail is smaller than the first entry of the old tail. The
Dershowitz–Manna multiset order therefore proves well-foundedness.
-/

@[expose] public section

namespace GraphMinor.GM05

/-- The lexicographic order of Graph Minors V, page 112, with prefixes
incomparable: both lists have a first unequal entry, and the first list's
entry is smaller. -/
def GenusListLT (A B : List ℕ) : Prop :=
  ∃ P : List ℕ, ∃ a b : ℕ, ∃ L R : List ℕ,
    A=P++a::L ∧ B=P++b::R ∧ a<b

/-- A decrease in a sorted genus list is a decrease of its multiset of
entries in the well-founded Dershowitz–Manna order. -/
theorem genusListLT_multiset {A B : List ℕ} (hA : A.Pairwise (· ≥ ·))
    (h : GenusListLT A B) : Multiset.IsDershowitzMannaLT (A : Multiset ℕ) (B : Multiset ℕ) := by
  obtain ⟨P,a,b,L,R,rfl,rfl,hab⟩ := h
  have htail : (a::L).Pairwise (· ≥ ·) := (List.pairwise_append.mp hA).2.1
  have hhead := (List.pairwise_cons.mp htail).1
  refine ⟨(P : Multiset ℕ),(a::L : List ℕ),(b::R : List ℕ),by simp,
    (Multiset.coe_add _ _).symm,(Multiset.coe_add _ _).symm,?_⟩
  intro y hy
  refine ⟨b,by simp,?_⟩
  rcases List.mem_cons.mp (Multiset.mem_coe.mp hy) with rfl|hy
  · exact hab
  · exact lt_of_le_of_lt (hhead y hy) hab

/-- The paper's order is well-founded on nonincreasing lists of natural
numbers. This is the combinatorial part of Graph Minors V, (8.9). -/
theorem genusList_wellFounded : WellFounded
    (fun A B : {L : List ℕ // L.Pairwise (· ≥ ·)} ↦ GenusListLT A.1 B.1) := by
  have hsub : Subrelation
      (fun A B : {L : List ℕ // L.Pairwise (· ≥ ·)} ↦ GenusListLT A.1 B.1)
      (Function.onFun Multiset.IsDershowitzMannaLT (fun A ↦ (A.1 : Multiset ℕ))) :=
    by
      intro A B h
      exact genusListLT_multiset A.2 h
  exact hsub.wf Multiset.wellFounded_isDershowitzMannaLT.onFun

/-- No infinite sequence of sorted genus lists strictly decreases at
every step. -/
theorem genusList_no_descending (g : ℕ → List ℕ) (hg : ∀ n,(g n).Pairwise (· ≥ ·)) :
    ¬∀ n,GenusListLT (g (n+1)) (g n) := by
  intro h
  exact (wellFounded_iff_isEmpty_descending_chain.mp genusList_wellFounded).false
    ⟨fun n ↦ ⟨g n,hg n⟩,h⟩

end GraphMinor.GM05
