module

public import GraphMinor.GM05.GenusListOrder
public import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Multiset.Filter

/-!
# Replacing one component by lower genera

In Graph Minors V, (8.10), a cut either lowers one connected genus or
replaces it by two smaller genera. All the unchanged component genera
at least as large as the old genus form a common prefix. The next
entry strictly decreases. This proves the comparison using the paper's
order, in which a proper prefix alone would not give a decrease.
-/

public section

namespace GraphMinor.GM05

/-- Sorting a multiset sum concatenates the sorted lists when every
entry of the first multiset is at least every entry of the second. -/
theorem sort_genus_add {M N : Multiset ℕ}
    (h : ∀ x ∈ M,∀ y ∈ N,y ≤ x) :
    (M+N).sort (· ≥ ·)=M.sort (· ≥ ·)++N.sort (· ≥ ·) := by
  apply List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _)
  · apply List.pairwise_append.mpr
    refine ⟨Multiset.pairwise_sort _ _,Multiset.pairwise_sort _ _,?_⟩
    intro x hx y hy
    exact h x ((Multiset.mem_sort (· ≥ ·)).mp hx) y ((Multiset.mem_sort (· ≥ ·)).mp hy)
  · apply Multiset.coe_eq_coe.mp
    rw [← Multiset.coe_add,Multiset.sort_eq,Multiset.sort_eq,Multiset.sort_eq]

/-- Replacing one genus by a nonempty multiset of strictly smaller
genera strictly lowers the sorted component-genus list. -/
theorem genusListLT_replace (M N : Multiset ℕ) (a : ℕ)
    (hne : ∃ n,n ∈ N) (hsmall : ∀ n ∈ N,n<a) :
    GenusListLT ((M+N).sort (· ≥ ·)) ((M+{a}).sort (· ≥ ·)) := by
  classical
  let P := M.filter (a ≤ ·)
  let R := M.filter (fun n ↦ ¬a ≤ n)
  have hM : P+R=M := Multiset.filter_add_not _ _
  have hP : ∀ n ∈ P,a ≤ n := fun n hn ↦ (Multiset.mem_filter.mp hn).2
  have hR : ∀ n ∈ R,n<a := fun n hn ↦ Nat.lt_of_not_ge (Multiset.mem_filter.mp hn).2
  have htail : ∀ n ∈ R+N,n<a := by
    intro n hn
    rcases Multiset.mem_add.mp hn with hn|hn
    · exact hR n hn
    · exact hsmall n hn
  have hnew : (M+N).sort (· ≥ ·)=P.sort (· ≥ ·)++(R+N).sort (· ≥ ·) := by
    rw [← hM,add_assoc]
    exact sort_genus_add (fun x hx y hy ↦ le_trans (Nat.le_of_lt (htail y hy)) (hP x hx))
  have hcross : ∀ x ∈ P,∀ y ∈ a ::ₘ R,y ≤ x := by
    intro x hx y hy
    rcases Multiset.mem_cons.mp hy with rfl|hy
    · exact hP x hx
    · exact le_trans (Nat.le_of_lt (hR y hy)) (hP x hx)
  have hOld : M+{a}=P+(a ::ₘ R) := by
    rw [← hM]
    rw [← Multiset.singleton_add]
    ac_rfl
  have hold : (M+{a}).sort (· ≥ ·)=P.sort (· ≥ ·)++a::R.sort (· ≥ ·) := by
    rw [hOld,sort_genus_add hcross,Multiset.sort_cons]
    exact fun n hn ↦ Nat.le_of_lt (hR n hn)
  cases he : (R+N).sort (· ≥ ·) with
  | nil =>
    obtain ⟨n,hn⟩ := hne
    have hm : n ∈ (R+N).sort (· ≥ ·) := (Multiset.mem_sort (· ≥ ·)).mpr (Multiset.mem_add.mpr (.inr hn))
    rw [he] at hm
    exact (List.not_mem_nil hm).elim
  | cons b L =>
    have hb : b ∈ R+N := (Multiset.mem_sort (· ≥ ·)).mp (he.symm ▸ List.mem_cons_self)
    exact ⟨P.sort (· ≥ ·),b,a,L,R.sort (· ≥ ·),hnew.trans (by rw [he]),hold,htail b hb⟩

/-- A genus-list comparison with a singleton is a comparison of the
first entries; the common prefix must be empty. -/
theorem genusListLT_singleton_iff {A : List ℕ} {g : ℕ} :
    GenusListLT A [g] ↔ ∃ a L,A=a::L ∧ a<g := by
  constructor
  · rintro ⟨P,a,b,L,R,hA,hB,hab⟩
    have hn := congrArg List.length hB
    simp only [List.length_append,List.length_cons,List.length_nil] at hn
    have hP : P=[] := List.length_eq_zero_iff.mp (by omega)
    have hR : R=[] := List.length_eq_zero_iff.mp (by omega)
    subst P
    subst R
    simp only [List.nil_append,List.cons.injEq,and_true] at hB
    subst b
    exact ⟨a,L,by simpa only [List.nil_append] using hA,hab⟩
  · rintro ⟨a,L,rfl,ha⟩
    exact ⟨[],a,g,L,[],rfl,rfl,ha⟩

/-- A strict decrease from a connected component's singleton genus
list is preserved when the unchanged component genera are added. -/
theorem genusListLT_add_singleton (M : Multiset ℕ) {A : List ℕ} {g : ℕ}
    (hA : A.Pairwise (· ≥ ·)) (h : GenusListLT A [g]) :
    GenusListLT ((M+(A : Multiset ℕ)).sort (· ≥ ·)) ((M+{g}).sort (· ≥ ·)) := by
  obtain ⟨a,L,rfl,ha⟩ := genusListLT_singleton_iff.mp h
  have htail := (List.pairwise_cons.mp hA).1
  apply genusListLT_replace M (a::L : List ℕ) g ⟨a,by simp⟩
  intro n hn
  rcases List.mem_cons.mp (Multiset.mem_coe.mp hn) with rfl|hn
  · exact ha
  · exact lt_of_le_of_lt (htail n hn) ha

end GraphMinor.GM05
