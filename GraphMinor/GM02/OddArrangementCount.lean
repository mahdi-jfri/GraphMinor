module

public import GraphMinor.GM02.SmallArrangementLists
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting small arrangements with an odd path

If a fixed path has odd length on at most two vertices, it contains one
vertex. Once that vertex is known, every other list is determined by its
length parity: there is at most one remaining vertex. The marked set has
at most that one vertex, so its nonemptiness is one further bit. This is
the small-separator count in II (2.8) when the parity profile is nonzero.
-/

public section
namespace GraphMinor.GM02
open Set Classical
universe u t

/-- On two vertices, equal parity profiles and the same singleton odd
path determine every list. One marked-set bit determines the rest. -/
theorem PathListArrangement.eq_of_odd_singleton {α : Type u} {S : Set α} {I : Type t}
    (hS : S.Finite) (hn : S.ncard ≤ 2) (A B : PathListArrangement S I)
    {i : I} {a : α} (hAi : A.paths i = [a]) (hBi : B.paths i = [a])
    (hpar : ∀ j, (A.paths j).length % 2 = (B.paths j).length % 2)
    (hm : A.marked.Nonempty ↔ B.marked.Nonempty) : A = B := by
  have haS : a ∈ S := A.vertex_mem i a (by rw [hAi]; simp)
  have hrem : ∀ x ∈ S \ {a}, ∀ y ∈ S \ {a}, x = y := by
    apply (Set.ncard_le_one hS.sdiff).1
    rw [Set.ncard_sdiff_singleton_of_mem haS]
    omega
  have hAmarked : A.marked ⊆ S \ {a} := by
    intro x hx
    refine ⟨A.marked_subset hx, ?_⟩
    intro heq
    have hxa : x = a := heq
    subst x
    exact A.marked_unused a hx i (by rw [hAi]; simp)
  have hBmarked : B.marked ⊆ S \ {a} := by
    intro x hx
    refine ⟨B.marked_subset hx, ?_⟩
    intro heq
    have hxa : x = a := heq
    subst x
    exact B.marked_unused a hx i (by rw [hBi]; simp)
  apply PathListArrangement.ext_data
  · funext j
    by_cases hji : j = i
    · subst j; exact hAi.trans hBi.symm
    · have hAl := A.length_add_le hS (Ne.symm hji)
      have hBl := B.length_add_le hS (Ne.symm hji)
      rw [hAi] at hAl
      rw [hBi] at hBl
      simp only [List.length_singleton] at hAl hBl
      have hlen := hpar j
      have heqlen : (A.paths j).length = (B.paths j).length := by omega
      by_cases hzero : (A.paths j).length = 0
      · have hAz := List.length_eq_zero_iff.1 hzero
        have hBz := List.length_eq_zero_iff.1 (heqlen.symm.trans hzero)
        exact hAz.trans hBz.symm
      · have hoddA : (A.paths j).length % 2 = 1 := by omega
        have hoddB : (B.paths j).length % 2 = 1 := by omega
        obtain ⟨x, hx⟩ := singleton_of_odd_of_length_le_two (A.paths j) (by omega) hoddA
        obtain ⟨y, hy⟩ := singleton_of_odd_of_length_le_two (B.paths j) (by omega) hoddB
        have hxS : x ∈ S \ {a} := ⟨A.vertex_mem j x (by rw [hx]; simp), by
          intro heq
          have hxa : x = a := heq
          subst x
          exact A.disjoint i j (Ne.symm hji) a (by rw [hAi]; simp) (by rw [hx]; simp)⟩
        have hyS : y ∈ S \ {a} := ⟨B.vertex_mem j y (by rw [hy]; simp), by
          intro heq
          have hya : y = a := heq
          subst y
          exact B.disjoint i j (Ne.symm hji) a (by rw [hBi]; simp) (by rw [hy]; simp)⟩
        rw [hx, hy, hrem x hxS y hyS]
  · ext x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hm.1 ⟨x, hx⟩
      exact (hrem y (hBmarked hy) x (hAmarked hx)) ▸ hy
    · intro hx
      obtain ⟨y, hy⟩ := hm.2 ⟨x, hx⟩
      exact (hrem y (hAmarked hy) x (hBmarked hx)) ▸ hy

/-- With a fixed odd path in its parity profile, a small arrangement has
at most one vertex choice and one marked bit. -/
theorem card_arrangements_with_odd_profile {α : Type u} {S : Set α} {I : Type t}
    (hS : S.Finite) (hn : S.ncard ≤ 2) (profile : I → ℕ) {i : I} (hi : profile i = 1) :
    Nat.card {A : PathListArrangement S I // ∀ j, (A.paths j).length % 2 = profile j} ≤
      S.ncard * 2 := by
  let T := {A : PathListArrangement S I // ∀ j, (A.paths j).length % 2 = profile j}
  have hsingleton : ∀ A : T, ∃ a, A.val.paths i = [a] := by
    intro A
    apply singleton_of_odd_of_length_le_two _ ((A.val.length_le hS i).trans hn)
    exact (A.property i).trans hi
  let f : T → S × Bool := fun A =>
    let a := (hsingleton A).choose
    have ha : A.val.paths i = [a] := (hsingleton A).choose_spec
    have ham : a ∈ A.val.paths i := by rw [ha]; exact List.mem_singleton_self a
    (⟨a, A.val.vertex_mem i a ham⟩, decide A.val.marked.Nonempty)
  let _ := hS.to_subtype
  have hf : Function.Injective f := by
    intro A B heq
    have ha : (hsingleton A).choose = (hsingleton B).choose :=
      congrArg (fun p => p.1.val) heq
    have hm := congrArg Prod.snd heq
    change decide A.val.marked.Nonempty = decide B.val.marked.Nonempty at hm
    apply Subtype.ext
    apply PathListArrangement.eq_of_odd_singleton hS hn A.val B.val
      (hsingleton A).choose_spec (ha ▸ (hsingleton B).choose_spec)
      (fun j => (A.property j).trans (B.property j).symm)
    simpa using (congrArg (fun b : Bool => b = true) hm).to_iff
  have h := Nat.card_le_card_of_injective f hf
  simpa [T, Nat.card_prod, Nat.card_coe_set_eq, show Nat.card Bool = 2 from by
    simp [Nat.card_eq_fintype_card]] using h

end GraphMinor.GM02
