module

public import GraphMinor.GM08.Defs6to18
import GraphMinor.GM08.Section4

/-!
# The label order in the disc induction of VIII, Section 12

The induction hypothesis and (4.3) make the smaller rooted graphs
well-rooted. Adding the isolated label `*` preserves well-quasi-ordering:
an infinite sequence has an infinite subsequence of one of the two
label kinds. This proves the assertion about `Q_{k-1}` on page 274.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u v w

private theorem increasing_sequence_in_infinite {A : Set ℕ} (hA : A.Infinite) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, f n ∈ A := by
  have hex : ∀ m : ℕ, ∃ n, n ∈ A ∧ m < n := by
    intro m
    by_contra! hle
    exact hA ((finite_le_nat m).subset hle)
  choose next hmem hlt using hex
  let f : ℕ → ℕ := fun n => Nat.recOn n (next 0) (fun _ prev => next prev)
  refine ⟨f, strictMono_nat_of_lt_succ (fun n => hlt (f n)), ?_⟩
  intro n
  cases n with
  | zero => exact hmem 0
  | succ n => exact hmem (f n)

/-- Adding the isolated label `*` to the well-rooted class of smaller
rooted graphs gives the well-quasi-order used in VIII, Section 12,
page 274. The two kinds of labels are incomparable. -/
theorem isWellQuasiOrder_qkLE {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] (k : ℤ)
    (hA : IsWellRootedRootedGraphClass (discRootedClassA (α := α) (β := β) S k)) :
    IsWellQuasiOrder (qkLE (α := α) (β := β) S k) := by
  classical
  constructor
  · constructor
    · intro a
      cases a with
      | none => trivial
      | some a => exact IsRootedGraphSimulatedIn.refl a.1
    · intro a b c hab hbc
      cases a <;> cases b <;> cases c <;> simp only [qkLE] at *
      exact hab.trans hbc
  · intro q
    obtain ⟨b, hb⟩ := Finite.exists_infinite_fiber (fun n => (q n).isSome)
    obtain ⟨f, hf, hfb⟩ := increasing_sequence_in_infinite (Set.infinite_coe_iff.mp hb)
    cases b with
    | false =>
      have hnone : ∀ n, q (f n) = none := by
        intro n
        have h := hfb n
        change (q (f n)).isSome = false at h
        cases he : q (f n) with
        | none => rfl
        | some a => simp only [he, Option.isSome_some, Bool.true_eq_false] at h
      refine ⟨f 0, f 1, hf (by omega), ?_⟩
      rw [hnone 0, hnone 1]
      trivial
    | true =>
      have hex : ∀ n, ∃ a, q (f n) = some a := by
        intro n
        have h := hfb n
        change (q (f n)).isSome = true at h
        cases he : q (f n) with
        | none => simp only [he, Option.isSome_none, Bool.false_eq_true] at h
        | some a => exact ⟨a, rfl⟩
      choose a ha using hex
      obtain ⟨i, j, hij, hsim⟩ := hA (fun n => (a n).1) (fun n => (a n).2)
      refine ⟨f i, f j, hf hij, ?_⟩
      rw [ha i, ha j]
      exact hsim

/-- The induction hypothesis on grafts gives well-rootedness of the
smaller rooted graphs by VIII (4.3), as used in Section 12, page 274. -/
theorem isWellRooted_discRootedClassA {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] (k : ℕ)
    (hA : IsWellRootedGraftClass {X : Graft α β | X.index ≤ k ∧ EmbedsGraft S X}) :
    IsWellRootedRootedGraphClass (discRootedClassA (α := α) (β := β) S k) := by
  classical
  apply theorem_4_3_proof hA
  · refine ⟨k, fun X hX => ?_⟩
    have h := hX.1
    change (X.index : ℤ) ≤ k at h
    omega
  · intro X hX
    refine ⟨?_, hX.2.1⟩
    have heq : X.toGraft.index = X.index := by
      change {v | v ∈ X.τ}.ncard = X.τ.length
      have hs : {v | v ∈ X.τ} = (X.τ.toFinset : Set α) := by ext v; simp
      rw [hs, ncard_coe_finset, List.toFinset_card_of_nodup hX.2.2]
    rw [heq]
    have h := hX.1
    change (X.index : ℤ) ≤ k at h
    omega

/-- There are no rooted graphs of negative index, so the initial label
class in the disc induction is empty. -/
theorem isWellRooted_discRootedClassA_negative {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] {k : ℤ} (hk : k < 0) :
    IsWellRootedRootedGraphClass (discRootedClassA (α := α) (β := β) S k) := by
  intro X hX
  have h := (hX 0).1
  change ((X 0).index : ℤ) ≤ k at h
  omega

end GraphMinor.GM08
