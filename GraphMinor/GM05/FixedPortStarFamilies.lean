module

public import GraphMinor.GM05.FixedPortStar
import Mathlib.Data.Fin.Tuple.Basic

/-!
# All local stars with their fixed ports

For GM V, (8.14), add the stars in one vertex disc in copy order.
All ports remain fixed. Each new centre avoids the old centres and
all prescribed ports, and each new ray misses every old double
crossing. The supporting lines stay distinct, and no point belongs
to rays of three distinct stars.
-/

public section
namespace GraphMinor.GM05
open Set Surface
universe v

private theorem exists_old_star_index {m : ℕ} (i : Fin (m+1)) (hi : i ≠ Fin.last m) :
    ∃ j : Fin m, j.castSucc = i :=
  Fin.lastCases (fun h ↦ (h rfl).elim) (fun j _ ↦ ⟨j,rfl⟩) i hi

/-- The fixed-port local general position family in GM V, proof of
(8.14), page 113. It includes distinct centres when there are no ports,
so isolated vertices are covered by the construction. -/
theorem exists_fixed_port_star_family (m : ℕ) {κ : Type v} [Fintype κ]
    (p : Fin m × κ → ℂ) (hp : ∀ q, ‖p q‖ = 1) (hpi : Function.Injective p)
    {Q : Set ℂ} (hQ : Q.Finite) (hpQ : ∀ q, p q ∈ Q)
    {s₀ s₁ : ℝ} (hs : s₀ < s₁) (hslen : s₁ ≤ s₀ + 1) :
    ∃ s : Fin m → ℝ, (∀ i, s i ∈ Ioo s₀ s₁) ∧
      (∀ i, (ee (s i) : ℂ) ∉ Q) ∧
      (∀ i j, i ≠ j → (ee (s i) : ℂ) ≠ (ee (s j) : ℂ)) ∧
      (∀ i j e f, (i,e) ≠ (j,f) →
        line[ℝ,(ee (s i) : ℂ),p (i,e)] ≠ line[ℝ,(ee (s j) : ℂ),p (j,f)]) ∧
      ∀ i j l e f g, i ≠ j → j ≠ l → i ≠ l → ∀ x : ℂ,
        ¬(x ∈ (line[ℝ,(ee (s i) : ℂ),p (i,e)] : Set ℂ) ∧
          x ∈ (line[ℝ,(ee (s j) : ℂ),p (j,f)] : Set ℂ) ∧
          x ∈ (line[ℝ,(ee (s l) : ℂ),p (l,g)] : Set ℂ)) := by
  classical
  induction m with
  | zero => exact ⟨Fin.elim0,fun i ↦ i.elim0,fun i ↦ i.elim0,fun i ↦ i.elim0,
      fun i ↦ i.elim0,fun i ↦ i.elim0⟩
  | succ m ih =>
    obtain ⟨s,hsI,hsQ,hsne,hline,hthree⟩ := ih
      (fun q ↦ p (q.1.castSucc,q.2)) (fun q ↦ hp (q.1.castSucc,q.2))
      (by
        intro q r he
        have h := hpi he
        exact Prod.ext ((Fin.castSucc_injective m) (congrArg (fun z : Fin (m+1) × κ ↦ z.1) h))
          (congrArg (fun z : Fin (m+1) × κ ↦ z.2) h))
      (fun q ↦ hpQ (q.1.castSucc,q.2))
    let a : Fin m × κ → ℂ := fun q ↦ ee (s q.1)
    let b : Fin m × κ → ℂ := fun q ↦ p (q.1.castSucc,q.2)
    have hab : ∀ q, a q ≠ b q := by
      intro q he
      apply hsQ q.1
      change a q ∈ Q
      rw [he]
      exact hpQ (q.1.castSucc,q.2)
    have hne : ∀ q r, q ≠ r → line[ℝ,a q,b q] ≠ line[ℝ,a r,b r] := by
      rintro ⟨i,e⟩ ⟨j,f⟩ h
      exact hline i j e f h
    have hnewa : ∀ e q, p (Fin.last m,e) ≠ a q := by
      intro e q he
      apply hsQ q.1
      change a q ∈ Q
      rw [← he]
      exact hpQ (Fin.last m,e)
    have hnewb : ∀ e q, p (Fin.last m,e) ≠ b q := by
      intro e q he
      have h := congrArg Prod.fst (hpi he)
      exact (Fin.castSucc_ne_last q.1) h.symm
    obtain ⟨sₙ,hsₙI,hsₙQ,-,hsp,hnewnew,hnewold,hcross,-⟩ := exists_fixed_port_star a b
      (fun _ ↦ Circle.norm_coe _) (fun q ↦ hp (q.1.castSucc,q.2)) hab hne
      (fun e ↦ p (Fin.last m,e)) (fun e ↦ hp (Fin.last m,e))
      (fun e f he ↦ congrArg Prod.snd (hpi he)) hnewa hnewb
      (hQ.union (finite_range fun i ↦ (ee (s i) : ℂ)))
      (fun e ↦ Or.inl (hpQ (Fin.last m,e))) hs hslen
    have hsₙne : ∀ j, (ee sₙ : ℂ) ≠ (ee (s j) : ℂ) :=
      fun j he ↦ hsₙQ (.inr ⟨j,he.symm⟩)
    refine ⟨Fin.snoc s sₙ,?_,?_,?_,?_,?_⟩
    · intro i
      exact Fin.lastCases (by simpa using hsₙI) (fun j ↦ by simpa using hsI j) i
    · intro i
      exact Fin.lastCases (by simpa using (fun h ↦ hsₙQ (.inl h)))
        (fun j ↦ by simpa using hsQ j) i
    · intro i j hij
      by_cases hi : i = Fin.last m
      · subst i
        obtain ⟨j,rfl⟩ := exists_old_star_index j (Ne.symm hij)
        simpa using hsₙne j
      · obtain ⟨i,rfl⟩ := exists_old_star_index i hi
        by_cases hj : j = Fin.last m
        · subst j
          simpa using (Ne.symm (hsₙne i))
        · obtain ⟨j,rfl⟩ := exists_old_star_index j hj
          simpa using hsne i j (fun he ↦ hij (congrArg Fin.castSucc he))
    · intro i j e f hij
      by_cases hi : i = Fin.last m
      · subst i
        by_cases hj : j = Fin.last m
        · subst j
          exact (by simpa using hnewnew e f (fun he ↦ hij (Prod.ext rfl he)))
        · obtain ⟨j,rfl⟩ := exists_old_star_index j hj
          simpa using hnewold e (j,f)
      · obtain ⟨i,rfl⟩ := exists_old_star_index i hi
        by_cases hj : j = Fin.last m
        · subst j
          simpa using Ne.symm (hnewold f (i,e))
        · obtain ⟨j,rfl⟩ := exists_old_star_index j hj
          have h : (i,e) ≠ (j,f) := fun he ↦ hij (congrArg (fun q : Fin m × κ ↦ (q.1.castSucc,q.2)) he)
          simpa using hline i j e f h
    · intro i j l e f g hij hjl hil x hx
      by_cases hi : i = Fin.last m
      · subst i
        obtain ⟨j,rfl⟩ := exists_old_star_index j (Ne.symm hij)
        obtain ⟨l,rfl⟩ := exists_old_star_index l (Ne.symm hil)
        have hjl' : j ≠ l := fun he ↦ hjl (congrArg Fin.castSucc he)
        have hd := hcross e (j,f) (l,g) (fun he ↦ hjl' (congrArg Prod.fst he))
        exact disjoint_left.mp hd (by simpa using hx.1) (by simpa using hx.2)
      · obtain ⟨i,rfl⟩ := exists_old_star_index i hi
        by_cases hj : j = Fin.last m
        · subst j
          obtain ⟨l,rfl⟩ := exists_old_star_index l (Ne.symm hjl)
          have hil' : i ≠ l := fun he ↦ hil (congrArg Fin.castSucc he)
          have hd := hcross f (i,e) (l,g) (fun he ↦ hil' (congrArg Prod.fst he))
          exact disjoint_left.mp hd (by simpa using hx.2.1) (by simpa using And.intro hx.1 hx.2.2)
        · obtain ⟨j,rfl⟩ := exists_old_star_index j hj
          by_cases hl : l = Fin.last m
          · subst l
            have hij' : i ≠ j := fun he ↦ hij (congrArg Fin.castSucc he)
            have hd := hcross g (i,e) (j,f) (fun he ↦ hij' (congrArg Prod.fst he))
            exact disjoint_left.mp hd (by simpa using hx.2.2) (by simpa using And.intro hx.1 hx.2.1)
          · obtain ⟨l,rfl⟩ := exists_old_star_index l hl
            exact hthree i j l e f g (fun he ↦ hij (congrArg Fin.castSucc he))
              (fun he ↦ hjl (congrArg Fin.castSucc he)) (fun he ↦ hil (congrArg Fin.castSucc he)) x
              (by simpa using hx)

end GraphMinor.GM05
