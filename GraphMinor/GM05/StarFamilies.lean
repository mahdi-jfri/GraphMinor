module

public import GraphMinor.GM05.StarGeneralPosition
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Finite families of stars with only pairwise crossings

Add the stars one at a time using the local selection lemma. Their
supporting lines remain distinct. A point on rays of three different
stars cannot occur: when the last of those stars was added, its rays
avoided intersections of the two older lines. This is the finite local
arrangement used for GM V, (8.14).
-/

public section
namespace GraphMinor.GM05
open Set Surface

private theorem exists_castSucc_of_ne_last {m : ℕ} (i : Fin (m+1)) (hi : i≠Fin.last m) :
    ∃ j : Fin m,j.castSucc=i := by
  exact Fin.lastCases (fun h ↦ (h rfl).elim) (fun j _ ↦ ⟨j,rfl⟩) i hi

/-- The local finite family for GM V, proof of (8.14), page 113.
Rays in different stars have no triple meeting, and all ray lines are
distinct. Each centre and each port lies in its prescribed short arc. -/
theorem exists_star_family_general_position (m k : ℕ)
    (c d : Fin m → ℝ) (hcd : ∀ i,c i<d i) (hcdlen : ∀ i,d i ≤ c i+1)
    (u v : Fin m → Fin k → ℝ) (huv : ∀ i e,u i e<v i e) (hlen : ∀ i e,v i e≤u i e+1)
    (hports : ∀ i,Pairwise (fun e f ↦ Disjoint
      ((fun t : ℝ ↦ (ee t : ℂ)) '' Ioo (u i e) (v i e))
      ((fun t : ℝ ↦ (ee t : ℂ)) '' Ioo (u i f) (v i f)))) :
    ∃ s : Fin m → ℝ, ∃ t : Fin m → Fin k → ℝ,
      (∀ i,s i∈Ioo (c i) (d i)) ∧
      (∀ i e,t i e∈Ioo (u i e) (v i e) ∧ (ee (t i e) : ℂ)≠(ee (s i) : ℂ)) ∧
      (∀ i j e f,(i,e)≠(j,f) →
        line[ℝ,(ee (s i) : ℂ),(ee (t i e) : ℂ)]≠line[ℝ,(ee (s j) : ℂ),(ee (t j f) : ℂ)]) ∧
      ∀ i j l e f g,i≠j → j≠l → i≠l → ∀ x : ℂ,
        ¬(x∈(line[ℝ,(ee (s i) : ℂ),(ee (t i e) : ℂ)] : Set ℂ) ∧
          x∈(line[ℝ,(ee (s j) : ℂ),(ee (t j f) : ℂ)] : Set ℂ) ∧
          x∈(line[ℝ,(ee (s l) : ℂ),(ee (t l g) : ℂ)] : Set ℂ)) := by
  classical
  induction m with
  | zero => exact ⟨Fin.elim0,Fin.elim0,fun i ↦ i.elim0,fun i ↦ i.elim0,fun i ↦ i.elim0,fun i ↦ i.elim0⟩
  | succ m ih =>
    obtain ⟨s,t,hs,ht,hne,hthree⟩ := ih (fun i ↦ c i.castSucc) (fun i ↦ d i.castSucc)
      (fun i ↦ hcd i.castSucc) (fun i ↦ hcdlen i.castSucc)
      (fun i ↦ u i.castSucc) (fun i ↦ v i.castSucc)
      (fun i ↦ huv i.castSucc) (fun i ↦ hlen i.castSucc) (fun i ↦ hports i.castSucc)
    let a : Fin m × Fin k → ℂ := fun p ↦ ee (s p.1)
    let b : Fin m × Fin k → ℂ := fun p ↦ ee (t p.1 p.2)
    have hlines : ∀ p q,p≠q → line[ℝ,a p,b p]≠line[ℝ,a q,b q] := by
      rintro ⟨i,e⟩ ⟨j,f⟩ hp
      exact hne i j e f hp
    obtain ⟨s₀,hs₀,t₀,ht₀,-,hnew,hnewnew,-,hcross,-⟩ :=
      exists_star_in_general_position a b (fun _ ↦ Circle.norm_coe _) hlines
        (hcd (Fin.last m)) (hcdlen (Fin.last m))
        (u (Fin.last m)) (v (Fin.last m)) (huv (Fin.last m)) (hlen (Fin.last m)) (hports (Fin.last m))
    refine ⟨Fin.snoc s s₀,Fin.snoc t t₀,?_,?_,?_,?_⟩
    · intro i
      exact Fin.lastCases (by simpa using hs₀) (fun j ↦ by simpa using hs j) i
    · intro i e
      exact Fin.lastCases (by simpa using ht₀ e) (fun j ↦ by simpa using ht j e) i
    · intro i j e f hij
      by_cases hi : i=Fin.last m
      · subst i
        by_cases hj : j=Fin.last m
        · subst j
          have hef : e≠f := fun he ↦ hij (by rw [he])
          simpa using hnewnew e f hef
        · obtain ⟨j,rfl⟩ := exists_castSucc_of_ne_last j hj
          simpa using hnew e (j,f)
      · obtain ⟨i,rfl⟩ := exists_castSucc_of_ne_last i hi
        by_cases hj : j=Fin.last m
        · subst j
          simpa using (hnew f (i,e)).symm
        · obtain ⟨j,rfl⟩ := exists_castSucc_of_ne_last j hj
          have hp : (i,e)≠(j,f) := by
            rintro ⟨rfl,rfl⟩
            exact hij rfl
          simpa using hne i j e f hp
    · intro i j l e f g hij hjl hil x hx
      by_cases hi : i=Fin.last m
      · subst i
        obtain ⟨j,rfl⟩ := exists_castSucc_of_ne_last j hij.symm
        obtain ⟨l,rfl⟩ := exists_castSucc_of_ne_last l hil.symm
        have hjl' : j≠l := fun he ↦ hjl (congrArg Fin.castSucc he)
        have hd := hcross e (j,f) (l,g) (fun he ↦ hjl' (congrArg Prod.fst he))
        exact disjoint_left.mp hd (by simpa using hx.1) (by simpa using hx.2)
      · obtain ⟨i,rfl⟩ := exists_castSucc_of_ne_last i hi
        by_cases hj : j=Fin.last m
        · subst j
          obtain ⟨l,rfl⟩ := exists_castSucc_of_ne_last l hjl.symm
          have hil' : i≠l := fun he ↦ hil (congrArg Fin.castSucc he)
          have hd := hcross f (i,e) (l,g) (fun he ↦ hil' (congrArg Prod.fst he))
          exact disjoint_left.mp hd (by simpa using hx.2.1) (by simpa using And.intro hx.1 hx.2.2)
        · obtain ⟨j,rfl⟩ := exists_castSucc_of_ne_last j hj
          by_cases hl : l=Fin.last m
          · subst l
            have hij' : i≠j := fun he ↦ hij (congrArg Fin.castSucc he)
            have hd := hcross g (i,e) (j,f) (fun he ↦ hij' (congrArg Prod.fst he))
            exact disjoint_left.mp hd (by simpa using hx.2.2) (by simpa using And.intro hx.1 hx.2.1)
          · obtain ⟨l,rfl⟩ := exists_castSucc_of_ne_last l hl
            exact hthree i j l e f g (fun he ↦ hij (congrArg Fin.castSucc he))
              (fun he ↦ hjl (congrArg Fin.castSucc he)) (fun he ↦ hil (congrArg Fin.castSucc he)) x
              (by simpa using hx)

end GraphMinor.GM05
