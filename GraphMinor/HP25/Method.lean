module

public import GraphMinor.HP25.Prop53
import GraphMinor.HP25.Alternate
import GraphMinor.HP25.CrossTools
import GraphMinor.HP25.CycleEdges
import GraphMinor.HP25.Lemma33
import GraphMinor.HP25.Lemma43Tools

/-!
# Algorithm 5.1: the three steps of the general method are correct

Humeau and Pous, Section 5.1 (page 18), Algorithm 5.1 ("General method for the two disjoint
paths decision problem"):
```
 2:     if there are no C-paths between non-consecutive vertices of C then
 3:         return False
 ...
 6:         if P does not separate C in G then
 7:             return True
 ...
 9:             G, P ← P_completion(G, C, P)
10:             G_i, C_i ← two subinstances induced by G, P and C
11:             return (2DP(G_1,C_1) ∨ 2DP(G_2,C_2))
```
and "By Proposition 5.2 and induction on the size of the recursive instances, the method is both
correct and terminating."

We prove that each step gives the right answer:
* line 3: a crossed cycle has a `C`-path between non-consecutive vertices
  (`exists_tPath_of_isCrossed`);
* line 7: if `P` does not separate `P̊₁` from `P̊₂`, then `C` is crossed (`isCrossed_of_not_separates`);
* line 11: after a `P`-completion `F` with path `P'`, if `P'` separates, then `C` is crossed in `G`
  if and only if one of the two subinstances of `G + F` along `P'` is crossed
  (`isCrossed_iff_of_completion`, from Proposition 5.2 and the safety of `F`). If `P'` does not
  separate in `G + F`, then line 7 applies to `G + F`, and `C` is crossed in `G` since `F` is safe.
  The paper does not check that `P'` separates; we add the check.
The subinstances are smaller: the side of `A` misses `B`, and the side of `B` misses `A`
(`SplitSetting.B_not_mem_S₁`, `SplitSetting.A_not_mem_S₂`).
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-- **Line 3 of Algorithm 5.1.** If `C` is crossed, then some `C`-path joins two vertices of `C`
that are not consecutive: `C = a A b B` up to rotation with `A` and `B` not empty. -/
theorem exists_tPath_of_isCrossed {C : List V} (h : IsCrossed G C) :
    ∃ (a b : V) (A B : List V) (k : ℕ) (P : G.Walk a b), C.rotate k = a :: A ++ b :: B ∧
      A ≠ [] ∧ B ≠ [] ∧ IsTPath G C P := by
  obtain ⟨a, b, c, d, Q, R, hQR⟩ := h
  obtain ⟨k, L₁, L₂, hrot, hc, hd⟩ := hQR.alternate
  exact ⟨a, b, L₁, L₂, k, Q, hrot, List.ne_nil_of_mem hc, List.ne_nil_of_mem hd, hQR.2.1⟩

/-- **Line 7 of Algorithm 5.1.** Let `C = a A b B` up to rotation and `P` a `C`-path from `a` to
`b`. If `P` does not separate `A` from `B`, then `C` is crossed: a path from `A` to `B` that
avoids `P` contains a `C`-path from `A` to `B`, which crosses `P`. -/
theorem isCrossed_of_not_separates {C : List V} {a b : V} {A B : List V}
    {k : ℕ} (hrot : C.rotate k = a :: A ++ b :: B) {P : G.Walk a b} (hP : IsTPath G C P)
    (hns : ¬ Separates G {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B}) : IsCrossed G C := by
  classical
  unfold Separates at hns
  push Not at hns
  obtain ⟨u, hu, w, hw, p, hp⟩ := hns
  change u ∈ A at hu
  change w ∈ B at hw
  have hmemC : ∀ v, v ∈ a :: A ++ b :: B → v ∈ C := fun v hv =>
    List.mem_rotate.mp (hrot ▸ hv)
  -- the part of `p` up to its first vertex in `B`
  obtain ⟨s, hs, p₁, h1, h2, -⟩ := exists_first_hit {v | v ∈ B} p hw
  -- from there back to the last vertex of `A` before it
  obtain ⟨t, ht, p₂, h3, h4, -⟩ := exists_first_hit {v | v ∈ A} p₁.reverse (by exact hu)
  change s ∈ B at hs
  change t ∈ A at ht
  have hp₂ : ∀ y ∈ p₂.support, y ∈ p.support ∧ (y ≠ s → y ∉ B) := fun y hy => by
    have hy' : y ∈ p₁.support := by
      have := h3 y hy
      rwa [Walk.support_reverse, List.mem_reverse] at this
    exact ⟨h1 y hy', h2 y hy'⟩
  obtain ⟨q, hq, hqs, hqin⟩ := exists_path_of_walk p₂ {v | v ∈ C} fun y hy hys hyt hyC => by
    obtain ⟨hyp, hyB⟩ := hp₂ y hy
    have hyP := hp y hyp
    change y ∈ C at hyC
    rw [← List.mem_rotate (n := k), hrot] at hyC
    simp only [List.cons_append, List.mem_cons, List.mem_append] at hyC
    rcases hyC with rfl | h | rfl | h
    · exact hyP P.start_mem_support
    · exact h4 y hy hyt h
    · exact hyP P.end_mem_support
    · exact hyB hys h
  have hqT : IsTPath G C q :=
    ⟨hq, hmemC s (by simp [hs]), hmemC t (by simp [ht]), fun y hy h1 h2 =>
      ⟨hqin y hy h1 h2, hqin y hy h1 h2⟩⟩
  refine isCrossed_of_alternate hrot ht hs P q.reverse hP hqT.reverse fun x hx1 hx2 => ?_
  rw [Walk.support_reverse, List.mem_reverse] at hx2
  exact hp x (hp₂ x (hqs x hx2)).1 hx1

namespace SplitSetting

variable {C : List V} {a b : V} {A B m : List V} {k : ℕ} {P : G.Walk a b}
  {G₁ G₂ : SimpleGraph V} {S₁ S₂ : Set V}

/-- The side of `A` misses `B`. -/
theorem B_not_mem_S₁ (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) {v : V} (hv : v ∈ B) :
    v ∉ S₁ := fun h1 => by
  have h12 : v ∈ S₁ ∩ S₂ := ⟨h1, hs.sub₂ v (by simp [hv])⟩
  rw [hs.comp.2.2.2.2.1] at h12
  exact hs.AB_not_mem (List.mem_append_right _ hv) h12

/-- The side of `B` misses `A`. -/
theorem A_not_mem_S₂ (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) {v : V} (hv : v ∈ A) :
    v ∉ S₂ := fun h2 => by
  have h12 : v ∈ S₁ ∩ S₂ := ⟨hs.sub₁ v (by simp [hv]), h2⟩
  rw [hs.comp.2.2.2.2.1] at h12
  exact hs.AB_not_mem (List.mem_append_left _ hv) h12

end SplitSetting

/-- **Line 11 of Algorithm 5.1.** Let `F` be safe for `C`, and `P' = a m b` a `C`-path of
`G + F` that separates `A` from `B` and whose vertices are all on both sides. If `G + F` is the
path composition along `P'` of `G₁ ⊇ a A b` and `G₂ ⊇ b B a` (Proposition 5.1), then `C` is crossed
in `G` if and only if `a A b m⁻¹` is crossed in `G₁` or `b B a m` is crossed in `G₂`. -/
theorem isCrossed_iff_of_completion [Finite V] {C : List V}
    (hC : IsCycleList G C) {a b : V} {A B m : List V} {k : ℕ}
    (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ []) (hB : B ≠ []) {F : SimpleGraph V}
    (hsafe : IsSafe G F C) {P' : (G ⊔ F).Walk a b} (hP' : IsTPath (G ⊔ F) C P')
    (hm : P'.support = a :: m ++ [b]) (hsides : OnBothSides (G ⊔ F) C A B P')
    (hsep : Separates (G ⊔ F) {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B})
    {G₁ G₂ : SimpleGraph V} {S₁ S₂ : Set V}
    (hcomp : IsPathComposition (G ⊔ F) G₁ G₂ S₁ S₂ P'.support)
    (hchain₁ : (a :: A ++ [b]).IsChain G₁.Adj) (hsub₁ : ∀ v ∈ a :: A ++ [b], v ∈ S₁)
    (hchain₂ : (b :: B ++ [a]).IsChain G₂.Adj) (hsub₂ : ∀ v ∈ b :: B ++ [a], v ∈ S₂) :
    IsCrossed G C ↔ IsCrossed G₁ (a :: A ++ b :: m.reverse) ∨ IsCrossed G₂ (b :: B ++ a :: m) := by
  have hs : SplitSetting (G ⊔ F) C a b A B m k P' G₁ G₂ S₁ S₂ :=
    ⟨hC.mono le_sup_left, hrot, hA, hB, hP', hm, hsep, hcomp, hchain₁, hsub₁, hchain₂, hsub₂⟩
  rw [← prop_5_2 hs hsides]
  exact ⟨fun h => h.mono le_sup_left, hsafe⟩

end GraphMinor.HP25
