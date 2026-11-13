module

public import GraphMinor.Compute.GM06LoopErasureStackOps
public import GraphMinor.Compute.Algorithm74Lift

import GraphMinor.Compute.CrossingOpsBasic

/-!
# Popping a closed subwalk from the loop-erasure stacks

Section 15 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) finds a
repeated vertex at position j and pops until only the first j darts remain.
Each removed vertex has its position cleared before the corresponding
dart is discarded. This loop proves the exact truncated stacks and
position table, preserving the physical stack arrays. The cost counts
each removed dart once.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Pop while the vertex stack extends beyond the repeated vertex. -/
def gm06ErasePopCond : Expr := exprLt (.op .add (.reg 613) (.const 1)) (.reg 614)

/-- Remove one vertex, clear its position, and discard its incoming dart. -/
def gm06ErasePopBody : Cmd :=
  .seq (stackPop 604 614 617)
    (.seq (.write 606 (.reg 617) (.reg 616)) (stackPop 605 615 618))

/-- The repeated-vertex truncation loop. -/
def gm06ErasePopLoop : Cmd := .while gm06ErasePopCond gm06ErasePopBody

private theorem pop_cond_eval {w j count : ℕ} (s : State) (hw : 1 < 2 ^ w)
    (hj : j + 1 < 2 ^ w) (hc : count < 2 ^ w)
    (h613 : s.regs 613 = j) (h614 : s.regs 614 = count) :
    gm06ErasePopCond.eval w s = some (if j + 1 < count then 1 else 0) := by
  exact eval_exprLt hw
    (GraphMinor.Compute.Crossing.eval_add (GraphMinor.Compute.Crossing.eval_reg h613 (by omega))
      (GraphMinor.Compute.Crossing.eval_const hw) hj)
    (GraphMinor.Compute.Crossing.eval_reg h614 hc)

/-- Repeated-vertex truncation returns precisely the first j darts and
their vertex stack. Each removed vertex position is actually cleared. -/
theorem gm06ErasePopLoop_exec {w n cap absent source : ℕ} (head : ℕ → ℕ) (darts : List ℕ)
    (j : ℕ) (s : State) (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hcap : cap + 1 < 2 ^ w)
    (habs : absent < 2 ^ w) (hj : j ≤ darts.length)
    (hnd : (gm06WalkVertices head source darts).Nodup)
    (hvertices : ∀ v ∈ gm06WalkVertices head source darts, v < n)
    (hdarts : ∀ d ∈ darts, d < 2 ^ w)
    (h604 : IsStack 604 614 (cap + 1) (gm06WalkVertices head source darts) s)
    (h605 : IsStack 605 615 cap darts s)
    (h606 : s.arrs 606 = gm06StackPositions n absent (gm06WalkVertices head source darts))
    (h613 : s.regs 613 = j) (h616 : s.regs 616 = absent) :
    ∃ sf t, Exec w gm06ErasePopLoop s sf t ∧ t ≤ 5 + 22 * (darts.length - j) ∧
      Keeps [614, 617, 615, 618] [606] s sf ∧
      IsStack 604 614 (cap + 1) (gm06WalkVertices head source (darts.take j)) sf ∧
      IsStack 605 615 cap (darts.take j) sf ∧
      sf.arrs 606 = gm06StackPositions n absent (gm06WalkVertices head source (darts.take j)) := by
  induction darts using List.reverseRecOn generalizing j s with
  | nil =>
    have hj0 : j = 0 := by simp only [List.length_nil] at hj; omega
    cases hj0
    have htop : s.regs 614 = 1 := by simpa only [gm06WalkVertices, List.map_nil, List.length_singleton] using h604.2.2.1
    have hc := pop_cond_eval s hw hw hw h613 htop
    refine ⟨s, 5, .while_false (by simpa only [Nat.zero_add, Nat.lt_irrefl, ↓reduceIte] using hc),
      by simp, Keeps.refl _ _ _, ?_, ?_, ?_⟩
    · simpa only [List.take_nil] using h604
    · simpa only [List.take_nil] using h605
    · simpa only [List.take_nil] using h606
  | append_singleton darts d ih =>
    have hlenCap : darts.length + 1 ≤ cap := by simpa only [List.length_append, List.length_singleton] using h605.2.1
    have htop : s.regs 614 = darts.length + 2 := by
      simpa only [gm06WalkVertices, List.length_cons, List.length_map, List.length_append,
        List.length_singleton, List.length_nil, Nat.add_assoc] using h604.2.2.1
    have hc := pop_cond_eval s hw (by simp only [List.length_append, List.length_singleton] at hj; omega)
      (by omega) h613 htop
    by_cases hfull : j = (darts ++ [d]).length
    · refine ⟨s, 5, .while_false (by
        have hj' : j = darts.length + 1 := by simpa only [List.length_append, List.length_singleton] using hfull
        simpa only [hj', Nat.add_assoc, Nat.lt_irrefl, ↓reduceIte] using hc),
        by simp only [hfull, Nat.sub_self, Nat.mul_zero]; omega, Keeps.refl _ _ _, ?_, ?_, ?_⟩
      · simpa only [hfull, List.take_length] using h604
      · simpa only [hfull, List.take_length] using h605
      · simpa only [hfull, List.take_length] using h606
    · have hj' : j ≤ darts.length := by simp only [List.length_append, List.length_singleton] at hj hfull; omega
      let vertices := gm06WalkVertices head source darts
      have hverticesEq : gm06WalkVertices head source (darts ++ [d]) = vertices ++ [head d] :=
        gm06WalkVertices_append_one head source darts d
      have hndParts := List.nodup_append.mp (hverticesEq ▸ hnd)
      have hv : head d < n := hvertices (head d) (by rw [hverticesEq]; exact List.mem_append_right _ List.mem_cons_self)
      have hd : d < 2 ^ w := hdarts d (List.mem_append_right _ List.mem_cons_self)
      have hnot : head d ∉ vertices := by
        intro hm
        exact hndParts.2.2 _ hm _ List.mem_cons_self rfl
      obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁, hv₁⟩ := gm06StackPop_exec vertices s
        (by decide : 617 ≠ 614) hw hcap (hv.trans hn) (by simpa only [hverticesEq] using h604)
      let s₂ := s₁.writeArr 606 (head d) absent
      have hpos₁ : s₁.arrs 606 = gm06StackPositions n absent (vertices ++ [head d]) :=
        (hk₁.2 606 (by simp)).trans (h606.trans (congrArg (gm06StackPositions n absent) hverticesEq))
      have he₂ : Exec w (.write 606 (.reg 617) (.reg 616)) s₁ s₂ 3 :=
        .write (GraphMinor.Compute.Crossing.eval_reg hv₁ (hv.trans hn))
          (GraphMinor.Compute.Crossing.eval_reg ((hk₁.1 616 (by decide)).trans h616) habs)
          (by simpa only [hpos₁, gm06StackPositions_length] using hv)
      have hpos₂ : s₂.arrs 606 = gm06StackPositions n absent vertices := by
        change (s₁.arrs 606).set (head d) absent = _
        rw [hpos₁, gm06StackPositions_pop vertices hv hnot]
      have h604₂ : IsStack 604 614 (cap + 1) vertices s₂ :=
        hd₁.of_preserve (by simp [s₂, State.writeArr]) rfl
      have h605₂ : IsStack 605 615 cap (darts ++ [d]) s₂ :=
        h605.of_preserve ((by simpa [s₂, State.writeArr] using hk₁.2 605 (by simp)))
          (by simpa [s₂, State.writeArr] using hk₁.1 615 (by decide))
      obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hd₃, _⟩ := gm06StackPop_exec darts s₂
        (by decide : 618 ≠ 615) hw (by omega) hd h605₂
      have hk₁₂ : Keeps [614, 617, 615, 618] [606] s s₂ :=
        (hk₁.mono (by simp) (by simp)).writeArr (by simp) _ _
      have hk₁₃ : Keeps [614, 617, 615, 618] [606] s s₃ :=
        hk₁₂.trans hk₃ (by simp) (by simp)
      have h604₃ := h604₂.of_preserve (hk₃.2 604 (by simp)) (hk₃.1 614 (by decide))
      have hpos₃ := (hk₃.2 606 (by simp)).trans hpos₂
      obtain ⟨sf, tf, hef, htf, hkf, hVf, hDf, hPf⟩ := ih j s₃ hj' hndParts.1
        (fun v hv => hvertices v (by rw [hverticesEq]; exact List.mem_append_left _ hv))
        (fun d hd => hdarts d (List.mem_append_left _ hd)) h604₃ hd₃ hpos₃
        ((hk₁₃.1 613 (by decide)).trans h613) ((hk₁₃.1 616 (by decide)).trans h616)
      refine ⟨sf, 5 + (t₁ + (3 + t₃)) + tf, .while_true
        (by simpa only [show j + 1 < darts.length + 2 by omega, ↓reduceIte] using hc) (by decide)
        (.seq he₁ (.seq he₂ he₃)) hef, ?_,
        hk₁₃.trans hkf (fun _ h => h) (fun _ h => h), ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · simpa only [List.take_append_of_le_length hj'] using hVf
      · simpa only [List.take_append_of_le_length hj'] using hDf
      · simpa only [List.take_append_of_le_length hj'] using hPf

end GraphMinor.Compute
