module

public import GraphMinor.LRPlanarity.DefsContour
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.LRPlanarity.TreeNeighborhoodBoundaryOrder
import GraphMinor.LRPlanarity.ExteriorK5Construction
import GraphMinor.Surface.ArcTools

/-!
# Nonalternation in a boundary traversal list

Part IV, Section 7c of the planarity note excludes alternating port pairs
by constructing a plane K5. A list in strict boundary-parameter order
turns alternating list indices into four ordered boundary parameters.
Choose the earlier end of each exterior arc first. The ordered-parameter
crossing lemma and the proved exterior obstruction then rule out both
possible interleavings.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7c: two disjoint exterior lines cannot have alternating
endpoint indices in a list read in strict boundary traversal order. -/
theorem not_alternating_boundary_indices {α : Type*} [DecidableEq α]
    {D A B : Set ℂ} (hD : IsClosedDisc D) (word : List α)
    (port : α → ℂ) (parameter : α → ℝ) (f : ℝ → ℂ)
    (hf : Continuous f) (hIco : InjOn f (Ico (0 : ℝ) 1)) (hIoc : InjOn f (Ioc (0 : ℝ) 1))
    (himage : f '' Icc (0 : ℝ) 1 = frontier D)
    (hparameter : ∀ p ∈ word, parameter p ∈ Ioo (0 : ℝ) 1 ∧ f (parameter p) = port p)
    (hsorted : word.Pairwise (fun p q => parameter p < parameter q))
    {a c b d : α} (ha : a ∈ word) (hc : c ∈ word) (hb : b ∈ word) (hd : d ∈ word)
    (hA : IsLineWithEnds A (port a) (port c)) (hB : IsLineWithEnds B (port b) (port d))
    (hAD : A ∩ D = {port a,port c}) (hBD : B ∩ D = {port b,port d}) (hAB : Disjoint A B) :
    ¬ AlternatingIndices (word.idxOf a) (word.idxOf c) (word.idxOf b) (word.idxOf d) := by
  have hθ : ∀ p ∈ word, ∀ q ∈ word, word.idxOf p < word.idxOf q → parameter p < parameter q := by
    intro p hp q hq hidx
    have hpidx := List.idxOf_lt_length_of_mem hp
    have hqidx := List.idxOf_lt_length_of_mem hq
    have h := List.pairwise_iff_getElem.mp hsorted (word.idxOf p) (word.idxOf q) hpidx hqidx hidx
    simpa only [List.getElem_idxOf hpidx,List.getElem_idxOf hqidx] using h
  have ordered : ∀ (X Y : Set ℂ) (p q r s : α), p ∈ word → q ∈ word → r ∈ word → s ∈ word →
      word.idxOf p < word.idxOf q → word.idxOf q < word.idxOf r → word.idxOf r < word.idxOf s →
      IsLineWithEnds X (port p) (port r) → IsLineWithEnds Y (port q) (port s) →
      X ∩ D = {port p,port r} → Y ∩ D = {port q,port s} → Disjoint X Y → False := by
    intro X Y p q r s hp hq hr hs hpq hqr hrs hX hY hXD hYD hXY
    have hcross := pairsCrossOn_of_ordered_boundary_parameters hf hIco hIoc
      (hparameter p hp).1.1 (hθ p hp q hq hpq) (hθ q hq r hr hqr)
      (hθ r hr s hs hrs) (hparameter s hs).1.2
    rw [himage,(hparameter p hp).2,(hparameter q hq).2,
      (hparameter r hr).2,(hparameter s hs).2] at hcross
    exact not_pairsCrossOn_of_exterior_lines hD hX hY hXD hYD hXY hcross
  have orient : ∀ (X : Set ℂ) (p q : α), p ∈ word → q ∈ word →
      IsLineWithEnds X (port p) (port q) → X ∩ D = {port p,port q} →
      ∃ u v : α, u ∈ word ∧ v ∈ word ∧
        word.idxOf u = min (word.idxOf p) (word.idxOf q) ∧
        word.idxOf v = max (word.idxOf p) (word.idxOf q) ∧
        IsLineWithEnds X (port u) (port v) ∧ X ∩ D = {port u,port v} := by
    intro X p q hp hq hX hXD
    rcases le_total (word.idxOf p) (word.idxOf q) with hpq | hqp
    · exact ⟨p,q,hp,hq,(min_eq_left hpq).symm,(max_eq_right hpq).symm,hX,hXD⟩
    · exact ⟨q,p,hq,hp,(min_eq_right hqp).symm,(max_eq_left hqp).symm,hX.symm,
        hXD.trans (Set.pair_comm _ _)⟩
  obtain ⟨a₀,a₁,ha₀,ha₁,hia₀,hia₁,hA',hAD'⟩ := orient A a c ha hc hA hAD
  obtain ⟨b₀,b₁,hb₀,hb₁,hib₀,hib₁,hB',hBD'⟩ := orient B b d hb hd hB hBD
  intro halt
  change (min _ _ < min _ _ ∧ min _ _ < max _ _ ∧ max _ _ < max _ _) ∨
    (min _ _ < min _ _ ∧ min _ _ < max _ _ ∧ max _ _ < max _ _) at halt
  rw [← hia₀,← hia₁,← hib₀,← hib₁] at halt
  rcases halt with ⟨hfirst,hmiddle,hlast⟩ | ⟨hfirst,hmiddle,hlast⟩
  · exact ordered A B a₀ b₀ a₁ b₁ ha₀ hb₀ ha₁ hb₁ hfirst hmiddle hlast hA' hB' hAD' hBD' hAB
  · exact ordered B A b₀ a₀ b₁ a₁ hb₀ ha₀ hb₁ ha₁ hfirst hmiddle hlast hB' hA' hBD' hAD' hAB.symm

end GraphMinor.LRPlanarity
