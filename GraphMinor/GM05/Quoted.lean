module

public import GraphMinor.GM05.Defs
import GraphMinor.GM01.DisconnectedSeparators
import GraphMinor.GM01.MengerSeparators

/-!
# Graph Minors V: the two results quoted from Graph Minors I

This file proves (3.1) and (4.3) from Graph Minors I, (2.9) and (2.8).
The finite index sets in (3.1) are relabelled as finsets. For (4.3), the
zero-component case is handled directly before applying (2.8).
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Graph Set GM01

universe u

/-- Graph Minors V, (3.1) (page 95), proved from Graph Minors I, (2.9) (`GM01.theorem_2_9_simple`). -/
theorem theorem_3_1_simple : Statement31.{u} := by
  classical
  intro V G θ n hθ heven hfin hG B hB_le hB_conn hB_disj V' hV' r
  rcases GM01.theorem_2_9_simple hθ heven hfin hG hV' B hB_le hB_conn hB_disj (r := r) with
    ⟨J, P, hJ_card, hP_fromTo, hP_disj, hP_int⟩ | ⟨X, J, hX_sub, hXJ_card, hsep⟩
  · left
    let J' : Finset (Fin n) := J.toFinset
    let e : J' ≃ J :=
      { toFun := fun j ↦ ⟨j.1, Set.mem_toFinset.1 j.2⟩
        invFun := fun j ↦ ⟨j.1, Set.mem_toFinset.2 j.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    refine ⟨J', fun j ↦ P (e j), ?_, ?_, ?_, ?_⟩
    · rw [← Set.ncard_eq_toFinset_card' J, hJ_card]
    · intro j
      exact hP_fromTo (e j)
    · intro j₁ j₂ hne
      exact hP_disj (e.injective.ne hne)
    · intro j
      have hunion_eq : (⋃ j' ∈ J', (B j').verts) = ⋃ j' ∈ J, (B j').verts := by
        ext x
        simp [J']
      rw [hunion_eq]
      exact hP_int (e j)
  · right
    let J' : Finset (Fin n) := J.toFinset
    refine ⟨X, J', hX_sub, ?_, ?_⟩
    · rw [← Set.ncard_eq_toFinset_card' J]
      exact hXJ_card
    · intro j hj
      have hj' : j ∉ J := by simpa [J'] using hj
      exact hsep j hj'

/-- Alias for `theorem_3_1_simple`. -/
theorem statement_3_1 : Statement31.{u} :=
  theorem_3_1_simple

/-- Graph Minors V, (4.3) (page 98), proved from Graph Minors I, (2.8) (`GM01.theorem_2_8_simple`). -/
theorem theorem_4_3_simple : Statement43.{u} := by
  classical
  intro V G θ m n d hθ heven hdn hfin hG A₁ A₂ hA₁ hA₂ D hD_le hD_disj hD_comp hex_paths hD_sep
  rcases hex_paths with ⟨P, hP_fam⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd_pos
  · have hn_pos : 0 < n := by omega
    right
    have hm_zero : m = 0 := by
      by_contra hm_ne
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_ne
      let k₀ : Fin m := ⟨0, hm_pos⟩
      have hD₀_comp : numComponents (D k₀) ≤ 0 := hD_comp k₀
      have hD₀_fin : (D k₀).verts.Finite := hfin.subset (hD_le k₀).1
      have : Finite (D k₀).verts := hD₀_fin.to_subtype
      have : Finite (D k₀).coe.ConnectedComponent := Quot.finite _
      have hD₀_empty : (D k₀).verts = ∅ := by
        ext v
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hv
        have hne : Nonempty (D k₀).coe.ConnectedComponent :=
          ⟨(D k₀).coe.connectedComponentMk ⟨v, hv⟩⟩
        have hpos : 0 < numComponents (D k₀) :=
          Nat.card_pos
        omega
      let i₀ : Fin n := ⟨0, hn_pos⟩
      have havoid : (P i₀).Avoids (D k₀).verts := by
        rw [Path.Avoids, hD₀_empty]
        exact disjoint_bot_right
      exact hD_sep k₀ (P i₀) (hP_fam.1 i₀) havoid
    rw [hm_zero]
    have hθ_pos : 0 < θ ^ 2 := by
      rw [sq]
      exact Nat.mul_pos (by omega) (by omega)
    simp only [zero_mul, mul_zero, Nat.zero_div, pow_zero, add_zero, one_mul]
    exact hθ_pos
  · have hs : 0 < d + 0 := by omega
    have hX_sub : (∅ : Set V) ⊆ G.verts := Set.empty_subset _
    have hX_card : (∅ : Set V).ncard ≤ 0 * m := by simp
    have hP_avoids : ∀ i : Fin n, (P i).Avoids (∅ : Set V) :=
      fun _ ↦ disjoint_bot_right
    have hD_sep' : ∀ k : Fin m, Separates G ((∅ : Set V) ∪ (D k).verts) A₁ A₂ := by
      intro k
      rw [Set.empty_union]
      exact hD_sep k
    have h28 := GM01.theorem_2_8_simple hθ heven hs hfin hG hA₁ hA₂ hX_sub hX_card
      P hP_fam hP_avoids D hD_le hD_comp hD_disj hD_sep'
    simpa using h28

/-- Alias for `theorem_4_3_simple`. -/
theorem statement_4_3 : Statement43.{u} :=
  theorem_4_3_simple

end GraphMinor.GM05
