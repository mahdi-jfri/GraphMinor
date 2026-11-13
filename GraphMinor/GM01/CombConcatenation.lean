module

public import GraphMinor.GM01.CombShiftRanges

/-!
# Concatenating two combs

Graph Minors I, (4.10), page 58, joins a comb prefix to the retained
part of `D`. The source is two combs joined by one edge from the last
spine vertex of the first to the first spine vertex of the second.
Consecutive embeddings identify their vertex sets with the comb whose
spine length is the sum. The only edge between the two intervals is
that joining edge.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function

/-- The last spine vertex of a positive-length comb. -/
def pathCombLastSpine (γ a : ℕ) (ha : 0 < a) : (pathComb γ a).verts :=
  ⟨Sum.inl ⟨a - 1, by omega⟩, pathComb_spine_mem γ a _⟩

/-- The source graph obtained by joining the last spine vertex of one
comb to the first spine vertex of the next, as contracted in GM01
(4.10), page 58. -/
def concatenatedComb (γ a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    SimpleGraph ((pathComb γ a).verts ⊕ (pathComb γ b).verts) where
  Adj u v := match u, v with
    | .inl u, .inl v => (pathComb γ a).coe.Adj u v
    | .inr u, .inr v => (pathComb γ b).coe.Adj u v
    | .inl u, .inr v => u = pathCombLastSpine γ a ha ∧ v = (rootedPathComb γ b hb).root
    | .inr u, .inl v => v = pathCombLastSpine γ a ha ∧ u = (rootedPathComb γ b hb).root
  symm := ⟨by
    rintro (u | u) (v | v) h
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨by
    intro u
    cases u with
    | inl u => exact (pathComb γ a).coe.loopless.irrefl u
    | inr u => exact (pathComb γ b).coe.loopless.irrefl u⟩

/-- The two consecutive source embeddings together cover the longer
comb and identify no pair of distinct source vertices. -/
theorem comb_concatenation_map_bijective (γ a b : ℕ) :
    Bijective (Sum.elim
      (combShiftEmbedding (γ := γ) 0 (by omega : 0 + a ≤ a + b))
      (combShiftEmbedding (γ := γ) a (le_refl (a + b)))) := by
  have hdis := disjoint_combShiftEmbedding_ranges (γ := γ) 0 a
    (by omega : 0 + a ≤ a + b) (le_refl (a + b)) (by omega : 0 + a ≤ a)
  constructor
  · rintro (u | u) (v | v) huv
    · exact congrArg Sum.inl ((combShiftEmbedding 0 (by omega : 0 + a ≤ a + b)).injective huv)
    · change combShiftEmbedding 0 (by omega : 0 + a ≤ a + b) u = combShiftEmbedding a (le_refl (a + b)) v at huv
      exact False.elim (Set.disjoint_left.mp hdis (mem_range_self u) (huv.symm ▸ mem_range_self v))
    · change combShiftEmbedding a (le_refl (a + b)) u = combShiftEmbedding 0 (by omega : 0 + a ≤ a + b) v at huv
      exact False.elim (Set.disjoint_left.mp hdis (huv.symm ▸ mem_range_self v) (mem_range_self u))
    · exact congrArg Sum.inr ((combShiftEmbedding a (le_refl (a + b))).injective huv)
  · intro v
    by_cases hv : (pathCombSpineIndex v.val).val < a
    · obtain ⟨u, hu⟩ := (mem_range_combShiftEmbedding_iff 0 (by omega : 0 + a ≤ a + b) v).mpr
        ⟨Nat.zero_le _, by omega⟩
      exact ⟨Sum.inl u, hu⟩
    · have hidx := (pathCombSpineIndex v.val).isLt
      obtain ⟨u, hu⟩ := (mem_range_combShiftEmbedding_iff a (le_refl (a + b)) v).mpr ⟨by omega, hidx⟩
      exact ⟨Sum.inr u, hu⟩

/-- The explicit vertex identification for the two joined combs. -/
noncomputable def combConcatenationEquiv (γ a b : ℕ) :
    ((pathComb γ a).verts ⊕ (pathComb γ b).verts) ≃ (pathComb γ (a + b)).verts :=
  Equiv.ofBijective _ (comb_concatenation_map_bijective γ a b)

/-- The only source edge crossing the boundary between two consecutive
comb intervals joins their adjacent spine ends. -/
theorem comb_concatenation_cross_adj_iff {γ a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (u : (pathComb γ a).verts) (v : (pathComb γ b).verts) :
    (pathComb γ (a + b)).coe.Adj
      (combShiftEmbedding 0 (by omega : 0 + a ≤ a + b) u)
      (combShiftEmbedding a (le_refl (a + b)) v) ↔
      u = pathCombLastSpine γ a ha ∧ v = (rootedPathComb γ b hb).root := by
  constructor
  · intro huv
    obtain ⟨u, hu⟩ := u
    obtain ⟨v, hv⟩ := v
    cases u with
    | inl i =>
      cases v with
      | inl j =>
        rcases pathGraph_adj.mp huv with hfor | hback
        · change 0 + i.val + 1 = a + j.val at hfor
          have hi := i.isLt
          refine ⟨Subtype.ext (congrArg Sum.inl (Fin.ext ?_)),
            Subtype.ext (congrArg Sum.inl (Fin.ext ?_))⟩
          · change i.val = a - 1
            omega
          · change j.val = 0
            omega
        · change a + j.val + 1 = 0 + i.val at hback
          have hi := i.isLt
          omega
      | inr pair =>
        have heq := congrArg Fin.val huv.1
        change 0 + i.val = a + pair.1.val at heq
        have hi := i.isLt
        omega
    | inr pair =>
      cases v with
      | inl j =>
        have heq := congrArg Fin.val huv.1
        change 0 + pair.1.val = a + j.val at heq
        have hi := pair.1.isLt
        omega
      | inr pair' =>
        have heq := congrArg Fin.val huv.1
        change 0 + pair.1.val = a + pair'.1.val at heq
        have hi := pair.1.isLt
        omega
  · rintro ⟨rfl, rfl⟩
    apply pathComb_spine_adj (γ := γ)
    apply pathGraph_adj.mpr
    exact Or.inl (by change 0 + (a - 1) + 1 = a + 0; omega)

/-- The vertex identification preserves and reflects every source
edge, including the single edge between the two combs. -/
theorem combConcatenationEquiv_adj_iff {γ a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (u v : (pathComb γ a).verts ⊕ (pathComb γ b).verts) :
    (pathComb γ (a + b)).coe.Adj (combConcatenationEquiv γ a b u) (combConcatenationEquiv γ a b v) ↔
      (concatenatedComb γ a b ha hb).Adj u v := by
  rcases u with u | u <;> rcases v with v | v
  · exact combShiftEmbedding_adj_iff 0 (by omega : 0 + a ≤ a + b) u v
  · exact comb_concatenation_cross_adj_iff ha hb u v
  · exact ((pathComb γ (a + b)).coe.adj_comm _ _).trans (comb_concatenation_cross_adj_iff ha hb v u)
  · exact combShiftEmbedding_adj_iff a (le_refl (a + b)) u v

end GraphMinor.GM01
