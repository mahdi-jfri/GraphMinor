module

public import GraphMinor.GM01.SubdivisionEmbeddingEdges
public import GraphMinor.GM09.Basic

/-!
# Reversing the source labels of a subdivision

The orientation choice after Graph Minors I, (4.9), page 58, reverses
the comb spine without changing `D`. Reindex the centres by the source
involution and the replacing paths by its induced edge involution.
Both maps are surjective, so the vertex cover stays the same. Path
ends and intersection conditions transport through the involution.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- An involutive source graph map reindexes a subdivision without
changing its represented graph or any intersection property. This
supplies the reflection choice following GM01 (4.9), page 58. -/
theorem subdivision_reindex {α β ν : Type*} {S : SimpleGraph ν} {D : Graph α β}
    (f : ν ↪ ν) (hf : ∀ {a b}, S.Adj a b → S.Adj (f a) (f b)) (hInv : Involutive f)
    (c : ν → α) (P : S.edgeSet → Graph α β)
    (hV : V(D) = range c ∪ ⋃ e, V(P e))
    (hPaths : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e e' : S.edgeSet, e ≠ e' →
      V(P e) ∩ V(P e') ⊆ range c ∧ Disjoint E(P e) E(P e')) :
    V(D) = range (fun v ↦ c (f v)) ∪ ⋃ e : S.edgeSet, V(P (subdivisionEmbeddingEdges f hf e)) ∧
      (∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
        IsGraphPathWithEnds D (P (subdivisionEmbeddingEdges f hf e)) (c (f a)) (c (f b)) ∧
        V(P (subdivisionEmbeddingEdges f hf e)) ∩ range (fun v ↦ c (f v)) = {c (f a),c (f b)}) ∧
      (∀ e e' : S.edgeSet, e ≠ e' →
        V(P (subdivisionEmbeddingEdges f hf e)) ∩ V(P (subdivisionEmbeddingEdges f hf e')) ⊆
          range (fun v ↦ c (f v)) ∧
        Disjoint E(P (subdivisionEmbeddingEdges f hf e)) E(P (subdivisionEmbeddingEdges f hf e'))) := by
  let map := subdivisionEmbeddingEdges f hf
  have hMapInv : Involutive map := subdivisionEmbeddingEdges_involutive f hf hInv
  have hRange : range (fun v ↦ c (f v)) = range c := by
    apply Set.Subset.antisymm
    · rintro x ⟨v, rfl⟩
      exact mem_range_self (f v)
    · rintro x ⟨v, rfl⟩
      exact ⟨f v, by change c (f (f v)) = c v; rw [hInv v]⟩
  have hUnion : (⋃ e : S.edgeSet, V(P (map e))) = ⋃ e : S.edgeSet, V(P e) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨map e, he⟩
    · intro x hx
      obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨map e, by rw [hMapInv e]; exact he⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hRange, hUnion]
    exact hV
  · intro e
    obtain ⟨a, b, he, hP, hRangeP⟩ := hPaths (map e)
    have he' := congrArg (Sym2.map f) he
    change (map (map e)).val = s(f a,f b) at he'
    rw [hMapInv e] at he'
    refine ⟨f a, f b, he', ?_, ?_⟩
    · change IsGraphPathWithEnds D (P (map e)) (c (f (f a))) (c (f (f b)))
      rw [hInv a, hInv b]
      exact hP
    · change V(P (map e)) ∩ range (fun v ↦ c (f v)) = {c (f (f a)),c (f (f b))}
      rw [hRange, hInv a, hInv b]
      exact hRangeP
  · intro e e' hne
    have h := hInter (map e) (map e') (hMapInv.injective.ne hne)
    rw [hRange]
    exact h

end GraphMinor.GM01
