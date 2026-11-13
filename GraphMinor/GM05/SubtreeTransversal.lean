module

public import GraphMinor.GM05.Defs
import GraphMinor.GM05.SubtreePacking

/-!
# Packing subtrees or meeting them with few vertices

Graph Minors V, (8.7), is the standard packing and hitting theorem for
subtrees of a tree. Connected vertex sets are path-closed in a tree, so
the leaf-induction packing theorem applies. The family need not be finite.
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

/-- Graph Minors V, (8.7), page 111: for any family of subtrees and any
natural `k`, either `k` members are pairwise vertex-disjoint, or fewer
than `k` tree vertices meet every member. The proof is direct leaf induction,
through `subtrees_pack_or_hit`. -/
theorem theorem_8_7_proof {ι : Type*} [Fintype ι] {T : SimpleGraph ι} (hT : T.IsTree)
    (F : Set (Set ι)) (hF : ∀ A∈F,(T.induce A).Connected) (k : ℕ) :
    (∃ A : Fin k → Set ι, (∀ i,A i∈F) ∧ Pairwise (fun i j ↦ Disjoint (A i) (A j))) ∨
      ∃ X : Set ι, X.ncard<k ∧ ∀ A∈F,(X∩A).Nonempty := by
  have hN : ∀ A : F, A.1.Nonempty := by
    intro A
    obtain ⟨t⟩ := (hF A.1 A.2).nonempty
    exact ⟨t.1,t.2⟩
  have hconv : ∀ A : F, ∀ a, a∈A.1 → ∀ b, b∈A.1 → ∀ c,
      OnTreePath T a b c → c∈A.1 := by
    intro A a ha b hb c hc
    obtain ⟨p,hp⟩ := (hF A.1 A.2).exists_isPath ⟨a,ha⟩ ⟨b,hb⟩
    let f : T.induce A.1 →g T := ⟨Subtype.val,fun h ↦ h⟩
    have hm := hc (p.map f) (hp.map Subtype.val_injective)
    rw [Walk.support_map] at hm
    obtain ⟨t,ht,htc⟩ := List.mem_map.mp hm
    exact htc ▸ t.2
  rcases subtrees_pack_or_hit hT (fun A : F ↦ A.1) hN hconv k with hpack|hhit
  · obtain ⟨A,hA⟩ := hpack
    exact Or.inl ⟨fun i ↦ (A i).1,fun i ↦ (A i).2,hA⟩
  · obtain ⟨X,hX,hmeet⟩ := hhit
    exact Or.inr ⟨X,hX,fun A hAF ↦ hmeet ⟨A,hAF⟩⟩

end GraphMinor.GM05
