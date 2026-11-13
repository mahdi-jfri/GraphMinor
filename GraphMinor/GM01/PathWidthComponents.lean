module

public import GraphMinor.GM01.PathWidth
import Mathlib.Data.Set.Finite.Range

/-!
# Combining path-decompositions of disjoint pieces

Concatenating decompositions preserves the bag bound when the two pieces
have disjoint vertex sets and cover all edges. This is the construction behind
Graph Minors I, (1.4), page 40.
-/

public section

namespace GraphMinor.GM01

open Graph

variable {α β : Type*}

/-- Concatenate decompositions of two disjoint pieces covering all edges. -/
theorem HasPathWidthLE.combine {G H K : Graph α β} {k : ℕ}
    (hH : HasPathWidthLE H k) (hK : HasPathWidthLE K k)
    (hHG : V(H) ⊆ V(G)) (hKG : V(K) ⊆ V(G))
    (hdisj : Disjoint V(H) V(K))
    (hedge : ∀ e x y, G.IsLink e x y → H.IsLink e x y ∨ K.IsLink e x y) :
    HasPathWidthLE G k := by
  obtain ⟨D, hD⟩ := hH
  obtain ⟨E, hE⟩ := hK
  let bag : Fin (D.length + E.length) → Set α := fun i ↦
    if hi : i.val < D.length then D.bag ⟨i.val, hi⟩
    else E.bag ⟨i.val - D.length, by omega⟩
  have old (i : Fin D.length) : bag ⟨i.val, by omega⟩ = D.bag i := by
    simp only [bag, i.isLt, ↓reduceDIte]
  have tail (i : Fin E.length) : bag ⟨D.length + i.val, by omega⟩ = E.bag i := by
    simp only [bag, Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceDIte,
      Nat.add_sub_cancel_left]
  refine ⟨⟨D.length + E.length, bag, ?_, ?_, ?_⟩, ?_⟩
  · intro i x hx
    dsimp only [bag] at hx
    split at hx
    · exact hHG (D.bag_subset _ hx)
    · exact hKG (E.bag_subset _ hx)
  · intro e x y he
    rcases hedge e x y he with he | he
    · obtain ⟨i, hx, hy⟩ := D.edge_covered e x y he
      exact ⟨⟨i.val, by omega⟩, (old i).symm ▸ hx, (old i).symm ▸ hy⟩
    · obtain ⟨i, hx, hy⟩ := E.edge_covered e x y he
      exact ⟨⟨D.length + i.val, by omega⟩, (tail i).symm ▸ hx, (tail i).symm ▸ hy⟩
  · intro i j l hij hjl x hx
    by_cases hi : i.val < D.length
    · by_cases hl : l.val < D.length
      · have hj : j.val < D.length := lt_of_le_of_lt hjl hl
        simp only [bag, hi, hl, hj, ↓reduceDIte] at hx ⊢
        exact D.interval ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨l.val, hl⟩ hij hjl hx
      · have hxH : x ∈ V(H) := D.bag_subset ⟨i.val, hi⟩ (by
          simpa only [bag, hi, ↓reduceDIte] using hx.1)
        have hxK : x ∈ V(K) := E.bag_subset ⟨l.val - D.length, by omega⟩ (by
          simpa only [bag, hl, ↓reduceDIte] using hx.2)
        exact False.elim (Set.disjoint_left.mp hdisj hxH hxK)
    · have hj : ¬ j.val < D.length := by omega
      have hl : ¬ l.val < D.length := by omega
      simp only [bag, hi, hl, hj, ↓reduceDIte] at hx ⊢
      apply E.interval ⟨i.val - D.length, by omega⟩ ⟨j.val - D.length, by omega⟩
        ⟨l.val - D.length, by omega⟩
        (Nat.sub_le_sub_right hij D.length) (Nat.sub_le_sub_right hjl D.length) hx
  · intro i
    dsimp only [bag]
    split
    · exact hD _
    · exact hE _

/-- A finite disjoint family of vertex sets closed under adjacency can be
handled one set at a time by concatenating its decompositions. -/
theorem hasPathWidthLE_finite_parts (G : Graph α β) {S : Set (Set α)}
    (hS : S.Finite) (hdisj : S.PairwiseDisjoint id)
    (hclosed : ∀ s ∈ S, ∀ e x y, G.IsLink e x y → x ∈ s → y ∈ s)
    {k : ℕ} (hwidth : ∀ s ∈ S, HasPathWidthLE (G.induce s) k) :
    HasPathWidthLE (G.induce (⋃₀ S)) k := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    refine ⟨⟨0, Fin.elim0, ?_, ?_, ?_⟩, fun i ↦ Fin.elim0 i⟩
    · exact fun i ↦ Fin.elim0 i
    · intro e x y he
      exact False.elim (by simpa using he.left_mem)
    · exact fun i ↦ Fin.elim0 i
  | @insert s S hs hS ih =>
    have hd : S.PairwiseDisjoint id := fun a ha b hb hab ↦
      hdisj (Set.mem_insert_of_mem _ ha) (Set.mem_insert_of_mem _ hb) hab
    have hw := ih hd (fun a ha ↦ hclosed a (Set.mem_insert_of_mem _ ha))
      (fun a ha ↦ hwidth a (Set.mem_insert_of_mem _ ha))
    apply (hwidth s (Set.mem_insert s S)).combine hw
    · intro x hx
      exact Set.mem_sUnion.mpr ⟨s, Set.mem_insert s S, hx⟩
    · intro x hx
      obtain ⟨a, ha, hxa⟩ := Set.mem_sUnion.mp hx
      exact Set.mem_sUnion.mpr ⟨a, Set.mem_insert_of_mem _ ha, hxa⟩
    · apply Set.disjoint_left.mpr
      intro x hxs hxS
      obtain ⟨a, ha, hxa⟩ := Set.mem_sUnion.mp hxS
      exact Set.disjoint_left.mp
        (hdisj (Set.mem_insert s S) (Set.mem_insert_of_mem _ ha)
          (fun h ↦ hs (h.symm ▸ ha))) hxs hxa
    · intro e x y he
      obtain ⟨a, ha, hxa⟩ := Set.mem_sUnion.mp he.left_mem
      have hya := hclosed a ha e x y he.1 hxa
      rcases ha with ha | ha
      · subst a
        exact Or.inl ⟨he.1, hxa, hya⟩
      · exact Or.inr ⟨he.1, Set.mem_sUnion.mpr ⟨a, ha, hxa⟩,
          Set.mem_sUnion.mpr ⟨a, ha, hya⟩⟩

/-- The vertex set of the connected component containing a vertex, as used in
Graph Minors I, Section 1, page 40. Reachability is the reflexive transitive
closure of adjacency. -/
@[expose] def componentVertices (G : Graph α β) (v : V(G)) : Set α :=
  {x ∈ V(G) | Relation.ReflTransGen G.Adj v x}

/-- Graph Minors I, (1.4), page 40: if every connected component has
path-width at most `k`, concatenate their decompositions to obtain that bound
for the whole graph. -/
theorem theorem_1_4_proof {G : Graph α β} (hfin : V(G).Finite) {k : ℕ}
    (h : ∀ v : V(G), HasPathWidthLE (G.induce (componentVertices G v)) k) :
    HasPathWidthLE G k := by
  classical
  let : Finite V(G) := hfin.to_subtype
  let S := Set.range (componentVertices G)
  have hS : S.Finite := Set.finite_range (f := componentVertices G)
  have symm {x y : α} (hxy : Relation.ReflTransGen G.Adj x y) :
      Relation.ReflTransGen G.Adj y x := by
    induction hxy with
    | refl => exact .refl
    | @tail b c hab hbc ih => exact (Relation.ReflTransGen.single hbc.symm).trans ih
  have heq {v w : V(G)} {x : α}
      (hxv : x ∈ componentVertices G v) (hxw : x ∈ componentVertices G w) :
      componentVertices G v = componentVertices G w := by
    have hvw := hxv.2.trans (symm hxw.2)
    apply Set.ext
    intro y
    exact ⟨fun hy ↦ ⟨hy.1, (symm hvw).trans hy.2⟩,
      fun hy ↦ ⟨hy.1, hvw.trans hy.2⟩⟩
  have hdisj : S.PairwiseDisjoint id := by
    intro a ha b hb hab
    obtain ⟨v, rfl⟩ := ha
    obtain ⟨w, rfl⟩ := hb
    exact Set.disjoint_left.mpr (fun _ hx hy ↦ hab (heq hx hy))
  have hclosed : ∀ s ∈ S, ∀ e x y, G.IsLink e x y → x ∈ s → y ∈ s := by
    intro s hs e x y he hx
    obtain ⟨v, rfl⟩ := hs
    exact ⟨he.right_mem, hx.2.tail ⟨e, he⟩⟩
  have hfull : ⋃₀ S = V(G) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨s, ⟨v, rfl⟩, hx⟩ := Set.mem_sUnion.mp hx
      exact hx.1
    · intro x hx
      exact Set.mem_sUnion.mpr ⟨componentVertices G ⟨x, hx⟩,
        ⟨⟨x, hx⟩, rfl⟩, hx, .refl⟩
  have hw := hasPathWidthLE_finite_parts G hS hdisj hclosed
    (fun s ⟨v, hv⟩ ↦ hv ▸ h v)
  rwa [hfull, G.induce_vertexSet] at hw

end GraphMinor.GM01
