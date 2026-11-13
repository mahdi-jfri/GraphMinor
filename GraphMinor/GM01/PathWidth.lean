module

public import GraphMinor.Statement
public import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Path-width

We use the path-decompositions of Graph Minors I, Section 1, page 39, for graphs
with loops and multiple edges. Adding the deleted vertices to every bag proves
the vertex-deletion bound (1.5). The definition does not require bags to cover
isolated vertices, in accordance with (W1) and (W2) in the paper.
-/

@[expose] public section

namespace GraphMinor.GM01

open Graph

variable {α β : Type*}

/-- Graph Minors I, Section 1, page 39: a sequence of subsets of the vertex set
satisfying edge coverage (W1) and the interval condition (W2). -/
structure PathDecomposition (G : Graph α β) where
  length : ℕ
  bag : Fin length → Set α
  bag_subset : ∀ i, bag i ⊆ V(G)
  edge_covered : ∀ e x y, G.IsLink e x y → ∃ i, x ∈ bag i ∧ y ∈ bag i
  interval : ∀ i j k, i ≤ j → j ≤ k → bag i ∩ bag k ⊆ bag j

/-- Graph Minors I, Section 1, page 39: path-width at most `k` means that there
is a path-decomposition whose bags have at most `k + 1` vertices. Finiteness of
bags is explicit so the definition also makes sense for an infinite ambient type. -/
def HasPathWidthLE (G : Graph α β) (k : ℕ) : Prop :=
  ∃ D : PathDecomposition G, ∀ i, (D.bag i).Finite ∧ (D.bag i).ncard ≤ k + 1

/-- The one-bag decomposition gives a bound for every graph with finitely many
vertices, including the empty graph. -/
theorem hasPathWidthLE_card (G : Graph α β) (hfin : V(G).Finite) :
    HasPathWidthLE G V(G).ncard := by
  refine ⟨⟨1, fun _ ↦ V(G), fun _ ↦ Set.Subset.rfl, ?_, ?_⟩, ?_⟩
  · intro e x y h
    exact ⟨0, h.left_mem, h.right_mem⟩
  · intro i j k hij hjk x hx
    exact hx.1
  · intro i
    exact ⟨hfin, Nat.le_succ _⟩

/-- Graph Minors I, Section 1, page 39: the least nonnegative bound on the
sizes of the bags, minus one. The finite-vertex hypothesis ensures a bound exists. -/
noncomputable def pathWidth (G : Graph α β) (hfin : V(G).Finite) : ℕ :=
  by
  classical
  exact Nat.find (show ∃ k, HasPathWidthLE G k from ⟨_, hasPathWidthLE_card G hfin⟩)

/-- Increasing the bound preserves a path-width bound. -/
theorem HasPathWidthLE.mono {G : Graph α β} {k l : ℕ}
    (h : HasPathWidthLE G k) (hkl : k ≤ l) : HasPathWidthLE G l := by
  obtain ⟨D, hD⟩ := h
  exact ⟨D, fun i ↦ ⟨(hD i).1, (hD i).2.trans (Nat.add_le_add_right hkl 1)⟩⟩

/-- The numerical path-width and the decomposition bound agree. -/
theorem pathWidth_le_iff (G : Graph α β) (hfin : V(G).Finite) (k : ℕ) :
    pathWidth G hfin ≤ k ↔ HasPathWidthLE G k := by
  classical
  constructor
  · intro h
    exact (Nat.find_spec (show ∃ k, HasPathWidthLE G k from
      ⟨_, hasPathWidthLE_card G hfin⟩)).mono h
  · intro h
    exact Nat.find_min' _ h


/-- A finite graph has a decomposition covering every vertex with the same
bound on bag size. Append singleton bags for the vertices absent from all bags. -/
theorem HasPathWidthLE.exists_covering {G : Graph α β} (hfin : V(G).Finite)
    {k : ℕ} (h : HasPathWidthLE G k) :
    ∃ D : PathDecomposition G,
      (∀ i, (D.bag i).Finite ∧ (D.bag i).ncard ≤ k + 1) ∧
      ∀ x ∈ V(G), ∃ i, x ∈ D.bag i := by
  classical
  obtain ⟨D, hD⟩ := h
  let U := {x ∈ V(G) | ∀ i, x ∉ D.bag i}
  have hU : U.Finite := hfin.subset (fun _ hx ↦ hx.1)
  let : Fintype U := hU.fintype
  let n := Fintype.card U
  let e : Fin n ≃ U := (Fintype.equivFin U).symm
  let bag : Fin (D.length + n) → Set α := fun i ↦
    if hi : i.val < D.length then D.bag ⟨i.val, hi⟩
    else {((e ⟨i.val - D.length, by omega⟩ : U) : α)}
  have old (i : Fin D.length) :
      bag ⟨i.val, by omega⟩ = D.bag i := by simp only [bag, i.isLt, ↓reduceDIte]
  have tail (i : Fin n) :
      bag ⟨D.length + i.val, by omega⟩ = {((e i : U) : α)} := by
    simp only [bag, Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceDIte,
      Nat.add_sub_cancel_left]
  have mem_tail (i : Fin (D.length + n)) (hi : ¬ i.val < D.length)
      {x : α} (hx : x ∈ bag i) :
      x = ((e ⟨i.val - D.length, by omega⟩ : U) : α) := by
    simpa only [bag, hi, ↓reduceDIte, Set.mem_singleton_iff] using hx
  refine ⟨⟨D.length + n, bag, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i x hx
    by_cases hi : i.val < D.length
    · exact D.bag_subset ⟨i.val, hi⟩ (by simpa only [bag, hi, ↓reduceDIte] using hx)
    · rw [mem_tail i hi hx]
      exact (e _).property.1
  · intro a x y ha
    obtain ⟨i, hx, hy⟩ := D.edge_covered a x y ha
    exact ⟨⟨i.val, by omega⟩, (old i).symm ▸ hx, (old i).symm ▸ hy⟩
  · intro i j l hij hjl x hx
    by_cases hi : i.val < D.length
    · by_cases hl : l.val < D.length
      · have hj : j.val < D.length := lt_of_le_of_lt hjl hl
        simp only [bag, hi, hl, hj, ↓reduceDIte] at hx ⊢
        exact D.interval ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨l.val, hl⟩ hij hjl hx
      · have hxU : x ∈ U := (mem_tail l hl hx.2) ▸ (e _).property
        exact False.elim (hxU.2 ⟨i.val, hi⟩ (by
          simpa only [bag, hi, ↓reduceDIte] using hx.1))
    · have hl : ¬ l.val < D.length := by omega
      have he : (⟨i.val - D.length, by omega⟩ : Fin n) =
          ⟨l.val - D.length, by omega⟩ := e.injective (Subtype.ext
            ((mem_tail i hi hx.1).symm.trans (mem_tail l hl hx.2)))
      have hev : i.val - D.length = l.val - D.length := congrArg Fin.val he
      have hil : i = l := Fin.ext (by omega)
      have hji : j = i := Fin.ext (by have := congrArg Fin.val hil; omega)
      exact hji ▸ hx.1
  · intro i
    by_cases hi : i.val < D.length
    · simpa only [bag, hi, ↓reduceDIte] using hD ⟨i.val, hi⟩
    · simp only [bag, hi, ↓reduceDIte]
      exact ⟨Set.finite_singleton _, by simp⟩
  · change ∀ x ∈ V(G), ∃ i : Fin (D.length + n), x ∈ bag i
    intro x hx
    by_cases hxold : ∃ i, x ∈ D.bag i
    · obtain ⟨i, hi⟩ := hxold
      exact ⟨⟨i.val, by omega⟩, (old i).symm ▸ hi⟩
    · have hxU : x ∈ U := ⟨hx, fun i hi ↦ hxold ⟨i, hi⟩⟩
      let i := e.symm ⟨x, hxU⟩
      refine ⟨⟨D.length + i.val, by omega⟩, ?_⟩
      rw [tail i]
      exact Set.mem_singleton_iff.mpr (congrArg Subtype.val (e.apply_symm_apply ⟨x, hxU⟩)).symm

/-- Graph Minors I, (1.5), page 40.

> If $X \subseteq V(G)$ and $G \setminus X$ has path-width $\le k$, then $G$ has path-width $\le k + |X|$.

First cover the remaining isolated vertices by singleton bags. Then add `X`
to every bag and append a bag `X` to allow an empty remaining graph. -/
theorem theorem_1_5_proof {G : Graph α β} (hfin : V(G).Finite)
    {X : Set α} (hX : X ⊆ V(G)) {k : ℕ}
    (h : HasPathWidthLE (G.deleteVerts X) k) :
    HasPathWidthLE G (k + X.ncard) := by
  classical
  have hdel : V(G.deleteVerts X).Finite := by
    rw [G.vertexSet_deleteVerts X]
    exact hfin.sdiff
  obtain ⟨D, hD, hcover⟩ := h.exists_covering hdel
  have hXfin := hfin.subset hX
  let bag : Fin (D.length + 1) → Set α := fun i ↦
    if hi : i.val < D.length then D.bag ⟨i.val, hi⟩ ∪ X else X
  have hbagX (i) : X ⊆ bag i := by
    dsimp only [bag]
    split <;> intro x hx
    · exact Or.inr hx
    · exact hx
  have old (i : Fin D.length) :
      bag ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = D.bag i ∪ X := by
    simp only [bag, i.isLt, ↓reduceDIte]
  have cover {x : α} (hx : x ∈ V(G)) : ∃ i, x ∈ bag i := by
    by_cases hxX : x ∈ X
    · exact ⟨⟨D.length, Nat.lt_succ_self _⟩, hbagX _ hxX⟩
    · have hxd : x ∈ V(G.deleteVerts X) := by
        rw [G.vertexSet_deleteVerts X]
        exact ⟨hx, hxX⟩
      obtain ⟨i, hi⟩ := hcover x hxd
      refine ⟨⟨i.val, by omega⟩, ?_⟩
      rw [old i]
      exact Or.inl hi
  refine ⟨⟨D.length + 1, bag, ?_, ?_, ?_⟩, ?_⟩
  · intro i x hx
    dsimp only [bag] at hx
    split at hx
    · apply hx.elim _ (hX ·)
      intro hx
      have hd := D.bag_subset _ hx
      rw [G.vertexSet_deleteVerts X] at hd
      exact hd.1
    · exact hX hx
  · intro e x y he
    by_cases hx : x ∈ X
    · obtain ⟨i, hi⟩ := cover he.right_mem
      exact ⟨i, hbagX i hx, hi⟩
    · by_cases hy : y ∈ X
      · obtain ⟨i, hi⟩ := cover he.left_mem
        exact ⟨i, hi, hbagX i hy⟩
      · obtain ⟨i, hix, hiy⟩ := D.edge_covered e x y
          ((G.deleteVerts_isLink X).2 ⟨he, hx, hy⟩)
        refine ⟨⟨i.val, by omega⟩, ?_, ?_⟩
        · rw [old i]; exact Or.inl hix
        · rw [old i]; exact Or.inl hiy
  · intro i j l hij hjl x hx
    by_cases hxX : x ∈ X
    · exact hbagX _ hxX
    · have hi : i.val < D.length := by
        by_contra hi
        exact hxX (by simpa only [bag, hi, ↓reduceDIte] using hx.1)
      have hl : l.val < D.length := by
        by_contra hl
        exact hxX (by simpa only [bag, hl, ↓reduceDIte] using hx.2)
      have hj : j.val < D.length := lt_of_le_of_lt hjl hl
      simp only [bag, hi, hl, hj, ↓reduceDIte, Set.mem_inter_iff, Set.mem_union, hxX, or_false] at hx ⊢
      exact D.interval ⟨i.val, hi⟩ ⟨j.val, hj⟩ ⟨l.val, hl⟩ hij hjl hx
  · intro i
    dsimp only [bag]
    split
    · rename_i hi
      exact ⟨(hD _).1.union hXfin, (Set.ncard_union_le _ _).trans (by
        have := (hD ⟨i.val, hi⟩).2
        omega)⟩
    · exact ⟨hXfin, by omega⟩

end GraphMinor.GM01
