module

public import GraphMinor.Wagner.GraphTools
public import GraphMinor.Wagner.MultigraphReduction

/-!
# Tools for building `K_5` minors

`HasK5MinorSimple K` asks for five pairwise disjoint, nonempty, preconnected vertex sets with an
edge between any two of them. This file gives a constructor that takes the ten disjointness facts
and the ten adjacency facts one by one (`hasK5_of_sets`), and a few facts about the relation
"some edge joins `X` and `Y`" (`Touch`).
-/

@[expose] public section

namespace GraphMinor.Wagner

open Set SimpleGraph

variable {γ : Type*} {K : SimpleGraph γ}

/-- Some edge of `K` joins a vertex of `X` to a vertex of `Y`. -/
def Touch (K : SimpleGraph γ) (X Y : Set γ) : Prop :=
  ∃ x ∈ X, ∃ y ∈ Y, K.Adj x y

theorem Touch.symm {X Y : Set γ} (h : Touch K X Y) : Touch K Y X := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  exact ⟨y, hy, x, hx, hxy.symm⟩

theorem Touch.mono {X Y X' Y' : Set γ} (h : Touch K X Y) (hX : X ⊆ X') (hY : Y ⊆ Y') :
    Touch K X' Y' := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  exact ⟨x, hX hx, y, hY hy, hxy⟩

theorem Touch.of_adj {X Y : Set γ} {x y : γ} (hx : x ∈ X) (hy : y ∈ Y) (h : K.Adj x y) :
    Touch K X Y :=
  ⟨x, hx, y, hy, h⟩

/-- Two preconnected sets have a preconnected union when one of them is empty or an edge joins
them. -/
theorem pc_union_touch {X Y : Set γ} (hX : (K.induce X).Preconnected)
    (hY : (K.induce Y).Preconnected) (h : X.Nonempty → Y.Nonempty → Touch K X Y) :
    (K.induce (X ∪ Y)).Preconnected := by
  rcases X.eq_empty_or_nonempty with rfl | hXne
  · exact pc_congr (empty_union Y).symm hY
  rcases Y.eq_empty_or_nonempty with rfl | hYne
  · exact pc_congr (union_empty X).symm hX
  obtain ⟨x, hx, y, hy, hxy⟩ := h hXne hYne
  exact pc_union_adj hX hY hx hy hxy

/-- Five sets that are nonempty, preconnected, pairwise disjoint and pairwise joined by edges give
a `K_5` minor. -/
theorem hasK5_of_sets (B₀ B₁ B₂ B₃ B₄ : Set γ)
    (n₀ : B₀.Nonempty) (n₁ : B₁.Nonempty) (n₂ : B₂.Nonempty) (n₃ : B₃.Nonempty)
    (n₄ : B₄.Nonempty)
    (c₀ : (K.induce B₀).Preconnected) (c₁ : (K.induce B₁).Preconnected)
    (c₂ : (K.induce B₂).Preconnected) (c₃ : (K.induce B₃).Preconnected)
    (c₄ : (K.induce B₄).Preconnected)
    (d₀₁ : Disjoint B₀ B₁) (d₀₂ : Disjoint B₀ B₂) (d₀₃ : Disjoint B₀ B₃) (d₀₄ : Disjoint B₀ B₄)
    (d₁₂ : Disjoint B₁ B₂) (d₁₃ : Disjoint B₁ B₃) (d₁₄ : Disjoint B₁ B₄)
    (d₂₃ : Disjoint B₂ B₃) (d₂₄ : Disjoint B₂ B₄) (d₃₄ : Disjoint B₃ B₄)
    (t₀₁ : Touch K B₀ B₁) (t₀₂ : Touch K B₀ B₂) (t₀₃ : Touch K B₀ B₃) (t₀₄ : Touch K B₀ B₄)
    (t₁₂ : Touch K B₁ B₂) (t₁₃ : Touch K B₁ B₃) (t₁₄ : Touch K B₁ B₄)
    (t₂₃ : Touch K B₂ B₃) (t₂₄ : Touch K B₂ B₄) (t₃₄ : Touch K B₃ B₄) :
    HasK5MinorSimple K := by
  refine ⟨![B₀, B₁, B₂, B₃, B₄], ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i <;> assumption
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | assumption
      | exact Disjoint.symm (by assumption)
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | assumption
      | exact Touch.symm (by assumption)

end GraphMinor.Wagner
