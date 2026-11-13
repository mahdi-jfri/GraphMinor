module

public import GraphMinor.GM16.Defs
public import GraphMinor.Statement
import GraphMinor.Minor.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# The Wagner graph `V₈` has no `K₅` minor

Every vertex of `wagnerGraphV8` is incident with only three edges, whereas every vertex of `K₅` has
degree four. In any minor model of `K₅` in `V₈`, each of the five pairwise disjoint branch sets
must therefore contain at least two vertices, requiring at least ten vertices in an eight-vertex
graph.
-/

public section

namespace GraphMinor.Wagner

open Set Graph

universe u v

/-- A 3-element superset of the edges incident with vertex `x` in `wagnerGraphV8`. -/
private def v8IncEdges (x : Fin 8) : Finset (Fin 12) :=
  {⟨x.1, by omega⟩, ⟨(x.1 + 7) % 8, by omega⟩, ⟨x.1 % 4 + 8, by omega⟩}

private theorem card_v8IncEdges_le (x : Fin 8) : (v8IncEdges x).card ≤ 3 := by
  dsimp only [v8IncEdges]
  exact (Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right ((Finset.card_insert_le _ _).trans (by simp)) 1)

private theorem mem_v8IncEdges_of_inc {e : Fin 12} {x : Fin 8}
    (hinc : GM16.wagnerGraphV8.Inc e x) : e ∈ v8IncEdges x := by
  obtain ⟨y, hlink⟩ := hinc
  dsimp only [GM16.wagnerGraphV8] at hlink
  dsimp only [v8IncEdges]
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  have hx8 : x.1 < 8 := x.2
  have he12 : e.1 < 12 := e.2
  by_cases he : e.1 < 8
  · simp only [he, ↓reduceDIte] at hlink
    rcases hlink with ⟨hx, -⟩ | ⟨-, hx⟩
    · exact Or.inl hx.symm
    · exact Or.inr (Or.inl (by omega))
  · simp only [he, ↓reduceDIte] at hlink
    rcases hlink with ⟨hx, -⟩ | ⟨-, hx⟩
    · exact Or.inr (Or.inr (by omega))
    · exact Or.inr (Or.inr (by omega))

/-- The Wagner graph `V₈` has no minor isomorphic to `K₅`. -/
theorem not_isIsoMinor_completeGraph_five_wagnerGraphV8 :
    ¬ IsIsoMinor (GM16.completeGraph 5) GM16.wagnerGraphV8 := by
  classical
  intro hm
  have hne : Nonempty (Fin 12) := ⟨0⟩
  obtain ⟨ηv, ηe, hM⟩ :=
    exists_isMinorModel_of_isIsoMinor_of_nonempty_or_isEmpty
      finite_univ finite_univ (Or.inl hne) hm
  let B : Fin 5 → Finset (Fin 8) := fun i => (toFinite (ηv i)).toFinset
  have hcard2 : ∀ i : Fin 5, 2 ≤ (B i).card := by
    intro i
    by_contra hlt
    obtain ⟨x₀, hx₀⟩ := hM.vertex_nonempty i trivial
    have hsub_single : ∀ x ∈ ηv i, x = x₀ := by
      intro x hx
      by_contra hne_x
      have hpair : ({x, x₀} : Finset (Fin 8)) ⊆ B i := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rw [Set.Finite.mem_toFinset]
        rcases hz with rfl | rfl <;> assumption
      have hc2 : 2 ≤ (B i).card := by
        have h1 : ({x, x₀} : Finset (Fin 8)).card = 2 := Finset.card_pair hne_x
        exact h1 ▸ Finset.card_le_card hpair
      exact hlt hc2
    let S : Finset (Fin 5) := Finset.univ.erase i
    have hScard : S.card = 4 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
      decide
    let g : Fin 5 → Fin 12 := fun j => ηe s(i, j)
    have hg_inj : InjOn g (S : Set (Fin 5)) := by
      intro j₁ hj₁ j₂ hj₂ hgj
      have hj₁_ne : j₁ ≠ i := (Finset.mem_erase.mp hj₁).1
      have hj₂_ne : j₂ ≠ i := (Finset.mem_erase.mp hj₂).1
      have he₁ : s(i, j₁) ∈ E(GM16.completeGraph 5) := ⟨i, j₁, hj₁_ne.symm, rfl⟩
      have he₂ : s(i, j₂) ∈ E(GM16.completeGraph 5) := ⟨i, j₂, hj₂_ne.symm, rfl⟩
      have hseq : s(i, j₁) = s(i, j₂) := hM.edge_injOn he₁ he₂ hgj
      rcases Sym2.eq_iff.mp hseq with ⟨-, rfl⟩ | ⟨hij₂, _⟩
      · rfl
      · exact (hj₂_ne hij₂.symm).elim
    have hg_sub : S.image g ⊆ v8IncEdges x₀ := by
      intro e he
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
      have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
      have he_mem : s(i, j) ∈ E(GM16.completeGraph 5) := ⟨i, j, hj_ne.symm, rfl⟩
      have hincK : (GM16.completeGraph 5).Inc s(i, j) i := ⟨j, hj_ne.symm, rfl⟩
      obtain ⟨x, hx, hincV⟩ := (hM.inc_iff i trivial s(i, j) he_mem).mp hincK
      rw [hsub_single x hx] at hincV
      exact mem_v8IncEdges_of_inc hincV
    have h4 : 4 ≤ (v8IncEdges x₀).card := by
      calc 4 = S.card := hScard.symm
        _ = (S.image g).card := (Finset.card_image_of_injOn hg_inj).symm
        _ ≤ (v8IncEdges x₀).card := Finset.card_le_card hg_sub
    have h3 := card_v8IncEdges_le x₀
    omega
  have hdisj : ((Finset.univ : Finset (Fin 5)) : Set (Fin 5)).PairwiseDisjoint B := by
    intro i _ j _ hij
    exact Finset.disjoint_left.mpr fun x hxi hxj => by
      rw [Set.Finite.mem_toFinset] at hxi hxj
      exact Set.disjoint_left.mp (hM.vertex_disjoint i trivial j trivial hij) hxi hxj
  have h10 : 10 ≤ (Finset.univ.biUnion B).card := by
    rw [Finset.card_biUnion hdisj]
    calc 10 = ∑ _i : Fin 5, 2 := by decide
      _ ≤ ∑ i : Fin 5, (B i).card := Finset.sum_le_sum fun i _ => hcard2 i
  have h8 : (Finset.univ.biUnion B).card ≤ 8 := by
    calc (Finset.univ.biUnion B).card ≤ (Finset.univ : Finset (Fin 8)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = 8 := by decide
  omega

/-- No graph isomorphic to `V₈` has a `K₅` minor. -/
theorem not_isIsoMinor_completeGraph_five_of_iso_wagnerGraphV8 {α : Type u} {β : Type v}
    {H : Graph α β} (hiso : Nonempty (Iso H GM16.wagnerGraphV8)) :
    ¬ IsIsoMinor (GM16.completeGraph 5) H := by
  obtain ⟨e⟩ := hiso
  intro hm
  exact not_isIsoMinor_completeGraph_five_wagnerGraphV8 (Iso.isIsoMinor_right hm e)

end GraphMinor.Wagner
