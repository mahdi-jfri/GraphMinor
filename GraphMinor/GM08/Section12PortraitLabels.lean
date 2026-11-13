module

public import GraphMinor.GM08.Defs6to18
import Mathlib.Logic.Function.Basic

/-!
# Assigning orders and labels to indexed painting cells

The disc pieces give distinct cells. Extend the chosen order and
label on each piece to functions on all point sets. On actual cells
the extensions keep those choices. This assembles the portrait data
from the painting constructed on VIII, page 272, for Section 12.
-/

public section

namespace GraphMinor.GM08

open Set Surface

/-- Assemble a portrait from indexed cells, their orders, and their
labels. Injectivity says that each cell has a unique prescribed label,
as in the derived portrait construction of VIII, Section 12. -/
theorem exists_portrait_of_indexed_cells {S Q ι : Type*} [TopologicalSpace S]
    (Pt : PaintingInDisc S) (c : ι → Set S) (hc : Pt.cells = range c)
    (hi : Function.Injective c) (α : List S) (hα : α.Nodup)
    (hαset : {x | x ∈ α} = Pt.U ∩ bd S)
    (μ : ι → List S) (hμ : ∀ i, (μ i).Nodup)
    (hμset : ∀ i, {x | x ∈ μ i} = closure (c i) \ c i)
    (φ : ι → Q) (q : Q) :
    ∃ P : QPortrait Q S, P.painting = Pt ∧ P.α = α ∧
      (∀ i, P.μ (c i) = μ i) ∧ ∀ i, P.φ (c i) = φ i := by
  classical
  let μ' := Function.extend c μ (fun _ => [])
  let φ' := Function.extend c φ (fun _ => q)
  have hμ' : ∀ i, μ' (c i) = μ i := hi.extend_apply μ (fun _ => [])
  have hφ' : ∀ i, φ' (c i) = φ i := hi.extend_apply φ (fun _ => q)
  let P : QPortrait Q S := {
    painting := Pt
    α := α
    α_nodup := hα
    α_set := hαset
    μ := μ'
    μ_nodup := by
      intro e he
      obtain ⟨i, rfl⟩ := hc ▸ he
      rw [hμ']
      exact hμ i
    μ_set := by
      intro e he
      obtain ⟨i, rfl⟩ := hc ▸ he
      rw [hμ']
      exact hμset i
    φ := φ' }
  exact ⟨P, rfl, rfl, hμ', hφ'⟩

end GraphMinor.GM08
