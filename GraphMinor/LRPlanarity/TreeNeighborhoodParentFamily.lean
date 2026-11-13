module

public import GraphMinor.LRPlanarity.Defs

/-!
# Parent-edge families indexed by child vertices

Part IV, Section 7b of the planarity note assigns one strip or subdivided
edge tube to each parent edge. The finite tree union instead indexes these
sets by child vertices. This file performs that reindexing, assigning the
specified empty value at roots, and proves its two evaluation rules.
-/

public section
namespace GraphMinor.LRPlanarity

/-- Reindex data on parent edges by their child, using a specified value at roots. -/
@[expose] noncomputable def parentEdgeFamily {N : ℕ} (T : Forest N)
    {α : Type*} (default : α)
    (f : {e : Fin N × Fin N // T.parent e.2 = some e.1} → α) (v : Fin N) : α :=
  if h : ∃ p, T.parent v = some p then f ⟨(Classical.choose h, v), Classical.choose_spec h⟩
  else default

/-- Evaluation at a vertex with a specified parent. -/
theorem parentEdgeFamily_some {N : ℕ} (T : Forest N) {α : Type*}
    (default : α) (f : {e : Fin N × Fin N // T.parent e.2 = some e.1} → α)
    {v p : Fin N} (hp : T.parent v = some p) :
    parentEdgeFamily T default f v = f ⟨(p, v), hp⟩ := by
  classical
  have hex : ∃ p, T.parent v = some p := ⟨p, hp⟩
  rw [parentEdgeFamily, dite_eq_left hex]
  congr 1
  apply Subtype.ext
  change (Classical.choose hex, v) = (p, v)
  exact Prod.ext (Option.some.inj ((Classical.choose_spec hex).symm.trans hp)) rfl

/-- Evaluation at a root. -/
theorem parentEdgeFamily_none {N : ℕ} (T : Forest N) {α : Type*}
    (default : α) (f : {e : Fin N × Fin N // T.parent e.2 = some e.1} → α)
    {v : Fin N} (hp : T.parent v = none) : parentEdgeFamily T default f v = default := by
  classical
  rw [parentEdgeFamily, dite_eq_right]
  rintro ⟨p, he⟩
  rw [hp] at he
  cases he

end GraphMinor.LRPlanarity
