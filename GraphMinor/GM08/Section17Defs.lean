module

public import GraphMinor.GM08.Defs

/-!
# The classes with fixed cuff counts

Fix a cylinder and order its two cuffs. The class `ℬ(k₁,k₂)` consists
of grafts with drawings having exactly those two cuff vertex counts,
as in Graph Minors VIII, Section 17, page 284.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u v w

/-- The class `ℬ(k₁,k₂)` of VIII Section 17, page 284, for a fixed
cylinder `S` with its two cuffs ordered as `C,D`: grafts with a drawing
having `k₁` vertices on `C` and `k₂` vertices on `D`. -/
def classBCuffCounts {α : Type u} {β : Type v} (S : Type w) [TopologicalSpace S]
    (C D : Set S) (k₁ k₂ : ℕ) : Set (Graft α β) :=
  {X | ∃ gd : GraftDrawing X.G X.T S,
    (gd.drawing.V ∩ C).ncard = k₁ ∧ (gd.drawing.V ∩ D).ncard = k₂}

end GraphMinor.GM08
