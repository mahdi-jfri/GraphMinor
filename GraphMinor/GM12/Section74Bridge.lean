module

public import GraphMinor.GM12.Section74
public import GraphMinor.GM12.Section75Defs

/-!
# XII (7.4) in the form used by (7.5)

`theorem_7_4` gives more than `Theorem74Statement` asks for, namely that the point set of `Γ'` is a
component of the point set of `Γ \ v`. This file drops that part.
-/

@[expose] public section

namespace GraphMinor.GM12

universe u

/-- Graph Minors XII, (7.4), pages 262--263, in the form of `Theorem74Statement`. -/
theorem gm12_theorem_7_4 : Theorem74Statement.{u} := by
  intro S _ _ _ hS Γ θ T d v hθ hd hv
  obtain ⟨Γ', T', d', r, hsub, -, hd', hr, hvr, hU, hi, hii, hiii⟩ := theorem_7_4_proof hS hθ hd hv
  exact ⟨Γ', T', d', r, hsub, hd'.1.1, hd', hr, hvr, hU, hi, hii, hiii⟩

end GraphMinor.GM12
