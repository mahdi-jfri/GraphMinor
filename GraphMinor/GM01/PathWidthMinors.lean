module

public import GraphMinor.GM01.PathWidth
import GraphMinor.GM01.PathWidthMinorModels
import GraphMinor.Minor.Basic

/-!
# Path-width does not increase under minors

This proves observation (a) on page 40 of Graph Minors I. Convert a
minor to its actual branch model, then use the bags meeting each
branch. When the ambient edge-label type is empty, the minor has
no edges either, and the empty decomposition suffices.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- Observation (a) in the proof of GM01 (1.2), page 40: a minor has
path-width no greater than the original graph. -/
theorem HasPathWidthLE.of_isIsoMinor {α β γ δ : Type*}
    {H : Graph α β} {G : Graph γ δ} {k : ℕ}
    (hG : HasPathWidthLE G k) (hH : V(H).Finite)
    (hV : V(G).Finite) (hE : E(G).Finite) (hMinor : IsIsoMinor H G) :
    HasPathWidthLE H k := by
  cases isEmpty_or_nonempty δ with
  | inl hEmpty =>
    let : IsEmpty δ := hEmpty
    obtain ⟨K, _, C, _, ⟨iso⟩⟩ := hMinor
    have hNo : ∀ e, e ∉ E(H) := by
      intro e he
      exact isEmptyElim (iso.edgeEquiv ⟨e, he⟩).val
    refine ⟨⟨0, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i, ?_, ?_⟩, fun i ↦ Fin.elim0 i⟩
    · intro e x y he
      exact False.elim (hNo e he.edge_mem)
    · intro i
      exact Fin.elim0 i
  | inr hNonempty =>
    let : Nonempty δ := hNonempty
    obtain ⟨fv, fe, M⟩ := exists_isMinorModel_of_isIsoMinor hV hE hMinor
    exact hG.of_minorModel hH M

end GraphMinor.GM01
