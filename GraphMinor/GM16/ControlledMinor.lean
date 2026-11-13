module

public import GraphMinor.GM16.Section3
import GraphMinor.GM12.Section4Model
import GraphMinor.Minor.Basic

/-!
# Controlled minors are minors

In the proof of XVI (1.3), page 51, a tangle in a subgraph of an
excluded-minor graph controls no copy of the excluded minor.
We retain the branch sets of a controlled minor to obtain its minor
model, and then use the model-to-minor theorem.
-/

public section
namespace GraphMinor.GM16
open Set Graph
universe u v u' v'

/-- A controlled minor of a finite graph is an isomorphic minor.
The tangle-control condition is additional to its minor model. -/
theorem ControlsMinor.isIsoMinor {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'} {G : Graph α β} {L : Graph α' β'}
    {T : Set (Hypergraph α β × Hypergraph α β)}
    (h : ControlsMinor G L T) (hVL : V(L).Finite) (hEL : E(L).Finite)
    (hVG : V(G).Finite) (hEG : E(G).Finite) : IsIsoMinor L G := by
  obtain ⟨ηv, ηe, hModel, _, _⟩ := GM12.controlsMinor_has_minorModel hVG hEG
    (gm12_controlsMinor_of_controlsMinor hVG hEG h (le_refl V(L).ncard))
  exact isIsoMinor_of_isMinorModel L G hVL hEL hVG hEG ηv ηe hModel

/-- A minor in a subgraph is a minor in the original graph. -/
theorem isIsoMinor_of_le {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'} {G H : Graph α β} {L : Graph α' β'}
    (h : IsIsoMinor L H) (hHG : H ≤ G) : IsIsoMinor L G := by
  obtain ⟨K, hKH, C, hC, hIso⟩ := h
  exact ⟨K, hKH.trans hHG, C, hC, hIso⟩

/-- The first sentence of Claim (1) in the proof of XVI (1.3), page 51:
a tangle in a subgraph of an excluded-minor graph controls no such minor. -/
theorem not_controlsMinor_of_excluded_minor {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'} {G H : Graph α β} {L : Graph α' β'}
    {T : Set (Hypergraph α β × Hypergraph α β)}
    (hVL : V(L).Finite) (hEL : E(L).Finite) (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hNo : ¬ IsIsoMinor L G) (hHG : H ≤ G) : ¬ ControlsMinor H L T := by
  intro hControl
  exact hNo (isIsoMinor_of_le
    (hControl.isIsoMinor hVL hEL (hVG.subset hHG.vertexSet_mono)
      (hEG.subset hHG.edgeSet_mono)) hHG)

end GraphMinor.GM16
