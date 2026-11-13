module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5PuncturedStarConnected
import GraphMinor.GM11.Defs
import GraphMinor.GM11.Walks

/-!
# Constructing the retained punctured barrier

For the attached-branch enclosures in VI (5.5), page 130, take
a connected retained component away from the attachment. Adjoin
the attachment and all edges with an endpoint in that component.
The resulting subdrawing retains the component and is connected
after the attachment is removed. Keeping its edge and point-set
formulas allows the component separation to identify its exact vertices.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Construct the incident-edge neighbourhood of a connected
retained component, including the attachment but excluding loops
based only at that attachment. Its punctured point set is connected. -/
theorem exists_punctured_root_subdrawing
    {S : Type} [TopologicalSpace S] [T2Space S] {G P : Drawing S}
    (hPG : P.IsSubdrawing G) (hP : IsConnected P.U)
    {s : S} (hs : s ∈ G.V) (hsP : s ∉ P.U) :
    ∃ T : Drawing S, T.IsSubdrawing G ∧ P.IsSubdrawing T ∧ s ∈ T.V ∧
      T.E = {e ∈ G.E | ∃ v ∈ P.V, v ∈ closure e} ∧
      T.U = (P.U ∪ {s}) ∪ ⋃ e ∈ T.E, closure e ∧ IsConnected (T.U \ {s}) := by
  let E := {e ∈ G.E | ∃ v ∈ P.V, v ∈ closure e}
  let T := G.span (P.V ∪ {s}) E
  have hTG : T.IsSubdrawing G := Drawing.span_isSubdrawing G _ _
  have hTE : T.E = E := by
    rw [Drawing.span_E]
    exact inter_eq_left.mpr (fun _ he => he.1)
  have hPT : P.IsSubdrawing T := by
    constructor
    · intro x hx
      rw [Drawing.span_V, Drawing.spanV]
      exact Or.inl ⟨Or.inl hx, hPG.1 hx⟩
    · intro e he
      rw [hTE]
      obtain ⟨v, w, hl⟩ := P.toGraph.exists_isLink_of_mem_edgeSet he
      have hvcl : v ∈ closure e :=
        (show v ∈ closure e ∩ P.V from hl.2.2.2.symm ▸ mem_insert v {w}).1
      exact ⟨hPG.2 he, v, hl.left_mem, hvcl⟩
  have hsT : s ∈ T.V := by
    rw [Drawing.span_V, Drawing.spanV]
    exact Or.inl ⟨Or.inr rfl, hs⟩
  have hTU : T.U = (P.U ∪ {s}) ∪ ⋃ e ∈ T.E, closure e := by
    apply subset_antisymm
    · intro x hx
      change x ∈ G.spanV (P.V ∪ {s}) E ∪ ⋃ e ∈ E ∩ G.E, closure e at hx
      rcases hx with hxV | hxE
      · rw [Drawing.spanV] at hxV
        rcases hxV with ⟨hxP | hxs, _⟩ | hxends
        · exact Or.inl (Or.inl (P.V_subset_U hxP))
        · exact Or.inl (Or.inr hxs)
        · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxends
          exact Or.inr (mem_iUnion₂.mpr ⟨e, hTE.symm ▸ he.1, hxe.1⟩)
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxE
        exact Or.inr (mem_iUnion₂.mpr ⟨e, hTE.symm ▸ he.1, hxe⟩)
    · rintro x ((hxP | hxs) | hxE)
      · exact hPT.U_subset hxP
      · exact mem_singleton_iff.mp hxs ▸ T.V_subset_U hsT
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxE
        exact T.closure_subset_U he hxe
  have hpuncture : T.U \ {s} = P.U ∪ ⋃ e ∈ E, (closure e \ {s}) := by
    rw [hTU, hTE]
    apply subset_antisymm
    · rintro x ⟨(hxP | hxs) | hxE, hxne⟩
      · exact Or.inl hxP
      · exact False.elim (hxne hxs)
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxE
        exact Or.inr (mem_iUnion₂.mpr ⟨e, he, hxe, hxne⟩)
    · rintro x (hxP | hxE)
      · refine ⟨Or.inl (Or.inl hxP), ?_⟩
        intro hxs
        exact hsP (mem_singleton_iff.mp hxs ▸ hxP)
      · obtain ⟨e, he, hxe, hxne⟩ := mem_iUnion₂.mp hxE
        exact ⟨Or.inr (mem_iUnion₂.mpr ⟨e, he, hxe⟩), hxne⟩
  refine ⟨T, hTG, hPT, hsT, hTE, hTU, ?_⟩
  rw [hpuncture]
  exact isConnected_union_punctured_incident_edges hPG hP hs hsP
    (fun _ he => he.1) (fun _ he => he.2)

end GraphMinor.GM06
