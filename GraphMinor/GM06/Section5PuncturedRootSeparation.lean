module

public import GraphMinor.GM06.Section3Induce
import GraphMinor.GM06.Section5PuncturedRootDrawing
import GraphMinor.GM06.Section5SeparationGeometry
import GraphMinor.GM11.Walks

/-!
# The punctured root as a side of a vertex separation

For the retained barrier in VI (5.5), page 130, a component of
the graph with the attachment removed has no neighbour outside
it except the attachment. Its incident-edge neighbourhood therefore
has precisely those vertices and the attachment. Its edges are the
complement of the drawing induced on the other vertices. This gives
a separation whose sides meet only at the attachment, while the
chosen side remains connected after that point is removed.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A retained component attached to the remaining vertices only
at s has a connected punctured separation side with exact vertices. -/
theorem exists_punctured_root_separation
    {S : Type} [TopologicalSpace S] [T2Space S] {G P : Drawing S}
    (hPG : P.IsSubdrawing G) (hP : IsConnected P.U)
    {s : S} (hs : s ∈ G.V) (hsP : s ∉ P.U)
    (hport : ∀ e a b, G.toGraph.IsLink e a b → a ∈ P.V → b ∈ P.V ∨ b = s) :
    ∃ T : Drawing S,
      IsGraphSeparation G.toGraph (induceDrawing G (G.V \ P.V)).toGraph T.toGraph ∧
      T.V = P.V ∪ {s} ∧ IsConnected (T.U \ {s}) ∧ P.IsSubdrawing T := by
  obtain ⟨T, hTG, hPT, hsT, hTE, hTU, hconn⟩ := exists_punctured_root_subdrawing hPG hP hs hsP
  let R := induceDrawing G (G.V \ P.V)
  have hRG : R.IsSubdrawing G := induceDrawing_isSubdrawing G sdiff_subset
  have hRV : R.V = G.V \ P.V := induceDrawing_V G sdiff_subset
  have hends (e) (he : e ∈ T.E) : closure e ∩ G.V ⊆ P.V ∪ {s} := by
    obtain ⟨heG, v, hvP, hvcl⟩ := hTE ▸ he
    obtain ⟨a, b, hl⟩ := G.toGraph.exists_isLink_of_mem_edgeSet heG
    have hvend : v ∈ ({a, b} : Set S) := hl.2.2.2 ▸ ⟨hvcl, hPG.1 hvP⟩
    have hab : a ∈ P.V ∪ {s} ∧ b ∈ P.V ∪ {s} := by
      rcases hvend with rfl | hvb
      · exact ⟨Or.inl hvP, (hport e v b hl hvP).elim Or.inl Or.inr⟩
      · have hvb' := mem_singleton_iff.mp hvb
        subst v
        exact ⟨(hport e b a hl.symm hvP).elim Or.inl Or.inr, Or.inl hvP⟩
    rw [hl.2.2.2]
    rintro x (rfl | hxb)
    · exact hab.1
    · exact mem_singleton_iff.mp hxb ▸ hab.2
  have hTV : T.V = P.V ∪ {s} := by
    apply subset_antisymm
    · intro x hxT
      have hxU := T.V_subset_U hxT
      rw [hTU] at hxU
      rcases hxU with (hxP | hxs) | hxe
      · exact Or.inl (vertex_mem_of_mem_subdrawing_point_set hPG hxP (hTG.1 hxT))
      · exact Or.inr hxs
      · obtain ⟨e, he, hxcl⟩ := mem_iUnion₂.mp hxe
        exact hends e he ⟨hxcl, hTG.1 hxT⟩
    · exact union_subset hPT.1 (singleton_subset_iff.mpr hsT)
  have hTEcompl : T.E = G.E \ R.E := by
    ext e
    rw [hTE, induceDrawing_E]
    constructor
    · rintro ⟨heG, v, hvP, hvcl⟩
      refine ⟨heG, ?_⟩
      rintro ⟨_, hsub⟩
      exact (hsub ⟨hvcl, hPG.1 hvP⟩).2 hvP
    · rintro ⟨heG, heR⟩
      refine ⟨heG, ?_⟩
      by_contra hnone
      apply heR
      refine ⟨heG, ?_⟩
      rintro v ⟨hvcl, hvG⟩
      exact ⟨hvG, fun hvP => hnone ⟨v, hvP, hvcl⟩⟩
  have hRle : R.toGraph ≤ G.toGraph :=
    ⟨hRG.1, fun e a b hl => (hRG.isLink_iff hl.1).mp hl⟩
  have hTle : T.toGraph ≤ G.toGraph :=
    ⟨hTG.1, fun e a b hl => (hTG.isLink_iff hl.1).mp hl⟩
  refine ⟨T, ⟨hRle, hTle, ?_, ?_, ?_⟩, hTV, hconn, hPT⟩
  · change R.V ∪ T.V = G.V
    rw [hRV, hTV]
    apply subset_antisymm
    · exact union_subset sdiff_subset (union_subset hPG.1 (singleton_subset_iff.mpr hs))
    · intro x hx
      by_cases hxP : x ∈ P.V
      · exact Or.inr (Or.inl hxP)
      · exact Or.inl ⟨hx, hxP⟩
  · change R.E ∪ T.E = G.E
    rw [hTEcompl, union_comm]
    exact sdiff_union_of_subset hRG.2
  · change Disjoint R.E T.E
    rw [hTEcompl]
    exact disjoint_left.mpr (fun e heR heT => heT.2 heR)

end GraphMinor.GM06
