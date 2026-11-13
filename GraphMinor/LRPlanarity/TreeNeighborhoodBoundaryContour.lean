module

public import GraphMinor.LRPlanarity.TreeNeighborhoodContourRecursion
public import GraphMinor.HP25.Web
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.LRPlanarity.TreeNeighborhoodBoundaryNonalternation
import GraphMinor.LRPlanarity.TreeNeighborhoodLeafOrder

/-!
# Nonalternation of the actual component contour

Part IV, Section 7c of the planarity note applies the exterior K5
obstruction after the boundary has been identified with the contour
recursion. Distinct cotree edges have disjoint exterior parts. Strict
boundary parameters therefore exclude alternating endpoint indices.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- A back edge's two ports belong to the same rooted component. -/
theorem port_ancestor_iff_source {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    {root : Fin N} (hroot : T.parent root = none) (p : Port N) (hp : T.BackEdge G p.edge) :
    T.Ancestor root p.vertex ↔ T.Ancestor root p.edge.1 := by
  cases hs : p.source
  · simp only [Port.vertex,hs,Bool.false_eq_true,ite_false]
    exact ⟨fun h => h.trans hp.2.1,fun h => root_ancestor_of_ancestor hroot h hp.2.1⟩
  · simp only [Port.vertex,hs,ite_true]

private theorem not_alternatingIndices_same_left (a b c : ℕ) : ¬AlternatingIndices a a b c := by
  intro h
  rcases h with ⟨hfirst,hmiddle,_⟩ | ⟨_,hmiddle,hlast⟩
  · simp only [min_self,max_self] at hfirst hmiddle
    exact Nat.lt_asymm hfirst hmiddle
  · simp only [min_self,max_self] at hmiddle hlast
    exact Nat.lt_asymm hmiddle hlast

private theorem not_alternatingIndices_same_right (a b c : ℕ) : ¬AlternatingIndices a b c c := by
  intro h
  apply not_alternatingIndices_same_left c a b
  exact h.elim Or.inr Or.inl

/-- Part IV, Section 7c: a component word read along its neighborhood
boundary is nonalternating. Its concrete exterior lines come from the
original embedding with the neighborhood interior removed. -/
theorem nonalternating_of_component_boundary_order {N : ℕ} {G : SimpleGraph (Fin N)}
    (T : Forest N) (drawing : HP25.PlaneEmbedding G univ) (root : Fin N)
    (hroot : T.parent root = none) (D : Set ℂ) (port : Port N → ℂ)
    (hD : IsClosedDisc D)
    (hvertices : ∀ v, T.Ancestor root v → drawing.pt v ∈ interior D)
    (hexterior : ∀ b, T.BackEdge G b → T.Ancestor root b.1 →
      port ⟨b,true⟩ ∈ frontier D ∧ port ⟨b,false⟩ ∈ frontier D ∧
      IsLineWithEnds (drawing.line b.1 b.2 \ interior D) (port ⟨b,true⟩) (port ⟨b,false⟩) ∧
      (drawing.line b.1 b.2 \ interior D) ∩ D = {port ⟨b,true⟩,port ⟨b,false⟩})
    (word : List (Port N))
    (hword : ∀ p, p ∈ word ↔ T.BackEdge G p.edge ∧ T.Ancestor root p.edge.1)
    (parameter : Port N → ℝ) (f : ℝ → ℂ)
    (hf : Continuous f) (hIco : InjOn f (Ico (0 : ℝ) 1)) (hIoc : InjOn f (Ioc (0 : ℝ) 1))
    (himage : f '' Icc (0 : ℝ) 1 = frontier D)
    (hparameters : ∀ p ∈ word, parameter p ∈ Ioo (0 : ℝ) 1 ∧ f (parameter p) = port p)
    (hsortword : word.Pairwise (fun p q => parameter p < parameter q)) : Nonalternating word := by
  intro b c hbc halt
  by_cases hb : T.BackEdge G b ∧ T.Ancestor root b.1
  · by_cases hc : T.BackEdge G c ∧ T.Ancestor root c.1
    · obtain ⟨_,_,hB,hBD⟩ := hexterior b hb.1 hb.2
      obtain ⟨_,_,hC,hCD⟩ := hexterior c hc.1 hc.2
      have hdisjoint : Disjoint (drawing.line b.1 b.2 \ interior D)
          (drawing.line c.1 c.2 \ interior D) := by
        rw [disjoint_left]
        intro x hxB hxC
        have hinter := drawing.inter b.1 (mem_univ _) b.2 (mem_univ _)
          c.1 (mem_univ _) c.2 (mem_univ _) hb.1.1 hc.1.1 (backEdge_unordered_ne hb.1 hc.1 hbc)
          ⟨hxB.1,hxC.1⟩
        obtain ⟨v,hv,he⟩ := hinter
        rcases hv.1 with hvs | hvt
        · exact hxB.2 (he ▸ hvertices v (hvs.symm ▸ hb.2))
        · have htarget := root_ancestor_of_ancestor hroot hb.2 hb.1.2.1
          exact hxB.2 (he ▸ hvertices v (hvt.symm ▸ htarget))
      exact not_alternating_boundary_indices hD word port parameter f hf hIco hIoc himage
        hparameters hsortword ((hword _).mpr hb) ((hword _).mpr hb)
        ((hword _).mpr hc) ((hword _).mpr hc) hB hC hBD hCD hdisjoint halt
    · have hsource : (⟨c,true⟩ : Port N) ∉ word := fun h => hc ((hword _).mp h)
      have htarget : (⟨c,false⟩ : Port N) ∉ word := fun h => hc ((hword _).mp h)
      rw [List.idxOf_eq_length hsource,List.idxOf_eq_length htarget] at halt
      exact not_alternatingIndices_same_right _ _ _ halt
  · have hsource : (⟨b,true⟩ : Port N) ∉ word := fun h => hb ((hword _).mp h)
    have htarget : (⟨b,false⟩ : Port N) ∉ word := fun h => hb ((hword _).mp h)
    rw [List.idxOf_eq_length hsource,List.idxOf_eq_length htarget] at halt
    exact not_alternatingIndices_same_left _ _ _ halt

end GraphMinor.LRPlanarity
