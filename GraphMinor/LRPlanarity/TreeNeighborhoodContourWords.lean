module

public import GraphMinor.LRPlanarity.DefsContour
public import GraphMinor.HP25.Web
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.LRPlanarity.TreeNeighborhoodBoundaryPorts
import GraphMinor.LRPlanarity.TreeNeighborhoodBoundaryNonalternation
import GraphMinor.LRPlanarity.TreeNeighborhoodLeafOrder
import GraphMinor.Surface.PlaneOrientation

/-!
# Nonalternating port words on one tree neighborhood boundary

Part IV, Sections 7b and 7c of the planarity note reads the finitely many
ports on each component disc in boundary order. The exterior arcs of
distinct back edges are disjoint, since all common original vertices lie
inside the disc. The exterior K5 obstruction therefore makes the boundary
word nonalternating. Identifying this word with the local tree-contour
recursion is a separate boundary-substitution step.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

instance instFinitePort (N : ℕ) : Finite (Port N) :=
  Finite.of_injective (fun p : Port N => (p.edge,p.source)) (by
    intro p q he
    cases p with
    | mk e side =>
      cases q with
      | mk f side' =>
        change (e,side) = (f,side') at he
        cases he
        rfl)

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

/-- Part IV, Sections 7b and 7c: the boundary of a component neighborhood
admits a nonalternating word containing each active back-edge port once.
The hypotheses are the concrete neighborhood conclusions, not a contour
order or a nonalternation assumption. -/
theorem exists_nonalternating_component_boundary_word {N : ℕ} {G : SimpleGraph (Fin N)}
    (T : Forest N) (drawing : HP25.PlaneEmbedding G univ) (root : Fin N)
    (hroot : T.parent root = none) (D : Set ℂ) (port : Port N → ℂ)
    (hD : IsClosedDisc D)
    (hvertices : ∀ v, T.Ancestor root v → drawing.pt v ∈ interior D)
    (hinj : InjOn port {p | T.BackEdge G p.edge ∧ T.Ancestor root p.edge.1})
    (hexterior : ∀ b, T.BackEdge G b → T.Ancestor root b.1 →
      port ⟨b,true⟩ ∈ frontier D ∧ port ⟨b,false⟩ ∈ frontier D ∧
      IsLineWithEnds (drawing.line b.1 b.2 \ interior D) (port ⟨b,true⟩) (port ⟨b,false⟩) ∧
      (drawing.line b.1 b.2 \ interior D) ∩ D = {port ⟨b,true⟩,port ⟨b,false⟩}) :
    ∃ word : List (Port N), word.Nodup ∧
      (∀ p, p ∈ word ↔ T.BackEdge G p.edge ∧ T.Ancestor root p.edge.1) ∧ Nonalternating word := by
  classical
  let active := fun p : Port N => T.BackEdge G p.edge ∧ T.Ancestor root p.edge.1
  let A := {p : Port N // active p}
  have hbd : discBd D = frontier D :=
    (subBd_eq_discBd_complex hD).symm.trans (Surface.subBd_eq_frontier _)
  have hcircle : IsOArc (frontier D) := hbd ▸ hD.isOArc_discBd
  have hportmem : ∀ p : A, port p.val ∈ frontier D := by
    intro p
    have h := hexterior p.val.edge p.property.1 p.property.2
    change port ⟨p.val.edge,p.val.source⟩ ∈ frontier D
    cases p.val.source
    · exact h.2.1
    · exact h.1
  obtain ⟨ordered,f,θ,hordered,hall,hf,hIco,hIoc,himage,hθ,hsorted⟩ :=
    exists_ordered_boundary_ports hcircle (fun p : A => port p.val)
      (fun p q he => Subtype.ext (hinj p.property q.property he)) hportmem
  let word := ordered.map Subtype.val
  let parameter := fun p : Port N => if h : active p then θ ⟨p,h⟩ else 0
  have hparam : ∀ p : A, parameter p.val = θ p := fun p => dite_eq_left p.property
  have hword : ∀ p : Port N, p ∈ word ↔ active p := by
    intro p
    constructor
    · intro hp
      obtain ⟨q,_,he⟩ := List.mem_map.mp hp
      exact he ▸ q.property
    · intro hp
      exact List.mem_map.mpr ⟨⟨p,hp⟩,hall ⟨p,hp⟩,rfl⟩
  have hparameters : ∀ p ∈ word, parameter p ∈ Ioo (0 : ℝ) 1 ∧ f (parameter p) = port p := by
    intro p hp
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hp
    rw [hparam q]
    exact hθ q
  have hsortword : word.Pairwise (fun p q => parameter p < parameter q) := by
    apply List.pairwise_map.mpr
    apply hsorted.imp
    intro p q h
    simpa only [hparam p,hparam q] using h
  refine ⟨word,hordered.map Subtype.val_injective,hword,?_⟩
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
