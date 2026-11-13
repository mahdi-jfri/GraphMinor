module

public import GraphMinor.Compute.Case3StepsDivisionLift
public import GraphMinor.Compute.Case3StepsBipartite

/-!
# Rurality of the multigraph division lift

Step (5) of XIII (9.9), page 104, applies (8.6) to the wall society. After
restoring multigraph edges, the division conditions follow from the boundary
and path lemmas. Its bipartite graph is isomorphic to the simple division's
bipartite graph: the map sends a member to its lift and a boundary vertex `u`
to `u.val`. The rural drawing is unchanged under this isomorphism.
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM13 GraphMinor.Transport Classical

/-- Restoring all parallel copies of member edges and assigning each loop to
one member preserves a rural division (XIII, Section 8, pages 95--96).
The map on boundary labels is `Fin.val`, with the cyclic order transported by
that embedding. -/
theorem case3LiftedFamily_isRuralDivision {n : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup)
    (F : Set (Alg86Subgraph D.toSimpleGraph))
    (hR : IsRuralDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' F))
    (S : Society ℕ (ℕ × ℕ × ℕ)) (hS : S.G = D.toGMDigraph.toGraph)
    (hΩ : S.Ω = relabelCyclicPerm ⟨Fin.val, Fin.val_injective⟩
      (case3SimpleSocietyInput D omega homega).toSociety.Ω)
    (assignment : Case3LoopAssignment (case3SimpleSocietyInput D omega homega) F :=
      case3DefaultLoopAssignment (case3SimpleSocietyInput D omega homega) F hR.isDivision) :
    IsRuralDivision S (case3LiftedFamily D omega homega F hR.isDivision assignment) := by
  let x := case3SimpleSocietyInput D omega homega
  let f : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let L := fun A => case3LiftMember D A (case3AssignedLoops assignment A)
  have hL : Function.Injective L := fun A B h => case3LiftMember_eq_imp D _ _ h
  have hF : F.Finite := hR.finite_𝒜.of_finite_image Alg86Subgraph.toGMGraph_injective.injOn
  let e₀ := Equiv.Set.image Alg86Subgraph.toGMGraph F Alg86Subgraph.toGMGraph_injective
  let e₁ := Equiv.Set.image L F hL
  let m : (Alg86Subgraph.toGMGraph '' F) ≃ (L '' F) := e₀.symm.trans e₁
  have hm : ∀ A : F, (m ⟨A.1.toGMGraph, ⟨A.1, A.2, rfl⟩⟩).1 = L A.1 := by
    intro A
    have heq : e₀.symm ⟨A.1.toGMGraph, ⟨A.1, A.2, rfl⟩⟩ = A :=
      (Equiv.symm_apply_eq e₀).mpr rfl
    change L (e₀.symm ⟨A.1.toGMGraph, ⟨A.1, A.2, rfl⟩⟩).1 = _
    rw [heq]
  have hbar₀ : S.Ω.bar = f '' x.toSociety.Ω.bar := by
    rw [hΩ, relabelCyclicPerm_bar]
  have hxbar : x.toSociety.Ω.bar = (omega.toFinset : Set (Fin n)) := by
    ext u
    rw [Alg81Input.toSociety_bar]
    change (u ∈ omega) ↔ u ∈ omega.toFinset
    exact List.mem_toFinset.symm
  have hbar : S.Ω.bar = Fin.val '' (omega.toFinset : Set (Fin n)) := by
    rw [hbar₀, hxbar]
    rfl
  have hbd : ∀ A : (Alg86Subgraph.toGMGraph '' F),
      divBoundary S (m A).1 = f '' divBoundary x.toSociety A.1 := by
    rintro ⟨_, A, hA, rfl⟩
    rw [hm ⟨A, hA⟩, divBoundary_toGMGraph]
    exact case3LiftMember_boundary_eq D omega homega F hR.isDivision hA S hS hbar assignment
  let iso := case3DivisionBipartiteIso x.toSociety S
    (Alg86Subgraph.toGMGraph '' F) (L '' F) m f hbar₀ hbd
  obtain ⟨hV, hE, hb, hr⟩ := hR.isRuralBipartite
  have hV' : V(divisionBipartiteGraph S (L '' F)).Finite := by
    have := hV.to_subtype
    have := Finite.of_equiv _ iso.vertexEquiv
    exact Set.finite_coe_iff.mp inferInstance
  have hE' : E(divisionBipartiteGraph S (L '' F)).Finite := by
    have := hE.to_subtype
    have := Finite.of_equiv _ iso.edgeEquiv
    exact Set.finite_coe_iff.mp inferInstance
  have hb' : (liftCyclicPermInr S.Ω).bar ⊆ V(divisionBipartiteGraph S (L '' F)) := by
    rintro _ ⟨u, hu, rfl⟩
    exact Or.inr ⟨u, Or.inr hu, rfl⟩
  refine ⟨case3LiftedFamily_isDivision D omega homega F hR.isDivision S hS hbar assignment,
    hF.image L, hV', hE', hb', ?_⟩
  let g : Sym2 (Fin n) ↪ (ℕ × ℕ × ℕ) :=
    ⟨fun e => ((Fintype.equivFin _ e).1, 0, 0), fun a b h =>
      (Fintype.equivFin _).injective (Fin.ext (congrArg Prod.fst h))⟩
  let fB := bipartiteVertexEmb f g
  apply case3RuralSociety_of_boundaryIso iso fB ?_ ?_ hr
  · change liftCyclicPermInr S.Ω = relabelCyclicPerm fB (liftCyclicPermInr x.toSociety.Ω)
    rw [hΩ]
    exact liftCyclicPermInr_relabelCyclicPerm f g x.toSociety.Ω
  · rintro _ ⟨u, hu, rfl⟩
    change (iso.vertexEquiv ⟨Sum.inr u, _⟩).1 = Sum.inr (f u)
    exact case3DivisionBipartiteIso_vertex_inr x.toSociety S
      (Alg86Subgraph.toGMGraph '' F) (L '' F) m f hbar₀ hbd u _

end GraphMinor.Compute
