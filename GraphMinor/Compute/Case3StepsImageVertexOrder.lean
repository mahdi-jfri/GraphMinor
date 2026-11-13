module

public import GraphMinor.Compute.Case3StepsPushMultigraph

/-!
# Composing the two increasing member vertex lists

A member is first numbered inside the compact compass, and the compass is
numbered inside the original graph. Their composition is the increasing
enumeration of the member's original vertex set. This identifies the compact
wall type required by the exact output interface.
-/

public section

namespace GraphMinor.Compute

/-- Mapping a member through the increasing compass list preserves its cardinality. -/
theorem case3ImageVertexCard {N : ℕ} (S : Finset (Fin N)) (T : Finset (Fin S.card))
    (U : Finset (Fin N)) (hU : U = T.image (S.orderEmbOfFin rfl)) : U.card = T.card := by
  rw [hU, Finset.card_image_of_injective _ (S.orderEmbOfFin rfl).injective]

/-- The increasing enumeration of the original member vertex set is the
composition of the increasing member and compass enumerations. -/
theorem case3ImageVertexOrder_apply {N : ℕ} (S : Finset (Fin N)) (T : Finset (Fin S.card))
    (U : Finset (Fin N)) (hU : U = T.image (S.orderEmbOfFin rfl)) (i : Fin T.card) :
    U.orderEmbOfFin rfl (Fin.cast (case3ImageVertexCard S T U hU).symm i) =
      S.orderEmbOfFin rfl (T.orderEmbOfFin rfl i) := by
  have hf : (fun j : Fin T.card => S.orderEmbOfFin rfl (T.orderEmbOfFin rfl j)) =
      U.orderEmbOfFin (case3ImageVertexCard S T U hU) := by
    apply Finset.orderEmbOfFin_unique
    · intro j
      rw [hU]
      exact Finset.mem_image.mpr ⟨T.orderEmbOfFin rfl j, T.orderEmbOfFin_mem rfl j, rfl⟩
    · exact (S.orderEmbOfFin rfl).strictMono.comp (T.orderEmbOfFin rfl).strictMono
  have hg : (fun j : Fin T.card => U.orderEmbOfFin rfl
        (Fin.cast (case3ImageVertexCard S T U hU).symm j)) =
      U.orderEmbOfFin (case3ImageVertexCard S T U hU) := by
    apply Finset.orderEmbOfFin_unique
    · intro j
      exact U.orderEmbOfFin_mem rfl _
    · intro a b hab
      apply (U.orderEmbOfFin rfl).strictMono
      change a.1 < b.1
      exact hab
  exact congrFun (hg.trans hf.symm) i

/-- The two compact member graphs have identical directed multiplicities
under the cardinality cast induced by the original vertex set. -/
theorem case3PushMultigraph_induce_image_edgeMult {N : ℕ} (S : Finset (Fin N))
    (D : MultiDigraph S.card) (T : Finset (Fin S.card)) (U : Finset (Fin N))
    (hU : U = T.image (S.orderEmbOfFin rfl)) (u v : Fin T.card) :
    ((case3PushMultigraph S D).induce (U.orderEmbOfFin rfl)).edgeMult
      (Fin.cast (case3ImageVertexCard S T U hU).symm u)
      (Fin.cast (case3ImageVertexCard S T U hU).symm v) =
      (D.induce (T.orderEmbOfFin rfl)).edgeMult u v := by
  change (case3PushMultigraph S D).edgeMult _ _ = _
  rw [case3ImageVertexOrder_apply S T U hU u, case3ImageVertexOrder_apply S T U hU v,
    case3PushMultigraph_edgeMult_image]
  rfl

end GraphMinor.Compute
