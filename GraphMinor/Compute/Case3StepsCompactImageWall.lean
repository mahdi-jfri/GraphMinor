module

public import GraphMinor.Compute.Case3StepsImageVertexOrder
public import GraphMinor.Compute.Case3StepsPushMemberGraph
public import GraphMinor.Compute.Algorithm99TransportMove

/-!
# The compact wall type of the original member

The image of the member vertex list has the same cardinality. Its increasing
numbering agrees with the composition of the member and compass lists.
Consequently the supplied compact wall can be cast to the exact compact
original-member type, and moving it back writes the wall encoding computed
through that composition.
-/

public section

namespace GraphMinor.Compute

open Graph

/-- Moving a wall twice composes its vertex-label maps. -/
theorem case3Wall_moveOrig_comp {h n m N : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (B : MultiDigraph m) (C : MultiDigraph N) (f : Fin n → Fin m) (g : Fin m → Fin N) :
    (W.moveOrig B f).moveOrig C g = W.moveOrig C (fun u => g (f u)) := by
  cases W
  simp only [WallOfHeight.moveOrig, List.map_map, Function.comp_def]

/-- A wall on compact member labels has a valid representative on the
exact compact type used for the restored member output. Moving that
representative back agrees with the program's composed inverse list. -/
theorem case3CompactImageWall_exists {h N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card)
    (T : Finset (Fin S.card)) (W : WallOfHeight h (D.induce (T.orderEmbOfFin rfl)))
    (hW : W.IsValid) :
    let P := case3PushMultigraph S D
    let V := T.image (S.orderEmbOfFin rfl)
    ∃ W_A : WallOfHeight h (P.deleteVerticesCompact Vᶜ), W_A.IsValid ∧
      (W_A.moveOrig P (compactEmb Vᶜ)).IsValid ∧
      W_A.moveOrig P (compactEmb Vᶜ) = W.moveOrig P
        (fun u => S.orderEmbOfFin rfl (T.orderEmbOfFin rfl u)) := by
  classical
  let P := case3PushMultigraph S D
  let V := T.image (S.orderEmbOfFin rfl)
  let U := Vᶜᶜ
  have hU : U = T.image (S.orderEmbOfFin rfl) := compl_compl V
  let c := case3ImageVertexCard S T U hU
  let e : Fin T.card → Fin U.card := Fin.cast c.symm
  have he : Function.Injective e := by
    intro u v huv
    exact Fin.ext (congrArg (fun z : Fin U.card => z.1) huv)
  have hmult (u v : Fin T.card) :
      (P.deleteVerticesCompact Vᶜ).edgeMult (e u) (e v) = (D.induce (T.orderEmbOfFin rfl)).edgeMult u v :=
    case3PushMultigraph_induce_image_edgeMult S D T U hU u v
  have hadj (u v : Fin T.card) (huv : (D.induce (T.orderEmbOfFin rfl)).toSimpleGraph.Adj u v) :
      (P.deleteVerticesCompact Vᶜ).toSimpleGraph.Adj (e u) (e v) := by
    rw [MultiDigraph.toSimpleGraph_adj] at huv ⊢
    rw [hmult u v, hmult v u]
    exact ⟨fun huv' => huv.1 (he huv'), huv.2⟩
  let W_A := W.moveOrig (P.deleteVerticesCompact Vᶜ) e
  have hW_A : W_A.IsValid := hW.moveOrig e he hadj
  have hnextAdj (u v : Fin Vᶜᶜ.card)
      (huv : (P.deleteVerticesCompact Vᶜ).toSimpleGraph.Adj u v) :
      P.toSimpleGraph.Adj (compactEmb Vᶜ u) (compactEmb Vᶜ v) := by
    rw [MultiDigraph.toSimpleGraph_adj] at huv ⊢
    exact ⟨fun heq => huv.1 ((compactEmb Vᶜ).injective heq), huv.2⟩
  have hnext : (W_A.moveOrig P (compactEmb Vᶜ)).IsValid :=
    hW_A.moveOrig (compactEmb Vᶜ) (compactEmb Vᶜ).injective hnextAdj
  refine ⟨W_A, hW_A, hnext, ?_⟩
  rw [case3Wall_moveOrig_comp]
  apply congrArg (fun f => W.moveOrig P f)
  funext u
  exact case3ImageVertexOrder_apply S T U hU u

/-- The exact compact representative also moves back to a wall inside
the original member vertex restriction, with the original wall height. -/
theorem case3CompactImageWall_exists_le {h N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card)
    (T : Finset (Fin S.card)) (W : WallOfHeight h (D.induce (T.orderEmbOfFin rfl)))
    (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    let P := case3PushMultigraph S D
    let V := T.image (S.orderEmbOfFin rfl)
    ∃ W_A : WallOfHeight h (P.deleteVerticesCompact Vᶜ), W_A.IsValid ∧
      ∃ hnext : (W_A.moveOrig P (compactEmb Vᶜ)).IsValid,
        ((W_A.moveOrig P (compactEmb Vᶜ)).toGMWall h2 he hnext).graph ≤
          P.toGMDigraph.toGraph.induce V.toNatSet ∧
        W_A.moveOrig P (compactEmb Vᶜ) = W.moveOrig P
          (fun u => S.orderEmbOfFin rfl (T.orderEmbOfFin rfl u)) := by
  classical
  let P := case3PushMultigraph S D
  let V := T.image (S.orderEmbOfFin rfl)
  obtain ⟨W_A, hWA, hnext, heq⟩ := case3CompactImageWall_exists S D T W hW
  have hle := WallOfHeight.isWallIn_toGMWall (W_A.moveOrig P (compactEmb Vᶜ)) h2 he hnext
  have hverts : V(((W_A.moveOrig P (compactEmb Vᶜ)).toGMWall h2 he hnext).graph) ⊆ V.toNatSet := by
    rw [WallOfHeight.vertexSet_toGMWall_eq, WallOfHeight.vertexFinset_moveOrig]
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
    refine ⟨compactEmb Vᶜ j, ?_, rfl⟩
    have hj := compactEmb_not_mem Vᶜ j
    simpa only [Finset.mem_compl, not_not, Finset.mem_coe] using hj
  refine ⟨W_A, hWA, hnext, ?_, heq⟩
  exact ⟨hverts, fun e u v hlink => ⟨hle.isLink_mono hlink,
    hverts hlink.left_mem, hverts hlink.right_mem⟩⟩

end GraphMinor.Compute
