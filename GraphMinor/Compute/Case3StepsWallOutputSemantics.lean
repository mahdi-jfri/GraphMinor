module

public import GraphMinor.Compute.Case3StepsOriginalMemberFacts
public import GraphMinor.Compute.Case3StepsSelectedBoundary
public import GraphMinor.Compute.Case3StepsInteriorMath
public import GraphMinor.Compute.Algorithm99Case3Claim
import GraphMinor.Compute.Case3StepsAttachmentBound

/-!
# The semantic conditions of a wall result

A selected interior member is restored to original labels in the lifted
rural division. Its computed boundary is the true society boundary, its
vertices avoid both the deleted set and the whole perimeter, and its full
multigraph is a subgraph of the deleted graph. These facts identify the
four arrays written by the member result program with output (b).
-/

public section

namespace GraphMinor.Compute

open Graph GraphMinor.Transport

section

variable {h h' n : ℕ} (G : MultiDigraph n) (X : Finset (Fin n))
  (W : WallOfHeight h (G.deleteVertices X)) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)


variable (d : Alg86DivisionOutput (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW)) (hd :
    IsValidAlg86DivisionOutput (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) d)
  (i : Case3SelectedGroup (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) d.core.Z)


include hd i

/-- A selected interior wall result satisfies the frozen output (b)
specification, with every society and division condition derived from the
valid (8.6) output. -/
theorem case3SelectedWall_isOutputB (h2' : 2 ≤ h') (he' : Even h')
    (havoid : Disjoint W.compassFinset X)
    (hint : Disjoint ((case3SelectedMember (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW)
        d.core.Z i)).verts (case3PullbackBits (compassEmb W) W.perimeterFinset))
    (W_A : WallOfHeight h' (((case3PushMultigraph W.compassFinset (case3RoutedMember
        (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) (case3CompactCompassMultigraph
        (G.deleteVertices X) W) d.core.Z (case3RawIndexLabel (case3CompactSocietyInput (G.deleteVertices
        X) W h2 he hW) i.1)))).deleteVerticesCompact ((case3SelectedMember (case3CompactSocietyInput
        (G.deleteVertices X) W h2 he hW) d.core.Z i).verts.image (W.compassFinset.orderEmbOfFin rfl))ᶜ))
        (hWA : W_A.IsValid)
    (hnext : (W_A.moveOrig (case3PushMultigraph W.compassFinset (case3RoutedMember
        (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) (case3CompactCompassMultigraph
        (G.deleteVertices X) W) d.core.Z (case3RawIndexLabel (case3CompactSocietyInput (G.deleteVertices
        X) W h2 he hW) i.1))) (compactEmb ((case3SelectedMember (case3CompactSocietyInput
        (G.deleteVertices X) W h2 he hW) d.core.Z i).verts.image (W.compassFinset.orderEmbOfFin
        rfl))ᶜ)).IsValid)
    (hsub : ((W_A.moveOrig (case3PushMultigraph W.compassFinset (case3RoutedMember
        (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) (case3CompactCompassMultigraph
        (G.deleteVertices X) W) d.core.Z (case3RawIndexLabel (case3CompactSocietyInput (G.deleteVertices
        X) W h2 he hW) i.1))) (compactEmb ((case3SelectedMember (case3CompactSocietyInput
        (G.deleteVertices X) W h2 he hW) d.core.Z i).verts.image (W.compassFinset.orderEmbOfFin
        rfl))ᶜ)).toGMWall h2' he' hnext).graph ≤
      ((case3PushMultigraph W.compassFinset (case3RoutedMember (case3CompactSocietyInput
          (G.deleteVertices X) W h2 he hW) (case3CompactCompassMultigraph (G.deleteVertices X) W)
          d.core.Z (case3RawIndexLabel (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW)
          i.1)))).toGMDigraph.toGraph.induce (((case3SelectedMember (case3CompactSocietyInput
          (G.deleteVertices X) W h2 he hW) d.core.Z i).verts.image (W.compassFinset.orderEmbOfFin
          rfl))).toNatSet)
    {a_out a_bd a_wall a_enc : ℕ} {s : State}
    (hV : s.arrs a_out = bitSetList ((case3SelectedMember (case3CompactSocietyInput (G.deleteVertices X)
        W h2 he hW) d.core.Z i).verts.image (W.compassFinset.orderEmbOfFin rfl))) (hBd : s.arrs a_bd =
        bitSetList ((case3GroupBoundary (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW)
        d.core.Z i.1).image (W.compassFinset.orderEmbOfFin rfl)))
    (hwall : s.arrs a_wall = (W_A.moveOrig (case3PushMultigraph W.compassFinset (case3RoutedMember
        (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) (case3CompactCompassMultigraph
        (G.deleteVertices X) W) d.core.Z (case3RawIndexLabel (case3CompactSocietyInput (G.deleteVertices
        X) W h2 he hW) i.1))) (compactEmb ((case3SelectedMember (case3CompactSocietyInput
        (G.deleteVertices X) W h2 he hW) d.core.Z i).verts.image (W.compassFinset.orderEmbOfFin
        rfl))ᶜ)).encList)
    (henc : s.arrs a_enc = ((case3PushMultigraph W.compassFinset (case3RoutedMember
        (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) (case3CompactCompassMultigraph
        (G.deleteVertices X) W) d.core.Z (case3RawIndexLabel (case3CompactSocietyInput (G.deleteVertices
        X) W h2 he hW) i.1)))).enc) :
    IsCase3StepsOutputB h h' G X W h2 he hW h2' he' a_out a_bd a_wall a_enc s := by
  classical
  let xc := case3CompactSocietyInput (G.deleteVertices X) W h2 he hW
  let Dc := case3CompactCompassMultigraph (G.deleteVertices X) W
  let Ac := case3SelectedMember xc d.core.Z i
  let Rc := case3RoutedMember xc Dc d.core.Z (case3RawIndexLabel xc i.1)
  let Vs := Ac.verts.image (W.compassFinset.orderEmbOfFin rfl)
  let Bds := (case3GroupBoundary xc d.core.Z i.1).image (W.compassFinset.orderEmbOfFin rfl)
  let P := case3PushMultigraph W.compassFinset Rc
  let omega := List.ofFn (compactCorner W h2 he)
  have homega : omega.Nodup := List.nodup_ofFn.mpr (compactCorner_injective W h2 he hW)
  have hR := case3CompactSelectedMembers_isRuralDivision (G.deleteVertices X) W h2 he hW d hd
  let assignment := case3OrderedLoopAssignment xc d.core.Z hR.isDivision
  let F := relabelGraph (origVertexEmb (compassEmb W) (compassEmb W).injective)
    (origEdgeEmb (compassEmb W) (compassEmb W).injective) ''
      case3LiftedFamily Dc omega homega (case3SelectedMembers xc d.core.Z) hR.isDivision assignment
  let A := (P).toGMDigraph.toGraph.induce (Vs).toNatSet
  have hmem : A ∈ F :=
    case3OriginalSelectedMember_mem W.compassFinset Dc omega homega d.core.Z hR.isDivision i
  have hverts : V(A) = (Vs).toNatSet :=
    case3OriginalSelectedMember_vertexSet W.compassFinset Dc omega homega d.core.Z hR.isDivision i
  have hsubset : Vs ⊆ W.compassFinset := case3OriginalMember_image_subset _ _
  have hperim : Disjoint Vs W.perimeterFinset :=
    (case3PullbackBits_disjoint_image_iff (compassEmb W) (Ac).verts W.perimeterFinset).mp hint
  have hboundary : Bds.toNatSet = GM13.divBoundary (case3CompassSociety (G.deleteVertices X) W h2 he hW) A := by
    have hb := case3OriginalSelectedMember_boundary W.compassFinset Dc omega homega d.core.Z hR.isDivision i
    change GM13.divBoundary (case3CompassSociety (G.deleteVertices X) W h2 he hW) A =
      ((alg86Boundary xc Ac).image (W.compassFinset.orderEmbOfFin rfl)).toNatSet at hb
    have hk : alg86Boundary xc Ac = case3GroupBoundary xc d.core.Z i.1 :=
      case3CompactSelectedMember_boundary (G.deleteVertices X) W h2 he hW d hd i
    exact (congrArg (fun bd : Finset (Fin xc.n) =>
      (bd.image (W.compassFinset.orderEmbOfFin rfl)).toNatSet) hk).symm.trans hb.symm
  refine ⟨case3CompassSociety (G.deleteVertices X) W h2 he hW, F, A, Vs, Bds, P, W_A,
    case3CompassSociety_isWallSociety_delGraph W h2 he hW rfl,
    case3CompassDivision_lift (G.deleteVertices X) W h2 he hW _ hR assignment,
    ?_, hverts.symm, hsubset, havoid.mono_left hsubset, hperim, ?_, ?_, hboundary,
    case3PushMultigraph_le W.compassFinset Rc (G.deleteVertices X) (case3RoutedMember_le _ _ _ _),
    case3OriginalSelectedMember_edgeSet W.compassFinset Dc omega homega d.core.Z hR.isDivision i,
    hWA, ⟨hnext, hsub, rfl⟩, hV, hBd, hwall, henc⟩
  · refine ⟨hmem, ?_⟩
    rw [hverts, WallOfHeight.vertexSet_perimeter_toGMWall_eq]
    exact case3Disjoint_toNatSet Vs W.perimeterFinset hperim
  · exact Finset.image_subset_image (case3GroupBoundary_subset_member xc d.core.Z i)
  · calc
      _ ≤ (case3GroupBoundary xc d.core.Z i.1).card := Finset.card_image_le
      _ ≤ 3 := case3GroupBoundary_card_le_three xc d hd i.1

end

end GraphMinor.Compute
