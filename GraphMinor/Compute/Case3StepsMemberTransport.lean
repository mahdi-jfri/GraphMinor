module

public import GraphMinor.Compute.Case3StepsInduceTransport
public import GraphMinor.Compute.Case3StepsMemberCompact
public import GraphMinor.Compute.Algorithm99TransportMove

/-!
# Returning a compact member to its division labels

The increasing vertex map identifies the graph passed to (7.2) with the
lifted member, with exactly the same directed copies. A wall returned by
(7.2) therefore moves through this map to a valid wall in the full routed
multigraph and lies inside the division member.
-/

public section

namespace GraphMinor.Compute

open Graph GraphMinor.Transport

/-- The consecutively numbered member renames to its lifted division graph. -/
theorem case3CompactMember_relabel {n : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup) (Z : Finset (Fin n))
    (hdiv : GM13.IsSocietyDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers (case3SimpleSocietyInput D omega homega) Z))
    (i : Case3SelectedGroup (case3SimpleSocietyInput D omega homega) Z) :
    let x := case3SimpleSocietyInput D omega homega
    let A := case3SelectedMember x Z i
    relabelGraph (origVertexEmb (A.verts.orderEmbOfFin rfl) (A.verts.orderEmbOfFin rfl).injective)
      (origEdgeEmb (A.verts.orderEmbOfFin rfl) (A.verts.orderEmbOfFin rfl).injective)
      (case3CompactMember x D Z i).toGMDigraph.toGraph =
        case3LiftMember D A
          (case3AssignedLoops (case3OrderedLoopAssignment x Z hdiv) A) := by
  dsimp only
  unfold case3CompactMember
  rw [case3Induce_relabel_eq, case3RoutedMember_eq_lift D omega homega Z hdiv i]
  rfl

/-- The ordered member inclusion preserves adjacency into the routed graph. -/
theorem case3CompactMember_adj (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (i : Case3SelectedGroup x Z)
    (u v : Fin (case3SelectedMember x Z i).verts.card)
    (hadj : (case3CompactMember x D Z i).toSimpleGraph.Adj u v) :
    (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).toSimpleGraph.Adj
      ((case3SelectedMember x Z i).verts.orderEmbOfFin rfl u)
      ((case3SelectedMember x Z i).verts.orderEmbOfFin rfl v) := by
  rw [MultiDigraph.toSimpleGraph_adj] at hadj ⊢
  exact ⟨fun he => hadj.1 (((case3SelectedMember x Z i).verts.orderEmbOfFin rfl).injective he), hadj.2⟩

/-- A wall on compact member labels moves to a valid wall of the routed
multigraph using the increasing member vertex list. -/
theorem case3CompactMember_wall_move {h : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (i : Case3SelectedGroup x Z)
    (W : WallOfHeight h (case3CompactMember x D Z i)) (hW : W.IsValid) :
    (W.moveOrig (case3RoutedMember x D Z (case3RawIndexLabel x i.1))
      ((case3SelectedMember x Z i).verts.orderEmbOfFin rfl)).IsValid := by
  exact hW.moveOrig _ ((case3SelectedMember x Z i).verts.orderEmbOfFin rfl).injective
    (case3CompactMember_adj x D Z i)

/-- All vertices of a moved compact wall belong to the selected member. -/
theorem case3CompactMember_wall_vertices {h : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (i : Case3SelectedGroup x Z)
    (W : WallOfHeight h (case3CompactMember x D Z i)) :
    (W.moveOrig (case3RoutedMember x D Z (case3RawIndexLabel x i.1))
      ((case3SelectedMember x Z i).verts.orderEmbOfFin rfl)).vertexFinset ⊆
        (case3SelectedMember x Z i).verts := by
  rw [WallOfHeight.vertexFinset_moveOrig]
  intro u hu
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
  exact (case3SelectedMember x Z i).verts.orderEmbOfFin_mem rfl v

/-- The moved wall lies in the routed graph restricted to the member's
vertices, rather than merely in its ambient multigraph. -/
theorem case3CompactMember_wall_le_induce {h : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (i : Case3SelectedGroup x Z)
    (W : WallOfHeight h (case3CompactMember x D Z i)) (h2 : 2 ≤ h) (he : Even h)
    (hW : W.IsValid) :
    let R := case3RoutedMember x D Z (case3RawIndexLabel x i.1)
    let S := (case3SelectedMember x Z i).verts
    let W' := W.moveOrig R (S.orderEmbOfFin rfl)
    (W'.toGMWall h2 he (case3CompactMember_wall_move x D Z i W hW)).graph ≤
      R.toGMDigraph.toGraph.induce S.toNatSet := by
  dsimp only
  have hw' := case3CompactMember_wall_move x D Z i W hW
  have hle := WallOfHeight.isWallIn_toGMWall _ h2 he hw'
  have hverts :
      V(((W.moveOrig (case3RoutedMember x D Z (case3RawIndexLabel x i.1))
        ((case3SelectedMember x Z i).verts.orderEmbOfFin rfl)).toGMWall h2 he hw').graph) ⊆
        (case3SelectedMember x Z i).verts.toNatSet := by
    rw [WallOfHeight.vertexSet_toGMWall_eq]
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, case3CompactMember_wall_vertices x D Z i W hu, rfl⟩
  exact ⟨hverts, fun e u v hlink => ⟨hle.isLink_mono hlink,
    hverts hlink.left_mem, hverts hlink.right_mem⟩⟩

end GraphMinor.Compute
