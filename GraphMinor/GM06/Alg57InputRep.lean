module

public import GraphMinor.Compute.GM06SuccessorGraphRep
public import GraphMinor.Compute.GM06LinkageRowsEncoding
public import GraphMinor.GM06.Alg511CuffRotations
public import GraphMinor.Surface.PlaneOrientation
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section4

/-!
# The cuff-augmented input and returned paths of VI (5.7)

The input contains the ordinary graph, its rotations with both
auxiliary cuffs, the two cuff orders and the given linkage rows.
Original edges occupy the initial label block, followed by inner
gaps and then outer gaps. These are the same labels used by (5.11).
The geometric witnesses below interpret only these supplied fields.
There are no region rows and no feasibility or reduction witnesses.
The output is a bit and, on success, length-prefixed rows of ordinary
directed words encoding a linkage in the original graph.
-/

public section
namespace GraphMinor.Compute.GM06SuccessorGraphRep
open GraphMinor.Surface

/-- The initial ordinary edge table activates every supplied edge. -/
@[expose] def initialTagged {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep x G.toGraph) : List ((Fin x.vertexCount × Fin x.vertexCount) × ℕ) :=
  rep.pairs.map (fun p => (p, 1))

/-- The actual vertex point named by an input label. -/
@[expose] def vertexLabels {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep x G.toGraph) : Fin x.vertexCount ↪ ClosedCylinder :=
  ⟨fun j => (rep.vertex j).val, Subtype.val_injective.comp rep.vertex.injective⟩

/-- Initial active labels retain the input's original edge positions. -/
@[expose] def edgeLabels {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep x G.toGraph) : Fin rep.initialTagged.length → Set ClosedCylinder :=
  fun j => (rep.edge ⟨j.val, by simpa only [initialTagged, List.length_map] using j.isLt⟩).val

/-- The activated table has exactly the original link interpretation. -/
theorem initial_links {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep x G.toGraph) (j : Fin rep.initialTagged.length) :
    G.toGraph.IsLink (rep.edgeLabels j) (rep.vertexLabels rep.initialTagged[j].1.1)
      (rep.vertexLabels rep.initialTagged[j].1.2) := by
  have hj : j.val < rep.pairs.length := by simpa only [initialTagged, List.length_map] using j.isLt
  have hrow : rep.initialTagged[j] = (rep.pairs[j.val], 1) := by
    change (rep.pairs.map (fun p => (p, 1)))[j.val]'_ = _
    exact List.getElem_map (fun p => (p, 1))
  rw [hrow]
  exact rep.link ⟨j.val, hj⟩

end GraphMinor.Compute.GM06SuccessorGraphRep

namespace GraphMinor.GM06
open GraphMinor.Compute Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- A polar disc is positively oriented in the usual plane when
its boundary winds positively around its centre. The plane chart
also ensures that the disc misses the point at infinity. -/
@[expose] def GM06PositivePolar (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) : Prop :=
  ∃ Ψ : C(ClosedUnitDisc, EuclideanPlane),
    (∀ z, Φ z = (Ψ z : OnePoint EuclideanPlane)) ∧
      0 < wind (fun w => complexPlane.symm (Ψ (polarDiscPoint 1 w)))
        (complexPlane.symm (Ψ polarCentre))

/-- A supplied row is the actual counterclockwise order in the
plane, with the same labelled directed ends as the shared cuff
interpretation. The positivity condition fixes the orientation of
its chart rather than leaving independent reflections at vertices. -/
@[expose] def GM06SuccessorRotationRowRep
    {Γ : Drawing (OnePoint EuclideanPlane)} {m : ℕ}
    (edge : Fin m ≃ Γ.E) (γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane)
    (v : OnePoint EuclideanPlane) (xs : List ℕ) : Prop :=
  xs.Nodup ∧
  (∀ r, r ∈ xs ↔ ∃ a : halfEdges Γ γ v, halfEdgeLabel edge a = r) ∧
  (xs.length ≤ 1 ∨ ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (z : ℕ → Circle),
    IsPolar Γ v Φ ∧ GM06PositivePolar Φ ∧ Set.InjOn z {r | r ∈ xs} ∧
    xs.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)) ∧
    (∀ a : halfEdges Γ γ v, ∀ t : I, 0 < t →
      Φ (polarDiscPoint t (z (halfEdgeLabel edge a))) ∈ range (spoke γ a.1)) ∧
    ∀ (j : Fin m) (w : Circle),
      polarRimMap Φ w ∈ (edge j).val ↔ ∃ r ∈ xs,
        z r = w ∧ (r = 2 * j.val ∨ r = 2 * j.val + 1))

/-- Forgetting chart orientation gives the shared geometric cuff
row interpretation, so the existing calibrated scans still apply. -/
theorem GM06SuccessorRotationRowRep.to_cuffRotation
    {Γ : Drawing (OnePoint EuclideanPlane)} {m : ℕ}
    {edge : Fin m ≃ Γ.E} {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {v : OnePoint EuclideanPlane} {xs : List ℕ}
    (h : GM06SuccessorRotationRowRep edge γ v xs) : Alg511CuffRotationRowRep edge γ v xs := by
  refine ⟨h.1, h.2.1, ?_⟩
  rcases h.2.2 with hsmall | ⟨Φ, z, hp, _, hi, hs, hspoke, hlabel⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨Φ, z, hp, hi, hs, hspoke, hlabel⟩

/-- Interpretation of the supplied rotation rows with both cuffs.
The ordinary prefix and both cuff families have fixed original indices.
The cuff curves specify the direction of each of their two ends. -/
@[expose] def GM06SuccessorRotationRep (k : ℕ) (x : GM06SuccessorInput)
    {G : Drawing ClosedCylinder} (rep : GM06SuccessorGraphRep x G.toGraph) : Prop :=
  ∃ (F : Drawing ClosedCylinder)
    (edge : Fin (rep.pairs.length + (k + k)) ≃ (cylinderSphereDrawing F).E)
    (γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane),
    G.IsSubdrawing F ∧ F.U = G.U ∪ bd ClosedCylinder ∧ F.V = G.V ∧
    EdgePar (cylinderSphereDrawing F) γ ∧
    (∀ j : Fin rep.pairs.length,
      (edge (j.castAdd (k + k))).val = cylinderToSphere '' (rep.edge j).val) ∧
    (∀ i : Fin k,
      (edge ((i.castAdd k).natAdd rep.pairs.length)).val =
        cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) ∧
    (∀ i : Fin k,
      (edge ((i.natAdd k).natAdd rep.pairs.length)).val =
        cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1)) ∧
    (∀ j : Fin rep.pairs.length,
      γ (cylinderToSphere '' (rep.edge j).val) 0 =
        cylinderToSphere (rep.vertex rep.pairs[j.val].1).val ∧
      γ (cylinderToSphere '' (rep.edge j).val) 1 =
        cylinderToSphere (rep.vertex rep.pairs[j.val].2).val) ∧
    (∀ i : Fin k, ∀ t : I,
      γ (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) t =
        cylinderToSphere (initialCuffGapCurve k i t)) ∧
    (∀ i : Fin k, ∀ t : I,
      γ (cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1)) t =
        cylinderToSphere (alg511OuterCuffGapCurve k i t)) ∧
    x.rotations.length = x.vertexCount ∧
    ∀ v : Fin x.vertexCount,
      GM06SuccessorRotationRowRep edge γ (cylinderToSphere (rep.vertex v).val)
        (x.rotations.getD v.val [])

/-- The complete ordinary input relation for VI (5.7), page 133.
All fields interpret the supplied graph, cuffs, rotations or linkage. -/
structure GM06SuccessorInputRep {k : ℕ} (x : GM06SuccessorInput)
    (G : Drawing ClosedCylinder) (L : CylinderLinkage k G) where
  graph : GM06SuccessorGraphRep x G.toGraph
  source : Fin k → Fin x.vertexCount
  target : Fin k → Fin x.vertexCount
  inner : x.innerCuff = List.ofFn (fun i => (source i).val)
  outer : x.outerCuff = List.ofFn (fun i => (target i).val)
  source_point : ∀ i, (graph.vertex (source i)).val = cylinderM1Point k i
  target_point : ∀ i, (graph.vertex (target i)).val = cylinderM2Point k i
  linkage : GM06LinkageRowsEncoding L graph.initialTagged graph.vertexLabels graph.edgeLabels x.linkage
  rotations : GM06SuccessorRotationRep k x graph

/-- The output bit and path-array format for VI (5.7). On success,
the array is the length-prefixed list of ordinary directed path rows.
The paths use the input graph's original edge and endpoint labels. -/
@[expose] def GM06SuccessorOutputRep {k : ℕ} {x : GM06SuccessorInput}
    {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    (rep : GM06SuccessorInputRep x G L) (θ : ℝ) (bit : ℕ) (words : List ℕ) : Prop :=
  (bit = 0 ∧ ¬ IsThetaFeasible k G (θ + 1 / (k : ℝ))) ∨
    (bit = 1 ∧ ∃ (M : CylinderLinkage k G) (rows : List (List ℕ)),
      words = gm06EncodeRows rows ∧ M.HasTheta (θ + 1 / (k : ℝ)) ∧
      GM06LinkageRowsEncoding M rep.graph.initialTagged rep.graph.vertexLabels rep.graph.edgeLabels rows)

namespace GM06SuccessorInputRep

/-- Both fixed cuff orders have one word per linkage path. -/
theorem cuff_lengths {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06SuccessorInputRep x G L) :
    x.innerCuff.length = k ∧ x.outerCuff.length = k := by
  rw [rep.inner, rep.outer]
  exact ⟨List.length_ofFn, List.length_ofFn⟩

/-- A row word is an outer-cuff label exactly when its actual point
is on the outer cuff. This is the condition used by the existing
Reduction 3 eligibility scan. -/
theorem outer_mem_iff {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06SuccessorInputRep x G L)
    (hG : IsCylinderSection5Drawing k G) (a : Fin x.vertexCount) :
    a.val ∈ x.outerCuff ↔ rep.graph.vertexLabels a ∈ cylinderCuff2 := by
  rw [rep.outer, List.mem_ofFn]
  constructor
  · rintro ⟨i, hi⟩
    have he : rep.target i = a := Fin.ext hi
    rw [← he]
    change (rep.graph.vertex (rep.target i)).val ∈ cylinderCuff2
    rw [rep.target_point]
    exact cylinderM2Point_mem_cylinderCuff2 k i
  · intro ha
    have habd : (rep.graph.vertex a).val ∈ bd ClosedCylinder := by
      rw [bd_closedCylinder]; exact Or.inr ha
    have haM : (rep.graph.vertex a).val ∈ cylinderM1 k ∪ cylinderM2 k :=
      hG.2.2 ▸ ⟨(rep.graph.vertex a).property, habd⟩
    rcases haM with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact False.elim (disjoint_cylinderCuffs.ne_of_mem (cylinderM1Point_mem_cylinderCuff1 k i) ha hi)
    · have heq : rep.target i = a := rep.graph.vertexLabels.injective ((rep.target_point i).trans hi)
      exact ⟨i, congrArg Fin.val heq⟩

/-- Every actual signed end of an augmented edge is present in its
vertex row, with the original consecutive endpoint label. -/
theorem marker_mem {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {m : ℕ}
    {edge : Fin m ≃ Γ.E} {γ : Set S → I → S} {v : S} {row : List ℕ}
    (hrow : Alg511CuffRotationRowRep edge γ v row) (j : Fin m) (b : Bool)
    (hend : γ (edge j).val (endOf b) = v) : 2 * j.val + b.toNat ∈ row := by
  let a : halfEdges Γ γ v := ⟨((edge j).val, b), (edge j).property, hend⟩
  apply (hrow.2.1 _).mpr
  refine ⟨a, ?_⟩
  have heq : (⟨a.1.1, a.2.1⟩ : Γ.E) = edge j := Subtype.ext rfl
  simp only [halfEdgeLabel, heq, Equiv.symm_apply_apply, a]

/-- The two directions of every outer cuff gap occur at its two
ends, with indices m+k+i and distinct even and odd dart labels.
For k=1 both ends occur in the same row and remain distinct words. -/
theorem outer_markers {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06SuccessorInputRep x G L)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    2 * (rep.graph.pairs.length + (k + i.val)) ∈ x.rotations.getD (rep.target i).val [] ∧
    2 * (rep.graph.pairs.length + (k + i.val)) + 1 ∈
      x.rotations.getD (rep.target (finSuccCycle i)).val [] := by
  obtain ⟨F, edge, γ, _, _, _, _, _, _, hedgeO, _, _, hγO, _, hrot⟩ := rep.rotations
  let j : Fin (rep.graph.pairs.length + (k + k)) := (i.natAdd k).natAdd rep.graph.pairs.length
  have hends := alg511_outer_gap_ends hG i
  constructor
  · apply marker_mem (hrot (rep.target i)).to_cuffRotation j false
    change γ (edge j).val 0 = _
    rw [hedgeO i, hγO, hends.1, rep.target_point]
  · apply marker_mem (hrot (rep.target (finSuccCycle i))).to_cuffRotation j true
    change γ (edge j).val 1 = _
    rw [hedgeO i, hγO, hends.2, rep.target_point]

end GM06SuccessorInputRep
end GraphMinor.GM06
