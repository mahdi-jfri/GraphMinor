module

public import GraphMinor.GM06.Alg511CuffParam
public import GraphMinor.GM06.Alg511RotationRows
import GraphMinor.GM11.PerimeterPull
import GraphMinor.GM06.Alg511AdjoinCuffs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Complete rotations with the successor procedure's cuff labels

The input of VI (5.11), page 134, must use the same directed cuff
markers as (5.7). Number original edges first, then inner gaps, then
outer gaps. Retain the original edge curves, prescribe the angular
curves on the new edges, and carry them to the sphere. A small polar
chart at each vertex gives a rotation of all its directed ends.
Only the finite rotation rows are supplied as input. The drawings,
parametrizations and charts below witness their interpretation.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute Set Topology Real GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- Consecutive edge indices for the original graph and the two
indexed cuff-gap families. -/
@[expose] def alg511CuffIndexEquiv (m k : ℕ) :
    Fin m ⊕ (Fin k ⊕ Fin k) ≃ Fin (m + (k + k)) :=
  (Equiv.sumCongr (Equiv.refl (Fin m)) finSumFinEquiv).trans finSumFinEquiv

/-- The augmented graph admits consecutive labels with the exact
original prefix and fixed inner and outer cuff indices. -/
theorem alg511_exists_indexed_cuff_edges {k : ℕ} {G F : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (hGF : G.IsSubdrawing F)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V)
    {m : ℕ} (old : Fin m ≃ G.E) :
    ∃ edge : Fin (m + (k + k)) ≃ F.E,
      (∀ j : Fin m, (edge (j.castAdd (k + k))).val = (old j).val) ∧
      (∀ i : Fin k, (edge ((i.castAdd k).natAdd m)).val = initialCuffGapCurve k i '' Ioo 0 1) ∧
      (∀ i : Fin k, (edge ((i.natAdd k).natAdd m)).val = alg511OuterCuffGapCurve k i '' Ioo 0 1) := by
  obtain ⟨e, heG, heI, heO⟩ := alg511_exists_cuff_edge_equiv hG hGF hFU hFV
  let edge := (alg511CuffIndexEquiv m k).symm.trans
    ((Equiv.sumCongr old (Equiv.refl _)).trans e)
  have hG' (j : Fin m) : edge (j.castAdd (k + k)) = e (.inl (old j)) := by
    simp [edge, alg511CuffIndexEquiv]
  have hI' (i : Fin k) : edge ((i.castAdd k).natAdd m) = e (.inr (.inl i)) := by
    simp [edge, alg511CuffIndexEquiv]
  have hO' (i : Fin k) : edge ((i.natAdd k).natAdd m) = e (.inr (.inr i)) := by
    change edge (alg511CuffIndexEquiv m k (.inr (.inr i))) = _
    dsimp only [edge, Equiv.trans_apply]
    rw [Equiv.symm_apply_apply]
    rfl
  refine ⟨edge, ?_, ?_, ?_⟩
  · intro j
    rw [hG']
    exact heG _
  · intro i
    rw [hI']
    exact heI i
  · intro i
    rw [hO']
    exact heO i

/-- A rotation row for an augmented drawing lists exactly the
actual directed ends at its vertex, in polar angular order. Both
ends of a loop have separate labels. -/
@[expose] def Alg511CuffRotationRowRep
    {S : Type u} [TopologicalSpace S] {Γ : Drawing S} {m : ℕ}
    (edge : Fin m ≃ Γ.E) (γ : Set S → I → S) (v : S) (xs : List ℕ) : Prop :=
  xs.Nodup ∧
  (∀ r, r ∈ xs ↔ ∃ a : halfEdges Γ γ v, halfEdgeLabel edge a = r) ∧
  (xs.length ≤ 1 ∨ ∃ (Φ : C(ClosedUnitDisc, S)) (z : ℕ → Circle),
    IsPolar Γ v Φ ∧ Set.InjOn z {r | r ∈ xs} ∧
    xs.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)) ∧
    (∀ a : halfEdges Γ γ v, ∀ t : I, 0 < t →
      Φ (polarDiscPoint t (z (halfEdgeLabel edge a))) ∈ range (spoke γ a.1)) ∧
    ∀ (j : Fin m) (w : Circle),
      polarRimMap Φ w ∈ (edge j).val ↔ ∃ r ∈ xs,
        z r = w ∧ (r = 2 * j.val ∨ r = 2 * j.val + 1))

private theorem exists_cuff_rotation_row
    {S : Type u} [TopologicalSpace S] (hS : IsClosedSurface S)
    {Γ : Drawing S} {m : ℕ} (edge : Fin m ≃ Γ.E)
    {γ : Set S → I → S} (hγ : EdgePar Γ γ) {v : S} (hv : v ∈ Γ.V) :
    ∃ xs : List ℕ, Alg511CuffRotationRowRep edge γ v xs := by
  classical
  let : T2Space S := hS.2.1
  by_cases htwo : 2 ≤ Nat.card (halfEdges Γ γ v)
  · obtain ⟨Φ, hp⟩ := exists_isPolar_of_sectors hS hγ hv htwo
    obtain ⟨Ψ, hΨ, _, d, hd⟩ := exists_polar_chart_with_halfedge_equiv hS hγ
      hv hp isOpen_univ (mem_univ _)
    obtain ⟨xs, z, hnd, hmem, hz, hzi, hs, _⟩ :=
      exists_polar_rotation_row d (halfEdgeLabel edge) (halfEdgeLabel_injective edge)
    refine ⟨xs, hnd, hmem, Or.inr ⟨Ψ, z, hΨ, hzi, hs, ?_, ?_⟩⟩
    · intro a t ht
      rw [hz a]
      exact hd a t ht
    · exact polar_rotation_row_edge_labels hγ hΨ d hd edge xs z hmem hz
  · let H := halfEdges Γ γ v
    let : Fintype H := (finite_halfEdges Γ γ v).fintype
    let e : Fin (Fintype.card H) ≃ H := (Fintype.equivFin H).symm
    let xs := List.ofFn (fun i => halfEdgeLabel edge (e i))
    have hnd : xs.Nodup := List.nodup_ofFn_ofInjective
      ((halfEdgeLabel_injective edge).comp e.injective)
    have hmem (r : ℕ) : r ∈ xs ↔ ∃ a : H, halfEdgeLabel edge a = r := by
      rw [List.mem_ofFn]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨e i, hi⟩
      · rintro ⟨a, ha⟩
        obtain ⟨i, rfl⟩ := e.surjective a
        exact ⟨i, ha⟩
    refine ⟨xs, hnd, hmem, Or.inl ?_⟩
    have hcard : Nat.card H = Fintype.card H := Nat.card_eq_fintype_card
    change xs.length ≤ 1
    rw [show xs.length = Fintype.card H from List.length_ofFn]
    change ¬ 2 ≤ Nat.card H at htwo
    omega

/-- If an endpoint array also describes this augmented graph, the
geometric rotation interpretation agrees with its exact endpoint
incidence interpretation. -/
theorem Alg511CuffRotationRowRep.to_rotationRowRep
    {S : Type u} [TopologicalSpace S] (x : GM06SuccessorInput)
    {G : Drawing S} (rep : GM06SuccessorGraphRep x G.toGraph)
    {γ : Set S → I → S}
    (hends : ∀ i : Fin rep.pairs.length,
      γ (rep.edge i).val 0 = (rep.vertex rep.pairs[i.val].1).val ∧
      γ (rep.edge i).val 1 = (rep.vertex rep.pairs[i.val].2).val)
    {v : Fin x.vertexCount} {xs : List ℕ}
    (h : Alg511CuffRotationRowRep rep.edge γ (rep.vertex v).val xs) :
    Alg511RotationRowRep x rep γ v xs :=
  ⟨h.1, fun r => (h.2.1 r).trans (alg511_halfEdgeLabel_exists_iff x rep hends v r), h.2.2⟩

/-- Every Section 5 input has complete geometric rotation rows
using exactly the successor program's original and cuff edge labels.
This construction uses no linkage and no feasibility assumption. -/
theorem alg511_exists_augmented_rotation_rows
    {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G)
    (x : GM06SuccessorInput) (rep : GM06SuccessorGraphRep x G.toGraph) :
    ∃ (F : Drawing ClosedCylinder)
      (edge : Fin (rep.pairs.length + (k + k)) ≃ (cylinderSphereDrawing F).E)
      (γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane)
      (rows : List (List ℕ)),
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
      rows.length = x.vertexCount ∧
      ∀ v : Fin x.vertexCount,
        Alg511CuffRotationRowRep edge γ (cylinderToSphere (rep.vertex v).val)
          (rows.getD v.val []) := by
  classical
  let : Nonempty ClosedCylinder := ⟨cylinderPoint 1 (by simp) 0⟩
  obtain ⟨F, _, _, hGF, hFU, hFV, _⟩ := alg511_exists_drawing_with_cuffs hG
  obtain ⟨γ₀, hγ₀, hends₀⟩ := alg511_exists_edgePar_with_prescribed_ends x rep
  obtain ⟨δ, hδ, hδG, hδI, hδO⟩ := alg511_exists_cuff_edgePar hG hGF hFU hFV hγ₀
  obtain ⟨γ, hγ, hγδ⟩ := alg511_exists_sphere_edgePar hδ
  obtain ⟨rawEdge, hrawG, hrawI, hrawO⟩ :=
    alg511_exists_indexed_cuff_edges hG hGF hFU hFV rep.edge
  let imageEdge : F.E ≃ (cylinderSphereDrawing F).E :=
    (Equiv.Set.image (fun a : Set ClosedCylinder => cylinderToSphere '' a) F.E
      (Set.image_injective.mpr injective_cylinderToSphere)).trans
        (Set.equivOfEq (cylinderSphereDrawing_E F).symm)
  let edge := rawEdge.trans imageEdge
  have hedge (j : Fin (rep.pairs.length + (k + k))) :
      (edge j).val = cylinderToSphere '' (rawEdge j).val := rfl
  have hI (i : Fin k) : initialCuffGapCurve k i '' Ioo 0 1 ∈ F.E := by
    obtain ⟨a, ha, heq⟩ := alg511_exists_exact_initial_gap_edge hG hGF hFU hFV i
    exact heq ▸ ha
  have hO (i : Fin k) : alg511OuterCuffGapCurve k i '' Ioo 0 1 ∈ F.E := by
    obtain ⟨a, ha, heq⟩ := alg511_exists_exact_outer_gap_edge hG hGF hFU hFV i
    exact heq ▸ ha
  have hvertex (v : Fin x.vertexCount) : cylinderToSphere (rep.vertex v).val ∈
      (cylinderSphereDrawing F).V := by
    rw [cylinderSphereDrawing_V, hFV]
    exact mem_image_of_mem _ (rep.vertex v).property
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  choose row hrow using fun v => exists_cuff_rotation_row hS edge hγ (hvertex v)
  refine ⟨F, edge, γ, List.ofFn row, hGF, hFU, hFV, hγ, ?_, ?_, ?_, ?_, ?_, ?_,
    List.length_ofFn, ?_⟩
  · intro j
    rw [hedge, hrawG]
    rfl
  · intro i
    rw [hedge, hrawI]
  · intro i
    rw [hedge, hrawO]
  · intro j
    constructor
    · rw [hγδ _ (hGF.2 (rep.edge j).property), hδG _ (rep.edge j).property, (hends₀ j).1]
    · rw [hγδ _ (hGF.2 (rep.edge j).property), hδG _ (rep.edge j).property, (hends₀ j).2]
  · intro i t
    rw [hγδ _ (hI i), hδI]
  · intro i t
    rw [hγδ _ (hO i), hδO]
  · intro v
    simpa [List.getD_eq_getElem?_getD, v.isLt] using hrow v

end GraphMinor.GM06
