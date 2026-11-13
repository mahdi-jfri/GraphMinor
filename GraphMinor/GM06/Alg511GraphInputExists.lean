module

public import GraphMinor.Compute.GM06Alg511Flow
public import GraphMinor.Compute.GM06SuccessorGraphRep
public import GraphMinor.GM06.Defs
import Mathlib.Tactic

/-!
# Coverage of the graph and cuff fields of VI (5.11)

Every Section 5 drawing has finite vertex and edge labels. List both
ends of each edge, retaining loops and parallel edges. Enumerate each
cuff by its prescribed Section 5 points. The resulting lists have
exactly the cuff membership needed by the initial flow search.

This file covers the graph and cuff fields only. Rotations and region
boundary walks still need their separate geometric interpretation.
The choices below are witnesses in an existence theorem, not an
executable encoder or fields selected by the decision program.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface Set

/-- Every Section 5 cylinder drawing admits the finite graph and cuff
part of an input, with the requested integer target pair unchanged. -/
theorem alg511_exists_graph_cuff_input (k : ℕ) (G : Drawing ClosedCylinder)
    (hG : IsCylinderSection5Drawing k G) (numerator denominator : ℤ) :
    ∃ (x : GM06Alg511Input) (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph),
      x.pathCount = k ∧ x.numerator = numerator ∧ x.denominator = denominator ∧
      (∀ a : Fin x.vertexCount,
        a.val ∈ x.innerCuff ↔ (rep.vertex a).val ∈ cylinderM1 k) ∧
      (∀ b : Fin x.vertexCount,
        b.val ∈ x.outerCuff ↔ (rep.vertex b).val ∈ cylinderM2 k) ∧
      ∃ source : Fin k → Fin x.vertexCount,
        (∀ i, (rep.vertex (source i)).val = cylinderM1Point k i) ∧
        (∀ a ∈ x.flowInput.A, ∃ i, source i = a) ∧
        x.innerCuff = List.ofFn (fun i => (source i).val) ∧
        ∃ target : Fin k → Fin x.vertexCount,
          (∀ i, (rep.vertex (target i)).val = cylinderM2Point k i) ∧
          x.outerCuff = List.ofFn (fun i => (target i).val) := by
  classical
  let : Fintype G.V := G.finite_V.fintype
  let : Fintype G.E := G.finite_edges.fintype
  let n := Fintype.card G.V
  let m := Fintype.card G.E
  let vertex : Fin n ≃ G.V := (Fintype.equivFin G.V).symm
  let edge₀ : Fin m ≃ G.E := (Fintype.equivFin G.E).symm
  have hend : ∀ i : Fin m, ∃ a b : Fin n,
      G.toGraph.IsLink (edge₀ i).val (vertex a).val (vertex b).val := by
    intro i
    obtain ⟨u, v, huv⟩ := G.toGraph.exists_isLink_of_mem_edgeSet (edge₀ i).property
    obtain ⟨a, ha⟩ := vertex.surjective ⟨u, huv.left_mem⟩
    obtain ⟨b, hb⟩ := vertex.surjective ⟨v, huv.right_mem⟩
    refine ⟨a, b, ?_⟩
    rw [congrArg Subtype.val ha, congrArg Subtype.val hb]
    exact huv
  choose a b hab using hend
  let pairs := List.ofFn (fun i : Fin m => (a i, b i))
  have hlen : pairs.length = m := List.length_ofFn
  let edge : Fin pairs.length ≃ G.E := (finCongr hlen).trans edge₀
  have hlink : ∀ i : Fin pairs.length,
      G.toGraph.IsLink (edge i).val (vertex pairs[i.val].1).val (vertex pairs[i.val].2).val := by
    intro i
    change G.toGraph.IsLink (edge i).val (vertex (pairs.get i).1).val (vertex (pairs.get i).2).val
    have hi : Fin.cast hlen i = finCongr hlen i := Fin.ext (finCongr_apply_coe hlen i).symm
    simpa only [edge, Equiv.trans_apply, pairs, List.get_ofFn, hi] using hab (finCongr hlen i)
  have hM1 : ∀ i : Fin k, cylinderM1Point k i ∈ G.V := by
    intro i
    have h : cylinderM1Point k i ∈ G.V ∩ bd ClosedCylinder := by
      rw [hG.2.2]
      exact Or.inl ⟨i, rfl⟩
    exact h.1
  have hM2 : ∀ i : Fin k, cylinderM2Point k i ∈ G.V := by
    intro i
    have h : cylinderM2Point k i ∈ G.V ∩ bd ClosedCylinder := by
      rw [hG.2.2]
      exact Or.inr ⟨i, rfl⟩
    exact h.1
  let source : Fin k → Fin n := fun i => vertex.symm ⟨cylinderM1Point k i, hM1 i⟩
  let target : Fin k → Fin n := fun i => vertex.symm ⟨cylinderM2Point k i, hM2 i⟩
  have hsource : ∀ i, (vertex (source i)).val = cylinderM1Point k i := by
    intro i
    exact congrArg Subtype.val (vertex.apply_symm_apply _)
  have htarget : ∀ i, (vertex (target i)).val = cylinderM2Point k i := by
    intro i
    exact congrArg Subtype.val (vertex.apply_symm_apply _)
  let x : GM06Alg511Input := {
    vertexCount := n
    endpoints := gm06EndpointWords (pairs.map fun p => (p.1.val, p.2.val))
    rotations := []
    regionBoundaries := []
    innerCuff := List.ofFn (fun i => (source i).val)
    outerCuff := List.ofFn (fun i => (target i).val)
    pathCount := k
    numerator := numerator
    denominator := denominator }
  let rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph := {
    vertex := vertex
    pairs := pairs
    endpoints := rfl
    edge := edge
    link := hlink }
  have hinj : Function.Injective (fun j => (vertex j).val) :=
    Subtype.val_injective.comp vertex.injective
  have hinner : ∀ c : Fin n, c.val ∈ x.innerCuff ↔ (vertex c).val ∈ cylinderM1 k := by
    intro c
    change c.val ∈ List.ofFn (fun i => (source i).val) ↔ _
    rw [List.mem_ofFn]
    constructor
    · rintro ⟨i, hi⟩
      have hc : source i = c := Fin.ext hi
      exact ⟨i, (hsource i).symm.trans (congrArg (fun j => (vertex j).val) hc)⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, congrArg Fin.val (hinj ((hsource i).trans hi))⟩
  have houter : ∀ c : Fin n, c.val ∈ x.outerCuff ↔ (vertex c).val ∈ cylinderM2 k := by
    intro c
    change c.val ∈ List.ofFn (fun i => (target i).val) ↔ _
    rw [List.mem_ofFn]
    constructor
    · rintro ⟨i, hi⟩
      have hc : target i = c := Fin.ext hi
      exact ⟨i, (htarget i).symm.trans (congrArg (fun j => (vertex j).val) hc)⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, congrArg Fin.val (hinj ((htarget i).trans hi))⟩
  refine ⟨x, rep, rfl, rfl, rfl, hinner, houter, source, hsource, ?_, rfl, target, htarget, rfl⟩
  intro c hc
  have hc' : c.val ∈ x.innerCuff := (Finset.mem_filter.mp hc).2
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hc'
  exact ⟨i, Fin.ext hi⟩

end GraphMinor.GM06
