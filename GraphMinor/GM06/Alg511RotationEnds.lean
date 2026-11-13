module

public import GraphMinor.GM06.Alg511EdgeParam
public import GraphMinor.GM06.Section5HalfEdgeLabels
import GraphMinor.Compute.GM06Alg511DartKeys
import Mathlib.Tactic

/-!
# Exact endpoint incidence of the geometric rotation labels

The finite rotation input for VI (5.11), page 134, uses the same
directed endpoint positions as (5.7). Once the parametrizations agree
with the supplied endpoint order, a half-edge label belongs at a
vertex exactly when that endpoint-array position stores the vertex.
The statement counts the two ends of a loop separately.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute Set GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- A geometric directed end reads its vertex at exactly its supplied
endpoint-array label. -/
theorem alg511_halfEdgeLabel_endpoint
    {S : Type u} [TopologicalSpace S] (x : GM06SuccessorInput)
    {G : Drawing S} (rep : GM06SuccessorGraphRep x G.toGraph)
    {γ : Set S → I → S}
    (hends : ∀ i : Fin rep.pairs.length,
      γ (rep.edge i).val 0 = (rep.vertex rep.pairs[i.val].1).val ∧
      γ (rep.edge i).val 1 = (rep.vertex rep.pairs[i.val].2).val)
    (v : Fin x.vertexCount) (a : halfEdges G γ (rep.vertex v).val) :
    x.endpoints.getD (halfEdgeLabel rep.edge a) 0 = v.val := by
  let i := rep.edge.symm ⟨a.1.1, a.2.1⟩
  have hei : (rep.edge i).val = a.1.1 :=
    congrArg Subtype.val (rep.edge.apply_symm_apply ⟨a.1.1, a.2.1⟩)
  have hp : γ (rep.edge i).val (endOf a.1.2) = (rep.vertex v).val := by
    rw [hei]
    exact a.2.2
  have hlabel : halfEdgeLabel rep.edge a = 2 * i.val + a.1.2.toNat := rfl
  obtain ⟨h₀, h₁⟩ := gm06Alg511EndpointWords_getD
    (rep.pairs.map fun p => (p.1.val, p.2.val)) i.val (by simpa only [List.length_map] using i.isLt)
  simp only [List.getElem_map] at h₀ h₁
  rw [hlabel, rep.endpoints]
  cases hb : a.1.2 with
  | false =>
    simp only [Bool.toNat_false, Nat.add_zero]
    rw [h₀]
    have hv : rep.pairs[i.val].1 = v := rep.vertex.injective
      (Subtype.ext ((hends i).1.symm.trans (by simpa [hb, endOf] using hp)))
    exact congrArg Fin.val hv
  | true =>
    simp only [Bool.toNat_true]
    rw [h₁]
    have hv : rep.pairs[i.val].2 = v := rep.vertex.injective
      (Subtype.ext ((hends i).2.symm.trans (by simpa [hb, endOf] using hp)))
    exact congrArg Fin.val hv

/-- Every valid endpoint position at a vertex is the label of an
actual directed end there, including either end of a loop. -/
theorem alg511_exists_halfEdgeLabel_of_endpoint
    {S : Type u} [TopologicalSpace S] (x : GM06SuccessorInput)
    {G : Drawing S} (rep : GM06SuccessorGraphRep x G.toGraph)
    {γ : Set S → I → S}
    (hends : ∀ i : Fin rep.pairs.length,
      γ (rep.edge i).val 0 = (rep.vertex rep.pairs[i.val].1).val ∧
      γ (rep.edge i).val 1 = (rep.vertex rep.pairs[i.val].2).val)
    (v : Fin x.vertexCount) (d : ℕ) (hd : d < 2 * rep.pairs.length)
    (hv : x.endpoints.getD d 0 = v.val) :
    ∃ a : halfEdges G γ (rep.vertex v).val, halfEdgeLabel rep.edge a = d := by
  let i : Fin rep.pairs.length := ⟨d / 2, by omega⟩
  obtain ⟨h₀, h₁⟩ := gm06Alg511EndpointWords_getD
    (rep.pairs.map fun p => (p.1.val, p.2.val)) i.val (by simpa only [List.length_map] using i.isLt)
  simp only [List.getElem_map] at h₀ h₁
  rw [rep.endpoints] at hv
  rcases Nat.mod_two_eq_zero_or_one d with heven | hodd
  · have hd' : d = 2 * i.val := by dsimp only [i]; omega
    have hvertex : rep.pairs[i.val].1 = v := Fin.ext (by rw [hd', h₀] at hv; exact hv)
    let a : halfEdges G γ (rep.vertex v).val := ⟨((rep.edge i).val, false),
      (rep.edge i).property, by simpa only [endOf, Bool.false_eq_true, ite_false, hvertex]
        using (hends i).1⟩
    refine ⟨a, ?_⟩
    change 2 * (rep.edge.symm (rep.edge i)).val + false.toNat = d
    rw [rep.edge.symm_apply_apply]
    simpa only [Bool.toNat_false, Nat.add_zero] using hd'.symm
  · have hd' : d = 2 * i.val + 1 := by dsimp only [i]; omega
    have hvertex : rep.pairs[i.val].2 = v := Fin.ext (by rw [hd', h₁] at hv; exact hv)
    let a : halfEdges G γ (rep.vertex v).val := ⟨((rep.edge i).val, true),
      (rep.edge i).property, by simpa only [endOf, ite_true, hvertex] using (hends i).2⟩
    refine ⟨a, ?_⟩
    change 2 * (rep.edge.symm (rep.edge i)).val + true.toNat = d
    rw [rep.edge.symm_apply_apply]
    simpa only [Bool.toNat_true] using hd'.symm

/-- The geometric half-edge labels at a vertex are precisely the
positions in its supplied endpoint array that name that vertex. -/
theorem alg511_halfEdgeLabel_exists_iff
    {S : Type u} [TopologicalSpace S] (x : GM06SuccessorInput)
    {G : Drawing S} (rep : GM06SuccessorGraphRep x G.toGraph)
    {γ : Set S → I → S}
    (hends : ∀ i : Fin rep.pairs.length,
      γ (rep.edge i).val 0 = (rep.vertex rep.pairs[i.val].1).val ∧
      γ (rep.edge i).val 1 = (rep.vertex rep.pairs[i.val].2).val)
    (v : Fin x.vertexCount) (d : ℕ) :
    (∃ a : halfEdges G γ (rep.vertex v).val, halfEdgeLabel rep.edge a = d) ↔
      d < x.endpoints.length ∧ x.endpoints.getD d 0 = v.val := by
  have hlen : x.endpoints.length = 2 * rep.pairs.length := by
    rw [rep.endpoints, gm06EndpointWords_length, List.length_map]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨by rw [hlen]; exact halfEdgeLabel_lt rep.edge a,
      alg511_halfEdgeLabel_endpoint x rep hends v a⟩
  · rintro ⟨hd, hv⟩
    rw [hlen] at hd
    exact alg511_exists_halfEdgeLabel_of_endpoint x rep hends v d hd hv

end GraphMinor.GM06
