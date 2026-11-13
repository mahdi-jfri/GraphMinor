module

public import GraphMinor.Compute.GM06DartMate
public import GraphMinor.Compute.GM06EndpointValency
public import Mathlib.Combinatorics.Graph.Basic
import GraphMinor.Compute.GM06EndpointLookup

/-!
# Interpreting an active directed edge and its opposite end

The neighbour query in VI (5.7), page 133, reads two endpoint
positions of one active original edge. Even positions have the
supplied link orientation and odd positions its reverse. Swapping
the directed-end label therefore gives the actual opposite vertex,
including when the two vertex values happen to coincide.
-/

public section
namespace GraphMinor.Compute
universe u v

/-- The two positions selected by a directed label and its mate
are exactly the endpoints of its active edge in the current graph. -/
theorem gm06ActiveDart_isLink {n : ℕ} {α : Type u} {β : Type v}
    (G : Graph α β) (vertex : Fin n → α)
    (tagged : List ((Fin n × Fin n) × ℕ)) (edge : Fin tagged.length → β)
    (hlinks : ∀ j : Fin tagged.length, tagged[j.val].2 = 1 →
      G.IsLink (edge j) (vertex tagged[j.val].1.1) (vertex tagged[j.val].1.2))
    (d : ℕ) (hd : d < 2 * tagged.length)
    (hactive : (tagged[d / 2]'(by omega)).2 = 1) :
    let xs := gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val))
    ∃ a b : Fin n,
      xs[d]?.getD 0 = a.val ∧ xs[gm06DartMate d]?.getD 0 = b.val ∧
      G.IsLink (edge ⟨d / 2, by omega⟩) (vertex a) (vertex b) := by
  dsimp only
  let j : Fin tagged.length := ⟨d / 2, by omega⟩
  let xs := gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val))
  have hlen : xs.length = 2 * tagged.length := by
    simp only [xs, gm06EndpointWords_length, List.length_map]
  have heven : xs[2 * j.val]?.getD 0 = tagged[j.val].1.1.val := by
    have hbound : 2 * j.val < xs.length := by rw [hlen]; omega
    rw [List.getElem?_eq_getElem hbound, Option.getD_some]
    rw [gm06EndpointWords_getElem_even, List.getElem_map]
    simpa only [List.length_map] using j.isLt
  have hodd : xs[2 * j.val + 1]?.getD 0 = tagged[j.val].1.2.val := by
    have hbound : 2 * j.val + 1 < xs.length := by rw [hlen]; omega
    rw [List.getElem?_eq_getElem hbound, Option.getD_some]
    rw [gm06EndpointWords_getElem_odd, List.getElem_map]
    simpa only [List.length_map] using j.isLt
  have hl := hlinks j hactive
  by_cases hp : d % 2 = 0
  · have hdEq : d = 2 * j.val := by dsimp only [j]; omega
    have hmEq : gm06DartMate d = 2 * j.val + 1 := by
      simp only [gm06DartMate, hp, ite_true]
      omega
    refine ⟨tagged[j.val].1.1, tagged[j.val].1.2, ?_, ?_, hl⟩
    · change xs[d]?.getD 0 = _
      exact (congrArg (fun r => xs[r]?.getD 0) hdEq).trans heven
    · change xs[gm06DartMate d]?.getD 0 = _
      rw [hmEq]
      exact hodd
  · have hdEq : d = 2 * j.val + 1 := by dsimp only [j]; omega
    have hmEq : gm06DartMate d = 2 * j.val := by
      simp only [gm06DartMate, hp, ite_false]
      omega
    refine ⟨tagged[j.val].1.2, tagged[j.val].1.1, ?_, ?_, hl.symm⟩
    · change xs[d]?.getD 0 = _
      exact (congrArg (fun r => xs[r]?.getD 0) hdEq).trans hodd
    · change xs[gm06DartMate d]?.getD 0 = _
      rw [hmEq]
      exact heven

end GraphMinor.Compute
