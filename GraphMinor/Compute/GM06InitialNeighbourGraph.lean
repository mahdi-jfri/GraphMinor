module

public import GraphMinor.Compute.GM06InitialNeighbour
public import GraphMinor.Compute.GM06ActiveDartLink
import GraphMinor.Compute.GM06EndpointValency

/-!
# The initial neighbour query returns an actual graph neighbour

A supplied directed path row starts at its prescribed initial
vertex and uses active edges. The verified neighbour program reads
the other endpoint of its first edge. The directed-end interpretation
therefore identifies its output with an actual link in the current
graph. This supplies the graph interpretation for the contraction
query in VI (5.7), page 133.
-/

public section
namespace GraphMinor.Compute
universe u v

/-- From a valid first directed path edge, the RAM query returns
the actual opposite vertex, with its original edge label retained. -/
theorem gm06InitialNeighbourProg_exec_on_graph {w n : ℕ} {α : Type u} {β : Type v}
    (G : Graph α β) (vertex : Fin n → α)
    (tagged : List ((Fin n × Fin n) × ℕ)) (edge : Fin tagged.length → β)
    (hlinks : ∀ j : Fin tagged.length, tagged[j.val].2 = 1 →
      G.IsLink (edge j) (vertex tagged[j.val].1.1) (vertex tagged[j.val].1.2))
    (paths : List (List ℕ)) (i : ℕ) (hi : i < paths.length) (hne : 0 < paths[i].length)
    (hfirst : paths[i][0] < 2 * tagged.length)
    (hactive : (tagged[paths[i][0] / 2]'(by omega)).2 = 1)
    (a : Fin n)
    (hstart : (gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))[paths[i][0]]?.getD 0 = a.val)
    (s : State) (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * tagged.length < 2 ^ w)
    (hpLen : (gm06EncodeRows paths).length < 2 ^ w)
    (hpWords : ∀ v ∈ gm06EncodeRows paths, v < 2 ^ w)
    (h3 : s.arrs 3 = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (h8 : s.arrs 8 = gm06EncodeRows paths) (h295 : s.regs 295 = i) :
    ∃ s' t, Exec w gm06InitialNeighbourProg s s' t ∧
      t ≤ 33 + 17 * i + 22 * paths[i].length ∧
      TwoPaths.Keeps [7, 8, 9, 11, 31, 23, 24, 301] [24] s s' ∧
      s'.regs 23 = paths[i][0] ∧ s'.regs 24 = gm06DartMate paths[i][0] ∧
      ∃ b : Fin n, s'.regs 301 = b.val ∧
        G.IsLink (edge ⟨paths[i][0] / 2, by omega⟩) (vertex a) (vertex b) := by
  let xs := gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val))
  have hlen : xs.length = 2 * tagged.length := by
    simp only [xs, gm06EndpointWords_length, List.length_map]
  have hx : ∀ x ∈ xs, x < 2 ^ w := by
    intro x hx
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact q.1.1.isLt.trans hn
    · exact q.1.2.isLt.trans hn
  obtain ⟨s', t, hex, ht, hframe, h23, h24, h301⟩ := gm06InitialNeighbourProg_exec
    xs paths i hi hne s hw hm hlen hx hfirst hpLen hpWords h3 h8 h295
  obtain ⟨a', b, ha', hb, hl⟩ := gm06ActiveDart_isLink G vertex tagged edge hlinks paths[i][0] hfirst hactive
  have haa : a' = a := Fin.ext (ha'.symm.trans hstart)
  subst a'
  refine ⟨s', t, hex, ht, hframe, h23, h24, b, ?_, hl⟩
  have hmate : gm06DartMate paths[i][0] < xs.length := hlen ▸ gm06DartMate_lt hfirst
  change xs[gm06DartMate paths[i][0]]?.getD 0 = b.val at hb
  rw [List.getElem?_eq_getElem hmate, Option.getD_some] at hb
  exact h301.trans hb

end GraphMinor.Compute
