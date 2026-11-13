module

public import GraphMinor.Compute.GM06PuncturedGraphPort

/-!
# Reading an active edge from a punctured adjacency

Every adjacency used by the component search comes from a supplied
active endpoint pair, and neither endpoint is the cut vertex.
Keeping that witness in either orientation lets the completeness
proof translate a searched walk back to an actual graph separation.
-/

public section
namespace GraphMinor.Compute

/-- A pair retained by the punctured graph is an active supplied pair
with both endpoints different from the cut label. -/
theorem gm06PuncturedPairs_mem_active {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n) {e : Fin n × Fin n}
    (he : e ∈ gm06PuncturedPairs tagged cut) :
    ∃ flag, (e, flag) ∈ tagged ∧ flag = 1 ∧ e.1 ≠ cut ∧ e.2 ≠ cut := by
  obtain ⟨⟨p, flag⟩, hp, hmap⟩ := List.mem_filterMap.mp he
  change (if flag = 1 then if p.1 = cut then none else if p.2 = cut then none else some p else none) = some e at hmap
  split_ifs at hmap with hb ha hc <;> cases hmap
  exact ⟨flag, hp, hb, ha, hc⟩

/-- A searched adjacency has an active original edge witness, in
one of its two endpoint orientations, and avoids the cut label. -/
theorem gm06PuncturedGraphData_adj_active {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n) {a b : Fin n}
    (hab : (gm06PuncturedGraphData tagged cut).vertexGraph.Adj a b) :
    a ≠ cut ∧ b ≠ cut ∧ ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧
      ((a = tagged[j].1.1 ∧ b = tagged[j].1.2) ∨
        (a = tagged[j].1.2 ∧ b = tagged[j].1.1)) := by
  obtain ⟨_, e, he⟩ := hab
  have hmem : (gm06PuncturedPairs tagged cut)[e.val]'e.isLt ∈ gm06PuncturedPairs tagged cut := List.getElem_mem e.isLt
  obtain ⟨flag, hp, hflag, hu, hv⟩ := gm06PuncturedPairs_mem_active tagged cut hmem
  obtain ⟨j, hj, hjp⟩ := List.mem_iff_getElem.mp hp
  have hpair : tagged[j].1 = (gm06PuncturedPairs tagged cut)[e.val]'e.isLt := congrArg Prod.fst hjp
  have hbflag : tagged[j].2 = 1 := (congrArg Prod.snd hjp).trans hflag
  change (a = ((gm06PuncturedPairs tagged cut)[e.val]'e.isLt).1 ∧
      b = ((gm06PuncturedPairs tagged cut)[e.val]'e.isLt).2) ∨
    (a = ((gm06PuncturedPairs tagged cut)[e.val]'e.isLt).2 ∧
      b = ((gm06PuncturedPairs tagged cut)[e.val]'e.isLt).1) at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hu, hv, ⟨j, hj⟩, hbflag, Or.inl ⟨(congrArg Prod.fst hpair).symm, (congrArg Prod.snd hpair).symm⟩⟩
  · exact ⟨hv, hu, ⟨j, hj⟩, hbflag, Or.inr ⟨(congrArg Prod.snd hpair).symm, (congrArg Prod.fst hpair).symm⟩⟩

end GraphMinor.Compute
