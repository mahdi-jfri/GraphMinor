module

public import GraphMinor.Compute.CrossingOpsEdgeRows

/-!
# Membership tests for the extra retained edges

The selected prefix contains every edge in earlier rows and chosen neighbours of its
last row. For an increasing pair, membership is therefore decided by the smaller
endpoint and the final row's neighbour marks.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- The numerical neighbours selected from the final row. -/
def edgeBoundaryList {N : ℕ} (lists : Fin N → List ℕ) (u : Fin N) (q : ℕ) : List ℕ :=
  ((lists u).filter (fun y => u.val < y)).take q

/-- Reading the second endpoints of a row recovers its increasing numerical neighbours. -/
theorem edgeRow_second_vals {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) (u : Fin N) :
    (edgeRow lists u).map (fun p => p.2.val) = (lists u).filter (fun y => u.val < y) := by
  rw [← map_val_toFin (h u).1, List.filter_map]
  simp only [edgeRow, List.map_map, Function.comp_def]

/-- A pair belongs to the final row prefix exactly when its numerical neighbour is selected. -/
theorem mem_edgeRow_take {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) (u v : Fin N) (q : ℕ) :
    (u, v) ∈ (edgeRow lists u).take q ↔ v.val ∈ edgeBoundaryList lists u q := by
  have hm : ((edgeRow lists u).take q).map (fun p => p.2.val) = edgeBoundaryList lists u q := by
    rw [List.map_take, edgeRow_second_vals h u]
    rfl
  rw [← hm]
  constructor
  · intro hh; exact List.mem_map.mpr ⟨(u, v), hh, rfl⟩
  · intro hh
    obtain ⟨⟨a, b⟩, hab, hval⟩ := List.mem_map.mp hh
    have ha := ((mem_edgeRow lists u a b).mp (List.mem_of_mem_take hab)).1
    have hb : b = v := Fin.ext hval
    simpa only [ha, hb] using hab

/-- Undirected prefix membership can be tested in its increasing orientation. -/
theorem mem_edgePrefixSet_ordered {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) (k : ℕ) (u v : Fin N) (huv : u.val < v.val) :
    s(u, v) ∈ edgePrefixSet lists k ↔ (u, v) ∈ (edgeStream lists).take k := by
  simp only [edgePrefixSet, Finset.mem_coe, List.mem_toFinset]
  rw [← List.map_take]
  constructor
  · intro hh
    obtain ⟨⟨a, b⟩, hab, heq⟩ := List.mem_map.mp hh
    have heq' : a = u ∧ b = v ∨ a = v ∧ b = u := by simpa only [Sym2.eq_iff] using heq
    rcases heq' with heq | heq
    · simpa only [heq.1, heq.2] using hab
    · have hlt := ((mem_edgeStream h a b).mp (List.mem_of_mem_take hab)).2
      have h1 := congrArg Fin.val heq.1
      have h2 := congrArg Fin.val heq.2
      omega
  · intro hh
    exact List.mem_map.mpr ⟨(u, v), hh, rfl⟩

/-- Among old edges in increasing orientation, the prefix test needs only the final
row index and membership in its chosen neighbour prefix. -/
theorem mem_edgePrefixSet_rows {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) (cut u v : Fin N) (q k : ℕ)
    (hq : q ≤ (edgeRow lists cut).length) (hk : (edgeRowsBefore lists cut.val).length + q = k)
    (hadj : G.Adj u v) (huv : u.val < v.val) :
    s(u, v) ∈ edgePrefixSet lists k ↔
      u.val < cut.val ∨ (u = cut ∧ v.val ∈ edgeBoundaryList lists cut q) := by
  rw [mem_edgePrefixSet_ordered h k u v huv, ← edgeRowsBefore_take_eq lists cut q k hq hk,
    List.mem_append, mem_edgeRowsBefore h]
  have hrow : (u, v) ∈ (edgeRow lists cut).take q ↔
      u = cut ∧ v.val ∈ edgeBoundaryList lists cut q := by
    constructor
    · intro hh
      have hu := ((mem_edgeRow lists cut u v).mp (List.mem_of_mem_take hh)).1
      refine ⟨hu, ?_⟩
      subst u
      exact (mem_edgeRow_take h cut v q).mp hh
    · rintro ⟨hu, hh⟩
      simpa only [hu] using (mem_edgeRow_take h cut v q).mpr hh
  simp only [hadj, huv, true_and, hrow]

end GraphMinor.Compute.Crossing
