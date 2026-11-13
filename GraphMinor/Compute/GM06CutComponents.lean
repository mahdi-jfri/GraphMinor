module

public import GraphMinor.Compute.GM06CutDataProgram
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Data.List.Dedup

/-!
# Finite components indexed by the inner cuff edges

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) finds each
cut graph through its inner cuff edge. The underlying simple graph is
used only for reachability. The separate end labels keep loops and
parallel edges in the returned component data. Each component keeps
exactly the reachable vertices, its incident edge labels and the
induced subsequences of the copied rotations. No geometric strip
claim is part of these finite definitions.
-/

@[expose] public section
namespace GraphMinor.Compute
open SimpleGraph

/-- Permanent edge labels with both outgoing ends present in the cut data. -/
def gm06CutEdgeLabels (data : GM06CutData) : List ℕ :=
  ((data.activeDarts.map (· / 2)).dedup).filter
    (fun e => decide (2 * e ∈ data.activeDarts ∧ 2 * e + 1 ∈ data.activeDarts))

/-- Copied endpoints of a permanent copied edge label. -/
def gm06CutEndpoints (data : GM06CutData) (e : ℕ) : ℕ × ℕ :=
  (data.origins[2 * e]?.getD 0, data.origins[2 * e + 1]?.getD 0)

/-- A cut edge is present exactly when both directed ends are active. -/
theorem gm06CutEdgeLabels_mem_iff (data : GM06CutData) (e : ℕ) :
    e ∈ gm06CutEdgeLabels data ↔ 2 * e ∈ data.activeDarts ∧ 2 * e + 1 ∈ data.activeDarts := by
  constructor
  · intro he
    exact of_decide_eq_true (List.mem_filter.mp he).2
  · intro he
    apply List.mem_filter.mpr
    exact ⟨by simpa only [List.mem_dedup] using
      (List.mem_map.mpr ⟨2 * e, he.1, by omega⟩ : e ∈ data.activeDarts.map (· / 2)),
      decide_eq_true he⟩

/-- Edge labels are listed without repetitions. -/
theorem gm06CutEdgeLabels_nodup (data : GM06CutData) : (gm06CutEdgeLabels data).Nodup :=
  (List.nodup_dedup _).filter _

/-- The simple graph used for component searches. The endpoint and
rotation lists continue to distinguish every loop and parallel edge. -/
def gm06CutGraph (n : ℕ) (data : GM06CutData) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ u.val ∈ data.vertices ∧ v.val ∈ data.vertices ∧
    ∃ e ∈ gm06CutEdgeLabels data,
      gm06CutEndpoints data e = (u.val, v.val) ∨ gm06CutEndpoints data e = (v.val, u.val)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1,
    h.2.2.2.imp (fun _ he => ⟨he.1, he.2.symm⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Adjacency is a finite decidable edge-label search. -/
instance gm06CutGraph_decidableRel (n : ℕ) (data : GM06CutData) :
    DecidableRel (gm06CutGraph n data).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ ∃ e ∈ gm06CutEdgeLabels data, _))

/-- The vertices of the component reached through a selected cuff edge,
listed in increasing permanent label order. -/
def gm06CutComponentVertices {n : ℕ} (data : GM06CutData) (root : Fin n) : List ℕ :=
  ((List.finRange n).filter (fun v => decide ((gm06CutGraph n data).Reachable root v))).map Fin.val

/-- Exact vertex criterion for the finite component. -/
theorem gm06CutComponentVertices_mem_iff {n : ℕ} (data : GM06CutData) (root v : Fin n) :
    v.val ∈ gm06CutComponentVertices data root ↔ (gm06CutGraph n data).Reachable root v := by
  simp only [gm06CutComponentVertices, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨u, hu, heq⟩
    exact (Fin.ext heq) ▸ hu
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- Component vertex lists have no repeated permanent labels. -/
theorem gm06CutComponentVertices_nodup {n : ℕ} (data : GM06CutData) (root : Fin n) :
    (gm06CutComponentVertices data root).Nodup :=
  ((List.nodup_finRange n).filter _).map Fin.val_injective

/-- At most n vertices are returned by one component search. -/
theorem gm06CutComponentVertices_length_le {n : ℕ} (data : GM06CutData) (root : Fin n) :
    (gm06CutComponentVertices data root).length ≤ n := by
  simp only [gm06CutComponentVertices, List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

/-- Every returned vertex belongs to the original permanent vertex space. -/
theorem gm06CutComponentVertices_bound {n : ℕ} (data : GM06CutData) (root : Fin n) :
    ∀ v ∈ gm06CutComponentVertices data root, v < n := by
  intro v hv
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hv
  exact u.isLt

/-- The root belongs to its own component, including an isolated live vertex. -/
theorem gm06CutComponentVertices_root_mem {n : ℕ} (data : GM06CutData) (root : Fin n) :
    root.val ∈ gm06CutComponentVertices data root :=
  (gm06CutComponentVertices_mem_iff data root root).mpr (.refl _)

/-- Reachability from a live root never enters an unused permanent slot. -/
theorem gm06CutGraph_reachable_live {n : ℕ} (data : GM06CutData) (root v : Fin n)
    (hroot : root.val ∈ data.vertices) (hr : (gm06CutGraph n data).Reachable root v) :
    v.val ∈ data.vertices := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact hroot
  | @cons a b c hab p ih => exact ih hab.2.2.1

/-- All edges whose two ends belong to the selected component.
Loops and parallel edge labels are retained individually. -/
def gm06CutComponentEdges {n : ℕ} (data : GM06CutData) (root : Fin n) : List ℕ :=
  (gm06CutEdgeLabels data).filter (fun e => decide (
    (gm06CutEndpoints data e).1 ∈ gm06CutComponentVertices data root ∧
      (gm06CutEndpoints data e).2 ∈ gm06CutComponentVertices data root))

/-- The component edge criterion is exactly endpoint membership. -/
theorem gm06CutComponentEdges_mem_iff {n : ℕ} (data : GM06CutData) (root : Fin n) (e : ℕ) :
    e ∈ gm06CutComponentEdges data root ↔ e ∈ gm06CutEdgeLabels data ∧
      (gm06CutEndpoints data e).1 ∈ gm06CutComponentVertices data root ∧
      (gm06CutEndpoints data e).2 ∈ gm06CutComponentVertices data root := by
  simp only [gm06CutComponentEdges, List.mem_filter, decide_eq_true_eq]

/-- The complete finite output of a component search. All permanent
rotation slots remain, with only the component's induced ends kept. -/
def gm06CutComponentData {n : ℕ} (data : GM06CutData) (root : Fin n) : GM06CutData :=
  let keep := fun d => decide (d / 2 ∈ gm06CutComponentEdges data root)
  { rotations := data.rotations.map (List.filter keep)
    origins := data.origins
    activeDarts := data.activeDarts.filter keep
    vertices := gm06CutComponentVertices data root }

/-- Active component darts are precisely the old active darts of the
retained edge labels. -/
theorem gm06CutComponentData_active_iff {n : ℕ} (data : GM06CutData) (root : Fin n) (d : ℕ) :
    d ∈ (gm06CutComponentData data root).activeDarts ↔
      d ∈ data.activeDarts ∧ d / 2 ∈ gm06CutComponentEdges data root := by
  simp [gm06CutComponentData]

/-- The induced copied rotations are exactly the filtered original
outgoing-end list, in their original cyclic orders. -/
theorem gm06CutComponentData_flatten {n : ℕ} (data : GM06CutData) (root : Fin n) :
    (gm06CutComponentData data root).rotations.flatten = data.rotations.flatten.filter
      (fun d => decide (d / 2 ∈ gm06CutComponentEdges data root)) := by
  simp only [gm06CutComponentData, List.filter_flatten]

/-- Passing to a component preserves absence of repeated rotation darts. -/
theorem gm06CutComponentData_nodup {n : ℕ} (data : GM06CutData) (root : Fin n)
    (hnd : data.rotations.flatten.Nodup) : (gm06CutComponentData data root).rotations.flatten.Nodup := by
  rw [gm06CutComponentData_flatten]
  exact hnd.filter _

/-- Paired active ends remain paired after restriction to a component. -/
theorem gm06CutComponentData_mate {n : ℕ} (data : GM06CutData) (root : Fin n)
    (hpair : ∀ d ∈ data.activeDarts, gm06DartMate d ∈ data.activeDarts) :
    ∀ d ∈ (gm06CutComponentData data root).activeDarts,
      gm06DartMate d ∈ (gm06CutComponentData data root).activeDarts := by
  intro d hd
  rw [gm06CutComponentData_active_iff] at hd ⊢
  exact ⟨hpair d hd.1, by simpa only [gm06DartMate_edge] using hd.2⟩

/-- Recomputing the component's edges from its active ends gives
exactly the selected component edge list. -/
theorem gm06CutComponentData_edge_mem_iff {n : ℕ} (data : GM06CutData) (root : Fin n) (e : ℕ) :
    e ∈ gm06CutEdgeLabels (gm06CutComponentData data root) ↔ e ∈ gm06CutComponentEdges data root := by
  rw [gm06CutEdgeLabels_mem_iff, gm06CutComponentData_active_iff, gm06CutComponentData_active_iff]
  have hdiv₀ : 2 * e / 2 = e := by omega
  have hdiv₁ : (2 * e + 1) / 2 = e := by omega
  rw [hdiv₀, hdiv₁]
  constructor
  · exact fun h => h.1.2
  · intro h
    have hp := (gm06CutEdgeLabels_mem_iff data e).mp ((gm06CutComponentEdges_mem_iff data root e).mp h).1
    exact ⟨⟨hp.1, h⟩, hp.2, h⟩

/-- A live component contains only live vertices and has a connected
induced vertex graph. This is the finite meaning of the component
returned by the search, independent of the strip interpretation. -/
theorem gm06CutComponentVertices_connected {n : ℕ} (data : GM06CutData) (root : Fin n) :
    ((gm06CutGraph n data).induce {v | v.val ∈ gm06CutComponentVertices data root}).Connected := by
  let G := gm06CutGraph n data
  let C := G.connectedComponentMk root
  have hc := SimpleGraph.ConnectedComponent.connected_toSimpleGraph C
  have heq : C.supp = {v | v.val ∈ gm06CutComponentVertices data root} := by
    ext v
    change v ∈ C.supp ↔ v.val ∈ gm06CutComponentVertices data root
    rw [gm06CutComponentVertices_mem_iff]
    change G.connectedComponentMk v = G.connectedComponentMk root ↔ G.Reachable root v
    rw [SimpleGraph.ConnectedComponent.eq, G.reachable_comm]
  change (G.induce C.supp).Connected at hc
  rw [heq] at hc
  exact hc

/-- The positive inner cuff dart identifies the starting vertex of
its finite cut component. Gap i retains original edge label m+i. -/
def gm06CutInnerRoot (data : GM06CutData) (m i : ℕ) : ℕ := data.origins[4 * (m + i)]?.getD 0

/-- Total component lookup. An invalid root label returns NONE. -/
def gm06CutComponentAt (n : ℕ) (data : GM06CutData) (root : ℕ) : Option GM06CutData :=
  if h : root < n then some (gm06CutComponentData data ⟨root, h⟩) else none

/-- The list of finite components in inner cuff-gap order. Valid input
puts the positive inner cuff dart in its corresponding component. -/
def gm06CutComponents (n m k : ℕ) (data : GM06CutData) : List (Option GM06CutData) :=
  (List.range k).map (fun i => gm06CutComponentAt n data (gm06CutInnerRoot data m i))

/-- Each cuff gap contributes exactly one indexed component slot. -/
theorem gm06CutComponents_length (n m k : ℕ) (data : GM06CutData) :
    (gm06CutComponents n m k data).length = k := by simp [gm06CutComponents]

/-- A valid selected root returns its exact finite component. -/
theorem gm06CutComponentAt_eq_some {n root : ℕ} (data : GM06CutData) (hr : root < n) :
    gm06CutComponentAt n data root = some (gm06CutComponentData data ⟨root, hr⟩) := by
  simp [gm06CutComponentAt, hr]

end GraphMinor.Compute
