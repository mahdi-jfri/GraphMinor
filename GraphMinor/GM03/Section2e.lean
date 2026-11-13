module

public import GraphMinor.GM03.Section2d
public import GraphMinor.GM11.HubCollar
import GraphMinor.GM11.HubWalk
import GraphMinor.GM11.CollarCut
import GraphMinor.GM11.Section81
import GraphMinor.GM11.RegionWalk
import GraphMinor.GM11.NiceStatements
import GraphMinor.GM11.Theorem75
import GraphMinor.GM11.RadialExists

/-!
# Graph Minors III, Section 2 Hub-Collar Perimeter Analysis for Claim (2) of `(2.2)`

This file develops the hub-collar perimeter and collar-chord tools for Claim `(2)` of `(2.2)`
(page 53) of N. Robertson and P. D. Seymour, *Graph Minors. III. Planar Tree-Width*,
J. Combin. Theory Ser. B **36** (1984), 49–64:
- `isHubCollar_shift_iter`, `perim_V_E_eq_of_isHubCollar`, and `exists_repeated_vertex_of_not_isCircuit`:
  cyclic shifting of hub collars and extracting a repeated vertex along the boundary walk of `R_N`
  when the connected perimeter `B = perimDraw (innerDraw D d' C) R_N` (`|B.V| ≥ 3`) is not a circuit.
- `bad_collar_vertex_subsingleton`: using `GM11.exists_end_limit` and `HasAtMostOneOuterEdge`
  (condition `(iv)` of `(2.2)`) to show that at most one visit of any vertex along the perimeter
  walk approaches an outer edge of `D`.
- `exists_collar_chord_of_good_corner`: constructing a collar chord inside a single region `q ∈ D.R`
  (`q ⊆ R_N`) across a repeated corner free of outer edges while preserving the outer perimeter.
-/

@[expose] public section

namespace GraphMinor.GM03

open Function Topology Classical Filter unitInterval
open Graph SimpleGraph Set
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM11
open GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM22

universe u v

variable {α : Type u} {β : Type v}

/-! ## Part 1: Hub Collar of `perimDraw N R_N` and Repeated Vertex when `¬ B.IsCircuit` -/

section HubCollarPerim

variable {S : Type} [TopologicalSpace S]

/-- Iterating `IsHubCollar.shift` `k` times shifts the collar sequences by `k`. -/
theorem isHubCollar_shift_iter {Γ Γ' H : Drawing S} {r : Set S} {n : ℕ}
    {v : ℕ → S} {a s P : ℕ → Set S} {ε : ℕ → I → S} {h : C(Circle × I, S)}
    (hc : IsHubCollar Γ Γ' H r n v a s P ε h) (k : ℕ) :
    ∃ h' : C(Circle × I, S),
      IsHubCollar Γ Γ' H r n (fun i => v (i + k)) (fun i => a (i + k))
        (fun i => s (i + k)) (fun i => P (i + k)) (fun i => ε (i + k)) h' ∧
      ∀ z t, h' (z, t) = h (z * Circle.exp (2 * Real.pi * (k / n)), t) := by
  induction k with
  | zero =>
    refine ⟨h, ?_, fun z t => ?_⟩
    · simpa using hc
    · simp [Circle.exp_zero]
  | succ k ih =>
    obtain ⟨h₁, hc₁, hh₁⟩ := ih
    obtain ⟨h₂, hc₂, hh₂⟩ := hc₁.shift
    have h_eq : ∀ α (f : ℕ → α), (fun i => f (i + (k + 1))) = (fun i => f (i + 1 + k)) :=
      fun _ f => funext fun i => congrArg f (by omega)
    refine ⟨h₂, ?_, fun z t => ?_⟩
    · rw [h_eq _ v, h_eq _ a, h_eq _ s, h_eq _ P, h_eq _ ε]
      exact hc₂
    · rw [hh₂, hh₁, mul_assoc, ← Circle.exp_add]
      have harg : 2 * Real.pi / (n : ℝ) + 2 * Real.pi * ((k : ℝ) / n) =
          2 * Real.pi * ((↑(k + 1) : ℝ) / n) := by push_cast; ring
      rw [harg]

/-- In a simple drawing `D`, any subdrawing `B` has no loops (`hloop` condition of
`exists_hub_collar`). -/
theorem noLoop_of_simple_subdrawing [T2Space S] {D B : Drawing S}
    (hSimple : D.toGraph.Simple) (hB : B.IsSubdrawing D) :
    ∀ e ∈ B.E, ∃ x y, x ≠ y ∧ closure e ∩ B.V = {x, y} := by
  intro e he
  obtain ⟨u, v, hl⟩ := B.toGraph.exists_isLink_of_mem_edgeSet he
  have hlD : D.toGraph.IsLink e u v :=
    ⟨hB.2 he, hB.1 hl.left_mem, hB.1 hl.right_mem, (hB.closure_inter_V he).symm.trans hl.2.2.2⟩
  have huv : u ≠ v := fun h => hSimple.not_isLoopAt e u (h ▸ hlD)
  exact ⟨u, v, huv, hl.2.2.2⟩

/-- If `IsGraphConnected B.toGraph` and `3 ≤ B.V.ncard`, then `B.E.Nonempty` and
`(PaintingOrDrawing.drawing B).IsTwoCell`. -/
theorem isTwoCell_and_E_nonempty_of_connected [ConnectedSpace S]
    (hS : IsClosedSurface S) (hSph : IsSphere S) {B : Drawing S}
    (hConn : IsGraphConnected B.toGraph) (hcard3 : 3 ≤ B.V.ncard) :
    B.E.Nonempty ∧ (PaintingOrDrawing.drawing B).IsTwoCell := by
  have : T2Space S := hS.2.1
  obtain ⟨hBV_ne, hBU_conn⟩ := (isGraphConnected_iff_isPreconnected_U B).mp hConn
  have hBE_ne : B.E.Nonempty := by
    by_contra hnot
    rw [not_nonempty_iff_eq_empty] at hnot
    have hBU_eq_V : B.U = B.V := by
      rw [B.U_eq, hnot]
      simp
    obtain ⟨u, hu⟩ := hBV_ne
    have hBV_sub : B.V ⊆ {u} := by
      intro v hv
      by_contra hvu
      have hcl₁ : IsClosed ({u} : Set S) := isClosed_singleton
      have hcl₂ : IsClosed (B.V \ {u}) := (B.finite_V.subset sdiff_subset).isClosed
      have hcov : B.U ⊆ {u} ∪ (B.V \ {u}) := by
        rw [hBU_eq_V]
        intro z hz
        by_cases hzu : z = u
        · exact Or.inl hzu
        · exact Or.inr ⟨hz, hzu⟩
      obtain ⟨z, _, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hBU_conn _ _ hcl₁ hcl₂ hcov
        ⟨u, B.V_subset_U hu, rfl⟩ ⟨v, B.V_subset_U hv, hv, hvu⟩
      exact hz₂.2 hz₁
    have hle1 : B.V.ncard ≤ 1 := (ncard_le_ncard hBV_sub).trans (by simp)
    omega
  have hBU_ne : B.U.Nonempty := by
    obtain ⟨v, hv⟩ := hBV_ne
    exact ⟨v, B.V_subset_U hv⟩
  exact ⟨hBE_ne, inferInstance, fun r hr =>
    (isOpenDisc_and_isPreconnected_frontier_of_isPreconnected_U hS hSph hBU_ne hBU_conn hr).1⟩

/-- In a hub collar `hc` of `R_N` in `B = perimDraw N R_N`, every vertex of `B.V` is `v i` for some
`i < n`, and every edge of `B.E` is `a i` for some `i < n`. -/
theorem perim_V_E_eq_of_isHubCollar [ConnectedSpace S] [T2Space S] (hS : IsClosedSurface S)
    {N Γ' H : Drawing S} {R_N : Set S} (hRN : R_N ∈ N.R)
    {n : ℕ} {v : ℕ → S} {a s P : ℕ → Set S} {ε : ℕ → I → S} {h : C(Circle × I, S)}
    (hc : IsHubCollar (perimDraw N R_N) Γ' H R_N n v a s P ε h) :
    (perimDraw N R_N).V = v '' Iio n ∧
    (perimDraw N R_N).E = a '' Iio n ∧
    (perimDraw N R_N).U = ⋃ i < n, closure (a i) := by
  let B := perimDraw N R_N
  obtain ⟨_, _, _, hBU_fr, _⟩ := perimDraw_spec hS hRN
  have hBU : B.U = ⋃ i < n, closure (a i) := by
    refine Subset.antisymm ?_ (iUnion₂_subset fun i _ => B.closure_subset_U (hc.edge i))
    change (perimDraw N R_N).U ⊆ _
    rw [hBU_fr, ← hc.range_bottom]
    rintro _ ⟨z, rfl⟩
    obtain ⟨i, hi, u, _, rfl⟩ := GM11.exists_circle_param hc.pos z
    change h (Circle.exp (2 * Real.pi * ((↑i + ↑u) / ↑n)), 0) ∈ _
    rw [hc.bottom i hi u]
    refine mem_iUnion₂.mpr ⟨i, hi, ?_⟩
    rw [← hc.ε_range i]
    exact mem_range_self u
  have hBV : B.V = v '' Iio n := by
    refine Subset.antisymm (fun x hx => ?_) ?_
    · have hxU : x ∈ B.U := B.V_subset_U hx
      rw [hBU] at hxU
      obtain ⟨i, hi, hxa⟩ := mem_iUnion₂.mp hxU
      have hcap : x ∈ closure (a i) ∩ B.V := ⟨hxa, hx⟩
      rw [hc.cap i] at hcap
      rcases hcap with rfl | rfl
      · exact ⟨i, hi, rfl⟩
      · refine ⟨(i + 1) % n, Nat.mod_lt _ hc.pos, ?_⟩
        exact IsHubCollar.mod_eq hc.per_v (i + 1)
    · rintro _ ⟨i, _, rfl⟩
      exact hc.vertex i
  have hBE : B.E = a '' Iio n := by
    refine Subset.antisymm (fun e he => ?_) ?_
    · obtain ⟨y, hy⟩ := he.1
      have hyU : y ∈ B.U := (he.2.1 hy).1
      have hy_not_V : y ∉ B.V := (he.2.1 hy).2
      rw [hBU] at hyU
      obtain ⟨i, hi, hya⟩ := mem_iUnion₂.mp hyU
      have hy_ai : y ∈ a i :=
        (B.closure_diff_V (hc.edge i)).symm ▸ ⟨hya, hy_not_V⟩
      exact ⟨i, hi, B.edge_eq_of_mem (hc.edge i) he hy_ai hy⟩
    · rintro _ ⟨i, _, rfl⟩
      exact hc.edge i
  exact ⟨hBV, hBE, hBU⟩

/-- A chain of `m` links produces a `GraphWalk` with explicit `edges` and `support`. -/
private theorem exists_collar_walk (D : Drawing S) {m : ℕ} {w : ℕ → S} {e : ℕ → Set S}
    (hlink : ∀ j < m, D.toGraph.IsLink (e j) (w j) (w (j + 1)))
    (hV : w m ∈ D.V) {z : S} (hz : w m = z) :
    ∀ d ≤ m, ∀ {u : S}, w (m - d) = u →
      ∃ W : GraphWalk D.toGraph u z,
        W.edges = (List.range' (m - d) d).map e ∧
        W.support = (List.range' (m - d) d).map w ++ [z] := by
  subst hz
  intro d
  induction d with
  | zero =>
    intro _ u hu
    subst hu
    simp only [Nat.sub_zero]
    exact ⟨.nil hV, by simp [GraphWalk.edges], by simp [GraphWalk.support]⟩
  | succ d ih =>
    intro hd u hu
    subst hu
    obtain ⟨W, hedges, hsupp⟩ := ih (by omega) rfl
    have hj : m - (d + 1) < m := by omega
    have hs : m - (d + 1) + 1 = m - d := by omega
    have hl := hlink _ hj
    rw [hs] at hl
    refine ⟨.cons hl W, ?_, ?_⟩
    · simp only [GraphWalk.edges, hedges]
      rw [show d + 1 = (d + 1) by rfl, List.range'_succ, List.map_cons, hs]
    · simp only [GraphWalk.support, hsupp]
      rw [show d + 1 = (d + 1) by rfl, List.range'_succ, List.map_cons, List.cons_append, hs]

/-- If `3 ≤ (perimDraw N R_N).V.ncard` and `¬ (perimDraw N R_N).IsCircuit`, then the vertex
sequence `v` of any hub collar `hc` of `R_N` in `perimDraw N R_N` repeats a vertex on `Iio n`:
there exist `i < j < n` with `v i = v j`. -/
theorem exists_repeated_vertex_of_not_isCircuit [ConnectedSpace S] [T2Space S] (hS : IsClosedSurface S)
    {D N Γ' H : Drawing S} {R_N : Set S} (hRN : R_N ∈ N.R)
    (_hSimple : D.toGraph.Simple) (_hBs : (perimDraw N R_N).IsSubdrawing D)
    (hcard3 : 3 ≤ (perimDraw N R_N).V.ncard)
    (hNotCirc : ¬ (perimDraw N R_N).IsCircuit)
    {n : ℕ} {v : ℕ → S} {a s P : ℕ → Set S} {ε : ℕ → I → S} {h : C(Circle × I, S)}
    (hc : IsHubCollar (perimDraw N R_N) Γ' H R_N n v a s P ε h) :
    ∃ i j, i < j ∧ j < n ∧ v i = v j := by
  let B := perimDraw N R_N
  obtain ⟨hBV, hBE, _⟩ := perim_V_E_eq_of_isHubCollar hS hRN hc
  have hn3 : 3 ≤ n := by
    have hIio : (Iio n).ncard = n := by
      have : Iio n = ↑(Finset.range n) := by ext x; simp
      rw [this, ncard_coe_finset, Finset.card_range]
    have hcard_le : (perimDraw N R_N).V.ncard ≤ n := by
      rw [hBV]
      exact (ncard_image_le (finite_Iio n)).trans hIio.le
    omega
  by_contra hno_rep
  push Not at hno_rep
  have hv_inj : ∀ i < n, ∀ j < n, v i = v j → i = j := by
    intro i hi j hj hij
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact (hno_rep i j hlt hj hij).elim
    · rfl
    · exact (hno_rep j i hgt hi hij.symm).elim
  have ha_inj : ∀ i < n, ∀ j < n, a i = a j → i = j := by
    intro i hi j hj haij
    have hcap := (hc.cap i).symm.trans (haij ▸ hc.cap j)
    rcases pair_eq_pair_iff.mp hcap with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact hv_inj i hi j hj h₁
    · exfalso
      have hij1 : i = (j + 1) % n :=
        hv_inj i hi ((j + 1) % n) (Nat.mod_lt _ hc.pos)
          (h₁.trans (IsHubCollar.mod_eq hc.per_v (j + 1)).symm)
      have hji1 : j = (i + 1) % n :=
        hv_inj j hj ((i + 1) % n) (Nat.mod_lt _ hc.pos)
          (h₂.symm.trans (IsHubCollar.mod_eq hc.per_v (i + 1)).symm)
      by_cases hi1 : i + 1 < n
      · rw [Nat.mod_eq_of_lt hi1] at hji1
        subst hji1
        by_cases hj1 : i + 1 + 1 < n
        · rw [Nat.mod_eq_of_lt hj1] at hij1
          omega
        · have h_eq_n : i + 1 + 1 = n := by omega
          rw [h_eq_n, Nat.mod_self] at hij1
          omega
      · have : i + 1 = n := by omega
        rw [this, Nat.mod_self] at hji1
        subst hji1
        rw [zero_add, Nat.mod_eq_of_lt (by omega)] at hij1
        omega
  have hlink : ∀ j < n, B.toGraph.IsLink (a j) (v j) (v (j + 1)) :=
    fun j _ => ⟨hc.edge j, hc.vertex j, hc.vertex (j + 1), hc.cap j⟩
  have hend : v n = v 0 := by
    have := hc.per_v 0
    rwa [zero_add] at this
  have hstart : v (n - n) = v 0 := by simp
  obtain ⟨W, hW_edges, hW_supp⟩ :=
    exists_collar_walk B hlink (hc.vertex n) hend n le_rfl hstart
  rw [Nat.sub_self] at hW_edges hW_supp
  have hW_len : 0 < W.length := by
    rw [GraphWalk.length, hW_edges, List.length_map, List.length_range']
    exact hc.pos
  have hW_edges_nodup : W.edges.Nodup := by
    rw [hW_edges, List.nodup_map_iff_inj_on (List.nodup_range')]
    intro i hi j hj hij
    rw [List.mem_range'] at hi hj
    rcases hi with ⟨ki, hki, rfl⟩
    rcases hj with ⟨kj, hkj, rfl⟩
    exact ha_inj (0 + 1 * ki) (by omega) (0 + 1 * kj) (by omega) hij
  have hW_Edges_set : B.E = {e | e ∈ W.edges} := by
    rw [hBE, hW_edges]
    ext e
    simp only [mem_image, mem_Iio, mem_ofPred_eq, List.mem_map, List.mem_range', zero_add, one_mul]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, ⟨i, hi, rfl⟩, rfl⟩
    · rintro ⟨j, ⟨i, hi, hij⟩, rfl⟩
      exact ⟨i, hi, hij ▸ rfl⟩
  have hW_V_set : B.V = {x | x ∈ W.support} := by
    rw [hBV, hW_supp]
    ext x
    simp only [mem_image, mem_Iio, mem_ofPred_eq, List.mem_append, List.mem_map,
      List.mem_range', zero_add, one_mul, List.mem_singleton]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact Or.inl ⟨i, ⟨i, hi, rfl⟩, rfl⟩
    · rintro (⟨j, ⟨i, hi, hij⟩, rfl⟩ | rfl)
      · exact ⟨i, hi, hij ▸ rfl⟩
      · exact ⟨0, hc.pos, rfl⟩
  have hW_supp_nodup : W.support.tail.Nodup := by
    have hr : List.range' 0 n = 0 :: List.range' 1 (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rfl
    have htail : W.support.tail = (List.range' 1 (n - 1)).map v ++ [v 0] := by
      rw [hW_supp, hr, List.map_cons, List.cons_append, List.tail_cons]
    rw [htail, List.nodup_append]
    refine ⟨?_, List.nodup_singleton _, ?_⟩
    · rw [List.nodup_map_iff_inj_on (List.nodup_range')]
      intro i hi j hj hij
      rw [List.mem_range'] at hi hj
      rcases hi with ⟨ki, hki, rfl⟩
      rcases hj with ⟨kj, hkj, rfl⟩
      exact hv_inj (1 + 1 * ki) (by omega) (1 + 1 * kj) (by omega) hij
    · intro x hx y hy hxy
      rw [List.mem_map] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [List.mem_range'] at hi
      rcases hi with ⟨ki, hki, rfl⟩
      rw [List.mem_singleton] at hy
      subst hy
      have hi0 := hv_inj (1 + 1 * ki) (by omega) 0 hc.pos hxy
      omega
  exact hNotCirc ⟨v 0, W, ⟨hW_supp_nodup, hW_edges_nodup⟩, hW_len, hW_V_set, hW_Edges_set⟩

/-- For any region `R_N ∈ N.R`, `R_N` is also a region of `perimDraw N R_N`. -/
theorem region_mem_perimDraw [ConnectedSpace S] [T2Space S] (hS : IsClosedSurface S)
    {N : Drawing S} {R_N : Set S} (hRN : R_N ∈ N.R) :
    R_N ∈ (perimDraw N R_N).R := by
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  let B := perimDraw N R_N
  obtain ⟨hBs, _, _, hBU_fr, _⟩ := perimDraw_spec hS hRN
  obtain ⟨x₀, hx₀⟩ := GM11.region_nonempty hRN
  have hx₀_not_BU : x₀ ∉ B.U := fun h => GM11.region_subset hRN hx₀ (hBs.U_subset h)
  obtain ⟨q, hq, hx₀_q⟩ := GM11.exists_region_of_notMem hx₀_not_BU
  have hRN_sub_q : R_N ⊆ q :=
    GM11.subset_region hq (GM11.region_isPreconnected hRN)
      (Set.disjoint_left.mpr fun z hzRN hzBU => GM11.region_subset hRN hzRN (hBs.U_subset hzBU))
      hx₀ hx₀_q
  have hq_sub_RN : q ⊆ R_N := by
    have hq_cov : q ⊆ R_N ∪ (closure R_N)ᶜ := by
      intro z hzq
      by_cases hzRN : z ∈ R_N
      · exact Or.inl hzRN
      · refine Or.inr fun hzcl => ?_
        have hzfr : z ∈ frontier R_N :=
          ⟨hzcl, by rw [(GM11.region_isOpen hRN).interior_eq]; exact hzRN⟩
        exact GM11.region_subset hq hzq (hBU_fr.symm ▸ hzfr)
    have hdis : Disjoint R_N (closure R_N)ᶜ :=
      Set.disjoint_left.mpr fun z hz hnot => hnot (subset_closure hz)
    rcases (GM11.region_isPreconnected hq).subset_or_subset
        (GM11.region_isOpen hRN) isClosed_closure.isOpen_compl hdis hq_cov with h | h
    · exact h
    · exact (h hx₀_q (subset_closure hx₀)).elim
  change R_N ∈ B.R
  rwa [← Subset.antisymm hq_sub_RN hRN_sub_q]

/-- For any vertex `v₀ ∈ B.V`, the set `{z : Circle | h (z, 0) = v₀}` is finite. -/
theorem collar_preimage_vertex_finite [T2Space S] {B Γ' H : Drawing S} {R_N : Set S}
    {n : ℕ} {v : ℕ → S} {a s P : ℕ → Set S} {ε : ℕ → I → S} {h : C(Circle × I, S)}
    (hc : IsHubCollar B Γ' H R_N n v a s P ε h) (v₀ : S) (hv₀ : v₀ ∈ B.V) :
    {z : Circle | h (z, 0) = v₀}.Finite := by
  refine ((finite_Iio n).image (fun i : ℕ => Circle.exp (2 * Real.pi * ((i : ℝ) / n)))).subset ?_
  intro z hz
  obtain ⟨i, hi, u, hu1, rfl⟩ := GM11.exists_circle_param hc.pos z
  change h (Circle.exp (2 * Real.pi * ((i + u.1) / n)), 0) = v₀ at hz
  rw [hc.bottom i hi u] at hz
  have hu0 : u = 0 := by
    by_contra hu_ne
    have hu_pos : (0 : I) < u := unitInterval.pos_iff_ne_zero.mpr hu_ne
    have hu_mem : ε i u ∈ a i := hc.image_Ioo i ▸ ⟨u, ⟨hu_pos, hu1⟩, rfl⟩
    exact ((hc.edge i).2.1 hu_mem).2 (hz ▸ hv₀)
  subst hu0
  exact ⟨i, hi, by simp⟩

/-- For any outer edge `f ∈ D.E \ (innerDraw D d' C).E`, any point `(z, 0)` in the closure of
`{p : Circle × I | 0 < p.2 ∧ h p ∈ f}` has `h (z, 0) ∈ closure f ∩ (perimDraw N R_N).V`, and there
is at most one such `z : Circle`. -/
theorem bad_collar_edge_subsingleton [ConnectedSpace S] [T2Space S] (hS : IsClosedSurface S)
    {D Γ' H : Drawing S} {d' : ℕ} {C : Fin d' → Drawing S} {R_N : Set S}
    (hSimple : D.toGraph.Simple) (hRN : R_N ∈ (innerDraw D d' C).R)
    {n : ℕ} {v : ℕ → S} {a s P : ℕ → Set S} {ε : ℕ → I → S} {h : C(Circle × I, S)}
    (hc : IsHubCollar (perimDraw (innerDraw D d' C) R_N) Γ' H R_N n v a s P ε h)
    {f : Set S} (hf : f ∈ D.E \ (innerDraw D d' C).E) :
    (∀ z : Circle, (z, (0 : I)) ∈ closure {p : Circle × I | 0 < p.2 ∧ h p ∈ f} →
      h (z, 0) ∈ closure f ∩ (perimDraw (innerDraw D d' C) R_N).V) ∧
    {z : Circle | (z, (0 : I)) ∈ closure {p : Circle × I | 0 < p.2 ∧ h p ∈ f}}.Subsingleton := by
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  let N := innerDraw D d' C
  let B := perimDraw N R_N
  obtain ⟨hNs, hNV, hNE, _⟩ := innerDraw_spec D d' C
  obtain ⟨hBs, hBV, _, hBU_fr, _⟩ := perimDraw_spec hS hRN
  have hBDs : B.IsSubdrawing D := ⟨hBs.1.trans hNs.1, fun e he => hNs.2 (hBs.2 he)⟩
  have hmem_BV : ∀ z : Circle, (z, (0 : I)) ∈ closure {p : Circle × I | 0 < p.2 ∧ h p ∈ f} →
      h (z, 0) ∈ closure f ∩ B.V := by
    intro z hz
    have hcl_pre : IsClosed (h ⁻¹' closure f) := isClosed_closure.preimage h.continuous
    have hz_clf : h (z, 0) ∈ closure f :=
      hcl_pre.closure_subset_iff.mpr (fun p hp => subset_closure hp.2) hz
    have hz_BU : h (z, 0) ∈ B.U := by
      change (perimDraw N R_N).U _
      rw [hBU_fr, ← hc.range_bottom]
      exact mem_range_self z
    refine ⟨hz_clf, ?_⟩
    by_contra hz_not_BV
    obtain ⟨e, heB, hze⟩ := B.exists_edge_of_mem hz_BU hz_not_BV
    have heD : e ∈ D.E := hBDs.2 heB
    have hz_not_DV : h (z, 0) ∉ D.V := (heD.2.1 hze).2
    have hzf : h (z, 0) ∈ f := (D.closure_diff_V hf.1).symm ▸ ⟨hz_clf, hz_not_DV⟩
    have hfe : f = e := D.edge_eq_of_mem hf.1 heD hzf hze
    exact hf.2 (hfe ▸ hBs.2 heB)
  refine ⟨hmem_BV, fun z₁ hz₁ z₂ hz₂ => ?_⟩
  have hz₁_BV := hmem_BV z₁ hz₁
  have hz₂_BV := hmem_BV z₂ hz₂
  set v₀ := h (z₁, 0)
  have hne_set : {p : Circle × I | 0 < p.2 ∧ h p ∈ f}.Nonempty :=
    closure_nonempty_iff.mp ⟨(z₁, 0), hz₁⟩
  obtain ⟨p₀, hp₀_pos, hp₀_f⟩ := hne_set
  have hp₀_RN : h p₀ ∈ R_N := hc.mem_r p₀ hp₀_pos
  obtain ⟨u₁, u₂, hu₁u₂, hcap_f⟩ :=
    noLoop_of_simple_subdrawing hSimple ⟨Subset.rfl, Subset.rfl⟩ f hf.1
  have hL_f : IsLineWithEnds (closure f) u₁ u₂ := GM11.isLine_closure hf.1 hu₁u₂ hcap_f
  have hf_eq_sdiff : f = closure f \ {u₁, u₂} := by
    conv_lhs => rw [← D.closure_diff_V hf.1]
    ext y
    constructor
    · rintro ⟨hycl, hyV⟩
      refine ⟨hycl, fun h => hyV ?_⟩
      have : y ∈ closure f ∩ D.V := hcap_f.symm ▸ h
      exact this.2
    · rintro ⟨hycl, hynot⟩
      exact ⟨hycl, fun hyV => hynot (hcap_f ▸ ⟨hycl, hyV⟩)⟩
  have hf_pre : IsPreconnected f := by
    rw [hf_eq_sdiff]
    exact (GM11.isPathConnected_sdiff_pair hL_f).isConnected.isPreconnected
  have hf_disj_NU : Disjoint f N.U := by
    rw [Set.disjoint_left]
    intro y hyf hyNU
    have hy_not_DV : y ∉ D.V := (hf.1.2.1 hyf).2
    rw [N.U_eq] at hyNU
    rcases hyNU with hyNV | hyE
    · exact hy_not_DV (hNs.1 hyNV)
    · obtain ⟨e, heN, hye⟩ := mem_iUnion₂.mp hyE
      have hye_e : y ∈ e := (D.closure_diff_V (hNs.2 heN)).symm ▸ ⟨hye, hy_not_DV⟩
      have hfe : f = e := D.edge_eq_of_mem hf.1 (hNs.2 heN) hyf hye_e
      exact hf.2 (hfe ▸ heN)
  have hf_sub_RN : f ⊆ R_N :=
    GM11.subset_region hRN hf_pre hf_disj_NU hp₀_f hp₀_RN
  have hnot_sub_NV : ¬ (closure f ∩ D.V ⊆ N.V) := fun hsub =>
    hf.2 (hNE ▸ ⟨hf.1, hNV ▸ hsub⟩)
  have hv₀_NV : v₀ ∈ N.V := hBs.1 hz₁_BV.2
  have hz₂_NV : h (z₂, 0) ∈ N.V := hBs.1 hz₂_BV.2
  have hv₀_cap : v₀ ∈ ({u₁, u₂} : Set S) := hcap_f ▸ ⟨hz₁_BV.1, hNs.1 hv₀_NV⟩
  have hz₂_cap : h (z₂, 0) ∈ ({u₁, u₂} : Set S) := hcap_f ▸ ⟨hz₂_BV.1, hNs.1 hz₂_NV⟩
  have hz₂_eq_v₀ : h (z₂, 0) = v₀ := by
    by_contra hne_v
    have hsub : closure f ∩ D.V ⊆ N.V := by
      rw [hcap_f]
      rcases hv₀_cap with h₁ | h₁ <;> rcases hz₂_cap with h₂ | h₂
      · exact (hne_v (h₂.trans h₁.symm)).elim
      · rw [mem_singleton_iff] at h₂
        rintro x (rfl | rfl)
        · exact h₁ ▸ hv₀_NV
        · exact h₂ ▸ hz₂_NV
      · rw [mem_singleton_iff] at h₁
        rintro x (rfl | rfl)
        · exact h₂ ▸ hz₂_NV
        · exact h₁ ▸ hv₀_NV
      · rw [mem_singleton_iff] at h₁ h₂
        exact (hne_v (h₂.trans h₁.symm)).elim
    exact hnot_sub_NV hsub
  obtain ⟨w, hvw, hcap_vw⟩ : ∃ w, v₀ ≠ w ∧ closure f ∩ D.V = {v₀, w} := by
    rcases hv₀_cap with h₁ | h₁
    · exact ⟨u₂, h₁ ▸ hu₁u₂, h₁ ▸ hcap_f⟩
    · rw [mem_singleton_iff] at h₁
      exact ⟨u₁, h₁ ▸ hu₁u₂.symm, by rw [hcap_f, h₁, pair_comm]⟩
  have hL_vw : IsLineWithEnds (closure f) v₀ w := GM11.isLine_closure hf.1 hvw hcap_vw
  obtain ⟨φ_vw, hφ0, hφ1⟩ := hL_vw
  let ψ : I → S := fun t => (φ_vw t).1
  have hψ_cont : Continuous ψ := continuous_subtype_val.comp φ_vw.continuous
  have hψ_inj : Function.Injective ψ := fun t₁ t₂ h => φ_vw.injective (Subtype.ext h)
  have hψ0 : ψ 0 = v₀ := hφ0
  have hψ1 : ψ 1 = w := hφ1
  have hψ_range : range ψ = closure f := by
    ext y
    exact ⟨fun ⟨t, ht⟩ => ht ▸ (φ_vw t).2, fun hy => ⟨φ_vw.symm ⟨y, hy⟩, by simp [ψ]⟩⟩
  have hf_eq_vw : f = closure f \ {v₀, w} := by
    conv_lhs => rw [← D.closure_diff_V hf.1]
    ext y
    constructor
    · rintro ⟨hycl, hyV⟩
      refine ⟨hycl, fun h => hyV ?_⟩
      have : y ∈ closure f ∩ D.V := hcap_vw.symm ▸ h
      exact this.2
    · rintro ⟨hycl, hynot⟩
      exact ⟨hycl, fun hyV => hynot (hcap_vw ▸ ⟨hycl, hyV⟩)⟩
  have hbot : ∀ z : Circle, h (z, 0) ∈ R_Nᶜ := by
    intro z hzRN
    have hz_fr : h (z, 0) ∈ frontier R_N := hc.range_bottom ▸ mem_range_self z
    rw [(GM11.region_isOpen hRN).frontier_eq] at hz_fr
    exact hz_fr.2 hzRN
  have hoff : ∀ p : Circle × I, 0 < p.2 → h p ∉ R_Nᶜ :=
    fun p hp hnot => hnot (hc.mem_r p hp)
  have hψ_RN : ∀ t ∈ Ioo (0 : I) 1, ψ t ∉ R_Nᶜ := by
    intro t ht hnot
    have ht_ne0 : ψ t ≠ v₀ := fun h => ht.1.ne' (hψ_inj (h.trans hψ0.symm))
    have ht_ne1 : ψ t ≠ w := fun h => ht.2.ne (hψ_inj (h.trans hψ1.symm))
    have ht_f : ψ t ∈ f := by
      rw [hf_eq_vw, ← hψ_range]
      exact ⟨mem_range_self t, fun h => h.elim ht_ne0 ht_ne1⟩
    exact hnot (hf_sub_RN ht_f)
  obtain ⟨z₀, _, hl₀⟩ :=
    GM11.exists_end_limit hc.injOn hoff hbot hc.isOpen hψ_cont hψ_RN
      (by rw [hψ0]; exact hbot z₁)
      (by rw [hψ0]; exact collar_preimage_vertex_finite hc v₀ hz₁_BV.2)
  have h_eq_z₀ : ∀ z : Circle,
      (z, (0 : I)) ∈ closure {p : Circle × I | 0 < p.2 ∧ h p ∈ f} →
      h (z, 0) = v₀ → z = z₀ := by
    intro z hz hzv₀
    by_contra hne
    obtain ⟨x, hxB, hxt⟩ := mem_closure_iff_seq_limit.mp hz
    have hx_ψ : ∀ k, ∃ s : I, ψ s = h (x k) := fun k => by
      rw [← mem_range, hψ_range]
      exact subset_closure (hxB k).2
    choose s hs using hx_ψ
    have hs_Ioo : ∀ k, s k ∈ Ioo (0 : I) 1 := by
      intro k
      have hxk_f : h (x k) ∈ f := (hxB k).2
      rw [hf_eq_vw] at hxk_f
      refine ⟨unitInterval.pos_iff_ne_zero.mpr fun h0 => hxk_f.2 (Or.inl ?_),
        unitInterval.lt_one_iff_ne_one.mpr fun h1 => hxk_f.2 (Or.inr ?_)⟩
      · rw [← hs k, h0, hψ0]
      · rw [← hs k, h1, hψ1]
        rfl
    have hg : ∀ k, GM11.collarInv h (ψ (s k)) = x k := fun k => by
      rw [hs k]
      exact GM11.collarInv_apply hc.injOn (hxB k).1
    obtain ⟨s', _, φ, hφ, hlim⟩ :=
      isCompact_univ.tendsto_subseq (x := s) fun _ => mem_univ _
    have hxφ : Tendsto (x ∘ φ) atTop (𝓝 (z, (0 : I))) := hxt.comp hφ.tendsto_atTop
    have hval : ψ s' = v₀ := by
      have h₁ : Tendsto (fun k => ψ (s (φ k))) atTop (𝓝 (ψ s')) :=
        (hψ_cont.tendsto s').comp hlim
      have h₂ : Tendsto (fun k => h (x (φ k))) atTop (𝓝 (h (z, 0))) :=
        (h.continuous.tendsto _).comp hxφ
      rw [← hzv₀]
      exact tendsto_nhds_unique h₁ (h₂.congr fun k => (hs (φ k)).symm)
    have hs'_zero : s' = 0 := hψ_inj (hval.trans hψ0.symm)
    subst hs'_zero
    have hne_prod : ((z₀, (0 : I)) : Circle × I) ≠ (z, 0) :=
      fun he => hne (congrArg Prod.fst he).symm
    obtain ⟨U₀, U_z, hU₀, hU_z, hdis⟩ := t2_separation_nhds hne_prod
    obtain ⟨u, hu, hus⟩ := hl₀ U₀ hU₀
    have hev₁ : ∀ᶠ k in atTop, s (φ k) ∈ Iio u := hlim (Iio_mem_nhds hu)
    have hev₂ : ∀ᶠ k in atTop, x (φ k) ∈ U_z := hxφ hU_z
    obtain ⟨k, hk₁, hk₂⟩ := (hev₁.and hev₂).exists
    have h_in_U₀ := hus (s (φ k)) ⟨(hs_Ioo (φ k)).1, hk₁⟩
    rw [hg (φ k)] at h_in_U₀
    exact Set.disjoint_left.mp hdis h_in_U₀ hk₂
  exact (h_eq_z₀ z₁ hz₁ rfl).trans (h_eq_z₀ z₂ hz₂ hz₂_eq_v₀).symm

/-- Under `SurfaceDShell D r₀ d' C Δ` and `HasAtMostOneOuterEdge D d' C`:
1. every `(z, 0) ∈ closure {p : Circle × I | 0 < p.2 ∧ h p ∈ D.U}` has `h (z, 0) ∈ B.V`, and
2. for every `v₀ ∈ B.V`, `{z : Circle | h (z, 0) = v₀ ∧ (z, (0 : I)) ∈ closure {p | 0 < p.2 ∧ h p ∈ D.U}}`
   is a `Subsingleton`. -/
theorem bad_collar_vertex_subsingleton [ConnectedSpace S] [T2Space S] (hS : IsClosedSurface S)
    {D Γ' H : Drawing S} {r₀ R_N : Set S} {d' : ℕ} {C : Fin d' → Drawing S} {Δ : Fin d' → Set S}
    (hShell : SurfaceDShell D r₀ d' C Δ)
    (hOuter : HasAtMostOneOuterEdge D d' C)
    (hSimple : D.toGraph.Simple) (hRN : R_N ∈ (innerDraw D d' C).R)
    {n : ℕ} {v : ℕ → S} {a s P : ℕ → Set S} {ε : ℕ → I → S} {h : C(Circle × I, S)}
    (hc : IsHubCollar (perimDraw (innerDraw D d' C) R_N) Γ' H R_N n v a s P ε h) :
    (∀ z : Circle, (z, (0 : I)) ∈ closure {p : Circle × I | 0 < p.2 ∧ h p ∈ D.U} →
      h (z, 0) ∈ (perimDraw (innerDraw D d' C) R_N).V) ∧
    ∀ v₀ ∈ (perimDraw (innerDraw D d' C) R_N).V,
      {z : Circle | h (z, 0) = v₀ ∧
        (z, (0 : I)) ∈ closure {p : Circle × I | 0 < p.2 ∧ h p ∈ D.U}}.Subsingleton := by
  let N := innerDraw D d' C
  let B := perimDraw N R_N
  obtain ⟨hNs, hNV, hNE, _⟩ := innerDraw_spec D d' C
  obtain ⟨hBs, _, _, hBU_fr, _⟩ := perimDraw_spec hS hRN
  have hex_edge : ∀ z : Circle,
      (z, (0 : I)) ∈ closure {p : Circle × I | 0 < p.2 ∧ h p ∈ D.U} →
      ∃ f ∈ D.E \ N.E, (z, (0 : I)) ∈ closure {p : Circle × I | 0 < p.2 ∧ h p ∈ f} := by
    intro z hz
    by_cases hd' : 0 < d'
    · let j_last : Fin d' := ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩
      let U_int := interior (Δ j_last)
      have hBU_sub : B.U ⊆ U_int :=
        hBs.U_subset.trans (hShell.innerDraw_U_subset_interior hd')
      have hz_Uint : h (z, 0) ∈ U_int := by
        apply hBU_sub
        change (perimDraw N R_N).U _
        rw [hBU_fr, ← hc.range_bottom]
        exact mem_range_self z
      have hCi_disj : ∀ i : Fin d', Disjoint (C i).V U_int := by
        intro i
        rw [Set.disjoint_left]
        intro x hxi hxU
        have hx_bd : x ∈ discBd (Δ i) := (hShell.discBd_eq i).symm ▸ (C i).V_subset_U hxi
        have hx_int : x ∈ interior (Δ i) := by
          by_cases hij : i = j_last
          · exact hij ▸ hxU
          · have hilt : i < j_last :=
              lt_of_le_of_ne (Fin.le_def.mpr (Nat.le_sub_one_of_lt i.2)) hij
            exact hShell.disc_subset_interior hilt (interior_subset hxU)
        rw [← discInt_eq_interior_of_isClosedDisc hS (hShell.isClosedDisc i)] at hx_int
        exact hx_int.2 hx_bd
      have hsub_union : {p : Circle × I | 0 < p.2 ∧ h p ∈ D.U} ∩ h ⁻¹' U_int ⊆
          ⋃ f ∈ D.E \ N.E, {p : Circle × I | 0 < p.2 ∧ h p ∈ f} := by
        rintro p ⟨⟨hp_pos, hp_DU⟩, hp_Uint⟩
        have hp_RN : h p ∈ R_N := hc.mem_r p hp_pos
        have hp_not_NU : h p ∉ N.U := GM11.region_subset hRN hp_RN
        have hp_not_DV : h p ∉ D.V := by
          intro hp_DV
          by_cases hp_Ci : h p ∈ ⋃ i : Fin d', (C i).V
          · obtain ⟨i, hpi⟩ := mem_iUnion.mp hp_Ci
            exact Set.disjoint_left.mp (hCi_disj i) hpi hp_Uint
          · exact hp_not_NU (N.V_subset_U (hNV.symm ▸ ⟨hp_DV, hp_Ci⟩))
        obtain ⟨f, hfD, hpf⟩ := D.exists_edge_of_mem hp_DU hp_not_DV
        have hf_not_NE : f ∉ N.E := fun hfN => hp_not_NU (N.closure_subset_U hfN (subset_closure hpf))
        exact mem_iUnion₂.mpr ⟨f, ⟨hfD, hf_not_NE⟩, hp_pos, hpf⟩
      have hz_inter : (z, (0 : I)) ∈ closure ({p : Circle × I | 0 < p.2 ∧ h p ∈ D.U} ∩ h ⁻¹' U_int) := by
        rw [mem_closure_iff] at hz ⊢
        intro V hV hzV
        obtain ⟨p, hpV, hpB⟩ := hz (V ∩ h ⁻¹' U_int) (hV.inter (isOpen_interior.preimage h.continuous)) ⟨hzV, hz_Uint⟩
        exact ⟨p, hpV.1, hpB, hpV.2⟩
      have hz_un := closure_mono hsub_union hz_inter
      have hfin_diff : (D.E \ N.E).Finite := D.finite_edges.subset sdiff_subset
      rw [hfin_diff.closure_biUnion] at hz_un
      obtain ⟨f, hf, hzf⟩ := mem_iUnion₂.mp hz_un
      exact ⟨f, hf, hzf⟩
    · have hd'0 : d' = 0 := by omega
      subst hd'0
      have hND : N = D := innerDraw_zero_eq D C
      have hempty : {p : Circle × I | 0 < p.2 ∧ h p ∈ D.U} = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        rintro p ⟨hp_pos, hp_DU⟩
        exact GM11.region_subset (hND ▸ hRN) (hc.mem_r p hp_pos) hp_DU
      rw [hempty, closure_empty] at hz
      exact hz.elim
  refine ⟨fun z hz => ?_, fun v₀ hv₀ z₁ hz₁ z₂ hz₂ => ?_⟩
  · obtain ⟨f, hf, hzf⟩ := hex_edge z hz
    exact ((bad_collar_edge_subsingleton hS hSimple hRN hc hf).1 z hzf).2
  · obtain ⟨f₁, hf₁, hz₁_f⟩ := hex_edge z₁ hz₁.2
    obtain ⟨f₂, hf₂, hz₂_f⟩ := hex_edge z₂ hz₂.2
    have h₁ := (bad_collar_edge_subsingleton hS hSimple hRN hc hf₁).1 z₁ hz₁_f
    have h₂ := (bad_collar_edge_subsingleton hS hSimple hRN hc hf₂).1 z₂ hz₂_f
    rw [hz₁.1] at h₁
    rw [hz₂.1] at h₂
    have hv₀_NV : v₀ ∈ D.V \ ⋃ i : Fin d', (C i).V := hNV ▸ hBs.1 hv₀
    have hf₁_not : ¬ (closure f₁ ∩ D.V ⊆ D.V \ ⋃ i : Fin d', (C i).V) :=
      fun hsub => hf₁.2 (hNE ▸ ⟨hf₁.1, hsub⟩)
    have hf₂_not : ¬ (closure f₂ ∩ D.V ⊆ D.V \ ⋃ i : Fin d', (C i).V) :=
      fun hsub => hf₂.2 (hNE ▸ ⟨hf₂.1, hsub⟩)
    have hf_eq : f₁ = f₂ :=
      hOuter v₀ hv₀_NV ⟨hf₁.1, h₁.1, hf₁_not⟩ ⟨hf₂.1, h₂.1, hf₂_not⟩
    subst hf_eq
    exact (bad_collar_edge_subsingleton hS hSimple hRN hc hf₁).2 hz₁_f hz₂_f

/-- For any drawing `Γ : Drawing S` and vertex `v₀ ∈ Γ.V`, `(compSubdraw Γ v₀).U` is path-connected. -/
theorem isPathConnected_compSubdraw_U [ConnectedSpace S] [T2Space S]
    (Γ : Drawing S) {v₀ : S} (hv₀ : v₀ ∈ Γ.V) :
    IsPathConnected (compSubdraw Γ v₀).U := by
  let Γ₁ := compSubdraw Γ v₀
  obtain ⟨_, _, hV₁, _, hE₁, _, hv₀_mem, _, _, _⟩ := compSubdraw_spec Γ hv₀
  have hwalk_join : ∀ {u w : S}, u ∈ reachV Γ v₀ → GraphWalk Γ.toGraph u w →
      w ∈ reachV Γ v₀ ∧ JoinedIn Γ₁.U u w := by
    intro u w hu W
    induction W with
    | nil _ =>
      exact ⟨hu, JoinedIn.refl (Γ₁.V_subset_U (hV₁.symm ▸ hu))⟩
    | @cons a b c e hl _ ih =>
      have hbR : b ∈ reachV Γ v₀ := by
        obtain ⟨Wa⟩ := hu.2
        exact ⟨hl.right_mem, ⟨Wa.append (GraphWalk.cons hl (GraphWalk.nil hl.right_mem))⟩⟩
      obtain ⟨hcR, hc_join⟩ := ih hbR
      have he₁ : e ∈ Γ₁.E := by
        rw [hE₁]
        refine ⟨hl.1, fun z hz => ?_⟩
        rw [hl.2.2.2] at hz
        rcases hz with rfl | rfl
        · exact hu
        · exact hbR
      have hcl_pc : IsPathConnected (closure e) := GM11.isPathConnected_closure_edge he₁
      have ha_cl : a ∈ closure e :=
        (hl.2.2.2.symm ▸ mem_insert a {b} : a ∈ closure e ∩ Γ.V).1
      have hb_cl : b ∈ closure e :=
        (hl.2.2.2.symm ▸ mem_insert_of_mem a rfl : b ∈ closure e ∩ Γ.V).1
      have hab_join : JoinedIn Γ₁.U a b :=
        (hcl_pc.joinedIn a ha_cl b hb_cl).mono (Γ₁.closure_subset_U he₁)
      exact ⟨hcR, hab_join.trans hc_join⟩
  have hjoin_V : ∀ u ∈ Γ₁.V, JoinedIn Γ₁.U v₀ u := by
    intro u hu
    obtain ⟨W⟩ := (hV₁ ▸ hu).2
    exact (hwalk_join ⟨hv₀, ⟨GraphWalk.nil hv₀⟩⟩ W).2
  refine ⟨v₀, Γ₁.V_subset_U hv₀_mem, fun x hx => ?_⟩
  rw [Γ₁.U_eq] at hx
  rcases hx with hxV | hxE
  · exact hjoin_V x hxV
  · obtain ⟨e, he₁, hxe⟩ := mem_iUnion₂.mp hxE
    obtain ⟨a, b, hl⟩ := Γ₁.toGraph.exists_isLink_of_mem_edgeSet he₁
    have ha_cl : a ∈ closure e := by
      have : a ∈ closure e ∩ Γ₁.V := hl.2.2.2 ▸ mem_insert a {b}
      exact this.1
    have hja := hjoin_V a hl.left_mem
    have hpc_e := GM11.isPathConnected_closure_edge he₁
    have hjx := (hpc_e.joinedIn a ha_cl x hxe).mono (Γ₁.closure_subset_U he₁)
    exact hja.trans hjx

/-! ## Part 2: Collar Chord Construction and Claim (2) of `(2.2)` -/

/-- Half of a unit interval parameter: `halfT t = t / 2 ∈ I`. -/
noncomputable def halfT (t : I) : I :=
  ⟨(t : ℝ) / 2, div_nonneg t.2.1 (by norm_num), by linarith [t.2.2]⟩

theorem continuous_halfT : Continuous halfT :=
  (continuous_subtype_val.div_const (2 : ℝ)).subtype_mk _

@[simp] theorem coe_halfT (t : I) : ((halfT t : I) : ℝ) = (t : ℝ) / 2 := by rfl

@[simp] theorem halfT_zero : halfT 0 = 0 := by
  ext
  rw [coe_halfT, Set.Icc.coe_zero]
  norm_num

theorem halfT_pos {t : I} (ht : 0 < t) : 0 < halfT t := by
  rw [← Subtype.coe_lt_coe, coe_halfT, Set.Icc.coe_zero]
  have : (0 : ℝ) < t := ht
  linarith

theorem halfT_lt_one (t : I) : halfT t < 1 := by
  rw [← Subtype.coe_lt_coe, coe_halfT, Set.Icc.coe_one]
  linarith [t.2.2]

theorem halfT_inj : Function.Injective halfT := by
  intro t₁ t₂ h
  ext
  have hval : (t₁ : ℝ) / 2 = (t₂ : ℝ) / 2 := by
    rw [← coe_halfT, ← coe_halfT, h]
  linarith

/-- Given a hub collar `hc` of `R_N` in `B = perimDraw (innerDraw D d' C) R_N` such that:
- `v j₁ = v 1` for some `3 ≤ j₁ < n`,
- `(circlePt (1 / n), 0) ∉ closure {p : Circle × I | 0 < p.2 ∧ h p ∈ D.U}`, and
- `v 0 ≠ v 2` and `¬ D.toGraph.Adj (v 0) (v 2)`,
there exists a line `K` with endpoints `v 0, v 2` inside a region `q ∈ D.R` (`q ⊆ R_N`) and a
region `R_N' ∈ (innerDraw D' d' C).R` satisfying all hypotheses of `addChordInRegion_spec`. -/
theorem exists_collar_chord_of_good_corner [ConnectedSpace S] [T2Space S]
    (hS : IsClosedSurface S)
    {D Γ' H : Drawing S} {r₀ R_N : Set S} {d' : ℕ} {C : Fin d' → Drawing S} {Δ : Fin d' → Set S}
    (hShell : SurfaceDShell D r₀ d' C Δ)
    (hOuter : HasAtMostOneOuterEdge D d' C)
    (hSimple : D.toGraph.Simple) (hRN : R_N ∈ (innerDraw D d' C).R)
    {n : ℕ} {v : ℕ → S} {a s P : ℕ → Set S} {ε : ℕ → I → S} {h : C(Circle × I, S)}
    (hc : IsHubCollar (perimDraw (innerDraw D d' C) R_N) Γ' H R_N n v a s P ε h)
    {j₁ : ℕ} (hj₁_ge : 3 ≤ j₁) (hj₁_lt : j₁ < n) (hv_j₁ : v j₁ = v 1)
    (hGood : (GM11.circlePt (1 / (n : ℝ)), (0 : I)) ∉
      closure {p : Circle × I | 0 < p.2 ∧ h p ∈ D.U})
    (hv02 : v 0 ≠ v 2) :
    ∃ (K q : Set S) (hK : IsLineWithEnds K (v 0) (v 2)) (hq : q ∈ D.R)
      (hKq : K \ {v 0, v 2} ⊆ q),
      q ⊆ R_N ∧
      (∀ hd' : 0 < d', q ⊆ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩)) ∧
      let hv₀_D : v 0 ∈ D.V :=
        (innerDraw_spec D d' C).1.1 ((perimDraw_spec hS hRN).1.1 (hc.vertex 0))
      let hv₂_D : v 2 ∈ D.V :=
        (innerDraw_spec D d' C).1.1 ((perimDraw_spec hS hRN).1.1 (hc.vertex 2))
      let D' := D.glue (GM11.lineDrawing hK hv02)
        (lineDrawing_meet_of_subset_region hq hv₀_D hv₂_D hK hv02 hKq)
      ∃ R_N' ∈ (innerDraw D' d' C).R,
        R_N' ⊆ R_N ∧
        R_N \ q ⊆ R_N' ∧
        (perimDraw (innerDraw D d' C) R_N).V ⊆ (perimDraw (innerDraw D' d' C) R_N').V := by
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  let N := innerDraw D d' C
  let B := perimDraw N R_N
  obtain ⟨hNs, hNV, hNE, _⟩ := innerDraw_spec D d' C
  obtain ⟨hBs, hBV, _, hBU_fr, _⟩ := perimDraw_spec hS hRN
  have hn4 : 4 ≤ n := by omega
  have hn_pos : (0 : ℝ) < n := by positivity
  let Ψ : I × I → Circle × I := fun p => (GM11.circlePt (2 * (p.1 : ℝ) / n), halfT p.2)
  have hΨ_cont : Continuous Ψ :=
    (GM11.continuous_circlePt.comp
      ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).div_const _)).prodMk
      (continuous_halfT.comp continuous_snd)
  let Φ : I × I → S := fun p => h (Ψ p)
  have hΦ_cont : Continuous Φ := h.continuous.comp hΨ_cont
  have hΦ00 : Φ (0, 0) = v 0 := by
    change h (GM11.circlePt (2 * (0 : ℝ) / n), halfT 0) = v 0
    have h0 : 2 * (0 : ℝ) / n = ((0 : ℕ) + ((0 : I) : ℝ)) / n := by simp
    rw [halfT_zero, h0]
    exact (hc.bottom 0 (by omega) 0).trans (hc.ε_zero 0)
  have hΦ10 : Φ (1, 0) = v 2 := by
    change h (GM11.circlePt (2 * (1 : ℝ) / n), halfT 0) = v 2
    have h2 : 2 * (1 : ℝ) / n = ((2 : ℕ) + ((0 : I) : ℝ)) / n := by norm_num
    rw [halfT_zero, h2]
    exact (hc.bottom 2 (by omega) 0).trans (hc.ε_zero 2)
  let K_bad : Set (I × I) := closure {p : I × I | 0 < p.2 ∧ Φ p ∈ D.U} ∪ {(0, 1)}
  have hK_bad_closed : IsClosed K_bad := isClosed_closure.union isClosed_singleton
  have hK_bad_ne : K_bad.Nonempty := ⟨(0, 1), Or.inr rfl⟩
  have hnot_Kbad : ∀ s ∈ Ioo (0 : I) 1, (s, (0 : I)) ∉ K_bad := by
    intro s hs hmem
    rcases hmem with hcl | heq
    · have hΨ_map : Ψ '' {p : I × I | 0 < p.2 ∧ Φ p ∈ D.U} ⊆
          {q : Circle × I | 0 < q.2 ∧ h q ∈ D.U} := by
        rintro _ ⟨p, ⟨hp_pos, hp_DU⟩, rfl⟩
        exact ⟨halfT_pos hp_pos, hp_DU⟩
      have hΨ_cl : Ψ (s, 0) ∈ closure {q : Circle × I | 0 < q.2 ∧ h q ∈ D.U} :=
        closure_mono hΨ_map (image_closure_subset_closure_image hΨ_cont ⟨(s, 0), hcl, rfl⟩)
      have hΨ_s0 : Ψ (s, 0) = (GM11.circlePt (2 * (s : ℝ) / n), 0) :=
        Prod.ext rfl halfT_zero
      rw [hΨ_s0] at hΨ_cl
      have hs_BV : h (GM11.circlePt (2 * (s : ℝ) / n), 0) ∈ B.V :=
        (bad_collar_vertex_subsingleton hS hShell hOuter hSimple hRN hc).1 _ hΨ_cl
      have hs0 : (0 : ℝ) < s := hs.1
      have hs1 : (s : ℝ) < 1 := hs.2
      rcases lt_trichotomy (2 * (s : ℝ)) 1 with hlt | heq1 | hgt
      · let u : I := ⟨2 * (s : ℝ), by linarith, by linarith⟩
        have hu_Ioo : u ∈ Ioo (0 : I) 1 :=
          ⟨Subtype.mk_lt_mk.mpr (by change (0 : ℝ) < 2 * (s : ℝ); linarith),
           Subtype.mk_lt_mk.mpr (by change 2 * (s : ℝ) < 1; linarith)⟩
        have h_eq_u : 2 * (s : ℝ) / n = ((0 : ℕ) + (u : ℝ)) / n := by simp [u]
        rw [h_eq_u] at hs_BV
        have h_bot := hc.bottom 0 (by omega) u
        change h (GM11.circlePt (((0 : ℕ) + (u : ℝ)) / n), 0) = ε 0 u at h_bot
        rw [h_bot] at hs_BV
        have hu_a0 : ε 0 u ∈ a 0 := hc.image_Ioo 0 ▸ ⟨u, hu_Ioo, rfl⟩
        exact ((hc.edge 0).2.1 hu_a0).2 hs_BV
      · rw [heq1] at hΨ_cl
        exact hGood hΨ_cl
      · let u : I := ⟨2 * (s : ℝ) - 1, by linarith, by linarith⟩
        have hu_Ioo : u ∈ Ioo (0 : I) 1 :=
          ⟨Subtype.mk_lt_mk.mpr (by change (0 : ℝ) < 2 * (s : ℝ) - 1; linarith),
           Subtype.mk_lt_mk.mpr (by change 2 * (s : ℝ) - 1 < 1; linarith)⟩
        have h_eq_u : 2 * (s : ℝ) / n = ((1 : ℕ) + (u : ℝ)) / n := by
          change 2 * (s : ℝ) / n = ((1 : ℕ) + (2 * (s : ℝ) - 1)) / n
          push_cast; ring
        rw [h_eq_u] at hs_BV
        have h_bot := hc.bottom 1 (by omega) u
        change h (GM11.circlePt (((1 : ℕ) + (u : ℝ)) / n), 0) = ε 1 u at h_bot
        rw [h_bot] at hs_BV
        have hu_a1 : ε 1 u ∈ a 1 := hc.image_Ioo 1 ▸ ⟨u, hu_Ioo, rfl⟩
        exact ((hc.edge 1).2.1 hu_a1).2 hs_BV
    · have : (0 : I) = 1 := congrArg Prod.snd (mem_singleton_iff.mp heq)
      exact zero_ne_one this
  let τ_real : I → ℝ := fun s =>
    min ((s : ℝ) * (1 - (s : ℝ))) (Metric.infDist (s, (0 : I)) K_bad / 2)
  have hτ_mem : ∀ s : I, τ_real s ∈ Icc (0 : ℝ) 1 := by
    intro s
    refine ⟨le_min (mul_nonneg s.2.1 (sub_nonneg.mpr s.2.2))
      (div_nonneg Metric.infDist_nonneg (by norm_num)), ?_⟩
    refine (min_le_left _ _).trans ?_
    nlinarith [s.2.1, s.2.2]
  let τ : I → I := fun s => ⟨τ_real s, (hτ_mem s).1, (hτ_mem s).2⟩
  have hτ_cont : Continuous τ := by
    refine Continuous.subtype_mk (Continuous.min ?_ ?_) _
    · exact continuous_subtype_val.mul (continuous_const.sub continuous_subtype_val)
    · exact (Metric.continuous_infDist_pt K_bad |>.comp
        (continuous_id.prodMk continuous_const)).div_const 2
  have hτ0 : τ 0 = 0 := by
    ext
    exact le_antisymm ((min_le_left _ _).trans (by simp)) (hτ_mem 0).1
  have hτ1 : τ 1 = 0 := by
    ext
    exact le_antisymm ((min_le_left _ _).trans (by simp)) (hτ_mem 1).1
  have hτ_pos : ∀ s ∈ Ioo (0 : I) 1, 0 < τ s := by
    intro s hs
    change (0 : ℝ) < min ((s : ℝ) * (1 - (s : ℝ))) (Metric.infDist (s, (0 : I)) K_bad / 2)
    have hs0 : (0 : ℝ) < s := hs.1
    have hs1 : (s : ℝ) < 1 := hs.2
    have hinf_pos : 0 < Metric.infDist (s, (0 : I)) K_bad :=
      (hK_bad_closed.notMem_iff_infDist_pos hK_bad_ne).mp (hnot_Kbad s hs)
    exact lt_min (mul_pos hs0 (sub_pos.mpr hs1)) (half_pos hinf_pos)
  have hτ_le_quarter : ∀ s : I, (τ s : ℝ) ≤ 1 / 4 := by
    intro s
    refine (min_le_left _ _).trans ?_
    have : (s : ℝ) * (1 - (s : ℝ)) = 1 / 4 - ((s : ℝ) - 1 / 2) ^ 2 := by ring
    linarith [sq_nonneg ((s : ℝ) - 1 / 2)]
  have hτ_avoid : ∀ s ∈ Ioo (0 : I) 1, ∀ t ∈ Ioc (0 : I) (τ s),
      Φ (s, t) ∈ R_N ∧ Φ (s, t) ∉ D.U := by
    intro s hs t ht
    have ht_pos : 0 < halfT t := halfT_pos ht.1
    refine ⟨hc.mem_r _ ht_pos, fun hDU => ?_⟩
    have hmem_Kbad : ((s, t) : I × I) ∈ K_bad :=
      Or.inl (subset_closure ⟨ht.1, hDU⟩)
    have hdist_le : Metric.infDist (s, (0 : I)) K_bad ≤ dist (s, (0 : I)) (s, t) :=
      Metric.infDist_le_dist_of_mem hmem_Kbad
    have hdist_eq : dist ((s, (0 : I)) : I × I) (s, t) = (t : ℝ) := by
      change max (dist s s) (dist (0 : I) t) = (t : ℝ)
      rw [_root_.dist_self, max_eq_right _root_.dist_nonneg]
      change |(0 : ℝ) - (t : ℝ)| = (t : ℝ)
      rw [zero_sub, abs_neg, abs_of_nonneg t.2.1]
    have ht_le_half : (t : ℝ) ≤ Metric.infDist (s, (0 : I)) K_bad / 2 :=
      (show (t : ℝ) ≤ (τ s : ℝ) from ht.2).trans (min_le_right _ _)
    have hinf_pos : 0 < Metric.infDist (s, (0 : I)) K_bad :=
      (hK_bad_closed.notMem_iff_infDist_pos hK_bad_ne).mp (hnot_Kbad s hs)
    linarith
  have hΨ_inj_pos : ∀ p q : I × I, 0 < p.2 → 0 < q.2 → Φ p = Φ q → p = q := by
    intro p q hp hq heq
    have hp' : 0 < (Ψ p).2 := halfT_pos hp
    have hq' : 0 < (Ψ q).2 := halfT_pos hq
    have hΨ_eq : Ψ p = Ψ q := hc.injOn hp' hq' heq
    have h_snd : p.2 = q.2 := halfT_inj (congrArg Prod.snd hΨ_eq)
    have h_circ : GM11.circlePt (2 * (p.1 : ℝ) / n) = GM11.circlePt (2 * (q.1 : ℝ) / n) :=
      congrArg Prod.fst hΨ_eq
    have hp_Ico : 2 * (p.1 : ℝ) / n ∈ Ico (0 : ℝ) (0 + 1) := by
      refine ⟨div_nonneg (mul_nonneg (by norm_num) p.1.2.1) hn_pos.le, ?_⟩
      rw [zero_add, div_lt_iff₀ hn_pos]
      have : (p.1 : ℝ) ≤ 1 := p.1.2.2
      have : (4 : ℝ) ≤ n := by exact_mod_cast hn4
      linarith
    have hq_Ico : 2 * (q.1 : ℝ) / n ∈ Ico (0 : ℝ) (0 + 1) := by
      refine ⟨div_nonneg (mul_nonneg (by norm_num) q.1.2.1) hn_pos.le, ?_⟩
      rw [zero_add, div_lt_iff₀ hn_pos]
      have : (q.1 : ℝ) ≤ 1 := q.1.2.2
      have : (4 : ℝ) ≤ n := by exact_mod_cast hn4
      linarith
    have h_div_eq := GM11.circlePt_injOn hp_Ico hq_Ico h_circ
    have h_fst : p.1 = q.1 := by
      ext
      have : 2 * (p.1 : ℝ) = 2 * (q.1 : ℝ) := (div_left_inj' hn_pos.ne').mp h_div_eq
      linarith
    exact Prod.ext h_fst h_snd
  let γ : I → S := fun s => Φ (s, τ s)
  have hγ_cont : Continuous γ := hΦ_cont.comp (continuous_id.prodMk hτ_cont)
  have hγ0 : γ 0 = v 0 := (congrArg (fun t => Φ (0, t)) hτ0).trans hΦ00
  have hγ1 : γ 1 = v 2 := (congrArg (fun t => Φ (1, t)) hτ1).trans hΦ10
  have hγ_inj : Function.Injective γ := by
    intro s₁ s₂ heq
    have hs_cases : ∀ s : I, s = 0 ∨ s = 1 ∨ s ∈ Ioo (0 : I) 1 := by
      intro s
      rcases eq_or_lt_of_le (unitInterval.nonneg s) with h0 | h0
      · exact Or.inl (Subtype.ext h0.symm)
      · rcases eq_or_lt_of_le (unitInterval.le_one s) with h1 | h1
        · exact Or.inr (Or.inl (Subtype.ext h1))
        · exact Or.inr (Or.inr ⟨h0, h1⟩)
    rcases hs_cases s₁ with rfl | rfl | hs₁ <;> rcases hs_cases s₂ with rfl | rfl | hs₂
    · rfl
    · exact (hv02 (hγ0.symm.trans (heq.trans hγ1))).elim
    · exfalso
      have h₂_RN : γ s₂ ∈ R_N := (hτ_avoid s₂ hs₂ (τ s₂) ⟨hτ_pos s₂ hs₂, le_rfl⟩).1
      rw [← heq, hγ0] at h₂_RN
      exact GM11.region_subset hRN h₂_RN (N.V_subset_U (hBs.1 (hc.vertex 0)))
    · exact (hv02 (hγ1.symm.trans (heq.trans hγ0)).symm).elim
    · rfl
    · exfalso
      have h₂_RN : γ s₂ ∈ R_N := (hτ_avoid s₂ hs₂ (τ s₂) ⟨hτ_pos s₂ hs₂, le_rfl⟩).1
      rw [← heq, hγ1] at h₂_RN
      exact GM11.region_subset hRN h₂_RN (N.V_subset_U (hBs.1 (hc.vertex 2)))
    · exfalso
      have h₁_RN : γ s₁ ∈ R_N := (hτ_avoid s₁ hs₁ (τ s₁) ⟨hτ_pos s₁ hs₁, le_rfl⟩).1
      rw [heq, hγ0] at h₁_RN
      exact GM11.region_subset hRN h₁_RN (N.V_subset_U (hBs.1 (hc.vertex 0)))
    · exfalso
      have h₁_RN : γ s₁ ∈ R_N := (hτ_avoid s₁ hs₁ (τ s₁) ⟨hτ_pos s₁ hs₁, le_rfl⟩).1
      rw [heq, hγ1] at h₁_RN
      exact GM11.region_subset hRN h₁_RN (N.V_subset_U (hBs.1 (hc.vertex 2)))
    · exact congrArg Prod.fst (hΨ_inj_pos _ _ (hτ_pos s₁ hs₁) (hτ_pos s₂ hs₂) heq)
  let K : Set S := range γ
  have hK : IsLineWithEnds K (v 0) (v 2) := by
    have ha_arc : IsArcMap γ := ⟨hγ_cont, hγ_inj⟩
    rw [← hγ0, ← hγ1]
    exact ha_arc.isLineWithEnds
  have hK_sdiff : K \ {v 0, v 2} = γ '' Ioo (0 : I) 1 := by
    ext y
    simp only [K, Set.mem_sdiff, mem_range, mem_insert_iff, mem_singleton_iff, mem_image, mem_Ioo]
    constructor
    · rintro ⟨⟨s, rfl⟩, hnot⟩
      refine ⟨s, ⟨?_, ?_⟩, rfl⟩
      · exact unitInterval.pos_iff_ne_zero.mpr fun h0 => hnot (Or.inl (h0 ▸ hγ0))
      · exact unitInterval.lt_one_iff_ne_one.mpr fun h1 => hnot (Or.inr (h1 ▸ hγ1))
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨s, rfl⟩, ?_⟩
      rintro (h0 | h1)
      · exact hs.1.ne' (hγ_inj (h0.trans hγ0.symm))
      · exact hs.2.ne (hγ_inj (h1.trans hγ1.symm))
  let D_under : Set (I × I) := {p : I × I | p.1 ∈ Ioo (0 : I) 1 ∧ p.2 ∈ Ioc (0 : I) (τ p.1)}
  let U_under : Set S := Φ '' D_under
  have hD_under_pre : IsPreconnected D_under := by
    let C_curve : Set (I × I) := (fun s : I => (s, τ s)) '' Ioo (0 : I) 1
    have hC_pre : IsPreconnected C_curve :=
      isPreconnected_Ioo.image _ (continuous_id.prodMk hτ_cont).continuousOn
    have hC_sub : C_curve ⊆ D_under := by
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨hs, hτ_pos s hs, le_rfl⟩
    refine isPreconnected_of_forall_pair ?_
    rintro p₁ ⟨hs₁, ht₁⟩ p₂ ⟨hs₂, ht₂⟩
    let S₁ : Set (I × I) := (fun t : I => (p₁.1, t)) '' Icc p₁.2 (τ p₁.1)
    let S₂ : Set (I × I) := (fun t : I => (p₂.1, t)) '' Icc p₂.2 (τ p₂.1)
    have hS₁_pre : IsPreconnected S₁ :=
      isPreconnected_Icc.image _ (continuous_const.prodMk continuous_id).continuousOn
    have hS₂_pre : IsPreconnected S₂ :=
      isPreconnected_Icc.image _ (continuous_const.prodMk continuous_id).continuousOn
    have hS₁_sub : S₁ ⊆ D_under := by
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨hs₁, ht₁.1.trans_le ht.1, ht.2⟩
    have hS₂_sub : S₂ ⊆ D_under := by
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨hs₂, ht₂.1.trans_le ht.1, ht.2⟩
    have hSC₁ : (S₁ ∩ C_curve).Nonempty :=
      ⟨(p₁.1, τ p₁.1), ⟨τ p₁.1, ⟨ht₁.2, le_rfl⟩, rfl⟩, ⟨p₁.1, hs₁, rfl⟩⟩
    have hSC₂ : ((S₁ ∪ C_curve) ∩ S₂).Nonempty :=
      ⟨(p₂.1, τ p₂.1), Or.inr ⟨p₂.1, hs₂, rfl⟩, ⟨τ p₂.1, ⟨ht₂.2, le_rfl⟩, rfl⟩⟩
    exact ⟨S₁ ∪ C_curve ∪ S₂, union_subset (union_subset hS₁_sub hC_sub) hS₂_sub,
      Or.inl (Or.inl ⟨p₁.2, ⟨le_rfl, ht₁.2⟩, rfl⟩),
      Or.inr ⟨p₂.2, ⟨le_rfl, ht₂.2⟩, rfl⟩,
      (hS₁_pre.union' hSC₁ hC_pre).union' hSC₂ hS₂_pre⟩
  have hU_under_pre : IsPreconnected U_under :=
    hD_under_pre.image Φ hΦ_cont.continuousOn
  have hU_under_sub : U_under ⊆ R_N ∧ Disjoint U_under D.U := by
    refine ⟨?_, Set.disjoint_left.mpr ?_⟩
    · rintro _ ⟨p, ⟨hs, ht⟩, rfl⟩
      exact (hτ_avoid p.1 hs p.2 ht).1
    · rintro _ ⟨p, ⟨hs, ht⟩, rfl⟩ hDU
      exact (hτ_avoid p.1 hs p.2 ht).2 hDU
  let s_half : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have hs_half_Ioo : s_half ∈ Ioo (0 : I) 1 :=
    ⟨Subtype.mk_lt_mk.mpr (by norm_num), Subtype.mk_lt_mk.mpr (by norm_num)⟩
  have hγ_half_U : γ s_half ∈ U_under :=
    ⟨(s_half, τ s_half), ⟨hs_half_Ioo, hτ_pos s_half hs_half_Ioo, le_rfl⟩, rfl⟩
  have hγ_half_not_DU : γ s_half ∉ D.U :=
    Set.disjoint_left.mp hU_under_sub.2 hγ_half_U
  obtain ⟨q, hq, hγ_half_q⟩ := GM11.exists_region_of_notMem hγ_half_not_DU
  have hU_under_q : U_under ⊆ q :=
    GM11.subset_region hq hU_under_pre hU_under_sub.2 hγ_half_U hγ_half_q
  have hKq : K \ {v 0, v 2} ⊆ q := by
    rw [hK_sdiff]
    rintro _ ⟨s, hs, rfl⟩
    exact hU_under_q ⟨(s, τ s), ⟨hs, hτ_pos s hs, le_rfl⟩, rfl⟩
  have hq_RN : q ⊆ R_N :=
    GM11.subset_region hRN (GM11.region_isPreconnected hq)
      (Set.disjoint_left.mpr fun z hzq hzNU => GM11.region_subset hq hzq (hNs.U_subset hzNU))
      hγ_half_q (hU_under_sub.1 hγ_half_U)
  have hq_int : ∀ hd' : 0 < d', q ⊆ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩) := by
    intro hd'
    let j_last : Fin d' := ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩
    have hv₀_int : v 0 ∈ interior (Δ j_last) :=
      hShell.innerDraw_U_subset_interior hd' (N.V_subset_U (hBs.1 (hc.vertex 0)))
    have hv₀_clq : v 0 ∈ closure q := by
      rw [← hγ0]
      have hsub : γ '' Ioo (0 : I) 1 ⊆ q := hK_sdiff ▸ hKq
      have h0_cl : (0 : I) ∈ closure (Ioo (0 : I) 1) := by
        rw [closure_Ioo (zero_ne_one' I)]
        exact ⟨le_rfl, zero_le_one⟩
      exact closure_mono hsub (image_closure_subset_closure_image hγ_cont ⟨0, h0_cl, rfl⟩)
    obtain ⟨w₀, hw₀_int, hw₀_q⟩ := mem_closure_iff.mp hv₀_clq _ isOpen_interior hv₀_int
    have hq_cov : q ⊆ interior (Δ j_last) ∪ (Δ j_last)ᶜ := by
      intro z hzq
      by_cases hzΔ : z ∈ Δ j_last
      · refine Or.inl ?_
        have hz_not_bd : z ∉ discBd (Δ j_last) := fun hbd => by
          rw [hShell.discBd_eq j_last] at hbd
          exact GM11.region_subset hq hzq ((hShell.isSubdrawing j_last).U_subset hbd)
        rw [← discInt_eq_interior_of_isClosedDisc hS (hShell.isClosedDisc j_last)]
        exact ⟨hzΔ, hz_not_bd⟩
      · exact Or.inr hzΔ
    have hdis : Disjoint (interior (Δ j_last)) (Δ j_last)ᶜ :=
      Set.disjoint_left.mpr fun z hz hnot => hnot (interior_subset hz)
    rcases (GM11.region_isPreconnected hq).subset_or_subset
        isOpen_interior (hShell.isClosedDisc j_last).isClosed.isOpen_compl hdis hq_cov with h₁ | h₂
    · exact h₁
    · exact (h₂ hw₀_q (interior_subset hw₀_int)).elim
  have hv₀_D : v 0 ∈ D.V := hNs.1 (hBs.1 (hc.vertex 0))
  have hv₂_D : v 2 ∈ D.V := hNs.1 (hBs.1 (hc.vertex 2))
  let D' := D.glue (GM11.lineDrawing hK hv02)
    (lineDrawing_meet_of_subset_region hq hv₀_D hv₂_D hK hv02 hKq)
  let N' := innerDraw D' d' C
  obtain ⟨hN's, hN'V, hN'E, _⟩ := innerDraw_spec D' d' C
  have hV_sub_L : (GM11.lineDrawing hK hv02).V ⊆ D.V := by
    rintro z (rfl | rfl)
    · exact hv₀_D
    · exact hv₂_D
  have hD'V : D'.V = D.V := union_eq_left.mpr hV_sub_L
  have hN'V_eq : N'.V = N.V := by rw [hN'V, hNV, hD'V]
  let e_new : Set S := K \ {v 0, v 2}
  have hcl_enew : closure e_new = K := GM11.closure_sdiff_pair hK
  have hD'E : D'.E = insert e_new D.E := by
    change (D.glue (GM11.lineDrawing hK hv02) _).E = insert e_new D.E
    rw [Drawing.glue_E, GM11.lineDrawing_E, union_singleton]
  have hcap_enew : closure e_new ∩ D'.V = {v 0, v 2} := by
    rw [hcl_enew, hD'V]
    refine Subset.antisymm (fun z ⟨hzK, hzV⟩ => ?_) ?_
    · by_contra hnot
      exact GM11.region_subset hq (hKq ⟨hzK, hnot⟩) (D.V_subset_U hzV)
    · rintro z (rfl | rfl)
      · exact ⟨⟨0, hγ0⟩, hv₀_D⟩
      · exact ⟨⟨1, hγ1⟩, hv₂_D⟩
  have hN'E_eq : N'.E = insert e_new N.E := by
    rw [hN'E, hNE, hD'E, hD'V]
    ext e
    simp only [mem_ofPred_eq, mem_insert_iff]
    constructor
    · rintro ⟨rfl | heD, hsub⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨heD, hsub⟩
    · rintro (rfl | ⟨heD, hsub⟩)
      · refine ⟨Or.inl rfl, ?_⟩
        rw [← hNV, ← hD'V, hcap_enew]
        rintro z (rfl | rfl)
        · exact hBs.1 (hc.vertex 0)
        · exact hBs.1 (hc.vertex 2)
      · exact ⟨Or.inr heD, hsub⟩
  have hN'U_e : N'.U = N.U ∪ e_new := by
    rw [N'.U_eq, N.U_eq, hN'V_eq, hN'E_eq, biUnion_insert, hcl_enew]
    refine Subset.antisymm ?_ ?_
    · rintro z (hzV | hzK | hzE)
      · exact Or.inl (Or.inl hzV)
      · by_cases hz02 : z ∈ ({v 0, v 2} : Set S)
        · rcases hz02 with rfl | rfl
          · exact Or.inl (Or.inl (hBs.1 (hc.vertex 0)))
          · exact Or.inl (Or.inl (hBs.1 (hc.vertex 2)))
        · exact Or.inr ⟨hzK, hz02⟩
      · exact Or.inl (Or.inr hzE)
    · rintro z ((hzV | hzE) | hze)
      · exact Or.inl hzV
      · exact Or.inr (Or.inr hzE)
      · exact Or.inr (Or.inl hze.1)
  let F_under : Set S := Φ '' {p : I × I | p.2 ≤ τ p.1}
  have hF_under_closed : IsClosed F_under := by
    refine ((isClosed_le (continuous_subtype_val.comp continuous_snd)
      (continuous_subtype_val.comp (hτ_cont.comp continuous_fst))).isCompact.image hΦ_cont).isClosed
  have hRN_inter_F : R_N ∩ F_under = U_under := by
    refine Subset.antisymm ?_ (subset_inter hU_under_sub.1
      (image_mono fun p hp => hp.2.2))
    rintro _ ⟨hRN_x, ⟨p, hp_le, rfl⟩⟩
    have hp2_pos : 0 < p.2 := by
      refine lt_of_le_of_ne (unitInterval.nonneg p.2) fun h0 => ?_
      have hp_fr : Φ p ∈ frontier R_N := by
        rw [← hc.range_bottom]
        refine ⟨GM11.circlePt (2 * (p.1 : ℝ) / n), ?_⟩
        change h (GM11.circlePt (2 * (p.1 : ℝ) / n), 0) = h (GM11.circlePt (2 * (p.1 : ℝ) / n), halfT p.2)
        rw [← h0, halfT_zero]
      rw [(GM11.region_isOpen hRN).frontier_eq] at hp_fr
      exact hp_fr.2 hRN_x
    have hp1_Ioo : p.1 ∈ Ioo (0 : I) 1 := by
      refine ⟨lt_of_le_of_ne (unitInterval.nonneg p.1) fun h0 => ?_,
        lt_of_le_of_ne (unitInterval.le_one p.1) fun h1 => ?_⟩
      · have : p.2 ≤ 0 := hτ0 ▸ (h0 ▸ hp_le)
        exact not_le_of_gt hp2_pos this
      · have : p.2 ≤ 0 := hτ1 ▸ (h1 ▸ hp_le)
        exact not_le_of_gt hp2_pos this
    exact ⟨p, ⟨hp1_Ioo, hp2_pos, hp_le⟩, rfl⟩
  let W_ext : Set S := R_N \ F_under
  have hW_ext_open : IsOpen W_ext := (GM11.region_isOpen hRN).sdiff hF_under_closed
  have he_new_sub_F : e_new ⊆ F_under := by
    rw [show e_new = K \ {v 0, v 2} from rfl, hK_sdiff]
    rintro _ ⟨s, _, rfl⟩
    exact ⟨(s, τ s), show τ s ≤ τ s from le_rfl, rfl⟩
  have hW_ext_not_N'U : W_ext ⊆ N'.Uᶜ := by
    rintro z ⟨hzRN, hzF⟩ hzN'
    rw [hN'U_e] at hzN'
    rcases hzN' with hzN | hze
    · exact GM11.region_subset hRN hzRN hzN
    · exact hzF (he_new_sub_F hze)
  let t_half : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have hF_lt_half : ∀ p : Circle × I, (t_half : ℝ) ≤ (p.2 : ℝ) → h p ∉ F_under := by
    rintro p hp ⟨q, hq_le, heq⟩
    have hp_pos : 0 < p.2 :=
      Subtype.coe_lt_coe.mp (lt_of_lt_of_le
        (show ((0 : I) : ℝ) < (t_half : ℝ) by rw [Set.Icc.coe_zero]; change (0 : ℝ) < 1 / 2; norm_num) hp)
    by_cases hq_pos : 0 < q.2
    · have hq'_pos : 0 < (Ψ q).2 := halfT_pos hq_pos
      have hp_eq := hc.injOn (x₁ := p) (x₂ := Ψ q) hp_pos hq'_pos heq.symm
      have hp2_eq : (p.2 : ℝ) = (q.2 : ℝ) / 2 :=
        (congrArg (fun x : Circle × I => (x.2 : ℝ)) hp_eq).trans (coe_halfT q.2)
      have hq2_le : (q.2 : ℝ) ≤ 1 / 4 :=
        (show (q.2 : ℝ) ≤ (τ q.1 : ℝ) from hq_le).trans (hτ_le_quarter q.1)
      have hp' : (1 : ℝ) / 2 ≤ (p.2 : ℝ) := hp
      rw [hp2_eq] at hp'
      linarith
    · have hq0 : q.2 = 0 := le_antisymm (not_lt.mp hq_pos) (unitInterval.nonneg q.2)
      have hΦ_fr : Φ q ∈ frontier R_N := by
        rw [← hc.range_bottom]
        exact ⟨GM11.circlePt (2 * (q.1 : ℝ) / n),
          congrArg h (Prod.ext rfl ((congrArg halfT hq0).trans halfT_zero).symm)⟩
      rw [(GM11.region_isOpen hRN).frontier_eq] at hΦ_fr
      exact hΦ_fr.2 (heq ▸ hc.mem_r p hp_pos)
  let y₀ : S := h (1, t_half)
  have hy₀_W : y₀ ∈ W_ext :=
    ⟨hc.mem_r (1, t_half) (Subtype.mk_lt_mk.mpr (by norm_num)),
     hF_lt_half (1, t_half) le_rfl⟩
  let C_mid : Set S := (fun z : Circle => h (z, t_half)) '' univ
  have hC_mid_pre : IsPreconnected C_mid :=
    isPreconnected_univ.image _ (h.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hC_mid_sub : C_mid ⊆ W_ext := by
    rintro _ ⟨z, -, rfl⟩
    exact ⟨hc.mem_r (z, t_half) (Subtype.mk_lt_mk.mpr (by norm_num)),
      hF_lt_half (z, t_half) le_rfl⟩
  have hy₀_Cmid : y₀ ∈ C_mid := ⟨1, mem_univ 1, rfl⟩
  let U_collar : Set S := R_N ∩ (R_Nᶜ ∪ h '' {p : Circle × I | p.2 < 1})
  have hU_collar_open : IsOpen U_collar := (GM11.region_isOpen hRN).inter hc.isOpen
  have hU_collar_eq : U_collar = h '' {p : Circle × I | 0 < p.2 ∧ p.2 < 1} := by
    ext x
    constructor
    · rintro ⟨hxRN, hx_or⟩
      rcases hx_or with hx_not | ⟨p, hp1, rfl⟩
      · exact (hx_not hxRN).elim
      · refine ⟨p, ⟨?_, hp1⟩, rfl⟩
        refine lt_of_le_of_ne (unitInterval.nonneg p.2) fun h0 => ?_
        have hfr : h p ∈ frontier R_N := by
          rw [← hc.range_bottom]
          exact ⟨p.1, congrArg h (Prod.ext rfl h0)⟩
        rw [(GM11.region_isOpen hRN).frontier_eq] at hfr
        exact hfr.2 hxRN
    · rintro ⟨p, ⟨hp0, hp1⟩, rfl⟩
      exact ⟨hc.mem_r p hp0, Or.inr ⟨p, hp1, rfl⟩⟩
  let U₁ : Set S := U_collar \ F_under
  have hU₁_sub_W : U₁ ⊆ W_ext := fun x ⟨hxU, hxF⟩ => ⟨hxU.1, hxF⟩
  have hC_mid_U₁ : C_mid ⊆ U₁ := by
    rintro _ ⟨z, -, rfl⟩
    refine ⟨?_, (hC_mid_sub ⟨z, mem_univ z, rfl⟩).2⟩
    rw [hU_collar_eq]
    exact ⟨(z, t_half), ⟨Subtype.mk_lt_mk.mpr (by norm_num),
      Subtype.mk_lt_mk.mpr (by norm_num)⟩, rfl⟩
  have hU₁_sub_comp : U₁ ⊆ connectedComponentIn W_ext y₀ := by
    intro x ⟨hxU, hxF⟩
    rw [hU_collar_eq] at hxU
    obtain ⟨⟨z, t₀⟩, ⟨ht₀_pos, ht₀_lt1⟩, rfl⟩ := hxU
    let seg : Set S := (fun t : I => h (z, t)) '' Icc (min t₀ t_half) (max t₀ t_half)
    have hseg_pre : IsPreconnected seg :=
      isPreconnected_Icc.image _ (h.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    have hseg_W : seg ⊆ W_ext := by
      rintro _ ⟨t, ht, rfl⟩
      have ht_pos : 0 < t := lt_of_lt_of_le (lt_min ht₀_pos (Subtype.mk_lt_mk.mpr (by norm_num))) ht.1
      refine ⟨hc.mem_r (z, t) ht_pos, ?_⟩
      intro hmem_F
      by_cases ht_ge : (t_half : ℝ) ≤ (t : ℝ)
      · exact hF_lt_half (z, t) ht_ge hmem_F
      · have ht₀_le_t : t₀ ≤ t := by
          have ht_lt : t < t_half := Subtype.coe_lt_coe.mp (not_le.mp ht_ge)
          exact (min_le_iff.mp ht.1).resolve_right (not_le.mpr ht_lt)
        obtain ⟨q, hq_le, heq⟩ := hmem_F
        have hq_pos : 0 < q.2 := by
          refine lt_of_le_of_ne (unitInterval.nonneg q.2) fun h0 => ?_
          have hfr : Φ q ∈ frontier R_N := by
            rw [← hc.range_bottom]
            exact ⟨GM11.circlePt (2 * (q.1 : ℝ) / n),
              congrArg h (Prod.ext rfl ((congrArg halfT h0.symm).trans halfT_zero).symm)⟩
          rw [(GM11.region_isOpen hRN).frontier_eq] at hfr
          exact hfr.2 (heq ▸ hc.mem_r (z, t) ht_pos)
        have h_eq := hc.injOn (x₁ := (z, t)) (x₂ := Ψ q) ht_pos (halfT_pos hq_pos) heq.symm
        have hz_eq : z = GM11.circlePt (2 * (q.1 : ℝ) / n) := congrArg Prod.fst h_eq
        have ht_eq : (t : ℝ) = (q.2 : ℝ) / 2 :=
          (congrArg (fun p : Circle × I => (p.2 : ℝ)) h_eq).trans (coe_halfT q.2)
        have ht₀_le_q : (t₀ : ℝ) ≤ (q.2 : ℝ) / 2 :=
          (Subtype.coe_le_coe.mpr ht₀_le_t).trans_eq ht_eq
        let q₂' : I := ⟨2 * (t₀ : ℝ), by linarith [t₀.2.1], by linarith [q.2.2.2]⟩
        have hq₂'_le : q₂' ≤ τ q.1 := by
          rw [← Subtype.coe_le_coe]
          have hq_τ : (q.2 : ℝ) ≤ (τ q.1 : ℝ) := Subtype.coe_le_coe.mpr hq_le
          change 2 * (t₀ : ℝ) ≤ (τ q.1 : ℝ)
          linarith
        have ht₀_half : halfT q₂' = t₀ :=
          Subtype.ext ((coe_halfT q₂').trans (by change 2 * (t₀ : ℝ) / 2 = t₀; ring))
        refine hxF ⟨(q.1, q₂'), hq₂'_le, ?_⟩
        change h (GM11.circlePt (2 * (q.1 : ℝ) / n), halfT q₂') = h (z, t₀)
        rw [← hz_eq, ht₀_half]
    have hx_seg : h (z, t₀) ∈ seg :=
      ⟨t₀, ⟨min_le_left _ _, le_max_left _ _⟩, rfl⟩
    have hz_half_seg : h (z, t_half) ∈ seg :=
      ⟨t_half, ⟨min_le_right _ _, le_max_right _ _⟩, rfl⟩
    have hz_half_comp : h (z, t_half) ∈ connectedComponentIn W_ext y₀ :=
      hC_mid_pre.subset_connectedComponentIn hy₀_Cmid hC_mid_sub ⟨z, mem_univ z, rfl⟩
    rw [connectedComponentIn_eq hz_half_comp]
    exact hseg_pre.subset_connectedComponentIn hz_half_seg hseg_W hx_seg
  have hW_ext_pre : IsPreconnected W_ext := by
    let C₀ := connectedComponentIn W_ext y₀
    have hC₀_open : IsOpen C₀ := hW_ext_open.connectedComponentIn
    have hC_other_open : IsOpen (W_ext \ C₀) := by
      have : W_ext \ C₀ = ⋃ x ∈ W_ext \ C₀, connectedComponentIn W_ext x := by
        ext z
        simp only [Set.mem_sdiff, mem_iUnion, exists_prop]
        constructor
        · intro hz
          exact ⟨z, hz, mem_connectedComponentIn hz.1⟩
        · rintro ⟨x, hx, hzx⟩
          refine ⟨connectedComponentIn_subset _ _ hzx, fun hzC₀ => hx.2 ?_⟩
          change x ∈ connectedComponentIn W_ext y₀
          rw [connectedComponentIn_eq hzC₀, ← connectedComponentIn_eq hzx]
          exact mem_connectedComponentIn hx.1
      rw [this]
      exact isOpen_biUnion fun x _ => hW_ext_open.connectedComponentIn
    have hRN_F_sub_U : R_N ∩ F_under ⊆ U_collar := by
      rw [hRN_inter_F, hU_collar_eq]
      rintro _ ⟨p, ⟨_, hp2_pos, _⟩, rfl⟩
      exact ⟨Ψ p, ⟨halfT_pos hp2_pos, halfT_lt_one p.2⟩, rfl⟩
    let O₁ : Set S := C₀ ∪ U_collar
    let O₂ : Set S := W_ext \ C₀
    have hO₁_open : IsOpen O₁ := hC₀_open.union hU_collar_open
    have hRN_cov : R_N ⊆ O₁ ∪ O₂ := by
      intro z hzRN
      by_cases hzF : z ∈ F_under
      · exact Or.inl (Or.inr (hRN_F_sub_U ⟨hzRN, hzF⟩))
      · by_cases hzC₀ : z ∈ C₀
        · exact Or.inl (Or.inl hzC₀)
        · exact Or.inr ⟨⟨hzRN, hzF⟩, hzC₀⟩
    have hO_disj : Disjoint O₁ O₂ := by
      rw [Set.disjoint_left]
      rintro z (hzC₀ | hzU) ⟨⟨_, hzF⟩, hz_not_C₀⟩
      · exact hz_not_C₀ hzC₀
      · exact hz_not_C₀ (hU₁_sub_comp ⟨hzU, hzF⟩)
    rcases (GM11.region_isPreconnected hRN).subset_or_subset hO₁_open hC_other_open hO_disj hRN_cov with h₁ | h₂
    · have hW_eq_C₀ : W_ext = C₀ := by
        refine Subset.antisymm (fun z hzW => ?_) (connectedComponentIn_subset _ _)
        rcases h₁ hzW.1 with hzC₀ | hzU
        · exact hzC₀
        · exact hU₁_sub_comp ⟨hzU, hzW.2⟩
      rw [hW_eq_C₀]
      exact isPreconnected_connectedComponentIn
    · exfalso
      exact (h₂ hy₀_W.1).2 (mem_connectedComponentIn hy₀_W)
  obtain ⟨R_N', hRN', hy₀_RN'⟩ := GM11.exists_region_of_notMem (hW_ext_not_N'U hy₀_W)
  have hW_sub_RN' : W_ext ⊆ R_N' :=
    GM11.subset_region hRN' hW_ext_pre
      (Set.disjoint_left.mpr fun z hzW hzN' => hW_ext_not_N'U hzW hzN')
      hy₀_W hy₀_RN'
  have hRN'_sub_RN : R_N' ⊆ R_N :=
    GM11.subset_region hRN (GM11.region_isPreconnected hRN')
      (Set.disjoint_left.mpr fun z hzRN' hzNU =>
        GM11.region_subset hRN' hzRN' (hN'U_e ▸ Or.inl hzNU))
      hy₀_RN' hy₀_W.1
  have hRN_sdiff_sub : R_N \ q ⊆ R_N' := by
    intro z ⟨hzRN, hzq⟩
    refine hW_sub_RN' ⟨hzRN, fun hzF => hzq ?_⟩
    exact hU_under_q (hRN_inter_F ▸ ⟨hzRN, hzF⟩)
  have harc_cl : ∀ θ ∈ Icc (2 / (n : ℝ)) 1, h (GM11.circlePt θ, 0) ∈ closure R_N' := by
    intro θ hθ
    have h_in_RN' : ∀ t ∈ Ioo (0 : I) t_half, h (GM11.circlePt θ, t) ∈ R_N' := by
      intro t ht
      refine hW_sub_RN' ⟨hc.mem_r _ ht.1, ?_⟩
      rintro ⟨p, hp_le, heq⟩
      have hp_pos : 0 < p.2 := by
        refine lt_of_le_of_ne (unitInterval.nonneg p.2) fun h0 => ?_
        have hfr : Φ p ∈ frontier R_N := by
          rw [← hc.range_bottom]
          exact ⟨GM11.circlePt (2 * (p.1 : ℝ) / n),
            congrArg h (Prod.ext rfl ((congrArg halfT h0.symm).trans halfT_zero).symm)⟩
        rw [(GM11.region_isOpen hRN).frontier_eq] at hfr
        exact hfr.2 (heq ▸ hc.mem_r _ ht.1)
      have h_eq := hc.injOn (x₁ := (GM11.circlePt θ, t)) (x₂ := Ψ p) ht.1 (halfT_pos hp_pos) heq.symm
      have h_circ : GM11.circlePt θ = GM11.circlePt (2 * (p.1 : ℝ) / n) :=
        congrArg Prod.fst h_eq
      have hp1_lt1 : p.1 < 1 := by
        refine lt_of_le_of_ne (unitInterval.le_one p.1) fun h1 => ?_
        have : p.2 ≤ 0 := hτ1 ▸ (h1 ▸ hp_le)
        exact not_le_of_gt hp_pos this
      have hp_lt_2n : 2 * (p.1 : ℝ) / n < 2 / n :=
        (div_lt_div_iff_of_pos_right hn_pos).mpr (by have : (p.1 : ℝ) < 1 := hp1_lt1; linarith)
      rcases eq_or_lt_of_le hθ.2 with rfl | hθ_lt1
      · have h1_eq : GM11.circlePt 1 = GM11.circlePt 0 := by
          simp [GM11.circlePt, Circle.exp_two_pi]
        rw [h1_eq] at h_circ
        have h0_Ico : (0 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := ⟨le_rfl, by norm_num⟩
        have hp_nn : 0 ≤ 2 * (p.1 : ℝ) / n :=
          div_nonneg (mul_nonneg (by norm_num) (unitInterval.nonneg p.1)) hn_pos.le
        have hp_Ico : 2 * (p.1 : ℝ) / n ∈ Ico (0 : ℝ) (0 + 1) := by
          refine ⟨hp_nn, ?_⟩
          have : (2 : ℝ) / n < 1 := (div_lt_iff₀ hn_pos).mpr (by
            have : (4 : ℝ) ≤ n := by exact_mod_cast hn4
            linarith)
          linarith
        have h_eq0 := GM11.circlePt_injOn h0_Ico hp_Ico h_circ
        have hp1_zero : p.1 = 0 := by
          ext
          change (p.1 : ℝ) = 0
          have : 2 * (p.1 : ℝ) = 0 := (div_eq_zero_iff.mp h_eq0.symm).resolve_right hn_pos.ne'
          linarith
        have : p.2 ≤ 0 := hτ0 ▸ (hp1_zero ▸ hp_le)
        exact not_le_of_gt hp_pos this
      · have hp_nn : 0 ≤ 2 * (p.1 : ℝ) / n :=
          div_nonneg (mul_nonneg (by norm_num) (unitInterval.nonneg p.1)) hn_pos.le
        have hθ_nn : 0 ≤ θ := le_trans (div_nonneg (by norm_num) hn_pos.le) hθ.1
        have hθ_Ico : θ ∈ Ico (0 : ℝ) (0 + 1) := ⟨hθ_nn, by linarith⟩
        have hp_Ico : 2 * (p.1 : ℝ) / n ∈ Ico (0 : ℝ) (0 + 1) :=
          ⟨hp_nn, hp_lt_2n.trans (hθ.1.trans_lt (by linarith))⟩
        have h_eq_θ := GM11.circlePt_injOn hθ_Ico hp_Ico h_circ
        linarith [hθ.1]
    have h0_cl : (0 : I) ∈ closure (Ioo (0 : I) t_half) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      refine ⟨⟨min (ε / 2) (1 / 4), ⟨by positivity, le_trans (min_le_right _ _) (by norm_num)⟩⟩,
        ⟨Subtype.mk_lt_mk.mpr (by positivity),
         Subtype.mk_lt_mk.mpr (lt_of_le_of_lt (min_le_right _ _) (by norm_num))⟩, ?_⟩
      change dist (0 : ℝ) (min (ε / 2) (1 / 4)) < ε
      rw [_root_.dist_comm, Real.dist_0_eq_abs, abs_of_pos (by positivity)]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hcont_ray : Continuous (fun t : I => h (GM11.circlePt θ, t)) :=
      h.continuous.comp (continuous_const.prodMk continuous_id)
    have himg_RN' : (fun t : I => h (GM11.circlePt θ, t)) '' Ioo (0 : I) t_half ⊆ R_N' := by
      rintro _ ⟨t, ht, rfl⟩
      exact h_in_RN' t ht
    exact closure_mono himg_RN'
      (image_closure_subset_closure_image hcont_ray ⟨0, h0_cl, rfl⟩)
  have hPV_sub : B.V ⊆ (perimDraw N' R_N').V := by
    obtain ⟨_, hB'V, _, _, _⟩ := perimDraw_spec hS hRN'
    rw [hB'V, hN'V_eq]
    obtain ⟨hBV_eq, _, _⟩ := perim_V_E_eq_of_isHubCollar hS hRN hc
    change (perimDraw N R_N).V ⊆ N.V ∩ closure R_N'
    rw [hBV_eq]
    rintro _ ⟨i, hi, rfl⟩
    have hi_lt : i < n := hi
    refine ⟨hBs.1 (hc.vertex i), ?_⟩
    have hvi_bot : ∀ k < n, v k = h (GM11.circlePt ((k : ℝ) / n), 0) := by
      intro k hk
      have := (hc.bottom k hk 0).trans (hc.ε_zero k)
      simpa [GM11.circlePt] using this.symm
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · interval_cases i
      · rw [hvi_bot 0 (by omega)]
        have h01 : GM11.circlePt (((0 : ℕ) : ℝ) / n) = GM11.circlePt 1 := by
          simp [GM11.circlePt, Circle.exp_two_pi]
        rw [h01]
        exact harc_cl 1 ⟨(div_le_iff₀ hn_pos).mpr (by
          have : (4 : ℝ) ≤ n := by exact_mod_cast hn4
          linarith), le_rfl⟩
      · rw [← hv_j₁, hvi_bot j₁ hj₁_lt]
        exact harc_cl ((j₁ : ℝ) / n)
          ⟨(div_le_div_iff_of_pos_right hn_pos).mpr (by
            have : (2 : ℝ) ≤ j₁ := by exact_mod_cast (by omega : 2 ≤ j₁)
            linarith),
           (div_le_iff₀ hn_pos).mpr (by
            have : (j₁ : ℝ) ≤ n := by exact_mod_cast hj₁_lt.le
            linarith)⟩
    · rw [hvi_bot i hi_lt]
      exact harc_cl ((i : ℝ) / n)
        ⟨(div_le_div_iff_of_pos_right hn_pos).mpr (by exact_mod_cast hi2),
         (div_le_iff₀ hn_pos).mpr (by
          have : (i : ℝ) ≤ n := by exact_mod_cast hi_lt.le
          linarith)⟩
  exact ⟨K, q, hK, hq, hKq, hq_RN, hq_int, R_N', hRN', hRN'_sub_RN, hRN_sdiff_sub, hPV_sub⟩

end HubCollarPerim

end GraphMinor.GM03
