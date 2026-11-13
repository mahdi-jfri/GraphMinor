module

public import GraphMinor.GM08.Section9
import GraphMinor.GM08.Section8Sleeve
import GraphMinor.GM09.Basic
import GraphMinor.GM07.CuffTree
import GraphMinor.GM22.Section2Forest
import GraphMinor.GM16.DrawingGraphPaths
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Counting vertices and edges in a sleeve

The last step of VIII (9.1), page 270, compares cyclomatic numbers.
A path has one more vertex than edge, and a circuit has equal numbers.
In a sleeve the circuits are disjoint, the spokes are disjoint, and every
spoke meets every circuit in a path. Inclusion and exclusion therefore
counts the vertices and edges of their union.
-/

public section

namespace GraphMinor.GM08

open Set Surface Graph
open scoped BigOperators

universe u v

private theorem ncard_set_mem_list {α : Type*} (l : List α) (h : l.Nodup) :
    ({x | x ∈ l} : Set α).ncard = l.length := by
  classical
  have heq : ({x | x ∈ l} : Set α) = (l.toFinset : Set α) := by ext x; simp
  rw [heq, Set.ncard_coe_finset, List.toFinset_card_of_nodup h]

private theorem length_edges {α β : Type*} {G : Graph α β} {a b : α}
    (W : GraphWalk G a b) : W.edges.length = W.length := by rfl

private theorem length_support {α β : Type*} {G : Graph α β} {a b : α}
    (W : GraphWalk G a b) : W.support.length = W.length + 1 := by
  induction W with
  | nil _ => rfl
  | cons _ _ ih =>
    simp only [GraphWalk.support, GraphWalk.length, GraphWalk.edges, List.length_cons] at *
    omega

/-- A drawing path has one more vertex than edge. -/
theorem card_vertices_eq_card_edges_add_one_of_path {S : Type u} [TopologicalSpace S]
    {P : Drawing S} {a b : S} (hP : P.IsPathBetween a b) : P.V.ncard = P.E.ncard + 1 := by
  obtain ⟨W, hW, hV, hE⟩ := hP
  rw [hV, hE, ncard_set_mem_list _ hW, ncard_set_mem_list _ hW.edges_nodup,
    length_support, length_edges]

/-- A drawing circuit has as many vertices as edges, including for a loop. -/
theorem card_vertices_eq_card_edges_of_circuit {S : Type u} [TopologicalSpace S]
    {C : Drawing S} (hC : C.IsCircuit) : C.V.ncard = C.E.ncard := by
  obtain ⟨u, W, hW, hpos, hV, hE⟩ := hC
  cases W with
  | nil _ => exact False.elim ((Nat.not_lt_zero _) hpos)
  | @cons u v _ e hl rest =>
    have hV' : C.V = {x | x ∈ rest.support} := by
      rw [hV]
      ext x
      simp only [Set.mem_ofPred_eq, GraphWalk.support, List.mem_cons]
      constructor
      · rintro (rfl | hx)
        · exact rest.end_mem_support
        · exact hx
      · exact Or.inr
    have hrest : rest.support.Nodup := hW.1
    rw [hV', hE, ncard_set_mem_list _ hrest, ncard_set_mem_list _ hW.2,
      length_support, length_edges]
    rfl

/-- Count a union of two finite families, each disjoint within itself.
Only intersections between the two families have to be subtracted. -/
theorem ncard_union_two_disjoint_families {α ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → Set α) (B : κ → Set α) (hA : ∀ i, (A i).Finite) (hB : ∀ j, (B j).Finite)
    (hdA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hdB : Pairwise (fun i j => Disjoint (B i) (B j))) :
    ((⋃ i, A i) ∪ ⋃ j, B j).ncard + ∑ i, ∑ j, (A i ∩ B j).ncard =
      (∑ i, (A i).ncard) + ∑ j, (B j).ncard := by
  classical
  let C : ι × κ → Set α := fun p => A p.1 ∩ B p.2
  have hC : ∀ p, (C p).Finite := fun p => (hA p.1).inter_of_left _
  have hdC : Pairwise (fun p q => Disjoint (C p) (C q)) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hpq
    by_cases hii : i = i'
    · subst i'
      have hjj : j ≠ j' := fun h => hpq (Prod.ext rfl h)
      exact (hdB hjj).mono inter_subset_right inter_subset_right
    · exact (hdA hii).mono inter_subset_left inter_subset_left
  have hinter : (⋃ i, A i) ∩ (⋃ j, B j) = ⋃ p, C p := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion, C]
    constructor
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      exact ⟨(i, j), hi, hj⟩
    · rintro ⟨⟨i, j⟩, hi, hj⟩
      exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  have hc := Set.ncard_union_add_ncard_inter (⋃ i, A i) (⋃ j, B j)
    (Set.finite_iUnion hA) (Set.finite_iUnion hB)
  rw [hinter, Set.ncard_iUnion_of_finite hA hdA, Set.ncard_iUnion_of_finite hB hdB,
    Set.ncard_iUnion_of_finite hC hdC] at hc
  simpa only [finsum_eq_sum_of_fintype, Fintype.sum_prod_type, C] using hc

/-- Every nonempty subdrawing of a path has at least one more vertex than edge.
It is a forest because a path contains no circle. This bounds the intersections
of radial paths and nest circuits in the cyclomatic-number argument of (9.1). -/
theorem card_edges_add_one_le_card_vertices_of_subdrawing_path
    {S : Type u} [TopologicalSpace S] [T2Space S] {P Q : Drawing S}
    {a b : S} (hP : P.IsPathBetween a b) (hQ : Q.IsSubdrawing P) (hne : Q.V.Nonempty) :
    Q.E.ncard + 1 ≤ Q.V.ncard := by
  have hforest : IsGraphForest Q.toGraph := GM07.isForest_of_noOArc fun J hJ hsub =>
    GM07.no_oArc_of_path hP hJ (hsub.trans hQ.U_subset)
  by_cases hE : Q.E.Nonempty
  · exact (GM22.ncard_edgeSet_le_ncard_vertexSet_of_isGraphForest
      Q.finite_V Q.finite_edges hforest).2 hE
  · have hE0 : Q.E = ∅ := Set.not_nonempty_iff_eq_empty.mp hE
    rw [hE0, Set.ncard_empty, Nat.zero_add]
    exact Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos Q.finite_V).mpr hne).ne'

/-- A nonempty intersection of a radial path and a circuit contributes at least
one more vertex than edge to inclusion and exclusion. -/
theorem card_edges_inter_add_one_le_card_vertices_inter_of_path
    {S : Type u} [TopologicalSpace S] [T2Space S] {D P C : Drawing S}
    (hPD : P.IsSubdrawing D) (hCD : C.IsSubdrawing D) {a b : S}
    (hP : P.IsPathBetween a b) (hne : (P.V ∩ C.V).Nonempty) :
    (P.E ∩ C.E).ncard + 1 ≤ (P.V ∩ C.V).ncard := by
  have hQ := card_edges_add_one_le_card_vertices_of_subdrawing_path hP
    (GM09.PlanarNests.Drawing.inf_isSubdrawing_left hPD hCD)
    ((GM09.PlanarNests.Drawing.inf_V hPD hCD).symm ▸ hne)
  rwa [GM09.PlanarNests.Drawing.inf_E hPD, GM09.PlanarNests.Drawing.inf_V hPD hCD] at hQ

private theorem disjoint_edges_of_disjoint_points {S : Type u} [TopologicalSpace S]
    {A B : Drawing S} (h : Disjoint A.U B.U) : Disjoint A.E B.E := by
  apply Set.disjoint_left.mpr
  intro e heA heB
  obtain ⟨x, hx⟩ := heA.1
  exact Set.disjoint_left.mp h (heA.2.1 hx).1 (heB.2.1 hx).1

/-- The vertex and edge count of a sleeve in VIII (9.1), page 270.
If it has `m` spokes and `l = ceil(m/2)` circuits, then `E + m = V + m*l`.
This follows by counting the path intersections once on each side. -/
theorem IsSleeve.card_edges_add_spokes {S : Type u} [TopologicalSpace S]
    {D Γ : Drawing S} {Δ F : Set S} (hΔ : IsClosedDisc Δ) (h : IsSleeve D Δ F Γ) :
    Γ.E.ncard + (D.V ∩ F).ncard =
      Γ.V.ncard + (D.V ∩ F).ncard * (((D.V ∩ F).ncard + 1) / 2) := by
  classical
  obtain ⟨-, -, -, -, sd, hV, hE⟩ := h
  have hCV : Pairwise (fun j j' => Disjoint (sd.circuitDraw j).V (sd.circuitDraw j').V) := by
    intro j j' hjj'
    apply Set.disjoint_left.mpr
    intro x hx hx'
    exact Set.disjoint_left.mp (sd.nest.pairwise_disjoint_circuits hΔ hjj')
      ((sd.isCircuit_draw j).2.2 ▸ (sd.circuitDraw j).V_subset_U hx)
      ((sd.isCircuit_draw j').2.2 ▸ (sd.circuitDraw j').V_subset_U hx')
  have hCE : Pairwise (fun j j' => Disjoint (sd.circuitDraw j).E (sd.circuitDraw j').E) := by
    intro j j' hjj'
    apply disjoint_edges_of_disjoint_points
    rw [(sd.isCircuit_draw j).2.2, (sd.isCircuit_draw j').2.2]
    exact sd.nest.pairwise_disjoint_circuits hΔ hjj'
  have hsubP : ∀ i, (sd.spoke i).IsSubdrawing D := by
    intro i
    obtain ⟨-, -, -, hsub, -⟩ := sd.isPath_spoke i
    exact hsub
  have hPE : Pairwise (fun i i' => Disjoint (sd.spoke i).E (sd.spoke i').E) :=
    fun i i' hii' => disjoint_edges_of_disjoint_points
      (disjoint_U_of_disjoint_V_subdrawing (hsubP i) (hsubP i') (sd.pairwise_disjoint_spokes hii'))
  have hcountV := ncard_union_two_disjoint_families
    (fun j => (sd.circuitDraw j).V) (fun i => (sd.spoke i).V)
    (fun j => (sd.circuitDraw j).finite_V) (fun i => (sd.spoke i).finite_V)
    hCV sd.pairwise_disjoint_spokes
  have hcountE := ncard_union_two_disjoint_families
    (fun j => (sd.circuitDraw j).E) (fun i => (sd.spoke i).E)
    (fun j => (sd.circuitDraw j).finite_edges) (fun i => (sd.spoke i).finite_edges) hCE hPE
  rw [← hV] at hcountV
  rw [← hE] at hcountE
  have hcircs : ∀ j, (sd.circuitDraw j).V.ncard = (sd.circuitDraw j).E.ncard :=
    fun j => card_vertices_eq_card_edges_of_circuit (sd.isCircuit_draw j).2.1
  have hspokes : ∀ i, (sd.spoke i).V.ncard = (sd.spoke i).E.ncard + 1 := by
    intro i
    obtain ⟨-, a, b, -, -, -, hp, -⟩ := sd.isPath_spoke i
    exact card_vertices_eq_card_edges_add_one_of_path hp
  have hinters : ∀ j i,
      ((sd.circuitDraw j).V ∩ (sd.spoke i).V).ncard =
        ((sd.circuitDraw j).E ∩ (sd.spoke i).E).ncard + 1 := by
    intro j i
    obtain ⟨Q, a, b, -, hQV, hQE, hp⟩ := sd.inter_isPath i j
    have hc := card_vertices_eq_card_edges_add_one_of_path hp
    rw [hQV, hQE] at hc
    simpa only [Set.inter_comm] using hc
  simp_rw [hcircs, hspokes, hinters] at hcountV
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at hcountV
  rw [Nat.mul_comm (((D.V ∩ F).ncard + 1) / 2) (D.V ∩ F).ncard] at hcountV
  omega

/-- The lower vertex/edge count for a union of nest circuits and radial paths
in VIII (9.1). Each radial path meets every circuit, so every intersection
is a nonempty forest and contributes at least one to the count. -/
theorem card_edges_add_paths_ge_of_circuit_path_union
    {S : Type u} [TopologicalSpace S] [T2Space S] {D H : Drawing S} {r s : ℕ}
    (C : Fin s → Drawing S) (P : Fin r → Drawing S)
    (hCD : ∀ j, (C j).IsSubdrawing D) (hPD : ∀ i, (P i).IsSubdrawing D)
    (hC : ∀ j, (C j).IsCircuit) (hP : ∀ i, ∃ a b, (P i).IsPathBetween a b)
    (hCV : Pairwise (fun j j' => Disjoint (C j).V (C j').V))
    (hPV : Pairwise (fun i i' => Disjoint (P i).V (P i').V))
    (hmeet : ∀ j i, ((C j).V ∩ (P i).V).Nonempty)
    (hV : H.V = (⋃ j, (C j).V) ∪ ⋃ i, (P i).V)
    (hE : H.E = (⋃ j, (C j).E) ∪ ⋃ i, (P i).E) :
    H.V.ncard + r * s ≤ H.E.ncard + r := by
  classical
  have hCE : Pairwise (fun j j' => Disjoint (C j).E (C j').E) :=
    fun j j' hjj' => disjoint_edges_of_disjoint_points
      (disjoint_U_of_disjoint_V_subdrawing (hCD j) (hCD j') (hCV hjj'))
  have hPE : Pairwise (fun i i' => Disjoint (P i).E (P i').E) :=
    fun i i' hii' => disjoint_edges_of_disjoint_points
      (disjoint_U_of_disjoint_V_subdrawing (hPD i) (hPD i') (hPV hii'))
  have hcountV := ncard_union_two_disjoint_families (fun j => (C j).V) (fun i => (P i).V)
    (fun j => (C j).finite_V) (fun i => (P i).finite_V) hCV hPV
  have hcountE := ncard_union_two_disjoint_families (fun j => (C j).E) (fun i => (P i).E)
    (fun j => (C j).finite_edges) (fun i => (P i).finite_edges) hCE hPE
  rw [← hV] at hcountV
  rw [← hE] at hcountE
  have hcircs : ∀ j, (C j).V.ncard = (C j).E.ncard :=
    fun j => card_vertices_eq_card_edges_of_circuit (hC j)
  have hpaths : ∀ i, (P i).V.ncard = (P i).E.ncard + 1 := by
    intro i
    obtain ⟨a, b, hp⟩ := hP i
    exact card_vertices_eq_card_edges_add_one_of_path hp
  have hinter : ∀ j i,
      ((C j).E ∩ (P i).E).ncard + 1 ≤ ((C j).V ∩ (P i).V).ncard := by
    intro j i
    obtain ⟨a, b, hp⟩ := hP i
    have hle := card_edges_inter_add_one_le_card_vertices_inter_of_path
      (hPD i) (hCD j) hp (Set.inter_comm (P i).V (C j).V ▸ hmeet j i)
    simpa only [Set.inter_comm] using hle
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun j _ =>
    Finset.sum_le_sum (s := Finset.univ) fun i _ => hinter j i
  simp_rw [hcircs, hpaths] at hcountV
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at hcountV hsum
  rw [Nat.mul_comm s r] at hsum
  omega

end GraphMinor.GM08
