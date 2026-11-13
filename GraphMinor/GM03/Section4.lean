module

public import GraphMinor.GM03.Defs
public import GraphMinor.GM03.Section2a
public import GraphMinor.GM03.Section2
public import GraphMinor.GM03.Section3a
public import GraphMinor.GM09.PlanarNests
import GraphMinor.GM03.Section4e
import GraphMinor.GM03.Section4f

/-!
# Graph Minors III, Section 4: The Production of Cylinders ((4.1)–(4.5))

This file formalizes Section 4 ("The Production of Cylinders", pages 59–62) of
N. Robertson and P. D. Seymour, *Graph Minors. III. Planar Tree-Width*,
J. Combin. Theory Ser. B **36** (1984), 49–64:
- `(4.1)` (`theorem_4_1`, pages 60–61): if $M$ has a nested sequence $C_1, \dots, C_s$ of circuits
  and $G$ has $r$ vertex-disjoint paths between $V(C_1)$ and $V(C_s)$, then $M$ majors the
  $r \times s$ cylinder.
- `(4.2)` (`theorem_4_2`, page 61): given a nested sequence $C_1, \dots, C_s$ of circuits of $M$,
  either $M$ majors the $r \times s$ cylinder or some $X \subseteq V(G)$ with $|X| < r$ separates
  $V(C_1)$ and $V(C_s)$.
- `(4.3)` (`theorem_4_3`, page 61): if $M$ majors the $r \times s$ cylinder ($s > r'$), then either
  $M$ majors the $(r + 1) \times (s - r')$ cylinder or $G$ is expressible as the sleeve union of
  two planar graphs.
- `(4.4)` (`theorem_4_4`, pages 61–62): if $G$ is not expressible as a sleeve union of two planar
  graphs and $M$ does not major the $r \times s$ cylinder, then $G$ has radius
  $< k = \text{cylinderRadiusBound } r\ s$.
- `(4.5)` (`theorem_4_5`, page 62): if $G$ is a planar graph not expressible as the sleeve union of
  two planar graphs, then either $G$ has a minor isomorphic to the $r \times s$ cylinder or $G$ has
  tree-width at most $\text{cylinderTreeWidthBound } r\ s$.
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM09.PlanarNests
open GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM22

universe u v

variable {α : Type u} {β : Type v}

/-! ## Helper Lemmas for (4.1) -/

instance {G : Graph α β} (M : PlanarDrawing G) : T2Space M.S :=
  M.isClosedSurface.2.1

instance {G : Graph α β} (M : PlanarDrawing G) : ConnectedSpace M.S :=
  (GM11.IsSphere.isClosedSurface M.isSphere).2

instance {G : Graph α β} (M : PlanarDrawing G) : Nonempty M.S :=
  (GM11.IsSphere.isClosedSurface M.isSphere).2.toNonempty

theorem disjoint_image_of_injOn {X Y : Type*} {f : X → Y} {s t u : Set X}
    (hinj : InjOn f u) (hs : s ⊆ u) (ht : t ⊆ u) (hd : Disjoint s t) :
    Disjoint (f '' s) (f '' t) := by
  refine disjoint_left.mpr ?_
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hfy⟩
  exact disjoint_left.mp hd hx (hinj (hs hx) (ht hy) hfy.symm ▸ hy)

/-- For any circuit $K$ of $G$ in a plane drawing $M$, the inside closed disc $\Delta$ bounded by
$K$ and disjoint from the infinite region is unique. -/
theorem isInsideDisc_unique {G : Graph α β} (M : PlanarDrawing G) {K : Graph α β}
    {Δ₁ Δ₂ : Set M.S} (h₁ : IsInsideDisc M K Δ₁) (h₂ : IsInsideDisc M K Δ₂) :
    Δ₁ = Δ₂ := by
  have hS : IsClosedSurface M.S := M.isClosedSurface
  by_contra hne
  have hcov : Δ₁ ∪ Δ₂ = univ :=
    GM14.cover_of_discBd_eq hS h₁.1 h₂.1 (h₁.2.1.trans h₂.2.1.symm) hne
  obtain ⟨p, hp⟩ := region_nonempty M.infRegion_mem
  have hp_in : p ∈ Δ₁ ∪ Δ₂ := hcov ▸ mem_univ p
  rcases hp_in with hp₁ | hp₂
  · exact disjoint_left.mp h₁.2.2 hp₁ hp
  · exact disjoint_left.mp h₂.2.2 hp₂ hp

/-- If $R \le M.\text{drawing}.\text{toGraph}$ has the same vertex and edge sets as
$(m.\text{symm}.\text{sub } Q)$ for $Q \le G$, then $m.\text{sub } R = Q$. -/
theorem gmap_sub_eq_of_symm_sub [Nonempty α] [Nonempty β] {G : Graph α β} (M : PlanarDrawing G)
    {Q : Graph α β} (hQ : Q ≤ G) {R : Graph M.S (Set M.S)} (hR : R ≤ M.drawing.toGraph)
    (hV : V(R) = V((gmap_of_planarDrawing M).symm.sub Q))
    (hE : E(R) = E((gmap_of_planarDrawing M).symm.sub Q)) :
    (gmap_of_planarDrawing M).sub R = Q := by
  let m := gmap_of_planarDrawing M
  have hinvV := m.bijV.invOn_invFunOn
  have hinvE := m.bijE.invOn_invFunOn
  refine (Compatible.of_le_le (m.sub_le hR) hQ).ext ?_ ?_
  · rw [m.vertexSet_sub, hV, m.symm.vertexSet_sub, image_image]
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      dsimp
      rw [hinvV.2 (hQ.vertexSet_mono hw)]
      exact hw
    · intro hv
      exact ⟨v, hv, hinvV.2 (hQ.vertexSet_mono hv)⟩
  · rw [m.edgeSet_sub hR, hE, m.symm.edgeSet_sub hQ, image_image]
    ext e
    constructor
    · rintro ⟨f, hf, rfl⟩
      dsimp
      rw [hinvE.2 (hQ.edgeSet_mono hf)]
      exact hf
    · intro he
      exact ⟨e, he, hinvE.2 (hQ.edgeSet_mono he)⟩

/-- Any subdrawing $R$ of $H$ induces a subgraph $R.\text{toGraph} \le H.\text{toGraph}$. -/
theorem toGraph_le_of_isSubdrawing {S : Type*} [TopologicalSpace S] {H R : Drawing S}
    (hRH : R.IsSubdrawing H) : R.toGraph ≤ H.toGraph := by
  refine ⟨hRH.1, fun e x y hl => ?_⟩
  refine ⟨hRH.2 hl.edge_mem, hRH.1 hl.left_mem, hRH.1 hl.right_mem, ?_⟩
  rw [← hRH.closure_inter_V hl.edge_mem]
  exact hl.2.2.2

/-- Transporting `Drawing.inf M.drawing A B` along `gmap_of_planarDrawing M` yields
`subgraphInter G (m.sub A.toGraph) (m.sub B.toGraph)`. -/
theorem gmap_sub_drawing_inf [Nonempty α] [Nonempty β] {G : Graph α β} (M : PlanarDrawing G)
    {A B : Drawing M.S} (hA : A.IsSubdrawing M.drawing) (hB : B.IsSubdrawing M.drawing) :
    subgraphInter G ((gmap_of_planarDrawing M).sub A.toGraph)
        ((gmap_of_planarDrawing M).sub B.toGraph) =
      (gmap_of_planarDrawing M).sub (Drawing.inf M.drawing A B).toGraph := by
  let m := gmap_of_planarDrawing M
  have hAle : m.sub A.toGraph ≤ G := m.sub_le (toGraph_le_of_isSubdrawing hA)
  have hBle : m.sub B.toGraph ≤ G := m.sub_le (toGraph_le_of_isSubdrawing hB)
  have hInf : (Drawing.inf M.drawing A B).IsSubdrawing M.drawing :=
    Drawing.inf_isSubdrawing M.drawing A B
  have hInf_le : m.sub (Drawing.inf M.drawing A B).toGraph ≤ G :=
    m.sub_le (toGraph_le_of_isSubdrawing hInf)
  refine (Compatible.of_le_le (subgraphInter_le hAle) hInf_le).ext ?_ ?_
  · rw [vertexSet_subgraphInter, m.vertexSet_sub, m.vertexSet_sub, m.vertexSet_sub,
      show V((Drawing.inf M.drawing A B).toGraph) = (Drawing.inf M.drawing A B).V from rfl,
      Drawing.inf_V hA hB]
    exact ((m.bijV.injOn.mono (union_subset hA.1 hB.1)).image_inter
      subset_union_left subset_union_right).symm
  · rw [edgeSet_subgraphInter hAle hBle, m.edgeSet_sub (toGraph_le_of_isSubdrawing hA),
      m.edgeSet_sub (toGraph_le_of_isSubdrawing hB),
      m.edgeSet_sub (toGraph_le_of_isSubdrawing hInf),
      show E((Drawing.inf M.drawing A B).toGraph) = (Drawing.inf M.drawing A B).E from rfl,
      Drawing.inf_E hA]
    exact ((m.bijE.injOn.mono (union_subset hA.2 hB.2)).image_inter
      subset_union_left subset_union_right).symm

/-- A single-vertex walk subgraph is a path in $G$ from $u$ to $u$. -/
theorem isGraphPathWithEnds_walkSubgraph_nil {G : Graph α β} {u : α} (hu : u ∈ V(G)) :
    IsGraphPathWithEnds G (walkSubgraph (GraphWalk.nil hu)) u u := by
  refine ⟨walkSubgraph_le (GraphWalk.nil hu), GraphWalk.nil ?_, by simp [GraphWalk.IsSimple],
    by simp [vertexSet_walkSubgraph], by simp [edgeSet_walkSubgraph]⟩
  simp [vertexSet_walkSubgraph]

/-- A single-vertex walk subgraph is a path in $G$. -/
theorem isGraphPath_singleton_of_mem {G : Graph α β} {u : α} (hu : u ∈ V(G)) :
    IsGraphPath G (walkSubgraph (GraphWalk.nil hu)) :=
  ⟨u, u, isGraphPathWithEnds_walkSubgraph_nil hu⟩

/-! ## (4.1) Nest-and-Paths Uncrossing in a Plane Drawing (pages 60–61) -/

/-- **Graph Minors III, (4.1)** (page 60):
"(4.1) *Let $r \ge 0$, $s \ge 1$ be integers, and let $M$ be a drawing of the planar graph $G$.
Suppose that there is a nested sequence $C_1, \dots, C_s$ of circuits of $M$ such that there are $r$
vertex-disjoint paths of $G$, each between $V(C_1)$ and $V(C_s)$. Then $M$ majors the $r \times s$
cylinder.*" -/
theorem theorem_4_1_proof {G : Graph α β} (M : PlanarDrawing G) (r s : ℕ) (hs : 0 < s)
    (C₀ : Fin s → Graph α β) (P₀ : Fin r → Graph α β)
    (hC₀ : IsNestedCircuitSeq M s C₀)
    (hP₀_disj : Pairwise (fun i₁ i₂ : Fin r => Disjoint V(P₀ i₁) V(P₀ i₂)))
    (hP₀_path : ∀ i : Fin r, IsPathBetween G (P₀ i)
      V(C₀ ⟨0, hs⟩) V(C₀ ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩)) :
    MajorsCylinder M r s := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨hs, C₀, Fin.elim0, hC₀, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  · rcases lt_or_eq_of_le (Nat.succ_le_of_lt hs) with hs2 | hs1
    · -- Main case `2 ≤ s` and `0 < r`: reduce to `planar_nest_uncrossing` in `M.drawing`.
      have hS : IsClosedSurface M.S := M.isClosedSurface
      have : Nonempty α := by
        obtain ⟨_, u, _⟩ := hC₀.1 ⟨0, hs⟩
        exact ⟨u⟩
      have : Nonempty β := by
        obtain ⟨_, _, W, _, hlen, _, hE⟩ := hC₀.1 ⟨0, hs⟩
        rcases W with _ | @⟨_, _, _, e, _, _⟩
        · simp at hlen
        · exact ⟨e⟩
      let m := gmap_of_planarDrawing M
      let ms := m.symm
      have hex_R₀ : ∀ j : Fin s, ∃ R : Drawing M.S,
          R.IsCircuit ∧ R.IsSubdrawing M.drawing ∧
          R.V = V(ms.sub (C₀ j)) ∧ R.E = E(ms.sub (C₀ j)) :=
        fun j => GM14.exists_circuit_drawing (ms.circuit (hC₀.1 j))
      choose R₀ hR₀_circ hR₀_sub hR₀_V hR₀_E using hex_R₀
      have hR₀_map : ∀ j : Fin s, m.sub (R₀ j).toGraph = C₀ j := fun j =>
        gmap_sub_eq_of_symm_sub M (hC₀.1 j).1 (toGraph_le_of_isSubdrawing (hR₀_sub j))
          (hR₀_V j) (hR₀_E j)
      have hR₀_U : ∀ j : Fin s,
          graphDrawingSubgraphU M.graphDrawing (C₀ j) = (R₀ j).U := by
        intro j
        rw [← hR₀_map j]
        exact graphDrawingSubgraphU_gmap_sub M (hR₀_sub j) (toGraph_le_of_isSubdrawing (hR₀_sub j))
      have h01 : (⟨0, hs⟩ : Fin s) < ⟨1, hs2⟩ := Fin.mk_lt_mk.mpr zero_lt_one
      obtain ⟨_, Δ₁, Δ₀, hΔ₁_in, hΔ₀_in, hΔ₁_sub⟩ := hC₀.2 h01
      have hΔ₀_disc : IsClosedDisc Δ₀ := hΔ₀_in.1
      have hΔ₀_bd : discBd Δ₀ = (R₀ ⟨0, hs⟩).U := hΔ₀_in.2.1.trans (hR₀_U ⟨0, hs⟩)
      have hΔ₀_fr : frontier Δ₀ = (R₀ ⟨0, hs⟩).U :=
        (GM14.IsClosedDisc.frontier_eq_discBd hS hΔ₀_disc).trans hΔ₀_bd
      have hex_Δ : ∀ j : Fin s, ∃ Δ : Set M.S, IsInsideDisc M (C₀ j) Δ ∧ Δ ⊆ Δ₀ := by
        intro j
        by_cases hj0 : j.1 = 0
        · have hjeq : j = ⟨0, hs⟩ := Fin.ext hj0
          exact ⟨Δ₀, hjeq ▸ hΔ₀_in, Subset.rfl⟩
        · have hj_gt : (⟨0, hs⟩ : Fin s) < j := Fin.mk_lt_mk.mpr (Nat.pos_of_ne_zero hj0)
          obtain ⟨_, Δj, Δ₀', hΔj, hΔ₀', hsub⟩ := hC₀.2 hj_gt
          have heq : Δ₀' = Δ₀ := isInsideDisc_unique M hΔ₀' hΔ₀_in
          exact ⟨Δj, hΔj, heq ▸ hsub⟩
      choose Δ_seq hΔ_seq_in hΔ_seq_sub using hex_Δ
      have hR₀_U_sub : ∀ j : Fin s, (R₀ j).U ⊆ Δ₀ := by
        intro j
        have hbd_j : discBd (Δ_seq j) = (R₀ j).U := (hΔ_seq_in j).2.1.trans (hR₀_U j)
        have hfr_j : frontier (Δ_seq j) = (R₀ j).U :=
          (GM14.IsClosedDisc.frontier_eq_discBd hS (hΔ_seq_in j).1).trans hbd_j
        rw [← hfr_j]
        exact (hΔ_seq_in j).1.isCompact.isClosed.frontier_subset.trans (hΔ_seq_sub j)
      have hΔ_seq_eq : ∀ j : Fin s, Δ_seq j = GM14.discIns Δ₀ (R₀ j) := by
        intro j
        obtain ⟨_, huniq⟩ := GM14.discIns_spec hΔ₀_disc (hR₀_circ j) (hR₀_U_sub j)
        exact huniq (Δ_seq j) (hΔ_seq_sub j) (hΔ_seq_in j).1
          ((hΔ_seq_in j).2.1.trans (hR₀_U j))
      have hR₀_disj : Pairwise (fun j₁ j₂ : Fin s => Disjoint (R₀ j₁).V (R₀ j₂).V) := by
        intro j₁ j₂ hj12
        have hdisjG : Disjoint V(C₀ j₁) V(C₀ j₂) := by
          rcases lt_or_gt_of_ne hj12 with hlt | hgt
          · exact (hC₀.2 hlt).1
          · exact (hC₀.2 hgt).1.symm
        rw [hR₀_V j₁, hR₀_V j₂, ms.vertexSet_sub, ms.vertexSet_sub]
        exact disjoint_image_of_injOn
          (ms.bijV.injOn.mono (union_subset (hC₀.1 j₁).1.vertexSet_mono
            (hC₀.1 j₂).1.vertexSet_mono))
          subset_union_left subset_union_right hdisjG
      let j_last : Fin s := ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩
      let C_in : Drawing M.S := R₀ j_last
      let C_out : Drawing M.S := R₀ ⟨0, hs⟩
      let C_nest₀ : Fin s → Drawing M.S := fun m => R₀ m.rev
      have hC_nest₀ : IsDiscNest M.drawing Δ₀ C_in C_out C_nest₀ := by
        refine ⟨fun m => ⟨hR₀_sub m.rev, hR₀_circ m.rev, hR₀_U_sub m.rev⟩, ?_, ?_, ?_⟩
        · intro m₁ m₂ hm12
          exact hR₀_disj (Fin.rev_injective.ne hm12)
        · intro m₁ m₂ hm12
          change GM14.discIns Δ₀ (R₀ m₁.rev) ⊆ GM14.discIns Δ₀ (R₀ m₂.rev)
          rw [← hΔ_seq_eq m₁.rev, ← hΔ_seq_eq m₂.rev]
          have hrev : m₂.rev ≤ m₁.rev := Fin.rev_le_rev.mpr hm12
          rcases eq_or_lt_of_le hrev with heq | hlt
          · rw [heq]
          · obtain ⟨_, Δ', Δ, hΔ', hΔ, hsub⟩ := hC₀.2 hlt
            rw [isInsideDisc_unique M (hΔ_seq_in m₁.rev) hΔ',
              isInsideDisc_unique M (hΔ_seq_in m₂.rev) hΔ]
            exact hsub
        · intro _
          refine ⟨?_, ?_⟩
          · dsimp [C_nest₀, C_in, j_last, Fin.rev]
          · have hrev_last : (⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ : Fin s).rev = ⟨0, hs⟩ := by
              ext; dsimp [Fin.rev]; omega
            dsimp [C_nest₀, C_out]
            rw [hrev_last]
      -- Construct `P_draw₀ : Fin r → Drawing M.S` satisfying `IsDiscPaths`.
      have hCin_disj_Cout_U : Disjoint C_in.V C_out.U := by
        have hlt_0_last : (⟨0, hs⟩ : Fin s) < j_last := Fin.mk_lt_mk.mpr (by omega)
        have hdisj_V : Disjoint C_in.V C_out.V := (hR₀_disj hlt_0_last.ne).symm
        refine disjoint_left.mpr fun x hx_in hx_out => ?_
        have hxV : x ∈ M.drawing.V := (hR₀_sub j_last).1 hx_in
        rw [C_out.U_eq] at hx_out
        rcases hx_out with hx_out_V | hx_out_E
        · exact disjoint_left.mp hdisj_V hx_in hx_out_V
        · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx_out_E
          have hcap : x ∈ closure e ∩ C_out.V := by
            rw [(hR₀_sub ⟨0, hs⟩).closure_inter_V he]
            exact ⟨hxe, hxV⟩
          exact disjoint_left.mp hdisj_V hx_in hcap.2
      have hex_P₀_draw : ∀ i : Fin r, ∃ P_i : Drawing M.S,
          P_i.IsSubdrawing M.drawing ∧ P_i.U ⊆ Δ₀ ∧ P_i.V ⊆ V(ms.sub (P₀ i)) ∧
          ∃ a ∈ C_in.V, ∃ b ∈ C_out.V, P_i.IsPathBetween a b := by
        intro i
        obtain ⟨u₀, hu₀, v₀, hv₀, hPi_path⟩ := hP₀_path i
        have hPi_draw := ms.path hPi_path
        obtain ⟨hle_Pi, W₀, hW₀s, hW₀V, _⟩ := hPi_draw
        obtain ⟨W₁, hW₁_supp, _⟩ := exists_walk_up_of_le hle_Pi W₀
        have hW₁s : W₁.IsSimple := by
          change W₁.support.Nodup
          rw [hW₁_supp]
          exact hW₀s
        let x₀ := Function.invFunOn (drawingInvV M) M.drawing.V u₀
        let y₀ := Function.invFunOn (drawingInvV M) M.drawing.V v₀
        have hx₀_out : x₀ ∈ C_out.V := by
          rw [show C_out = R₀ ⟨0, hs⟩ from rfl, hR₀_V ⟨0, hs⟩, ms.vertexSet_sub]
          exact mem_image_of_mem _ hu₀
        have hy₀_in : y₀ ∈ C_in.V := by
          rw [show C_in = R₀ j_last from rfl, hR₀_V j_last, ms.vertexSet_sub]
          exact mem_image_of_mem _ hv₀
        have hhit_in : ∃ x ∈ W₁.support, x ∈ C_in.V :=
          ⟨y₀, W₁.end_mem_support, hy₀_in⟩
        obtain ⟨a_i, ha_i, W_a, W_tail, hW₁_eq, _⟩ := exists_first_hit_split W₁ hhit_in
        have hWa_s : W_a.IsSimple := (GM11.isSimple_of_append (hW₁_eq ▸ hW₁s)).1
        have hWa_rev_s : W_a.reverse.IsSimple := hWa_s.reverse
        have hhit_out : ∃ x ∈ W_a.reverse.support, x ∈ C_out.V :=
          ⟨x₀, W_a.reverse.end_mem_support, hx₀_out⟩
        obtain ⟨b_i, hb_i, W_i, W_rest, hWa_rev_eq, hWi_first⟩ :=
          exists_first_hit_split W_a.reverse hhit_out
        have hWi_s : W_i.IsSimple := (GM11.isSimple_of_append (hWa_rev_eq ▸ hWa_rev_s)).1
        let P_i := walkDrawing M.drawing W_i
        have hPi_V_sub : P_i.V ⊆ V(ms.sub (P₀ i)) := by
          intro z hz
          rw [walkDrawing_V, mem_ofPred_eq] at hz
          have hz_rev : z ∈ W_a.reverse.support := by
            rw [hWa_rev_eq, GraphWalk.mem_support_append]
            exact Or.inl hz
          rw [GraphWalk.support_reverse, List.mem_reverse] at hz_rev
          have hz_W₁ : z ∈ W₁.support := by
            rw [hW₁_eq, GraphWalk.mem_support_append]
            exact Or.inl hz_rev
          rw [hW₀V, mem_ofPred_eq, ← hW₁_supp]
          exact hz_W₁
        have ha_in_Δ₀ : a_i ∈ Δ₀ \ C_out.U :=
          ⟨hR₀_U_sub j_last (C_in.V_subset_U ha_i),
            disjoint_left.mp hCin_disj_Cout_U ha_i⟩
        have hWi_U_sub : P_i.U ⊆ Δ₀ := by
          have hrev_eq : P_i = walkDrawing M.drawing W_i.reverse :=
            (walkDrawing_reverse M.drawing W_i).symm
          rw [hrev_eq]
          rcases walk_subset_disc_or_exists_outer_detour (hR₀_sub ⟨0, hs⟩)
              hΔ₀_disc.isCompact.isClosed hΔ₀_fr W_i.reverse hWi_s.reverse hb_i ha_in_Δ₀ with
            hsub | ⟨u₁, hu₁, u₂, hu₂, hu12, W_pre, W_sub, W_post, hrev_split, _, _, _⟩
          · exact hsub
          · exfalso
            have hu₁_supp : u₁ ∈ W_i.support := by
              have h : u₁ ∈ W_i.reverse.support := by
                rw [hrev_split, GraphWalk.mem_support_append]
                exact Or.inl W_pre.end_mem_support
              rwa [GraphWalk.support_reverse, List.mem_reverse] at h
            have hu₂_supp : u₂ ∈ W_i.support := by
              have h : u₂ ∈ W_i.reverse.support := by
                rw [hrev_split, GraphWalk.mem_support_append, GraphWalk.mem_support_append]
                exact Or.inr (Or.inl W_sub.end_mem_support)
              rwa [GraphWalk.support_reverse, List.mem_reverse] at h
            have h1 : u₁ = b_i := hWi_first u₁ hu₁_supp hu₁
            have h2 : u₂ = b_i := hWi_first u₂ hu₂_supp hu₂
            exact hu12 (h1.trans h2.symm)
        exact ⟨P_i, walkDrawing_isSubdrawing M.drawing W_i, hWi_U_sub, hPi_V_sub,
          a_i, ha_i, b_i, hb_i, walkDrawing_isPathBetween M.drawing hWi_s⟩
      choose P_draw₀ hP₀_sub hP₀_U hP₀_V_sub hP₀_ends using hex_P₀_draw
      have hP_draw₀ : IsDiscPaths M.drawing Δ₀ C_in C_out P_draw₀ := by
        refine ⟨fun i => ⟨hP₀_sub i, hP₀_U i, hP₀_ends i⟩, ?_⟩
        intro i₁ i₂ hi12
        refine disjoint_of_subset (hP₀_V_sub i₁) (hP₀_V_sub i₂) ?_
        rw [ms.vertexSet_sub, ms.vertexSet_sub]
        have hle₁ := (hP₀_path i₁).choose_spec.2.choose_spec.2.1
        have hle₂ := (hP₀_path i₂).choose_spec.2.choose_spec.2.1
        exact disjoint_image_of_injOn
          (ms.bijV.injOn.mono (union_subset hle₁.vertexSet_mono hle₂.vertexSet_mono))
          subset_union_left subset_union_right (hP₀_disj hi12)
      obtain ⟨C', P', hC', hP', hinf⟩ :=
        planar_nest_uncrossing hS hΔ₀_disc hΔ₀_bd ⟨C_nest₀, hC_nest₀⟩ ⟨P_draw₀, hP_draw₀⟩
      let C_final : Fin s → Graph α β := fun j => m.sub (C' j.rev).toGraph
      let P_final : Fin r → Graph α β := fun i => m.sub (P' i).toGraph
      have hC_final_U : ∀ j : Fin s,
          graphDrawingSubgraphU M.graphDrawing (C_final j) = (C' j.rev).U := fun j =>
        graphDrawingSubgraphU_gmap_sub M (hC'.1 j.rev).1
          (toGraph_le_of_isSubdrawing (hC'.1 j.rev).1)
      have hC_final_in : ∀ j : Fin s,
          IsInsideDisc M (C_final j) (GM14.discIns Δ₀ (C' j.rev)) := by
        intro j
        obtain ⟨hsub, hdisc, hbd, _, _, _⟩ := hC'.disc_props hS hΔ₀_disc j.rev
        refine ⟨hdisc, hbd.trans (hC_final_U j).symm, ?_⟩
        exact disjoint_of_subset_left hsub hΔ₀_in.2.2
      have hC_final_nested : IsNestedCircuitSeq M s C_final := by
        refine ⟨fun j => m.circuit
          (GM14.isGraphCircuit_of_isCircuit (hC'.1 j.rev).2.1 (hC'.1 j.rev).1), ?_⟩
        intro j₁ j₂ hj12
        refine ⟨?_, ?_⟩
        · dsimp [C_final]
          rw [m.vertexSet_sub, m.vertexSet_sub]
          exact disjoint_image_of_injOn
            (m.bijV.injOn.mono (union_subset (hC'.1 j₁.rev).1.1 (hC'.1 j₂.rev).1.1))
            subset_union_left subset_union_right
            (hC'.2.1 (Fin.rev_injective.ne hj12.ne))
        · refine ⟨GM14.discIns Δ₀ (C' j₂.rev), GM14.discIns Δ₀ (C' j₁.rev),
            hC_final_in j₂, hC_final_in j₁, ?_⟩
          exact hC'.2.2.1 (Fin.rev_le_rev.mpr hj12.le)
      have hP_final_disj : Pairwise (fun i₁ i₂ : Fin r => Disjoint V(P_final i₁) V(P_final i₂)) := by
        intro i₁ i₂ hi12
        dsimp [P_final]
        rw [m.vertexSet_sub, m.vertexSet_sub]
        exact disjoint_image_of_injOn
          (m.bijV.injOn.mono (union_subset (hP'.1 i₁).1.1 (hP'.1 i₂).1.1))
          subset_union_left subset_union_right (hP'.2 hi12)
      have hC'_0 : C' ⟨0, hs⟩ = C_in := (hC'.2.2.2 hs).1
      have hC'_last : C' j_last = C_out := (hC'.2.2.2 hs).2
      have hrev_0 : (⟨0, hs⟩ : Fin s).rev = j_last := by ext; dsimp [j_last, Fin.rev]
      have hrev_last : j_last.rev = ⟨0, hs⟩ := by ext; dsimp [j_last, Fin.rev]; omega
      have hP_final_path : ∀ i : Fin r,
          IsPathBetween G (P_final i) V(C_final ⟨0, hs⟩) V(C_final j_last) := by
        intro i
        obtain ⟨a_i, ha_i, b_i, hb_i, hPi_path⟩ := (hP'.1 i).2.2
        have hPi_G : IsGraphPathWithEnds M.drawing.toGraph (P' i).toGraph a_i b_i :=
          ⟨toGraph_le_of_isSubdrawing (hP'.1 i).1, hPi_path⟩
        have hm_path := (m.path hPi_G).symm
        refine ⟨drawingInvV M b_i, ?_, drawingInvV M a_i, ?_, hm_path⟩
        · dsimp [C_final]
          rw [hrev_0, hC'_last, m.vertexSet_sub]
          exact mem_image_of_mem _ hb_i
        · dsimp [C_final]
          rw [hrev_last, hC'_0, m.vertexSet_sub]
          exact mem_image_of_mem _ ha_i
      have h_inter_path : ∀ (i : Fin r) (j : Fin s),
          IsGraphPath G (subgraphInter G (P_final i) (C_final j)) := by
        intro i j
        dsimp [P_final, C_final]
        rw [gmap_sub_drawing_inf M (hP'.1 i).1 (hC'.1 j.rev).1,
          Drawing.inf_comm (hP'.1 i).1 (hC'.1 j.rev).1]
        obtain ⟨u, v, huv⟩ := hinf j.rev i
        have hInf_sub : (Drawing.inf M.drawing (C' j.rev) (P' i)).IsSubdrawing M.drawing :=
          Drawing.inf_isSubdrawing M.drawing (C' j.rev) (P' i)
        exact ⟨drawingInvV M u, drawingInvV M v,
          m.path ⟨toGraph_le_of_isSubdrawing hInf_sub, huv⟩⟩
      exact ⟨hs, C_final, P_final, hC_final_nested, hP_final_disj, hP_final_path, h_inter_path⟩
    · -- Case `s = 1`: replace each `P₀ i` by its initial 1-vertex path in `V(C₀ 0)`.
      subst hs1
      have hex_u : ∀ i : Fin r, ∃ u ∈ V(C₀ ⟨0, hs⟩) ∩ V(P₀ i), u ∈ V(G) := by
        intro i
        obtain ⟨u, huC, _, _, hP⟩ := hP₀_path i
        exact ⟨u, ⟨huC, hP.left_mem⟩, (hC₀.1 ⟨0, hs⟩).1.vertexSet_mono huC⟩
      choose u hu_mem huG using hex_u
      let P' : Fin r → Graph α β := fun i => walkSubgraph (GraphWalk.nil (huG i))
      refine ⟨hs, C₀, P', hC₀, ?_, ?_, ?_⟩
      · intro i₁ i₂ hi12
        dsimp [P']
        rw [vertexSet_walkSubgraph, vertexSet_walkSubgraph]
        simp only [GraphWalk.support_nil, List.mem_singleton, ofPred_eq_eq_singleton,
          disjoint_singleton]
        intro heq
        exact disjoint_left.mp (hP₀_disj hi12) (hu_mem i₁).2 (heq ▸ (hu_mem i₂).2)
      · intro i
        exact ⟨u i, (hu_mem i).1, u i, (hu_mem i).1,
          isGraphPathWithEnds_walkSubgraph_nil (huG i)⟩
      · intro i j
        have hj0 : j = ⟨0, hs⟩ := Fin.ext (by omega)
        subst hj0
        have heq : subgraphInter G (P' i) (C₀ ⟨0, hs⟩) = P' i := by
          have hP'_le : P' i ≤ G := walkSubgraph_le (GraphWalk.nil (huG i))
          refine (Compatible.of_le_le (subgraphInter_le hP'_le) hP'_le).ext ?_ ?_
          · rw [vertexSet_subgraphInter]
            dsimp [P']
            rw [vertexSet_walkSubgraph]
            ext x
            simp only [mem_inter_iff, GraphWalk.support_nil, List.mem_singleton, mem_ofPred_eq]
            exact ⟨fun h => h.1, fun h => ⟨h, h ▸ (hu_mem i).1⟩⟩
          · rw [edgeSet_subgraphInter hP'_le (hC₀.1 ⟨0, hs⟩).1]
            dsimp [P']
            rw [edgeSet_walkSubgraph]
            simp
        rw [heq]
        exact isGraphPath_singleton_of_mem (huG i)

/-! ## (4.2) Menger Dichotomy for a Nested Sequence of Circuits (page 61) -/

/-- **Graph Minors III, (4.2)** (page 61):
"(4.2) *Let $r \ge 0$, $s \ge 1$ be integers, and let $M$ be a drawing of the planar graph $G$. Let
$C_1, \dots, C_s$ be a nested sequence of circuits of $M$. Then one of the following holds:*

(i) *$M$ majors the $r \times s$ cylinder,*
(ii) *there exists $X \subseteq V(G)$ with $|X| < r$, such that $X$ separates $V(C_1)$ and
$V(C_s)$.*" -/
theorem theorem_4_2_proof {G : Graph α β} (M : PlanarDrawing G) (r s : ℕ) (hs : 0 < s)
    (C : Fin s → Graph α β) (hC : IsNestedCircuitSeq M s C) :
    MajorsCylinder M r s ∨
      ∃ X ⊆ V(G), X.ncard < r ∧
        Separates G X V(C ⟨0, hs⟩) V(C ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩) := by
  by_cases hsep : ∃ X ⊆ V(G), X.ncard < r ∧
      Separates G X V(C ⟨0, hs⟩) V(C ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩)
  · exact Or.inr hsep
  · left
    have hno_sep : ∀ Z ⊆ V(G),
        Separates G Z V(C ⟨0, hs⟩) V(C ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩) → r ≤ Z.ncard := by
      intro Z hZG hZsep
      by_contra hlt
      exact hsep ⟨Z, hZG, Nat.lt_of_not_ge hlt, hZsep⟩
    obtain ⟨P, hP_disj, hP_path⟩ :=
      exists_disjoint_isPathBetween_of_separates M.graphDrawing.finite_V
        (hC.1 ⟨0, hs⟩).1.vertexSet_mono
        (hC.1 ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩).1.vertexSet_mono r hno_sep
    exact theorem_4_1_proof M r s hs C P hC hP_disj hP_path

/-! ## (4.3) Augmenting a Cylinder or Decomposing as a Sleeve Union (page 61) -/

/-- **Graph Minors III, (4.3)** (page 61):
"(4.3) *Let $r \ge 0$ be an integer, and let $r' = r + 1$ if $r$ is odd, and $r' = r$ if $r$ is
even. Let $s > r'$ be an integer. Let $M$ be a drawing of the planar graph $G$, and suppose that $M$
majors the $r \times s$ cylinder. Then either $M$ majors the $(r + 1) \times (s - r')$ cylinder, or
$G$ is expressible as the sleeve union of two planar graphs.*" -/
theorem theorem_4_3_proof {G : Graph α β} (M : PlanarDrawing G) (r s : ℕ)
    (hs : 2 * ((r + 1) / 2) < s)
    (hMaj : MajorsCylinder M r s) :
    MajorsCylinder M (r + 1) (s - 2 * ((r + 1) / 2)) ∨
      IsExpressibleAsPlanarSleeveUnion G := by
  let d := (r + 1) / 2
  have hs_mid : 0 < s - 2 * d := by omega
  obtain ⟨hs0, C, P, hC, hP_disj, hP_path, hP_inter⟩ := hMaj
  let C_mid : Fin (s - 2 * d) → Graph α β := fun j => C ⟨d + j.1, by omega⟩
  have hC_mid : IsNestedCircuitSeq M (s - 2 * d) C_mid := by
    refine ⟨fun j => hC.1 ⟨d + j.1, by omega⟩, fun j₁ j₂ hj12 => ?_⟩
    have hlt : (⟨d + j₁.1, by omega⟩ : Fin s) < ⟨d + j₂.1, by omega⟩ :=
      Fin.mk_lt_mk.mpr (by omega)
    exact hC.2 hlt
  rcases theorem_4_2_proof M (r + 1) (s - 2 * d) hs_mid C_mid hC_mid with
    hMaj' | ⟨X, hXV, hXcard, hXsep⟩
  · exact Or.inl hMaj'
  · right
    have hC0 : C_mid ⟨0, hs_mid⟩ = C ⟨d, by omega⟩ := rfl
    have hClast : C_mid ⟨s - 2 * d - 1, Nat.sub_lt hs_mid zero_lt_one⟩ =
        C ⟨s - d - 1, by omega⟩ := by
      dsimp [C_mid]; congr 1; ext; dsimp; omega
    rw [hC0, hClast] at hXsep
    exact sleeve_of_sep M hs C P hC hP_disj hP_path hP_inter X hXV (by omega) hXsep

/-! ## (4.4) Radius Bound When $M$ Does Not Major the $r \times s$ Cylinder (pages 61–62) -/

/-- Arithmetic step for the induction in (4.4) (page 62):
$$s + 2 \lfloor (m + 1) / 2 \rfloor + \lfloor m^2 / 2 \rfloor = s + \lfloor (m + 1)^2 / 2 \rfloor.$$ -/
theorem cylinderRadiusBound_step (m s : ℕ) :
    cylinderRadiusBound m (s + 2 * ((m + 1) / 2)) = cylinderRadiusBound (m + 1) s := by
  unfold cylinderRadiusBound
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h1 : (k + k + 1) / 2 = k := by omega
    have h2 : (k + k) ^ 2 = 2 * (2 * k ^ 2) := by ring
    have h3 : (k + k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
    rw [h1, h2, h3]
    omega
  · have h1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have h2 : (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by ring
    have h3 : (2 * k + 1 + 1) ^ 2 = 2 * (2 * k ^ 2 + 4 * k + 2) := by ring
    rw [h1, h2, h3]
    omega

/-- **Graph Minors III, (4.4)** (pages 61–62):
"(4.4) *Let $r \ge 0$, $s \ge 1$ be integers, and let $M$ be a drawing of the planar graph $G$.
Suppose that $G$ is not expressible as a sleeve union of two planar
graphs, and $M$ does not major the $r \times s$ cylinder. Then $G$ has radius $<k$, where*
$$
\begin{aligned}
k &= s + \frac{1}{2}r^2 && (r\text{ even}) \\
&= s + \frac{1}{2}(r^2 - 1) && (r\text{ odd}).
\end{aligned}
$$" -/
theorem theorem_4_4_proof {G : Graph α β} (M : PlanarDrawing G) (r s : ℕ) (hs : 0 < s)
    (hNotSleeve : ¬ IsExpressibleAsPlanarSleeveUnion G)
    (hNotMaj : ¬ MajorsCylinder M r s) :
    HasRadiusLE G (cylinderRadiusBound r s - 1) := by
  induction r generalizing s with
  | zero =>
    have hbound : cylinderRadiusBound 0 s = s := by simp [cylinderRadiusBound]
    rw [hbound]
    by_contra hnot_rad
    obtain ⟨C, hC⟩ := theorem_2_8_proof M s (fun _ => hnot_rad)
    exact hNotMaj ⟨hs, C, Fin.elim0, hC, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ m ih =>
    let s' := s + 2 * ((m + 1) / 2)
    have hs' : 0 < s' := by omega
    have hs'_gt : 2 * ((m + 1) / 2) < s' := by omega
    have hNotMaj' : ¬ MajorsCylinder M m s' := by
      intro hMaj'
      rcases theorem_4_3_proof M m s' hs'_gt hMaj' with hMaj_succ | hSleeve
      · have hsub : s' - 2 * ((m + 1) / 2) = s := by omega
        rw [hsub] at hMaj_succ
        exact hNotMaj hMaj_succ
      · exact hNotSleeve hSleeve
    have hrad := ih s' hs' hNotMaj'
    rwa [cylinderRadiusBound_step m s] at hrad

/-! ## (4.5) Cylinder Minor or Tree-Width Bound for Sleeve-Irreducible Planar Graphs (page 62) -/

/-- Every planar graph $G$ (`IsPlanar G`) admits a `PlanarDrawing G`. -/
theorem nonempty_planarDrawing_of_isPlanar {G : Graph α β} (hPlanar : IsPlanar G) :
    Nonempty (PlanarDrawing G) := by
  obtain ⟨_, _, S, topS, _, hSph, ⟨Γ⟩⟩ := hPlanar
  have hCS : IsClosedSurface S := (GM11.IsSphere.isClosedSurface hSph).1
  have : T2Space S := hCS.2.1
  have : ConnectedSpace S := (GM11.IsSphere.isClosedSurface hSph).2
  obtain ⟨y, -, hyU⟩ := GM11.exists_notMem_U (Γ := Γ.drawing) hCS isOpen_univ univ_nonempty
  obtain ⟨R₀, hR₀, -⟩ := GM11.exists_region_of_notMem hyU
  exact ⟨{
    S := S
    topSpace := topS
    isClosedSurface := hCS
    isSphere := hSph
    graphDrawing := Γ
    infRegion := R₀
    infRegion_mem := hR₀ }⟩

/-- **Graph Minors III, (4.5)** (page 62):
"(4.5) *Let $r \ge 0$, $s \ge 1$ be integers. If $G$ is a planar graph which is not expressible as
the sleeve union of two planar graphs, then either $G$ has a minor isomorphic to the $r \times s$
cylinder, or it has tree-width at most*
$$
\begin{aligned}
&3(s + \frac{1}{2}r^2) - 2 && (r\text{ even}) \\
&3(s + \frac{1}{2}(r^2 - 1)) - 2 && (r\text{ odd}).
\end{aligned}
$$" -/
theorem theorem_4_5_proof {G : Graph α β} (r s : ℕ) (hs : 0 < s)
    (hPlanar : IsPlanar G) (hNotSleeve : ¬ IsExpressibleAsPlanarSleeveUnion G) :
    IsIsoMinor (cylinderGraph r s) G ∨ TreeWidthLE G (cylinderTreeWidthBound r s) := by
  obtain ⟨M⟩ := nonempty_planarDrawing_of_isPlanar hPlanar
  by_cases hMaj : MajorsCylinder M r s
  · exact Or.inl (isIsoMinor_cylinderGraph_of_majorsCylinder M hMaj)
  · right
    have hrad : HasRadiusLE G (cylinderRadiusBound r s - 1) :=
      theorem_4_4_proof M r s hs hNotSleeve hMaj
    have htw := theorem_2_7_proof hPlanar hrad
    have hbound : 3 * (cylinderRadiusBound r s - 1) + 1 = cylinderTreeWidthBound r s := by
      unfold cylinderTreeWidthBound cylinderRadiusBound
      omega
    rwa [hbound] at htw

end GraphMinor.GM03
