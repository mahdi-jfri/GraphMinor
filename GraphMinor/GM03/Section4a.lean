module

public import GraphMinor.GM03.Defs
public import GraphMinor.GM03.Section2a
public import GraphMinor.GM07.CuffChart
public import GraphMinor.GM09.Basic
import GraphMinor.GM07.CuffCells
import GraphMinor.GM07.CuffOrder
import GraphMinor.GM07.CuffSegments
import GraphMinor.GM09.PlanarNests
import GraphMinor.GM16.LineDrawingPath
import GraphMinor.Surface.SphereDisc

/-!
# Graph Minors III, Section 4 Helpers: Walk Decomposition and Cyclic Spoke Ordering

This file proves the structural decomposition of nested circuits $C_1, \dots, C_s$ and disjoint
radial paths $P_1, \dots, P_r$ (with $P_i \cap C_j$ a path for all $i, j$) in a plane drawing $M$,
used in the proofs of Graph Minors III, (4.3) (page 61) and (4.5) (page 62):

1. Every circuit $K$ in a plane drawing $M$ bounds a unique inside closed disc disjoint from the
   infinite region (`exists_insideDisc_of_circuit`).
2. Along each path $P_i$ between $V(C_1)$ and $V(C_s)$, the intersection paths $P_i \cap C_j$
   appear as contiguous subwalks in strict order $j = 0, 1, \dots, s - 1$, separated by radial
   subwalks whose open arcs lie in the open annuli between consecutive inside discs.
3. There is a single cyclic ordering $\sigma$ of $\{1, \dots, r\}$ such that on every circuit
   $C_j$ ($0 \le j < s$), $C_j$ decomposes into $r$ pairwise disjoint connected pieces
   `K_circ k j` (containing $V(P_{\sigma(k)} \cap C_j)$) linked in cyclic order $k \to k + 1 \bmod r$
   by $r$ distinct circular edges `e_circ k j` of $C_j$.
-/

public section

namespace GraphMinor.GM03

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM09.PlanarNests
open GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM16

universe u v

variable {α : Type u} {β : Type v}

/-! ## 1. Cyclic Index Helpers and Inside Discs -/

/-- Previous spoke index $(i + r - 1) \bmod r$ on a circle of length $r$. -/
def prevSpoke {r : ℕ} (i : Fin r) : Fin r :=
  ⟨(i.1 + r - 1) % r, Nat.mod_lt _ i.pos⟩

theorem nextSpoke_prevSpoke {r : ℕ} (i : Fin r) : nextSpoke (prevSpoke i) = i := by
  have hi := i.2
  have hr : 0 < r := i.pos
  ext
  dsimp [nextSpoke, prevSpoke]
  by_cases h0 : i.1 = 0
  · simp only [h0, zero_add, Nat.mod_eq_of_lt (show r - 1 < r by omega)]
    have : r - 1 + 1 = r := by omega
    rw [this, Nat.mod_self]
  · have hlt : i.1 - 1 < r := by omega
    have heq : (i.1 + r - 1) % r = i.1 - 1 := by
      have : i.1 + r - 1 = (i.1 - 1) + 1 * r := by omega
      rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    rw [heq]
    have hlt2 : i.1 - 1 + 1 < r ∨ i.1 - 1 + 1 = r := by omega
    rcases hlt2 with h1 | h1
    · rw [Nat.mod_eq_of_lt h1]; omega
    · omega

theorem prevSpoke_nextSpoke {r : ℕ} (i : Fin r) : prevSpoke (nextSpoke i) = i := by
  have hi := i.2
  have hr : 0 < r := i.pos
  ext
  dsimp [nextSpoke, prevSpoke]
  by_cases hlast : i.1 + 1 = r
  · have hmod : (i.1 + 1) % r = 0 := by rw [hlast, Nat.mod_self]
    rw [hmod]
    simp [Nat.mod_eq_of_lt (show r - 1 < r by omega)]
    omega
  · have hlt : i.1 + 1 < r := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have : i.1 + 1 + r - 1 = i.1 + 1 * r := by omega
    rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

theorem nextSpoke_pair_inj {r : ℕ} (hr : 3 ≤ r) {k₁ k₂ : Fin r}
    (h : ({k₁, nextSpoke k₁} : Set (Fin r)) = {k₂, nextSpoke k₂}) : k₁ = k₂ := by
  by_contra hne
  have hk₁ : k₁ ∈ ({k₂, nextSpoke k₂} : Set (Fin r)) := h ▸ mem_insert k₁ _
  have hk₂ : k₂ ∈ ({k₁, nextSpoke k₁} : Set (Fin r)) := h.symm ▸ mem_insert k₂ _
  have h1 : k₁ = nextSpoke k₂ := hk₁.resolve_left hne
  have h2 : k₂ = nextSpoke k₁ := hk₂.resolve_left (Ne.symm hne)
  have hv1 : k₁.1 = (k₂.1 + 1) % r := congrArg Fin.val h1
  have hv2 : k₂.1 = (k₁.1 + 1) % r := congrArg Fin.val h2
  have := k₁.2
  have := k₂.2
  by_cases h1lt : k₁.1 + 1 < r <;> by_cases h2lt : k₂.1 + 1 < r
  · rw [Nat.mod_eq_of_lt h1lt] at hv2; rw [Nat.mod_eq_of_lt h2lt] at hv1; omega
  · have hk2 : k₂.1 + 1 = r := by omega
    rw [Nat.mod_eq_of_lt h1lt] at hv2; rw [hk2, Nat.mod_self] at hv1; omega
  · have hk1 : k₁.1 + 1 = r := by omega
    rw [hk1, Nat.mod_self] at hv2; rw [Nat.mod_eq_of_lt h2lt] at hv1; omega
  · omega

local instance {G : Graph α β} (M : PlanarDrawing G) : T2Space M.S :=
  M.isClosedSurface.2.1

local instance {G : Graph α β} (M : PlanarDrawing G) : ConnectedSpace M.S :=
  (GM11.IsSphere.isClosedSurface M.isSphere).2

local instance {G : Graph α β} (M : PlanarDrawing G) : Nonempty M.S :=
  (GM11.IsSphere.isClosedSurface M.isSphere).2.toNonempty

theorem disjoint_image_of_injOn' {X Y : Type*} {f : X → Y} {s t u : Set X}
    (hinj : InjOn f u) (hs : s ⊆ u) (ht : t ⊆ u) (hd : Disjoint s t) :
    Disjoint (f '' s) (f '' t) := by
  refine disjoint_left.mpr ?_
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hfy⟩
  exact disjoint_left.mp hd hx (hinj (hs hx) (ht hy) hfy.symm ▸ hy)

theorem isInsideDisc_eq {G : Graph α β} (M : PlanarDrawing G) {K : Graph α β}
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

theorem gmap_sub_eq_of_symm_sub' [Nonempty α] [Nonempty β] {G : Graph α β} (M : PlanarDrawing G)
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

theorem toGraph_le_of_isSubdrawing' {S : Type*} [TopologicalSpace S] {H R : Drawing S}
    (hRH : R.IsSubdrawing H) : R.toGraph ≤ H.toGraph := by
  refine ⟨hRH.1, fun e x y hl => ?_⟩
  refine ⟨hRH.2 hl.edge_mem, hRH.1 hl.left_mem, hRH.1 hl.right_mem, ?_⟩
  rw [← hRH.closure_inter_V hl.edge_mem]
  exact hl.2.2.2

/-- Every circuit $K$ of $G$ in a plane drawing $M$ bounds an inside closed disc $\Delta$ disjoint
from `M.infRegion`. -/
theorem exists_insideDisc_of_circuit {G : Graph α β} (M : PlanarDrawing G) {K : Graph α β}
    (hK : IsGraphCircuit G K) : ∃ Δ : Set M.S, IsInsideDisc M K Δ := by
  have hS : IsClosedSurface M.S := M.isClosedSurface
  have hman : ∀ x : M.S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have : Nonempty α := by obtain ⟨_, u, _⟩ := hK; exact ⟨u⟩
  have : Nonempty β := by
    obtain ⟨_, _, W, _, hlen, _, _⟩ := hK
    rcases W with _ | @⟨_, _, _, e, _, _⟩
    · simp at hlen
    · exact ⟨e⟩
  let m := gmap_of_planarDrawing M
  let ms := m.symm
  obtain ⟨R, hR_circ, hR_sub, hR_V, hR_E⟩ := GM14.exists_circuit_drawing (ms.circuit hK)
  have hR_map : m.sub R.toGraph = K :=
    gmap_sub_eq_of_symm_sub' M hK.1 (toGraph_le_of_isSubdrawing' hR_sub) hR_V hR_E
  have hR_U : graphDrawingSubgraphU M.graphDrawing K = R.U := by
    rw [← hR_map]
    exact graphDrawingSubgraphU_gmap_sub M hR_sub (toGraph_le_of_isSubdrawing' hR_sub)
  obtain ⟨Δ₁, Δ₂, _, hΔ₁, hΔ₂, hb₁, hb₂, _, hcap, _, _⟩ :=
    sphere_disc M.S M.isSphere R.U (IsCircuit.isOArc_U hR_circ)
  have hinf_off : Disjoint M.infRegion (discBd Δ₁) := by
    rw [hb₁]
    refine disjoint_left.mpr fun x hxinf hxR => ?_
    obtain ⟨z, -, hz_eq⟩ := (mem_R_iff M.drawing).mp M.infRegion_mem
    rw [hz_eq] at hxinf
    exact (connectedComponentIn_subset _ _ hxinf).2 (hR_sub.U_subset hxR)
  rcases hΔ₁.side hman (region_isPreconnected M.infRegion_mem) hinf_off with hin | hout
  · refine ⟨Δ₂, hΔ₂, hb₂.trans hR_U.symm, disjoint_left.mpr fun x hx₂ hxinf => ?_⟩
    have hx₁_int : x ∈ discInt Δ₁ := hin hxinf
    have hx_cap : x ∈ Δ₁ ∩ Δ₂ := ⟨ hx₁_int.1, hx₂ ⟩
    rw [hcap, ← hb₁] at hx_cap
    exact hx₁_int.2 hx_cap
  · exact ⟨Δ₁, hΔ₁, hb₁.trans hR_U.symm, hout.symm⟩

/-! ## 2. Contiguous Subwalks of Simple Walks -/

private theorem walkSubgraph_only_edge_at_start {G : Graph α β} {a w b : α} {e₀ : β}
    (hl : G.IsLink e₀ a w) (r : GraphWalk G w b) (ha_not : a ∉ r.support)
    {f : β} {z : α} (hf : (walkSubgraph (GraphWalk.cons hl r)).IsLink f a z) :
    f = e₀ ∧ z = w := by
  rw [walkSubgraph_isLink] at hf
  obtain ⟨hf_mem, hfz⟩ := hf
  rcases List.mem_cons.mp hf_mem with rfl | hfr
  · rcases hl.symm.left_eq_or_eq hfz.symm with hwz | hwa
    · exact ⟨rfl, hwz.symm⟩
    · exact (ha_not (hwa ▸ r.start_mem_support)).elim
  · exfalso
    exact ha_not (r.left_mem_support_of_mem_edges hfr hfz)

private theorem not_mem_support_of_walk_walkSubgraph_cons {G : Graph α β} {a w b u v : α} {e₀ : β}
    (hl : G.IsLink e₀ a w) (r : GraphWalk G w b) (ha_not : a ∉ r.support)
    (L : GraphWalk (walkSubgraph (GraphWalk.cons hl r)) u v) (hLs : L.IsSimple)
    (hu : u ≠ a) (hv : v ≠ a) : a ∉ L.support := by
  intro haL
  obtain ⟨A, B, hAB⟩ := L.exists_append_of_mem haL
  have hAs : A.IsSimple := (isSimple_of_append (hAB ▸ hLs)).1
  have hBs : B.IsSimple := (isSimple_of_append (hAB ▸ hLs)).2
  cases B with
  | nil _ => exact hv rfl
  | @cons _ z₂ _ f₂ hlf₂ rB =>
    obtain ⟨_, hz₂w⟩ := walkSubgraph_only_edge_at_start hl r ha_not hlf₂
    cases hz₂w.symm
    have hA_rev : A.reverse.IsSimple := hAs.reverse
    cases hA_eq : A.reverse with
    | nil _ => exact hu rfl
    | @cons _ z₁ _ f₁ hlf₁ rA =>
      obtain ⟨_, hz₁w⟩ := walkSubgraph_only_edge_at_start hl r ha_not hlf₁
      cases hz₁w.symm
      have hnd : (A.append (GraphWalk.cons hlf₂ rB)).support.Nodup := hAB ▸ hLs
      rw [GraphWalk.support_append] at hnd
      have h_in_A : w ∈ A.support := by
        have : w ∈ A.reverse.support := by rw [hA_eq]; exact List.mem_cons_of_mem _ rA.start_mem_support
        rwa [GraphWalk.support_reverse, List.mem_reverse] at this
      have h_in_tail : w ∈ (GraphWalk.cons hlf₂ rB).support.tail := rB.start_mem_support
      exact (List.nodup_append.mp hnd).2.2 w h_in_A w h_in_tail rfl

private theorem walk_walkSubgraph_unique {G : Graph α β} {a b u v : α}
    (W : GraphWalk G a b) (hWs : W.IsSimple)
    (L₁ L₂ : GraphWalk (walkSubgraph W) u v) (h₁ : L₁.IsSimple) (h₂ : L₂.IsSimple) :
    L₁.support = L₂.support ∧ L₁.edges = L₂.edges := by
  induction W generalizing u v with
  | nil ha =>
    cases L₁ with
    | nil _ =>
      cases L₂ with
      | nil _ => exact ⟨rfl, rfl⟩
      | cons hl₂ _ => simp at hl₂
    | cons hl₁ _ => simp at hl₁
  | @cons a w b e₀ hl r ih =>
    have ha_not : a ∉ r.support := (List.nodup_cons.mp hWs).1
    have hrs : r.IsSimple := (List.nodup_cons.mp hWs).2
    have hle_r : walkSubgraph r ≤ walkSubgraph (GraphWalk.cons hl r) := by
      refine ⟨fun x hx => ?_, fun f x y hlf => ?_⟩
      · rw [vertexSet_walkSubgraph] at hx ⊢
        exact List.mem_cons_of_mem _ hx
      · rw [walkSubgraph_isLink] at hlf ⊢
        exact ⟨List.mem_cons_of_mem _ hlf.1, hlf.2⟩
    have down_to_r : ∀ {p q : α} (L : GraphWalk (walkSubgraph (GraphWalk.cons hl r)) p q),
        a ∉ L.support → ∃ L' : GraphWalk (walkSubgraph r) p q,
          L'.support = L.support ∧ L'.edges = L.edges := by
      intro p q L haL
      refine exists_walk_down_of_le hle_r L (fun x hx => ?_) (fun f hf => ?_)
      · have hx_mem : x ∈ (GraphWalk.cons hl r).support := by
          have h := L.mem_vertexSet_of_mem_support hx
          rwa [vertexSet_walkSubgraph] at h
        rcases List.mem_cons.mp hx_mem with rfl | hxr
        · exact (haL hx).elim
        · rw [vertexSet_walkSubgraph]; exact hxr
      · obtain ⟨x, y, hlL⟩ := (walkSubgraph (GraphWalk.cons hl r)).exists_isLink_of_mem_edgeSet
          (walk_edges_subset_edgeSet L f hf)
        have hxy := walk_isLink_mem_support L hf hlL
        rw [walkSubgraph_isLink] at hlL
        rcases List.mem_cons.mp hlL.1 with rfl | hfr
        · exfalso
          rcases hl.left_eq_or_eq hlL.2 with rfl | rfl
          · exact haL hxy.1
          · exact haL hxy.2
        · rw [edgeSet_walkSubgraph]; exact hfr
    by_cases hau : a = u
    · cases hau
      by_cases hav : a = v
      · cases hav
        cases L₁ with
        | nil _ =>
          cases L₂ with
          | nil _ => exact ⟨rfl, rfl⟩
          | cons _ r₂ => exact ((List.nodup_cons.mp h₂).1 r₂.end_mem_support).elim
        | cons _ r₁ => exact ((List.nodup_cons.mp h₁).1 r₁.end_mem_support).elim
      · have hva : v ≠ a := Ne.symm hav
        cases L₁ with
        | nil _ => exact (hva rfl).elim
        | @cons _ w₁ _ f₁ hlf₁ r₁ =>
          cases L₂ with
          | nil _ => exact (hva rfl).elim
          | @cons _ w₂ _ f₂ hlf₂ r₂ =>
            obtain ⟨rfl, rfl⟩ := walkSubgraph_only_edge_at_start hl r ha_not hlf₁
            obtain ⟨rfl, rfl⟩ := walkSubgraph_only_edge_at_start hl r ha_not hlf₂
            obtain ⟨r₁', hs₁, he₁⟩ := down_to_r r₁ (List.nodup_cons.mp h₁).1
            obtain ⟨r₂', hs₂, he₂⟩ := down_to_r r₂ (List.nodup_cons.mp h₂).1
            have hr₁s : r₁'.IsSimple := by unfold GraphWalk.IsSimple; rw [hs₁]; exact (List.nodup_cons.mp h₁).2
            have hr₂s : r₂'.IsSimple := by unfold GraphWalk.IsSimple; rw [hs₂]; exact (List.nodup_cons.mp h₂).2
            obtain ⟨hss, hee⟩ := ih hrs r₁' r₂' hr₁s hr₂s
            exact ⟨by simp [← hs₁, ← hs₂, hss], by simp [← he₁, ← he₂, hee]⟩
    · have hua : u ≠ a := Ne.symm hau
      by_cases hav : a = v
      · cases hav
        cases h1_rev : L₁.reverse with
        | nil _ => exact (hua rfl).elim
        | @cons _ w₁ _ f₁ hlf₁ r₁ =>
          cases h2_rev : L₂.reverse with
          | nil _ => exact (hua rfl).elim
          | @cons _ w₂ _ f₂ hlf₂ r₂ =>
            have hr1_s : (GraphWalk.cons hlf₁ r₁).IsSimple := h1_rev ▸ h₁.reverse
            have hr2_s : (GraphWalk.cons hlf₂ r₂).IsSimple := h2_rev ▸ h₂.reverse
            obtain ⟨rfl, rfl⟩ := walkSubgraph_only_edge_at_start hl r ha_not hlf₁
            obtain ⟨rfl, rfl⟩ := walkSubgraph_only_edge_at_start hl r ha_not hlf₂
            obtain ⟨r₁', hs₁, he₁⟩ := down_to_r r₁ (List.nodup_cons.mp hr1_s).1
            obtain ⟨r₂', hs₂, he₂⟩ := down_to_r r₂ (List.nodup_cons.mp hr2_s).1
            have hr₁'s : r₁'.IsSimple := by unfold GraphWalk.IsSimple; rw [hs₁]; exact (List.nodup_cons.mp hr1_s).2
            have hr₂'s : r₂'.IsSimple := by unfold GraphWalk.IsSimple; rw [hs₂]; exact (List.nodup_cons.mp hr2_s).2
            obtain ⟨hss, hee⟩ := ih hrs r₁' r₂' hr₁'s hr₂'s
            have hrev_s : L₁.reverse.support = L₂.reverse.support := by
              rw [h1_rev, h2_rev]; simp [← hs₁, ← hs₂, hss]
            have hrev_e : L₁.reverse.edges = L₂.reverse.edges := by
              rw [h1_rev, h2_rev]; simp [← he₁, ← he₂, hee]
            rw [GraphWalk.support_reverse, GraphWalk.support_reverse, List.reverse_inj] at hrev_s
            rw [GraphWalk.edges_reverse, GraphWalk.edges_reverse, List.reverse_inj] at hrev_e
            exact ⟨hrev_s, hrev_e⟩
      · have hva : v ≠ a := Ne.symm hav
        have ha₁ := not_mem_support_of_walk_walkSubgraph_cons hl r ha_not L₁ h₁ hua hva
        have ha₂ := not_mem_support_of_walk_walkSubgraph_cons hl r ha_not L₂ h₂ hua hva
        obtain ⟨L₁', hs₁, he₁⟩ := down_to_r L₁ ha₁
        obtain ⟨L₂', hs₂, he₂⟩ := down_to_r L₂ ha₂
        have h₁'s : L₁'.IsSimple := by unfold GraphWalk.IsSimple; rw [hs₁]; exact h₁
        have h₂'s : L₂'.IsSimple := by unfold GraphWalk.IsSimple; rw [hs₂]; exact h₂
        obtain ⟨hss, hee⟩ := ih hrs L₁' L₂' h₁'s h₂'s
        exact ⟨hs₁.symm.trans (hss.trans hs₂), he₁.symm.trans (hee.trans he₂)⟩

/-- Every path subgraph $Q \le P$ of a simple walk $W$ is spanned by a contiguous subwalk $W_2$
of $W = W_1 \cdot W_2 \cdot W_3$. -/
theorem exists_contiguous_subwalk_of_isGraphPath {G P Q : Graph α β} {a b : α}
    (W : GraphWalk G a b) (hWs : W.IsSimple)
    (hPV : V(P) = {z | z ∈ W.support}) (hPE : E(P) = {e | e ∈ W.edges})
    (hQP : Q ≤ P) (hQ : IsGraphPath G Q) :
    ∃ (x y : α) (W₁ : GraphWalk G a x) (W₂ : GraphWalk G x y) (W₃ : GraphWalk G y b),
      W = W₁.append (W₂.append W₃) ∧
      V(Q) = {z | z ∈ W₂.support} ∧ E(Q) = {e | e ∈ W₂.edges} := by
  obtain ⟨u, v, hQuv⟩ := hQ
  have huW : u ∈ W.support := by
    have h := hQP.vertexSet_mono hQuv.left_mem
    rwa [hPV] at h
  have hvW : v ∈ W.support := by
    have h := hQP.vertexSet_mono hQuv.right_mem
    rwa [hPV] at h
  obtain ⟨A, B, hAB⟩ := W.exists_append_of_mem huW
  have hvAB : v ∈ A.support ∨ v ∈ B.support := by
    rw [← GraphWalk.mem_support_append, ← hAB]; exact hvW
  have hQ_to_walkSub : ∀ {p q : α}, IsGraphPathWithEnds G Q p q →
      ∀ (W₁ : GraphWalk G a p) (W₂ : GraphWalk G p q) (W₃ : GraphWalk G q b),
        W = W₁.append (W₂.append W₃) →
        V(Q) = {z | z ∈ W₂.support} ∧ E(Q) = {e | e ∈ W₂.edges} := by
    intro p q hQpq W₁ W₂ W₃ hW_eq
    obtain ⟨hQG, W_Q, hW_Qs, hVQ, hEQ⟩ := hQpq
    have hQW : Q ≤ walkSubgraph W := by
      refine ⟨fun z hz => by rw [vertexSet_walkSubgraph, ← hPV]; exact hQP.vertexSet_mono hz,
        fun e z₁ z₂ hl => ?_⟩
      rw [walkSubgraph_isLink]
      have heW : e ∈ W.edges := by
        have h := hQP.edgeSet_mono hl.edge_mem
        rwa [hPE] at h
      exact ⟨heW, hl.mono hQG⟩
    obtain ⟨L₁, hs₁, he₁⟩ := exists_walk_up_of_le hQW W_Q
    have hW₂_le : walkSubgraph W₂ ≤ walkSubgraph W := by
      refine ⟨fun z hz => ?_, fun e z₁ z₂ hl => ?_⟩
      · rw [vertexSet_walkSubgraph] at hz
        rw [vertexSet_walkSubgraph, hW_eq, mem_ofPred_eq, GraphWalk.mem_support_append,
          GraphWalk.mem_support_append]
        exact Or.inr (Or.inl hz)
      · rw [walkSubgraph_isLink] at hl ⊢
        refine ⟨?_, hl.2⟩
        rw [hW_eq, GraphWalk.edges_append, GraphWalk.edges_append]
        exact List.mem_append_right _ (List.mem_append_left _ hl.1)
    obtain ⟨W₂_sub, hs₂_sub, he₂_sub⟩ := exists_walk_walkSubgraph W₂
    obtain ⟨L₂, hs₂, he₂⟩ := exists_walk_up_of_le hW₂_le W₂_sub
    have hW₂s : W₂.IsSimple := (isSimple_of_append (isSimple_of_append (hW_eq ▸ hWs)).2).1
    have hL₁s : L₁.IsSimple := by unfold GraphWalk.IsSimple; rw [hs₁]; exact hW_Qs
    have hL₂s : L₂.IsSimple := by unfold GraphWalk.IsSimple; rw [hs₂, hs₂_sub]; exact hW₂s
    obtain ⟨hss, hee⟩ := walk_walkSubgraph_unique W hWs L₁ L₂ hL₁s hL₂s
    have hs_eq : W_Q.support = W₂.support := hs₁.symm.trans (hss.trans (hs₂.trans hs₂_sub))
    have he_eq : W_Q.edges = W₂.edges := he₁.symm.trans (hee.trans (he₂.trans he₂_sub))
    rw [hVQ, hs_eq, hEQ, he_eq]
    exact ⟨rfl, rfl⟩
  rcases hvAB with hvA | hvB
  · obtain ⟨W₁, W₂, hA_eq⟩ := A.exists_append_of_mem hvA
    have hW_eq : W = W₁.append (W₂.append B) := by rw [hAB, hA_eq, GraphWalk.append_assoc]
    obtain ⟨hV_eq, hE_eq⟩ := hQ_to_walkSub hQuv.symm W₁ W₂ B hW_eq
    exact ⟨v, u, W₁, W₂, B, hW_eq, hV_eq, hE_eq⟩
  · obtain ⟨W₂, W₃, hB_eq⟩ := B.exists_append_of_mem hvB
    have hW_eq : W = A.append (W₂.append W₃) := by rw [hAB, hB_eq]
    obtain ⟨hV_eq, hE_eq⟩ := hQ_to_walkSub hQuv A W₂ W₃ hW_eq
    exact ⟨u, v, A, W₂, W₃, hW_eq, hV_eq, hE_eq⟩

/-! ## 3. Topological Disc-Avoidance for Simple Walks and Monotone Circuit Order -/

private theorem isPreconnected_line_diff_right {S : Type*} [TopologicalSpace S] {L : Set S}
    {a b : S} (hL : IsLineWithEnds L a b) (_hab : a ≠ b) : IsPreconnected (L \ {b}) := by
  obtain ⟨f, hf0, hf1⟩ := hL
  have hEq : L \ {b} = (fun t : unitInterval => (f t).1) '' {t : unitInterval | (t : ℝ) < 1} := by
    ext x
    constructor
    · rintro ⟨hxL, hxb⟩
      obtain ⟨t, ht⟩ := f.surjective ⟨x, hxL⟩
      have ht1 : (t : ℝ) < 1 := by
        refine lt_of_le_of_ne t.2.2 fun h1 => hxb ?_
        have hteq : t = 1 := Subtype.ext h1
        have := congrArg Subtype.val ht
        rw [hteq, hf1] at this
        exact this.symm
      exact ⟨t, ht1, congrArg Subtype.val ht⟩
    · rintro ⟨t, ht1, rfl⟩
      change (t : ℝ) < 1 at ht1
      refine ⟨(f t).2, fun hfb => ?_⟩
      have hteq : f t = f 1 := Subtype.ext (hfb.trans hf1.symm)
      have := congrArg Subtype.val (f.injective hteq)
      simp only [Icc.coe_one] at this
      linarith
  have hpre : IsPreconnected {t : unitInterval | (t : ℝ) < 1} := by
    let g : ℝ → unitInterval :=
      fun s => ⟨max 0 (min 1 s), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
    have hg : Continuous g :=
      Continuous.subtype_mk (continuous_const.max (continuous_const.min continuous_id)) _
    have hsurj : g '' Ico (0 : ℝ) 1 = {t : unitInterval | (t : ℝ) < 1} := by
      ext t
      simp only [mem_image, mem_Ico, mem_ofPred_eq]
      constructor
      · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
        change max 0 (min 1 s) < 1
        rw [min_eq_right hs1.le, max_eq_right hs0]
        exact hs1
      · intro ht
        refine ⟨t.1, ⟨t.2.1, ht⟩, Subtype.ext ?_⟩
        change max 0 (min 1 t.1) = t.1
        rw [min_eq_right ht.le, max_eq_right t.2.1]
    rw [← hsurj]
    exact (convex_Ico (0 : ℝ) 1).isPreconnected.image g hg.continuousOn
  rw [hEq]
  exact hpre.image _ (continuous_subtype_val.comp f.continuous).continuousOn

private theorem walkDrawing_disjoint_circuit_except_end {S : Type*} [TopologicalSpace S] [T2Space S]
    {H C : Drawing S} (hC : C.IsSubdrawing H) {p q : S}
    (U : GraphWalk H.toGraph p q) (hUs : U.IsSimple)
    (honly : ∀ z ∈ U.support, z ∈ C.V → z = q) :
    Disjoint ((walkDrawing H U).U \ {q}) C.U := by
  refine disjoint_left.mpr fun w ⟨hwU, hwq⟩ hwC => ?_
  have hw_inf : w ∈ (Drawing.inf H C (walkDrawing H U)).U := by
    rw [Drawing.inf_U hC (walkDrawing_isSubdrawing H U)]
    exact ⟨hwC, hwU⟩
  by_cases hwV : w ∈ H.V
  · have hwCV : w ∈ C.V := by
      by_contra hnot
      obtain ⟨e, he, hwe⟩ := C.exists_edge_of_mem hwC hnot
      exact ((hC.2 he).2.1 hwe).2 hwV
    have hwUV : w ∈ U.support := by
      by_contra hnot
      have hwUV' : w ∉ (walkDrawing H U).V := by rwa [walkDrawing_V]
      obtain ⟨e, he, hwe⟩ := (walkDrawing H U).exists_edge_of_mem hwU hwUV'
      exact (((walkDrawing_isSubdrawing H U).2 he).2.1 hwe).2 hwV
    exact hwq (honly w hwUV hwCV)
  · have hInf := Drawing.inf_isSubdrawing H C (walkDrawing H U)
    obtain ⟨e, he_inf, hwe⟩ := (Drawing.inf H C (walkDrawing H U)).exists_edge_of_mem hw_inf
      (fun h => hwV (hInf.1 h))
    rw [Drawing.inf_E hC, walkDrawing_E] at he_inf
    obtain ⟨heC, heU⟩ := he_inf
    obtain ⟨x, y, hl⟩ := H.toGraph.exists_isLink_of_mem_edgeSet (walk_edges_subset_edgeSet U e heU)
    have hxy_supp := walk_isLink_mem_support U heU hl
    have hlC : C.toGraph.IsLink e x y := (hC.isLink_iff heC).mpr hl
    have hx_eq : x = q := honly x hxy_supp.1 hlC.left_mem
    have hy_eq : y = q := honly y hxy_supp.2 hlC.right_mem
    subst hx_eq hy_eq
    exact not_isLink_self_of_mem_edges_of_isSimple U hUs heU hl

theorem walkDrawing_outside_disc_except_end {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {H C : Drawing S} (hC : C.IsSubdrawing H)
    {Δ : Set S} (hΔ : IsClosedDisc Δ) (hbd : discBd Δ = C.U)
    {p q : S} (U : GraphWalk H.toGraph p q) (hUs : U.IsSimple)
    (hp_out : p ∉ Δ) (hq_in : q ∈ C.V)
    (honly : ∀ z ∈ U.support, z ∈ C.V → z = q) :
    (walkDrawing H U).U ∩ Δ = {q} := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hqΔ : q ∈ Δ := Surface.discBd_subset Δ (hbd ▸ C.V_subset_U hq_in)
  have hpq : p ≠ q := fun h => hp_out (h ▸ hqΔ)
  have hline : IsLineWithEnds (walkDrawing H U).U p q :=
    GM14.isLine_of_isPathBetween (walkDrawing_isPathBetween H hUs) hpq
  have hpre : IsPreconnected ((walkDrawing H U).U \ {q}) :=
    isPreconnected_line_diff_right hline hpq
  have hdisj_bd : Disjoint ((walkDrawing H U).U \ {q}) (discBd Δ) := by
    rw [hbd]
    exact walkDrawing_disjoint_circuit_except_end hC U hUs honly
  rcases hΔ.side hman hpre hdisj_bd with hin | hout
  · exfalso
    have hp_diff : p ∈ (walkDrawing H U).U \ {q} :=
      ⟨(walkDrawing H U).V_subset_U (by rw [walkDrawing_V]; exact U.start_mem_support), hpq⟩
    exact hp_out (hin hp_diff).1
  · ext z
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hzU, hzΔ⟩
      by_contra hzq
      exact disjoint_left.mp hout ⟨hzU, hzq⟩ hzΔ
    · rintro rfl
      exact ⟨(walkDrawing H U).V_subset_U (by rw [walkDrawing_V]; exact U.end_mem_support), hqΔ⟩

theorem walkDrawing_inside_disc_except_end {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {H C : Drawing S} (hC : C.IsSubdrawing H)
    {Δ : Set S} (hΔ : IsClosedDisc Δ) (hbd : discBd Δ = C.U)
    {p q : S} (U : GraphWalk H.toGraph p q) (hUs : U.IsSimple)
    (hp_in : p ∈ discInt Δ) (hq_bd : q ∈ C.V)
    (honly : ∀ z ∈ U.support, z ∈ C.V → z = q) :
    (walkDrawing H U).U ⊆ Δ ∧ (walkDrawing H U).U ∩ discBd Δ = {q} := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hq_discBd : q ∈ discBd Δ := hbd ▸ C.V_subset_U hq_bd
  have hpq : p ≠ q := fun h => hp_in.2 (h ▸ hq_discBd)
  have hline : IsLineWithEnds (walkDrawing H U).U p q :=
    GM14.isLine_of_isPathBetween (walkDrawing_isPathBetween H hUs) hpq
  have hpre : IsPreconnected ((walkDrawing H U).U \ {q}) :=
    isPreconnected_line_diff_right hline hpq
  have hdisj_bd : Disjoint ((walkDrawing H U).U \ {q}) (discBd Δ) := by
    rw [hbd]
    exact walkDrawing_disjoint_circuit_except_end hC U hUs honly
  rcases hΔ.side hman hpre hdisj_bd with hin | hout
  · refine ⟨fun z hz => ?_, ?_⟩
    · by_cases hzq : z = q
      · exact hzq ▸ Surface.discBd_subset Δ hq_discBd
      · exact (hin ⟨hz, hzq⟩).1
    · ext z
      simp only [mem_inter_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hzU, hzbd⟩
        by_contra hzq
        exact (hin ⟨hzU, hzq⟩).2 hzbd
      · rintro rfl
        exact ⟨(walkDrawing H U).V_subset_U (by rw [walkDrawing_V]; exact U.end_mem_support), hq_discBd⟩
  · exfalso
    have hp_diff : p ∈ (walkDrawing H U).U \ {q} :=
      ⟨(walkDrawing H U).V_subset_U (by rw [walkDrawing_V]; exact U.start_mem_support), hpq⟩
    exact disjoint_left.mp hout hp_diff hp_in.1

/-! ## 4. Angle Sorting on `Circle` and Subdrawing Path Extraction -/

private theorem circle_exp_inj_of_abs_lt_two_pi {s t : ℝ}
    (h : |s - t| < 2 * Real.pi) (heq : Circle.exp s = Circle.exp t) : s = t := by
  by_contra hne
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp heq
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2pi : 0 < 2 * Real.pi := by linarith
  have hdiff : s - t = m * (2 * Real.pi) := by linarith
  have habs : |(m : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
    calc |(m : ℝ)| * (2 * Real.pi) = |(m : ℝ)| * |2 * Real.pi| := by rw [abs_of_pos h2pi]
      _ = |(m : ℝ) * (2 * Real.pi)| := (abs_mul _ _).symm
      _ = |s - t| := by rw [← hdiff]
      _ < 2 * Real.pi := h
  have hm_abs : |(m : ℝ)| < 1 := by nlinarith
  have hm0 : m = 0 := by
    have h1 : (-1 : ℝ) < m := by linarith [neg_abs_le (m : ℝ)]
    have h2 : (m : ℝ) < 1 := lt_of_le_of_lt (le_abs_self _) hm_abs
    have h1' : (-1 : ℤ) < m := by exact_mod_cast h1
    have h2' : m < (1 : ℤ) := by exact_mod_cast h2
    omega
  rw [hm0] at hdiff
  simp at hdiff
  exact hne (sub_eq_zero.mp hdiff)

theorem exists_circle_spoke_params {S : Type*} [TopologicalSpace S] [T2Space S]
    {F : Set S} (hF : IsOArc F) {r : ℕ} (hr : 2 ≤ r) {t : Fin r → S}
    (ht_mem : ∀ i : Fin r, t i ∈ F) (ht_inj : Function.Injective t) :
    ∃ (σ : Equiv.Perm (Fin r)) (B : Fin r → Set S) (τ : Fin r → ℝ → S),
      ∀ k : Fin r,
        IsParam (B k) (t (σ k)) (t (σ (nextSpoke k))) (τ k) ∧
        B k ⊆ F ∧
        ∀ i : Fin r, i ≠ σ k → i ≠ σ (nextSpoke k) → t i ∉ B k := by
  obtain ⟨φ⟩ := hF
  have hr0 : 0 < r := by omega
  let θ : Fin r → ℝ := fun i => Complex.arg (φ.symm ⟨t i, ht_mem i⟩ : Circle)
  have hexp : ∀ i : Fin r, (φ (Circle.exp (θ i))).1 = t i := by
    intro i
    simp [θ, Circle.exp_arg]
  have hrange : ∀ i : Fin r, -Real.pi < θ i ∧ θ i ≤ Real.pi := fun i =>
    ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  have hθ_inj : Function.Injective θ := fun i₁ i₂ h =>
    ht_inj (by rw [← hexp i₁, ← hexp i₂, h])
  let rel : Fin r → Fin r → Prop := fun u v => θ u ≤ θ v
  let _ : DecidableRel rel := Classical.decRel _
  have _ : Std.Total rel := ⟨fun _ _ => le_total _ _⟩
  have _ : IsTrans (Fin r) rel := ⟨fun _ _ _ => le_trans⟩
  let L₀ : List (Fin r) := List.finRange r
  let L : List (Fin r) := L₀.insertionSort rel
  have hlen : L.length = r := by
    rw [(List.perm_insertionSort rel L₀).length_eq, List.length_finRange]
  have hnd : L.Nodup :=
    (List.perm_insertionSort rel L₀).nodup_iff.mpr (List.nodup_finRange r)
  have hpw : L.Pairwise rel := List.pairwise_insertionSort rel L₀
  let σ_fn : Fin r → Fin r := fun k => L[k.1]'(Nat.lt_of_lt_of_eq k.2 hlen.symm)
  have hσ_inj : Function.Injective σ_fn := by
    intro k₁ k₂ h
    have := (List.Nodup.getElem_inj_iff hnd).mp h
    exact Fin.ext this
  let σ : Equiv.Perm (Fin r) := Equiv.ofBijective σ_fn (Finite.injective_iff_bijective.mp hσ_inj)
  have hσ_apply : ∀ k : Fin r, σ k = L[k.1]'(Nat.lt_of_lt_of_eq k.2 hlen.symm) := fun _ => rfl
  have hθ_strict : ∀ k₁ k₂ : Fin r, k₁ < k₂ → θ (σ k₁) < θ (σ k₂) := by
    intro k₁ k₂ hk
    have hle : θ (σ k₁) ≤ θ (σ k₂) :=
      List.pairwise_iff_getElem.mp hpw k₁.1 k₂.1
        (Nat.lt_of_lt_of_eq k₁.2 hlen.symm) (Nat.lt_of_lt_of_eq k₂.2 hlen.symm) hk
    exact lt_of_le_of_ne hle fun heq => hk.ne (σ.injective (hθ_inj heq))
  let a_ang : Fin r → ℝ := fun k => θ (σ k)
  let b_ang : Fin r → ℝ := fun k =>
    if k.1 + 1 < r then θ (σ (nextSpoke k)) else θ (σ ⟨0, hr0⟩) + 2 * Real.pi
  have hab_bounds : ∀ k : Fin r, 0 < b_ang k - a_ang k ∧ b_ang k - a_ang k < 2 * Real.pi := by
    intro k
    dsimp [a_ang, b_ang]
    split_ifs with hk
    · have hnext : nextSpoke k = ⟨k.1 + 1, hk⟩ := by
        ext; dsimp [nextSpoke]; exact Nat.mod_eq_of_lt hk
      have hlt : k < nextSpoke k := by rw [hnext]; exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self _)
      have h1 := hθ_strict k (nextSpoke k) hlt
      have hr1 := hrange (σ k)
      have hr2 := hrange (σ (nextSpoke k))
      constructor <;> linarith
    · have hk_eq : k.1 = r - 1 := by have := k.2; omega
      have h0k : (⟨0, hr0⟩ : Fin r) < k := Fin.mk_lt_mk.mpr (by omega)
      have h1 := hθ_strict ⟨0, hr0⟩ k h0k
      have hr1 := hrange (σ ⟨0, hr0⟩)
      have hr2 := hrange (σ k)
      constructor <;> linarith
  let τ : Fin r → ℝ → S := fun k m =>
    (φ (Circle.exp (a_ang k + m * (b_ang k - a_ang k)))).1
  let B : Fin r → Set S := fun k => τ k '' Icc 0 1
  refine ⟨σ, B, τ, fun k => ?_⟩
  have hcont : Continuous (τ k) :=
    continuous_subtype_val.comp (φ.continuous.comp (Circle.exp.continuous.comp (by fun_prop)))
  have hinj : InjOn (τ k) (Icc 0 1) := by
    intro m₁ hm₁ m₂ hm₂ heq
    have hcexp : Circle.exp (a_ang k + m₁ * (b_ang k - a_ang k)) =
        Circle.exp (a_ang k + m₂ * (b_ang k - a_ang k)) :=
      φ.injective (Subtype.ext heq)
    obtain ⟨hpos, hlt2pi⟩ := hab_bounds k
    have habs_m : |m₁ - m₂| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hm₁.1, hm₁.2, hm₂.1, hm₂.2]
    have habs_ang : |(a_ang k + m₁ * (b_ang k - a_ang k)) -
        (a_ang k + m₂ * (b_ang k - a_ang k))| < 2 * Real.pi := by
      have heq_d : (a_ang k + m₁ * (b_ang k - a_ang k)) -
          (a_ang k + m₂ * (b_ang k - a_ang k)) = (m₁ - m₂) * (b_ang k - a_ang k) := by ring
      rw [heq_d, abs_mul, abs_of_pos hpos]
      nlinarith
    have hlin := circle_exp_inj_of_abs_lt_two_pi habs_ang hcexp
    nlinarith
  have hτ0 : τ k 0 = t (σ k) := by
    dsimp [τ, a_ang]; simp [hexp]
  have hτ1 : τ k 1 = t (σ (nextSpoke k)) := by
    dsimp [τ, a_ang, b_ang]
    have hring : ∀ x y : ℝ, x + 1 * (y - x) = y := fun x y => by ring
    rw [hring]
    split_ifs with hk
    · exact hexp _
    · have hnext0 : nextSpoke k = ⟨0, hr0⟩ := by
        ext; dsimp [nextSpoke]
        have : k.1 + 1 = r := by have := k.2; omega
        rw [this, Nat.mod_self]
      rw [hnext0]
      have hper : Circle.exp (θ (σ ⟨0, hr0⟩) + 2 * Real.pi) = Circle.exp (θ (σ ⟨0, hr0⟩)) :=
        Circle.exp_eq_exp.mpr ⟨1, by push_cast; ring⟩
      rw [hper, hexp]
  refine ⟨⟨hcont.continuousOn, hinj, rfl, hτ0, hτ1⟩, ?_, ?_⟩
  · rintro _ ⟨m, _, rfl⟩
    exact (φ _).2
  · intro i hi1 hi2 ⟨m, hm, hm_eq⟩
    let idx := σ.symm i
    have hi_σ : σ idx = i := σ.apply_symm_apply i
    have hidx1 : idx ≠ k := fun h => hi1 (by rw [← hi_σ, h])
    have hidx2 : idx ≠ nextSpoke k := fun h => hi2 (by rw [← hi_σ, h])
    have hcexp : Circle.exp (a_ang k + m * (b_ang k - a_ang k)) = Circle.exp (θ (σ idx)) := by
      apply φ.injective
      ext
      exact hm_eq.trans (hexp i).symm |>.trans (by rw [hi_σ])
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hcexp
    have hpi : 0 < Real.pi := Real.pi_pos
    obtain ⟨hpos, _⟩ := hab_bounds k
    have hlow : a_ang k ≤ a_ang k + m * (b_ang k - a_ang k) := by nlinarith [hm.1]
    have hhigh : a_ang k + m * (b_ang k - a_ang k) ≤ b_ang k := by nlinarith [hm.2]
    dsimp [a_ang, b_ang] at hlow hhigh hn
    split_ifs at hlow hhigh hn with hk
    · have hnext : nextSpoke k = ⟨k.1 + 1, hk⟩ := by
        ext; dsimp [nextSpoke]; exact Nat.mod_eq_of_lt hk
      have hr_k := hrange (σ k)
      have hr_nk := hrange (σ (nextSpoke k))
      have hr_idx := hrange (σ idx)
      have hn1 : (-1 : ℝ) < n := by nlinarith
      have hn2 : (n : ℝ) < 1 := by nlinarith
      have hn1' : (-1 : ℤ) < n := by exact_mod_cast hn1
      have hn2' : n < (1 : ℤ) := by exact_mod_cast hn2
      have hn0 : n = 0 := by omega
      rw [hn0] at hn
      simp at hn
      have hθ_le1 : θ (σ k) ≤ θ (σ idx) := by linarith
      have hθ_le2 : θ (σ idx) ≤ θ (σ (nextSpoke k)) := by linarith
      have hk_le : k ≤ idx := by
        by_contra hlt; push Not at hlt
        linarith [hθ_strict idx k hlt]
      have hidx_le : idx ≤ nextSpoke k := by
        by_contra hlt; push Not at hlt
        linarith [hθ_strict (nextSpoke k) idx hlt]
      rw [hnext] at hidx_le hidx2
      have : idx.1 = k.1 ∨ idx.1 = k.1 + 1 := by
        have h1 : k.1 ≤ idx.1 := hk_le
        have h2 : idx.1 ≤ k.1 + 1 := hidx_le
        omega
      rcases this with h_eq | h_eq
      · exact hidx1 (Fin.ext h_eq)
      · exact hidx2 (Fin.ext h_eq)
    · have hk_last : k.1 = r - 1 := by have := k.2; omega
      have hnext0 : nextSpoke k = ⟨0, hr0⟩ := by
        ext; dsimp [nextSpoke]
        have : k.1 + 1 = r := by have := k.2; omega
        rw [this, Nat.mod_self]
      have h0_lt_idx : (⟨0, hr0⟩ : Fin r) < idx :=
        lt_of_le_of_ne (Fin.mk_le_mk.mpr (Nat.zero_le _)) (Ne.symm (hnext0 ▸ hidx2))
      have hidx_lt_k : idx < k := by
        refine lt_of_le_of_ne (Fin.mk_le_mk.mpr ?_) hidx1
        have := idx.2; omega
      have hθ1 := hθ_strict ⟨0, hr0⟩ idx h0_lt_idx
      have hθ2 := hθ_strict idx k hidx_lt_k
      rcases le_or_gt n 0 with hn_le | hn_gt
      · have hn_le' : (n : ℝ) ≤ 0 := by exact_mod_cast hn_le
        nlinarith
      · have hn_ge1 : (1 : ℤ) ≤ n := by omega
        have hn_ge1' : (1 : ℝ) ≤ n := by exact_mod_cast hn_ge1
        nlinarith

/-- Given a circuit subdrawing `N`, pairwise disjoint connected subdrawings `R i` of `N` with
`t i ∈ (R i).V`, and a parametrized line `P ⊆ N.U` from `t l` to `t r` (`l ≠ r`) avoiding all other
`t i`, extract a path subdrawing `A` of `N` between some `u ∈ (R l).V` and `w ∈ (R r).V` (`u ≠ w`)
whose point set `A.U` meets `⋃ i, (R i).U` only at `{u, w}`. -/
theorem exists_spoke_arc_subdrawing {S : Type*} [TopologicalSpace S] [T2Space S]
    {N : Drawing S} (hN_circ : N.IsCircuit) {ι : Type*} {R : ι → Drawing S} {t : ι → S}
    (hR_sub : ∀ i, (R i).IsSubdrawing N)
    (hR_conn : ∀ i, IsPreconnected (R i).U)
    (hR_disj : ∀ i i', i ≠ i' → Disjoint (R i).U (R i').U)
    (ht : ∀ i, t i ∈ (R i).V) {l r : ι} (hlr : l ≠ r)
    {τ : ℝ → S} {P : Set S} (hτ : IsParam P (t l) (t r) τ) (hP : P ⊆ N.U)
    (hoff : ∀ i, i ≠ l → i ≠ r → t i ∉ P) :
    ∃ (A : Drawing S) (u w : S),
      A.IsSubdrawing N ∧ u ∈ (R l).V ∧ w ∈ (R r).V ∧ u ≠ w ∧
      A.IsPathBetween u w ∧ IsLineWithEnds A.U u w ∧ A.U ⊆ P ∧
      A.U ∩ (⋃ i, (R i).U) = {u, w} := by
  have hOArc : IsOArc N.U := IsCircuit.isOArc_U hN_circ
  obtain ⟨a', b', ha'0, hab', hb'1, hsp⟩ :=
    GM07.exists_top_split hOArc hR_sub hR_conn hR_disj ht hlr hτ hP hoff
  have hmem01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 ∧ (1 : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨⟨le_rfl, zero_le_one⟩, zero_le_one, le_rfl⟩
  have hcomp : ∀ i, IsCompact {m | m ∈ Icc (0 : ℝ) 1 ∧ τ m ∈ (R i).U} := fun i =>
    isCompact_Icc.of_isClosed_subset
      (hτ.cont.preimage_isClosed_of_isClosed isClosed_Icc (R i).isClosed_U) inter_subset_left
  obtain ⟨a, ⟨haI, haR⟩, hamax⟩ := (hcomp l).exists_isMaxOn
    ⟨0, hmem01.1, by rw [hτ.zero]; exact (R l).V_subset_U (ht l)⟩ continuous_id.continuousOn
  obtain ⟨b, ⟨hbI, hbR⟩, hbmin⟩ := (hcomp r).exists_isMinOn
    ⟨1, hmem01.2, by rw [hτ.one]; exact (R r).V_subset_U (ht r)⟩ continuous_id.continuousOn
  have ha_le : a ≤ a' := by
    rcases hsp a haI l haR with ⟨_, hle⟩ | ⟨hlr_eq, _⟩
    · exact hle
    · exact (hlr hlr_eq).elim
  have hb_ge : b' ≤ b := by
    rcases hsp b hbI r hbR with ⟨hrl_eq, _⟩ | ⟨_, hge⟩
    · exact (hlr hrl_eq.symm).elim
    · exact hge
  have hab : a < b := lt_of_le_of_lt ha_le (lt_of_lt_of_le hab' hb_ge)
  have hno_inner : ∀ m ∈ Icc a b, ∀ i, τ m ∈ (R i).U → (i = l ∧ m = a) ∨ (i = r ∧ m = b) := by
    intro m hm i hi
    have hm01 : m ∈ Icc (0 : ℝ) 1 := ⟨haI.1.trans hm.1, hm.2.trans hbI.2⟩
    rcases hsp m hm01 i hi with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact Or.inl ⟨rfl, le_antisymm (hamax ⟨hm01, hi⟩) hm.1⟩
    · exact Or.inr ⟨rfl, le_antisymm hm.2 (hbmin ⟨hm01, hi⟩)⟩
  let u := τ a
  let w := τ b
  have huw : u ≠ w := fun heq => by
    change τ a = τ b at heq
    exact Set.disjoint_left.mp (hR_disj l r hlr) haR (heq ▸ hbR)
  have end_in_V : ∀ {c : ℝ} {k : ι}, c ∈ Icc (0 : ℝ) 1 → τ c ∈ (R k).U →
      (∀ m ∈ Ioo a b, τ m ∉ (R k).U) → (c = a ∨ c = b) → τ c ∈ (R k).V := by
    intro c k hcI hcR hmiss hcab
    by_contra hcRV
    have hcNV : τ c ∉ N.V := by
      intro hcNV
      obtain ⟨e, he, hce⟩ := (R k).exists_edge_of_mem hcR hcRV
      exact edge_notMem_V ((hR_sub k).2 he) hce hcNV
    obtain ⟨e, heR, hce⟩ := (R k).exists_edge_of_mem hcR hcRV
    have heN : e ∈ N.E := (hR_sub k).2 heR
    let K : Set S := N.V ∪ ⋃ f ∈ N.E \ {e}, closure f
    have hK_closed : IsClosed K :=
      N.finite_V.isClosed.union
        ((N.finite_edges.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure)
    have hIoo_K : τ '' Ioo a b ⊆ K := by
      rintro _ ⟨m, hm, rfl⟩
      have hm01 : m ∈ Icc (0 : ℝ) 1 := ⟨haI.1.trans hm.1.le, hm.2.le.trans hbI.2⟩
      have hmU : τ m ∈ N.U := hP (hτ.mem hm01)
      rw [N.U_eq] at hmU
      rcases hmU with hmV | hmE
      · exact Or.inl hmV
      · obtain ⟨f, hfN, hmf⟩ := mem_iUnion₂.mp hmE
        have hfe : f ≠ e := by
          intro hfe_eq
          subst hfe_eq
          have hcl_sub : closure f ⊆ (R k).U := by
            rw [(R k).U_eq]
            exact subset_biUnion_of_mem (u := fun g => closure g) heR |>.trans subset_union_right
          exact hmiss m hm (hcl_sub hmf)
        exact Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hfN, hfe⟩, hmf⟩)
    have hc_cl_Ioo : c ∈ closure (Ioo a b) := by
      rw [closure_Ioo hab.ne]
      rcases hcab with rfl | rfl
      · exact ⟨le_rfl, hab.le⟩
      · exact ⟨hab.le, le_rfl⟩
    have hIoo_sub : Ioo a b ⊆ Icc (0 : ℝ) 1 :=
      fun m hm => ⟨haI.1.trans hm.1.le, hm.2.le.trans hbI.2⟩
    have hc_cl_img : τ c ∈ closure (τ '' Ioo a b) := by
      have hcont_ab : ContinuousOn τ (closure (Ioo a b)) := by
        rw [closure_Ioo hab.ne]
        exact hτ.cont.mono (Icc_subset_Icc haI.1 hbI.2)
      exact hcont_ab.image_closure (mem_image_of_mem τ hc_cl_Ioo)
    have hcK : τ c ∈ K := closure_minimal hIoo_K hK_closed hc_cl_img
    rcases hcK with hcV | hcF
    · exact hcNV hcV
    · obtain ⟨f, ⟨hfN, hfe⟩, hcf⟩ := mem_iUnion₂.mp hcF
      have hcf' : τ c ∈ f := by rw [← N.closure_diff_V hfN]; exact ⟨hcf, hcNV⟩
      exact hfe (N.edge_eq_of_mem hfN heN hcf' hce)
  have huV : u ∈ (R l).V := end_in_V haI haR
    (fun m hm h => by
      rcases hno_inner m ⟨hm.1.le, hm.2.le⟩ l h with ⟨_, hma⟩ | ⟨hlr_eq, _⟩
      · exact hm.1.ne' hma
      · exact hlr hlr_eq) (Or.inl rfl)
  have hwV : w ∈ (R r).V := end_in_V hbI hbR
    (fun m hm h => by
      rcases hno_inner m ⟨hm.1.le, hm.2.le⟩ r h with ⟨hrl_eq, _⟩ | ⟨_, hmb⟩
      · exact hlr hrl_eq.symm
      · exact hm.2.ne hmb) (Or.inr rfl)
  let B : Set S := τ '' Icc a b
  have hsub_ab : Icc a b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc haI.1 hbI.2
  have hB_line : IsLineWithEnds B u w :=
    isLineWithEnds_image (GM07.isLine_Icc hab) (hτ.cont.mono hsub_ab) (hτ.inj.mono hsub_ab)
  have hB_sub : B ⊆ N.U := fun _ ⟨m, hm, heq⟩ => heq ▸ hP (hτ.mem (hsub_ab hm))
  let A : Drawing S := N.span (N.V ∩ B) {e ∈ N.E | e ⊆ B}
  have hA_sub : A.IsSubdrawing N := N.span_isSubdrawing _ _
  have huNV : u ∈ N.V := (hR_sub l).1 huV
  have hwNV : w ∈ N.V := (hR_sub r).1 hwV
  have hA_U : A.U = B := by
    change N.spanU (N.V ∩ B) {e ∈ N.E | e ⊆ B} = B
    apply Subset.antisymm
    · refine union_subset (union_subset ?_ (iUnion₂_subset ?_)) (iUnion₂_subset ?_)
      · exact fun x hx => hx.1.2
      · intro e he x hx
        exact hB_line.isCompact.isClosed.closure_subset_iff.mpr he.1.2 hx.1
      · intro e he
        exact hB_line.isCompact.isClosed.closure_subset_iff.mpr he.1.2
    · intro x hxB
      by_cases hxV : x ∈ N.V
      · exact Or.inl (Or.inl ⟨⟨hxV, hxB⟩, hxV⟩)
      · obtain ⟨e, heN, hxe⟩ := N.exists_edge_of_mem (hB_sub hxB) hxV
        have he_sub : e ⊆ B :=
          GM07.subset_line_or_off hOArc hB_line hB_sub huw heN.2.2.1.isConnected.isPreconnected
            (heN.2.1.trans sdiff_subset)
            (fun hu_e => (heN.2.1 hu_e).2 huNV)
            (fun hw_e => (heN.2.1 hw_e).2 hwNV) hxe hxB
        exact Or.inr (mem_iUnion₂.mpr ⟨e, ⟨⟨heN, he_sub⟩, heN⟩, subset_closure hxe⟩)
  have huAV : u ∈ A.V := Or.inl ⟨⟨huNV, hB_line.left_mem⟩, huNV⟩
  have hwAV : w ∈ A.V := Or.inl ⟨⟨hwNV, hB_line.right_mem⟩, hwNV⟩
  have hA_line : IsLineWithEnds A.U u w := hA_U.symm ▸ hB_line
  have hA_path : A.IsPathBetween u w :=
    GM16.drawing_isPathBetween_of_isLine_U hA_line huw huAV hwAV
  refine ⟨A, u, w, hA_sub, huV, hwV, huw, hA_path, hA_line,
    hA_U ▸ fun _ ⟨m, hm, heq⟩ => heq ▸ hτ.mem (hsub_ab hm), ?_⟩
  rw [hA_U]
  ext z
  simp only [mem_inter_iff, mem_iUnion, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨⟨m, hm, rfl⟩, i, hi⟩
    rcases hno_inner m hm i hi with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨hB_line.left_mem, l, haR⟩
    · exact ⟨hB_line.right_mem, r, hbR⟩

/-! ## 5. Combined Nested Walk Decomposition and Circle-Piece Data -/

/-- A path in $G$ cannot contain every edge of a circuit $C \le G$. -/
theorem exists_edge_diff_of_circuit_of_path {G C Q : Graph α β}
    (hC : IsGraphCircuit G C) (hQ : IsGraphPath G Q) :
    ∃ e ∈ E(C), e ∉ E(Q) := by
  by_contra hno
  push Not at hno
  obtain ⟨hCG, u₀, W_C, hWC_sc, hWC_pos, hVC, hEC⟩ := hC
  obtain ⟨a, b, hQG, W_Q, hWQ_s, hVQ, hEQ⟩ := hQ
  have hCQ : C ≤ Q := by
    refine ⟨fun x hx => ?_, fun e x y hl => ?_⟩
    · rw [hVC, mem_ofPred_eq] at hx
      cases W_C with
      | nil _ => simp at hWC_pos
      | @cons _ w _ f hlf rC =>
        have hfQ : f ∈ E(Q) := hno f (by rw [hEC]; simp)
        obtain ⟨p, q, hlQ⟩ := Q.exists_isLink_of_mem_edgeSet hfQ
        rcases List.mem_cons.mp hx with rfl | hxr
        · rcases (hlf.mono hCG).left_eq_or_eq (hlQ.mono hQG) with rfl | rfl
          · exact hlQ.left_mem
          · exact hlQ.right_mem
        · by_cases hxr_end : x = u₀
          · subst hxr_end
            rcases (hlf.mono hCG).left_eq_or_eq (hlQ.mono hQG) with rfl | rfl
            · exact hlQ.left_mem
            · exact hlQ.right_mem
          · obtain ⟨A, B, hsplit⟩ := rC.exists_append_of_mem hxr
            cases B with
            | nil _ => exact (hxr_end rfl).elim
            | @cons _ z _ g hlg _ =>
              have hgC : g ∈ E(C) := by
                rw [hEC, mem_ofPred_eq]
                simp [hsplit, GraphWalk.edges_append]
              obtain ⟨p', q', hlQ'⟩ := Q.exists_isLink_of_mem_edgeSet (hno g hgC)
              rcases (hlg.mono hCG).left_eq_or_eq (hlQ'.mono hQG) with rfl | rfl
              · exact hlQ'.left_mem
              · exact hlQ'.right_mem
    · exact (hQG.isLink_iff (hno e hl.edge_mem)).mpr (hl.mono hCG)
  obtain ⟨W_CQ, hs_CQ, he_CQ⟩ := exists_walk_up_of_le hCQ W_C
  cases W_CQ with
  | nil _ =>
    cases W_C with
    | nil _ => simp at hWC_pos
    | cons _ _ => simp at he_CQ
  | @cons _ w _ e₀ hl₀ r₀ =>
    have he₀_not_r₀ : e₀ ∉ r₀.edges := by
      have hed : W_C.edges.Nodup := hWC_sc.2
      rw [← he_CQ] at hed
      exact (List.nodup_cons.mp hed).1
    have hr₀_s : r₀.IsSimple := by
      have h1 : W_C.support.tail.Nodup := hWC_sc.1
      rw [← hs_CQ] at h1
      exact h1
    have hle_QW : Q ≤ walkSubgraph W_Q := by
      refine ⟨fun z hz => by rw [vertexSet_walkSubgraph, ← hVQ]; exact hz, fun f x y hlf => ?_⟩
      rw [walkSubgraph_isLink]
      have hfE : f ∈ E(Q) := hlf.edge_mem
      rw [hEQ] at hfE
      exact ⟨hfE, hlf⟩
    by_cases hwu : w = u₀
    · subst hwu
      have hloop_in_WQ : e₀ ∈ W_Q.edges := by
        have heE : e₀ ∈ E(Q) := hl₀.edge_mem
        rwa [hEQ] at heE
      exact not_isLink_self_of_mem_edges_of_isSimple W_Q hWQ_s hloop_in_WQ hl₀
    · obtain ⟨L₁, hs₁, he₁⟩ := exists_walk_up_of_le hle_QW (GraphWalk.cons hl₀ (.nil hl₀.right_mem))
      obtain ⟨L₂, hs₂, he₂⟩ := exists_walk_up_of_le hle_QW r₀.reverse
      have hL₁s : L₁.IsSimple := by
        unfold GraphWalk.IsSimple; rw [hs₁]; simp [Ne.symm hwu]
      have hL₂s : L₂.IsSimple := by
        unfold GraphWalk.IsSimple; rw [hs₂]; exact hr₀_s.reverse
      obtain ⟨_, hee⟩ := walk_walkSubgraph_unique W_Q hWQ_s L₁ L₂ hL₁s hL₂s
      have he_eq : [e₀] = r₀.reverse.edges := he₁.symm.trans (hee.trans he₂)
      have he₀_in : e₀ ∈ r₀.reverse.edges := by rw [← he_eq]; simp
      rw [GraphWalk.edges_reverse, List.mem_reverse] at he₀_in
      exact he₀_not_r₀ he₀_in

/-- Complete ordered walk and circle-piece structure for nested circuits $C_1, \dots, C_s$ and
$r \ge 1$ vertex-disjoint paths $P_1, \dots, P_r$ with $P_i \cap C_j$ a path for all $i, j$. -/
structure OrderedNestedCylinderData {G : Graph α β} (M : PlanarDrawing G) (r s : ℕ)
    (hs : 0 < s) (C : Fin s → Graph α β) (P : Fin r → Graph α β) where
  /-- Outer endpoint $a_i \in V(C_0)$ of $P_i$. -/
  a : Fin r → α
  /-- Inner endpoint $b_i \in V(C_{s - 1})$ of $P_i$. -/
  b : Fin r → α
  /-- Simple walk $W_i$ spanning $P_i$ from $a_i$ to $b_i$. -/
  W : ∀ i : Fin r, GraphWalk G (a i) (b i)
  W_simple : ∀ i : Fin r, (W i).IsSimple
  a_mem : ∀ i : Fin r, a i ∈ V(C ⟨0, hs⟩)
  b_mem : ∀ i : Fin r, b i ∈ V(C ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩)
  P_V : ∀ i : Fin r, V(P i) = {z | z ∈ (W i).support}
  P_E : ∀ i : Fin r, E(P i) = {e | e ∈ (W i).edges}
  /-- Entry vertex $x_{i, j}$ of $P_i$ on $C_j$. -/
  x : Fin r → Fin s → α
  /-- Exit vertex $y_{i, j}$ of $P_i$ on $C_j$. -/
  y : Fin r → Fin s → α
  W_pre : ∀ (i : Fin r) (j : Fin s), GraphWalk G (a i) (x i j)
  W_mid : ∀ (i : Fin r) (j : Fin s), GraphWalk G (x i j) (y i j)
  W_post : ∀ (i : Fin r) (j : Fin s), GraphWalk G (y i j) (b i)
  W_split : ∀ (i : Fin r) (j : Fin s),
    W i = (W_pre i j).append ((W_mid i j).append (W_post i j))
  mid_V : ∀ (i : Fin r) (j : Fin s), {z | z ∈ (W_mid i j).support} = V(P i) ∩ V(C j)
  mid_E : ∀ (i : Fin r) (j : Fin s), {e | e ∈ (W_mid i j).edges} = E(P i) ∩ E(C j)
  x_zero : ∀ i : Fin r, x i ⟨0, hs⟩ = a i
  y_last : ∀ i : Fin r, y i ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ = b i
  /-- Radial subwalk from $y_{i, j_1}$ to $x_{i, j_2}$ whenever $j_1 < j_2$. -/
  between_post : ∀ (i : Fin r) {j₁ j₂ : Fin s}, j₁ < j₂ →
    ∃ R : GraphWalk G (y i j₁) (x i j₂),
      W_post i j₁ = R.append ((W_mid i j₂).append (W_post i j₂))
  /-- Consistent cyclic permutation $\sigma$ of the $r$ spokes across all $s$ circuits. -/
  σ : Equiv.Perm (Fin r)
  /-- Connected piece of $C_j$ contracted into spoke $k$ on circle $j$. -/
  K_circ : Fin r → Fin s → Graph α β
  /-- Retained circular edge of $C_j$ linking spoke $k$ to `nextSpoke k`. -/
  e_circ : Fin r → Fin s → β
  K_circ_le : ∀ (k : Fin r) (j : Fin s),
    K_circ k j ≤ (C j).deleteEdges (Set.range fun m => e_circ m j)
  K_circ_conn : ∀ (k : Fin r) (j : Fin s), GraphConnected (K_circ k j)
  inter_sub_K_circ : ∀ (k : Fin r) (j : Fin s),
    V(P (σ k)) ∩ V(C j) ⊆ V(K_circ k j)
  K_circ_disj : ∀ (j : Fin s) {k₁ k₂ : Fin r}, k₁ ≠ k₂ →
    Disjoint V(K_circ k₁ j) V(K_circ k₂ j)
  e_circ_inj : ∀ (j : Fin s), Function.Injective (fun m => e_circ m j)
  e_circ_link : ∀ (k : Fin r) (j : Fin s),
    ∃ u ∈ V(K_circ k j), ∃ w ∈ V(K_circ (nextSpoke k) j), (C j).IsLink (e_circ k j) u w

theorem graphConnected_of_walk {H : Graph α β} {u₀ : α} (hu₀ : u₀ ∈ V(H))
    (hreach : ∀ z ∈ V(H), Nonempty (GraphWalk H u₀ z)) : GraphConnected H := by
  refine ⟨⟨u₀, hu₀⟩, fun x hx y hy => ?_⟩
  obtain ⟨Wx⟩ := hreach x hx
  obtain ⟨Wy⟩ := hreach y hy
  have hwalk : ∀ {p q : α} (W : GraphWalk H p q), Relation.ReflTransGen H.Adj p q := by
    intro p q W
    induction W with
    | nil _ => exact .refl
    | @cons a b c e hl r ih => exact Relation.ReflTransGen.head ⟨e, hl⟩ ih
  exact hwalk (Wx.reverse.append Wy)

theorem graphConnected_walkSubgraph {G : Graph α β} {a b : α} (W : GraphWalk G a b) :
    GraphConnected (walkSubgraph W) := by
  obtain ⟨W', hs, _⟩ := exists_walk_walkSubgraph W
  refine graphConnected_of_walk (by rw [vertexSet_walkSubgraph]; exact W.start_mem_support)
    fun z hz => ?_
  rw [vertexSet_walkSubgraph, mem_ofPred_eq, ← hs] at hz
  obtain ⟨A, _, _⟩ := W'.exists_append_of_mem hz
  exact ⟨A⟩

end GraphMinor.GM03
end

