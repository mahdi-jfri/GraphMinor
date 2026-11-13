module

public import GraphMinor.GM08.Section7Defs
public import GraphMinor.Minor.Model
public import GraphMinor.GM11.EvenCircuit
import GraphMinor.GM11.Section4b
import GraphMinor.GM11.Rings
import GraphMinor.GM11.Separate
import GraphMinor.GM11.NiceStatements
import GraphMinor.GM12.Section3OneDiscComplement
import GraphMinor.Surface.CrossingProved

@[expose] public section

/-!
# Grid Frames and Jordan Separation in a Sphere Drawing (for GM VIII (7.1))

Given a minor model of `GM01.gridGraph θ` in `D₀.toGraph` for a drawing `D₀` on
`S₀ = OnePoint EuclideanPlane`, this file lifts the concentric square frames `Q_k` of the `θ`-grid
to circuits `C'_k` of `D₀` and uses `DiscCrossingStatement.of_isPathConnected_proved` on the four
cardinal spokes `(top, right, bottom, left)` to show that for every `1 ≤ k ≤ m - 1`, `C'_{k-1}` and
`C'_{k+1}` lie on opposite sides of `C'_k`.
-/

namespace GraphMinor
namespace GM08

open Set Function Topology Graph Surface GM11

abbrev SphereSurf := OnePoint EuclideanPlane

/-!
## 1. Crossing Pairs on a Simple-Closed Walk
-/

/-- Two subdrawings of `D₀` with disjoint vertex sets have disjoint point sets `U`. -/
theorem disjoint_U_of_disjoint_V {S : Type*} [TopologicalSpace S] {D₀ A B : Drawing S}
    (hA : A.IsSubdrawing D₀) (hB : B.IsSubdrawing D₀) (hV : Disjoint A.V B.V) :
    Disjoint A.U B.U := by
  have hE : Disjoint A.E B.E := by
    refine Set.disjoint_left.mpr fun e heA heB => ?_
    obtain ⟨u, v, hl⟩ := (A.toGraph.edge_mem_iff_exists_isLink e).mp heA
    have hlD : D₀.toGraph.IsLink e u v := (hA.isLink_iff heA).mp hl
    have hlB : B.toGraph.IsLink e u v := (hB.isLink_iff heB).mpr hlD
    exact Set.disjoint_left.mp hV hl.2.1 hlB.2.1
  rw [A.U_eq, B.U_eq]
  refine Disjoint.union_left ?_ ?_
  · refine Disjoint.union_right hV ?_
    refine Set.disjoint_left.mpr fun x hxA hxcl => ?_
    obtain ⟨f, hfB, hxf⟩ := Set.mem_iUnion₂.mp hxcl
    have hxB : x ∈ closure f ∩ D₀.V := ⟨hxf, hA.1 hxA⟩
    rw [← hB.closure_inter_V hfB] at hxB
    exact Set.disjoint_left.mp hV hxA hxB.2
  · refine Disjoint.union_right ?_ ?_
    · refine Set.disjoint_left.mpr fun x hxcl hxB => ?_
      obtain ⟨e, heA, hxe⟩ := Set.mem_iUnion₂.mp hxcl
      have hxA : x ∈ closure e ∩ D₀.V := ⟨hxe, hB.1 hxB⟩
      rw [← hA.closure_inter_V heA] at hxA
      exact Set.disjoint_left.mp hV hxA.2 hxB
    · refine Set.disjoint_left.mpr fun x hxA hxB => ?_
      obtain ⟨e, heA, hxe⟩ := Set.mem_iUnion₂.mp hxA
      obtain ⟨f, hfB, hxf⟩ := Set.mem_iUnion₂.mp hxB
      by_cases hxV : x ∈ D₀.V
      · have h₁ : x ∈ closure e ∩ A.V := by rw [hA.closure_inter_V heA]; exact ⟨hxe, hxV⟩
        have h₂ : x ∈ closure f ∩ B.V := by rw [hB.closure_inter_V hfB]; exact ⟨hxf, hxV⟩
        exact Set.disjoint_left.mp hV h₁.2 h₂.2
      · have hxe' : x ∈ e := by
          have := D₀.closure_diff_V (hA.2 heA)
          have hmem : x ∈ closure e \ D₀.V := ⟨hxe, hxV⟩
          rwa [this] at hmem
        have hxf' : x ∈ f := by
          have := D₀.closure_diff_V (hB.2 hfB)
          have hmem : x ∈ closure f \ D₀.V := ⟨hxf, hxV⟩
          rwa [this] at hmem
        have hef : e = f := D₀.edge_eq_of_mem (hA.2 heA) (hB.2 hfB) hxe' hxf'
        exact Set.disjoint_left.mp hE heA (hef ▸ hfB)

/-- For a walk `W` of a drawing `D₀` on `SphereSurf`, `(walkDrawing D₀ W).U` is path-connected. -/
theorem isPathConnected_walkDrawing_U (D₀ : Drawing SphereSurf) {u v : SphereSurf}
    (W : GraphWalk D₀.toGraph u v) : IsPathConnected (walkDrawing D₀ W).U := by
  have : ConnectedSpace SphereSurf := (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).2
  have heq : (walkDrawing D₀ W).U = {x | x ∈ W.support ∨ ∃ e ∈ W.edges, x ∈ closure e} := by
    ext x
    exact GM11.mem_walkDrawing_U D₀ W
  rw [heq]
  exact GM11.isPathConnected_walk_U W

/-- If a closed set `C = J₁ ∪ J₂` satisfies `J₁ ∩ J₂ ⊆ {a, c}` with `J₁, J₂` closed and `a, b, c, d`
pairwise distinct with `a, c ∈ C`, `b ∈ J₁ \ {a, c}`, `d ∈ J₂ \ {a, c}`, then
`PairsCrossOn C a c b d`. -/
theorem pairsCrossOn_of_closed_cover {S : Type*} [TopologicalSpace S]
    {C J₁ J₂ : Set S} {a c b d : S}
    (hcov : C = J₁ ∪ J₂) (hJ₁ : IsClosed J₁) (hJ₂ : IsClosed J₂)
    (hint : J₁ ∩ J₂ ⊆ {a, c})
    (ha : a ∈ C) (hc : c ∈ C) (hac : a ≠ c) (hbd : b ≠ d)
    (hb₁ : b ∈ J₁) (hb_ac : b ∉ ({a, c} : Set S))
    (hd₂ : d ∈ J₂) (hd_ac : d ∉ ({a, c} : Set S)) :
    PairsCrossOn C a c b d := by
  have hbC : b ∈ C := hcov ▸ Or.inl hb₁
  have hdC : d ∈ C := hcov ▸ Or.inr hd₂
  have hab : a ≠ b := fun h => hb_ac (by simp [h])
  have hcb : c ≠ b := fun h => hb_ac (by simp [h])
  have had : a ≠ d := fun h => hd_ac (by simp [h])
  have hcd : c ≠ d := fun h => hd_ac (by simp [h])
  refine ⟨ha, hbC, hc, hdC, hac, hbd, hab, had, hcb, hcd, ?_⟩
  intro heq
  let K := connectedComponentIn (C \ {a, c}) b
  have hbK : b ∈ K := mem_connectedComponentIn ⟨hbC, hb_ac⟩
  have hdK : d ∈ K := by
    change d ∈ connectedComponentIn (C \ {a, c}) b
    rw [heq]
    exact mem_connectedComponentIn ⟨hdC, hd_ac⟩
  have hKsub : K ⊆ C \ {a, c} := connectedComponentIn_subset _ _
  have hKcov : K ⊆ J₁ ∪ J₂ := fun x hx => hcov ▸ (hKsub hx).1
  obtain ⟨y, hyK, hy₁, hy₂⟩ :=
    isPreconnected_closed_iff.mp isPreconnected_connectedComponentIn J₁ J₂ hJ₁ hJ₂ hKcov
      ⟨b, hbK, hb₁⟩ ⟨d, hdK, hd₂⟩
  exact (hKsub hyK).2 (hint ⟨hy₁, hy₂⟩)

/-- Four-arc decomposition of a simple-closed walk: if `W = (W₀.append W₁).append (W₂.append W₃)`
has vertices partitioned into four pairwise disjoint sets `S₀, S₁, S₂, S₃` (except each segment's
terminal joint, which starts the next segment), then choosing `a ∈ V(W) ∩ S₀`, `b ∈ V(W) ∩ S₁`,
`c ∈ V(W) ∩ S₂`, `d ∈ V(W) ∩ S₃` yields `PairsCrossOn (walkDrawing D₀ W).U a c b d`. -/
theorem pairsCrossOn_of_four_arcs (D₀ : Drawing SphereSurf)
    {q₀ q₁ q₂ q₃ : SphereSurf}
    (W₀ : GraphWalk D₀.toGraph q₀ q₁) (W₁ : GraphWalk D₀.toGraph q₁ q₂)
    (W₂ : GraphWalk D₀.toGraph q₂ q₃) (W₃ : GraphWalk D₀.toGraph q₃ q₀)
    {S₀ S₁ S₂ S₃ : Set SphereSurf}
    (hdis01 : Disjoint S₀ S₁) (hdis02 : Disjoint S₀ S₂) (hdis03 : Disjoint S₀ S₃)
    (hdis12 : Disjoint S₁ S₂) (hdis13 : Disjoint S₁ S₃) (hdis23 : Disjoint S₂ S₃)
    (hW₀ : ∀ x ∈ W₀.support, x = q₁ ∨ x ∈ S₀)
    (hW₁ : ∀ x ∈ W₁.support, x = q₂ ∨ x ∈ S₁)
    (hW₂ : ∀ x ∈ W₂.support, x = q₃ ∨ x ∈ S₂)
    (hW₃ : ∀ x ∈ W₃.support, x = q₀ ∨ x ∈ S₃)
    (hq₀ : q₀ ∈ S₀) (hq₁ : q₁ ∈ S₁) (hq₂ : q₂ ∈ S₂) (hq₃ : q₃ ∈ S₃)
    (hnd₀ : W₀.IsSimple) (hnd₁ : W₁.IsSimple) (hnd₂ : W₂.IsSimple) (hnd₃ : W₃.IsSimple)
    (hE_disj : Pairwise fun i j : Fin 4 =>
      Disjoint {e | e ∈ ([W₀.edges, W₁.edges, W₂.edges, W₃.edges].get i)}
               {e | e ∈ ([W₀.edges, W₁.edges, W₂.edges, W₃.edges].get j)})
    {a b c d : SphereSurf}
    (ha : a ∈ (walkDrawing D₀ ((W₀.append W₁).append (W₂.append W₃))).V ∩ S₀)
    (hb : b ∈ (walkDrawing D₀ ((W₀.append W₁).append (W₂.append W₃))).V ∩ S₁)
    (hc : c ∈ (walkDrawing D₀ ((W₀.append W₁).append (W₂.append W₃))).V ∩ S₂)
    (hd : d ∈ (walkDrawing D₀ ((W₀.append W₁).append (W₂.append W₃))).V ∩ S₃) :
    PairsCrossOn (walkDrawing D₀ ((W₀.append W₁).append (W₂.append W₃))).U a c b d := by
  set W := (W₀.append W₁).append (W₂.append W₃)
  have mem_W_iff : ∀ z, z ∈ (walkDrawing D₀ W).V ↔
      z ∈ W₀.support ∨ z ∈ W₁.support ∨ z ∈ W₂.support ∨ z ∈ W₃.support := by
    intro z
    rw [GM11.walkDrawing_V, Set.mem_ofPred_eq, GraphWalk.mem_support_append,
      GraphWalk.mem_support_append, GraphWalk.mem_support_append, or_assoc]
  have haW₀ : a ∈ W₀.support := by
    rcases (mem_W_iff a).mp ha.1 with h | h | h | h
    · exact h
    · rcases hW₁ a h with rfl | h1
      · exact absurd hq₂ (Set.disjoint_left.mp hdis02 ha.2)
      · exact absurd h1 (Set.disjoint_left.mp hdis01 ha.2)
    · rcases hW₂ a h with rfl | h2
      · exact absurd hq₃ (Set.disjoint_left.mp hdis03 ha.2)
      · exact absurd h2 (Set.disjoint_left.mp hdis02 ha.2)
    · rcases hW₃ a h with rfl | h3
      · exact W₀.start_mem_support
      · exact absurd h3 (Set.disjoint_left.mp hdis03 ha.2)
  have hcW₂ : c ∈ W₂.support := by
    rcases (mem_W_iff c).mp hc.1 with h | h | h | h
    · rcases hW₀ c h with rfl | h0
      · exact absurd hq₁ (Set.disjoint_left.mp hdis12.symm hc.2)
      · exact absurd h0 (Set.disjoint_left.mp hdis02.symm hc.2)
    · rcases hW₁ c h with rfl | h1
      · exact W₂.start_mem_support
      · exact absurd h1 (Set.disjoint_left.mp hdis12.symm hc.2)
    · exact h
    · rcases hW₃ c h with rfl | h3
      · exact absurd hq₀ (Set.disjoint_left.mp hdis02.symm hc.2)
      · exact absurd h3 (Set.disjoint_left.mp hdis23 hc.2)
  have hbW₁ : b ∈ W₁.support := by
    rcases (mem_W_iff b).mp hb.1 with h | h | h | h
    · rcases hW₀ b h with rfl | h0
      · exact W₁.start_mem_support
      · exact absurd h0 (Set.disjoint_left.mp hdis01.symm hb.2)
    · exact h
    · rcases hW₂ b h with rfl | h2
      · exact absurd hq₃ (Set.disjoint_left.mp hdis13 hb.2)
      · exact absurd h2 (Set.disjoint_left.mp hdis12 hb.2)
    · rcases hW₃ b h with rfl | h3
      · exact absurd hq₀ (Set.disjoint_left.mp hdis01.symm hb.2)
      · exact absurd h3 (Set.disjoint_left.mp hdis13 hb.2)
  have hdW₃ : d ∈ W₃.support := by
    rcases (mem_W_iff d).mp hd.1 with h | h | h | h
    · rcases hW₀ d h with rfl | h0
      · exact absurd hq₁ (Set.disjoint_left.mp hdis13.symm hd.2)
      · exact absurd h0 (Set.disjoint_left.mp hdis03.symm hd.2)
    · rcases hW₁ d h with rfl | h1
      · exact absurd hq₂ (Set.disjoint_left.mp hdis23.symm hd.2)
      · exact absurd h1 (Set.disjoint_left.mp hdis13.symm hd.2)
    · rcases hW₂ d h with rfl | h2
      · exact W₃.start_mem_support
      · exact absurd h2 (Set.disjoint_left.mp hdis23.symm hd.2)
    · exact h
  obtain ⟨A₁, A₂, hAsplit⟩ := W₀.exists_append_of_mem haW₀
  obtain ⟨C₁, C₂, hCsplit⟩ := W₂.exists_append_of_mem hcW₂
  let Q₁ : GraphWalk D₀.toGraph a c := A₂.append (W₁.append C₁)
  let Q₂ : GraphWalk D₀.toGraph c a := C₂.append (W₃.append A₁)
  let J₁ := (walkDrawing D₀ Q₁).U
  let J₂ := (walkDrawing D₀ Q₂).U
  have hA_disj : ∀ z ∈ A₁.support, z ∈ A₂.support → z = a := by
    intro z hz₁ hz₂
    have hnd : (A₁.support ++ A₂.support.tail).Nodup := by
      rw [← GraphWalk.support_append, ← hAsplit]
      exact hnd₀
    rw [A₂.support_eq_cons] at hz₂
    rcases List.mem_cons.mp hz₂ with rfl | hz₂'
    · rfl
    · exact ((List.nodup_append.mp hnd).2.2 z hz₁ z hz₂' rfl).elim
  have hC_disj : ∀ z ∈ C₁.support, z ∈ C₂.support → z = c := by
    intro z hz₁ hz₂
    have hnd : (C₁.support ++ C₂.support.tail).Nodup := by
      rw [← GraphWalk.support_append, ← hCsplit]
      exact hnd₂
    rw [C₂.support_eq_cons] at hz₂
    rcases List.mem_cons.mp hz₂ with rfl | hz₂'
    · rfl
    · exact ((List.nodup_append.mp hnd).2.2 z hz₁ z hz₂' rfl).elim
  have hA_edisj : ∀ e ∈ A₁.edges, e ∉ A₂.edges := by
    intro e he₁ he₂
    have hnd : (A₁.edges ++ A₂.edges).Nodup := by
      rw [← GraphWalk.edges_append, ← hAsplit]
      exact hnd₀.edges_nodup
    exact (List.nodup_append.mp hnd).2.2 e he₁ e he₂ rfl
  have hC_edisj : ∀ e ∈ C₁.edges, e ∉ C₂.edges := by
    intro e he₁ he₂
    have hnd : (C₁.edges ++ C₂.edges).Nodup := by
      rw [← GraphWalk.edges_append, ← hCsplit]
      exact hnd₂.edges_nodup
    exact (List.nodup_append.mp hnd).2.2 e he₁ e he₂ rfl
  have hQ_sup_eq : ∀ z, z ∈ W.support ↔ z ∈ Q₁.support ∨ z ∈ Q₂.support := by
    intro z
    change z ∈ ((W₀.append W₁).append (W₂.append W₃)).support ↔
      z ∈ (A₂.append (W₁.append C₁)).support ∨ z ∈ (C₂.append (W₃.append A₁)).support
    rw [hAsplit, hCsplit]
    simp only [GraphWalk.mem_support_append]
    constructor
    · rintro (((hA1 | hA2) | h1) | (hC1 | hC2) | h3)
      · exact Or.inr (Or.inr (Or.inr hA1))
      · exact Or.inl (Or.inl hA2)
      · exact Or.inl (Or.inr (Or.inl h1))
      · exact Or.inl (Or.inr (Or.inr hC1))
      · exact Or.inr (Or.inl hC2)
      · exact Or.inr (Or.inr (Or.inl h3))
    · rintro ((hA2 | h1 | hC1) | (hC2 | h3 | hA1))
      · exact Or.inl (Or.inl (Or.inr hA2))
      · exact Or.inl (Or.inr h1)
      · exact Or.inr (Or.inl (Or.inl hC1))
      · exact Or.inr (Or.inl (Or.inr hC2))
      · exact Or.inr (Or.inr h3)
      · exact Or.inl (Or.inl (Or.inl hA1))
  have hQ_ed_eq : ∀ e, e ∈ W.edges ↔ e ∈ Q₁.edges ∨ e ∈ Q₂.edges := by
    intro e
    change e ∈ ((W₀.append W₁).append (W₂.append W₃)).edges ↔
      e ∈ (A₂.append (W₁.append C₁)).edges ∨ e ∈ (C₂.append (W₃.append A₁)).edges
    rw [hAsplit, hCsplit]
    simp only [GraphWalk.edges_append, List.mem_append]
    constructor
    · rintro (((hA1 | hA2) | h1) | (hC1 | hC2) | h3)
      · exact Or.inr (Or.inr (Or.inr hA1))
      · exact Or.inl (Or.inl hA2)
      · exact Or.inl (Or.inr (Or.inl h1))
      · exact Or.inl (Or.inr (Or.inr hC1))
      · exact Or.inr (Or.inl hC2)
      · exact Or.inr (Or.inr (Or.inl h3))
    · rintro ((hA2 | h1 | hC1) | (hC2 | h3 | hA1))
      · exact Or.inl (Or.inl (Or.inr hA2))
      · exact Or.inl (Or.inr h1)
      · exact Or.inr (Or.inl (Or.inl hC1))
      · exact Or.inr (Or.inl (Or.inr hC2))
      · exact Or.inr (Or.inr h3)
      · exact Or.inl (Or.inl (Or.inl hA1))
  have hcov : (walkDrawing D₀ W).U = J₁ ∪ J₂ := by
    ext z
    rw [Set.mem_union, GM11.mem_walkDrawing_U D₀ W, GM11.mem_walkDrawing_U D₀ Q₁,
      GM11.mem_walkDrawing_U D₀ Q₂]
    constructor
    · rintro (hz | ⟨e, he, hze⟩)
      · rcases (hQ_sup_eq z).mp hz with h1 | h2
        · exact Or.inl (Or.inl h1)
        · exact Or.inr (Or.inl h2)
      · rcases (hQ_ed_eq e).mp he with h1 | h2
        · exact Or.inl (Or.inr ⟨e, h1, hze⟩)
        · exact Or.inr (Or.inr ⟨e, h2, hze⟩)
    · rintro ((hz | ⟨e, he, hze⟩) | (hz | ⟨e, he, hze⟩))
      · exact Or.inl ((hQ_sup_eq z).mpr (Or.inl hz))
      · exact Or.inr ⟨e, (hQ_ed_eq e).mpr (Or.inl he), hze⟩
      · exact Or.inl ((hQ_sup_eq z).mpr (Or.inr hz))
      · exact Or.inr ⟨e, (hQ_ed_eq e).mpr (Or.inr he), hze⟩
  have ha_ne_q₁ : a ≠ q₁ := fun h => Set.disjoint_left.mp hdis01 ha.2 (h ▸ hq₁)
  have hc_ne_q₃ : c ≠ q₃ := fun h => Set.disjoint_left.mp hdis23 hc.2 (h ▸ hq₃)
  have hA₁_S₀ : ∀ z ∈ A₁.support, z ∈ S₀ := by
    intro z hz
    have hz₀ : z ∈ W₀.support := hAsplit ▸ (GraphWalk.mem_support_append _ _).mpr (Or.inl hz)
    rcases hW₀ z hz₀ with hzq | hzS
    · exfalso
      have hq₁_A₂ : q₁ ∈ A₂.support := A₂.end_mem_support
      exact ha_ne_q₁ (hA_disj q₁ (hzq ▸ hz) hq₁_A₂).symm
    · exact hzS
  have hC₁_S₂ : ∀ z ∈ C₁.support, z ∈ S₂ := by
    intro z hz
    have hz₂ : z ∈ W₂.support := hCsplit ▸ (GraphWalk.mem_support_append _ _).mpr (Or.inl hz)
    rcases hW₂ z hz₂ with hzq | hzS
    · exfalso
      have hq₃_C₂ : q₃ ∈ C₂.support := C₂.end_mem_support
      exact hc_ne_q₃ (hC_disj q₃ (hzq ▸ hz) hq₃_C₂).symm
    · exact hzS
  have hQ_V_inter : ∀ z, z ∈ Q₁.support → z ∈ Q₂.support → z = a ∨ z = c := by
    intro z hz₁ hz₂
    simp only [Q₁, Q₂, GraphWalk.mem_support_append] at hz₁ hz₂
    rcases hz₁ with hA₂ | hW₁' | hC₁ <;> rcases hz₂ with hC₂ | hW₃' | hA₁
    · have hzW₀ : z ∈ W₀.support := hAsplit ▸ (GraphWalk.mem_support_append _ _).mpr (Or.inr hA₂)
      have hzW₂ : z ∈ W₂.support := hCsplit ▸ (GraphWalk.mem_support_append _ _).mpr (Or.inr hC₂)
      rcases hW₀ z hzW₀ with eq0 | hz0 <;> rcases hW₂ z hzW₂ with eq2 | hz2
      · exact (Set.disjoint_left.mp hdis13 (eq0 ▸ hq₁) (eq2 ▸ hq₃)).elim
      · exact (Set.disjoint_left.mp hdis12 (eq0 ▸ hq₁) hz2).elim
      · exact (Set.disjoint_left.mp hdis03 hz0 (eq2 ▸ hq₃)).elim
      · exact (Set.disjoint_left.mp hdis02 hz0 hz2).elim
    · have hzW₀ : z ∈ W₀.support := hAsplit ▸ (GraphWalk.mem_support_append _ _).mpr (Or.inr hA₂)
      rcases hW₀ z hzW₀ with eq0 | hz0 <;> rcases hW₃ z hW₃' with eq3 | hz3
      · exact (Set.disjoint_left.mp hdis01 (eq3 ▸ hq₀) (eq0 ▸ hq₁)).elim
      · exact (Set.disjoint_left.mp hdis13 (eq0 ▸ hq₁) hz3).elim
      · exact Or.inl (eq3.trans (hA_disj q₀ A₁.start_mem_support (eq3 ▸ hA₂)))
      · exact (Set.disjoint_left.mp hdis03 hz0 hz3).elim
    · exact Or.inl (hA_disj z hA₁ hA₂)
    · have hzW₂ : z ∈ W₂.support := hCsplit ▸ (GraphWalk.mem_support_append _ _).mpr (Or.inr hC₂)
      rcases hW₁ z hW₁' with eq1 | hz1 <;> rcases hW₂ z hzW₂ with eq2 | hz2
      · exact (Set.disjoint_left.mp hdis23 (eq1 ▸ hq₂) (eq2 ▸ hq₃)).elim
      · exact Or.inr (eq1.trans (hC_disj q₂ C₁.start_mem_support (eq1 ▸ hC₂)))
      · exact (Set.disjoint_left.mp hdis13 hz1 (eq2 ▸ hq₃)).elim
      · exact (Set.disjoint_left.mp hdis12 hz1 hz2).elim
    · rcases hW₁ z hW₁' with eq1 | hz1 <;> rcases hW₃ z hW₃' with eq3 | hz3
      · exact (Set.disjoint_left.mp hdis02 (eq3 ▸ hq₀) (eq1 ▸ hq₂)).elim
      · exact (Set.disjoint_left.mp hdis23 (eq1 ▸ hq₂) hz3).elim
      · exact (Set.disjoint_left.mp hdis01 (eq3 ▸ hq₀) hz1).elim
      · exact (Set.disjoint_left.mp hdis13 hz1 hz3).elim
    · have hz0 := hA₁_S₀ z hA₁
      rcases hW₁ z hW₁' with eq1 | hz1
      · exact (Set.disjoint_left.mp hdis02 hz0 (eq1 ▸ hq₂)).elim
      · exact (Set.disjoint_left.mp hdis01 hz0 hz1).elim
    · exact Or.inr (hC_disj z hC₁ hC₂)
    · have hz2 := hC₁_S₂ z hC₁
      rcases hW₃ z hW₃' with eq3 | hz3
      · exact (Set.disjoint_left.mp hdis02 (eq3 ▸ hq₀) hz2).elim
      · exact (Set.disjoint_left.mp hdis23 hz2 hz3).elim
    · exact (Set.disjoint_left.mp hdis02 (hA₁_S₀ z hA₁) (hC₁_S₂ z hC₁)).elim
  have hQ_E_disj : ∀ e, e ∈ Q₁.edges → e ∉ Q₂.edges := by
    intro e he₁ he₂
    simp only [Q₁, Q₂, GraphWalk.edges_append, List.mem_append] at he₁ he₂
    have heA₂ : ∀ h : e ∈ A₂.edges, e ∈ W₀.edges := fun h => by
      rw [hAsplit, GraphWalk.edges_append]; exact List.mem_append_right _ h
    have heA₁ : ∀ h : e ∈ A₁.edges, e ∈ W₀.edges := fun h => by
      rw [hAsplit, GraphWalk.edges_append]; exact List.mem_append_left _ h
    have heC₁ : ∀ h : e ∈ C₁.edges, e ∈ W₂.edges := fun h => by
      rw [hCsplit, GraphWalk.edges_append]; exact List.mem_append_left _ h
    have heC₂ : ∀ h : e ∈ C₂.edges, e ∈ W₂.edges := fun h => by
      rw [hCsplit, GraphWalk.edges_append]; exact List.mem_append_right _ h
    have d02 : Disjoint {x | x ∈ W₀.edges} {x | x ∈ W₂.edges} := hE_disj (by decide : (0 : Fin 4) ≠ 2)
    have d03 : Disjoint {x | x ∈ W₀.edges} {x | x ∈ W₃.edges} := hE_disj (by decide : (0 : Fin 4) ≠ 3)
    have d12 : Disjoint {x | x ∈ W₁.edges} {x | x ∈ W₂.edges} := hE_disj (by decide : (1 : Fin 4) ≠ 2)
    have d13 : Disjoint {x | x ∈ W₁.edges} {x | x ∈ W₃.edges} := hE_disj (by decide : (1 : Fin 4) ≠ 3)
    have d23 : Disjoint {x | x ∈ W₂.edges} {x | x ∈ W₃.edges} := hE_disj (by decide : (2 : Fin 4) ≠ 3)
    have d01 : Disjoint {x | x ∈ W₀.edges} {x | x ∈ W₁.edges} := hE_disj (by decide : (0 : Fin 4) ≠ 1)
    rcases he₁ with h1 | h1 | h1 <;> rcases he₂ with h2 | h2 | h2
    · exact Set.disjoint_left.mp d02 (heA₂ h1) (heC₂ h2)
    · exact Set.disjoint_left.mp d03 (heA₂ h1) h2
    · exact hA_edisj e h2 h1
    · exact Set.disjoint_left.mp d12 h1 (heC₂ h2)
    · exact Set.disjoint_left.mp d13 h1 h2
    · exact Set.disjoint_left.mp d01.symm h1 (heA₁ h2)
    · exact hC_edisj e h1 h2
    · exact Set.disjoint_left.mp d23 (heC₁ h1) h2
    · exact Set.disjoint_left.mp d02.symm (heC₁ h1) (heA₁ h2)
  have hint : J₁ ∩ J₂ ⊆ {a, c} := by
    intro z ⟨hz₁, hz₂⟩
    have hVQ₁ : (walkDrawing D₀ Q₁).V = {x | x ∈ Q₁.support} := GM11.walkDrawing_V D₀ Q₁
    have hVQ₂ : (walkDrawing D₀ Q₂).V = {x | x ∈ Q₂.support} := GM11.walkDrawing_V D₀ Q₂
    have hsub₁ := GM11.walkDrawing_isSubdrawing D₀ Q₁
    have hsub₂ := GM11.walkDrawing_isSubdrawing D₀ Q₂
    by_cases hzV : z ∈ D₀.V
    · have hzQ₁ : z ∈ Q₁.support := by
        rcases (GM11.mem_walkDrawing_U D₀ Q₁).mp hz₁ with h | ⟨e, he, hze⟩
        · exact h
        · have heQ₁ : e ∈ (walkDrawing D₀ Q₁).E := by rw [GM11.walkDrawing_E]; exact he
          have : z ∈ closure e ∩ (walkDrawing D₀ Q₁).V := by
            rw [hsub₁.closure_inter_V heQ₁]
            exact ⟨hze, hzV⟩
          rw [hVQ₁] at this
          exact this.2
      have hzQ₂ : z ∈ Q₂.support := by
        rcases (GM11.mem_walkDrawing_U D₀ Q₂).mp hz₂ with h | ⟨e, he, hze⟩
        · exact h
        · have heQ₂ : e ∈ (walkDrawing D₀ Q₂).E := by rw [GM11.walkDrawing_E]; exact he
          have : z ∈ closure e ∩ (walkDrawing D₀ Q₂).V := by
            rw [hsub₂.closure_inter_V heQ₂]
            exact ⟨hze, hzV⟩
          rw [hVQ₂] at this
          exact this.2
      exact hQ_V_inter z hzQ₁ hzQ₂
    · exfalso
      rcases (GM11.mem_walkDrawing_U D₀ Q₁).mp hz₁ with h | ⟨e₁, he₁, hze₁⟩
      · exact hzV (Q₁.mem_vertexSet_of_mem_support h)
      rcases (GM11.mem_walkDrawing_U D₀ Q₂).mp hz₂ with h | ⟨e₂, he₂, hze₂⟩
      · exact hzV (Q₂.mem_vertexSet_of_mem_support h)
      have he₁D : e₁ ∈ D₀.E := GM11.mem_E_of_mem_edges Q₁ he₁
      have he₂D : e₂ ∈ D₀.E := GM11.mem_E_of_mem_edges Q₂ he₂
      have hze₁' : z ∈ e₁ := by
        have h := D₀.closure_diff_V he₁D
        have hm : z ∈ closure e₁ \ D₀.V := ⟨hze₁, hzV⟩
        rwa [h] at hm
      have hze₂' : z ∈ e₂ := by
        have h := D₀.closure_diff_V he₂D
        have hm : z ∈ closure e₂ \ D₀.V := ⟨hze₂, hzV⟩
        rwa [h] at hm
      have heq_e : e₁ = e₂ := D₀.edge_eq_of_mem he₁D he₂D hze₁' hze₂'
      exact hQ_E_disj e₁ he₁ (heq_e ▸ he₂)
  have hbJ₁ : b ∈ J₁ :=
    (GM11.mem_walkDrawing_U D₀ Q₁).mpr (Or.inl
      ((GraphWalk.mem_support_append _ _).mpr (Or.inr
        ((GraphWalk.mem_support_append _ _).mpr (Or.inl hbW₁)))))
  have hdJ₂ : d ∈ J₂ :=
    (GM11.mem_walkDrawing_U D₀ Q₂).mpr (Or.inl
      ((GraphWalk.mem_support_append _ _).mpr (Or.inr
        ((GraphWalk.mem_support_append _ _).mpr (Or.inl hdW₃)))))
  have haC : a ∈ (walkDrawing D₀ W).U :=
    (walkDrawing D₀ W).V_subset_U ha.1
  have hcC : c ∈ (walkDrawing D₀ W).U :=
    (walkDrawing D₀ W).V_subset_U hc.1
  have hac : a ≠ c := fun h => Set.disjoint_left.mp hdis02 ha.2 (h ▸ hc.2)
  have hbd : b ≠ d := fun h => Set.disjoint_left.mp hdis13 hb.2 (h ▸ hd.2)
  have hb_ac : b ∉ ({a, c} : Set SphereSurf) := by
    rintro (rfl | rfl)
    · exact Set.disjoint_left.mp hdis01 ha.2 hb.2
    · exact Set.disjoint_left.mp hdis12 hb.2 hc.2
  have hd_ac : d ∉ ({a, c} : Set SphereSurf) := by
    rintro (rfl | rfl)
    · exact Set.disjoint_left.mp hdis03 ha.2 hd.2
    · exact Set.disjoint_left.mp hdis23 hc.2 hd.2
  exact pairsCrossOn_of_closed_cover hcov (walkDrawing D₀ Q₁).isClosed_U
    (walkDrawing D₀ Q₂).isClosed_U hint haC hcC hac hbd hbJ₁ hb_ac hdJ₂ hd_ac

/-!
## 2. Staying Inside a Closed Disc Up to the First Hit on `C.V`
-/

/-- If a walk `W` of `D₀` starts in `discInt D` (for a closed disc `D ⊆ SphereSurf` with
`discBd D = C.U` for a subdrawing `C` of `D₀`), ends at `z ∈ C.V`, and hits `C.V` only at `z`
and only at the end (`W.IsSimple`), then `(walkDrawing D₀ W).U ⊆ D`. -/
theorem walkDrawing_subset_disc_of_first_hit (D₀ C : Drawing SphereSurf) {D : Set SphereSurf}
    (hD : IsClosedDisc D) (hCs : C.IsSubdrawing D₀) (hbd : discBd D = C.U)
    {u z : SphereSurf} (W : GraphWalk D₀.toGraph u z) (hW : W.IsSimple)
    (hu : u ∈ discInt D) (hz : z ∈ C.V)
    (hfirst : ∀ x ∈ W.support, x ∈ C.V → x = z) :
    (walkDrawing D₀ W).U ⊆ D := by
  have hS' : IsClosedSurface SphereSurf := (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have hman : ∀ p : SphereSurf, IsManifoldPoint p := fun p => (hS'.2.2 p).isManifoldPoint
  have hCU_V : C.U ∩ D₀.V = C.V := by
    ext x
    constructor
    · rintro ⟨hxU, hxV⟩
      rw [C.U_eq] at hxU
      rcases hxU with hxCV | hxcl
      · exact hxCV
      · obtain ⟨f, hfC, hxf⟩ := Set.mem_iUnion₂.mp hxcl
        have : x ∈ closure f ∩ C.V := by
          rw [hCs.closure_inter_V hfC]
          exact ⟨hxf, hxV⟩
        exact this.2
    · intro hxCV
      exact ⟨C.V_subset_U hxCV, hCs.1 hxCV⟩
  induction W with
  | nil _ =>
    exact absurd (hbd ▸ C.V_subset_U hz) hu.2
  | @cons a b z e hl r ih =>
    have ha_ne_z : a ≠ z := fun h => hu.2 (hbd ▸ h ▸ C.V_subset_U hz)
    have ha_not_CV : a ∉ C.V := fun haC => ha_ne_z (hfirst a (by simp) haC)
    have heD : e ∈ D₀.E := hl.1
    have he_not_CE : e ∉ C.E := fun heC => ha_not_CV ((hCs.isLink_iff heC).mpr hl).2.1
    have he_disj_bd : Disjoint e (discBd D) := by
      rw [hbd, C.U_eq]
      refine Disjoint.union_right ?_ ?_
      · exact Set.disjoint_left.mpr fun x hxe hxCV => (heD.2.1 hxe).2 (hCs.1 hxCV)
      · refine Set.disjoint_left.mpr fun x hxe hxcl => ?_
        obtain ⟨f, hfC, hxf⟩ := Set.mem_iUnion₂.mp hxcl
        have hx_not_V : x ∉ D₀.V := (heD.2.1 hxe).2
        have hxf' : x ∈ f := by
          have h := D₀.closure_diff_V (hCs.2 hfC)
          have hm : x ∈ closure f \ D₀.V := ⟨hxf, hx_not_V⟩
          rwa [h] at hm
        exact he_not_CE (D₀.edge_eq_of_mem heD (hCs.2 hfC) hxe hxf' ▸ hfC)
    have ha_cl : a ∈ closure e := by
      have : a ∈ closure e ∩ D₀.V := by rw [hl.2.2.2]; simp
      exact this.1
    have hb_cl : b ∈ closure e := by
      have : b ∈ closure e ∩ D₀.V := by rw [hl.2.2.2]; simp
      exact this.1
    have he_conn : IsPathConnected e := heD.2.2.1
    have he_int : e ⊆ discInt D := by
      rcases hD.side hman he_conn.isConnected.isPreconnected he_disj_bd with hin | hout
      · exact hin
      · exfalso
        obtain ⟨y, hy_int, hye⟩ := mem_closure_iff.mp ha_cl _ (hD.isOpen_discInt hman) hu
        exact Set.disjoint_left.mp hout hye hy_int.1
    have hcle_D : closure e ⊆ D :=
      closure_minimal (he_int.trans (discInt_subset D)) hD.isClosed
    have hr_simp : r.IsSimple := hW.of_cons
    have hr_sub : (walkDrawing D₀ r).U ⊆ D := by
      by_cases hbz : b = z
      · subst hbz
        have hr0 : r.length = 0 := hr_simp.length_eq_zero
        cases r with
        | nil _ =>
          intro x hx
          rw [GM11.mem_walkDrawing_U] at hx
          rcases hx with hx | ⟨f, hf, _⟩
          · simp only [GraphWalk.support_nil, List.mem_singleton] at hx
            exact hx ▸ hcle_D hb_cl
          · exact absurd hf List.not_mem_nil
        | cons _ _ => simp [GraphWalk.length] at hr0
      · have hb_not_CV : b ∉ C.V := fun hbC =>
          hbz (hfirst b (List.mem_cons_of_mem _ r.start_mem_support) hbC)
        have hb_not_CU : b ∉ C.U := fun hbU => hb_not_CV (hCU_V.subset ⟨hbU, hl.2.2.1⟩)
        have hb_int : b ∈ discInt D := ⟨hcle_D hb_cl, hbd ▸ hb_not_CU⟩
        exact ih hr_simp hb_int hz fun x hx hxC => hfirst x (List.mem_cons_of_mem _ hx) hxC
    intro x hx
    rw [GM11.mem_walkDrawing_U] at hx
    rcases hx with hx | ⟨f, hf, hxf⟩
    · rcases List.mem_cons.mp hx with rfl | hxr
      · exact hu.1
      · exact hr_sub ((GM11.mem_walkDrawing_U D₀ r).mpr (Or.inl hxr))
    · rcases List.mem_cons.mp hf with rfl | hfr
      · exact hcle_D hxf
      · exact hr_sub ((GM11.mem_walkDrawing_U D₀ r).mpr (Or.inr ⟨f, hfr, hxf⟩))

end GM08
end GraphMinor
