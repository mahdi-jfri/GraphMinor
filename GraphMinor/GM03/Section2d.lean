module

public import GraphMinor.GM03.Section2c

/-!
# Graph Minors III, Section 2: Chord Addition and Claim (1) of (2.2)

This file formalizes the chord-addition infrastructure and **Claim (1)** of the inductive step of
**(2.2)** (page 53) of N. Robertson and P. D. Seymour, *Graph Minors. III. Planar Tree-Width*,
J. Combin. Theory Ser. B **36** (1984), 49–64:
- **Drawing connectivity (`compSubdraw_spec`, `isGraphConnected_iff_isPreconnected_U`)**: for any
  drawing `Γ : Drawing S`, `IsGraphConnected Γ.toGraph ↔ Γ.V.Nonempty ∧ IsPreconnected Γ.U`, via
  the decomposition of `Γ` into the reachable subdrawing `compSubdraw Γ v₀` (whose point set is
  closed and preconnected) and its complement `restSubdraw Γ v₀`.
- **Unified chord-addition lemma (`addChordInRegion_spec`)**: adding a line `K` inside a region
  `q ∈ D.R` (`q ⊆ R_N`, `∀ hd' : 0 < d', q ⊆ interior (Δ ⟨d' - 1, ...⟩)`) between two distinct
  non-adjacent perimeter vertices `v₁, v₂ ∈ (perimDraw N R_N).V` preserves `SurfaceDShell`,
  `HasAtMostOneOuterEdge`, `Simple`, `IsIsoMinor`, `HasDrawingRadiusLE`, and
  `3 ≤ (perimDraw N' R_N').V.ncard`, while keeping `(innerDraw D' d' C).V = (innerDraw D d' C).V`
  and increasing `(innerDraw D' d' C).E.ncard` by `1`.
- **Claim (1) of (2.2) (`lemma_2_2_claim_1`, page 53)**: "(1) $C_{d'}$ is connected." If the
  perimeter subdrawing `B = perimDraw (innerDraw D d' C) R_N` is not connected, then a bridge chord
  can be added in a region `q ∈ D.R` (`q ⊆ R_N`), increasing `|(innerDraw D d' C).E|` by `1` while
  preserving all invariants (i)–(iv).
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function Topology Classical unitInterval
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM11
open GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM22 GraphMinor.Thomas

universe u v

variable {S : Type} [TopologicalSpace S]

/-! ## Part 1: Drawing Connectivity and Reachable Component Subdrawings -/

section DrawingConnectivity

/-- The vertex set of `Γ` reachable from `v₀` by a walk in `Γ.toGraph`. -/
def reachV [T2Space S] (Γ : Drawing S) (v₀ : S) : Set S :=
  {v ∈ Γ.V | Nonempty (GraphWalk Γ.toGraph v₀ v)}

/-- The edge set of `Γ` whose endpoints lie in `reachV Γ v₀`. -/
def reachE [T2Space S] (Γ : Drawing S) (v₀ : S) : Set (Set S) :=
  {e ∈ Γ.E | closure e ∩ Γ.V ⊆ reachV Γ v₀}

/-- The subdrawing of `Γ` on the component of `v₀`. -/
noncomputable def compSubdraw [T2Space S] (Γ : Drawing S) (v₀ : S) : Drawing S :=
  Γ.span (reachV Γ v₀) (reachE Γ v₀)

/-- The subdrawing of `Γ` on the complement of the component of `v₀`. -/
noncomputable def restSubdraw [T2Space S] (Γ : Drawing S) (v₀ : S) : Drawing S :=
  Γ.span (Γ.V \ reachV Γ v₀) {e ∈ Γ.E | closure e ∩ Γ.V ⊆ Γ.V \ reachV Γ v₀}

/-- Every edge `e ∈ Γ.E` has either both endpoints in `reachV Γ v₀` or both endpoints in
`Γ.V \ reachV Γ v₀`. -/
theorem edge_reach_or_rest [T2Space S] (Γ : Drawing S) {v₀ : S} {e : Set S} (he : e ∈ Γ.E) :
    closure e ∩ Γ.V ⊆ reachV Γ v₀ ∨ closure e ∩ Γ.V ⊆ Γ.V \ reachV Γ v₀ := by
  by_cases h : (closure e ∩ reachV Γ v₀).Nonempty
  · refine Or.inl fun z ⟨hze, hzV⟩ => ⟨hzV, ?_⟩
    obtain ⟨u, hue, huV, ⟨W⟩⟩ := h
    by_cases hzu : z = u
    · exact hzu ▸ ⟨W⟩
    · rcases Γ.edge_cond e he with ⟨a, b, -, hcap, -⟩ | ⟨a, hcap, -⟩
      · have hu_ab : u ∈ ({a, b} : Set S) := hcap ▸ ⟨hue, huV⟩
        have hz_ab : z ∈ ({a, b} : Set S) := hcap ▸ ⟨hze, hzV⟩
        have hpair : ({u, z} : Set S) = {a, b} := by
          rcases hu_ab with rfl | rfl <;> rcases hz_ab with rfl | rfl
          · exact (hzu rfl).elim
          · rfl
          · exact pair_comm u z
          · exact (hzu rfl).elim
        have hl : Γ.toGraph.IsLink e u z := ⟨he, huV, hzV, hcap.trans hpair.symm⟩
        exact ⟨W.append (GraphWalk.cons hl (GraphWalk.nil hzV))⟩
      · have hu_a : u = a := mem_singleton_iff.mp (hcap ▸ ⟨hue, huV⟩)
        have hz_a : z = a := mem_singleton_iff.mp (hcap ▸ ⟨hze, hzV⟩)
        exact (hzu (hz_a.trans hu_a.symm)).elim
  · refine Or.inr fun z ⟨hze, hzV⟩ => ⟨hzV, fun hzR => h ⟨z, hze, hzR⟩⟩

/-- Specification of `compSubdraw Γ v₀` and `restSubdraw Γ v₀`: they partition `Γ.V`, `Γ.E`, and
`Γ.U` into two disjoint closed subdrawings, and `(compSubdraw Γ v₀).U` is preconnected. -/
theorem compSubdraw_spec [T2Space S] (Γ : Drawing S) {v₀ : S} (hv₀ : v₀ ∈ Γ.V) :
    let Γ₁ := compSubdraw Γ v₀
    let Γ₂ := restSubdraw Γ v₀
    Γ₁.IsSubdrawing Γ ∧
    Γ₂.IsSubdrawing Γ ∧
    Γ₁.V = reachV Γ v₀ ∧
    Γ₂.V = Γ.V \ reachV Γ v₀ ∧
    Γ₁.E = reachE Γ v₀ ∧
    Γ₂.E = {e ∈ Γ.E | closure e ∩ Γ.V ⊆ Γ.V \ reachV Γ v₀} ∧
    v₀ ∈ Γ₁.V ∧
    Γ.U = Γ₁.U ∪ Γ₂.U ∧
    Disjoint Γ₁.U Γ₂.U ∧
    IsPreconnected Γ₁.U := by
  let Γ₁ := compSubdraw Γ v₀
  let Γ₂ := restSubdraw Γ v₀
  have hSub₁ : Γ₁.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hSub₂ : Γ₂.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have hE₁ : Γ₁.E = reachE Γ v₀ := by
    change (Γ.span (reachV Γ v₀) (reachE Γ v₀)).E = reachE Γ v₀
    rw [Γ.span_E]
    ext e
    exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩
  have hE₂ : Γ₂.E = {e ∈ Γ.E | closure e ∩ Γ.V ⊆ Γ.V \ reachV Γ v₀} := by
    change (Γ.span (Γ.V \ reachV Γ v₀) _).E = _
    rw [Γ.span_E]
    ext e
    exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩
  have hV₁ : Γ₁.V = reachV Γ v₀ := by
    change (Γ.span (reachV Γ v₀) (reachE Γ v₀)).V = reachV Γ v₀
    rw [Γ.span_V]
    refine Subset.antisymm (union_subset (fun x hx => hx.1) (iUnion₂_subset ?_))
      fun x hx => Or.inl ⟨hx, hx.1⟩
    rintro e ⟨⟨_, he_sub⟩, _⟩ x hx
    exact he_sub hx
  have hV₂ : Γ₂.V = Γ.V \ reachV Γ v₀ := by
    change (Γ.span (Γ.V \ reachV Γ v₀) _).V = Γ.V \ reachV Γ v₀
    rw [Γ.span_V]
    refine Subset.antisymm (union_subset (fun x hx => hx.1) (iUnion₂_subset ?_))
      fun x hx => Or.inl ⟨hx, hx.1⟩
    rintro e ⟨⟨_, he_sub⟩, _⟩ x hx
    exact he_sub hx
  have hv₀_mem : v₀ ∈ Γ₁.V := by
    rw [hV₁]
    exact ⟨hv₀, ⟨GraphWalk.nil hv₀⟩⟩
  have hU_union : Γ.U = Γ₁.U ∪ Γ₂.U := by
    refine Subset.antisymm ?_ (union_subset hSub₁.U_subset hSub₂.U_subset)
    rw [Γ.U_eq]
    refine union_subset ?_ (iUnion₂_subset fun e he => ?_)
    · intro v hv
      by_cases hvR : v ∈ reachV Γ v₀
      · exact Or.inl (Γ₁.V_subset_U (hV₁.symm ▸ hvR))
      · exact Or.inr (Γ₂.V_subset_U (hV₂.symm ▸ ⟨hv, hvR⟩))
    · rcases edge_reach_or_rest Γ he with h₁ | h₂
      · exact (Γ₁.closure_subset_U (hE₁.symm ▸ ⟨he, h₁⟩)).trans subset_union_left
      · exact (Γ₂.closure_subset_U (hE₂.symm ▸ ⟨he, h₂⟩)).trans subset_union_right
  have hU_disj : Disjoint Γ₁.U Γ₂.U := by
    refine Set.disjoint_left.mpr fun z hz₁ hz₂ => ?_
    by_cases hzV : z ∈ Γ.V
    · have hzV₁ : z ∈ Γ₁.V := by
        by_contra hnot
        obtain ⟨e, he₁, hze⟩ := Γ₁.exists_edge_of_mem hz₁ hnot
        exact ((hSub₁.2 he₁).2.1 hze).2 hzV
      have hzV₂ : z ∈ Γ₂.V := by
        by_contra hnot
        obtain ⟨e, he₂, hze⟩ := Γ₂.exists_edge_of_mem hz₂ hnot
        exact ((hSub₂.2 he₂).2.1 hze).2 hzV
      rw [hV₁] at hzV₁
      rw [hV₂] at hzV₂
      exact hzV₂.2 hzV₁
    · have hzV₁ : z ∉ Γ₁.V := fun h => hzV (hSub₁.1 h)
      have hzV₂ : z ∉ Γ₂.V := fun h => hzV (hSub₂.1 h)
      obtain ⟨e₁, he₁, hze₁⟩ := Γ₁.exists_edge_of_mem hz₁ hzV₁
      obtain ⟨e₂, he₂, hze₂⟩ := Γ₂.exists_edge_of_mem hz₂ hzV₂
      have heq : e₁ = e₂ := Γ.edge_eq_of_mem (hSub₁.2 he₁) (hSub₂.2 he₂) hze₁ hze₂
      subst heq
      rw [hE₁] at he₁
      rw [hE₂] at he₂
      rcases Γ.edge_cond e₁ he₁.1 with ⟨a, b, -, hcap, -⟩ | ⟨a, hcap, -⟩
      · have ha : a ∈ closure e₁ ∩ Γ.V := hcap ▸ mem_insert a {b}
        exact (he₂.2 ha).2 (he₁.2 ha)
      · have ha : a ∈ closure e₁ ∩ Γ.V := hcap ▸ mem_singleton a
        exact (he₂.2 ha).2 (he₁.2 ha)
  have hPre₁ : IsPreconnected Γ₁.U := by
    have hwalk_comp : ∀ {u w : S}, u ∈ reachV Γ v₀ → GraphWalk Γ.toGraph u w →
        w ∈ reachV Γ v₀ ∧ w ∈ connectedComponentIn Γ₁.U u := by
      intro u w hu W
      induction W with
      | nil hw =>
        exact ⟨hu, mem_connectedComponentIn (Γ₁.V_subset_U (hV₁.symm ▸ hu))⟩
      | @cons a b c e hl W' ih =>
        have hbR : b ∈ reachV Γ v₀ := by
          obtain ⟨Wa⟩ := hu.2
          exact ⟨hl.right_mem, ⟨Wa.append (GraphWalk.cons hl (GraphWalk.nil hl.right_mem))⟩⟩
        obtain ⟨hcR, hc_comp⟩ := ih hbR
        have he₁ : e ∈ Γ₁.E := by
          rw [hE₁]
          refine ⟨hl.1, fun z hz => ?_⟩
          rw [hl.2.2.2] at hz
          rcases hz with rfl | rfl
          · exact hu
          · exact hbR
        have hcl_pre : IsPreconnected (closure e) :=
          (hl.1.2.2.1.isConnected.isPreconnected).closure
        have hcl_sub : closure e ⊆ Γ₁.U := Γ₁.closure_subset_U he₁
        have ha_cl : a ∈ closure e := by
          have : a ∈ closure e ∩ Γ.V := hl.2.2.2.symm ▸ mem_insert a {b}
          exact this.1
        have hb_cl : b ∈ closure e := by
          have : b ∈ closure e ∩ Γ.V := hl.2.2.2.symm ▸ mem_insert_of_mem a rfl
          exact this.1
        have hb_comp : b ∈ connectedComponentIn Γ₁.U a :=
          hcl_pre.subset_connectedComponentIn ha_cl hcl_sub hb_cl
        rw [connectedComponentIn_eq hb_comp]
        exact ⟨hcR, hc_comp⟩
    have hV₁_comp : ∀ v ∈ Γ₁.V, v ∈ connectedComponentIn Γ₁.U v₀ := by
      intro v hv
      rw [hV₁] at hv
      obtain ⟨W⟩ := hv.2
      exact (hwalk_comp ⟨hv₀, ⟨GraphWalk.nil hv₀⟩⟩ W).2
    have hU₁_sub : Γ₁.U ⊆ connectedComponentIn Γ₁.U v₀ := by
      nth_rw 1 [Γ₁.U_eq]
      refine union_subset hV₁_comp (iUnion₂_subset fun e he₁ => ?_)
      have he_pre : IsPreconnected (closure e) :=
        ((hSub₁.2 he₁).2.2.1.isConnected.isPreconnected).closure
      have he_sub : closure e ⊆ Γ₁.U := Γ₁.closure_subset_U he₁
      rcases Γ.edge_cond e (hSub₁.2 he₁) with ⟨a, b, -, hcap, -⟩ | ⟨a, hcap, -⟩
      · have ha : a ∈ closure e ∩ Γ.V := hcap ▸ mem_insert a {b}
        have ha₁ : a ∈ Γ₁.V := hV₁.symm ▸ (hE₁ ▸ he₁).2 ha
        exact (he_pre.subset_connectedComponentIn ha.1 he_sub).trans
          (connectedComponentIn_eq (hV₁_comp a ha₁)).symm.subset
      · have ha : a ∈ closure e ∩ Γ.V := hcap ▸ mem_singleton a
        have ha₁ : a ∈ Γ₁.V := hV₁.symm ▸ (hE₁ ▸ he₁).2 ha
        exact (he_pre.subset_connectedComponentIn ha.1 he_sub).trans
          (connectedComponentIn_eq (hV₁_comp a ha₁)).symm.subset
    have hU₁_eq : Γ₁.U = connectedComponentIn Γ₁.U v₀ :=
      Subset.antisymm hU₁_sub (connectedComponentIn_subset Γ₁.U v₀)
    rw [hU₁_eq]
    exact isPreconnected_connectedComponentIn
  exact ⟨hSub₁, hSub₂, hV₁, hV₂, hE₁, hE₂, hv₀_mem, hU_union, hU_disj, hPre₁⟩

/-- A drawing `Γ : Drawing S` has a connected graph `IsGraphConnected Γ.toGraph` if and only if
`Γ.V.Nonempty` and `IsPreconnected Γ.U`. -/
theorem isGraphConnected_iff_isPreconnected_U [T2Space S] (Γ : Drawing S) :
    IsGraphConnected Γ.toGraph ↔ Γ.V.Nonempty ∧ IsPreconnected Γ.U := by
  constructor
  · rintro ⟨⟨v₀, hv₀⟩, hwalk⟩
    obtain ⟨_, _, hV₁, hV₂, _, hE₂, _, hU_union, _, hPre₁⟩ := compSubdraw_spec Γ hv₀
    have hV₂_empty : (restSubdraw Γ v₀).V = ∅ := by
      rw [hV₂, eq_empty_iff_forall_notMem]
      rintro v ⟨hv, hvnot⟩
      exact hvnot ⟨hv, hwalk v₀ hv₀ v hv⟩
    have hE₂_empty : (restSubdraw Γ v₀).E = ∅ := by
      rw [hE₂, eq_empty_iff_forall_notMem]
      rintro e ⟨he, he_sub⟩
      rcases Γ.edge_cond e he with ⟨a, b, -, hcap, -⟩ | ⟨a, hcap, -⟩
      · have ha : a ∈ closure e ∩ Γ.V := hcap ▸ mem_insert a {b}
        exact (he_sub ha).2 ⟨ha.2, hwalk v₀ hv₀ a ha.2⟩
      · have ha : a ∈ closure e ∩ Γ.V := hcap ▸ mem_singleton a
        exact (he_sub ha).2 ⟨ha.2, hwalk v₀ hv₀ a ha.2⟩
    have hU₂_empty : (restSubdraw Γ v₀).U = ∅ := by
      rw [(restSubdraw Γ v₀).U_eq, hV₂_empty, hE₂_empty]
      simp
    rw [hU_union, hU₂_empty, union_empty]
    exact ⟨⟨v₀, hv₀⟩, hPre₁⟩
  · rintro ⟨⟨v₀, hv₀⟩, hPre⟩
    obtain ⟨_, _, hV₁, hV₂, _, _, hv₀_mem, hU_union, hU_disj, _⟩ := compSubdraw_spec Γ hv₀
    have hU₂_empty : (restSubdraw Γ v₀).U = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro w hw
      obtain ⟨z, -, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp hPre
        (compSubdraw Γ v₀).U (restSubdraw Γ v₀).U
        (compSubdraw Γ v₀).isClosed_U (restSubdraw Γ v₀).isClosed_U
        hU_union.subset
        ⟨v₀, hU_union ▸ Or.inl ((compSubdraw Γ v₀).V_subset_U hv₀_mem),
          (compSubdraw Γ v₀).V_subset_U hv₀_mem⟩
        ⟨w, hU_union ▸ Or.inr hw, hw⟩
      exact Set.disjoint_left.mp hU_disj hz₁ hz₂
    have hreach_all : ∀ v ∈ Γ.V, Nonempty (GraphWalk Γ.toGraph v₀ v) := by
      intro v hv
      by_contra hnot
      have hv₂ : v ∈ (restSubdraw Γ v₀).U :=
        (restSubdraw Γ v₀).V_subset_U (hV₂.symm ▸ ⟨hv, fun hR => hnot hR.2⟩)
      rw [hU₂_empty] at hv₂
      exact hv₂
    refine ⟨⟨v₀, hv₀⟩, fun u hu v hv => ?_⟩
    obtain ⟨Wu⟩ := hreach_all u hu
    obtain ⟨Wv⟩ := hreach_all v hv
    exact ⟨Wu.reverse.append Wv⟩

/-- In a sphere `S`, if a drawing `Γ : Drawing S` has `Γ.U.Nonempty` and `IsPreconnected Γ.U`,
then every region `q ∈ Γ.R` is an open disc (`IsOpenDisc q`) and its frontier is preconnected. -/
theorem isOpenDisc_and_isPreconnected_frontier_of_isPreconnected_U [ConnectedSpace S]
    (hS : IsClosedSurface S) (hSph : IsSphere S)
    {Γ : Drawing S} (hUne : Γ.U.Nonempty) (hPre : IsPreconnected Γ.U)
    {q : Set S} (hq : q ∈ Γ.R) :
    IsOpenDisc q ∧ IsPreconnected (frontier q) := by
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  have h₄ : ∀ F : Set S, F ⊆ q → IsOArc F → ∃ Δ : Set S, Δ ⊆ q ∧ IsClosedDisc Δ ∧ discBd Δ = F := by
    intro F hF hO
    obtain ⟨Δ, h₁, h₂, h₃⟩ := GM11.exists_disc_missing hS hSph hO hPre
      (Set.disjoint_left.mpr fun x hx hxF => GM11.region_subset hq (hF hxF) hx)
    obtain ⟨z, hz⟩ : F.Nonempty := by
      obtain ⟨φ⟩ := hO
      exact ⟨(φ 1).1, (φ 1).2⟩
    have hzΔ : z ∈ Δ := GM11.discBd_subset Δ (h₂ ▸ hz)
    exact ⟨Δ, GM11.subset_region hq (IsClosedDisc.isPathConnected h₁).isConnected.isPreconnected
      h₃ hzΔ (hF hz), h₁, h₂⟩
  have hdisc : IsOpenDisc q := by
    rcases open_disc S q hS inferInstance
        ⟨GM11.region_nonempty hq, GM11.region_isPreconnected hq⟩
        (GM11.region_isOpen hq) h₄ with h | h
    · obtain ⟨x, hx⟩ := hUne
      exact (GM11.region_subset hq (h.2 ▸ mem_univ x) hx).elim
    · exact h
  exact ⟨hdisc, GM11.isPreconnected_frontier hdisc⟩

end DrawingConnectivity

/-! ## Part 2: Unified Chord-Addition Lemma (`addChordInRegion_spec`) -/

section AddChord

variable [T2Space S]

/-- If `D : Drawing S` and `K : Set S` is a line (`IsLineWithEnds K v₁ v₂`) between two distinct
vertices `v₁, v₂ ∈ D.V` whose interior `K \ {v₁, v₂}` lies in a region `q ∈ D.R`, then
`D.U ∩ (lineDrawing hK hv₁v₂).U ⊆ D.V ∩ (lineDrawing hK hv₁v₂).V`. -/
theorem lineDrawing_meet_of_subset_region {D : Drawing S} {q K : Set S} {v₁ v₂ : S}
    (hq : q ∈ D.R) (hv₁ : v₁ ∈ D.V) (hv₂ : v₂ ∈ D.V)
    (hK : IsLineWithEnds K v₁ v₂) (hv₁v₂ : v₁ ≠ v₂) (hKq : K \ {v₁, v₂} ⊆ q) :
    D.U ∩ (GM11.lineDrawing hK hv₁v₂).U ⊆ D.V ∩ (GM11.lineDrawing hK hv₁v₂).V := by
  rintro y ⟨hyU, hyK⟩
  have hy_pair : y ∈ ({v₁, v₂} : Set S) := by
    by_contra hnot
    exact GM11.region_subset hq (hKq ⟨hyK, hnot⟩) hyU
  rcases hy_pair with rfl | rfl
  · exact ⟨hv₁, Or.inl rfl⟩
  · exact ⟨hv₂, Or.inr rfl⟩

/-- When `d' = 0`, `innerDraw D 0 C = D`. -/
theorem innerDraw_zero_eq (D : Drawing S) (C : Fin 0 → Drawing S) :
    innerDraw D 0 C = D := by
  obtain ⟨hSub, hV, hE, _⟩ := innerDraw_spec D 0 C
  have hV_eq : (innerDraw D 0 C).V = D.V := by
    rw [hV, iUnion_of_empty, sdiff_empty]
  have hE_eq : (innerDraw D 0 C).E = D.E := by
    rw [hE]
    ext e
    simp only [iUnion_of_empty, sdiff_empty, mem_ofPred_eq, and_iff_left_iff_imp]
    exact fun _ => inter_subset_right
  have hU_eq : (innerDraw D 0 C).U = D.U := by
    rw [(innerDraw D 0 C).U_eq, D.U_eq, hV_eq, hE_eq]
  cases h1 : innerDraw D 0 C
  cases h2 : D
  rw [h1, h2] at hU_eq hV_eq
  dsimp only at hU_eq hV_eq
  subst hU_eq hV_eq
  rfl

/-- Unified Chord-Addition Lemma for (2.2):
Adding a chord `K` (`IsLineWithEnds K v₁ v₂`, `K \ {v₁, v₂} ⊆ q`) inside a region `q ∈ D.R`
(`q ⊆ R_N`, `∀ hd' : 0 < d', q ⊆ interior (Δ ⟨d' - 1, ...⟩)`) between two distinct non-adjacent
vertices `v₁, v₂ ∈ (perimDraw (innerDraw D d' C) R_N).V` preserves all inductive invariants of
(2.2) while keeping `(innerDraw D' d' C).V = (innerDraw D d' C).V` and increasing
`|(innerDraw D' d' C).E|` by `1`, provided `R_N' ∈ (innerDraw D' d' C).R` satisfies `R_N' ⊆ R_N`,
`R_N \ q ⊆ R_N'`, and `(perimDraw N R_N).V ⊆ (perimDraw N' R_N').V`. -/
theorem addChordInRegion_spec [ConnectedSpace S]
    (hS : IsClosedSurface S) (hSph : IsSphere S)
    {D : Drawing S} {r₀ R_N q K : Set S} {d d' : ℕ}
    {C : Fin d' → Drawing S} {Δ : Fin d' → Set S} {v₁ v₂ : S}
    (hd'd : d' < d)
    (hShell : SurfaceDShell D r₀ d' C Δ)
    (hOuter : HasAtMostOneOuterEdge D d' C)
    (hSimple : D.toGraph.Simple)
    (hrad : HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D r₀ hShell.r₀_mem) d)
    (hRN : R_N ∈ (innerDraw D d' C).R) (hr₀_sub : r₀ ⊆ R_N)
    (hcard3 : 3 ≤ (perimDraw (innerDraw D d' C) R_N).V.ncard)
    (hq : q ∈ D.R) (hq_RN : q ⊆ R_N)
    (hq_int : ∀ hd' : 0 < d', q ⊆ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩))
    (hv₁ : v₁ ∈ (perimDraw (innerDraw D d' C) R_N).V)
    (hv₂ : v₂ ∈ (perimDraw (innerDraw D d' C) R_N).V)
    (hv₁v₂ : v₁ ≠ v₂) (hnotAdj : ¬ D.toGraph.Adj v₁ v₂)
    (hK : IsLineWithEnds K v₁ v₂) (hKq : K \ {v₁, v₂} ⊆ q)
    (hv₁D : v₁ ∈ D.V) (hv₂D : v₂ ∈ D.V) :
    let D' := D.glue (GM11.lineDrawing hK hv₁v₂)
      (lineDrawing_meet_of_subset_region hq hv₁D hv₂D hK hv₁v₂ hKq)
    ∀ {R_N' : Set S},
      R_N' ∈ (innerDraw D' d' C).R →
      R_N' ⊆ R_N →
      R_N \ q ⊆ R_N' →
      (perimDraw (innerDraw D d' C) R_N).V ⊆ (perimDraw (innerDraw D' d' C) R_N').V →
      ∃ (r₀' : Set S) (hr₀' : r₀' ∈ D'.R),
        SurfaceDShell D' r₀' d' C Δ ∧
        HasAtMostOneOuterEdge D' d' C ∧
        D'.toGraph.Simple ∧
        IsIsoMinor D.toGraph D'.toGraph ∧
        HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D' r₀' hr₀') d ∧
        R_N' ∈ (innerDraw D' d' C).R ∧
        r₀' ⊆ R_N' ∧
        3 ≤ (perimDraw (innerDraw D' d' C) R_N').V.ncard ∧
        (innerDraw D' d' C).V = (innerDraw D d' C).V ∧
        (innerDraw D' d' C).E.ncard = (innerDraw D d' C).E.ncard + 1 := by
  intro D' R_N' hRN' hRN'_sub hRN_sdiff_sub hPV_sub
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  let hmeet := lineDrawing_meet_of_subset_region hq hv₁D hv₂D hK hv₁v₂ hKq
  let e_new : Set S := K \ {v₁, v₂}
  let N := innerDraw D d' C
  let N' := innerDraw D' d' C
  obtain ⟨hNs, hNV, hNE, _⟩ := innerDraw_spec D d' C
  obtain ⟨hN's, hN'V, hN'E, _⟩ := innerDraw_spec D' d' C
  obtain ⟨hBs, hBV, _, _, _⟩ := perimDraw_spec hS hRN
  obtain ⟨hB's, hB'V, _, _, _⟩ := perimDraw_spec hS hRN'
  have hv₁_NV : v₁ ∈ N.V := (hBV ▸ hv₁).1
  have hv₂_NV : v₂ ∈ N.V := (hBV ▸ hv₂).1
  have hV_sub_L : (GM11.lineDrawing hK hv₁v₂).V ⊆ D.V := by
    rintro z (rfl | rfl)
    · exact hv₁D
    · exact hv₂D
  have hD'V : D'.V = D.V := union_eq_left.mpr hV_sub_L
  have hD'U : D'.U = D.U ∪ K := rfl
  have hD'U_e : D'.U = D.U ∪ e_new := by
    refine Subset.antisymm (union_subset subset_union_left fun z hzK => ?_)
      (union_subset_union_right _ sdiff_subset)
    by_cases hz : z ∈ ({v₁, v₂} : Set S)
    · exact Or.inl (D.V_subset_U (hV_sub_L hz))
    · exact Or.inr ⟨hzK, hz⟩
  have hD'E : D'.E = insert e_new D.E := by
    change (D.glue (GM11.lineDrawing hK hv₁v₂) hmeet).E = insert e_new D.E
    rw [Drawing.glue_E, GM11.lineDrawing_E, union_singleton]
  have he_new_mem : e_new ∈ D'.E := hD'E ▸ mem_insert e_new D.E
  have he_new_not_DE : e_new ∉ D.E := by
    intro heD
    obtain ⟨z, hz⟩ := (GM11.isPathConnected_sdiff_pair hK).nonempty
    exact GM11.region_subset hq (hKq hz) ((heD.2.1 hz).1)
  have hcl_enew : closure e_new = K := GM11.closure_sdiff_pair hK
  have hcap_enew : closure e_new ∩ D'.V = {v₁, v₂} := by
    rw [hcl_enew, hD'V]
    refine Subset.antisymm (fun z ⟨hzK, hzV⟩ => ?_) ?_
    · by_contra hnot
      exact GM11.region_subset hq (hKq ⟨hzK, hnot⟩) (D.V_subset_U hzV)
    · rintro z (rfl | rfl)
      · exact ⟨(GM11.lineDrawing hK hv₁v₂).V_subset_U (Or.inl rfl), hv₁D⟩
      · exact ⟨(GM11.lineDrawing hK hv₁v₂).V_subset_U (Or.inr rfl), hv₂D⟩
  have hle : D.toGraph ≤ D'.toGraph := by
    refine ⟨by change D.V ⊆ D'.V; rw [hD'V], ?_⟩
    intro e u v ⟨he, hu, hv, hcap⟩
    refine ⟨hD'E ▸ mem_insert_of_mem e_new he, hD'V.symm ▸ hu, hD'V.symm ▸ hv, ?_⟩
    rwa [hD'V]
  have hSimple' : D'.toGraph.Simple :=
    { not_isLoopAt := fun e z ⟨he, _, _, hcap⟩ => by
        rw [hD'E, mem_insert_iff] at he
        rcases he with rfl | heD
        · rw [hcap_enew] at hcap
          rcases pair_eq_pair_iff.mp hcap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hv₁v₂ rfl
        · rw [hD'V] at hcap
          have hzD : z ∈ D.V := by
            have : z ∈ ({z, z} : Set S) := mem_insert z {z}
            rw [← hcap] at this
            exact this.2
          exact hSimple.not_isLoopAt e z ⟨heD, hzD, hzD, hcap⟩
      eq_of_isLink := fun e₁ e₂ u v ⟨he₁, _, _, hcap₁⟩ ⟨he₂, _, _, hcap₂⟩ => by
        rw [hD'E, mem_insert_iff] at he₁ he₂
        rcases he₁ with rfl | he₁D <;> rcases he₂ with rfl | he₂D
        · rfl
        · exfalso
          rw [hcap_enew] at hcap₁
          rw [hD'V] at hcap₂
          have hl : D.toGraph.IsLink e₂ v₁ v₂ :=
            ⟨he₂D, hv₁D, hv₂D, hcap₂.trans hcap₁.symm⟩
          exact hnotAdj ⟨e₂, hl⟩
        · exfalso
          rw [hcap_enew] at hcap₂
          rw [hD'V] at hcap₁
          have hl : D.toGraph.IsLink e₁ v₁ v₂ :=
            ⟨he₁D, hv₁D, hv₂D, hcap₁.trans hcap₂.symm⟩
          exact hnotAdj ⟨e₁, hl⟩
        · rw [hD'V] at hcap₁ hcap₂
          have huD : u ∈ D.V := by
            have : u ∈ ({u, v} : Set S) := mem_insert u {v}
            rw [← hcap₁] at this
            exact this.2
          have hvD : v ∈ D.V := by
            have : v ∈ ({u, v} : Set S) := mem_insert_of_mem u rfl
            rw [← hcap₁] at this
            exact this.2
          exact hSimple.eq_of_isLink ⟨he₁D, huD, hvD, hcap₁⟩ ⟨he₂D, huD, hvD, hcap₂⟩ }
  have hr_ne_q : ∀ r ∈ D.R, r ≠ q → r ∈ D'.R := by
    intro r hr hne
    have hdisj_rq : Disjoint r q :=
      Set.disjoint_left.mpr fun z hzr hzq => hne (GM11.region_eq_of_mem hr hq hzr hzq)
    obtain ⟨w, hw⟩ := GM11.region_nonempty hr
    have hw_not_D'U : w ∉ D'.U := by
      rw [hD'U_e]
      exact not_or.mpr ⟨GM11.region_subset hr hw, fun hwe => Set.disjoint_left.mp hdisj_rq hw (hKq hwe)⟩
    obtain ⟨r', hr', hwr'⟩ := GM11.exists_region_of_notMem hw_not_D'U
    have hr_sub_r' : r ⊆ r' :=
      GM11.subset_region hr' (GM11.region_isPreconnected hr)
        (Set.disjoint_left.mpr fun z hzr hzD' => by
          rw [hD'U_e] at hzD'
          rcases hzD' with hzD | hze
          · exact GM11.region_subset hr hzr hzD
          · exact Set.disjoint_left.mp hdisj_rq hzr (hKq hze))
        hw hwr'
    have hr'_sub_r : r' ⊆ r :=
      GM11.subset_region hr (GM11.region_isPreconnected hr')
        (Set.disjoint_left.mpr fun z hzr' hzD =>
          GM11.region_subset hr' hzr' (hD'U ▸ Or.inl hzD))
        hwr' hw
    exact Subset.antisymm hr'_sub_r hr_sub_r' ▸ hr'
  have hr'_dic : ∀ r' ∈ D'.R, (r' ∈ D.R ∧ r' ≠ q) ∨ (r' ⊆ q ∧ v₁ ∈ closure r' ∧ v₂ ∈ closure r') := by
    intro r' hr'
    obtain ⟨z₀, hz₀⟩ := GM11.region_nonempty hr'
    have hz₀_not_DU : z₀ ∉ D.U := fun h => GM11.region_subset hr' hz₀ (hD'U ▸ Or.inl h)
    obtain ⟨r, hr, hz₀_r⟩ := GM11.exists_region_of_notMem hz₀_not_DU
    have hr'_sub_r : r' ⊆ r :=
      GM11.subset_region hr (GM11.region_isPreconnected hr')
        (Set.disjoint_left.mpr fun z hzr' hzU =>
          GM11.region_subset hr' hzr' (hD'U ▸ Or.inl hzU))
        hz₀ hz₀_r
    by_cases hrq : r = q
    · subst r
      refine Or.inr ⟨hr'_sub_r, ?_⟩
      have hmeet_e : (e_new ∩ closure r').Nonempty := by
        by_contra hnot_meet
        rw [not_nonempty_iff_eq_empty] at hnot_meet
        have hq_cov : q ⊆ r' ∪ (closure r')ᶜ := by
          intro z hzq
          by_cases hzcl : z ∈ closure r'
          · refine Or.inl ?_
            have hz_not_DU : z ∉ D.U := GM11.region_subset hq hzq
            have hz_not_enew : z ∉ e_new := fun hze => by
              have : z ∈ (∅ : Set S) := hnot_meet ▸ ⟨hze, hzcl⟩
              exact this
            have hz_not_D'U : z ∉ D'.U := by
              rw [hD'U_e]
              exact not_or.mpr ⟨hz_not_DU, hz_not_enew⟩
            obtain ⟨r'', hr'', hzr''⟩ := GM11.exists_region_of_notMem hz_not_D'U
            obtain ⟨w, hwr'', hwr'⟩ :=
              mem_closure_iff.mp hzcl r'' (GM11.region_isOpen hr'') hzr''
            rwa [GM11.region_eq_of_mem hr'' hr' hwr'' hwr'] at hzr''
          · exact Or.inr hzcl
        have hdisj_open : Disjoint r' (closure r')ᶜ :=
          Set.disjoint_left.mpr fun z hzr' hnot => hnot (subset_closure hzr')
        rcases (GM11.region_isPreconnected hq).subset_or_subset
            (GM11.region_isOpen hr') isClosed_closure.isOpen_compl hdisj_open hq_cov with h₁ | h₂
        · obtain ⟨w, hw⟩ := (GM11.isPathConnected_sdiff_pair hK).nonempty
          exact GM11.region_subset hr' (h₁ (hKq hw)) (Or.inr hw.1)
        · exact h₂ (hr'_sub_r hz₀) (subset_closure hz₀)
      have he_cl : e_new ⊆ closure r' :=
        GM11.edge_subset_closure_of_incident hS he_new_mem hr' hmeet_e
      have hK_cl : K ⊆ closure r' := hcl_enew ▸ closure_minimal he_cl isClosed_closure
      exact ⟨hK_cl ((GM11.lineDrawing hK hv₁v₂).V_subset_U (Or.inl rfl)),
        hK_cl ((GM11.lineDrawing hK hv₁v₂).V_subset_U (Or.inr rfl))⟩
    · have hr_D' : r ∈ D'.R := hr_ne_q r hr hrq
      have hr'_eq : r' = r := GM11.region_eq_of_mem hr' hr_D' hz₀ hz₀_r
      exact Or.inl ⟨hr'_eq ▸ hr, hr'_eq ▸ hrq⟩
  have hN'V_eq : N'.V = N.V := by
    rw [hN'V, hNV, hD'V]
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
        · exact hv₁_NV
        · exact hv₂_NV
      · exact ⟨Or.inr heD, hsub⟩
  have he_new_not_NE : e_new ∉ N.E := fun h => he_new_not_DE (hNs.2 h)
  have hN'E_card : N'.E.ncard = N.E.ncard + 1 := by
    rw [hN'E_eq, ncard_insert_of_notMem he_new_not_NE N.finite_edges]
  have hOuter' : HasAtMostOneOuterEdge D' d' C := by
    intro v hv
    rw [hD'V] at hv
    have hset_eq :
        {e ∈ D'.E | v ∈ closure e ∧ ¬ (closure e ∩ D'.V ⊆ D'.V \ ⋃ i, (C i).V)} =
        {e ∈ D.E | v ∈ closure e ∧ ¬ (closure e ∩ D.V ⊆ D.V \ ⋃ i, (C i).V)} := by
      ext e
      simp only [mem_ofPred_eq, hD'E, hD'V, mem_insert_iff]
      constructor
      · rintro ⟨rfl | heD, hve, hnot⟩
        · exfalso
          apply hnot
          rw [← hNV, ← hD'V, hcap_enew]
          rintro z (rfl | rfl)
          · exact hv₁_NV
          · exact hv₂_NV
        · exact ⟨heD, hve, hnot⟩
      · rintro ⟨heD, hve, hnot⟩
        exact ⟨Or.inr heD, hve, hnot⟩
    rw [hset_eq]
    exact hOuter v hv
  have hcard3' : 3 ≤ (perimDraw N' R_N').V.ncard :=
    hcard3.trans (ncard_le_ncard hPV_sub
      (N'.finite_V.subset (hB'V ▸ inter_subset_left)))
  have hPV_cl : N.V ∩ closure R_N ⊆ N'.V ∩ closure R_N' := by
    rwa [← hBV, ← hB'V]
  by_cases hd' : 0 < d'
  · let j_last : Fin d' := ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩
    have hr_disj_mem : ∀ {r : Set S} (j : Fin d'), r ∈ D.R → Disjoint r (Δ j) → r ∈ D'.R := by
      intro r j hr hdisj
      refine hr_ne_q r hr fun hrq => ?_
      obtain ⟨z₀, hz₀⟩ := GM11.region_nonempty hq
      have hz₀_last : z₀ ∈ interior (Δ j_last) := hq_int hd' hz₀
      have hz₀_Δj : z₀ ∈ Δ j := by
        by_cases hjeq : j = j_last
        · exact hjeq ▸ interior_subset hz₀_last
        · have hjlt : j < j_last :=
            lt_of_le_of_ne (Fin.le_def.mpr (Nat.le_sub_one_of_lt j.2)) hjeq
          exact interior_subset (hShell.disc_subset_interior hjlt (interior_subset hz₀_last))
      exact Set.disjoint_left.mp hdisj (hrq ▸ hz₀) hz₀_Δj
    have hr₀' : r₀ ∈ D'.R := hr_disj_mem j_last hShell.r₀_mem (hShell.disjoint_inf j_last).symm
    have hr₀_sub_RN' : r₀ ⊆ R_N' := by
      refine (subset_sdiff.mpr ⟨hr₀_sub, ?_⟩).trans hRN_sdiff_sub
      exact (hShell.disjoint_inf j_last).symm.mono_right
        ((hq_int hd').trans interior_subset)
    have hC_sub' : ∀ j : Fin d', (C j).IsSubdrawing D' := fun j =>
      ⟨hD'V ▸ (hShell.isSubdrawing j).1,
       fun e he => hD'E ▸ mem_insert_of_mem e_new ((hShell.isSubdrawing j).2 he)⟩
    have hShell' : SurfaceDShell D' r₀ d' C Δ :=
      { r₀_mem := hr₀'
        isSubdrawing := hC_sub'
        isCircuit := hShell.isCircuit
        isClosedDisc := hShell.isClosedDisc
        discBd_eq := hShell.discBd_eq
        disjoint_inf := hShell.disjoint_inf
        disjoint_V := hShell.disjoint_V
        disc_subset_interior := hShell.disc_subset_interior
        vertex_in_or_inside := fun hd'₀ v hv => hShell.vertex_in_or_inside hd'₀ v (hD'V ▸ hv)
        edge_induced := fun j e u v ⟨he, hu, hv, hcap⟩ huC hvC => by
          rw [hD'E, mem_insert_iff] at he
          rcases he with rfl | heD
          · exfalso
            have hv₁_u : v₁ ∈ ({u, v} : Set S) := by
              rw [← hcap, hcap_enew]; exact mem_insert v₁ {v₂}
            rcases hv₁_u with rfl | rfl
            · exact (hNV ▸ hv₁_NV).2 (mem_iUnion.mpr ⟨j, huC⟩)
            · exact (hNV ▸ hv₁_NV).2 (mem_iUnion.mpr ⟨j, hvC⟩)
          · rw [hD'V] at hcap
            exact hShell.edge_induced j ⟨heD, hD'V ▸ hu, hD'V ▸ hv, hcap⟩ huC hvC
        edge_inside_of_ends := fun j e he hnot_ends => by
          rw [hD'E, mem_insert_iff] at he
          rcases he with rfl | heD
          · have hq_sub : q ⊆ interior (Δ j) := by
              by_cases hjeq : j = j_last
              · exact hjeq ▸ hq_int hd'
              · have hjlt : j < j_last :=
                  lt_of_le_of_ne (Fin.le_def.mpr (Nat.le_sub_one_of_lt j.2)) hjeq
                exact (hq_int hd').trans
                  (interior_subset.trans (hShell.disc_subset_interior hjlt))
            exact hKq.trans hq_sub
          · rw [hD'V] at hnot_ends
            exact hShell.edge_inside_of_ends j e heD hnot_ends
        shell_vertex_chain := fun j u huC => by
          obtain ⟨r_u, hru_D, hu_cl, hru_disj, k, hk_le, R_seq, hseq_D, hseq_0, hseq_k,
              hseq_disj, hseq_step⟩ := hShell.shell_vertex_chain j u huC
          refine ⟨r_u, hr_disj_mem j hru_D hru_disj, hu_cl, hru_disj, k, hk_le, R_seq,
            fun m => hr_disj_mem j (hseq_D m) (hseq_disj m), hseq_0, hseq_k, hseq_disj,
            fun m => ?_⟩
          obtain ⟨w, hwD, hw_not_int, hw1, hw2⟩ := hseq_step m
          exact ⟨w, hD'V.symm ▸ hwD, hw_not_int, hw1, hw2⟩ }
    have hrad' : HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D' r₀ hr₀') d := by
      refine hasDrawingRadiusLE_of_modify_in_RN hS hSph hShell hd'd hrad hr₀' hRN hr₀_sub
        hRN' hr₀_sub_RN' hC_sub'
        (fun _ v hvD' hvΔ => by
          have hvD : v ∈ D.V := hD'V ▸ hvD'
          rcases hShell.vertex_in_or_inside hd' v hvD with ⟨i, hvi⟩ | hv_int
          · by_cases hij : i = j_last
            · subst hij
              exact Or.inl hvi
            · exfalso
              have hilt : i < j_last :=
                lt_of_le_of_ne (Fin.le_def.mpr (Nat.le_sub_one_of_lt i.2)) hij
              have hv_int_i : v ∈ interior (Δ i) := hShell.disc_subset_interior hilt hvΔ
              rw [← discInt_eq_interior_of_isClosedDisc hS (hShell.isClosedDisc i)] at hv_int_i
              exact hv_int_i.2 ((hShell.discBd_eq i).symm ▸ (C i).V_subset_U hvi)
          · refine Or.inr (hN'V_eq.symm ▸ hNV.symm ▸ ⟨hvD, ?_⟩)
            intro h_un
            obtain ⟨i, hvi⟩ := mem_iUnion.mp h_un
            have hv_int_i : v ∈ interior (Δ i) := by
              by_cases hij : i = j_last
              · subst hij; exact hv_int
              · have hilt : i < j_last :=
                  lt_of_le_of_ne (Fin.le_def.mpr (Nat.le_sub_one_of_lt i.2)) hij
                exact hShell.disc_subset_interior hilt (interior_subset hv_int)
            rw [← discInt_eq_interior_of_isClosedDisc hS (hShell.isClosedDisc i)] at hv_int_i
            exact hv_int_i.2 ((hShell.discBd_eq i).symm ▸ (C i).V_subset_U hvi))
        (fun _ => rfl)
        (fun _ _ hr hdisj => hr_disj_mem j_last hr hdisj)
        (fun _ _ hw _ => hD'V.symm ▸ hw)
        hPV_cl
        (fun _ w hwN' => by
          have hwN : w ∈ N.V := hN'V_eq ▸ hwN'
          rcases hShell.vertex_in_or_inside hd' w (hNs.1 hwN) with ⟨i, hwi⟩ | hw_int
          · exact ((hNV ▸ hwN).2 (mem_iUnion.mpr ⟨i, hwi⟩)).elim
          · exact hw_int)
        (fun r hr hdisj => hr_ne_q r hr fun hrq => by
          obtain ⟨z, hz⟩ := GM11.region_nonempty hq
          exact Set.disjoint_left.mp hdisj (hrq ▸ hz) (hq_RN hz))
        (fun _ hw _ => hD'V.symm ▸ hw)
        (fun q' hq' => ?_)
      rcases hr'_dic q' hq' with ⟨hq'D, hq'ne⟩ | ⟨_, hv₁_cl, _⟩
      · by_cases hzone : q' ⊆ R_N ∧
            ∀ hd'₀ : 0 < d', q' ⊆ interior (Δ ⟨d' - 1, Nat.sub_lt hd'₀ zero_lt_one⟩)
        · refine Or.inl ⟨?_, hzone.2⟩
          have hdisj_q : Disjoint q' q :=
            Set.disjoint_left.mpr fun z hzq' hzq => hq'ne (GM11.region_eq_of_mem hq'D hq hzq' hzq)
          exact fun z hzq' => hRN_sdiff_sub ⟨hzone.1 hzq', Set.disjoint_left.mp hdisj_q hzq'⟩
        · exact Or.inr (Or.inl ⟨hq'D, hzone⟩)
      · exact Or.inr (Or.inr
          ⟨v₁, (hPV_cl (hBV ▸ hv₁)).1, (hPV_cl (hBV ▸ hv₁)).2, hv₁_cl⟩)
    exact ⟨r₀, hr₀', hShell', hOuter', hSimple', isIsoMinor_of_le hle, hrad',
      hRN', hr₀_sub_RN', hcard3', hN'V_eq, hN'E_card⟩
  · have hd'0 : d' = 0 := Nat.eq_zero_of_not_pos hd'
    subst hd'0
    have hN_eq : N = D := innerDraw_zero_eq D C
    have hN'_eq : N' = D' := innerDraw_zero_eq D' C
    have hRN_eq_r₀ : R_N = r₀ := by
      obtain ⟨p₀, hp₀⟩ := GM11.region_nonempty hShell.r₀_mem
      exact GM11.region_eq_of_mem (hN_eq ▸ hRN) hShell.r₀_mem (hr₀_sub hp₀) hp₀
    have hq_eq_r₀ : q = r₀ := by
      obtain ⟨z₀, hz₀⟩ := GM11.region_nonempty hq
      exact GM11.region_eq_of_mem hq hShell.r₀_mem hz₀ (hRN_eq_r₀ ▸ hq_RN hz₀)
    have hr₀' : R_N' ∈ D'.R := hN'_eq ▸ hRN'
    have hShell' : SurfaceDShell D' R_N' 0 C Δ :=
      { r₀_mem := hr₀'
        isSubdrawing := fun j => Fin.elim0 j
        isCircuit := fun j => Fin.elim0 j
        isClosedDisc := fun j => Fin.elim0 j
        discBd_eq := fun j => Fin.elim0 j
        disjoint_inf := fun j => Fin.elim0 j
        disjoint_V := fun j => Fin.elim0 j
        disc_subset_interior := fun j => Fin.elim0 j
        vertex_in_or_inside := fun h => (Nat.lt_irrefl 0 h).elim
        edge_inside_of_ends := fun j => Fin.elim0 j
        edge_induced := fun j => Fin.elim0 j
        shell_vertex_chain := fun j => Fin.elim0 j }
    have hrad' : HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D' R_N' hr₀') d := by
      change ∀ R' ∈ D'.R, ∃ k ≤ d, ∃ R_seq : Fin (k + 1) → Set S,
        (∀ j, R_seq j ∈ D'.R) ∧
        R_seq ⟨0, Nat.zero_lt_succ k⟩ = R_N' ∧
        R_seq ⟨k, Nat.lt_succ_self k⟩ = R' ∧
        ∀ j : Fin k, ∃ v ∈ D'.V,
          v ∈ closure (R_seq ⟨j.1, Nat.lt_succ_of_lt j.2⟩) ∧
          v ∈ closure (R_seq ⟨j.1 + 1, Nat.add_lt_add_right j.2 1⟩)
      intro R' hR'
      rcases hr'_dic R' hR' with ⟨hR'D, hR'ne⟩ | ⟨_, hv₁_cl, _⟩
      · obtain ⟨k, hkd, R_seq, hseq_mem, hseq_0, hseq_k, hseq_step⟩ := hrad R' hR'D
        change Fin (k + 1) → Set S at R_seq
        change ∀ j, R_seq j ∈ D.R at hseq_mem
        change R_seq 0 = r₀ at hseq_0
        change R_seq ⟨k, Nat.lt_succ_self k⟩ = R' at hseq_k
        change ∀ j : Fin k, ∃ v ∈ D.V,
          v ∈ closure (R_seq ⟨j.1, Nat.lt_succ_of_lt j.2⟩) ∧
          v ∈ closure (R_seq ⟨j.1 + 1, Nat.add_lt_add_right j.2 1⟩) at hseq_step
        let R_seq' : Fin (k + 1) → Set S := fun j => if R_seq j = r₀ then R_N' else R_seq j
        refine ⟨k, hkd, R_seq', fun j => ?_, ?_, ?_, fun j => ?_⟩
        · dsimp [R_seq']
          split_ifs with hj
          · exact hr₀'
          · exact hr_ne_q (R_seq j) (hseq_mem j) (hq_eq_r₀ ▸ hj)
        · dsimp [R_seq']
          simp only [hseq_0, ↓reduceIte]
        · dsimp [R_seq']
          rw [hseq_k]
          exact ite_eq_right_iff.mpr fun h => (hR'ne (hq_eq_r₀.symm ▸ h)).elim
        · obtain ⟨w, hwD, hw1, hw2⟩ := hseq_step j
          refine ⟨w, hD'V.symm ▸ hwD, ?_, ?_⟩
          · dsimp [R_seq']
            split_ifs with h1
            · rw [h1] at hw1
              exact (hPV_cl ⟨hN_eq ▸ hwD, hRN_eq_r₀ ▸ hw1⟩).2
            · exact hw1
          · dsimp [R_seq']
            split_ifs with h2
            · rw [h2] at hw2
              exact (hPV_cl ⟨hN_eq ▸ hwD, hRN_eq_r₀ ▸ hw2⟩).2
            · exact hw2
      · refine ⟨1, hd'd, ![R_N', R'], ?_, rfl, rfl, ?_⟩
        · intro j
          fin_cases j
          · exact hr₀'
          · exact hR'
        · intro j
          fin_cases j
          exact ⟨v₁, hD'V.symm ▸ hv₁D, (hPV_cl (hBV ▸ hv₁)).2, hv₁_cl⟩
    exact ⟨R_N', hr₀', hShell', hOuter', hSimple', isIsoMinor_of_le hle, hrad',
      hRN', Subset.rfl, hcard3', hN'V_eq, hN'E_card⟩

end AddChord

/-! ## Part 3: Claim (1) of (2.2) (`lemma_2_2_claim_1`) -/

section Claim1

variable [T2Space S]

/-- **Claim (1) of (2.2)** (Graph Minors III, Section 2, page 53):
"(1) *$C_{d'}$ is connected.*

For if not, it follows from (S2) applied to $C_{d'-1}$ that there are vertices $v_1$, $v_2$ of $C_{d'}$ in different components of $C_{d'}$, and hence of $H$ but incident with the same region of $M'$. We add an edge joining them. The resulting graph still satisfies (i)–(iv), contrary to (v)." -/
theorem lemma_2_2_claim_1 [ConnectedSpace S]
    (hS : IsClosedSurface S) (hSph : IsSphere S)
    {D : Drawing S} {r₀ R_N : Set S} {d d' : ℕ}
    {C : Fin d' → Drawing S} {Δ : Fin d' → Set S}
    (hd'd : d' < d)
    (hShell : SurfaceDShell D r₀ d' C Δ)
    (hOuter : HasAtMostOneOuterEdge D d' C)
    (hSimple : D.toGraph.Simple)
    (hrad : HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D r₀ hShell.r₀_mem) d)
    (hRN : R_N ∈ (innerDraw D d' C).R) (hr₀_sub : r₀ ⊆ R_N)
    (hcard3 : 3 ≤ (perimDraw (innerDraw D d' C) R_N).V.ncard)
    (hnot_conn : ¬ IsGraphConnected (perimDraw (innerDraw D d' C) R_N).toGraph) :
    ∃ (D' : Drawing S) (r₀' R_N' : Set S) (hr₀' : r₀' ∈ D'.R),
      SurfaceDShell D' r₀' d' C Δ ∧
      HasAtMostOneOuterEdge D' d' C ∧
      D'.toGraph.Simple ∧
      IsIsoMinor D.toGraph D'.toGraph ∧
      HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D' r₀' hr₀') d ∧
      R_N' ∈ (innerDraw D' d' C).R ∧
      r₀' ⊆ R_N' ∧
      3 ≤ (perimDraw (innerDraw D' d' C) R_N').V.ncard ∧
      (innerDraw D' d' C).V = (innerDraw D d' C).V ∧
      (innerDraw D' d' C).E.ncard = (innerDraw D d' C).E.ncard + 1 := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  let N := innerDraw D d' C
  let B := perimDraw N R_N
  obtain ⟨hNs, hNV, hNE, _⟩ := innerDraw_spec D d' C
  obtain ⟨hBs, hBV, hBE, hBU, _⟩ := perimDraw_spec hS hRN
  have hBV_ne : B.V.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.mp h, ncard_empty] at hcard3
    omega
  obtain ⟨v₀, hv₀B⟩ := hBV_ne
  have hv₀N : v₀ ∈ N.V := (hBV ▸ hv₀B).1
  let N₁ := compSubdraw N v₀
  let N₂ := restSubdraw N v₀
  obtain ⟨hN₁s, hN₂s, hN₁V, hN₂V, hN₁E, hN₂E, hv₀_N₁, hNU_union, hNU_disj, hN₁_pre⟩ :=
    compSubdraw_spec N hv₀N
  have hBU_not_pre : ¬ IsPreconnected B.U := fun hPre =>
    hnot_conn ((isGraphConnected_iff_isPreconnected_U B).mpr ⟨⟨v₀, hv₀B⟩, hPre⟩)
  have hBU_N₁_ne : (B.U ∩ N₁.U).Nonempty :=
    ⟨v₀, B.V_subset_U hv₀B, N₁.V_subset_U hv₀_N₁⟩
  have hBU_N₂_ne : (B.U ∩ N₂.U).Nonempty := by
    by_contra hnot
    rw [not_nonempty_iff_eq_empty] at hnot
    have hBU_sub_N₁ : B.U ⊆ N₁.U := by
      intro z hzB
      rcases hNU_union ▸ hBs.U_subset hzB with hz₁ | hz₂
      · exact hz₁
      · exact (Set.eq_empty_iff_forall_notMem.mp hnot z ⟨hzB, hz₂⟩).elim
    have hRN_N₁ : R_N ∈ N₁.R := by
      obtain ⟨w, hw⟩ := GM11.region_nonempty hRN
      have hw_not_N₁ : w ∉ N₁.U := fun h => GM11.region_subset hRN hw (hN₁s.U_subset h)
      obtain ⟨R₁, hR₁, hwR₁⟩ := GM11.exists_region_of_notMem hw_not_N₁
      have hRN_R₁ : R_N ⊆ R₁ :=
        GM11.subset_region hR₁ (GM11.region_isPreconnected hRN)
          (Set.disjoint_left.mpr fun z hzRN hz₁ =>
            GM11.region_subset hRN hzRN (hN₁s.U_subset hz₁))
          hw hwR₁
      have hdisj_fr : Disjoint R₁ (frontier R_N) := by
        refine Set.disjoint_left.mpr fun z hzR₁ hzfr => ?_
        exact GM11.region_subset hR₁ hzR₁ (hBU_sub_N₁ (hBU.symm ▸ hzfr))
      have hR₁_cl : R₁ ⊆ closure R_N := by
        rcases GM11.subset_or_disjoint_of_frontier isClosed_closure
            (GM11.region_isPreconnected hR₁)
            (hdisj_fr.mono_right frontier_closure_subset) with hsub | hdisj
        · exact hsub
        · exact (Set.disjoint_left.mp hdisj hwR₁ (subset_closure hw)).elim
      have hR₁_RN : R₁ ⊆ R_N := by
        intro z hzR₁
        have hz_not_fr : z ∉ frontier R_N := Set.disjoint_left.mp hdisj_fr hzR₁
        have hz_int : z ∈ interior R_N := by
          by_contra hnot_int
          exact hz_not_fr ⟨hR₁_cl hzR₁, hnot_int⟩
        rwa [(GM11.region_isOpen hRN).interior_eq] at hz_int
      exact Subset.antisymm hR₁_RN hRN_R₁ ▸ hR₁
    have hPre_fr : IsPreconnected (frontier R_N) :=
      (isOpenDisc_and_isPreconnected_frontier_of_isPreconnected_U hS hSph
        ⟨v₀, N₁.V_subset_U hv₀_N₁⟩ hN₁_pre hRN_N₁).2
    exact hBU_not_pre (hBU ▸ hPre_fr)
  have h_exists_q : ∃ q ∈ D.R, q ⊆ R_N ∧
      (∀ hd' : 0 < d', q ⊆ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩)) ∧
      (closure q ∩ N₁.U).Nonempty ∧ (closure q ∩ N₂.U).Nonempty := by
    by_cases hd' : 0 < d'
    · let j_last : Fin d' := ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩
      let C_last := C j_last
      let Δ_last := Δ j_last
      have hNU_int : N.U ⊆ interior Δ_last := hShell.innerDraw_U_subset_interior hd'
      have hbd_eq : discBd Δ_last = C_last.U := hShell.discBd_eq j_last
      have hfr_Δ : frontier Δ_last = C_last.U :=
        (GM11.IsClosedDisc.frontier_eq_discBd hS (hShell.isClosedDisc j_last)).trans hbd_eq
      have hdisj_NC : Disjoint N.U C_last.U := by
        refine Set.disjoint_left.mpr fun z hzN hzC => ?_
        have hz_int := hNU_int hzN
        rw [← discInt_eq_interior_of_isClosedDisc hS (hShell.isClosedDisc j_last)] at hz_int
        exact hz_int.2 (hbd_eq.symm ▸ hzC)
      let N_plus := N.glue C_last
        (by rw [Set.disjoint_iff_inter_eq_empty.mp hdisj_NC]; exact empty_subset _)
      have hNp_U : N_plus.U = N.U ∪ C_last.U := rfl
      have hNp_V : N_plus.V = N.V ∪ C_last.V := rfl
      have hNp_E : N_plus.E = N.E ∪ C_last.E := by
        change (N.glue C_last _).E = N.E ∪ C_last.E
        rw [Drawing.glue_E]
      have hNp_sub : N_plus.IsSubdrawing D :=
        ⟨union_subset hNs.1 (hShell.isSubdrawing j_last).1,
         hNp_E ▸ union_subset hNs.2 (hShell.isSubdrawing j_last).2⟩
      let Ω : Set S := R_N ∩ interior Δ_last
      have hΩ_open : IsOpen Ω := (GM11.region_isOpen hRN).inter isOpen_interior
      obtain ⟨z₁, hz₁B, hz₁N₁⟩ := hBU_N₁_ne
      obtain ⟨z₂, hz₂B, hz₂N₂⟩ := hBU_N₂_ne
      have hz₁_cl_Ω : z₁ ∈ closure Ω := by
        rw [mem_closure_iff]
        intro O hO hz₁O
        have hz₁_int : z₁ ∈ interior Δ_last := hNU_int (hN₁s.U_subset hz₁N₁)
        obtain ⟨w, ⟨hwO, hw_int⟩, hwRN⟩ :=
          mem_closure_iff.mp (hBU ▸ hz₁B).1 (O ∩ interior Δ_last)
            (hO.inter isOpen_interior) ⟨hz₁O, hz₁_int⟩
        exact ⟨w, hwO, hwRN, hw_int⟩
      have hz₂_cl_Ω : z₂ ∈ closure Ω := by
        rw [mem_closure_iff]
        intro O hO hz₂O
        have hz₂_int : z₂ ∈ interior Δ_last := hNU_int (hN₂s.U_subset hz₂N₂)
        obtain ⟨w, ⟨hwO, hw_int⟩, hwRN⟩ :=
          mem_closure_iff.mp (hBU ▸ hz₂B).1 (O ∩ interior Δ_last)
            (hO.inter isOpen_interior) ⟨hz₂O, hz₂_int⟩
        exact ⟨w, hwO, hwRN, hw_int⟩
      obtain ⟨p₁, hp₁_univ, hp₁_Ω⟩ :=
        mem_closure_iff.mp hz₁_cl_Ω univ isOpen_univ (mem_univ z₁)
      have hp₁_not_Np : p₁ ∉ N_plus.U := by
        rintro (hpN | hpC)
        · exact GM11.region_subset hRN hp₁_Ω.1 hpN
        · have hp_int := hp₁_Ω.2
          rw [← discInt_eq_interior_of_isClosedDisc hS (hShell.isClosedDisc j_last)] at hp_int
          exact hp_int.2 (hbd_eq.symm ▸ hpC)
      obtain ⟨Ω', hΩ', hp₁_Ω'⟩ := GM11.exists_region_of_notMem hp₁_not_Np
      have hΩ'_sub_Ω : Ω' ⊆ Ω := by
        have hsub_RN : Ω' ⊆ R_N :=
          GM11.subset_region hRN (GM11.region_isPreconnected hΩ')
            (Set.disjoint_left.mpr fun z hzΩ' hzN =>
              GM11.region_subset hΩ' hzΩ' (Or.inl hzN))
            hp₁_Ω' hp₁_Ω.1
        have hdisj_C : Disjoint Ω' C_last.U :=
          Set.disjoint_left.mpr fun z hzΩ' hzC =>
            GM11.region_subset hΩ' hzΩ' (Or.inr hzC)
        have hsub_Δ : Ω' ⊆ Δ_last := by
          rcases GM11.subset_or_disjoint_of_frontier (hShell.isClosedDisc j_last).isClosed
              (GM11.region_isPreconnected hΩ') (hfr_Δ.symm ▸ hdisj_C) with hsub | hdisj
          · exact hsub
          · exact (Set.disjoint_left.mp hdisj hp₁_Ω' (interior_subset hp₁_Ω.2)).elim
        intro z hzΩ'
        refine ⟨hsub_RN hzΩ', ?_⟩
        rw [← discInt_eq_interior_of_isClosedDisc hS (hShell.isClosedDisc j_last)]
        exact ⟨hsub_Δ hzΩ', fun hz_bd =>
          Set.disjoint_left.mp hdisj_C hzΩ' (hbd_eq ▸ hz_bd)⟩
      have hΩ_sub_Ω' : Ω ⊆ Ω' := by
        intro y hyΩ
        let Q_out : Set S := Ωᶜ
        have hp₁_not_Q : p₁ ∉ Q_out := not_not.mpr hp₁_Ω
        have hy_not_Q : y ∉ Q_out := not_not.mpr hyΩ
        have hNp_Q : N_plus.U ⊆ Q_out := by
          rintro z (hzN | hzC) hzΩ
          · exact GM11.region_subset hRN hzΩ.1 hzN
          · have hz_int := hzΩ.2
            rw [← discInt_eq_interior_of_isClosedDisc hS (hShell.isClosedDisc j_last)] at hz_int
            exact hz_int.2 (hbd_eq.symm ▸ hzC)
        obtain ⟨r_same, hr_same, hp₁_same, hy_same⟩ :=
          GM11.same_region_of_discs hS hSph hp₁_not_Q hy_not_Q N_plus.E.ncard N_plus rfl hNp_Q
            (fun F hF hF_sub => by
              have hF_split : F ⊆ N.U ∪ C_last.U := hF_sub
              by_cases hFN : (F ∩ N.U).Nonempty
              · have hF_in_N : F ⊆ N.U := by
                  intro x hxF
                  by_contra hx_not_N
                  have hxC : x ∈ C_last.U := (hF_split hxF).resolve_left hx_not_N
                  obtain ⟨w, -, hwN, hwC⟩ :=
                    isPreconnected_closed_iff.mp hF.isPreconnected N.U C_last.U
                      N.isClosed_U C_last.isClosed_U hF_split hFN ⟨x, hxF, hxC⟩
                  exact Set.disjoint_left.mp hdisj_NC hwN hwC
                obtain ⟨Δ_F, hΔ_F, hbd_F, hdisj_F⟩ :=
                  GM11.exists_disc_missing hS hSph hF (GM11.region_isPreconnected hRN)
                    (Set.disjoint_left.mpr fun x hxRN hxF =>
                      GM11.region_subset hRN hxRN (hF_in_N hxF))
                exact ⟨Δ_F, hΔ_F, fun x hxΔ hxΩ =>
                  Set.disjoint_left.mp hdisj_F hxΔ hxΩ.1, hbd_F⟩
              · have hF_in_C : F ⊆ C_last.U := fun x hxF =>
                  (hF_split hxF).resolve_left fun hxN => hFN ⟨x, hxF, hxN⟩
                have hint_pre : IsPreconnected (interior Δ_last) := by
                  rw [← discInt_eq_interior_of_isClosedDisc hS (hShell.isClosedDisc j_last)]
                  exact (hShell.isClosedDisc j_last).isPreconnected_discInt
                obtain ⟨Δ_F, hΔ_F, hbd_F, hdisj_F⟩ :=
                  GM11.exists_disc_missing hS hSph hF hint_pre
                    (Set.disjoint_left.mpr fun x hx_int hxF => by
                      rw [← discInt_eq_interior_of_isClosedDisc hS
                        (hShell.isClosedDisc j_last)] at hx_int
                      exact hx_int.2 (hbd_eq.symm ▸ hF_in_C hxF))
                exact ⟨Δ_F, hΔ_F, fun x hxΔ hxΩ =>
                  Set.disjoint_left.mp hdisj_F hxΔ hxΩ.2, hbd_F⟩)
        rwa [← GM11.region_eq_of_mem hr_same hΩ' hp₁_same hp₁_Ω']
      have hΩ_mem : Ω ∈ N_plus.R := Subset.antisymm hΩ'_sub_Ω hΩ_sub_Ω' ▸ hΩ'
      have hcl_Ω_eq := closure_RN_eq_biUnion_closure_regions hS hNp_sub hΩ_mem
      have hz₁_un : z₁ ∈ ⋃ (q ∈ D.R) (_ : q ⊆ Ω), closure q := hcl_Ω_eq ▸ hz₁_cl_Ω
      simp only [mem_iUnion, exists_prop] at hz₁_un
      obtain ⟨r₁, hr₁, hr₁_Ω, hz₁_r₁⟩ := hz₁_un
      have hz₂_un : z₂ ∈ ⋃ (q ∈ D.R) (_ : q ⊆ Ω), closure q := hcl_Ω_eq ▸ hz₂_cl_Ω
      simp only [mem_iUnion, exists_prop] at hz₂_un
      obtain ⟨r₂, hr₂, hr₂_Ω, hz₂_r₂⟩ := hz₂_un
      let Z : Set (Set S) := {q ∈ D.R | q ⊆ Ω ∧ (closure q ∩ N₁.U).Nonempty}
      have hr₁_Z : r₁ ∈ Z := ⟨hr₁, hr₁_Ω, z₁, hz₁_r₁, hz₁N₁⟩
      by_cases hr₂_Z : r₂ ∈ Z
      · exact ⟨r₂, hr₂, hr₂_Ω.trans inter_subset_left,
          fun _ => hr₂_Ω.trans inter_subset_right, hr₂_Z.2.2, z₂, hz₂_r₂, hz₂N₂⟩
      · obtain ⟨e, heD, he_not_Np, a, b, haZ, hbZ, ha_Ω, hb_Ω, ⟨_, haR, pa, hpa_e, hpa_a⟩,
            ⟨_, hbR, pb, hpb_e, hpb_b⟩⟩ :=
          GM11.theorem_5_1_proof hS hNp_sub hΩ_mem hr₁ hr₁_Z hr₂ hr₂_Z hr₁_Ω hr₂_Ω
        have he_cl_a : closure e ⊆ closure a :=
          closure_minimal (GM11.edge_subset_closure_of_incident hS heD haR ⟨pa, hpa_e, hpa_a⟩)
            isClosed_closure
        have he_cl_b : closure e ⊆ closure b :=
          closure_minimal (GM11.edge_subset_closure_of_incident hS heD hbR ⟨pb, hpb_e, hpb_b⟩)
            isClosed_closure
        have ha_cl_Δ : closure a ⊆ Δ_last :=
          closure_minimal ((ha_Ω.trans inter_subset_right).trans interior_subset)
            (hShell.isClosedDisc j_last).isClosed
        have hV_in_CN : ∀ w ∈ closure e ∩ D.V, w ∈ C_last.V ∨ w ∈ N.V := by
          intro w ⟨hwe, hwV⟩
          have hw_Δ : w ∈ Δ_last := ha_cl_Δ (he_cl_a hwe)
          rcases hShell.vertex_in_or_inside hd' w hwV with ⟨i, hwi⟩ | hw_int
          · by_cases hij : i = j_last
            · subst hij
              exact Or.inl hwi
            · exfalso
              have hilt : i < j_last :=
                lt_of_le_of_ne (Fin.le_def.mpr (Nat.le_sub_one_of_lt i.2)) hij
              have hw_int_i : w ∈ interior (Δ i) := hShell.disc_subset_interior hilt hw_Δ
              rw [← discInt_eq_interior_of_isClosedDisc hS (hShell.isClosedDisc i)] at hw_int_i
              exact hw_int_i.2 ((hShell.discBd_eq i).symm ▸ (C i).V_subset_U hwi)
          · refine Or.inr (hNV.symm ▸ ⟨hwV, ?_⟩)
            intro h_un
            obtain ⟨i, hwi⟩ := mem_iUnion.mp h_un
            have hw_int_i : w ∈ interior (Δ i) := by
              by_cases hij : i = j_last
              · subst hij
                exact hw_int
              · have hilt : i < j_last :=
                  lt_of_le_of_ne (Fin.le_def.mpr (Nat.le_sub_one_of_lt i.2)) hij
                exact hShell.disc_subset_interior hilt (interior_subset hw_int)
            rw [← discInt_eq_interior_of_isClosedDisc hS (hShell.isClosedDisc i)] at hw_int_i
            exact hw_int_i.2 ((hShell.discBd_eq i).symm ▸ (C i).V_subset_U hwi)
        have h_has_NV : ∃ w ∈ closure e ∩ D.V, w ∈ N.V := by
          by_contra hno_NV
          push Not at hno_NV
          have hall_C : ∀ w ∈ closure e ∩ D.V, w ∈ C_last.V := fun w hw =>
            (hV_in_CN w hw).resolve_right (hno_NV w hw)
          rcases D.edge_cond e heD with ⟨u, v, -, hcap, -⟩ | ⟨u, hcap, -⟩
          · have hu : u ∈ closure e ∩ D.V := hcap ▸ mem_insert u {v}
            have hv : v ∈ closure e ∩ D.V := hcap ▸ mem_insert_of_mem u rfl
            have heC : e ∈ C_last.E :=
              hShell.edge_induced j_last ⟨heD, hu.2, hv.2, hcap⟩ (hall_C u hu) (hall_C v hv)
            exact he_not_Np (hNp_E ▸ Or.inr heC)
          · have hu : u ∈ closure e ∩ D.V := hcap ▸ mem_singleton u
            exact hSimple.not_isLoopAt e u ⟨heD, hu.2, hu.2, hcap.trans (pair_eq_singleton u).symm⟩
        obtain ⟨w, ⟨hwe, hwV⟩, hwNV⟩ := h_has_NV
        have hw_not_N₁ : w ∉ N₁.U := fun hw₁ =>
          hbZ ⟨hbR, hb_Ω, w, he_cl_b hwe, hw₁⟩
        have hw_N₂ : w ∈ N₂.U :=
          (hNU_union ▸ N.V_subset_U hwNV).resolve_left hw_not_N₁
        exact ⟨a, haR, ha_Ω.trans inter_subset_left,
          fun _ => ha_Ω.trans inter_subset_right, haZ.2.2, w, he_cl_a hwe, hw_N₂⟩
    · have hd'0 : d' = 0 := Nat.eq_zero_of_not_pos hd'
      subst hd'0
      have hN_eq : N = D := innerDraw_zero_eq D C
      have hRN_D : R_N ∈ D.R := hN_eq ▸ hRN
      obtain ⟨z₁, hz₁B, hz₁N₁⟩ := hBU_N₁_ne
      obtain ⟨z₂, hz₂B, hz₂N₂⟩ := hBU_N₂_ne
      exact ⟨R_N, hRN_D, Subset.rfl, fun h => (Nat.lt_irrefl 0 h).elim,
        ⟨z₁, (hBU ▸ hz₁B).1, hz₁N₁⟩, ⟨z₂, (hBU ▸ hz₂B).1, hz₂N₂⟩⟩
  obtain ⟨q, hq, hq_RN, hq_int, hq_N₁, hq_N₂⟩ := h_exists_q
  have h_vert_of_cl : ∀ (Γ₀ : Drawing S), Γ₀.IsSubdrawing N →
      (closure q ∩ Γ₀.U).Nonempty → ∃ v ∈ Γ₀.V, v ∈ closure q := by
    intro Γ₀ hΓ₀s ⟨z, hzq, hzΓ₀⟩
    by_cases hzV : z ∈ Γ₀.V
    · exact ⟨z, hzV, hzq⟩
    · obtain ⟨e, heΓ₀, hze⟩ := Γ₀.exists_edge_of_mem hzΓ₀ hzV
      have heD : e ∈ D.E := hNs.2 (hΓ₀s.2 heΓ₀)
      have he_cl : closure e ⊆ closure q :=
        closure_minimal (GM11.edge_subset_closure_of_incident hS heD hq ⟨z, hze, hzq⟩)
          isClosed_closure
      rcases Γ₀.edge_cond e heΓ₀ with ⟨u, v, -, hcap, -⟩ | ⟨u, hcap, -⟩
      · have hu : u ∈ closure e ∩ Γ₀.V := hcap ▸ mem_insert u {v}
        exact ⟨u, hu.2, he_cl hu.1⟩
      · have hu : u ∈ closure e ∩ Γ₀.V := hcap ▸ mem_singleton u
        exact ⟨u, hu.2, he_cl hu.1⟩
  obtain ⟨v₁, hv₁_N₁, hv₁_cl_q⟩ := h_vert_of_cl N₁ hN₁s hq_N₁
  obtain ⟨v₂, hv₂_N₂, hv₂_cl_q⟩ := h_vert_of_cl N₂ hN₂s hq_N₂
  have hv₁_NV : v₁ ∈ N.V := hN₁s.1 hv₁_N₁
  have hv₂_NV : v₂ ∈ N.V := hN₂s.1 hv₂_N₂
  have hv₁_D : v₁ ∈ D.V := hNs.1 hv₁_NV
  have hv₂_D : v₂ ∈ D.V := hNs.1 hv₂_NV
  have hv₁_BV : v₁ ∈ B.V := hBV.symm ▸ ⟨hv₁_NV, closure_mono hq_RN hv₁_cl_q⟩
  have hv₂_BV : v₂ ∈ B.V := hBV.symm ▸ ⟨hv₂_NV, closure_mono hq_RN hv₂_cl_q⟩
  have hv₁v₂ : v₁ ≠ v₂ := fun heq =>
    Set.disjoint_left.mp hNU_disj (N₁.V_subset_U hv₁_N₁) (heq ▸ N₂.V_subset_U hv₂_N₂)
  have hnotAdj : ¬ D.toGraph.Adj v₁ v₂ := by
    rintro ⟨e, heD, _, _, hcap⟩
    have heN : e ∈ N.E := by
      rw [hNE]
      refine ⟨heD, ?_⟩
      rw [hcap, ← hNV]
      rintro z (rfl | rfl)
      · exact hv₁_NV
      · exact hv₂_NV
    rcases edge_reach_or_rest N heN with h₁ | h₂
    · have hv₂_in : v₂ ∈ closure e ∩ N.V := by
        rw [hNs.closure_inter_V heN, hcap]; exact mem_insert_of_mem v₁ rfl
      exact (hN₂V ▸ hv₂_N₂).2 (h₁ hv₂_in)
    · have hv₁_in : v₁ ∈ closure e ∩ N.V := by
        rw [hNs.closure_inter_V heN, hcap]; exact mem_insert v₁ {v₂}
      exact (h₂ hv₁_in).2 (hN₁V ▸ hv₁_N₁)
  obtain ⟨g₁, hg₁, hg₁0, hg₁t⟩ := GM11.exists_path_into_region hS D hv₁_D hq hv₁_cl_q
  obtain ⟨g₂, hg₂, hg₂0, hg₂t⟩ := GM11.exists_path_into_region hS D hv₂_D hq hv₂_cl_q
  have hq_pc : IsPathConnected q :=
    GM11.isPathConnected_of_isOpen hS (GM11.region_isOpen hq)
      (GM11.region_isPreconnected hq) (GM11.region_nonempty hq)
  have hv₁_not_q : v₁ ∉ q := fun h => GM11.region_subset hq h (D.V_subset_U hv₁_D)
  obtain ⟨γ, hγ_cont, hγ_inj, hγ0, hγ1, hγ_in, -⟩ :=
    GM11.exists_chord hq_pc hv₁v₂ hv₁_not_q hg₁ hg₂ hg₁0 hg₂0 hg₁t hg₂t
  let K : Set S := range γ
  have hK : IsLineWithEnds K v₁ v₂ := hγ0 ▸ hγ1 ▸ GM11.isLine_range hγ_cont hγ_inj
  have hKq : K \ {v₁, v₂} ⊆ q := by
    rintro _ ⟨⟨t, rfl⟩, hnot⟩
    have ht0 : t ≠ 0 := fun h => hnot (Or.inl (h ▸ hγ0))
    have ht1 : t ≠ 1 := fun h => hnot (Or.inr (h ▸ hγ1))
    exact hγ_in t ht0 ht1
  let hmeet := lineDrawing_meet_of_subset_region hq hv₁_D hv₂_D hK hv₁v₂ hKq
  let D' := D.glue (GM11.lineDrawing hK hv₁v₂) hmeet
  let N' := innerDraw D' d' C
  let e_new : Set S := K \ {v₁, v₂}
  obtain ⟨hN's, hN'V, hN'E, _⟩ := innerDraw_spec D' d' C
  have hV_sub_L : (GM11.lineDrawing hK hv₁v₂).V ⊆ D.V := by
    rintro z (rfl | rfl)
    · exact hv₁_D
    · exact hv₂_D
  have hD'V : D'.V = D.V := union_eq_left.mpr hV_sub_L
  have hD'E : D'.E = insert e_new D.E := by
    change (D.glue (GM11.lineDrawing hK hv₁v₂) hmeet).E = insert e_new D.E
    rw [Drawing.glue_E, GM11.lineDrawing_E, union_singleton]
  have hcl_enew : closure e_new = K := GM11.closure_sdiff_pair hK
  have hcap_enew : closure e_new ∩ D'.V = {v₁, v₂} := by
    rw [hcl_enew, hD'V]
    refine Subset.antisymm (fun z ⟨hzK, hzV⟩ => ?_) ?_
    · by_contra hnot
      exact GM11.region_subset hq (hKq ⟨hzK, hnot⟩) (D.V_subset_U hzV)
    · rintro z (rfl | rfl)
      · exact ⟨(GM11.lineDrawing hK hv₁v₂).V_subset_U (Or.inl rfl), hv₁_D⟩
      · exact ⟨(GM11.lineDrawing hK hv₁v₂).V_subset_U (Or.inr rfl), hv₂_D⟩
  have hN'V_eq : N'.V = N.V := by rw [hN'V, hNV, hD'V]
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
        · exact hv₁_NV
        · exact hv₂_NV
      · exact ⟨Or.inr heD, hsub⟩
  have hN'U_eq : N'.U = N.U ∪ K := by
    rw [N'.U_eq, N.U_eq, hN'V_eq, hN'E_eq, biUnion_insert, hcl_enew]
    ext z; simp only [mem_union]; tauto
  have hN'U_e : N'.U = N.U ∪ e_new := by
    rw [hN'U_eq]
    refine Subset.antisymm (union_subset subset_union_left fun z hzK => ?_)
      (union_subset_union_right _ sdiff_subset)
    by_cases hz : z ∈ ({v₁, v₂} : Set S)
    · rcases hz with rfl | rfl
      · exact Or.inl (N.V_subset_U hv₁_NV)
      · exact Or.inl (N.V_subset_U hv₂_NV)
    · exact Or.inr ⟨hzK, hz⟩
  let R_N' : Set S := R_N \ e_new
  have hq_sdiff_ne : (q \ e_new).Nonempty := by
    obtain ⟨p₀, hp₀⟩ := GM11.region_nonempty hq
    have hK_closed : IsClosed K := hcl_enew ▸ isClosed_closure
    have hq_not_sub_K : ¬ q ⊆ K := by
      intro hsub
      obtain ⟨t₀, ht₀⟩ : ∃ t₀ : I, t₀ ≠ 0 ∧ t₀ ≠ 1 :=
        ⟨⟨1 / 2, by norm_num, by norm_num⟩,
         fun h => by have := congrArg Subtype.val h; norm_num at this,
         fun h => by have := congrArg Subtype.val h; norm_num at this⟩
      have hx₀_q : γ t₀ ∈ q := hγ_in t₀ ht₀.1 ht₀.2
      obtain ⟨D₀, D₀', hD₀, -, hx₀_int, hsub_D₀, hD₀_q, -⟩ :=
        GM11.exists_closedDisc_nbhd hS (GM11.region_isOpen hq) hx₀_q
      have hF₀ : IsOArc (discBd D₀) := IsClosedDisc.isOArc_discBd hD₀
      exact GM11.not_oArc_subset_arc hγ_cont hγ_inj hF₀
        ((GM11.discBd_subset D₀).trans (hD₀_q.trans hsub))
    obtain ⟨w, hwq, hwK⟩ := not_subset.mp hq_not_sub_K
    exact ⟨w, hwq, fun hwe => hwK hwe.1⟩
  obtain ⟨w₀, hw₀_q, hw₀_not_e⟩ := hq_sdiff_ne
  have hw₀_RN' : w₀ ∈ R_N' := ⟨hq_RN hw₀_q, hw₀_not_e⟩
  have hw₀_not_N'U : w₀ ∉ N'.U := by
    rw [hN'U_e]
    exact not_or.mpr ⟨GM11.region_subset hRN (hq_RN hw₀_q), hw₀_not_e⟩
  obtain ⟨R_N'', hRN'', hw₀_RN''⟩ := GM11.exists_region_of_notMem hw₀_not_N'U
  have hRN''_sub_RN' : R_N'' ⊆ R_N' := by
    have hsub_RN : R_N'' ⊆ R_N :=
      GM11.subset_region hRN (GM11.region_isPreconnected hRN'')
        (Set.disjoint_left.mpr fun z hz'' hzN =>
          GM11.region_subset hRN'' hz'' (hN'U_e ▸ Or.inl hzN))
        hw₀_RN'' hw₀_RN'.1
    exact fun z hz'' =>
      ⟨hsub_RN hz'', fun hze => GM11.region_subset hRN'' hz'' (hN'U_e ▸ Or.inr hze)⟩
  have hRN'_sub_RN'' : R_N' ⊆ R_N'' := by
    intro y hyRN'
    let Q_out : Set S := R_N'ᶜ
    have hw₀_not_Q : w₀ ∉ Q_out := not_not.mpr hw₀_RN'
    have hy_not_Q : y ∉ Q_out := not_not.mpr hyRN'
    have hN'_Q : N'.U ⊆ Q_out := by
      rw [hN'U_e]
      rintro z (hzN | hze) hzRN'
      · exact GM11.region_subset hRN hzRN'.1 hzN
      · exact hzRN'.2 hze
    obtain ⟨r_same, hr_same, hw₀_same, hy_same⟩ :=
      GM11.same_region_of_discs hS hSph hw₀_not_Q hy_not_Q N'.E.ncard N' rfl hN'_Q
        (fun F hF hF_sub => by
          have hF_in_N : F ⊆ N.U := by
            rw [hNU_union]
            refine GM11.oArc_subset_of_bridge N₁.isClosed_U N₂.isClosed_U hNU_disj
              hγ_cont hγ_inj
              (hγ0.symm ▸ N₁.V_subset_U hv₁_N₁)
              (hγ1.symm ▸ N₂.V_subset_U hv₂_N₂)
              (fun t ht0 ht1 hz => GM11.region_subset hRN (hq_RN (hγ_in t ht0 ht1))
                (hNU_union ▸ hz))
              hF ?_
            rwa [← hNU_union, ← hN'U_eq]
          obtain ⟨Δ_F, hΔ_F, hbd_F, hdisj_F⟩ :=
            GM11.exists_disc_missing hS hSph hF (GM11.region_isPreconnected hRN)
              (Set.disjoint_left.mpr fun x hxRN hxF =>
                GM11.region_subset hRN hxRN (hF_in_N hxF))
          exact ⟨Δ_F, hΔ_F, fun x hxΔ hxRN' =>
            Set.disjoint_left.mp hdisj_F hxΔ hxRN'.1, hbd_F⟩)
    rwa [← GM11.region_eq_of_mem hr_same hRN'' hw₀_same hw₀_RN'']
  have hRN' : R_N' ∈ N'.R := Subset.antisymm hRN''_sub_RN' hRN'_sub_RN'' ▸ hRN''
  have hRN_sdiff_sub : R_N \ q ⊆ R_N' :=
    fun z ⟨hzRN, hzq⟩ => ⟨hzRN, fun hze => hzq (hKq hze)⟩
  have hcl_RN' : closure R_N' = closure R_N := by
    refine Subset.antisymm (closure_mono sdiff_subset) (closure_minimal ?_ isClosed_closure)
    intro z hzRN
    by_cases hze : z ∈ e_new
    · have hw₀_not_D'U : w₀ ∉ D'.U := by
        intro hwU
        rcases (show D'.U = D.U ∪ e_new by
          refine Subset.antisymm (union_subset subset_union_left fun x hxK => ?_)
            (union_subset_union_right _ sdiff_subset)
          by_cases hx : x ∈ ({v₁, v₂} : Set S)
          · exact Or.inl (D.V_subset_U (hV_sub_L hx))
          · exact Or.inr ⟨hxK, hx⟩) ▸ hwU with hwDU | hwe
        · exact GM11.region_subset hq hw₀_q hwDU
        · exact hw₀_not_e hwe
      obtain ⟨r_w, hr_w, hw₀_rw⟩ := GM11.exists_region_of_notMem hw₀_not_D'U
      have hrw_sub_q : r_w ⊆ q :=
        GM11.subset_region hq (GM11.region_isPreconnected hr_w)
          (Set.disjoint_left.mpr fun x hxr hxDU =>
            GM11.region_subset hr_w hxr (Or.inl hxDU))
          hw₀_rw hw₀_q
      have hrw_sub_RN' : r_w ⊆ R_N' := fun x hxr =>
        ⟨hq_RN (hrw_sub_q hxr), fun hxe =>
          GM11.region_subset hr_w hxr (Or.inr hxe.1)⟩
      have he_cl_rw : e_new ⊆ closure r_w := by
        have hmeet_rw : (e_new ∩ closure r_w).Nonempty := by
          by_contra hnot_meet
          rw [not_nonempty_iff_eq_empty] at hnot_meet
          have hq_cov : q ⊆ r_w ∪ (closure r_w)ᶜ := by
            intro x hxq
            by_cases hxcl : x ∈ closure r_w
            · refine Or.inl ?_
              have hx_not_DU : x ∉ D.U := GM11.region_subset hq hxq
              have hx_not_enew : x ∉ e_new := fun hxe => by
                have : x ∈ (∅ : Set S) := hnot_meet ▸ ⟨hxe, hxcl⟩
                exact this
              have hx_not_D'U : x ∉ D'.U := by
                rintro (hxDU | hxK)
                · exact hx_not_DU hxDU
                · by_cases hxp : x ∈ ({v₁, v₂} : Set S)
                  · exact hx_not_DU (D.V_subset_U (hV_sub_L hxp))
                  · exact hx_not_enew ⟨hxK, hxp⟩
              obtain ⟨r'', hr'', hxr''⟩ := GM11.exists_region_of_notMem hx_not_D'U
              obtain ⟨w, hwr'', hwr'⟩ :=
                mem_closure_iff.mp hxcl r'' (GM11.region_isOpen hr'') hxr''
              rwa [GM11.region_eq_of_mem hr'' hr_w hwr'' hwr'] at hxr''
            · exact Or.inr hxcl
          have hdisj_open : Disjoint r_w (closure r_w)ᶜ :=
            Set.disjoint_left.mpr fun x hxr hnot => hnot (subset_closure hxr)
          rcases (GM11.region_isPreconnected hq).subset_or_subset
              (GM11.region_isOpen hr_w) isClosed_closure.isOpen_compl hdisj_open hq_cov with h₁ | h₂
          · obtain ⟨w, hw⟩ := (GM11.isPathConnected_sdiff_pair hK).nonempty
            exact GM11.region_subset hr_w (h₁ (hKq hw)) (Or.inr hw.1)
          · exact h₂ hw₀_q (subset_closure hw₀_rw)
        exact GM11.edge_subset_closure_of_incident hS
          (hD'E ▸ mem_insert e_new D.E) hr_w hmeet_rw
      exact closure_mono hrw_sub_RN' (he_cl_rw hze)
    · exact subset_closure ⟨hzRN, hze⟩
  obtain ⟨_, hB'V, _, _, _⟩ := perimDraw_spec hS hRN'
  have hPV_sub : B.V ⊆ (perimDraw N' R_N').V := by
    rw [hBV, hB'V, hN'V_eq, hcl_RN']
  obtain ⟨r₀', hr₀', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    addChordInRegion_spec hS hSph hd'd hShell hOuter hSimple hrad hRN hr₀_sub hcard3
      hq hq_RN hq_int hv₁_BV hv₂_BV hv₁v₂ hnotAdj hK hKq hv₁_D hv₂_D
      hRN' sdiff_subset hRN_sdiff_sub hPV_sub
  exact ⟨D', r₀', R_N', hr₀', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end Claim1

end GraphMinor.GM03
