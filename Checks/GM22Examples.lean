module

import GraphMinor.GM22.Defs

/-!
# Sanity checks and small examples for Graph Minors XXII definitions

This file verifies on small concrete graphs that the definitions in `GraphMinor/GM22/Defs.lean`
are non-trivial and behave as intended:
* `effectOn` distinguishes non-empty components from the empty subgraph (`effectOn_oneVert_eq`,
  `effectOn_bot_eq_empty`, `not_hasSameEffectOn_oneVert_bot`).
* `IsVitalFor` holds for the edgeless spanning subgraph on a single vertex (`isVitalFor_oneVert`),
  fails for the empty subgraph (`not_isVitalFor_bot`), and fails for a subgraph with a redundant
  loop edge (`not_isVitalFor_loopGraph`).
* `IsVitalLinkage` and `IsVitalPLinkage` hold for the 1-vertex path linkage (`isVitalPLinkage_oneVert`)
  and fail for the empty subgraph (`not_isVitalLinkage_bot`).
-/

namespace GraphMinor.GM22Examples

open Set Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM22

/-- The single-vertex edgeless graph on `Unit` with edge type `Empty`. -/
def oneVert : Graph Unit Empty :=
  Graph.noEdge ({()} : Set Unit) Empty

/-- A graph on `Unit` with a single loop edge `() : Unit`. -/
def loopGraph : Graph Unit Unit where
  vertexSet := {()}
  edgeSet := {()}
  IsLink _ x y := x = () ∧ y = ()
  isLink_symm _ _ := ⟨fun _ _ ⟨hx, hy⟩ => ⟨hy, hx⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h₁ h₂ := Or.inl (h₁.1.trans h₂.1.symm)
  edge_mem_iff_exists_isLink _ := ⟨fun _ => ⟨(), (), rfl, rfl⟩, fun _ => mem_singleton_iff.mpr rfl⟩
  left_mem_of_isLink _ _ _ h := mem_singleton_iff.mpr h.1

/-- `oneVert` is a connected graph. -/
theorem isGraphConnected_oneVert : IsGraphConnected oneVert := by
  refine ⟨⟨(), mem_singleton ()⟩, ?_⟩
  intro x _ y _
  cases x; cases y
  exact ⟨GraphWalk.nil (mem_singleton ())⟩

/-- Any subgraph of `oneVert` with a nonempty vertex set is equal to `oneVert`. -/
theorem eq_oneVert_of_le_of_nonempty {H : Graph Unit Empty} (hH : H ≤ oneVert)
    (hne : V(H).Nonempty) : H = oneVert := by
  refine Graph.ext ?_ fun e _ _ => ?_
  · apply Subset.antisymm hH.vertexSet_mono
    rintro ⟨⟩ _
    rcases hne with ⟨⟨⟩, h⟩
    exact h
  · exact Empty.elim e

/-- `oneVert` is its own unique component. -/
theorem isGraphComponent_oneVert : IsGraphComponent oneVert oneVert := by
  refine ⟨le_rfl, isGraphConnected_oneVert, ?_⟩
  intro C' _ hle hconn
  exact eq_oneVert_of_le_of_nonempty hle hconn.1

theorem graphComponents_oneVert : graphComponents oneVert = {oneVert} := by
  ext C
  simp only [graphComponents, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · intro hC
    exact eq_oneVert_of_le_of_nonempty hC.1 hC.2.1.1
  · rintro rfl
    exact isGraphComponent_oneVert

/-- The effect of `oneVert` on `{()}` is `{{()}}`. -/
theorem effectOn_oneVert_eq : effectOn oneVert ({()} : Set Unit) = {{()}} := by
  ext B
  simp only [effectOn, graphComponents_oneVert, mem_ofPred_eq, mem_singleton_iff, exists_eq_left]
  change (B.Nonempty ∧ B = {()} ∩ {()}) ↔ B = {()}
  rw [inter_self]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ singleton_nonempty (), h⟩⟩

/-- The effect of the empty subgraph `⊥` on any set `Z` is empty. -/
theorem effectOn_bot_eq_empty (Z : Set Unit) :
    effectOn (⊥ : Graph Unit Empty) Z = ∅ := by
  ext B
  simp only [effectOn, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_exists]
  intro _ C hC
  exact absurd (hC.1.vertexSet_mono hC.2.1.1.some_mem) (by simp)

/-- `oneVert` and `⊥` do not have the same effect on `{()}`. -/
theorem not_hasSameEffectOn_oneVert_bot :
    ¬ HasSameEffectOn oneVert (⊥ : Graph Unit Empty) ({()} : Set Unit) := by
  rw [HasSameEffectOn, effectOn_oneVert_eq, effectOn_bot_eq_empty]
  exact singleton_ne_empty {()}

/-- `oneVert` is vital for `{()}` in `oneVert`. -/
theorem isVitalFor_oneVert : IsVitalFor oneVert oneVert ({()} : Set Unit) := by
  refine ⟨le_rfl, Subset.rfl, ?_⟩
  intro L' hL' heff
  have hmem : ({()} : Set Unit) ∈ effectOn L' ({()} : Set Unit) := by
    rw [heff, effectOn_oneVert_eq]
    exact mem_singleton _
  rcases hmem with ⟨_, C, hC, _⟩
  have hne : V(L').Nonempty := hC.2.1.1.mono hC.1.vertexSet_mono
  exact eq_oneVert_of_le_of_nonempty hL' hne

/-- The empty subgraph `⊥` is not vital for `{()}` in `oneVert`. -/
theorem not_isVitalFor_bot : ¬ IsVitalFor oneVert (⊥ : Graph Unit Empty) ({()} : Set Unit) := by
  intro h
  have := h.2.1 (mem_singleton ())
  simp at this

/-- The edgeless spanning subgraph of `loopGraph` has the same effect on `{()}` as `loopGraph`,
so `loopGraph` is not vital for `{()}` in `loopGraph`. -/
theorem not_isVitalFor_loopGraph : ¬ IsVitalFor loopGraph loopGraph ({()} : Set Unit) := by
  intro h
  let L₀ : Graph Unit Unit := Graph.noEdge ({()} : Set Unit) Unit
  have hle : L₀ ≤ loopGraph := by
    refine ⟨Subset.rfl, ?_⟩
    intro e x y hlink
    simp [L₀] at hlink
  have hconn_loop : IsGraphConnected loopGraph := by
    refine ⟨⟨(), mem_singleton ()⟩, fun x _ y _ => ?_⟩
    cases x; cases y
    exact ⟨GraphWalk.nil (mem_singleton ())⟩
  have hcomp_loop : IsGraphComponent loopGraph loopGraph :=
    ⟨le_rfl, hconn_loop, fun C' hle₁ hle₂ _ => le_antisymm hle₂ hle₁⟩
  have hconn_L₀ : IsGraphConnected L₀ := by
    refine ⟨⟨(), mem_singleton ()⟩, fun x _ y _ => ?_⟩
    cases x; cases y
    exact ⟨GraphWalk.nil (mem_singleton ())⟩
  have hcomp_L₀ : IsGraphComponent L₀ L₀ :=
    ⟨le_rfl, hconn_L₀, fun C' hle₁ hle₂ _ => le_antisymm hle₂ hle₁⟩
  have heff : effectOn L₀ ({()} : Set Unit) = effectOn loopGraph ({()} : Set Unit) := by
    ext B
    simp only [effectOn, mem_ofPred_eq]
    constructor
    · rintro ⟨hne, C, hC, rfl⟩
      refine ⟨hne, loopGraph, hcomp_loop, ?_⟩
      ext x
      cases x
      simp only [mem_inter_iff, mem_singleton_iff, and_true]
      rcases hC.2.1.1 with ⟨⟨⟩, hx⟩
      exact ⟨fun _ => mem_singleton (), fun _ => hx⟩
    · rintro ⟨hne, C, hC, rfl⟩
      refine ⟨hne, L₀, hcomp_L₀, ?_⟩
      ext x
      cases x
      simp only [mem_inter_iff, mem_singleton_iff, and_true]
      rcases hC.2.1.1 with ⟨⟨⟩, hx⟩
      exact ⟨fun _ => mem_singleton (), fun _ => hx⟩
  have heq := h.2.2 L₀ hle heff
  have hedge : () ∈ E(L₀) := by
    rw [heq]
    exact mem_singleton ()
  simp [L₀] at hedge

/-- `oneVert` is a graph path with ends `()` and `()`. -/
theorem isGraphPath_oneVert : IsGraphPath oneVert oneVert := by
  refine ⟨(), (), le_rfl, ⟨GraphWalk.nil (mem_singleton ()), ?_, ?_, ?_⟩⟩
  · simp [GraphWalk.IsSimple, GraphWalk.support]
  · ext x
    cases x
    simp [oneVert, GraphWalk.support]
  · ext e
    exact Empty.elim e

/-- `oneVert` is a linkage in `oneVert`. -/
theorem isLinkage_oneVert : IsLinkage oneVert oneVert := by
  refine ⟨le_rfl, ?_⟩
  intro P hP
  rw [graphComponents_oneVert, mem_singleton_iff] at hP
  subst hP
  exact isGraphPath_oneVert

/-- `()` is the unique terminal of `oneVert`. -/
theorem terminals_oneVert : terminals oneVert = {()} := by
  ext x
  cases x
  simp only [terminals, mem_ofPred_eq, mem_singleton_iff, iff_true]
  refine ⟨mem_singleton (), ?_⟩
  have hval : vertexValency oneVert () = 0 := by
    unfold vertexValency
    have h₁ : {e ∈ E(oneVert) | ∃ w ≠ (), oneVert.IsLink e () w} = ∅ := by
      ext e; exact Empty.elim e
    have h₂ : {e ∈ E(oneVert) | oneVert.IsLink e () ()} = ∅ := by
      ext e; exact Empty.elim e
    rw [h₁, h₂, ncard_empty]
  rw [hval]
  decide

/-- `oneVert` is a vital 1-linkage in `oneVert`. -/
theorem isVitalPLinkage_oneVert : IsVitalPLinkage oneVert oneVert 1 := by
  refine ⟨⟨isLinkage_oneVert, ?_⟩, isLinkage_oneVert, rfl, ?_⟩
  · rw [terminals_oneVert, ncard_singleton]
  · intro L' hL' hpat
    have hmem : ({()} : Set Unit) ∈ linkagePattern L' := by
      rw [hpat]
      refine ⟨singleton_nonempty (), oneVert, ?_, ?_⟩
      · rw [graphComponents_oneVert]
        exact mem_singleton _
      · rw [terminals_oneVert]
        exact (inter_self _).symm
    rcases hmem with ⟨_, P, hP, _⟩
    have hne : V(L').Nonempty := hP.2.1.1.mono hP.1.vertexSet_mono
    exact eq_oneVert_of_le_of_nonempty hL'.1 hne

/-- The empty subgraph `⊥` is not a vital linkage in `oneVert`. -/
theorem not_isVitalLinkage_bot : ¬ IsVitalLinkage oneVert (⊥ : Graph Unit Empty) := by
  intro h
  have : () ∈ V((⊥ : Graph Unit Empty)) := by
    rw [h.2.1]
    exact mem_singleton ()
  simp at this

/-! ## Section 7 definitions: `IsAdequateFor`, `IsSufficientFor`, `IsGoodMember`, `IsBadMember`, `ConditionJ7` -/

/-- The single-vertex edgeless graph on `Unit` with edge type `Set Unit`. -/
def oneVertSet : Graph Unit (Set Unit) :=
  Graph.noEdge ({()} : Set Unit) (Set Unit)

/-- The 1-vertex, 0-edge, 0-root rooted digraph on `Unit` with edge type `Empty`. -/
def oneVertRootedDigraph : RootedDigraph Unit Empty 0 where
  G := {
    toGraph := oneVert
    head := Empty.elim
    tail := Empty.elim
    isLink_of_mem := fun e => Empty.elim e
  }
  roots := Fin.elim0
  roots_mem := fun i => Fin.elim0 i

/-- The discrete topology on `Unit`. -/
instance : TopologicalSpace Unit := ⊥

/-- The empty drawing on `Unit`. -/
def emptyDrawingUnit : Drawing Unit where
  U := ∅
  V := ∅
  isClosed_U := isClosed_empty
  V_subset_U := empty_subset _
  finite_V := finite_empty
  finite_edges := Set.toFinite _
  edge_cond := fun _ ⟨⟨_, hx⟩, hsub, _⟩ => False.elim (hsub hx).1

/-- A 1-vertex, 0-edge drawing on `Unit`. -/
def oneVertDrawingUnit : Drawing Unit where
  U := {()}
  V := {()}
  isClosed_U := isClosed_discrete _
  V_subset_U := Subset.rfl
  finite_V := finite_singleton ()
  finite_edges := Set.toFinite _
  edge_cond := fun _ ⟨⟨_, hx⟩, hsub, _⟩ => False.elim ((hsub hx).2 (hsub hx).1)

/-- `{oneVertSet}` is sufficient for the identity model of `oneVertRootedDigraph` when `K = ⊥`. -/
theorem isSufficientFor_singleton_oneVert :
    IsSufficientFor (∅ : Set Unit) {oneVertSet} {oneVertSet} (⊥ : Graph Unit (Set Unit))
      oneVertRootedDigraph (fun _ => oneVertSet) Empty.elim where
  subset := Subset.rfl
  mem_of_edge_inc_W _ _ _ hA _ := hA
  φV_meets _ _ := ⟨(), mem_singleton (), Or.inr (mem_iUnion₂.mpr ⟨oneVertSet, mem_singleton _, mem_singleton ()⟩)⟩
  φE_mem e := Empty.elim e
  mem_of_inter_K_ne_NW _ hA _ := hA

/-- `∅` is not sufficient for the identity model of `oneVertRootedDigraph` when `K = ⊥`. -/
theorem not_isSufficientFor_empty :
    ¬ IsSufficientFor (∅ : Set Unit) {oneVertSet} ∅ (⊥ : Graph Unit (Set Unit))
      oneVertRootedDigraph (fun _ => oneVertSet) Empty.elim := by
  intro h
  obtain ⟨x, _, hx⟩ := h.φV_meets () (mem_singleton ())
  simp at hx

/-- `{oneVertSet}` is adequate for the identity model of `oneVertRootedDigraph` when `K = ⊥`. -/
theorem isAdequateFor_singleton_oneVert :
    IsAdequateFor (Function.Embedding.refl Unit) (Function.Embedding.refl (Set Unit))
      (∅ : Set Unit) {oneVertSet} {oneVertSet} emptyDrawingUnit (⊥ : Graph Unit (Set Unit))
      oneVertRootedDigraph (fun _ => oneVertSet) Empty.elim where
  subset := Subset.rfl
  mem_of_not_le_Γ_union_NW _ _ _ hA _ := hA
  φV_meets _ _ := ⟨(), mem_singleton (), Or.inr (mem_iUnion₂.mpr ⟨oneVertSet, mem_singleton _, mem_singleton ()⟩)⟩
  φE_mem e := Empty.elim e
  mem_of_inter_K_ne_NW _ hA _ := hA

/-- `oneVertSet` is a good member with respect to `oneVertDrawingUnit` and `πLen = 1`. -/
theorem isGoodMember_oneVert :
    IsGoodMember (Function.Embedding.refl Unit) (Function.Embedding.refl (Set Unit))
      oneVertDrawingUnit (fun _ => 1) (fun _ _ => ()) oneVertSet := by
  refine ⟨fun x _ => mem_singleton (), fun u _ v _ => ?_⟩
  cases u; cases v
  have hGA_eq : (oneVertDrawingUnit.toEmbeddedGraph (Function.Embedding.refl Unit)
      (Function.Embedding.refl (Set Unit))) ⊓ oneVertSet = oneVertSet := by
    refine Graph.ext ?_ fun e x y => ?_
    · ext ⟨⟩
      simp [oneVertDrawingUnit, Drawing.toEmbeddedGraph, oneVertSet]
    · simp [oneVertSet]
  have hP : IsGraphPathWithEnds ((oneVertDrawingUnit.toEmbeddedGraph (Function.Embedding.refl Unit)
      (Function.Embedding.refl (Set Unit))) ⊓ oneVertSet) oneVertSet () () := by
    rw [hGA_eq]
    refine ⟨le_rfl, ⟨GraphWalk.nil (mem_singleton ()), ?_, ?_, ?_⟩⟩
    · simp [GraphWalk.IsSimple, GraphWalk.support]
    · ext ⟨⟩; simp [oneVertSet, GraphWalk.support]
    · ext e; simp [oneVertSet, GraphWalk.edges]
  refine ⟨oneVertSet, hP, ?_⟩
  rw [Set.disjoint_left]
  intro ⟨⟩ hx
  exact False.elim (hx.2 ⟨(), hP⟩)

/-- `oneVertSet` is a bad member with respect to `emptyDrawingUnit` and `πLen = 1`. -/
theorem isBadMember_oneVert_emptyDrawing :
    IsBadMember (Function.Embedding.refl Unit) (Function.Embedding.refl (Set Unit))
      emptyDrawingUnit (fun _ => 1) (fun _ _ => ()) oneVertSet := by
  intro h
  have : () ∈ emptyDrawingUnit.V := h.1 ⟨0, rfl⟩
  exact this

/-- `ConditionJ7` holds vacuously for the empty family `𝒜 = ∅`. -/
theorem conditionJ7_empty :
    ConditionJ7 (Function.Embedding.refl Unit) (Function.Embedding.refl (Set Unit))
      oneVertSet ∅ ∅ (fun _ => 1) (fun _ _ => ()) emptyDrawingUnit ∅ where
  path_in_A _ hA := False.elim hA
  no_small_sep _ hA := False.elim hA
  structure_Γ_inter_A _ hA := False.elim hA

/-! ## Section 8 definitions: `divisionIncidenceGraph` -/

/-- In `divisionIncidenceGraph {()} {oneVert}`, `((), oneVert)` links `Sum.inl ()` and
`Sum.inr oneVert`. -/
theorem divisionIncidenceGraph_oneVert_isLink :
    (divisionIncidenceGraph ({()} : Set Unit) {oneVert}).IsLink
      ((), oneVert) (Sum.inl ()) (Sum.inr oneVert) :=
  ⟨mem_singleton (), mem_singleton _, mem_singleton (), Or.inl ⟨rfl, rfl⟩⟩

/-- In `divisionIncidenceGraph {()} {⊥}`, `((), ⊥)` is not an edge because `() ∉ V(⊥)`. -/
theorem not_divisionIncidenceGraph_bot_edge :
    ((), (⊥ : Graph Unit Empty)) ∉
      E(divisionIncidenceGraph ({()} : Set Unit) {(⊥ : Graph Unit Empty)}) := by
  intro h
  exact h.2.2

end GraphMinor.GM22Examples
