module

public import GraphMinor.GM08.Section11Xi
import GraphMinor.GM16.DrawingGraphPaths

/-!
# The part of a branch set outside the image rings

In the proof of Graph Minors VIII, (11.2), a node `s` of the first portrait is sent to a tree
`σ(s)` of the forest `Ξ`, whose vertices are nodes of `Γ_2` (`partA`). An edge of `Ξ` lies in a
cell of the second portrait. In a cell `D(e')` it is replaced by `e'`. In the disc `Σ_j` of a ring
that is not the image of a ring of `Γ_1`, the edges of `Ξ` are replaced by the forest `Ξ'_j` of
`Γ_2` from (8.4). So the branch set of `s` also contains the vertices of `Ξ'_j` joined in `Ξ'_j`
to a vertex of `σ(s)` (`partB`).

* Vertices of `partB s` that are nodes lie in `partA s` (`partA_of_partB`).
* `partA s ∪ partB s` for distinct `s` are disjoint (`eq_of_partAB`).
* The vertices of `partB s` that are not nodes are inside a ring not hit (`inside_of_partB`).
* `partA s ∪ partB s` is joined by links of `Γ_2` that avoid a given set of edges, if each edge of
  `σ(s)` is replaced as above (`reflTransGen_partAB`).
-/

public section

namespace GraphMinor
namespace GM08

open Set Topology Surface Graph

universe u

variable {S : Type u} [TopologicalSpace S] [T1Space S]

/-- The vertices of the tree `σ(s)`, for a node `s`. -/
@[expose] def partA (σv : S → Graph S (Set S)) (N₁ : Set S) (s : S) : Set S :=
  {z | s ∈ N₁ ∧ z ∈ V(σv s)}

/-- The vertices joined in some `Ξ'_j` (`j ∈ J`) to a vertex of `σ(s)` on `F_j`. -/
@[expose] def partB (σv : S → Graph S (Set S)) (N₁ : Set S) {t : ℕ} (F : Fin t → Set S)
    (Ξ' : Fin t → Drawing S) (J : Set (Fin t)) (s : S) : Set S :=
  {z | ∃ j ∈ J, ∃ u ∈ partA σv N₁ s, u ∈ F j ∧ z ∈ (Ξ' j).V ∧
    Nonempty (GraphWalk (Ξ' j).toGraph u z)}

/-- The hypotheses on the forest `Ξ` and the trees `σ(s)`. -/
structure XiSetting (Ξ : Drawing S) (σv : S → Graph S (Set S)) (N₁ : Set S) (Γ : Drawing S)
    {t : ℕ} (F : Fin t → Set S) (Ξ' : Fin t → Drawing S) (J : Set (Fin t)) : Prop where
  hS : IsClosedDisc (univ : Set S)
  foundation : IsFoundation Γ univ F
  ΞV : Ξ.V = ringNodes Γ F
  comp : ∀ s ∈ N₁, GM06.IsGraphComponent (σv s) Ξ.toGraph
  inj : ∀ s₁ ∈ N₁, ∀ s₂ ∈ N₁, s₁ ≠ s₂ → σv s₁ ≠ σv s₂
  sub : ∀ j ∈ J, (Ξ' j).IsSubdrawing Γ
  U_sub : ∀ j ∈ J, (Ξ' j).U ⊆ F j ∪ insideSet (F j)
  iff : ∀ j ∈ J, ∀ u ∈ Γ.V ∩ F j, ∀ v ∈ Γ.V ∩ F j,
    (u ∈ (xiPart Ξ ((F j ∪ insideSet (F j)) \ ringNodes Γ F)).V ∧
      v ∈ (xiPart Ξ ((F j ∪ insideSet (F j)) \ ringNodes Γ F)).V ∧
      Nonempty (GraphWalk (xiPart Ξ ((F j ∪ insideSet (F j)) \ ringNodes Γ F)).toGraph u v)) ↔
    (u ∈ (Ξ' j).V ∧ v ∈ (Ξ' j).V ∧ Nonempty (GraphWalk (Ξ' j).toGraph u v))

variable {Ξ : Drawing S} {σv : S → Graph S (Set S)} {N₁ : Set S} {Γ : Drawing S} {t : ℕ}
  {F : Fin t → Set S} {Ξ' : Fin t → Drawing S} {J : Set (Fin t)}

theorem partA_subset (h : XiSetting Ξ σv N₁ Γ F Ξ' J) (s : S) :
    partA σv N₁ s ⊆ ringNodes Γ F := fun z hz => by
  rw [← h.ΞV]
  exact (h.comp s hz.1).1.vertexSet_mono hz.2

/-- A walk of `Ξ` from a vertex of `σ(s)` stays in `σ(s)`. -/
theorem partA_of_walk (h : XiSetting Ξ σv N₁ Γ F Ξ' J) {s x y : S} (hx : x ∈ partA σv N₁ s)
    (W : GraphWalk Ξ.toGraph x y) : y ∈ partA σv N₁ s := by
  have hC := h.comp s hx.1
  have hxR := GM09.self_mem_reachableComponent (hC.1.vertexSet_mono hx.2)
  have key := GM09.walk_support_subset_reachableComponent hxR W y W.end_mem_support
  rw [← GM09.isGraphComponent_eq_reachableComponent hC hx.2] at key
  exact ⟨hx.1, key⟩

/-- Trees of distinct nodes are disjoint. -/
theorem eq_of_partA (h : XiSetting Ξ σv N₁ Γ F Ξ' J) {s s' z : S} (hz : z ∈ partA σv N₁ s)
    (hz' : z ∈ partA σv N₁ s') : s = s' := by
  by_contra hne
  have hC := h.comp s hz.1
  have hC' := h.comp s' hz'.1
  exact h.inj s hz.1 s' hz'.1 hne (hC.eq_of_mem_mem hC' hz.2 hz'.2)

/-- A vertex of `Ξ'_j` that is a node of `Γ` lies on `F_j`. -/
theorem mem_ring_of_mem_Ξ' (h : XiSetting Ξ σv N₁ Γ F Ξ' J) {j : Fin t} (hj : j ∈ J) {z : S}
    (hz : z ∈ (Ξ' j).V) (hzN : z ∈ ringNodes Γ F) : z ∈ Γ.V ∩ F j := by
  refine ⟨(h.sub j hj).1 hz, ?_⟩
  rcases h.U_sub j hj ((Ξ' j).V_subset_U hz) with h' | h'
  · exact h'
  · exact absurd h' (hzN.2 j)

/-- A walk of `Ξ'_j` between vertices of `σ(s)` and `σ(s')` on `F_j` forces `s = s'`; more
precisely, the end of such a walk on `F_j` is in `σ(s)`. -/
theorem partA_of_walk_Ξ' (h : XiSetting Ξ σv N₁ Γ F Ξ' J) {j : Fin t} (hj : j ∈ J) {s u z : S}
    (hu : u ∈ partA σv N₁ s) (huF : u ∈ F j) (hz : z ∈ Γ.V ∩ F j)
    (W : GraphWalk (Ξ' j).toGraph u z) : z ∈ partA σv N₁ s := by
  have huV : u ∈ Γ.V ∩ F j := ⟨(partA_subset h s hu).1, huF⟩
  have huΞ : u ∈ (Ξ' j).V := W.start_mem_support |> GraphWalk.mem_vertexSet_of_mem_support W
  have hzΞ : z ∈ (Ξ' j).V := W.end_mem_support |> GraphWalk.mem_vertexSet_of_mem_support W
  obtain ⟨-, -, ⟨W'⟩⟩ := (h.iff j hj u huV z hz).mpr ⟨huΞ, hzΞ, ⟨W⟩⟩
  exact partA_of_walk h hu (W'.mono (GM16.toGraph_le_of_isSubdrawing (xiPart_isSubdrawing _ _)))

/-- Vertices of `partB s` that are nodes lie in `partA s`. -/
theorem partA_of_partB (h : XiSetting Ξ σv N₁ Γ F Ξ' J) {s z : S}
    (hz : z ∈ partB σv N₁ F Ξ' J s) (hzN : z ∈ ringNodes Γ F) : z ∈ partA σv N₁ s := by
  obtain ⟨j, hj, u, hu, huF, hzΞ, ⟨W⟩⟩ := hz
  exact partA_of_walk_Ξ' h hj hu huF (mem_ring_of_mem_Ξ' h hj hzΞ hzN) W

/-- A vertex of `partB s` that is not a node is inside the ring `F_j` of its forest `Ξ'_j`. -/
theorem inside_of_mem_Ξ' (h : XiSetting Ξ σv N₁ Γ F Ξ' J) {j : Fin t} (hj : j ∈ J) {z : S}
    (hz : z ∈ (Ξ' j).V) (hzN : z ∉ ringNodes Γ F) : z ∈ insideSet (F j) := by
  rcases h.U_sub j hj ((Ξ' j).V_subset_U hz) with h' | h'
  · exact absurd ⟨(h.sub j hj).1 hz, fun i => h.foundation.not_inside_of_mem h.hS h' i⟩ hzN
  · exact h'

/-- A vertex of `partB s` that is not a node is inside a ring `F_j`, `j ∈ J`. -/
theorem inside_of_partB (h : XiSetting Ξ σv N₁ Γ F Ξ' J) {s z : S}
    (hz : z ∈ partB σv N₁ F Ξ' J s) (hzN : z ∉ ringNodes Γ F) :
    ∃ j ∈ J, z ∈ insideSet (F j) := by
  obtain ⟨j, hj, u, hu, huF, hzΞ, -⟩ := hz
  exact ⟨j, hj, inside_of_mem_Ξ' h hj hzΞ hzN⟩

/-- The sets `partA s ∪ partB s` of distinct nodes are disjoint. -/
theorem eq_of_partAB (h : XiSetting Ξ σv N₁ Γ F Ξ' J) {s s' z : S}
    (hz : z ∈ partA σv N₁ s ∪ partB σv N₁ F Ξ' J s)
    (hz' : z ∈ partA σv N₁ s' ∪ partB σv N₁ F Ξ' J s') : s = s' := by
  by_cases hzN : z ∈ ringNodes Γ F
  · have h1 : z ∈ partA σv N₁ s := hz.elim id fun hb => partA_of_partB h hb hzN
    have h2 : z ∈ partA σv N₁ s' := hz'.elim id fun hb => partA_of_partB h hb hzN
    exact eq_of_partA h h1 h2
  · have hb : z ∈ partB σv N₁ F Ξ' J s :=
      hz.elim (fun ha => absurd (partA_subset h s ha) hzN) id
    have hb' : z ∈ partB σv N₁ F Ξ' J s' :=
      hz'.elim (fun ha => absurd (partA_subset h s' ha) hzN) id
    obtain ⟨j, hj, u, hu, huF, hzΞ, ⟨W⟩⟩ := hb
    obtain ⟨j', hj', u', hu', hu'F, hzΞ', ⟨W'⟩⟩ := hb'
    have hjj : j = j' := by
      by_contra hne
      exact Set.disjoint_left.mp (h.foundation.disjoint_inside hne)
        (inside_of_mem_Ξ' h hj hzΞ hzN) (inside_of_mem_Ξ' h hj' hzΞ' hzN)
    subst hjj
    have hu'V : u' ∈ Γ.V ∩ F j := ⟨(partA_subset h s' hu').1, hu'F⟩
    exact eq_of_partA h (partA_of_walk_Ξ' h hj hu huF hu'V (W.append W'.reverse)) hu'

/-- The edges of a walk are edges of the graph. -/
theorem edge_mem_of_mem_edges {β' : Type*} {G' : Graph S β'} {p q : S} (W : GraphWalk G' p q)
    {e : β'} (he : e ∈ W.edges) : e ∈ E(G') := by
  induction W with
  | nil _ => simp [GraphWalk.edges] at he
  | cons hl rest ih =>
    simp only [GraphWalk.edges, List.mem_cons] at he
    rcases he with rfl | he
    · exact hl.edge_mem
    · exact ih he

/-- Links of `Γ` between points of `Z` by edges not in `Eb`. -/
@[expose] def linkRel (Γ : Drawing S) (Z : Set S) (Eb : Set (Set S)) (p q : S) : Prop :=
  p ∈ Z ∧ q ∈ Z ∧ ∃ e, e ∉ Eb ∧ Γ.toGraph.IsLink e p q

theorem linkRel_symm {Z : Set S} {Eb : Set (Set S)} : Symmetric (linkRel Γ Z Eb) :=
  fun _ _ ⟨hp, hq, e, he, hl⟩ => ⟨hq, hp, e, he, hl.symm⟩

/-- A walk of a subgraph of `Γ` whose vertices reachable from its start lie in `Z`, and whose
edges avoid `Eb`, gives a chain of `linkRel`. -/
theorem reflTransGen_of_walk {G' : Graph S (Set S)} (hG' : G' ≤ Γ.toGraph) {Z : Set S}
    {Eb : Set (Set S)} {p q : S} (W : GraphWalk G' p q)
    (hZ : ∀ w, Nonempty (GraphWalk G' p w) → w ∈ Z) (hE : ∀ e ∈ W.edges, e ∉ Eb) :
    Relation.ReflTransGen (linkRel Γ Z Eb) p q := by
  induction W with
  | nil _ => exact .refl
  | @cons u w' v' e hl rest ih =>
    refine Relation.ReflTransGen.head ⟨hZ u ⟨.nil hl.left_mem⟩,
      hZ w' ⟨.cons hl (.nil hl.right_mem)⟩, e, hE e (by simp), hl.mono hG'⟩ ?_
    exact ih (fun w ⟨W'⟩ => hZ w ⟨.cons hl W'⟩) (fun f hf => hE f (by simp [hf]))

/-- The branch set `partA s ∪ partB s` is joined by links of `Γ` that avoid `Eb`, if each edge of
`σ(s)` has equal ends, or is replaced by a link of `Γ` avoiding `Eb`, or lies in the cell of a
ring `F_j`, `j ∈ J`, with its ends on `F_j`. -/
theorem reflTransGen_partAB (h : XiSetting Ξ σv N₁ Γ F Ξ' J) {s : S} (hs : s ∈ N₁)
    {Eb : Set (Set S)} (hEb : ∀ j ∈ J, ∀ e ∈ (Ξ' j).E, e ∉ Eb)
    (hstep : ∀ f p q, (σv s).IsLink f p q → p = q ∨ (∃ e, e ∉ Eb ∧ Γ.toGraph.IsLink e p q) ∨
      ∃ j ∈ J, f ⊆ (F j ∪ insideSet (F j)) \ ringNodes Γ F ∧ p ∈ F j ∧ q ∈ F j) :
    ∀ p ∈ partA σv N₁ s ∪ partB σv N₁ F Ξ' J s, ∀ q ∈ partA σv N₁ s ∪ partB σv N₁ F Ξ' J s,
      Relation.ReflTransGen (linkRel Γ (partA σv N₁ s ∪ partB σv N₁ F Ξ' J s) Eb) p q := by
  set Z := partA σv N₁ s ∪ partB σv N₁ F Ξ' J s
  have hC := h.comp s hs
  -- One edge of `σ(s)`.
  have hone : ∀ f p q, (σv s).IsLink f p q → Relation.ReflTransGen (linkRel Γ Z Eb) p q := by
    intro f p q hl
    have hp : p ∈ partA σv N₁ s := ⟨hs, hl.left_mem⟩
    have hq : q ∈ partA σv N₁ s := ⟨hs, hl.right_mem⟩
    rcases hstep f p q hl with rfl | ⟨e, he, hle⟩ | ⟨j, hj, hfc, hpF, hqF⟩
    · exact .refl
    · exact .single ⟨Or.inl hp, Or.inl hq, e, he, hle⟩
    · have hlx := xiPart_isLink (hl.mono hC.1) hfc
      have hpV : p ∈ Γ.V ∩ F j := ⟨(partA_subset h s hp).1, hpF⟩
      have hqV : q ∈ Γ.V ∩ F j := ⟨(partA_subset h s hq).1, hqF⟩
      obtain ⟨-, -, ⟨W⟩⟩ := (h.iff j hj p hpV q hqV).mp
        ⟨hlx.left_mem, hlx.right_mem, ⟨.cons hlx (.nil hlx.right_mem)⟩⟩
      refine reflTransGen_of_walk (GM16.toGraph_le_of_isSubdrawing (h.sub j hj)) W
        (fun w ⟨W'⟩ => Or.inr ⟨j, hj, p, hp, hpF, ?_, ⟨W'⟩⟩) (fun e he => hEb j hj e ?_)
      · exact W'.end_mem_support |> GraphWalk.mem_vertexSet_of_mem_support W'
      · exact edge_mem_of_mem_edges W he
  -- Two vertices of `σ(s)`.
  have htwo : ∀ p ∈ partA σv N₁ s, ∀ q ∈ partA σv N₁ s,
      Relation.ReflTransGen (linkRel Γ Z Eb) p q := by
    intro p hp q hq
    obtain ⟨W⟩ := hC.2.1.2 p hp.2 q hq.2
    clear hp hq
    induction W with
    | nil _ => exact .refl
    | cons hl rest ih => exact (hone _ _ _ hl).trans ih
  -- Each point of `Z` is joined to a vertex of `σ(s)`.
  have hanchor : ∀ z ∈ Z, ∃ a ∈ partA σv N₁ s, Relation.ReflTransGen (linkRel Γ Z Eb) a z := by
    rintro z (hz | ⟨j, hj, u, hu, huF, hzΞ, ⟨W⟩⟩)
    · exact ⟨z, hz, .refl⟩
    · refine ⟨u, hu, reflTransGen_of_walk (GM16.toGraph_le_of_isSubdrawing (h.sub j hj)) W
        (fun w ⟨W'⟩ => Or.inr ⟨j, hj, u, hu, huF, ?_, ⟨W'⟩⟩) (fun e he => hEb j hj e ?_)⟩
      · exact W'.end_mem_support |> GraphWalk.mem_vertexSet_of_mem_support W'
      · exact edge_mem_of_mem_edges W he
  intro p hp q hq
  obtain ⟨a, ha, hap⟩ := hanchor p hp
  obtain ⟨b, hb, hbq⟩ := hanchor q hq
  have hsymm : Relation.ReflTransGen (linkRel Γ Z Eb) p a := by
    clear hbq hb hp
    induction hap with
    | refl => exact .refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (linkRel_symm hbc) ih
  exact (hsymm.trans (htwo a ha b hb)).trans hbq

end GM08
end GraphMinor
