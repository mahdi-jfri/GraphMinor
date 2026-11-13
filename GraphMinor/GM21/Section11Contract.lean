module

public import GraphMinor.GM21.Section11Core
public import GraphMinor.GM21.Section1Two

/-!
# Graph Minors XXI, (11.1): contracting an edge

Steps (1) to (3) of the proof of (11.1) delete an isolated vertex or contract an edge, and use
induction. This file gives the tools.

* `contract x y e H`: the graph `H / e`, where `e` has ends `x` and `y`; the new vertex is called
  `x`, and `y` is gone. `mergeVertex x y` sends `y` to `x` and fixes every other vertex.
* Reachability in `H` and in `H / e` agree (`reachable_contract_iff`), so contracting `e` does not
  lower the number of components (`numComponents_le_contract`).
* The number of components of `G` with an isolated vertex deleted (`numComponents_le_delete`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-! ## Counting components -/

section Components

/-- If `f` is constant on the fibres of `g` over `s`, then `f` takes at most as many values on `s`
as `g` does. -/
theorem ncard_image_le_of_factor {γ δ : Type*} {s : Set α} (hs : s.Finite) {f : α → γ}
    {g : α → δ} (h : ∀ u ∈ s, ∀ v ∈ s, g u = g v → f u = f v) :
    (f '' s).ncard ≤ (g '' s).ncard := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨u₀, -⟩
  · simp
  let k : δ → γ := fun c ↦ if hc : ∃ u ∈ s, g u = c then f hc.choose else f u₀
  have hk : f '' s = k '' (g '' s) := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨g u, ⟨u, hu, rfl⟩, ?_⟩
      have hc : ∃ u' ∈ s, g u' = g u := ⟨u, hu, rfl⟩
      simp only [k, hc, dite_true]
      exact h _ hc.choose_spec.1 _ hu hc.choose_spec.2
    · rintro ⟨c, ⟨u, hu, rfl⟩, rfl⟩
      have hc : ∃ u' ∈ s, g u' = g u := ⟨u, hu, rfl⟩
      simp only [k, hc, dite_true]
      exact ⟨_, hc.choose_spec.1, rfl⟩
  rw [hk]
  exact ncard_image_le (hs.image g)

/-- The components of a graph are the components `reachableComponent H v` of its vertices. -/
theorem setOf_isComponentOf_eq {H : Hypergraph α β} (hH : H.IsGraph) :
    {C | IsComponentOf H C} = reachableComponent H '' H.vertexSet := by
  ext C
  constructor
  · intro hC
    obtain ⟨v, hv⟩ := hC.2.1
    exact ⟨v, hC.1.vertexSet_subset hv, (eq_reachableComponent_of_isComponentOf hH hC hv).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact isComponentOf_reachableComponent hH hv

theorem numComponents_eq {H : Hypergraph α β} (hH : H.IsGraph) :
    numComponents H = (reachableComponent H '' H.vertexSet).ncard := by
  rw [numComponents, setOf_isComponentOf_eq hH]

/-- A vertex joined to a vertex of `H` by a path of `H` is a vertex of `H`. -/
theorem mem_vertexSet_of_reachable {H : Hypergraph α β} {u v : α} (hu : u ∈ H.vertexSet)
    (hr : H.skeleton.Reachable u v) : v ∈ H.vertexSet := by
  obtain ⟨w⟩ := hr
  exact mem_vertexSet_of_mem_walk_support hu w w.end_mem_support

/-- Two vertices joined by a path have the same component. -/
theorem reachableComponent_eq_of_reachable {H : Hypergraph α β} (hH : H.IsGraph) {u v : α}
    (hu : u ∈ H.vertexSet) (hr : H.skeleton.Reachable u v) :
    reachableComponent H u = reachableComponent H v :=
  (eq_reachableComponent_of_isComponentOf hH
    (isComponentOf_reachableComponent hH (mem_vertexSet_of_reachable hu hr))
    ⟨hu, hr.symm⟩).symm

end Components

/-! ## The contraction `H / e` -/

section Contract

/-- The map `V(H) → V(H / e)`: it sends `y` to `x` and fixes every other vertex. -/
noncomputable def mergeVertex (x y : α) (v : α) : α := by
  classical
  exact if v = y then x else v

theorem mergeVertex_self (x y : α) : mergeVertex x y y = x := by
  simp [mergeVertex]

theorem mergeVertex_of_ne {x y v : α} (h : v ≠ y) : mergeVertex x y v = v := by
  simp [mergeVertex, h]

theorem mergeVertex_eq_iff {x y v w : α} :
    mergeVertex x y v = w ↔ (v ≠ y ∧ v = w) ∨ (v = y ∧ x = w) := by
  by_cases h : v = y
  · subst h; simp [mergeVertex_self]
  · simp [mergeVertex_of_ne h, h]

/-- `H / e`, for an edge `e` with ends `x` and `y`: the vertex `y` is merged into `x`, and `e` is
deleted. If `y ∉ V(H)` and `e ∉ E(H)`, then `H / e = H` (`contract_eq_self`). -/
def contract (x y : α) (e : β) (H : Hypergraph α β) : Hypergraph α β where
  vertexSet := {v | (v ∈ H.vertexSet ∧ v ≠ y) ∨ (v = x ∧ y ∈ H.vertexSet)}
  edgeSet := H.edgeSet \ {e}
  Inc f v := f ≠ e ∧ ((H.Inc f v ∧ v ≠ y) ∨ (v = x ∧ H.Inc f y))
  vertex_mem_of_inc _ _ h := by
    rcases h.2 with ⟨h', hv⟩ | ⟨rfl, h'⟩
    · exact Or.inl ⟨H.vertex_mem_of_inc h', hv⟩
    · exact Or.inr ⟨rfl, H.vertex_mem_of_inc h'⟩
  edge_mem_of_inc _ _ h := by
    refine ⟨?_, h.1⟩
    rcases h.2 with ⟨h', -⟩ | ⟨-, h'⟩ <;> exact H.edge_mem_of_inc h'
  vertexSet_finite := (H.vertexSet_finite.union (finite_singleton x)).subset fun v hv ↦ by
    rcases hv with ⟨hv, -⟩ | ⟨rfl, -⟩
    · exact Or.inl hv
    · exact Or.inr rfl
  edgeSet_finite := H.edgeSet_finite.subset sdiff_subset

variable {x y : α} {e : β}

theorem mem_contract_vertexSet {H : Hypergraph α β} {v : α} :
    v ∈ (contract x y e H).vertexSet ↔ (v ∈ H.vertexSet ∧ v ≠ y) ∨ (v = x ∧ y ∈ H.vertexSet) :=
  Iff.rfl

theorem contract_inc {H : Hypergraph α β} {f : β} {v : α} :
    (contract x y e H).Inc f v ↔ f ≠ e ∧ ((H.Inc f v ∧ v ≠ y) ∨ (v = x ∧ H.Inc f y)) :=
  Iff.rfl

/-- `V(H / e)` is the image of `V(H)`. -/
theorem contract_vertexSet_eq_image (H : Hypergraph α β) :
    (contract x y e H).vertexSet = mergeVertex x y '' H.vertexSet := by
  ext v
  rw [mem_contract_vertexSet, mem_image]
  simp only [mergeVertex_eq_iff]
  constructor
  · rintro (⟨hv, hvy⟩ | ⟨rfl, hy⟩)
    · exact ⟨v, hv, Or.inl ⟨hvy, rfl⟩⟩
    · exact ⟨y, hy, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨w, hw, ⟨hwy, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨hw, hwy⟩
    · exact Or.inr ⟨rfl, hw⟩

theorem mergeVertex_mem_contract {H : Hypergraph α β} {v : α} (hv : v ∈ H.vertexSet) :
    mergeVertex x y v ∈ (contract x y e H).vertexSet := by
  rw [contract_vertexSet_eq_image]
  exact mem_image_of_mem _ hv

theorem contract_le {H K : Hypergraph α β} (hle : H ≤ K) :
    contract x y e H ≤ contract x y e K where
  vertexSet_subset v hv := by
    rcases hv with ⟨hv, hvy⟩ | ⟨rfl, hy⟩
    · exact Or.inl ⟨hle.vertexSet_subset hv, hvy⟩
    · exact Or.inr ⟨rfl, hle.vertexSet_subset hy⟩
  edgeSet_subset f hf := ⟨hle.edgeSet_subset hf.1, hf.2⟩
  ends_eq f hf := by
    ext v
    simp only [Hypergraph.ends, mem_ofPred_eq, contract_inc, GM10.inc_iff_of_le hle hf.1]

theorem contract_union (A B : Hypergraph α β) :
    contract x y e (A ∪ B) = contract x y e A ∪ contract x y e B := by
  ext
  · simp only [mem_contract_vertexSet]
    show _ ↔ _ ∨ _
    simp only [mem_contract_vertexSet]
    change ((_ ∨ _) ∧ _) ∨ (_ ∧ (_ ∨ _)) ↔ _
    tauto
  · change _ ∈ (A.edgeSet ∪ B.edgeSet) \ {e} ↔ _ ∈ (A.edgeSet \ {e}) ∪ (B.edgeSet \ {e})
    rw [union_sdiff_distrib]
  · change _ ∧ (((_ ∨ _) ∧ _) ∨ (_ ∧ (_ ∨ _))) ↔ (_ ∧ _) ∨ (_ ∧ _)
    tauto

/-- If `y ∉ V(H)` and `e ∉ E(H)`, then `H / e = H`. -/
theorem contract_eq_self {H : Hypergraph α β} (hy : y ∉ H.vertexSet) (he : e ∉ H.edgeSet) :
    contract x y e H = H := by
  ext v
  · rw [mem_contract_vertexSet]
    constructor
    · rintro (⟨hv, -⟩ | ⟨-, h⟩)
      · exact hv
      · exact absurd h hy
    · intro hv
      exact Or.inl ⟨hv, fun h ↦ hy (h ▸ hv)⟩
  · change v ∈ H.edgeSet \ {e} ↔ _
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun h' ↦ he ((mem_singleton_iff.1 h') ▸ h)⟩⟩
  · rename_i w
    rw [contract_inc]
    constructor
    · rintro ⟨-, ⟨h, -⟩ | ⟨-, h⟩⟩
      · exact h
      · exact absurd (H.vertex_mem_of_inc h) hy
    · intro h
      refine ⟨fun h' ↦ he (h' ▸ H.edge_mem_of_inc h), Or.inl ⟨h, ?_⟩⟩
      rintro rfl
      exact hy (H.vertex_mem_of_inc h)

/-! ### Reachability -/

variable {H : Hypergraph α β}

/-- Paths of `H` map to paths of `H / e`, if the ends of `e` are among `x` and `y`. -/
theorem reachable_contract_of_reachable (hends : ∀ v, H.Inc e v → v = x ∨ v = y) {u v : α}
    (hr : H.skeleton.Reachable u v) :
    (contract x y e H).skeleton.Reachable (mergeVertex x y u) (mergeVertex x y v) := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj p ih =>
    refine SimpleGraph.Reachable.trans ?_ ih
    obtain ⟨hab, f, ha, hb⟩ := hadj
    by_cases hf : f = e
    · subst hf
      have hma : ∀ z, H.Inc f z → mergeVertex x y z = x := fun z hz ↦ by
        rcases hends z hz with rfl | rfl
        · by_cases hzy : z = y
          · rw [hzy, mergeVertex_self]
          · exact mergeVertex_of_ne hzy
        · exact mergeVertex_self _ _
      rw [hma a ha, hma b hb]
    by_cases hm : mergeVertex x y a = mergeVertex x y b
    · rw [hm]
    have hinc : ∀ z, H.Inc f z → (contract x y e H).Inc f (mergeVertex x y z) := fun z hz ↦ by
      refine ⟨hf, ?_⟩
      by_cases hzy : z = y
      · subst hzy; rw [mergeVertex_self]; exact Or.inr ⟨rfl, hz⟩
      · rw [mergeVertex_of_ne hzy]; exact Or.inl ⟨hz, hzy⟩
    exact SimpleGraph.Adj.reachable ⟨hm, f, hinc a ha, hinc b hb⟩

/-- A vertex of `H / e` has a preimage in `H`. -/
theorem exists_preimage_of_mem_contract {a : α} (ha : a ∈ (contract x y e H).vertexSet) :
    ∃ u ∈ H.vertexSet, mergeVertex x y u = a := by
  rw [contract_vertexSet_eq_image] at ha
  exact ha

/-- If `e ∈ E(H)` joins `x` and `y`, then two vertices of `H` with the same image are joined by a
path of `H`. -/
theorem reachable_of_mergeVertex_eq (hex : H.Inc e x) (hey : H.Inc e y) {u v : α}
    (h : mergeVertex x y u = mergeVertex x y v) :
    H.skeleton.Reachable u v := by
  by_cases huv : u = v
  · rw [huv]
  have hxy : H.skeleton.Reachable x y := by
    by_cases hxy : x = y
    · rw [hxy]
    · exact SimpleGraph.Adj.reachable ⟨hxy, e, hex, hey⟩
  by_cases huy : u = y <;> by_cases hvy : v = y
  · rw [huy, hvy]
  · rw [huy, mergeVertex_self, mergeVertex_of_ne hvy] at h
    rw [huy, ← h]
    exact hxy.symm
  · rw [hvy, mergeVertex_self, mergeVertex_of_ne huy] at h
    rw [hvy, h]
    exact hxy
  · rw [mergeVertex_of_ne huy, mergeVertex_of_ne hvy] at h
    exact absurd h huv

/-- Paths of `H / e` lift to paths of `H`, if `e ∈ E(H)` joins `x` and `y`. -/
theorem reachable_of_reachable_contract (hex : H.Inc e x) (hey : H.Inc e y) {a b : α}
    (hr : (contract x y e H).skeleton.Reachable a b) {u v : α} (hu : u ∈ H.vertexSet)
    (hua : mergeVertex x y u = a) (hvb : mergeVertex x y v = b) :
    H.skeleton.Reachable u v := by
  obtain ⟨w⟩ := hr
  induction w generalizing u with
  | nil =>
    exact reachable_of_mergeVertex_eq hex hey (hua.trans hvb.symm)
  | @cons a c b hadj p ih =>
    obtain ⟨hac, f, ha, hc⟩ := hadj
    -- Preimages of `a` and `c` incident with `f`.
    have hpre : ∀ z, (contract x y e H).Inc f z →
        ∃ z', H.Inc f z' ∧ mergeVertex x y z' = z := by
      rintro z ⟨-, ⟨hz, hzy⟩ | ⟨rfl, hz⟩⟩
      · exact ⟨z, hz, mergeVertex_of_ne hzy⟩
      · exact ⟨y, hz, mergeVertex_self _ _⟩
    obtain ⟨a', ha', rfl⟩ := hpre a ha
    obtain ⟨c', hc', rfl⟩ := hpre _ hc
    have ha'H := H.vertex_mem_of_inc ha'
    have hc'H := H.vertex_mem_of_inc hc'
    have hstep : H.skeleton.Reachable a' c' := by
      by_cases h : a' = c'
      · rw [h]
      · exact SimpleGraph.Adj.reachable ⟨h, f, ha', hc'⟩
    exact (reachable_of_mergeVertex_eq hex hey hua).trans (hstep.trans (ih hc'H rfl hvb))

/-- If `e ∈ E(H)` joins `x` and `y` and has no other end, then two vertices of `H` are joined by a
path of `H` exactly when their images are joined by a path of `H / e`. -/
theorem reachable_contract_iff (hex : H.Inc e x) (hey : H.Inc e y)
    (hends : ∀ v, H.Inc e v → v = x ∨ v = y) {u v : α} (hu : u ∈ H.vertexSet) :
    (contract x y e H).skeleton.Reachable (mergeVertex x y u) (mergeVertex x y v) ↔
      H.skeleton.Reachable u v :=
  ⟨fun h ↦ reachable_of_reachable_contract hex hey h hu rfl rfl,
    reachable_contract_of_reachable hends⟩

/-- Contracting an edge does not lower the number of components. -/
theorem numComponents_le_contract (hH : H.IsGraph) (hHc : (contract x y e H).IsGraph)
    (hex : H.Inc e x) (hey : H.Inc e y) :
    numComponents H ≤ numComponents (contract x y e H) := by
  rw [numComponents_eq hH, numComponents_eq hHc, contract_vertexSet_eq_image, image_image]
  refine ncard_image_le_of_factor H.vertexSet_finite fun u hu v hv h ↦ ?_
  have hmv := mergeVertex_mem_contract (e := e) (x := x) (y := y) hv
  have hr : (contract x y e H).skeleton.Reachable (mergeVertex x y u) (mergeVertex x y v) := by
    have := self_mem_reachableComponent hmv
    rw [← h] at this
    exact this.2
  exact reachableComponent_eq_of_reachable hH hu
    (reachable_of_reachable_contract hex hey hr hu rfl rfl)

end Contract

/-! ## Deleting an isolated vertex -/

/-- Deleting a vertex lowers the number of components by at most one. -/
theorem numComponents_le_delete {H : Hypergraph α β} (v : α) (hH : H.IsGraph)
    (hHd : (GM10.deleteVertices H {v}).IsGraph) :
    numComponents H ≤ numComponents (GM10.deleteVertices H {v}) + 1 := by
  rw [numComponents_eq hH, numComponents_eq hHd]
  have hsub : reachableComponent H '' H.vertexSet ⊆
      insert (reachableComponent H v) (reachableComponent H '' (H.vertexSet \ {v})) := by
    rintro _ ⟨u, hu, rfl⟩
    by_cases huv : u = v
    · rw [huv]; exact mem_insert _ _
    · exact mem_insert_of_mem _ ⟨u, ⟨hu, huv⟩, rfl⟩
  refine (ncard_le_ncard hsub ((H.vertexSet_finite.sdiff).image _ |>.insert _)).trans
    ((ncard_insert_le _ _).trans (Nat.add_le_add_right ?_ 1))
  refine ncard_image_le_of_factor (H.vertexSet_finite.sdiff) fun u hu w hw h ↦ ?_
  have hw' : w ∈ (GM10.deleteVertices H {v}).vertexSet := hw
  have := self_mem_reachableComponent hw'
  rw [← h] at this
  exact reachableComponent_eq_of_reachable hH hu.1
    (reachable_of_le (GM10.deleteVertices_le H {v}) this.2)

/-! ## The pattern of a linkage from its terminals -/

/-- The pattern of a linkage: the block of a terminal `t` is the set of terminals joined to `t`. -/
theorem linkagePattern_eq_image {G L : Hypergraph α β} (hL : IsLinkage G L) :
    linkagePattern L =
      (fun t ↦ {t' ∈ terminals L | L.skeleton.Reachable t t'}) '' terminals L := by
  ext B
  constructor
  · intro hB
    obtain ⟨t, htB⟩ : B.Nonempty := by
      rcases hL.mem_linkagePattern_structure hB with ⟨a, _, h, _⟩ | ⟨a, _, _, _, _, h, _⟩
      · exact ⟨a, by rw [h]; rfl⟩
      · exact ⟨a, by rw [h]; exact mem_insert _ _⟩
    obtain ⟨C, hC, rfl⟩ := hB
    have hBt := htB
    have ht := htB.1
    refine ⟨t, ht, ?_⟩
    rw [eq_reachableComponent_of_isComponentOf hL.2.1 hC hBt.2]
    ext t'
    exact ⟨fun h ↦ ⟨h.1, ⟨h.1.1, h.2⟩⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨reachableComponent L t, isComponentOf_reachableComponent hL.2.1 ht.1, ?_⟩
    ext t'
    exact ⟨fun h ↦ ⟨h.1, ⟨h.1.1, h.2⟩⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩

/-- A linkage that is a subgraph of `B` is a linkage in `B`. -/
theorem IsLinkage.mono_ambient {A B L : Hypergraph α β} (h : IsLinkage A L) (hLB : L ≤ B) :
    IsLinkage B L :=
  ⟨hLB, h.2.1, h.2.2⟩

/-! ## Contracting an edge of a linkage -/

section ContractLinkage

variable {G N : Hypergraph α β} {x y : α} {e : β}

/-- The ends of an edge with two ends `x ≠ y`. -/
theorem ends_eq_pair_of_ncard {H : Hypergraph α β} (h2 : (H.ends e).ncard = 2) (hex : H.Inc e x)
    (hey : H.Inc e y) (hxy : x ≠ y) : H.ends e = {x, y} := by
  refine (eq_of_subset_of_ncard_le ?_ ?_ (finite_of_ncard_ne_zero (by omega))).symm
  · rintro v (rfl | rfl)
    · exact hex
    · exact hey
  · rw [h2, ncard_pair hxy]

variable (hN : IsLinkage G N) (heN : e ∈ N.edgeSet) (hex : N.Inc e x) (hey : N.Inc e y)
  (hxy : x ≠ y)
include hN heN hex hey hxy

theorem ends_of_inc_e {v : α} (hv : N.Inc e v) : v = x ∨ v = y := by
  have := ends_eq_pair_of_ncard (hN.ends_ncard_eq_two heN) hex hey hxy
  have hv' : v ∈ N.ends e := hv
  rw [this] at hv'
  exact hv'

/-- In a linkage, an edge other than `e` is not incident with both `x` and `y`. -/
theorem not_inc_both {f : β} (hf : f ∈ N.edgeSet) (hfe : f ≠ e) (hfx : N.Inc f x)
    (hfy : N.Inc f y) : False := by
  have h1 := ends_eq_pair_of_ncard (hN.ends_ncard_eq_two hf) hfx hfy hxy
  have h2 := ends_eq_pair_of_ncard (hN.ends_ncard_eq_two heN) hex hey hxy
  exact hfe (no_parallel_edges_of_exists_deg_one
    (fun H hH hHne ↦ hN.exists_deg_one_of_le hH hHne) f hf e heN (h1.trans h2.symm))

theorem incidentEdges_contract_of_ne {v : α} (hvx : v ≠ x) (hvy : v ≠ y) :
    incidentEdges (contract x y e N) v = incidentEdges N v := by
  ext f
  simp only [incidentEdges, mem_ofPred_eq, contract_inc]
  constructor
  · rintro ⟨⟨hf, -⟩, -, ⟨h, -⟩ | ⟨h, -⟩⟩
    · exact ⟨hf, h⟩
    · exact absurd h hvx
  · rintro ⟨hf, h⟩
    have hfe : f ≠ e := by
      rintro rfl
      rcases ends_of_inc_e hN heN hex hey hxy h with h' | h'
      · exact hvx h'
      · exact hvy h'
    exact ⟨⟨hf, hfe⟩, hfe, Or.inl ⟨h, hvy⟩⟩

theorem incidentEdges_contract_x :
    incidentEdges (contract x y e N) x = (incidentEdges N x ∪ incidentEdges N y) \ {e} := by
  ext f
  simp only [incidentEdges, mem_ofPred_eq, contract_inc, mem_sdiff, mem_union, mem_singleton_iff]
  constructor
  · rintro ⟨⟨hf, -⟩, hfe, ⟨h, -⟩ | ⟨-, h⟩⟩
    · exact ⟨Or.inl ⟨hf, h⟩, hfe⟩
    · exact ⟨Or.inr ⟨hf, h⟩, hfe⟩
  · rintro ⟨⟨hf, h⟩ | ⟨hf, h⟩, hfe⟩
    · exact ⟨⟨hf, hfe⟩, hfe, Or.inl ⟨h, hxy⟩⟩
    · exact ⟨⟨hf, hfe⟩, hfe, Or.inr ⟨trivial, h⟩⟩

theorem ncard_incidentEdges_contract_x :
    (incidentEdges (contract x y e N) x).ncard + 2 =
      (incidentEdges N x).ncard + (incidentEdges N y).ncard := by
  have hfin : ∀ v, (incidentEdges N v).Finite := fun v ↦ N.edgeSet_finite.subset fun _ h ↦ h.1
  have hinter : incidentEdges N x ∩ incidentEdges N y = {e} := by
    ext f
    constructor
    · rintro ⟨⟨hf, hfx⟩, ⟨-, hfy⟩⟩
      by_contra hfe
      exact not_inc_both hN heN hex hey hxy hf hfe hfx hfy
    · rintro rfl
      exact ⟨⟨heN, hex⟩, ⟨heN, hey⟩⟩
  have hU := ncard_union_add_ncard_inter _ _ (hfin x) (hfin y)
  rw [hinter, ncard_singleton] at hU
  rw [incidentEdges_contract_x hN heN hex hey hxy,
    ncard_sdiff_singleton_of_mem
      (show e ∈ incidentEdges N x ∪ incidentEdges N y from Or.inl ⟨heN, hex⟩)]
  have : 0 < (incidentEdges N x ∪ incidentEdges N y).ncard :=
    (ncard_pos ((hfin x).union (hfin y))).2 ⟨e, Or.inl ⟨heN, hex⟩⟩
  omega

/-- Every edge of `N / e` has two ends. -/
theorem contract_ends_ncard {f : β} (hf : f ∈ (contract x y e N).edgeSet) :
    ((contract x y e N).ends f).ncard = 2 := by
  obtain ⟨hfN, hfe⟩ := hf
  have hfe : f ≠ e := hfe
  have hends : (contract x y e N).ends f = mergeVertex x y '' N.ends f := by
    ext v
    simp only [Hypergraph.ends, mem_ofPred_eq, contract_inc, mem_image, mergeVertex_eq_iff]
    constructor
    · rintro ⟨-, ⟨h, hvy⟩ | ⟨rfl, h⟩⟩
      · exact ⟨v, h, Or.inl ⟨hvy, rfl⟩⟩
      · exact ⟨y, h, Or.inr ⟨rfl, rfl⟩⟩
    · rintro ⟨w, hw, ⟨hwy, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨hfe, Or.inl ⟨hw, hwy⟩⟩
      · exact ⟨hfe, Or.inr ⟨rfl, hw⟩⟩
  rw [hends]
  obtain ⟨a, b, hab, hfab⟩ := ncard_eq_two.1 (hN.ends_ncard_eq_two hfN)
  rw [hfab, image_pair, ncard_pair]
  intro hm
  have ha : N.Inc f a := by rw [← mem_ofPred_eq (p := N.Inc f), ← Hypergraph.ends, hfab]; simp
  have hb : N.Inc f b := by rw [← mem_ofPred_eq (p := N.Inc f), ← Hypergraph.ends, hfab]; simp
  by_cases hay : a = y
  · rw [hay, mergeVertex_self] at hm
    rw [hay] at ha
    have hbx : b = x := by
      by_cases hby : b = y
      · exact absurd (hay.trans hby.symm) hab
      · rw [mergeVertex_of_ne hby] at hm; exact hm.symm
    rw [hbx] at hb
    exact not_inc_both hN heN hex hey hxy hfN hfe hb ha
  · rw [mergeVertex_of_ne hay] at hm
    by_cases hby : b = y
    · rw [hby, mergeVertex_self] at hm
      rw [hby] at hb
      rw [hm] at ha
      exact not_inc_both hN heN hex hey hxy hfN hfe ha hb
    · rw [mergeVertex_of_ne hby] at hm
      exact hab hm

theorem vertexDegree_contract_eq (v : α) :
    vertexDegree (contract x y e N) v = (incidentEdges (contract x y e N) v).ncard :=
  vertexDegree_eq_ncard_incidentEdges (fun _ hf ↦ contract_ends_ncard hN heN hex hey hxy hf) v

theorem one_le_ncard_incidentEdges_x : 1 ≤ (incidentEdges N x).ncard :=
  (ncard_pos (N.edgeSet_finite.subset fun _ h ↦ h.1)).2 ⟨e, heN, hex⟩

theorem one_le_ncard_incidentEdges_y : 1 ≤ (incidentEdges N y).ncard :=
  (ncard_pos (N.edgeSet_finite.subset fun _ h ↦ h.1)).2 ⟨e, heN, hey⟩

/-- The terminals of `N / e` are the images of the terminals of `N`. -/
theorem terminals_contract : terminals (contract x y e N) = mergeVertex x y '' terminals N := by
  have hdegN : ∀ v, vertexDegree N v = (incidentEdges N v).ncard :=
    vertexDegree_eq_ncard_incidentEdges fun _ hf ↦ hN.ends_ncard_eq_two hf
  have hxN : x ∈ N.vertexSet := N.vertex_mem_of_inc hex
  have hyN : y ∈ N.vertexSet := N.vertex_mem_of_inc hey
  ext v
  simp only [terminals, IsTerminal, mem_ofPred_eq, mem_image, mergeVertex_eq_iff,
    vertexDegree_contract_eq hN heN hex hey hxy, hdegN]
  by_cases hvx : v = x
  · subst hvx
    have h1 := ncard_incidentEdges_contract_x hN heN hex hey hxy
    have h2 := hN.ncard_incidentEdges_le_two v
    have h3 := hN.ncard_incidentEdges_le_two y
    have h4 := one_le_ncard_incidentEdges_x hN heN hex hey hxy
    have h5 := one_le_ncard_incidentEdges_y hN heN hex hey hxy
    constructor
    · rintro ⟨-, hdeg⟩
      by_cases hx1 : (incidentEdges N v).ncard ≤ 1
      · exact ⟨v, ⟨hxN, hx1⟩, Or.inl ⟨hxy, rfl⟩⟩
      · exact ⟨y, ⟨hyN, by omega⟩, Or.inr ⟨rfl, rfl⟩⟩
    · rintro ⟨w, ⟨-, hw⟩, ⟨-, rfl⟩ | ⟨rfl, -⟩⟩
      · exact ⟨Or.inl ⟨hxN, hxy⟩, by omega⟩
      · exact ⟨Or.inl ⟨hxN, hxy⟩, by omega⟩
  by_cases hvy : v = y
  · subst hvy
    constructor
    · rintro ⟨⟨-, h⟩ | ⟨h, -⟩, -⟩
      · exact absurd rfl h
      · exact absurd h.symm hxy
    · rintro ⟨w, -, ⟨hw, rfl⟩ | ⟨-, h⟩⟩
      · exact absurd rfl hw
      · exact absurd h hxy
  rw [incidentEdges_contract_of_ne hN heN hex hey hxy hvx hvy]
  constructor
  · rintro ⟨⟨hv, -⟩ | ⟨h, -⟩, hdeg⟩
    · exact ⟨v, ⟨hv, hdeg⟩, Or.inl ⟨hvy, rfl⟩⟩
    · exact absurd h hvx
  · rintro ⟨w, ⟨hw, hdeg⟩, ⟨-, rfl⟩ | ⟨-, h⟩⟩
    · exact ⟨Or.inl ⟨hw, hvy⟩, hdeg⟩
    · exact absurd h.symm hvx

/-- **Contracting an edge of a linkage gives a linkage.** -/
theorem isLinkage_contract (hNG : N ≤ G) : IsLinkage (contract x y e G) (contract x y e N) := by
  have hle := contract_le (x := x) (y := y) (e := e) hNG
  refine isLinkage_of_deg_le_two_of_reachable_deg_le_one hle
    (fun _ hf ↦ contract_ends_ncard hN heN hex hey hxy hf) ?_ ?_
  · intro v _
    by_cases hvx : v = x
    · subst hvx
      have h1 := ncard_incidentEdges_contract_x hN heN hex hey hxy
      have h2 := hN.ncard_incidentEdges_le_two v
      have h3 := hN.ncard_incidentEdges_le_two y
      have h4 := one_le_ncard_incidentEdges_x hN heN hex hey hxy
      have h5 := one_le_ncard_incidentEdges_y hN heN hex hey hxy
      omega
    by_cases hvy : v = y
    · subst hvy
      rw [show incidentEdges (contract x v e N) v = ∅ from eq_empty_of_forall_notMem
        fun f hf ↦ by
          rcases hf.2.2 with ⟨-, h⟩ | ⟨h, -⟩
          · exact h rfl
          · exact hxy h.symm]
      simp
    · rw [incidentEdges_contract_of_ne hN heN hex hey hxy hvx hvy]
      exact hN.ncard_incidentEdges_le_two v
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := exists_preimage_of_mem_contract hv
    obtain ⟨z, hz, hr⟩ := hN.exists_reachable_terminal hu
    have hzc : mergeVertex x y z ∈ terminals (contract x y e N) := by
      rw [terminals_contract hN heN hex hey hxy]
      exact mem_image_of_mem _ hz
    refine ⟨_, hzc.1, reachable_contract_of_reachable
      (fun w hw ↦ ends_of_inc_e hN heN hex hey hxy hw) hr, ?_⟩
    have := hzc.2
    rw [vertexDegree_contract_eq hN heN hex hey hxy] at this
    exact this

/-- **The pattern of `N / e`** is the image of the pattern of `N`. -/
theorem linkagePattern_contract (hNG : N ≤ G) :
    linkagePattern (contract x y e N) = image (mergeVertex x y) '' linkagePattern N := by
  have hc := isLinkage_contract hN heN hex hey hxy hNG
  have hends : ∀ w, N.Inc e w → w = x ∨ w = y :=
    fun w hw ↦ ends_of_inc_e hN heN hex hey hxy hw
  rw [linkagePattern_eq_image hc, linkagePattern_eq_image hN, terminals_contract hN heN hex hey hxy,
    image_image, image_image]
  refine image_congr fun t ht ↦ ?_
  ext s
  simp only [mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨⟨t', ht', rfl⟩, hr⟩
    exact ⟨t', ⟨ht', (reachable_contract_iff hex hey hends ht.1 (v := t')).1 hr⟩, rfl⟩
  · rintro ⟨t', ⟨ht', hr⟩, rfl⟩
    exact ⟨⟨t', ht', rfl⟩, (reachable_contract_iff hex hey hends ht.1 (v := t')).2 hr⟩

end ContractLinkage

/-- If `e ∉ E(H)`, then `H / e` is the image of `H` under `mergeVertex x y`. -/
theorem contract_eq_mapHypergraph {x y : α} {e : β} {H : Hypergraph α β} (he : e ∉ H.edgeSet) :
    contract x y e H = mapHypergraph (mergeVertex x y) id H := by
  ext v
  · rw [contract_vertexSet_eq_image]; rfl
  · change v ∈ H.edgeSet \ {e} ↔ v ∈ id '' H.edgeSet
    rw [image_id]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun h' ↦ he ((mem_singleton_iff.1 h') ▸ h)⟩⟩
  · rename_i w
    rw [contract_inc]
    change _ ↔ ∃ f₀ v₀, H.Inc f₀ v₀ ∧ id f₀ = v ∧ mergeVertex x y v₀ = w
    constructor
    · rintro ⟨-, ⟨h, hwy⟩ | ⟨rfl, h⟩⟩
      · exact ⟨v, w, h, rfl, mergeVertex_of_ne hwy⟩
      · exact ⟨v, y, h, rfl, mergeVertex_self _ _⟩
    · rintro ⟨f₀, v₀, h, rfl, rfl⟩
      refine ⟨fun h' ↦ he (h' ▸ H.edge_mem_of_inc h), ?_⟩
      by_cases hv₀ : v₀ = y
      · subst hv₀; rw [mergeVertex_self]; exact Or.inr ⟨rfl, h⟩
      · rw [mergeVertex_of_ne hv₀]; exact Or.inl ⟨h, hv₀⟩

end GM21
end GraphMinor
