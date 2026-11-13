module

public import GraphMinor.GM21.Section11Contract

/-!
# Graph Minors XXI, (11.1): lifting a linkage of `G / e` to `G`

Steps (2) and (3) of the proof of (11.1) contract an edge `e` with ends `x` and `y`, and say that
`G / e` is again an intertwining. For this, every linkage `M` of `G / e` must come from a linkage
`K` of `G` with `K / e = M`, and `K` must have the right pattern. The paper takes this for granted.

There are three ways to lift `M`. Let `a` be the number of edges of `M` at `x` that meet `x` in
`G`, and `b` the number of those that meet `y` in `G`.

* If `b = 0`, then `M` itself is a subgraph of `G` (`lift_le`).
* If `a = 0`, then `M` with `x` renamed `y` is a subgraph of `G` (`swapLift`).
* If `a ≤ 1` and `b ≤ 1`, then `M` with `y` and `e` added is a linkage of `G` (`edgeLift`).

`exists_lift` chooses one of them, so that `K` has the pattern of a given linkage `L` of `G` whose
pattern is sent to that of `M`. Two patterns that agree after `y` is merged into `x` are equal under
a condition on `x` and `y` (`linkagePattern_eq_of_image_eq`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-! ## Patterns that agree after merging `y` into `x` -/

section Pattern

variable {x y : α}

theorem image_eq_self_of_forall {γ : Type*} {f : γ → γ} {S : Set γ} (h : ∀ a ∈ S, f a = a) :
    f '' S = S := by
  conv_rhs => rw [← image_id S]
  exact image_congr h

theorem image_mergeVertex_of_notMem {B : Set α} (hy : y ∉ B) : mergeVertex x y '' B = B :=
  image_eq_self_of_forall fun _ hv ↦ mergeVertex_of_ne fun h ↦ hy (h ▸ hv)

theorem mem_image_mergeVertex_iff {v : α} {B : Set α} :
    v ∈ mergeVertex x y '' B ↔ (v ∈ B ∧ v ≠ y) ∨ (v = x ∧ y ∈ B) := by
  simp only [mem_image, mergeVertex_eq_iff]
  constructor
  · rintro ⟨w, hw, ⟨hwy, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inl ⟨hw, hwy⟩
    · exact Or.inr ⟨rfl, hw⟩
  · rintro (⟨hv, hvy⟩ | ⟨rfl, hy⟩)
    · exact ⟨v, hv, Or.inl ⟨hvy, rfl⟩⟩
    · exact ⟨y, hy, Or.inr ⟨rfl, rfl⟩⟩

theorem image_mergeVertex_pair (hxy : x ≠ y) : mergeVertex x y '' {x, y} = {x} := by
  rw [image_pair, mergeVertex_self, mergeVertex_of_ne hxy, pair_eq_singleton]

/-- Merging `y` into `x` is one-to-one on the sets that avoid `y`. -/
theorem injOn_image_mergeVertex_of_notMem_y :
    InjOn (image (mergeVertex x y)) {B : Set α | y ∉ B} := by
  intro B₁ h₁ B₂ h₂ h
  rwa [image_mergeVertex_of_notMem h₁, image_mergeVertex_of_notMem h₂] at h

/-- Merging `y` into `x` is one-to-one on the sets that avoid `x`. -/
theorem injOn_image_mergeVertex_of_notMem_x :
    InjOn (image (mergeVertex x y)) {B : Set α | x ∉ B} := by
  have hx : ∀ B : Set α, x ∉ B → (x ∈ mergeVertex x y '' B ↔ y ∈ B) := fun B hB ↦ by
    rw [mem_image_mergeVertex_iff]
    constructor
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      exacts [absurd h hB, h]
    · exact fun h ↦ Or.inr ⟨rfl, h⟩
  have ho : ∀ B : Set α, ∀ v, v ≠ x → v ≠ y → (v ∈ mergeVertex x y '' B ↔ v ∈ B) :=
    fun B v hvx hvy ↦ by
      rw [mem_image_mergeVertex_iff]
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩)
        exacts [h, absurd h hvx]
      · exact fun h ↦ Or.inl ⟨h, hvy⟩
  intro B₁ h₁ B₂ h₂ h
  ext v
  by_cases hvy : v = y
  · rw [hvy, ← hx B₁ h₁, ← hx B₂ h₂, h]
  by_cases hvx : v = x
  · rw [hvx]
    exact ⟨fun h' ↦ absurd h' h₁, fun h' ↦ absurd h' h₂⟩
  · rw [← ho B₁ v hvx hvy, ← ho B₂ v hvx hvy, h]

/-- Merging `y` into `x` is one-to-one on `{x, y}` together with the sets that avoid both. -/
theorem injOn_image_mergeVertex_pair (hxy : x ≠ y) :
    InjOn (image (mergeVertex x y)) {B : Set α | (x ∉ B ∧ y ∉ B) ∨ B = {x, y}} := by
  intro B₁ h₁ B₂ h₂ h
  rcases h₁ with ⟨h₁x, h₁y⟩ | rfl <;> rcases h₂ with ⟨h₂x, h₂y⟩ | rfl
  · rwa [image_mergeVertex_of_notMem h₁y, image_mergeVertex_of_notMem h₂y] at h
  · rw [image_mergeVertex_of_notMem h₁y, image_mergeVertex_pair hxy] at h
    exact absurd (h ▸ mem_singleton x) h₁x
  · rw [image_mergeVertex_of_notMem h₂y, image_mergeVertex_pair hxy] at h
    exact absurd (h ▸ mem_singleton x) h₂x
  · rfl

/-- **Two patterns that agree after merging `y` into `x`.** They are equal if neither linkage has
`y` as a terminal, or neither has `x` as a terminal, or both have `{x, y}` as a block. -/
theorem linkagePattern_eq_of_image_eq {G K L : Hypergraph α β} (hxy : x ≠ y)
    (hK : IsLinkage G K) (hL : IsLinkage G L)
    (h : image (mergeVertex x y) '' linkagePattern K =
      image (mergeVertex x y) '' linkagePattern L)
    (hc : (y ∉ terminals K ∧ y ∉ terminals L) ∨ (x ∉ terminals K ∧ x ∉ terminals L) ∨
      ({x, y} ∈ linkagePattern K ∧ {x, y} ∈ linkagePattern L)) :
    linkagePattern K = linkagePattern L := by
  have hsub : ∀ {N : Hypergraph α β}, IsLinkage G N → ∀ B ∈ linkagePattern N, B ⊆ terminals N :=
    fun hN B hB ↦ by
      rw [hN.terminals_eq_sUnion_linkagePattern]
      exact subset_sUnion_of_mem hB
  rcases hc with ⟨hyK, hyL⟩ | ⟨hxK, hxL⟩ | ⟨hpK, hpL⟩
  · exact (injOn_image_mergeVertex_of_notMem_y.image_eq_image_iff
      (fun B hB hy ↦ hyK (hsub hK B hB hy)) (fun B hB hy ↦ hyL (hsub hL B hB hy))).1 h
  · exact (injOn_image_mergeVertex_of_notMem_x.image_eq_image_iff
      (fun B hB hx ↦ hxK (hsub hK B hB hx)) (fun B hB hx ↦ hxL (hsub hL B hB hx))).1 h
  · have hD : ∀ {N : Hypergraph α β}, IsLinkage G N → {x, y} ∈ linkagePattern N →
        linkagePattern N ⊆ {B : Set α | (x ∉ B ∧ y ∉ B) ∨ B = {x, y}} := fun hN hp B hB ↦ by
      by_cases hB' : B = {x, y}
      · exact Or.inr hB'
      · have hd := hN.disjoint_of_mem_linkagePattern hB hp hB'
        exact Or.inl ⟨fun hx ↦ disjoint_left.1 hd hx (Or.inl rfl),
          fun hy ↦ disjoint_left.1 hd hy (Or.inr rfl)⟩
    exact ((injOn_image_mergeVertex_pair hxy).image_eq_image_iff (hD hK hpK) (hD hL hpL)).1 h

end Pattern

/-! ## Contraction and incidence -/

section ContractInc

variable {x y : α} {e : β}

/-- The ends of an edge `f ≠ e` in `H / e` are the images of its ends in `H`. -/
theorem contract_ends {H : Hypergraph α β} {f : β} (hfe : f ≠ e) :
    (contract x y e H).ends f = mergeVertex x y '' H.ends f := by
  ext v
  change (contract x y e H).Inc f v ↔ v ∈ mergeVertex x y '' {w | H.Inc f w}
  rw [contract_inc, mem_image_mergeVertex_iff]
  exact and_iff_right hfe

/-- Contracting an edge of a graph gives a graph. -/
theorem isGraph_contract {H : Hypergraph α β} (hH : H.IsGraph) : (contract x y e H).IsGraph := by
  intro f hf
  obtain ⟨hfH, hfe⟩ := hf
  rw [contract_ends hfe]
  have hfin : (H.ends f).Finite := H.vertexSet_finite.subset fun _ h ↦ H.vertex_mem_of_inc h
  exact ⟨(hH f hfH).1.image _, (ncard_image_le hfin).trans (hH f hfH).2⟩

/-- Away from `x` and `y`, contracting `e` does not change the edges at a vertex. -/
theorem incidentEdges_contract_of_ne' {N : Hypergraph α β}
    (hends : ∀ v, N.Inc e v → v = x ∨ v = y) {v : α} (hvx : v ≠ x) (hvy : v ≠ y) :
    incidentEdges (contract x y e N) v = incidentEdges N v := by
  ext f
  constructor
  · rintro ⟨⟨hf, -⟩, -, ⟨h, -⟩ | ⟨h, -⟩⟩
    · exact ⟨hf, h⟩
    · exact absurd h hvx
  · rintro ⟨hf, h⟩
    have hfe : f ≠ e := by
      rintro rfl
      rcases hends v h with h' | h'
      · exact hvx h'
      · exact hvy h'
    exact ⟨⟨hf, hfe⟩, hfe, Or.inl ⟨h, hvy⟩⟩

end ContractInc

/-! ## The three lifts -/

section Lift

variable {G M : Hypergraph α β} {x y : α} {e : β}

/-- The edges of `M` that meet `v` in `G`. -/
def liftEdges (M G : Hypergraph α β) (v : α) : Set β := {f ∈ M.edgeSet | G.Inc f v}

theorem liftEdges_finite (v : α) : (liftEdges M G v).Finite :=
  M.edgeSet_finite.subset fun _ h ↦ h.1

theorem lift_vertexSet_subset (hex : G.Inc e x) (hM : IsLinkage (contract x y e G) M) :
    M.vertexSet ⊆ G.vertexSet := fun v hv ↦ by
  rcases hM.1.vertexSet_subset hv with ⟨h, -⟩ | ⟨rfl, -⟩
  exacts [h, G.vertex_mem_of_inc hex]

theorem lift_y_notMem (hxy : x ≠ y) (hM : IsLinkage (contract x y e G) M) :
    y ∉ M.vertexSet := fun hy ↦ by
  rcases hM.1.vertexSet_subset hy with ⟨-, h⟩ | ⟨h, -⟩
  exacts [h rfl, hxy h.symm]

theorem lift_edge_mem (hM : IsLinkage (contract x y e G) M) {f : β} (hf : f ∈ M.edgeSet) :
    f ∈ G.edgeSet ∧ f ≠ e :=
  hM.1.edgeSet_subset hf

theorem lift_e_notMem (hM : IsLinkage (contract x y e G) M) : e ∉ M.edgeSet := fun he ↦
  (lift_edge_mem hM he).2 rfl

theorem lift_inc_iff (hM : IsLinkage (contract x y e G) M) {f : β} {v : α}
    (hf : f ∈ M.edgeSet) : M.Inc f v ↔ (G.Inc f v ∧ v ≠ y) ∨ (v = x ∧ G.Inc f y) := by
  rw [GM10.inc_iff_of_le hM.1 hf, contract_inc]
  exact and_iff_right (lift_edge_mem hM hf).2

/-- No edge of `M` meets both `x` and `y` in `G`: it would be a loop of `M`. -/
theorem lift_not_inc_both (hG : G.IsGraph) (hxy : x ≠ y) (hM : IsLinkage (contract x y e G) M)
    {f : β} (hf : f ∈ M.edgeSet) (hfx : G.Inc f x) (hfy : G.Inc f y) : False := by
  have hGf := (lift_edge_mem hM hf).1
  have hends : G.ends f = {x, y} := by
    refine (eq_of_subset_of_ncard_le ?_ ?_
      (G.vertexSet_finite.subset fun _ h ↦ G.vertex_mem_of_inc h)).symm
    · rintro v (rfl | rfl)
      exacts [hfx, hfy]
    · rw [ncard_pair hxy]
      exact (hG f hGf).2
  have hle : (M.ends f).ncard ≤ 1 := by
    calc (M.ends f).ncard ≤ ({x} : Set α).ncard := by
          refine ncard_le_ncard (fun v hv ↦ ?_) (finite_singleton x)
          change M.Inc f v at hv
          rcases (lift_inc_iff hM hf).1 hv with ⟨h, hvy⟩ | ⟨rfl, -⟩
          · have : v ∈ G.ends f := h
            rw [hends] at this
            rcases this with rfl | rfl
            · rfl
            · exact absurd rfl hvy
          · rfl
      _ = 1 := ncard_singleton x
  have := hM.ends_ncard_eq_two hf
  omega

theorem lift_incidentEdges_x (hxy : x ≠ y) (hM : IsLinkage (contract x y e G) M) :
    incidentEdges M x = liftEdges M G x ∪ liftEdges M G y := by
  ext f
  constructor
  · rintro ⟨hf, h⟩
    rcases (lift_inc_iff hM hf).1 h with ⟨h, -⟩ | ⟨-, h⟩
    exacts [Or.inl ⟨hf, h⟩, Or.inr ⟨hf, h⟩]
  · rintro (⟨hf, h⟩ | ⟨hf, h⟩)
    exacts [⟨hf, (lift_inc_iff hM hf).2 (Or.inl ⟨h, hxy⟩)⟩,
      ⟨hf, (lift_inc_iff hM hf).2 (Or.inr ⟨rfl, h⟩)⟩]

/-- The degree of `x` in `M` is `a + b`. -/
theorem lift_ncard_x (hG : G.IsGraph) (hxy : x ≠ y) (hM : IsLinkage (contract x y e G) M) :
    (incidentEdges M x).ncard = (liftEdges M G x).ncard + (liftEdges M G y).ncard := by
  rw [lift_incidentEdges_x hxy hM]
  exact ncard_union_eq (disjoint_left.2 fun f h1 h2 ↦ lift_not_inc_both hG hxy hM h1.1 h1.2 h2.2)
    (liftEdges_finite x) (liftEdges_finite y)

/-! ### First lift: `M` itself -/

/-- If no edge of `M` meets `y` in `G`, then `M` is a subgraph of `G`. -/
theorem lift_le (hex : G.Inc e x) (hM : IsLinkage (contract x y e G) M)
    (hb : liftEdges M G y = ∅) : M ≤ G where
  vertexSet_subset := lift_vertexSet_subset hex hM
  edgeSet_subset _ hf := (lift_edge_mem hM hf).1
  ends_eq f hf := by
    have hfy : ¬ G.Inc f y := fun h ↦ (eq_empty_iff_forall_notMem.1 hb) f ⟨hf, h⟩
    ext v
    change G.Inc f v ↔ M.Inc f v
    rw [lift_inc_iff hM hf]
    symm
    constructor
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      exacts [h, absurd h hfy]
    · intro h
      exact Or.inl ⟨h, fun hv ↦ hfy (hv ▸ h)⟩

/-! ### Second lift: `x` renamed `y` -/

section Swap

variable [DecidableEq α]

/-- `M` with `x` renamed `y`. -/
noncomputable def swapLift (x y : α) (M : Hypergraph α β) : Hypergraph α β :=
  mapHypergraph (Equiv.swap x y) id M

theorem swapLift_inc {f : β} {w : α} : (swapLift x y M).Inc f w ↔ M.Inc f (Equiv.swap x y w) := by
  constructor
  · rintro ⟨f₀, v₀, h, rfl, rfl⟩
    rwa [Equiv.swap_apply_self]
  · intro h
    exact ⟨f, _, h, rfl, Equiv.swap_apply_self _ _ _⟩

theorem mergeVertex_swap {u : α} (hu : u ≠ y) : mergeVertex x y (Equiv.swap x y u) = u := by
  by_cases hux : u = x
  · rw [hux, Equiv.swap_apply_left, mergeVertex_self]
  · rw [Equiv.swap_apply_of_ne_of_ne hux hu, mergeVertex_of_ne hu]

theorem swapLift_le (hxy : x ≠ y) (hey : G.Inc e y) (hM : IsLinkage (contract x y e G) M)
    (ha : liftEdges M G x = ∅) : swapLift x y M ≤ G where
  vertexSet_subset := by
    rintro _ ⟨v, hv, rfl⟩
    by_cases hvx : v = x
    · rw [hvx, Equiv.swap_apply_left]
      exact G.vertex_mem_of_inc hey
    · have hvy : v ≠ y := fun h ↦ lift_y_notMem hxy hM (h ▸ hv)
      rw [Equiv.swap_apply_of_ne_of_ne hvx hvy]
      rcases hM.1.vertexSet_subset hv with ⟨h, -⟩ | ⟨h, -⟩
      exacts [h, absurd h hvx]
  edgeSet_subset := by
    rintro _ ⟨f, hf, rfl⟩
    exact (lift_edge_mem hM hf).1
  ends_eq := by
    rintro _ ⟨f, hf, rfl⟩
    have hfx : ¬ G.Inc f x := fun h ↦ (eq_empty_iff_forall_notMem.1 ha) f ⟨hf, h⟩
    ext w
    change G.Inc f w ↔ (swapLift x y M).Inc f w
    rw [swapLift_inc, lift_inc_iff hM hf]
    symm
    by_cases hwx : w = x
    · rw [hwx, Equiv.swap_apply_left]
      constructor
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        exacts [absurd rfl h, absurd h hxy.symm]
      · intro h
        exact absurd h hfx
    by_cases hwy : w = y
    · rw [hwy, Equiv.swap_apply_right]
      constructor
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        exacts [absurd h hfx, h]
      · intro h
        exact Or.inr ⟨rfl, h⟩
    · rw [Equiv.swap_apply_of_ne_of_ne hwx hwy]
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩)
        exacts [h, absurd h hwx]
      · intro h
        exact Or.inl ⟨h, hwy⟩

theorem contract_swapLift (hxy : x ≠ y) (hM : IsLinkage (contract x y e G) M) :
    contract x y e (swapLift x y M) = M := by
  have hyM := lift_y_notMem hxy hM
  ext v
  · rw [contract_vertexSet_eq_image]
    change v ∈ mergeVertex x y '' (Equiv.swap x y '' M.vertexSet) ↔ v ∈ M.vertexSet
    rw [image_image, image_eq_self_of_forall fun u hu ↦
      mergeVertex_swap (x := x) fun h ↦ hyM (by rw [← h]; exact hu)]
  · change v ∈ id '' M.edgeSet \ {e} ↔ v ∈ M.edgeSet
    rw [image_id]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun h' ↦ lift_e_notMem hM ((mem_singleton_iff.1 h') ▸ h)⟩⟩
  · rename_i w
    rw [contract_inc, swapLift_inc, swapLift_inc, Equiv.swap_apply_right]
    by_cases hwx : w = x
    · rw [hwx, Equiv.swap_apply_left]
      constructor
      · rintro ⟨-, ⟨h, -⟩ | ⟨-, h⟩⟩
        exacts [absurd (M.vertex_mem_of_inc h) hyM, h]
      · intro h
        exact ⟨fun hv ↦ lift_e_notMem hM (hv ▸ M.edge_mem_of_inc h), Or.inr ⟨rfl, h⟩⟩
    by_cases hwy : w = y
    · rw [hwy]
      constructor
      · rintro ⟨-, ⟨-, h⟩ | ⟨h, -⟩⟩
        exacts [absurd rfl h, absurd h hxy.symm]
      · intro h
        exact absurd (M.vertex_mem_of_inc h) hyM
    · rw [Equiv.swap_apply_of_ne_of_ne hwx hwy]
      constructor
      · rintro ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩
        exacts [h, absurd h hwx]
      · intro h
        exact ⟨fun hv ↦ lift_e_notMem hM (hv ▸ M.edge_mem_of_inc h), Or.inl ⟨h, hwy⟩⟩

/-- **The second lift.** If no edge of `M` meets `x` in `G`, rename `x` to `y`. -/
theorem exists_swapLift (hxy : x ≠ y) (hey : G.Inc e y) (hM : IsLinkage (contract x y e G) M)
    (ha : liftEdges M G x = ∅) :
    ∃ K, IsLinkage G K ∧ image (mergeVertex x y) '' linkagePattern K = linkagePattern M ∧
      contract x y e K = M ∧ x ∉ terminals K := by
  have hyM := lift_y_notMem hxy hM
  have hMM : IsLinkage M M := ⟨le_rfl, hM.2.1, hM.2.2⟩
  have hinj : InjOn (Equiv.swap x y) M.vertexSet := (Equiv.injective _).injOn
  refine ⟨swapLift x y M, ?_, ?_, contract_swapLift hxy hM, ?_⟩
  · exact ((isLinkage_mapHypergraph le_rfl hinj (injOn_id _)).2 hMM).mono_ambient
      (swapLift_le hxy hey hM ha)
  · change image (mergeVertex x y) '' linkagePattern (mapHypergraph (Equiv.swap x y) id M) = _
    rw [linkagePattern_mapHypergraph le_rfl hinj (injOn_id _), image_image]
    refine image_eq_self_of_forall fun B hB ↦ ?_
    have hBM : B ⊆ M.vertexSet := fun u hu ↦ by
      have : u ∈ terminals M := by
        rw [hMM.terminals_eq_sUnion_linkagePattern]
        exact ⟨B, hB, hu⟩
      exact this.1
    rw [image_image]
    exact image_eq_self_of_forall fun u hu ↦
      mergeVertex_swap (x := x) fun h ↦ hyM (by rw [← h]; exact hBM hu)
  · rintro ⟨⟨v, hv, hvx⟩, -⟩
    rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at hvx
    exact hyM (hvx ▸ hv)

end Swap

/-! ### Third lift: `y` and `e` added -/

/-- `M` with `y` and `e` added. -/
def edgeLift (G M : Hypergraph α β) (y : α) (e : β) : Hypergraph α β :=
  subOn G (insert y M.vertexSet) (insert e M.edgeSet)

/-- **The third lift.** If `x ∈ V(M)`, `a ≤ 1` and `b ≤ 1`, add `y` and `e`. -/
theorem exists_edgeLift (hG : G.IsGraph) (hex : G.Inc e x) (hey : G.Inc e y) (hxy : x ≠ y)
    (hends : ∀ v, G.Inc e v → v = x ∨ v = y) (hM : IsLinkage (contract x y e G) M)
    (hxM : x ∈ M.vertexSet) (ha : (liftEdges M G x).ncard ≤ 1)
    (hb : (liftEdges M G y).ncard ≤ 1) :
    ∃ K, IsLinkage G K ∧ image (mergeVertex x y) '' linkagePattern K = linkagePattern M ∧
      contract x y e K = M ∧ (x ∈ terminals K ↔ liftEdges M G x = ∅) ∧
      (y ∈ terminals K ↔ liftEdges M G y = ∅) ∧
      (liftEdges M G x = ∅ → liftEdges M G y = ∅ → {x, y} ∈ linkagePattern K) := by
  set K := edgeLift G M y e with hKdef
  have hyM := lift_y_notMem hxy hM
  have hKG : K ≤ G := by
    refine subOn_le fun f hf _ v hv ↦ ?_
    by_cases hvy : v = y
    · exact Or.inl hvy
    right
    rcases hf with rfl | hf
    · rcases hends v hv with rfl | rfl
      exacts [hxM, absurd rfl hvy]
    · exact M.vertex_mem_of_inc ((lift_inc_iff hM hf).2 (Or.inl ⟨hv, hvy⟩))
  have hKe : e ∈ K.edgeSet := ⟨Or.inl rfl, G.edge_mem_of_inc hex⟩
  have hKex : K.Inc e x := ⟨hex, Or.inl rfl, Or.inr hxM⟩
  have hKey : K.Inc e y := ⟨hey, Or.inl rfl, Or.inl rfl⟩
  have hKends : ∀ v, K.Inc e v → v = x ∨ v = y := fun v h ↦ hends v h.1
  have hcK : contract x y e K = M := by
    ext v
    · rw [mem_contract_vertexSet]
      constructor
      · rintro (⟨⟨hv | hv, -⟩, hvy⟩ | ⟨rfl, -⟩)
        exacts [absurd hv hvy, hv, hxM]
      · intro hv
        exact Or.inl ⟨⟨Or.inr hv, lift_vertexSet_subset hex hM hv⟩, fun h ↦ hyM (h ▸ hv)⟩
    · constructor
      · rintro ⟨⟨hv | hv, -⟩, hve⟩
        exacts [absurd hv hve, hv]
      · intro hv
        exact ⟨⟨Or.inr hv, (lift_edge_mem hM hv).1⟩, (lift_edge_mem hM hv).2⟩
    · rename_i w
      rw [contract_inc]
      constructor
      · rintro ⟨hfe, ⟨⟨h, hf, -⟩, hwy⟩ | ⟨rfl, ⟨h, hf, -⟩⟩⟩
        · exact (lift_inc_iff hM (hf.resolve_left hfe)).2 (Or.inl ⟨h, hwy⟩)
        · exact (lift_inc_iff hM (hf.resolve_left hfe)).2 (Or.inr ⟨rfl, h⟩)
      · intro h
        have hf := M.edge_mem_of_inc h
        refine ⟨(lift_edge_mem hM hf).2, ?_⟩
        rcases (lift_inc_iff hM hf).1 h with ⟨h', hwy⟩ | ⟨rfl, h'⟩
        · exact Or.inl ⟨⟨h', Or.inr hf, Or.inr (M.vertex_mem_of_inc h)⟩, hwy⟩
        · exact Or.inr ⟨rfl, h', Or.inr hf, Or.inl rfl⟩
  have hKx : incidentEdges K x = insert e (liftEdges M G x) := by
    ext f
    constructor
    · rintro ⟨-, h, hf, -⟩
      rcases hf with rfl | hf
      exacts [Or.inl rfl, Or.inr ⟨hf, h⟩]
    · rintro (rfl | ⟨hf, h⟩)
      exacts [⟨hKe, hKex⟩, ⟨⟨Or.inr hf, (lift_edge_mem hM hf).1⟩, h, Or.inr hf, Or.inr hxM⟩]
  have hKy : incidentEdges K y = insert e (liftEdges M G y) := by
    ext f
    constructor
    · rintro ⟨-, h, hf, -⟩
      rcases hf with rfl | hf
      exacts [Or.inl rfl, Or.inr ⟨hf, h⟩]
    · rintro (rfl | ⟨hf, h⟩)
      exacts [⟨hKe, hKey⟩, ⟨⟨Or.inr hf, (lift_edge_mem hM hf).1⟩, h, Or.inr hf, Or.inl rfl⟩]
  have hKo : ∀ v, v ≠ x → v ≠ y → incidentEdges K v = incidentEdges M v := fun v hvx hvy ↦ by
    conv_rhs => rw [← hcK]
    exact (incidentEdges_contract_of_ne' hKends hvx hvy).symm
  have heA : ∀ w, e ∉ liftEdges M G w := fun w h ↦ lift_e_notMem hM h.1
  have hcard : ∀ w, (insert e (liftEdges M G w)).ncard = (liftEdges M G w).ncard + 1 :=
    fun w ↦ ncard_insert_of_notMem (heA w) (liftEdges_finite w)
  have hK2 : ∀ f ∈ K.edgeSet, (K.ends f).ncard = 2 := by
    intro f hf
    rw [← hKG.ends_eq f hf]
    rcases hf.1 with rfl | hfM
    · have : G.ends f = {x, y} := by
        ext v
        exact ⟨fun h ↦ hends v h, by rintro (rfl | rfl); exacts [hex, hey]⟩
      rw [this, ncard_pair hxy]
    · have h2 := hM.ends_ncard_eq_two hfM
      rw [← hM.1.ends_eq f hfM, contract_ends (lift_edge_mem hM hfM).2] at h2
      have hfin : (G.ends f).Finite :=
        G.vertexSet_finite.subset fun _ h ↦ G.vertex_mem_of_inc h
      have := ncard_image_le (f := mergeVertex x y) hfin
      have := (hG f (lift_edge_mem hM hfM).1).2
      omega
  have hdegM : ∀ v, vertexDegree M v = (incidentEdges M v).ncard :=
    hM.vertexDegree_eq_ncard_incidentEdges_of_le le_rfl
  have hdegx := lift_ncard_x hG hxy hM
  have hK : IsLinkage G K := by
    refine isLinkage_of_deg_le_two_of_reachable_deg_le_one hKG hK2 ?_ ?_
    · intro v _
      by_cases hvx : v = x
      · rw [hvx, hKx, hcard]
        omega
      by_cases hvy : v = y
      · rw [hvy, hKy, hcard]
        omega
      rw [hKo v hvx hvy]
      exact hM.ncard_incidentEdges_le_two v
    · intro v hv
      have hπv : mergeVertex x y v ∈ M.vertexSet := hcK ▸ mergeVertex_mem_contract hv
      obtain ⟨t, ht, hr⟩ := hM.exists_reachable_terminal hπv
      have hr' : (contract x y e K).skeleton.Reachable (mergeVertex x y v) t := by
        rw [hcK]
        exact hr
      have htdeg : (incidentEdges M t).ncard ≤ 1 := by
        have := ht.2
        rwa [hdegM] at this
      by_cases htx : t = x
      · rw [htx] at hr' htdeg
        rw [hdegx] at htdeg
        by_cases ha0 : liftEdges M G x = ∅
        · refine ⟨x, ⟨Or.inr hxM, G.vertex_mem_of_inc hex⟩,
            reachable_of_reachable_contract hKex hKey hr' hv rfl (mergeVertex_of_ne hxy), ?_⟩
          rw [hKx, ha0, insert_empty_eq, ncard_singleton]
        · have hpos : 0 < (liftEdges M G x).ncard :=
            (ncard_pos (liftEdges_finite x)).2 (nonempty_iff_ne_empty.2 ha0)
          have hb0 : liftEdges M G y = ∅ :=
            (ncard_eq_zero (liftEdges_finite y)).1 (by omega)
          refine ⟨y, ⟨Or.inl rfl, G.vertex_mem_of_inc hey⟩,
            reachable_of_reachable_contract hKex hKey hr' hv rfl (mergeVertex_self x y), ?_⟩
          rw [hKy, hb0, insert_empty_eq, ncard_singleton]
      · have htc : t ∈ (contract x y e K).vertexSet := by
          rw [hcK]
          exact ht.1
        obtain ⟨t', ht'K, ht't⟩ := exists_preimage_of_mem_contract htc
        have ht'y : t' ≠ y := fun h ↦ htx (by rw [← ht't, h, mergeVertex_self])
        have ht'eq : t' = t := by rw [← ht't, mergeVertex_of_ne ht'y]
        subst ht'eq
        refine ⟨t', ht'K, reachable_of_reachable_contract hKex hKey hr' hv rfl
          (mergeVertex_of_ne ht'y), ?_⟩
        rw [hKo t' htx ht'y]
        exact htdeg
  have hdegK : ∀ v, vertexDegree K v = (incidentEdges K v).ncard :=
    hK.vertexDegree_eq_ncard_incidentEdges_of_le le_rfl
  have hxK : x ∈ K.vertexSet := ⟨Or.inr hxM, G.vertex_mem_of_inc hex⟩
  have hyK : y ∈ K.vertexSet := ⟨Or.inl rfl, G.vertex_mem_of_inc hey⟩
  have hTx : x ∈ terminals K ↔ liftEdges M G x = ∅ := by
    change (x ∈ K.vertexSet ∧ vertexDegree K x ≤ 1) ↔ _
    rw [hdegK, hKx, hcard, ← ncard_eq_zero (liftEdges_finite x)]
    exact ⟨fun h ↦ by omega, fun h ↦ ⟨hxK, by omega⟩⟩
  have hTy : y ∈ terminals K ↔ liftEdges M G y = ∅ := by
    change (y ∈ K.vertexSet ∧ vertexDegree K y ≤ 1) ↔ _
    rw [hdegK, hKy, hcard, ← ncard_eq_zero (liftEdges_finite y)]
    exact ⟨fun h ↦ by omega, fun h ↦ ⟨hyK, by omega⟩⟩
  refine ⟨K, hK, ?_, hcK, hTx, hTy, fun ha0 hb0 ↦ ?_⟩
  · rw [← linkagePattern_contract hK hKe hKex hKey hxy hKG, hcK]
  · exact (hK.pair_mem_linkagePattern_iff (hTx.2 ha0) (hTy.2 hb0) hxy).2
      (SimpleGraph.Adj.reachable ⟨hxy, e, hKex, hKey⟩)

/-! ### Choosing the lift -/

/-- **Lifting a linkage of `G / e`.** Let `L` be a linkage of `G` whose pattern is sent to the
pattern of a linkage `M` of `G / e`, and suppose that `{x, y}` is a block of `L` when both `x` and
`y` are terminals of `L`. Then `M = K / e` for some linkage `K` of `G` with the pattern of `L`. -/
theorem exists_lift (hG : G.IsGraph) (hex : G.Inc e x) (hey : G.Inc e y) (hxy : x ≠ y)
    (hends : ∀ v, G.Inc e v → v = x ∨ v = y) {L : Hypergraph α β} (hL : IsLinkage G L)
    (hC : x ∈ terminals L → y ∈ terminals L → {x, y} ∈ linkagePattern L)
    (hM : IsLinkage (contract x y e G) M)
    (hpat : linkagePattern M = image (mergeVertex x y) '' linkagePattern L) :
    ∃ K, IsLinkage G K ∧ linkagePattern K = linkagePattern L ∧ contract x y e K = M := by
  suffices h : ∃ K, IsLinkage G K ∧
      image (mergeVertex x y) '' linkagePattern K = linkagePattern M ∧ contract x y e K = M ∧
      ((y ∉ terminals K ∧ y ∉ terminals L) ∨ (x ∉ terminals K ∧ x ∉ terminals L) ∨
        ({x, y} ∈ linkagePattern K ∧ {x, y} ∈ linkagePattern L)) by
    obtain ⟨K, hK, hKp, hKc, hc⟩ := h
    exact ⟨K, hK, linkagePattern_eq_of_image_eq hxy hK hL (hKp.trans hpat) hc, hKc⟩
  have hT : terminals M = mergeVertex x y '' terminals L := by
    rw [hM.terminals_eq_sUnion_linkagePattern, hL.terminals_eq_sUnion_linkagePattern, hpat,
      image_sUnion]
  classical
  have hxT : x ∈ terminals M ↔ x ∈ terminals L ∨ y ∈ terminals L := by
    rw [hT, mem_image_mergeVertex_iff]
    constructor
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      exacts [Or.inl h, Or.inr h]
    · rintro (h | h)
      exacts [Or.inl ⟨h, hxy⟩, Or.inr ⟨rfl, h⟩]
  have hdeg := lift_ncard_x hG hxy hM
  have hdeg2 := hM.ncard_incidentEdges_le_two x
  rw [hdeg] at hdeg2
  have hTx : x ∈ terminals M →
      (liftEdges M G x).ncard + (liftEdges M G y).ncard ≤ 1 := fun h ↦ by
    have := h.2
    rwa [hM.vertexDegree_eq_ncard_incidentEdges_of_le le_rfl, hdeg] at this
  have hpair : x ∈ terminals L → y ∈ terminals L →
      (liftEdges M G x).ncard + (liftEdges M G y).ncard = 0 := fun hx hy ↦ by
    have h1 : {x} ∈ linkagePattern M := by
      rw [hpat]
      exact ⟨{x, y}, hC hx hy, image_mergeVertex_pair hxy⟩
    have hxM : x ∈ M.vertexSet := (hxT.2 (Or.inl hx)).1
    rw [← hdeg]
    exact (hM.ncard_incidentEdges_eq_zero_iff hxM).2 h1
  have hxV : 0 < (liftEdges M G x).ncard + (liftEdges M G y).ncard → x ∈ M.vertexSet :=
    fun h ↦ by
      rw [← hdeg] at h
      obtain ⟨f, -, hf⟩ := nonempty_of_ncard_ne_zero h.ne'
      exact M.vertex_mem_of_inc hf
  have hz : ∀ w, (liftEdges M G w).ncard = 0 ↔ liftEdges M G w = ∅ :=
    fun w ↦ ncard_eq_zero (liftEdges_finite w)
  rcases Nat.eq_zero_or_pos (liftEdges M G y).ncard with hb | hb
  · by_cases hyL : y ∈ terminals L
    · have hxTM : x ∈ terminals M := hxT.2 (Or.inr hyL)
      have hab := hTx hxTM
      by_cases hxL : x ∈ terminals L
      · have h0 := hpair hxL hyL
        obtain ⟨K, hK, hKp, hKc, -, -, hKxy⟩ :=
          exists_edgeLift hG hex hey hxy hends hM hxTM.1 (by omega) (by omega)
        exact ⟨K, hK, hKp, hKc, Or.inr (Or.inr
          ⟨hKxy ((hz x).1 (by omega)) ((hz y).1 (by omega)), hC hxL hyL⟩)⟩
      · rcases Nat.eq_zero_or_pos (liftEdges M G x).ncard with ha | ha
        · obtain ⟨K, hK, hKp, hKc, hKx⟩ := exists_swapLift hxy hey hM ((hz x).1 ha)
          exact ⟨K, hK, hKp, hKc, Or.inr (Or.inl ⟨hKx, hxL⟩)⟩
        · obtain ⟨K, hK, hKp, hKc, hKx, -, -⟩ :=
            exists_edgeLift hG hex hey hxy hends hM hxTM.1 (by omega) (by omega)
          refine ⟨K, hK, hKp, hKc, Or.inr (Or.inl ⟨fun h ↦ ?_, hxL⟩)⟩
          have := (hz x).2 (hKx.1 h)
          omega
    · have hMG := lift_le hex hM ((hz y).1 hb)
      refine ⟨M, hM.mono_ambient hMG, ?_, contract_eq_self (lift_y_notMem hxy hM)
        (lift_e_notMem hM), Or.inl ⟨fun h ↦ lift_y_notMem hxy hM h.1, hyL⟩⟩
      refine image_eq_self_of_forall fun B hB ↦ image_mergeVertex_of_notMem fun hy ↦ ?_
      have : y ∈ terminals M := by
        rw [hM.terminals_eq_sUnion_linkagePattern]
        exact ⟨B, hB, hy⟩
      exact lift_y_notMem hxy hM this.1
  · rcases Nat.eq_zero_or_pos (liftEdges M G x).ncard with ha | ha
    · by_cases hY : (liftEdges M G y).ncard = 2 ∨ (x ∉ terminals L ∧ y ∈ terminals L)
      · obtain ⟨K, hK, hKp, hKc, hKx⟩ := exists_swapLift hxy hey hM ((hz x).1 ha)
        refine ⟨K, hK, hKp, hKc, Or.inr (Or.inl ⟨hKx, ?_⟩)⟩
        rcases hY with h2 | ⟨h, -⟩
        · intro hxL
          have := hTx (hxT.2 (Or.inl hxL))
          omega
        · exact h
      · have hb2 : (liftEdges M G y).ncard ≠ 2 := fun h ↦ hY (Or.inl h)
        obtain ⟨K, hK, hKp, hKc, -, hKy, -⟩ :=
          exists_edgeLift hG hex hey hxy hends hM (hxV (by omega)) (by omega) (by omega)
        refine ⟨K, hK, hKp, hKc, Or.inl ⟨fun h ↦ ?_, fun hyL ↦ ?_⟩⟩
        · have := (hz y).2 (hKy.1 h)
          omega
        · by_cases hxL : x ∈ terminals L
          · have := hpair hxL hyL
            omega
          · exact hY (Or.inr ⟨hxL, hyL⟩)
    · obtain ⟨K, hK, hKp, hKc, -, hKy, -⟩ :=
        exists_edgeLift hG hex hey hxy hends hM (hxV (by omega)) (by omega) (by omega)
      refine ⟨K, hK, hKp, hKc, Or.inl ⟨fun h ↦ ?_, fun hyL ↦ ?_⟩⟩
      · have := (hz y).2 (hKy.1 h)
        omega
      · have := hTx (hxT.2 (Or.inr hyL))
        omega

end Lift

end GM21
end GraphMinor
