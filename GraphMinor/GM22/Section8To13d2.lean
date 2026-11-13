module

public import GraphMinor.GM22.Section8To13d1
public import GraphMinor.GM22.Section8To13c4

/-!
# Vision Boundary Numberings, Attachment Paths, and Homogeneity (`hyp_vii`, `hyp_viii`, `hyp_xi`, `hyp_xiii`)

This file completes the verification of the remaining hypotheses of Graph Minors XXII,
Theorem (8.3) (`Hypotheses83InGraph`) from Hypothesis C, a vision `vis`, and an `h`-homogeneous
subwall `H'` of `H` (Graph Minors XXII, page 563):
- `tildeA_hyp_vii`: boundary ordering `πA` of `Z ∩ V(tA) = divBoundary S_H A` with `πLen tA ≤ 3`.
- `tildeA_hyp_viii`: `πLen tA` pairwise vertex-disjoint paths in `J \ X = S_H.G` from `πA tA` to
  the four corners `PiSet`, preserving clockwise order on the sphere when `πLen tA = 3`.
- `tildeA_hyp_xi`: representative vertex `vA tA ∈ Γ.drawing.V` and path in `G \ X` from `vA tA` to
  `Z ∩ V(tA)` meeting `V(H.graph)` only at `vA tA`.
- `tildeA_hyp_xiii`: homogeneity outside the closed disc `D_disc` of the subwall `H'`.
-/

@[expose] public section

namespace GraphMinor
namespace GM22

open Set Function Topology Graph Hypergraph
open GraphMinor.Surface
open GraphMinor.GM09
open GraphMinor.GM11
open GraphMinor.GM13
open GraphMinor.GM14

universe u v

/-! ## 1. List Ordering and Vision Root Sequence Helpers -/

/-- If `L : List α` has no duplicates and `{x | x ∈ L} = S`, then `fun i : Fin L.length => L[i.1]`
is an ordering of `S`, and `S.ncard = L.length`. -/
theorem isOrderingOf_list_get {α : Type u} {L : List α} {S : Set α}
    (hnodup : L.Nodup) (hset : {x : α | x ∈ L} = S) :
    IsOrderingOf S (fun i : Fin L.length => L[i.1]) ∧ S.ncard = L.length := by
  have hinj : Function.Injective (fun i : Fin L.length => L[i.1]) := by
    intro i j hij
    exact (List.nodup_iff_injective_get.mp hnodup) hij
  have hrange : Set.range (fun i : Fin L.length => L[i.1]) = S := by
    rw [← hset]
    ext x
    simp only [mem_range, mem_ofPred_eq, List.mem_iff_get]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, hi⟩⟩
  have hcard : S.ncard = L.length := by
    rw [← hrange, ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact ⟨⟨hinj, hrange⟩, hcard⟩

/-- Under `HypothesisC G q X H S_H 𝒜` and `vis : Vision G X H S_H 𝒜`, `vis.xSeq.length = q`. -/
theorem vision_xSeq_length_eq {α : Type u} {β : Type v}
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) (vis : Vision G X H S_H 𝒜) :
    vis.xSeq.length = q := by
  have h := (isOrderingOf_list_get vis.xSeq_nodup vis.xSeq_set).2
  exact h.symm.trans hc.X_ncard

/-- The ordering `ω : Fin q → α` of `X` induced by `vis.xSeq`. -/
def visionXOrdering {α : Type u} {β : Type v}
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) (vis : Vision G X H S_H 𝒜) : Fin q → α :=
  fun i => vis.xSeq[i.1]'(by have := vision_xSeq_length_eq hc vis; omega)

theorem isOrderingOf_visionXOrdering {α : Type u} {β : Type v}
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) (vis : Vision G X H S_H 𝒜) :
    IsOrderingOf X (visionXOrdering hc vis) := by
  obtain ⟨⟨hinj, hrange⟩, _⟩ := isOrderingOf_list_get vis.xSeq_nodup vis.xSeq_set
  have hlen : vis.xSeq.length = q := vision_xSeq_length_eq hc vis
  refine ⟨?_, ?_⟩
  · intro i j hij
    have h1 := @hinj ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ hij
    exact Fin.ext (Fin.mk.inj h1)
  · refine Eq.trans ?_ hrange
    ext x
    simp only [mem_range, visionXOrdering]
    exact ⟨fun ⟨i, hi⟩ => ⟨⟨i.1, by omega⟩, hi⟩, fun ⟨i, hi⟩ => ⟨⟨i.1, by omega⟩, hi⟩⟩

theorem visionXOrdering_mem_vertexSet {α : Type u} {β : Type v}
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) (vis : Vision G X H S_H 𝒜) (i : Fin q) :
    visionXOrdering hc vis i ∈ G.vertexSet := by
  apply hc.X_subset
  exact (Set.ext_iff.mp (isOrderingOf_visionXOrdering hc vis).2 _).mp (mem_range_self i)

/-- The rooted digraph `R_G : GM22.RootedDigraph α β q` associated with `(G, vis.xSeq)`. -/
def visionRootedDigraph {α : Type u} {β : Type v}
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) (vis : Vision G X H S_H 𝒜) :
    GM22.RootedDigraph α β q :=
  toGM22RootedDigraph ⟨G, visionXOrdering hc vis, visionXOrdering_mem_vertexSet hc vis⟩

/-! ## 2. Boundary Numberings and Disjoint Paths to Corners (`hyp_vii`, `hyp_viii`) -/

/-- Any three pairwise distinct corners `x, y, z ∈ W.corners` satisfy either
`(wallCornerCyclicPerm W).IsClockwise3 x y z` or `(wallCornerCyclicPerm W).IsClockwise3 x z y`. -/
theorem wallCornerCyclicPerm_isClockwise3_or_swap {α : Type u} {β : Type v} (W : Wall α β)
    {x y z : α} (hx : x ∈ W.corners) (hy : y ∈ W.corners) (hz : z ∈ W.corners)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (wallCornerCyclicPerm W).IsClockwise3 x y z ∨
    (wallCornerCyclicPerm W).IsClockwise3 x z y := by
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  obtain ⟨k, rfl⟩ := hz
  have hij : i ≠ j := fun h => hxy (congrArg W.corner h)
  have hik : i ≠ k := fun h => hxz (congrArg W.corner h)
  have hjk : j ≠ k := fun h => hyz (congrArg W.corner h)
  rw [wallCornerCyclicPerm_isClockwise3_iff, wallCornerCyclicPerm_isClockwise3_iff]
  omega

/-- For any member `A ∈ 𝒜`, `divBoundary S_H A` is finite. -/
theorem finite_divBoundary {α : Type u} {β : Type v}
    {S_H : Society α β} (A : Graph α β) :
    (divBoundary S_H A).Finite := by
  refine S_H.finite_V.subset ?_
  rintro x ⟨_, hxbar | ⟨e, he, hinc⟩⟩
  · exact S_H.bar_subset hxbar
  · obtain ⟨y, hl⟩ := hinc
    exact hl.left_mem

/-- For any `A ∈ 𝒜`, there exist an ordering `s : Fin (divBoundary S_H A).ncard → α` of
`divBoundary S_H A`, corner targets `t : Fin (divBoundary S_H A).ncard → α`, and pairwise
vertex-disjoint paths `P : Fin (divBoundary S_H A).ncard → Graph α β` in `S_H.G` from `s i` to
`t i ∈ S_H.Ω.bar` such that when `(divBoundary S_H A).ncard = 3`,
`S_H.Ω.IsClockwise3 (t 0) (t 1) (t 2)` holds. -/
theorem exists_ordered_boundary_paths {α : Type u} {β : Type v}
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) {A : Graph α β} (hA : A ∈ 𝒜) :
    let k := (divBoundary S_H A).ncard
    ∃ (s t : Fin k → α) (P : Fin k → Graph α β),
      IsOrderingOf (divBoundary S_H A) s ∧
      Pairwise (fun i j => Disjoint V(P i) V(P j)) ∧
      (∀ i : Fin k, t i ∈ S_H.Ω.bar ∧ IsGraphPathWithEnds S_H.G (P i) (s i) (t i)) ∧
      (∀ h3 : k = 3,
        S_H.Ω.IsClockwise3 (t ⟨0, by omega⟩) (t ⟨1, by omega⟩) (t ⟨2, by omega⟩)) := by
  intro k
  obtain ⟨P₀, hdisj₀, hex₀⟩ := hc.isRuralDivision.isDivision.disjoint_paths_to_bar hA
  choose s₀ hs₀ t₀ ht₀ hP₀ using hex₀
  have hs₀_inj : Function.Injective s₀ := by
    intro i j hij
    by_contra hne
    exact Set.disjoint_left.mp (hdisj₀ hne) (hP₀ i).left_mem (hij ▸ (hP₀ j).left_mem)
  have ht₀_inj : Function.Injective t₀ := by
    intro i j hij
    by_contra hne
    exact Set.disjoint_left.mp (hdisj₀ hne) (hP₀ i).right_mem (hij ▸ (hP₀ j).right_mem)
  have hs₀_range : Set.range s₀ = divBoundary S_H A := by
    have hsub : Set.range s₀ ⊆ divBoundary S_H A := by
      rintro _ ⟨i, rfl⟩; exact hs₀ i
    have hcard : (divBoundary S_H A).ncard ≤ (Set.range s₀).ncard := by
      rw [ncard_range_of_injective hs₀_inj, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact Set.eq_of_subset_of_ncard_le hsub hcard (finite_divBoundary A)
  open Classical in
  let σ : Equiv.Perm (Fin k) :=
    if hk : k = 3 then
      if S_H.Ω.IsClockwise3 (t₀ ⟨0, by omega⟩) (t₀ ⟨1, by omega⟩) (t₀ ⟨2, by omega⟩) then
        Equiv.refl (Fin k)
      else
        Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩
    else
      Equiv.refl (Fin k)
  refine ⟨s₀ ∘ σ, t₀ ∘ σ, P₀ ∘ σ, ⟨hs₀_inj.comp σ.injective, ?_⟩, ?_, ?_, ?_⟩
  · rw [Set.range_comp, σ.surjective.range_eq, Set.image_univ, hs₀_range]
  · intro i j hij
    exact hdisj₀ (σ.injective.ne hij)
  · intro i
    exact ⟨ht₀ (σ i), hP₀ (σ i)⟩
  · intro hk
    dsimp only [σ, Function.comp_apply]
    split_ifs with hcw
    · exact hcw
    · have hswap0 : (Equiv.swap (⟨1, by omega⟩ : Fin k) ⟨2, by omega⟩) ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
        rw [Equiv.swap_apply_of_ne_of_ne] <;> intro h <;> exact absurd (congrArg Fin.val h) (by dsimp; omega)
      have hswap1 : (Equiv.swap (⟨1, by omega⟩ : Fin k) ⟨2, by omega⟩) ⟨1, by omega⟩ = ⟨2, by omega⟩ :=
        Equiv.swap_apply_left _ _
      have hswap2 : (Equiv.swap (⟨1, by omega⟩ : Fin k) ⟨2, by omega⟩) ⟨2, by omega⟩ = ⟨1, by omega⟩ :=
        Equiv.swap_apply_right _ _
      rw [hswap0, hswap1, hswap2]
      have hbar_eq : S_H.Ω = wallCornerCyclicPerm H := hc.isWallSociety.2
      have hbar_set : S_H.Ω.bar = H.corners := by rw [hbar_eq]; rfl
      rw [hbar_eq] at hcw ⊢
      have ht0_mem : t₀ ⟨0, by omega⟩ ∈ H.corners := hbar_set ▸ ht₀ ⟨0, by omega⟩
      have ht1_mem : t₀ ⟨1, by omega⟩ ∈ H.corners := hbar_set ▸ ht₀ ⟨1, by omega⟩
      have ht2_mem : t₀ ⟨2, by omega⟩ ∈ H.corners := hbar_set ▸ ht₀ ⟨2, by omega⟩
      have h01 : t₀ ⟨0, by omega⟩ ≠ t₀ ⟨1, by omega⟩ :=
        ht₀_inj.ne (fun h => absurd (congrArg Fin.val h) (by dsimp; omega))
      have h02 : t₀ ⟨0, by omega⟩ ≠ t₀ ⟨2, by omega⟩ :=
        ht₀_inj.ne (fun h => absurd (congrArg Fin.val h) (by dsimp; omega))
      have h12 : t₀ ⟨1, by omega⟩ ≠ t₀ ⟨2, by omega⟩ :=
        ht₀_inj.ne (fun h => absurd (congrArg Fin.val h) (by dsimp; omega))
      exact (wallCornerCyclicPerm_isClockwise3_or_swap H ht0_mem ht1_mem ht2_mem h01 h02 h12).resolve_left hcw

/-- The boundary sequence length `πLen tA` for `tA : Graph α β`:
`(vis.sSeq (tA.deleteVerts X)).length` when `tA.deleteVerts X` is an interior member of `𝒜`, and
`(divBoundary S_H (tA.deleteVerts X)).ncard` otherwise. -/
noncomputable def tildeA_πLen {α : Type u} {β : Type v}
    {G : GM13.Digraph α β} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (vis : Vision G X H S_H 𝒜) (tA : Graph α β) : ℕ :=
  open Classical in
  if IsInteriorMember H 𝒜 (tA.deleteVerts X) then
    (vis.sSeq (tA.deleteVerts X)).length
  else
    (divBoundary S_H (tA.deleteVerts X)).ncard

theorem tildeA_πLen_pos {α : Type u} {β : Type v}
    {G : GM13.Digraph α β} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (vis : Vision G X H S_H 𝒜) {tA : Graph α β}
    (h_int : IsInteriorMember H 𝒜 (tA.deleteVerts X)) :
    tildeA_πLen vis tA = (vis.sSeq (tA.deleteVerts X)).length := by
  unfold tildeA_πLen; split_ifs; rfl

theorem tildeA_πLen_neg {α : Type u} {β : Type v}
    {G : GM13.Digraph α β} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (vis : Vision G X H S_H 𝒜) {tA : Graph α β}
    (h_int : ¬ IsInteriorMember H 𝒜 (tA.deleteVerts X)) :
    tildeA_πLen vis tA = (divBoundary S_H (tA.deleteVerts X)).ncard := by
  unfold tildeA_πLen; split_ifs; rfl

/-- The boundary ordering `πA tA : Fin (tildeA_πLen vis tA) → α` for `tA : Graph α β`. -/
noncomputable def tildeA_πA {α : Type u} {β : Type v} [Nonempty α]
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) (vis : Vision G X H S_H 𝒜)
    (tA : Graph α β) : Fin (tildeA_πLen vis tA) → α :=
  open Classical in
  if h_int : IsInteriorMember H 𝒜 (tA.deleteVerts X) then
    fun i => (vis.sSeq (tA.deleteVerts X))[i.1]'(by
      have := tildeA_πLen_pos vis h_int
      omega)
  else if hA : tA.deleteVerts X ∈ 𝒜 then
    fun i => (exists_ordered_boundary_paths hc hA).choose
      (i.cast (tildeA_πLen_neg vis h_int))
  else
    fun _ => Classical.arbitrary α

/-- Under `HypothesisC G q X H S_H 𝒜` and `vis : Vision G X H S_H 𝒜`, Hypothesis (vii) of
Theorem (8.3) holds for `tildeA_πLen vis` and `tildeA_πA hc vis`. -/
theorem tildeA_hyp_vii {α : Type u} {β : Type v} [Nonempty α]
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) (vis : Vision G X H S_H 𝒜) :
    let Z := divTotalBoundary S_H 𝒜
    let 𝒜_83 := (fun A => (vis.tildeA A).toGraph) '' 𝒜
    ∀ tA ∈ 𝒜_83, tildeA_πLen vis tA ≤ 3 ∧ IsOrderingOf (Z ∩ V(tA)) (tildeA_πA hc vis tA) := by
  rintro Z 𝒜_83 _ ⟨A, hA, rfl⟩
  let tA := (vis.tildeA A).toGraph
  change tildeA_πLen vis tA ≤ 3 ∧ IsOrderingOf (Z ∩ V(tA)) (tildeA_πA hc vis tA)
  obtain ⟨_, hdel_eq, _, hZA⟩ := tildeA_properties hc vis hA
  have hle3 : (divBoundary S_H A).ncard ≤ 3 :=
    hc.isRuralDivision.isDivision.boundary_ncard_le_three hA
  rw [hZA]
  by_cases h_int : IsInteriorMember H 𝒜 (tA.deleteVerts X)
  · have h_int_A : IsInteriorMember H 𝒜 A := hdel_eq ▸ h_int
    obtain ⟨hnodup, hset, _⟩ := vis.sSeq_valid h_int_A
    obtain ⟨hord_A, hcard_A⟩ := isOrderingOf_list_get hnodup hset
    have hlen_eq : tildeA_πLen vis tA = (vis.sSeq A).length := by
      rw [tildeA_πLen_pos vis h_int, hdel_eq]
    refine ⟨by omega, ?_⟩
    have hπA_eq : ∀ i : Fin (tildeA_πLen vis tA),
        tildeA_πA hc vis tA i = (vis.sSeq A)[i.1]'(by omega) := by
      intro i
      unfold tildeA_πA
      split_ifs
      dsimp only
      congr 1; rw [hdel_eq]
    refine ⟨?_, ?_⟩
    · intro i j hij
      rw [hπA_eq i, hπA_eq j] at hij
      have h1 := @hord_A.1 ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ hij
      exact Fin.ext (Fin.mk.inj h1)
    · ext x
      rw [← hord_A.2]
      simp only [mem_range]
      exact ⟨fun ⟨i, hi⟩ => ⟨⟨i.1, by omega⟩, by rw [← hi, hπA_eq i]⟩,
        fun ⟨i, hi⟩ => ⟨⟨i.1, by omega⟩, by rw [hπA_eq ⟨i.1, by omega⟩, ← hi]⟩⟩
  · have hA' : tA.deleteVerts X ∈ 𝒜 := hdel_eq.symm ▸ hA
    have hlen_eq : tildeA_πLen vis tA = (divBoundary S_H A).ncard := by
      rw [tildeA_πLen_neg vis h_int, hdel_eq]
    refine ⟨by omega, ?_⟩
    have hord₀ := (exists_ordered_boundary_paths hc hA').choose_spec.choose_spec.choose_spec.1
    have hπA_eq : tildeA_πA hc vis tA =
        fun i => (exists_ordered_boundary_paths hc hA').choose (i.cast (tildeA_πLen_neg vis h_int)) := by
      unfold tildeA_πA
      split_ifs
      rfl
    rw [← hdel_eq, hπA_eq]
    refine ⟨?_, ?_⟩
    · intro i j hij
      exact (Fin.castOrderIso (tildeA_πLen_neg vis h_int)).injective (hord₀.1 hij)
    · refine Eq.trans ?_ hord₀.2
      ext x
      simp only [mem_range]
      exact ⟨fun ⟨i, hi⟩ => ⟨i.cast (tildeA_πLen_neg vis h_int), hi⟩,
        fun ⟨i, hi⟩ => ⟨i.cast (tildeA_πLen_neg vis h_int).symm, by simpa using hi⟩⟩

/-- Under `HypothesisC G q X H S_H 𝒜` and `vis : Vision G X H S_H 𝒜`, Hypothesis (viii) of
Theorem (8.3) holds for `tildeA_πLen vis` and `tildeA_πA hc vis`. -/
theorem tildeA_hyp_viii {α : Type u} {β : Type v} [Nonempty α]
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) (vis : Vision G X H S_H 𝒜)
    {W : DrawnWall α β} (hW_toWall : W.toWall = H)
    {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    {C₀ : Drawing (OnePoint EuclideanPlane)}
    (hinj : InjOn pos V(W.graph))
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hmem_V : ∀ v ∈ V(W.graph), fig1Sph φ (pos v) ∈ C₀.V ↔ v ∈ V(W.perimeter))
    {orient : GM19.SurfaceOrientation (OnePoint EuclideanPlane)}
    (horient : ∀ i j k : Fin 4,
      (wallCornerCyclicPerm W.toWall).IsClockwise3
        (W.toWall.corner i) (W.toWall.corner j) (W.toWall.corner k) →
      orient.pos (Set.univ \ interior (closure (fig1Sph φ '' fig1EnclosedSet W.height)ᶜ))
        (fig1Sph φ (pos (W.toWall.corner i)))
        (fig1Sph φ (pos (W.toWall.corner j)))
        (fig1Sph φ (pos (W.toWall.corner k)))) :
    let J := G.toGraph.induce (X ∪ V(S_H.G))
    let r₀ := interior (closure (fig1Sph φ '' fig1EnclosedSet W.height)ᶜ)
    let PiSet := wallPiSet H φ pos
    let 𝒜_83 := (fun A => (vis.tildeA A).toGraph) '' 𝒜
    ∀ tA ∈ 𝒜_83,
      ∃ (P : Fin (tildeA_πLen vis tA) → Graph α β)
        (t : Fin (tildeA_πLen vis tA) → OnePoint EuclideanPlane),
        (∀ i : Fin (tildeA_πLen vis tA), t i ∈ PiSet ∧
          IsGraphPathWithEnds (J.deleteVerts X) (P i) (tildeA_πA hc vis tA i)
            (drawingVertToGraph Γ (t i))) ∧
        Pairwise (fun i j : Fin (tildeA_πLen vis tA) => Disjoint V(P i) V(P j)) ∧
        (∀ h3 : tildeA_πLen vis tA = 3,
          orient.pos (Set.univ \ r₀) (t ⟨0, by omega⟩) (t ⟨1, by omega⟩) (t ⟨2, by omega⟩)) := by
  subst hW_toWall
  intro J r₀ PiSet 𝒜_83
  obtain ⟨_, _, hdraw_corner, _⟩ := wallPiSet_props hinj hΓv hmem_V
  have hJ_del : J.deleteVerts X = S_H.G := by
    have hGX : (G.deleteVertices X).toGraph = G.toGraph.deleteVerts X :=
      gm13_deleteVertices_toGraph_eq G X
    have hH_GX : W.toWall.graph ≤ G.toGraph.deleteVerts X := hGX ▸ hc.wall_in
    have hSH_G : S_H.G = wallCompass (G.toGraph.deleteVerts X) W.toWall :=
      hc.isWallSociety.1.trans (by rw [hGX])
    have hV_SH : V(S_H.G) = wallCompassVerts (G.toGraph.deleteVerts X) W.toWall := by
      rw [hSH_G]; exact vertexSet_wallCompass hH_GX
    have hSH_sub : V(S_H.G) ⊆ V(G.toGraph.deleteVerts X) := by
      rw [hV_SH]; exact wallCompassVerts_subset_vertexSet hH_GX
    have hSH_disj_X : Disjoint V(S_H.G) X := by
      rw [Set.disjoint_left]
      intro v hv hvX
      exact (G.toGraph.vertexSet_deleteVerts X ▸ hSH_sub hv).2 hvX
    rw [hSH_G, wallCompass, ← hV_SH]
    refine Graph.ext ?_ fun e x y => ?_
    · rw [Graph.vertexSet_deleteVerts]
      change (X ∪ V(S_H.G)) \ X = V(S_H.G)
      ext v
      simp only [mem_sdiff, mem_union]
      exact ⟨fun ⟨h, hvX⟩ => h.resolve_left hvX,
        fun hv => ⟨Or.inr hv, Set.disjoint_left.mp hSH_disj_X hv⟩⟩
    · simp only [J, Graph.deleteVerts_isLink, Graph.induce_isLink, mem_union]
      exact ⟨fun ⟨⟨hl, hx, hy⟩, hxX, hyX⟩ => ⟨⟨hl, hxX, hyX⟩, hx.resolve_left hxX, hy.resolve_left hyX⟩,
        fun ⟨⟨hl, hxX, hyX⟩, hxS, hyS⟩ => ⟨⟨hl, Or.inr hxS, Or.inr hyS⟩, hxX, hyX⟩⟩
  have hbar_eq : S_H.Ω = wallCornerCyclicPerm W.toWall := hc.isWallSociety.2
  have hbar_set : S_H.Ω.bar = W.toWall.corners := by rw [hbar_eq]; rfl
  -- First show that for any `tA ∈ 𝒜_83`, there exist paths in `S_H.G` to `t_g : Fin (tildeA_πLen vis tA) → α` in `S_H.Ω.bar`
  have hex_graph : ∀ tA ∈ 𝒜_83,
      ∃ (P : Fin (tildeA_πLen vis tA) → Graph α β) (t_g : Fin (tildeA_πLen vis tA) → α),
        (∀ i : Fin (tildeA_πLen vis tA), t_g i ∈ S_H.Ω.bar ∧
          IsGraphPathWithEnds S_H.G (P i) (tildeA_πA hc vis tA i) (t_g i)) ∧
        Pairwise (fun i j : Fin (tildeA_πLen vis tA) => Disjoint V(P i) V(P j)) ∧
        (∀ h3 : tildeA_πLen vis tA = 3,
          S_H.Ω.IsClockwise3 (t_g ⟨0, by omega⟩) (t_g ⟨1, by omega⟩) (t_g ⟨2, by omega⟩)) := by
    rintro _ ⟨A, hA, rfl⟩
    let tA := (vis.tildeA A).toGraph
    obtain ⟨_, hdel_eq, _, _⟩ := tildeA_properties hc vis hA
    by_cases h_int : IsInteriorMember W.toWall 𝒜 (tA.deleteVerts X)
    · have h_int_A : IsInteriorMember W.toWall 𝒜 A := hdel_eq ▸ h_int
      have hlen_eq : tildeA_πLen vis tA = (vis.sSeq A).length := by
        rw [tildeA_πLen_pos vis h_int, hdel_eq]
      have hπA_eq : ∀ i : Fin (tildeA_πLen vis tA),
          tildeA_πA hc vis tA i = (vis.sSeq A)[i.1]'(by omega) := by
        intro i; unfold tildeA_πA; split_ifs; dsimp only; congr 1; rw [hdel_eq]
      by_cases h3 : tildeA_πLen vis tA = 3
      · have hs_len : (vis.sSeq A).length = 3 := hlen_eq.symm.trans h3
        let s₁ := tildeA_πA hc vis tA ⟨0, by omega⟩
        let s₂ := tildeA_πA hc vis tA ⟨1, by omega⟩
        let s₃ := tildeA_πA hc vis tA ⟨2, by omega⟩
        have hsSeq_eq : vis.sSeq A = [s₁, s₂, s₃] := by
          rcases hs_list : vis.sSeq A with _ | ⟨x₁, _ | ⟨x₂, _ | ⟨x₃, _ | _⟩⟩⟩
          · simp [hs_list] at hs_len
          · simp [hs_list] at hs_len
          · simp [hs_list] at hs_len
          · dsimp [s₁, s₂, s₃]
            rw [hπA_eq ⟨0, by omega⟩, hπA_eq ⟨1, by omega⟩, hπA_eq ⟨2, by omega⟩]
            simp [hs_list]
          · simp [hs_list] at hs_len
        obtain ⟨P₁, P₂, P₃, t₁, t₂, t₃, hd12, hd13, hd23,
          hP1, _, ht1_inter, hP2, _, ht2_inter, hP3, _, ht3_inter, hcw⟩ :=
          (vis.sSeq_valid h_int_A).2.2 s₁ s₂ s₃ hsSeq_eq
        have ht1_bar : t₁ ∈ S_H.Ω.bar := by
          have : t₁ ∈ V(P₁) ∩ S_H.Ω.bar := ht1_inter.symm ▸ mem_singleton t₁
          exact this.2
        have ht2_bar : t₂ ∈ S_H.Ω.bar := by
          have : t₂ ∈ V(P₂) ∩ S_H.Ω.bar := ht2_inter.symm ▸ mem_singleton t₂
          exact this.2
        have ht3_bar : t₃ ∈ S_H.Ω.bar := by
          have : t₃ ∈ V(P₃) ∩ S_H.Ω.bar := ht3_inter.symm ▸ mem_singleton t₃
          exact this.2
        let P : Fin (tildeA_πLen vis tA) → Graph α β := fun i =>
          if i.1 = 0 then P₁ else if i.1 = 1 then P₂ else P₃
        let t_g : Fin (tildeA_πLen vis tA) → α := fun i =>
          if i.1 = 0 then t₁ else if i.1 = 1 then t₂ else t₃
        refine ⟨P, t_g, ?_, ?_, ?_⟩
        · intro ⟨i, hi⟩
          have hi3 : i < 3 := h3 ▸ hi
          interval_cases i
          · exact ⟨ht1_bar, hP1⟩
          · exact ⟨ht2_bar, hP2⟩
          · exact ⟨ht3_bar, hP3⟩
        · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
          have hi3 : i < 3 := h3 ▸ hi
          have hj3 : j < 3 := h3 ▸ hj
          have hne_val : i ≠ j := fun h => hij (Fin.ext h)
          interval_cases i <;> interval_cases j <;> try exact (hne_val rfl).elim
          · exact hd12
          · exact hd13
          · exact hd12.symm
          · exact hd23
          · exact hd13.symm
          · exact hd23.symm
        · intro _
          exact hcw
      · obtain ⟨s₀, t₀, P₀, hord₀, hdisj₀, hP₀, _⟩ := exists_ordered_boundary_paths hc hA
        have hord_π : IsOrderingOf (divBoundary S_H A) (tildeA_πA hc vis tA) := by
          have h := (tildeA_hyp_vii hc vis tA ⟨A, hA, rfl⟩).2
          rwa [(tildeA_properties hc vis hA).2.2.2] at h
        have hex_idx : ∀ i : Fin (tildeA_πLen vis tA),
            ∃ j : Fin (divBoundary S_H A).ncard, s₀ j = tildeA_πA hc vis tA i := by
          intro i
          rw [← mem_range, hord₀.2, ← hord_π.2]
          exact mem_range_self i
        choose idx hidx using hex_idx
        have hidx_inj : Function.Injective idx := by
          intro i j hij
          exact hord_π.1 (by rw [← hidx i, ← hidx j, hij])
        refine ⟨P₀ ∘ idx, t₀ ∘ idx, ?_, ?_, fun h3' => (h3 h3').elim⟩
        · intro i
          dsimp only [Function.comp_apply]
          rw [← hidx i]
          exact hP₀ (idx i)
        · intro i j hij
          exact hdisj₀ (hidx_inj.ne hij)
    · have hA' : tA.deleteVerts X ∈ 𝒜 := hdel_eq.symm ▸ hA
      have hp_spec := (exists_ordered_boundary_paths hc hA').choose_spec
      let t₀ := hp_spec.choose
      let P₀ := hp_spec.choose_spec.choose
      obtain ⟨_, hdisj₀, hP₀, hcw₀⟩ := hp_spec.choose_spec.choose_spec
      have hπA_eq : tildeA_πA hc vis tA =
          fun i => (exists_ordered_boundary_paths hc hA').choose (i.cast (tildeA_πLen_neg vis h_int)) := by
        unfold tildeA_πA; split_ifs; rfl
      refine ⟨fun i => P₀ (i.cast (tildeA_πLen_neg vis h_int)),
        fun i => t₀ (i.cast (tildeA_πLen_neg vis h_int)),
        ?_, ?_, ?_⟩
      · intro i
        rw [hπA_eq]
        exact hP₀ (i.cast (tildeA_πLen_neg vis h_int))
      · intro i j hij
        exact hdisj₀ (fun h => hij ((Fin.castOrderIso (tildeA_πLen_neg vis h_int)).injective h))
      · intro h3
        have hk3 : (divBoundary S_H (tA.deleteVerts X)).ncard = 3 :=
          (tildeA_πLen_neg vis h_int).symm.trans h3
        exact hcw₀ hk3
  intro tA htA
  obtain ⟨P, t_g, hP, hdisj, hcw⟩ := hex_graph tA htA
  have hex_corner : ∀ i : Fin (tildeA_πLen vis tA), ∃ m : Fin 4, t_g i = W.toWall.corner m := by
    intro i
    have hmem : t_g i ∈ W.toWall.corners := hbar_set ▸ (hP i).1
    obtain ⟨m, hm⟩ := hmem
    exact ⟨m, hm.symm⟩
  choose m hm using hex_corner
  let t : Fin (tildeA_πLen vis tA) → OnePoint EuclideanPlane :=
    fun i => fig1Sph φ (pos (W.toWall.corner (m i)))
  refine ⟨P, t, ?_, hdisj, ?_⟩
  · intro i
    refine ⟨⟨m i, rfl⟩, ?_⟩
    rw [hJ_del, hdraw_corner (m i), ← hm i]
    exact (hP i).2
  · intro h3
    have hcw_g := hcw h3
    rw [hbar_eq, hm ⟨0, by omega⟩, hm ⟨1, by omega⟩, hm ⟨2, by omega⟩] at hcw_g
    exact horient (m ⟨0, by omega⟩) (m ⟨1, by omega⟩) (m ⟨2, by omega⟩) hcw_g

/-! ## 3. Connectedness of `H.perimeter` and `H.graph`, and `hyp_xi` -/

/-- `elementaryWallPerimeterVerts h` is connected in `elementaryWall h` (`IsElemWallConn`). -/
theorem isElemWallConn_elementaryWallPerimeterVerts {h : ℕ} (hh : 2 ≤ h) (he : Even h) :
    IsElemWallConn h (elementaryWallPerimeterVerts h) := by
  have hrow0 : IsElemWallConn h (elemRow h 0) := isElemWallConn_elemRow hh (by omega)
  have hrowh : IsElemWallConn h (elemRow h h) := isElemWallConn_elemRow hh le_rfl
  have hstrip0 : IsElemWallConn h (elemStrip h 0) := isElemWallConn_elemStrip hh he (by omega)
  have hstriph : IsElemWallConn h (elemStrip h h) := isElemWallConn_elemStrip hh he le_rfl
  obtain ⟨p00, hp00_r, hp00_s⟩ := elemRow_inter_elemStrip_nonempty hh (y := 0) (k := 0) (by omega) (by omega)
  obtain ⟨ph0, hph0_r, hph0_s⟩ := elemRow_inter_elemStrip_nonempty hh (y := h) (k := 0) le_rfl (by omega)
  obtain ⟨phh, hphh_r, hphh_s⟩ := elemRow_inter_elemStrip_nonempty hh (y := h) (k := h) le_rfl le_rfl
  have h1 : IsElemWallConn h (elemRow h 0 ∪ elemStrip h 0) :=
    hrow0.union_of_inter hstrip0 hp00_r hp00_s
  have h2 : IsElemWallConn h ((elemRow h 0 ∪ elemStrip h 0) ∪ elemRow h h) :=
    h1.union_of_inter hrowh (Or.inr hph0_s) hph0_r
  have h3 : IsElemWallConn h (((elemRow h 0 ∪ elemStrip h 0) ∪ elemRow h h) ∪ elemStrip h h) :=
    h2.union_of_inter hstriph (Or.inr hphh_r) hphh_s
  have heq : ((elemRow h 0 ∪ elemStrip h 0) ∪ elemRow h h) ∪ elemStrip h h =
      elementaryWallPerimeterVerts h := by
    ext ⟨x, y⟩
    simp only [elementaryWallPerimeterVerts, elemRow, elemStrip, mem_union, mem_ofPred_eq]
    constructor
    · rintro (((⟨hp, rfl⟩ | ⟨hp, hx⟩) | ⟨hp, rfl⟩) | ⟨hp, hx⟩)
      · exact ⟨hp, Or.inl rfl⟩
      · exact ⟨hp, Or.inr (Or.inr (Or.inl (by omega)))⟩
      · exact ⟨hp, Or.inr (Or.inl rfl)⟩
      · exact ⟨hp, Or.inr (Or.inr (Or.inr (by omega)))⟩
    · rintro ⟨hp, rfl | rfl | hx1 | hx2h⟩
      · exact Or.inl (Or.inl (Or.inl ⟨hp, rfl⟩))
      · exact Or.inl (Or.inr ⟨hp, rfl⟩)
      · exact Or.inl (Or.inl (Or.inr ⟨hp, by omega⟩))
      · exact Or.inr ⟨hp, by have := hp.1; omega⟩
  rwa [← heq]

/-- `elementaryWallVerts h` is connected in `elementaryWall h` (`IsElemWallConn`). -/
theorem isElemWallConn_elementaryWallVerts {h : ℕ} (hh : 2 ≤ h) (he : Even h) :
    IsElemWallConn h (elementaryWallVerts h) := by
  refine ⟨Subset.rfl, fun p hp q hq => ?_⟩
  have hrow_p : IsElemWallConn h (elemRow h p.2) := isElemWallConn_elemRow hh hp.2.1
  have hrow_q : IsElemWallConn h (elemRow h q.2) := isElemWallConn_elemRow hh hq.2.1
  have hstrip0 : IsElemWallConn h (elemStrip h 0) := isElemWallConn_elemStrip hh he (by omega)
  obtain ⟨r₁, hr₁_r, hr₁_s⟩ := elemRow_inter_elemStrip_nonempty hh hp.2.1 (k := 0) (by omega)
  obtain ⟨r₂, hr₂_r, hr₂_s⟩ := elemRow_inter_elemStrip_nonempty hh hq.2.1 (k := 0) (by omega)
  have h1 : IsElemWallConn h (elemRow h p.2 ∪ elemStrip h 0) :=
    hrow_p.union_of_inter hstrip0 hr₁_r hr₁_s
  have h2 : IsElemWallConn h ((elemRow h p.2 ∪ elemStrip h 0) ∪ elemRow h q.2) :=
    h1.union_of_inter hrow_q (Or.inr hr₂_s) hr₂_r
  obtain ⟨w, hw⟩ := h2.2 p (Or.inl (Or.inl ⟨hp, rfl⟩)) q (Or.inr ⟨hq, rfl⟩)
  exact ⟨w, fun z hz => h2.1 (hw z hz)⟩

/-- If `IsGraphPathWithEnds G P a b`, then every vertex `v ∈ V(P)` is joined by a walk in `P` to `a`,
and `a` is joined by a walk in `P` to `b`. -/
theorem exists_walk_of_mem_isGraphPathWithEnds {α : Type u} {β : Type v}
    {G P : Graph α β} {a b : α} (hP : IsGraphPathWithEnds G P a b) :
    (∀ v ∈ V(P), Nonempty (GraphWalk P v a)) ∧ Nonempty (GraphWalk P a b) := by
  obtain ⟨hP_le, w, hsimp, hV, hE⟩ := hP
  refine ⟨fun v hv => ?_, ⟨w⟩⟩
  have hv_supp : v ∈ w.support := by rwa [hV] at hv
  clear hP_le hsimp hV hE hv
  induction w with
  | @nil x hx =>
    simp only [GraphWalk.support, List.mem_singleton] at hv_supp
    subst hv_supp
    exact ⟨GraphWalk.nil hx⟩
  | @cons x x₁ y e hl rest ih =>
    simp only [GraphWalk.support, List.mem_cons] at hv_supp
    rcases hv_supp with rfl | hv_rest
    · exact ⟨GraphWalk.nil hl.left_mem⟩
    · obtain ⟨w'⟩ := ih hv_rest
      exact ⟨w'.append (GraphWalk.cons hl.symm (GraphWalk.nil hl.left_mem))⟩

/-- Every vertex of `W.perimeter` is joined by a walk in `W.perimeter` to `W.corner 0`. -/
theorem exists_walk_perimeter_to_corner0 {α : Type u} {β : Type v} (W : Wall α β)
    {v : α} (hv : v ∈ V(W.perimeter)) :
    Nonempty (GraphWalk W.perimeter v (W.corner 0)) := by
  have hh2 := W.two_le_height
  have he := W.even_height
  have hconn := isElemWallConn_elementaryWallPerimeterVerts hh2 he
  have hpath_perim : ∀ {p q : ℕ × ℕ} (hp : p ∈ elementaryWallPerimeterVerts W.height)
      (hq : q ∈ elementaryWallPerimeterVerts W.height) (hadj : elementaryWallAdj W.height p q),
      W.subdivisionPaths (W.baseEdge hadj) ≤ W.perimeter := by
    intro p q hp hq hadj
    exact le_subgraphSUnion W.perimeter_paths_le
      ⟨s(p, q), ⟨p, q, ⟨hadj, rfl⟩, hp, hq⟩, rfl⟩
  have hwalk_branch : ∀ {p q : ℕ × ℕ} (w₀ : GraphWalk (elementaryWall W.height) p q),
      (∀ z ∈ w₀.support, z ∈ elementaryWallPerimeterVerts W.height) →
      ∀ (hp : p ∈ elementaryWallVerts W.height) (hq : q ∈ elementaryWallVerts W.height),
        Nonempty (GraphWalk W.perimeter (W.branchVertex p hp) (W.branchVertex q hq)) := by
    intro p q w₀
    induction w₀ with
    | @nil a _ =>
      intro hsupp ha _
      have ha_perim : a ∈ elementaryWallPerimeterVerts W.height :=
        hsupp a (by simp [GraphWalk.support])
      exact ⟨GraphWalk.nil (branchVertex_mem_perimeter_of_mem_perimeterVerts W ha_perim)⟩
    | @cons a a₁ b e hl rest ih =>
      intro hsupp ha hb
      have ha_perim : a ∈ elementaryWallPerimeterVerts W.height :=
        hsupp a (by simp [GraphWalk.support])
      have ha₁_perim : a₁ ∈ elementaryWallPerimeterVerts W.height :=
        hsupp a₁ (by simp [GraphWalk.support, Surface.GraphWalk.start_mem_support])
      have hadj : elementaryWallAdj W.height a a₁ := hl.1
      have hP_le : W.subdivisionPaths (W.baseEdge hadj) ≤ W.perimeter :=
        hpath_perim ha_perim ha₁_perim hadj
      obtain ⟨_, w₁, _, _, _⟩ := W.isGraphPathWithEnds_baseEdge hadj
      obtain ⟨w₂⟩ := ih (fun z hz => hsupp z (by simp [GraphWalk.support, hz])) hadj.2.1 hb
      exact ⟨(w₁.mono hP_le).append w₂⟩
  rw [Wall.perimeter, GM09.vertexSet_subgraphSUnion] at hv
  obtain ⟨P, ⟨e₀, ⟨p, q, ⟨hadj, rfl⟩, hp_perim, hq_perim⟩, rfl⟩, hvP⟩ := mem_iUnion₂.mp hv
  have hP_le : W.subdivisionPaths (W.baseEdge hadj) ≤ W.perimeter :=
    hpath_perim hp_perim hq_perim hadj
  obtain ⟨w_v⟩ := (exists_walk_of_mem_isGraphPathWithEnds (W.isGraphPathWithEnds_baseEdge hadj)).1 v hvP
  have hc0_vert : elementaryWallCorner W.height 0 ∈ elementaryWallVerts W.height := by
    dsimp [elementaryWallCorner, elementaryWallVerts]
    refine ⟨by omega, by omega, by simp, by simp; omega⟩
  have hc0_perim : elementaryWallCorner W.height 0 ∈ elementaryWallPerimeterVerts W.height :=
    ⟨hc0_vert, Or.inl rfl⟩
  obtain ⟨w₀, hw₀⟩ := hconn.2 p hp_perim (elementaryWallCorner W.height 0) hc0_perim
  obtain ⟨w_b⟩ := hwalk_branch w₀ hw₀ hadj.1 hc0_vert
  exact ⟨(w_v.mono hP_le).append w_b⟩

/-- Every vertex of `W.graph` is joined by a walk in `W.graph` to `W.corner 0`. -/
theorem exists_walk_wall_to_corner0 {α : Type u} {β : Type v} (W : Wall α β)
    {v : α} (hv : v ∈ V(W.graph)) :
    Nonempty (GraphWalk W.graph v (W.corner 0)) := by
  have hh2 := W.two_le_height
  have he := W.even_height
  have hconn := isElemWallConn_elementaryWallVerts hh2 he
  have hc0_vert : elementaryWallCorner W.height 0 ∈ elementaryWallVerts W.height := by
    dsimp [elementaryWallCorner, elementaryWallVerts]
    refine ⟨by omega, by omega, by simp, by simp; omega⟩
  have hwalk_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      Nonempty (GraphWalk W.graph (W.branchVertex p hp) (W.corner 0)) := by
    intro p hp
    have hdisj : Disjoint (liftElemSet W (elementaryWallVerts W.height)) (∅ : Set α) :=
      disjoint_bot_right
    obtain ⟨w⟩ := exists_walk_in_liftElemSet W hdisj hp hc0_vert hconn hp hc0_vert
    exact ⟨w.mono Graph.deleteVerts_le⟩
  rw [W.vertexSet_eq] at hv
  rcases hv with hvB | hvP
  · obtain ⟨p, hp, rfl⟩ := W.exists_branchVertex_eq hvB
    exact hwalk_branch p hp
  · obtain ⟨b, hb, hv_sub⟩ := mem_iUnion₂.mp hvP
    obtain ⟨⟨e₀, ⟨p, q, hadj, rfl⟩⟩, hb_eq⟩ := W.baseIso.edgeEquiv.surjective ⟨b, hb⟩
    have hb_base : b = W.baseEdge hadj := (congrArg Subtype.val hb_eq).symm
    rw [hb_base] at hv_sub
    have hP := W.isGraphPathWithEnds_baseEdge hadj
    obtain ⟨w₁⟩ := (exists_walk_of_mem_isGraphPathWithEnds hP).1 v hv_sub
    obtain ⟨w₂⟩ := hwalk_branch p hadj.1
    exact ⟨(w₁.mono hP.1).append w₂⟩

/-- If `K ≤ S_H.G`, `A ∈ 𝒜`, and `w : GraphWalk K u v` is a walk in `K` starting at `u ∈ V(A)` and
ending at `v` with `v ∉ V(A) ∨ v ∈ S_H.Ω.bar`, then some vertex of `w` belongs to
`divBoundary S_H A ∩ V(K)`. -/
theorem exists_mem_divBoundary_of_walk {α : Type u} {β : Type v}
    {S_H : Society α β} {𝒜 : Set (Graph α β)} (hdiv : IsSocietyDivision S_H 𝒜)
    {K : Graph α β} (hK : K ≤ S_H.G) {A : Graph α β} (hA : A ∈ 𝒜)
    {u v : α} (w : GraphWalk K u v) (hu : u ∈ V(A)) (hv : v ∉ V(A) ∨ v ∈ S_H.Ω.bar) :
    (divBoundary S_H A ∩ V(K)).Nonempty := by
  induction w with
  | @nil a haK =>
    rcases hv with hva | hbar
    · exact (hva hu).elim
    · exact ⟨a, ⟨hu, Or.inl hbar⟩, haK⟩
  | @cons a x b e hl w_tail ih =>
    by_cases hx : x ∈ V(A)
    · exact ih hx hv
    · have hl_SH : S_H.G.IsLink e a x := hl.mono hK
      have he_not_A : e ∉ E(A) := by
        intro heA
        obtain ⟨y₁, y₂, hlA⟩ := A.exists_isLink_of_mem_edgeSet heA
        have hl_SH' : S_H.G.IsLink e y₁ y₂ := hlA.mono (hdiv.sub_of_mem hA)
        rcases S_H.G.eq_or_eq_of_isLink_of_isLink hl_SH hl_SH' with rfl | rfl
        · have h := hl_SH.right_unique hl_SH'
          exact hx (h ▸ hlA.right_mem)
        · have h := hl_SH.right_unique hl_SH'.symm
          exact hx (h ▸ hlA.left_mem)
      exact ⟨a, ⟨hu, Or.inr ⟨e, ⟨hl_SH.edge_mem, he_not_A⟩, ⟨x, hl_SH⟩⟩⟩, hl.left_mem⟩

/-- For every non-interior member `A ∈ 𝒜`, `(divBoundary S_H A ∩ V(H.perimeter)).Nonempty`. -/
theorem divBoundary_inter_perimeter_nonempty_of_not_interior {α : Type u} {β : Type v}
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) {A : Graph α β} (hA : A ∈ 𝒜)
    (hnot_int : ¬ IsInteriorMember H 𝒜 A) :
    (divBoundary S_H A ∩ V(H.perimeter)).Nonempty := by
  have hnot_disj : ¬ Disjoint V(A) V(H.perimeter) := fun h => hnot_int ⟨hA, h⟩
  obtain ⟨u, huA, huP⟩ := Set.not_disjoint_iff.mp hnot_disj
  obtain ⟨w⟩ := exists_walk_perimeter_to_corner0 H huP
  have hGX : (G.deleteVertices X).toGraph = G.toGraph.deleteVerts X :=
    gm13_deleteVertices_toGraph_eq G X
  have hH_GX : H.graph ≤ G.toGraph.deleteVerts X := hGX ▸ hc.wall_in
  have hH_SH : H.graph ≤ S_H.G := by
    rw [hc.isWallSociety.1, hGX]
    exact wall_le_wallCompass hH_GX
  have hP_SH : H.perimeter ≤ S_H.G := H.perimeter_le.trans hH_SH
  have hc0_bar : H.corner 0 ∈ S_H.Ω.bar := by
    rw [hc.isWallSociety.2]
    exact ⟨0, rfl⟩
  exact exists_mem_divBoundary_of_walk hc.isRuralDivision.isDivision hP_SH hA w huA (Or.inr hc0_bar)

/-- For every interior member `A ∈ 𝒜`, `vis.vOf A ∈ V(H.graph)` and there is a path `P` in `S_H.G`
from `vis.vOf A` to a vertex `s ∈ divBoundary S_H A` with `V(P) ∩ V(H.graph) = {vis.vOf A}`. -/
theorem interior_vOf_path_to_divBoundary {α : Type u} {β : Type v}
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) (vis : Vision G X H S_H 𝒜)
    {A : Graph α β} (h_int : IsInteriorMember H 𝒜 A) :
    vis.vOf A ∈ V(H.graph) ∧
    ∃ s ∈ divBoundary S_H A, ∃ P : Graph α β,
      IsGraphPathWithEnds S_H.G P (vis.vOf A) s ∧
      V(P) ∩ V(H.graph) = {vis.vOf A} := by
  obtain ⟨hv_H, P, s, hs_or, hP, hinter⟩ := vis.vOf_valid h_int
  refine ⟨hv_H, s, ?_, P, hP.symm, hinter⟩
  rcases hs_or with hs_bd | ⟨hbd_empty, hsA⟩
  · exact hs_bd
  · exfalso
    have hGX : (G.deleteVertices X).toGraph = G.toGraph.deleteVerts X :=
      gm13_deleteVertices_toGraph_eq G X
    have hH_GX : H.graph ≤ G.toGraph.deleteVerts X := hGX ▸ hc.wall_in
    have hH_SH : H.graph ≤ S_H.G := by
      rw [hc.isWallSociety.1, hGX]
      exact wall_le_wallCompass hH_GX
    obtain ⟨w_P⟩ := (exists_walk_of_mem_isGraphPathWithEnds hP).2
    obtain ⟨w_H⟩ := exists_walk_wall_to_corner0 H hv_H
    have w_tot : GraphWalk S_H.G s (H.corner 0) := (w_P.mono hP.1).append (w_H.mono hH_SH)
    have hc0_bar : H.corner 0 ∈ S_H.Ω.bar := by
      rw [hc.isWallSociety.2]
      exact ⟨0, rfl⟩
    obtain ⟨z, hz_bd, _⟩ :=
      exists_mem_divBoundary_of_walk hc.isRuralDivision.isDivision le_rfl h_int.1 w_tot hsA (Or.inr hc0_bar)
    exact (hbd_empty ▸ hz_bd).elim

/-- The representative vertex `tildeA_vOfGraph hc vis tA ∈ V(H.graph)` for `tA : Graph α β`:
`vis.vOf (tA.deleteVerts X)` when `tA.deleteVerts X` is an interior member of `𝒜`, and a chosen
vertex of `divBoundary S_H (tA.deleteVerts X) ∩ V(H.perimeter)` otherwise. -/
noncomputable def tildeA_vOfGraph {α : Type u} {β : Type v}
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) (vis : Vision G X H S_H 𝒜)
    (tA : Graph α β) : α :=
  open Classical in
  if h_int : IsInteriorMember H 𝒜 (tA.deleteVerts X) then
    vis.vOf (tA.deleteVerts X)
  else if hA : tA.deleteVerts X ∈ 𝒜 then
    (divBoundary_inter_perimeter_nonempty_of_not_interior hc hA h_int).choose
  else
    H.corner 0

/-- The drawn representative vertex `tildeA_vA hc vis φ pos tA ∈ OnePoint EuclideanPlane`. -/
noncomputable def tildeA_vA {α : Type u} {β : Type v}
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) (vis : Vision G X H S_H 𝒜)
    (φ : EuclideanPlane ≃ₜ EuclideanPlane) (pos : α → ℝ × ℝ)
    (tA : Graph α β) : OnePoint EuclideanPlane :=
  fig1Sph φ (pos (tildeA_vOfGraph hc vis tA))

/-- Under `HypothesisC G q X H S_H 𝒜` and `vis : Vision G X H S_H 𝒜`, Hypothesis (xi) of
Theorem (8.3) holds for `tildeA_vA hc vis φ pos`. -/
theorem tildeA_hyp_xi {α : Type u} {β : Type v} [Nonempty α]
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) (vis : Vision G X H S_H 𝒜)
    {W : DrawnWall α β} (hW_toWall : W.toWall = H)
    {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1)) :
    let Z := divTotalBoundary S_H 𝒜
    let 𝒜_83 := (fun A => (vis.tildeA A).toGraph) '' 𝒜
    ∀ tA ∈ 𝒜_83, tildeA_vA hc vis φ pos tA ∈ Γ.drawing.V ∧
      ∃ u ∈ Z ∩ V(tA), ∃ P : Graph α β,
        IsGraphPathWithEnds (G.toGraph.deleteVerts X) P
          (drawingVertToGraph Γ (tildeA_vA hc vis φ pos tA)) u ∧
        V(P) ∩ V(W.graph) = {drawingVertToGraph Γ (tildeA_vA hc vis φ pos tA)} := by
  subst hW_toWall
  rintro Z 𝒜_83 _ ⟨A, hA, rfl⟩
  let tA := (vis.tildeA A).toGraph
  obtain ⟨_, hdel_eq, _, hZA⟩ := tildeA_properties hc vis hA
  have hGX : (G.deleteVertices X).toGraph = G.toGraph.deleteVerts X :=
    gm13_deleteVertices_toGraph_eq G X
  have hH_GX : W.toWall.graph ≤ G.toGraph.deleteVerts X := hGX ▸ hc.wall_in
  have hSH_le_GX : S_H.G ≤ G.toGraph.deleteVerts X := by
    rw [hc.isWallSociety.1, hGX]
    exact wallCompass_le hH_GX
  have hvOf_mem : tildeA_vOfGraph hc vis tA ∈ V(W.graph) := by
    unfold tildeA_vOfGraph
    split_ifs with h_int hA'
    · exact (vis.vOf_valid h_int).1
    · exact W.toWall.perimeter_le.vertexSet_mono
        (divBoundary_inter_perimeter_nonempty_of_not_interior hc hA' h_int).choose_spec.2
    · exact W.toWall.perimeter_le.vertexSet_mono (corner_mem_perimeter W.toWall 0)
  have hvA_V : tildeA_vA hc vis φ pos tA ∈ Γ.drawing.V := by
    unfold tildeA_vA
    rw [← hΓv ⟨tildeA_vOfGraph hc vis tA, hvOf_mem⟩]
    exact (Γ.iso.vertexEquiv _).2
  have hdraw_vA : drawingVertToGraph Γ (tildeA_vA hc vis φ pos tA) = tildeA_vOfGraph hc vis tA := by
    unfold tildeA_vA
    rw [← hΓv ⟨tildeA_vOfGraph hc vis tA, hvOf_mem⟩, drawingVertToGraph_apply_vertexEquiv]
  refine ⟨hvA_V, ?_⟩
  rw [hdraw_vA, hZA]
  by_cases h_int : IsInteriorMember W.toWall 𝒜 (tA.deleteVerts X)
  · have h_int_A : IsInteriorMember W.toWall 𝒜 A := hdel_eq ▸ h_int
    have hvOf_eq : tildeA_vOfGraph hc vis tA = vis.vOf A := by
      unfold tildeA_vOfGraph
      split_ifs
      rw [hdel_eq]
    rw [hvOf_eq]
    obtain ⟨_, s, hs_bd, P, hP, hinter⟩ := interior_vOf_path_to_divBoundary hc vis h_int_A
    exact ⟨s, hs_bd, P, ⟨hP.1.trans hSH_le_GX, hP.2⟩, hinter⟩
  · have hA' : tA.deleteVerts X ∈ 𝒜 := hdel_eq.symm ▸ hA
    have hvOf_eq : tildeA_vOfGraph hc vis tA =
        (divBoundary_inter_perimeter_nonempty_of_not_interior hc hA' h_int).choose := by
      unfold tildeA_vOfGraph
      split_ifs
      rfl
    have hspec := (divBoundary_inter_perimeter_nonempty_of_not_interior hc hA' h_int).choose_spec
    let u₀ := tildeA_vOfGraph hc vis tA
    have hu₀_bd : u₀ ∈ divBoundary S_H A := by
      rw [← hdel_eq]
      change tildeA_vOfGraph hc vis tA ∈ _
      rw [hvOf_eq]
      exact hspec.1
    have hu₀_W : u₀ ∈ V(W.graph) := hvOf_mem
    have hu₀_GX : u₀ ∈ V(G.toGraph.deleteVerts X) := hH_GX.vertexSet_mono hu₀_W
    let P : Graph α β := Graph.noEdge {u₀} β
    have hP_le : P ≤ G.toGraph.deleteVerts X := by
      refine ⟨singleton_subset_iff.mpr hu₀_GX, fun e x y hl => ?_⟩
      simp [P, Graph.noEdge] at hl
    have hP_path : IsGraphPathWithEnds (G.toGraph.deleteVerts X) P u₀ u₀ := by
      refine ⟨hP_le, GraphWalk.nil (mem_singleton u₀), List.nodup_singleton u₀, ?_, ?_⟩
      · ext z; simp [P, Graph.noEdge, GraphWalk.support]
      · ext e; simp [P, Graph.noEdge, GraphWalk.edges]
    refine ⟨u₀, hu₀_bd, P, hP_path, ?_⟩
    ext z
    simp only [P, Graph.noEdge, mem_inter_iff, mem_singleton_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hu₀_W⟩⟩

/-! ## 4. Double-Shift Subwall Coordinates and `hyp_xiii` -/

/-- If `H'` is a subwall of `W` at shift `(i, j)` and `H'' = subwallOfShift H' h i'' j'' ...`,
then for every `u ∈ V(H''.graph)`, `pos u ∈ shiftHomeo (i + i'') (j + j'') '' fig1Set h`. -/
theorem pos_mem_double_shift_fig1Set_of_mem_subwallOfShift {α : Type u} {β : Type v}
    {W : DrawnWall α β} {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hΓe : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β) (hf : f ∈ E(W.graph)),
      f ∈ E(W.subdivisionPaths (W.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q)
    {H' : Wall α β} {i j : ℕ}
    (hh' : H'.height ≤ W.height) (hi_even : Even i) (hj_even : Even j)
    (hi : i ≤ 2 * W.height - 2 * H'.height) (hj : j ≤ W.height - H'.height)
    (hbranch : ∀ (p : ℕ × ℕ) (hp' : p ∈ elementaryWallVerts H'.height)
      (hp : wallShift i j p ∈ elementaryWallVerts W.height),
      H'.branchVertex p hp' = W.branchVertex (wallShift i j p) hp)
    (hpaths : H'.subdivisionPaths = W.subdivisionPaths)
    (hbase : H'.baseGraph = W.baseGraph.induce
      ((fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
        {p : elementaryWallVerts W.height |
          ∃ q ∈ elementaryWallVerts H'.height, p.1 = wallShift i j q}))
    {h i'' j'' : ℕ} (hh2 : 2 ≤ h) (hh_even : Even h) (hh_le : h ≤ H'.height)
    (hi''_even : Even i'') (hj''_even : Even j'')
    (hi'' : i'' ≤ 2 * H'.height - 2 * h) (hj'' : j'' ≤ H'.height - h)
    {u : α}
    (hu : u ∈ V((subwallOfShift H' h i'' j'' hh2 hh_even hh_le hi''_even hj''_even hi'' hj'').graph)) :
    pos u ∈ shiftHomeo (i + i'') (j + j'') '' fig1Set h := by
  let H'' := subwallOfShift H' h i'' j'' hh2 hh_even hh_le hi''_even hj''_even hi'' hj''
  have hbranch'' : ∀ (p : ℕ × ℕ) (hp'' : p ∈ elementaryWallVerts H''.height)
      (hp' : wallShift i'' j'' p ∈ elementaryWallVerts H'.height),
      H''.branchVertex p hp'' = H'.branchVertex (wallShift i'' j'' p) hp' :=
    fun _ _ _ => rfl
  have hpaths'' : H''.subdivisionPaths = H'.subdivisionPaths := rfl
  have hbase'' : H''.baseGraph = H'.baseGraph.induce
      ((fun p : elementaryWallVerts H'.height => (H'.baseIso.vertexEquiv p).1) ''
        {p : elementaryWallVerts H'.height |
          ∃ q ∈ elementaryWallVerts H''.height, p.1 = wallShift i'' j'' q}) := rfl
  have hshift_eq : ∀ z : ℝ × ℝ,
      shiftHomeo i j (shiftHomeo i'' j'' z) = shiftHomeo (i + i'') (j + j'') z := by
    intro z
    ext <;> simp [shiftHomeo_apply] <;> ring
  rw [H''.vertexSet_eq] at hu
  rcases hu with huB | huP
  · obtain ⟨p'', hp'', rfl⟩ := H''.exists_branchVertex_eq huB
    have hp' := wallShift_mem_elementaryWallVerts hh_le hi'' hj'' hp''
    have hpW := wallShift_mem_elementaryWallVerts hh' hi hj hp'
    rw [hbranch'' p'' hp'' hp', hbranch _ hp' hpW, hpos_branch _ hpW,
      ← shiftHomeo_latticePoint, ← shiftHomeo_latticePoint, hshift_eq]
    exact ⟨GM16.latticePoint p'', latticePoint_mem_fig1Set hh2 hp'', rfl⟩
  · obtain ⟨b, hb, hu_sub⟩ := mem_iUnion₂.mp huP
    obtain ⟨⟨e₀, ⟨p'', q'', hadj'', rfl⟩⟩, hb_eq⟩ := H''.baseIso.edgeEquiv.surjective ⟨b, hb⟩
    have hb_base : b = H''.baseEdge hadj'' := (congrArg Subtype.val hb_eq).symm
    have hadj' := (elementaryWallAdj_wallShift_iff hh_le hi''_even hj''_even hi'' hj''
      hadj''.1 hadj''.2.1).mpr hadj''
    have hadjW := (elementaryWallAdj_wallShift_iff hh' hi_even hj_even hi hj
      hadj'.1 hadj'.2.1).mpr hadj'
    rw [hb_base, subwall_baseEdge_eq hh_le hi''_even hj''_even hi'' hj'' hbranch'' hbase'' hadj'',
      subwall_baseEdge_eq hh' hi_even hj_even hi hj hbranch hbase hadj',
      hpaths'', hpaths] at hu_sub
    have hseg := pos_mem_fig1Segment_of_mem_subdivisionPaths hΓv hΓe hadjW hu_sub
    rw [← shiftHomeo_image_fig1Segment, ← shiftHomeo_image_fig1Segment] at hseg
    obtain ⟨w, ⟨z, hz, rfl⟩, hweq⟩ := hseg
    rw [← hweq, hshift_eq]
    refine ⟨z, ?_, rfl⟩
    simp only [fig1Set, mem_iUnion]
    exact ⟨p'', q'', hadj'', hz⟩

/-- Helper to transport `GM13.HasSameDeltaFolio` from `rootedDigraphOfList` along root-length
equalities. -/
theorem gm13_hasSameDeltaFolio_of_roots_eq {α : Type u} {β : Type v}
    {G₁ G₂ : GM13.Digraph α β} {l₁ l₂ : List α}
    (hl₁ : ∀ x ∈ l₁, x ∈ G₁.vertexSet) (hl₂ : ∀ x ∈ l₂, x ∈ G₂.vertexSet)
    (heq : l₁.length = l₂.length) {δ k : ℕ} (hk : l₁.length = k)
    {r₁ r₂ : Fin k → α} (hr₁ : ∀ j : Fin k, r₁ j ∈ G₁.vertexSet)
    (hr₂ : ∀ j : Fin k, r₂ j ∈ G₂.vertexSet)
    (h1 : ∀ j : Fin k, r₁ j = l₁[j.1]'(by omega))
    (h2 : ∀ j : Fin k, r₂ j = l₂[j.1]'(by omega))
    (hsame : GM13.HasSameDeltaFolio (rootedDigraphOfList G₁ l₁ hl₁)
      (heq.symm ▸ rootedDigraphOfList G₂ l₂ hl₂) δ) :
    GM13.HasSameDeltaFolio ⟨G₂, r₂, hr₂⟩ ⟨G₁, r₁, hr₁⟩ δ := by
  subst hk
  have hcast : ∀ {m n : ℕ} (h : m = n) (R : GM13.RootedDigraph α β m),
      h ▸ R = ⟨R.digraph, fun i => R.roots (i.cast h.symm), fun i => R.roots_mem _⟩ := by
    intro m n h R; subst h; rfl
  rw [hcast] at hsame
  have hR₁ : (⟨G₁, r₁, hr₁⟩ : GM13.RootedDigraph α β l₁.length) =
      rootedDigraphOfList G₁ l₁ hl₁ := by
    dsimp [rootedDigraphOfList]
    congr 1
    funext j
    exact h1 j
  have hR₂ : (⟨G₂, r₂, hr₂⟩ : GM13.RootedDigraph α β l₁.length) =
      ⟨G₂, fun i => (rootedDigraphOfList G₂ l₂ hl₂).roots (i.cast heq),
        fun i => (rootedDigraphOfList G₂ l₂ hl₂).roots_mem _⟩ := by
    dsimp [rootedDigraphOfList]
    congr 1
    funext j
    exact h2 j
  rw [hR₁, hR₂]
  exact hsame.symm

/-- For interior members `A, A' ∈ 𝒜`, `vis.HasSameMemberDeltaFolio δ A A'` implies
`tildeA_πLen vis tA' = tildeA_πLen vis tA` and `GM22.HasSameDeltaFolio` between the corresponding
`subRootedDigraph`s in `Hypotheses83InGraph.hyp_xiii`. -/
theorem tildeA_subRootedDigraph_hasSameDeltaFolio {α : Type u} {β : Type v} [Nonempty α] [Nonempty β]
    {G : GM13.Digraph α β} {q δ : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) (vis : Vision G X H S_H 𝒜)
    {A A' : Graph α β} (h_int : IsInteriorMember H 𝒜 A) (h_int' : IsInteriorMember H 𝒜 A')
    (hfolio : vis.HasSameMemberDeltaFolio δ A A') :
    let tA := (vis.tildeA A).toGraph
    let tA' := (vis.tildeA A').toGraph
    ∃ hlen : tildeA_πLen vis tA' = tildeA_πLen vis tA,
      ∀ (htA_le : tA ≤ G.toGraph) (htA'_le : tA' ≤ G.toGraph)
        (hmem_A : ∀ j : Fin (tildeA_πLen vis tA + q),
          seqConcat (tildeA_πA hc vis tA) (visionXOrdering hc vis) j ∈ V(tA))
        (hmem_A' : ∀ j : Fin (tildeA_πLen vis tA + q),
          seqConcat (tildeA_πA hc vis tA' ∘ Fin.cast hlen.symm) (visionXOrdering hc vis) j ∈ V(tA')),
        GM22.HasSameDeltaFolio
          (subRootedDigraph (toGM22Digraph G) tA' htA'_le
            (seqConcat (tildeA_πA hc vis tA' ∘ Fin.cast hlen.symm) (visionXOrdering hc vis))
            hmem_A')
          (subRootedDigraph (toGM22Digraph G) tA htA_le
            (seqConcat (tildeA_πA hc vis tA) (visionXOrdering hc vis))
            hmem_A)
          δ := by
  intro tA tA'
  obtain ⟨_, hdel_A, _, _⟩ := tildeA_properties hc vis h_int.1
  obtain ⟨_, hdel_A', _, _⟩ := tildeA_properties hc vis h_int'.1
  have h_int_tA : IsInteriorMember H 𝒜 (tA.deleteVerts X) := hdel_A.symm ▸ h_int
  have h_int_tA' : IsInteriorMember H 𝒜 (tA'.deleteVerts X) := hdel_A'.symm ▸ h_int'
  have hlen_tA : tildeA_πLen vis tA = (vis.sSeq A).length := by
    rw [tildeA_πLen_pos vis h_int_tA, hdel_A]
  have hlen_tA' : tildeA_πLen vis tA' = (vis.sSeq A').length := by
    rw [tildeA_πLen_pos vis h_int_tA', hdel_A']
  have hlen_x : vis.xSeq.length = q := vision_xSeq_length_eq hc vis
  have hpi_len_A : (vis.pi A).length = tildeA_πLen vis tA + q := by
    simp [Vision.pi, hlen_tA, hlen_x]
  have hpi_len_A' : (vis.pi A').length = tildeA_πLen vis tA' + q := by
    simp [Vision.pi, hlen_tA', hlen_x]
  have hlen_app_A : (vis.sSeq A ++ vis.xSeq).length = tildeA_πLen vis tA + q := hpi_len_A
  have hlen_app_A' : (vis.sSeq A' ++ vis.xSeq).length = tildeA_πLen vis tA' + q := hpi_len_A'
  obtain ⟨hpi_A, hpi_A', hpi_eq, hsame_gm13⟩ := hfolio
  have hlen : tildeA_πLen vis tA' = tildeA_πLen vis tA := by omega
  refine ⟨hlen, fun htA_le htA'_le hmem_A hmem_A' => ?_⟩
  let rA : Fin (tildeA_πLen vis tA + q) → α :=
    seqConcat (tildeA_πA hc vis tA) (visionXOrdering hc vis)
  let rA' : Fin (tildeA_πLen vis tA + q) → α :=
    seqConcat (tildeA_πA hc vis tA' ∘ Fin.cast hlen.symm) (visionXOrdering hc vis)
  have hrA_eq : ∀ j : Fin (tildeA_πLen vis tA + q),
      rA j = (vis.pi A)[j.1]'(by omega) := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun k => ?_) j
    · simp only [rA, seqConcat, Fin.append_left, Fin.val_castAdd, Vision.pi]
      rw [List.getElem_append_left (by omega)]
      unfold tildeA_πA
      split_ifs
      dsimp only
      congr 1; rw [hdel_A]
    · simp only [rA, seqConcat, Fin.append_right, Fin.val_natAdd, Vision.pi]
      rw [List.getElem_append_right (by omega)]
      unfold visionXOrdering
      congr 1
      omega
  have hrA'_eq : ∀ j : Fin (tildeA_πLen vis tA + q),
      rA' j = (vis.pi A')[j.1]'(by omega) := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun k => ?_) j
    · simp only [rA', seqConcat, Fin.append_left, Fin.val_castAdd, Vision.pi, Function.comp_apply]
      rw [List.getElem_append_left (by omega)]
      unfold tildeA_πA
      split_ifs
      dsimp only [Fin.val_cast]
      congr 1; rw [hdel_A']
    · simp only [rA', seqConcat, Fin.append_right, Fin.val_natAdd, Vision.pi]
      rw [List.getElem_append_right (by omega)]
      unfold visionXOrdering
      congr 1
      omega
  let R₁ : GM13.RootedDigraph α β (tildeA_πLen vis tA + q) :=
    ⟨vis.tildeA A', rA', hmem_A'⟩
  let R₂ : GM13.RootedDigraph α β (tildeA_πLen vis tA + q) :=
    ⟨vis.tildeA A, rA, hmem_A⟩
  have hsame_R₁_R₂ : GM13.HasSameDeltaFolio R₁ R₂ δ :=
    gm13_hasSameDeltaFolio_of_roots_eq hpi_A hpi_A' hpi_eq hpi_len_A
      hmem_A hmem_A' hrA_eq hrA'_eq hsame_gm13
  intro αH βH R_H hDet
  have hsub_A : (vis.tildeA A).IsSubdigraph G := (vis.tildeA_valid h_int.1).1
  have hsub_A' : (vis.tildeA A').IsSubdigraph G := (vis.tildeA_valid h_int'.1).1
  rw [hasRootedDigraphModel_subRootedDigraph_iff_of_isSubdigraph hsub_A' rA' hmem_A' R_H,
      hasRootedDigraphModel_subRootedDigraph_iff_of_isSubdigraph hsub_A rA hmem_A R_H]
  exact gm22_hasSameDeltaFolio_of_gm13 R₁ R₂ hsame_R₁_R₂ R_H hDet

/-- **Homogeneity outside `D_disc` (`hyp_xiii`)**: Under `HypothesisC G q X H S_H 𝒜`, a vision `vis`,
and an `h`-homogeneous subwall `H'` of `W.toWall = H` at shift `(i, j)`, Hypothesis (xiii) of
Theorem (8.3) holds with distance bound `8 * h + 2`. -/
theorem tildeA_hyp_xiii {α : Type u} {β : Type v} [Nonempty α] [Nonempty β]
    {G : GM13.Digraph α β} {q δ h : ℕ} (hh2 : 2 ≤ h) (hh_even : Even h)
    {X : Set α} {H : Wall α β} {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) (vis : Vision G X H S_H 𝒜)
    {W : DrawnWall α β} (hW_toWall : W.toWall = H)
    {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hinj : InjOn pos V(W.graph))
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hΓU : Γ.drawing.U = fig1Sph φ '' fig1Set W.height)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hΓe : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β) (hf : f ∈ E(W.graph)),
      f ∈ E(W.subdivisionPaths (W.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q)
    {T : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
      Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)))}
    {d : Set (OnePoint EuclideanPlane) → Set (OnePoint EuclideanPlane) → ℕ}
    (hd : HasTangleMetric Γ.drawing W.height T d)
    {H' : Wall α β} {i j : ℕ}
    (hh_le_H' : h ≤ H'.height)
    (hh' : H'.height ≤ W.height) (hi_even : Even i) (hj_even : Even j)
    (hi : i ≤ 2 * W.height - 2 * H'.height) (hj : j ≤ W.height - H'.height)
    (hbranch : ∀ (p : ℕ × ℕ) (hp' : p ∈ elementaryWallVerts H'.height)
      (hp : wallShift i j p ∈ elementaryWallVerts W.height),
      H'.branchVertex p hp' = W.branchVertex (wallShift i j p) hp)
    (hpaths : H'.subdivisionPaths = W.subdivisionPaths)
    (hbase : H'.baseGraph = W.baseGraph.induce
      ((fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
        {p : elementaryWallVerts W.height |
          ∃ q ∈ elementaryWallVerts H'.height, p.1 = wallShift i j q}))
    (hhom : IsHomogeneousSubwall vis δ h H') :
    let R_G := visionRootedDigraph hc vis
    let 𝒜_83 := (fun A => (vis.tildeA A).toGraph) '' 𝒜
    let D_disc := closure ((fig1Sph φ ∘ shiftHomeo i j) '' fig1EnclosedSet H'.height)ᶜ
    ∀ (tA : Graph α β), tA ∈ 𝒜_83 → tildeA_vA hc vis φ pos tA ∈ Set.univ \ D_disc →
      ∀ v ∈ Γ.drawing.V \ D_disc,
        ∀ (htA_le : tA ≤ R_G.G.toGraph)
          (hmem_A : ∀ k : Fin (tildeA_πLen vis tA + q),
            seqConcat (tildeA_πA hc vis tA) R_G.roots k ∈ V(tA)),
          ∃ tA' ∈ 𝒜_83,
            subsetTangleDist Γ.drawing W.height d {v} {tildeA_vA hc vis φ pos tA'} ≤ 8 * h + 2 ∧
            ∃ hlen : tildeA_πLen vis tA' = tildeA_πLen vis tA,
              ∀ (htA'_le : tA' ≤ R_G.G.toGraph)
                (hmem_A' : ∀ k : Fin (tildeA_πLen vis tA + q),
                  seqConcat (tildeA_πA hc vis tA' ∘ Fin.cast hlen.symm) R_G.roots k ∈ V(tA')),
                GM22.HasSameDeltaFolio
                  (subRootedDigraph R_G.G tA' htA'_le
                    (seqConcat (tildeA_πA hc vis tA' ∘ Fin.cast hlen.symm) R_G.roots) hmem_A')
                  (subRootedDigraph R_G.G tA htA_le
                    (seqConcat (tildeA_πA hc vis tA) R_G.roots) hmem_A)
                  δ := by
  subst hW_toWall
  intro R_G 𝒜_83 D_disc
  obtain ⟨_, hcompl_D, hinside_of_not_D, _, _⟩ :=
    subwall_disc_props hinj hpos_branch hΓU hΓv hΓe hh' hi_even hj_even hi hj hbranch hpaths hbase
  rintro _ ⟨A, hA, rfl⟩ hvA_not_D v hv_not_D htA_le hmem_A
  let tA := (vis.tildeA A).toGraph
  obtain ⟨_, hdel_eq, _, _⟩ := tildeA_properties hc vis hA
  -- First show `A` must be an interior member and `vis.vOf A ∈ H'.insideVerts`
  have h_int : IsInteriorMember W.toWall 𝒜 (tA.deleteVerts X) := by
    by_contra hnot_int
    have hA' : tA.deleteVerts X ∈ 𝒜 := hdel_eq.symm ▸ hA
    have hperim : tildeA_vOfGraph hc vis tA ∈ V(W.perimeter) := by
      unfold tildeA_vOfGraph
      split_ifs
      exact (divBoundary_inter_perimeter_nonempty_of_not_interior hc hA' hnot_int).choose_spec.2
    have hW_mem : tildeA_vOfGraph hc vis tA ∈ V(W.graph) :=
      W.toWall.perimeter_le.vertexSet_mono hperim
    have hnot_int_W : pos (tildeA_vOfGraph hc vis tA) ∉ interior (fig1EnclosedSet W.height) :=
      (mem_perimeter_iff_pos_not_mem_interior hinj hpos_branch hΓv hΓe hW_mem).mp hperim
    rw [hcompl_D, image_comp] at hvA_not_D
    obtain ⟨w, ⟨z, hz_int, rfl⟩, hweq⟩ := hvA_not_D
    have hpos_eq : pos (tildeA_vOfGraph hc vis tA) = shiftHomeo i j z :=
      (isOpenEmbedding_fig1Sph φ).injective hweq.symm
    have hz_shift_int : shiftHomeo i j z ∈ interior (shiftHomeo i j '' fig1EnclosedSet H'.height) := by
      rw [interior_image_eq_of_isOpenEmbedding (shiftHomeo i j).isOpenEmbedding]
      exact ⟨z, hz_int, rfl⟩
    have hz_W_int : shiftHomeo i j z ∈ interior (fig1EnclosedSet W.height) :=
      interior_mono (shiftHomeo_image_fig1EnclosedSet_subset hh' hi_even hj_even hi hj) hz_shift_int
    exact hnot_int_W (hpos_eq ▸ hz_W_int)
  have h_int_A : IsInteriorMember W.toWall 𝒜 A := hdel_eq ▸ h_int
  have hvOf_eq : tildeA_vOfGraph hc vis tA = vis.vOf A := by
    unfold tildeA_vOfGraph; split_ifs; rw [hdel_eq]
  have hvA_V : tildeA_vA hc vis φ pos tA ∈ Γ.drawing.V := by
    unfold tildeA_vA
    rw [hvOf_eq, ← hΓv ⟨vis.vOf A, (vis.vOf_valid h_int_A).1⟩]
    exact (Γ.iso.vertexEquiv _).2
  have hdraw_vA : drawingVertToGraph Γ (tildeA_vA hc vis φ pos tA) = vis.vOf A := by
    unfold tildeA_vA
    rw [hvOf_eq, ← hΓv ⟨vis.vOf A, (vis.vOf_valid h_int_A).1⟩, drawingVertToGraph_apply_vertexEquiv]
  have hvOf_in_H' : vis.vOf A ∈ H'.insideVerts :=
    hdraw_vA ▸ hinside_of_not_D (tildeA_vA hc vis φ pos tA) ⟨hvA_V, hvA_not_D.2⟩
  -- Locate `v ∈ Γ.drawing.V \ D_disc` inside a brick of `H'`
  obtain ⟨⟨u, huW⟩, hu_eq⟩ := Γ.iso.vertexEquiv.surjective ⟨v, hv_not_D.1⟩
  have hval_u : (Γ.iso.vertexEquiv ⟨u, huW⟩).1 = v := congrArg Subtype.val hu_eq
  have hv_eq : v = fig1Sph φ (pos u) := hval_u.symm.trans (hΓv ⟨u, huW⟩)
  have hdraw_v : drawingVertToGraph Γ v = u := by
    rw [← hval_u, drawingVertToGraph_apply_vertexEquiv]
  have hu_in_H' : u ∈ H'.insideVerts := hdraw_v ▸ hinside_of_not_D v hv_not_D
  have hpos_u_fig1 : pos u ∈ shiftHomeo i j '' fig1Set H'.height :=
    pos_mem_shift_fig1Set_of_mem_subwall hpos_branch hΓv hΓe hh' hi_even hj_even hi hj
      hbranch hpaths hbase hu_in_H'.1
  obtain ⟨z_u, hz_u_set, hz_u_eq⟩ := hpos_u_fig1
  have hz_u_enc : z_u ∈ fig1EnclosedSet H'.height :=
    fig1Set_subset_enclosed H'.even_height H'.two_le_height hz_u_set
  obtain ⟨x₀, y₀, hb₀, hz_u_brick⟩ := exists_fig1Brick_of_mem_enclosed hz_u_enc
  obtain ⟨i'', j'', hi''_even, hj''_even, hi''_le, hj''_le, _, hbrick_sub⟩ :=
    exists_subwall_covering_brick H' hh2 hh_even hh_le_H' hb₀
  let H'' := subwallOfShift H' h i'' j'' hh2 hh_even hh_le_H' hi''_even hj''_even hi''_le hj''_le
  have hH''_sub : H''.IsSubwallOf H' :=
    isSubwallOf_subwallOfShift H' h i'' j'' hh2 hh_even hh_le_H' hi''_even hj''_even hi''_le hj''_le
  obtain ⟨A', h_int_A', hvOf_A'_in, hfolio⟩ :=
    hhom.2 h_int_A hvOf_in_H' hH''_sub rfl
  let tA' := (vis.tildeA A').toGraph
  have htA'_mem : tA' ∈ 𝒜_83 := ⟨A', h_int_A'.1, rfl⟩
  obtain ⟨_, hdel_A', _, _⟩ := tildeA_properties hc vis h_int_A'.1
  have h_int_tA' : IsInteriorMember W.toWall 𝒜 (tA'.deleteVerts X) := hdel_A'.symm ▸ h_int_A'
  have hvOf_A'_eq : tildeA_vOfGraph hc vis tA' = vis.vOf A' := by
    unfold tildeA_vOfGraph; split_ifs; rw [hdel_A']
  have hvA'_eq : tildeA_vA hc vis φ pos tA' = fig1Sph φ (pos (vis.vOf A')) := by
    unfold tildeA_vA; rw [hvOf_A'_eq]
  have hvA'_V : tildeA_vA hc vis φ pos tA' ∈ Γ.drawing.V := by
    rw [hvA'_eq, ← hΓv ⟨vis.vOf A', (vis.vOf_valid h_int_A').1⟩]
    exact (Γ.iso.vertexEquiv _).2
  -- Show both `v` and `vA tA'` belong to `(fig1Sph φ ∘ shiftHomeo (i + i'') (j + j'')) '' fig1EnclosedSet h`
  have hshift_eq : ∀ z : ℝ × ℝ,
      shiftHomeo i j (shiftHomeo i'' j'' z) = shiftHomeo (i + i'') (j + j'') z := by
    intro z; ext <;> simp [shiftHomeo_apply] <;> ring
  have hv_enc : v ∈ (fig1Sph φ ∘ shiftHomeo (i + i'') (j + j'')) '' fig1EnclosedSet h := by
    obtain ⟨w_u, hw_u_enc, hw_u_eq⟩ := hbrick_sub hz_u_brick
    refine ⟨w_u, hw_u_enc, ?_⟩
    change fig1Sph φ (shiftHomeo (i + i'') (j + j'') w_u) = v
    rw [← hshift_eq, hw_u_eq, hz_u_eq, hv_eq]
  have hvA'_enc :
      tildeA_vA hc vis φ pos tA' ∈ (fig1Sph φ ∘ shiftHomeo (i + i'') (j + j'')) '' fig1EnclosedSet h := by
    have hpos_A' := pos_mem_double_shift_fig1Set_of_mem_subwallOfShift
      hpos_branch hΓv hΓe hh' hi_even hj_even hi hj hbranch hpaths hbase
      hh2 hh_even hh_le_H' hi''_even hj''_even hi''_le hj''_le hvOf_A'_in.1
    obtain ⟨w_A', hw_A'_set, hw_A'_eq⟩ := hpos_A'
    refine ⟨w_A', fig1Set_subset_enclosed hh_even hh2 hw_A'_set, ?_⟩
    change fig1Sph φ (shiftHomeo (i + i'') (j + j'') w_A') = tildeA_vA hc vis φ pos tA'
    rw [hw_A'_eq, hvA'_eq]
  have hdist_le :
      subsetTangleDist Γ.drawing W.height d {v} {tildeA_vA hc vis φ pos tA'} ≤ 8 * h + 2 :=
    (subsetTangleDist_le_of_mem_shifted_enclosed hpos_branch hΓU hΓv hd
      (hh_le_H'.trans hh') (hi_even.add hi''_even) (hj_even.add hj''_even)
      (by omega) (by omega) hv_not_D.1 hvA'_V hv_enc hvA'_enc).2
  obtain ⟨hlen, hfolio_gm22⟩ :=
    tildeA_subRootedDigraph_hasSameDeltaFolio hc vis h_int_A h_int_A' hfolio
  exact ⟨tA', htA'_mem, hdist_le, hlen, fun htA'_le hmem_A' =>
    hfolio_gm22 htA_le htA'_le hmem_A hmem_A'⟩

end GM22
end GraphMinor
