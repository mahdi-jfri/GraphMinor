module

public import GraphMinor.GM21.Section6GapPieces

/-!
# Graph Minors XXI, (6.3), claim (2): the halves of a support at a vertex

When the surface is cut along a line `F` with an end `a`, the support `F_j*` holding `a` is cut at
`a` into two pieces, one on each side of `F` near `a`. We call them the *halves* of `F_j*` at `a`:
two supports `A₋, A₊` with end `a`, `A₋ ∪ A₊ = F_j*` and `A₋ ∩ A₊ = {a}` (`IsHalves`).

* `exists_halves`: halves exist at each vertex of a support, and the graphs `μ(A₋)`, `μ(A₊)` share
  only vertices of `μ(a)` and no edge. This is (V4) read on angles (`Section6Angles.lean`).
* `exists_halves_pair`: for two vertices `a ≠ b` of one support, the halves can be chosen so that
  `b` is in the half `A₊` at `a` and `a` is in the half `B₋` at `b`. Then the support is the union
  of three pieces `A₋`, `M`, `B₊`, where `M` runs from `a` to `b`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace CutLine

open Set Topology GraphMinor.Surface GraphMinor.GM21.Supports
open GraphMinor.GM19 hiding Drawing

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-- `F` is a support with ends `b, a` when it is one with ends `a, b`. -/
theorem supportHasEnds_swap {Γ : Drawing S} {F : Set S} {a b : S}
    (h : SupportHasEnds Γ F a b) : SupportHasEnds Γ F b a := by
  rcases h with ⟨v, hv, hF, ha, hb⟩ | ⟨hsub, hne, ha, hb, hline⟩
  · exact Or.inl ⟨v, hv, hF, hb, ha⟩
  · exact Or.inr ⟨hsub, hne.symm, hb, ha, hline.symm⟩

/-- The *halves* of a support `I` at a vertex `a`: two supports with end `a`, whose union is `I` and
which meet only in `a`. -/
structure IsHalves (Γ : Drawing S) (I Am Ap : Set S) (a : S) : Prop where
  left : ∃ u, SupportHasEnds Γ Am a u
  right : ∃ w, SupportHasEnds Γ Ap a w
  union : Am ∪ Ap = I
  inter : Am ∩ Ap = {a}

theorem IsHalves.swap {Γ : Drawing S} {I Am Ap : Set S} {a : S} (h : IsHalves Γ I Am Ap a) :
    IsHalves Γ I Ap Am a :=
  ⟨h.right, h.left, by rw [union_comm, h.union], by rw [inter_comm, h.inter]⟩

theorem IsHalves.mem_left {Γ : Drawing S} {I Am Ap : Set S} {a : S} (h : IsHalves Γ I Am Ap a) :
    a ∈ Am :=
  (h.inter.symm ▸ mem_singleton a : a ∈ Am ∩ Ap).1

theorem IsHalves.mem_right {Γ : Drawing S} {I Am Ap : Set S} {a : S} (h : IsHalves Γ I Am Ap a) :
    a ∈ Ap :=
  (h.inter.symm ▸ mem_singleton a : a ∈ Am ∩ Ap).2

theorem IsHalves.left_subset {Γ : Drawing S} {I Am Ap : Set S} {a : S} (h : IsHalves Γ I Am Ap a) :
    Am ⊆ I :=
  h.union ▸ subset_union_left

theorem IsHalves.right_subset {Γ : Drawing S} {I Am Ap : Set S} {a : S}
    (h : IsHalves Γ I Am Ap a) : Ap ⊆ I :=
  h.union ▸ subset_union_right

variable {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
  {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}

/-- The graphs of the halves share only vertices of `μ(a)` and no edge. -/
def HalvesMeetIn (G : Hypergraph α β) (Γ : Drawing S) (μ : BoundaryUnit S → Hypergraph α β)
    (Am Ap : Set S) (a : S) : Prop :=
  (supportGraph G Γ μ Am).vertexSet ∩ (supportGraph G Γ μ Ap).vertexSet ⊆
      (μ (.vertex a)).vertexSet ∧
    Disjoint (supportGraph G Γ μ Am).edgeSet (supportGraph G Γ μ Ap).edgeSet

theorem HalvesMeetIn.swap {Am Ap : Set S} {a : S} (h : HalvesMeetIn G Γ μ Am Ap a) :
    HalvesMeetIn G Γ μ Ap Am a :=
  ⟨by rw [inter_comm]; exact h.1, h.2.symm⟩

/-- A support written with angles, together with the facts about its ends that we use. -/
theorem support_angles (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (j : Fin r) :
    ∃ (C : Set S) (_ : C ∈ cuffs S) (f : Circle ≃ₜ (C : Set S)) (t₀ t₁ : ℝ), t₀ ≤ t₁ ∧
      t₁ < t₀ + 2 * Real.pi ∧ cuffPoint f t₀ ∈ Γ.V ∧ cuffPoint f t₁ ∈ Γ.V ∧
      F_star j = cuffPoint f '' Icc t₀ t₁ := by
  have hS := hP.is_surface
  obtain ⟨u, w, hsup⟩ := hP.supports_isSupport j
  obtain ⟨C, hC, hFC⟩ := exists_cuff_of_supportHasEnds hsup
  obtain ⟨t₀, -, t₁, ht₁, hends, hF, -⟩ :=
    support_eq_cuffPoint_Icc hS hC (cuffHomeo hS hC) hsup hFC
  have hm := ends_mem_of_supportHasEnds hsup
  refine ⟨C, hC, cuffHomeo hS hC, t₀, t₁, ht₁.1, ht₁.2, ?_, ?_, hF⟩
  · rcases hends with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
    exacts [hm.2.2.1.1, hm.2.2.2.1.1]
  · rcases hends with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1]
    exacts [hm.2.2.2.1.1, hm.2.2.1.1]

section angles

variable (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (j : Fin r)
  {C : Set S} (hC : C ∈ cuffs S) (f : Circle ≃ₜ C) {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁)
  (hlt : t₁ < t₀ + 2 * Real.pi) (ht₀V : cuffPoint f t₀ ∈ Γ.V) (ht₁V : cuffPoint f t₁ ∈ Γ.V)
  (hF : F_star j = cuffPoint f '' Icc t₀ t₁)
include hP hC hle hlt ht₀V ht₁V hF

/-- The halves at the point at angle `x`. -/
theorem halves_at {x : ℝ} (hx : x ∈ Icc t₀ t₁) (hxV : cuffPoint f x ∈ Γ.V) :
    IsHalves Γ (F_star j) (cuffPoint f '' Icc t₀ x) (cuffPoint f '' Icc x t₁) (cuffPoint f x) ∧
      HalvesMeetIn G Γ μ (cuffPoint f '' Icc t₀ x) (cuffPoint f '' Icc x t₁) (cuffPoint f x) := by
  have hS := hP.is_surface
  have hsplit := cuffPoint_Icc_split f le_rfl hx.1 hx.2 le_rfl hlt
  have ht₀ : cuffPoint f t₀ ∈ Γ.V ∩ C := ⟨ht₀V, GM17.cuffPoint_mem f t₀⟩
  refine ⟨⟨⟨_, supportHasEnds_swap (supportHasEnds_cuffPoint_Icc hS hC f le_rfl hx.1
    (hx.2.trans le_rfl) hlt ht₀V hxV)⟩, ⟨_, supportHasEnds_cuffPoint_Icc hS hC f hx.1 hx.2 le_rfl
    hlt hxV ht₁V⟩, by rw [hsplit.1, hF], hsplit.2⟩, ?_, ?_⟩
  · exact supportGraph_inter_vertexSet_subset_of_angle_between hP j hC f ht₀ ht₁V hle hlt hF
      le_rfl hx.1 le_rfl le_rfl hx.2 le_rfl rfl rfl hxV
  · exact supportGraph_edgeSet_disjoint_of_angles hP j hC f hlt ht₀ ht₁V hF le_rfl hx.1 hx.2
      le_rfl ht₀V hxV

end angles

/-- **Halves exist** at every vertex of a support. -/
theorem exists_halves (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (j : Fin r) {a : S}
    (ha : a ∈ Γ.V ∩ F_star j) :
    ∃ Am Ap, IsHalves Γ (F_star j) Am Ap a ∧ HalvesMeetIn G Γ μ Am Ap a := by
  obtain ⟨C, hC, f, t₀, t₁, hle, hlt, ht₀V, ht₁V, hF⟩ := support_angles hP j
  have haF := ha.2
  rw [hF] at haF
  obtain ⟨x, hx, rfl⟩ := haF
  exact ⟨_, _, halves_at hP j hC f hle hlt ht₀V ht₁V hF hx ha.1⟩

/-- **Halves at two vertices of one support**, chosen so that `b` is in the half `A₊` at `a` and
`a` is in the half `B₋` at `b`. The middle piece `M` runs from `a` to `b`. -/
theorem exists_halves_pair (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (j : Fin r)
    {a b : S} (ha : a ∈ Γ.V ∩ F_star j) (hb : b ∈ Γ.V ∩ F_star j) (hab : a ≠ b) :
    ∃ Am Ap Bm Bp M : Set S, IsHalves Γ (F_star j) Am Ap a ∧ HalvesMeetIn G Γ μ Am Ap a ∧
      IsHalves Γ (F_star j) Bm Bp b ∧ HalvesMeetIn G Γ μ Bm Bp b ∧
      SupportHasEnds Γ M a b ∧ Am ∪ M = Bm ∧ Am ∩ M = {a} ∧ M ∪ Bp = Ap ∧ M ∩ Bp = {b} ∧
      Disjoint Am Bp := by
  obtain ⟨C, hC, f, t₀, t₁, hle, hlt, ht₀V, ht₁V, hF⟩ := support_angles hP j
  have hS := hP.is_surface
  have haF := ha.2
  have hbF := hb.2
  rw [hF] at haF hbF
  obtain ⟨x, hx, rfl⟩ := haF
  obtain ⟨y, hy, rfl⟩ := hbF
  have hxy : x ≠ y := fun h => hab (by rw [h])
  obtain ⟨hA, hA'⟩ := halves_at hP j hC f hle hlt ht₀V ht₁V hF hx ha.1
  obtain ⟨hB, hB'⟩ := halves_at hP j hC f hle hlt ht₀V ht₁V hF hy hb.1
  rcases lt_or_gt_of_ne hxy with hlt' | hlt'
  · have h1 := cuffPoint_Icc_split f le_rfl hx.1 hlt'.le hy.2 hlt
    have h2 := cuffPoint_Icc_split f hx.1 hlt'.le hy.2 le_rfl hlt
    refine ⟨_, _, _, _, cuffPoint f '' Icc x y, hA, hA', hB, hB',
      supportHasEnds_cuffPoint_Icc hS hC f hx.1 hlt'.le hy.2 hlt ha.1 hb.1, h1.1, h1.2, h2.1, h2.2,
      Gap.disjoint_pieces f hx.1 hlt' hy.2 hlt⟩
  · have h1 := cuffPoint_Icc_split f hy.1 hlt'.le hx.2 le_rfl hlt
    have h2 := cuffPoint_Icc_split f le_rfl hy.1 hlt'.le hx.2 hlt
    refine ⟨_, _, _, _, cuffPoint f '' Icc y x, hA.swap, hA'.swap, hB.swap, hB'.swap,
      supportHasEnds_swap (supportHasEnds_cuffPoint_Icc hS hC f hy.1 hlt'.le hx.2 hlt hb.1 ha.1),
      by rw [union_comm, h1.1], by rw [inter_comm, h1.2], by rw [union_comm, h2.1],
      by rw [inter_comm, h2.2], (Gap.disjoint_pieces f hy.1 hlt' hx.2 hlt).symm⟩

end CutLine
end GM21
end GraphMinor
