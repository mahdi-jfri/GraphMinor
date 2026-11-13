module

public import GraphMinor.GM21.Section6Supports
import GraphMinor.GM10.TangleLemmas

/-!
# Graph Minors XXI, Section 6: the graphs `μ(I)` of the parts `I` of a support

In the proofs of (6.4)–(6.7) a support `F*` of a presentation is cut into smaller supports
`I ⊆ F*`, and the graphs `μ(I)` are compared. This file collects what is used about them, for a
support `F* = F_j*` written by angles, `F* = {cuffPoint f t : t₀ ≤ t ≤ t₁}`:

- `μ(I)` is a subgraph of `G` (`supportGraph_le`), grows with `I` (`supportGraph_mono`), has no
  edge of `Γ` (`supportGraph_edgeSet_disjoint`), and meets `Γ` only in the vertices of `Γ` in `I`
  (`supportGraph_vertexSet_inter_subset`);
- if `I₁` and `I₂` are supports of `F*` that meet in one vertex `w`, then `μ(I₁)` and `μ(I₂)`
  have no common edge (`supportGraph_edgeSet_disjoint_of_angles`). This is the edge part of
  "(and consequently $E(\mu(s_1) \cap \mu(s_2)) = \emptyset$)" in (V4) (page 22 of the preprint);
  the vertex part is `Supports.supportGraph_inter_vertexSet_subset_of_angle_between`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Hypergraph GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM21.Supports

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}

section general

variable (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (j : Fin r)
include h_pres

/-- `μ(u)` is a subgraph of `G` for `u ∈ V(Γ) ∩ F_j*`. -/
theorem μ_vertex_le {u : S} (hu : u ∈ Γ.V ∩ F_star j) : μ (.vertex u) ≤ G :=
  (h_pres.μ_vertex_sub j u hu).1.trans (h_pres.v1_sub j)

/-- `μ(s)` is a subgraph of `G` for a space `s ⊆ F_j*`. -/
theorem μ_space_le {s : Set S} (hs : s ∈ drawingSpaces Γ) (hsF : s ⊆ F_star j) :
    μ (.space s) ≤ G :=
  (h_pres.μ_space_sub j s hs hsF).trans (h_pres.v1_sub j)

/-- `ιV u` is a vertex of `μ(u)`. -/
theorem ιV_mem_μ_vertex {u : S} (hu : u ∈ Γ.V ∩ F_star j) :
    ιV u ∈ (μ (.vertex u)).vertexSet := by
  have h : ιV u ∈ (μ (.vertex u)).vertexSet ∩ Γ_sub.vertexSet := by
    rw [(h_pres.μ_vertex_sub j u hu).2.2.2]
    exact mem_singleton _
  exact h.1

/-- An edge of `μ(I)` is an edge of `μ(s)` for a space `s ⊆ I`. -/
theorem exists_space_of_mem_edgeSet {I : Set S} (hI : I ⊆ F_star j) {e : β}
    (he : e ∈ (supportGraph G Γ μ I).edgeSet) :
    ∃ s ∈ drawingSpaces Γ, s ⊆ I ∧ e ∈ (μ (.space s)).edgeSet := by
  rcases he.2 with h | h
  · rw [mem_iUnion₂] at h
    obtain ⟨s, ⟨hs, hsI⟩, hes⟩ := h
    exact ⟨s, hs, hsI, hes⟩
  · rw [mem_iUnion₂] at h
    obtain ⟨u, hu, heu⟩ := h
    rw [(h_pres.μ_vertex_sub j u ⟨hu.1, hI hu.2⟩).2.1] at heu
    exact heu.elim

/-- `μ(I)` is a subgraph of `G` for `I ⊆ F_j*`. -/
theorem supportGraph_le {I : Set S} (hI : I ⊆ F_star j) : supportGraph G Γ μ I ≤ G where
  vertexSet_subset := inter_subset_left
  edgeSet_subset := inter_subset_left
  ends_eq e he := by
    ext x
    simp only [Hypergraph.ends, mem_ofPred_eq, supportGraph]
    refine ⟨fun hx => ⟨hx, ?_⟩, fun h => h.1⟩
    obtain ⟨s, hs, hsI, hes⟩ := exists_space_of_mem_edgeSet h_pres j hI he
    exact Or.inl ⟨s, hs, hsI, (GM10.inc_iff_of_le (μ_space_le h_pres j hs (hsI.trans hI)) hes).2 hx⟩

/-- `μ(I) ≤ μ(I')` for `I ⊆ I' ⊆ F_j*`. -/
theorem supportGraph_mono {I I' : Set S} (hI' : I' ⊆ F_star j) (h : I ⊆ I') :
    supportGraph G Γ μ I ≤ supportGraph G Γ μ I' := by
  rw [GM10.le_iff_of_le (supportGraph_le h_pres j (h.trans hI')) (supportGraph_le h_pres j hI')]
  constructor
  · rintro x ⟨hxG, hx | hx⟩
    · rw [mem_iUnion₂] at hx
      obtain ⟨s, ⟨hs, hsI⟩, hxs⟩ := hx
      exact ⟨hxG, Or.inl (mem_biUnion (x := s) ⟨hs, hsI.trans h⟩ hxs)⟩
    · rw [mem_iUnion₂] at hx
      obtain ⟨u, ⟨huV, huI⟩, hxu⟩ := hx
      exact ⟨hxG, Or.inr (mem_biUnion (x := u) ⟨huV, h huI⟩ hxu)⟩
  · rintro e ⟨heG, he | he⟩
    · rw [mem_iUnion₂] at he
      obtain ⟨s, ⟨hs, hsI⟩, hes⟩ := he
      exact ⟨heG, Or.inl (mem_biUnion (x := s) ⟨hs, hsI.trans h⟩ hes)⟩
    · rw [mem_iUnion₂] at he
      obtain ⟨u, ⟨huV, huI⟩, heu⟩ := he
      exact ⟨heG, Or.inr (mem_biUnion (x := u) ⟨huV, h huI⟩ heu)⟩

/-- `μ(u) ≤ μ(I)` for `u ∈ V(Γ) ∩ I`. -/
theorem μ_vertex_le_supportGraph_of_subset {I : Set S} (hI : I ⊆ F_star j) {u : S} (hu : u ∈ Γ.V ∩ I) :
    μ (.vertex u) ≤ supportGraph G Γ μ I := by
  have hle := μ_vertex_le h_pres j ⟨hu.1, hI hu.2⟩
  rw [GM10.le_iff_of_le hle (supportGraph_le h_pres j hI)]
  refine ⟨fun x hx => ⟨hle.vertexSet_subset hx, Or.inr (mem_biUnion (x := u) hu hx)⟩, ?_⟩
  rw [(h_pres.μ_vertex_sub j u ⟨hu.1, hI hu.2⟩).2.1]
  exact empty_subset _

/-- `μ(I)` has no edge of `Γ`. -/
theorem supportGraph_edgeSet_disjoint {I : Set S} (hI : I ⊆ F_star j) :
    Disjoint (supportGraph G Γ μ I).edgeSet Γ_sub.edgeSet := by
  rw [Set.disjoint_left]
  intro e he heΓ
  obtain ⟨s, hs, hsI, hes⟩ := exists_space_of_mem_edgeSet h_pres j hI he
  exact Set.disjoint_left.mp (h_pres.v1_inter_E j)
    ((h_pres.μ_space_sub j s hs (hsI.trans hI)).edgeSet_subset hes) heΓ

/-- `μ(I)` meets `Γ` only in the vertices of `Γ` in `I`, for a closed `I ⊆ F_j*`. -/
theorem supportGraph_vertexSet_inter_subset {I : Set S} (hI : I ⊆ F_star j) (hIc : IsClosed I) :
    (supportGraph G Γ μ I).vertexSet ∩ Γ_sub.vertexSet ⊆ ιV '' (Γ.V ∩ I) := by
  rintro x ⟨⟨-, hx | hx⟩, hxΓ⟩
  · rw [mem_iUnion₂] at hx
    obtain ⟨s, ⟨hs, hsI⟩, hxs⟩ := hx
    obtain ⟨u₁, u₂, hs_ends⟩ :=
      exists_spaceHasEnds_of_mem_drawingSpaces h_pres.is_surface h_pres.cuff_vertices_ge_two hs
    have hx_ends : x ∈ ({ιV u₁, ιV u₂} : Set α) := by
      rw [← (h_pres.v3_space j s hs u₁ u₂ (hsI.trans hI) hs_ends).1]
      exact ⟨hxs, hxΓ⟩
    have hcl : closure s ⊆ I := closure_minimal hsI hIc
    rw [hs_ends.2.2.2.2.2] at hcl
    rcases hx_ends with rfl | rfl
    · exact ⟨u₁, ⟨hs_ends.2.1.1, hcl (Or.inr (Or.inl rfl))⟩, rfl⟩
    · exact ⟨u₂, ⟨hs_ends.2.2.1.1, hcl (Or.inr (Or.inr rfl))⟩, rfl⟩
  · rw [mem_iUnion₂] at hx
    obtain ⟨u, hu, hxu⟩ := hx
    have h : x ∈ (μ (.vertex u)).vertexSet ∩ Γ_sub.vertexSet := ⟨hxu, hxΓ⟩
    rw [(h_pres.μ_vertex_sub j u ⟨hu.1, hI hu.2⟩).2.2.2, mem_singleton_iff] at h
    exact ⟨u, hu, h.symm⟩

end general

/-- The part of `F_j*` between angles `x ≤ y` lies in `F_j*`. -/
theorem image_Icc_subset (j : Fin r) {C : Set S} (f : Circle ≃ₜ C) {t₀ t₁ : ℝ}
    (hF : F_star j = GM19.cuffPoint f '' Icc t₀ t₁) {x y : ℝ} (hx : t₀ ≤ x) (hy : y ≤ t₁) :
    GM19.cuffPoint f '' Icc x y ⊆ F_star j := by
  rw [hF]
  exact image_mono (Icc_subset_Icc hx hy)

section angles

variable (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (j : Fin r)
  {C : Set S} (hC : C ∈ cuffs S) (f : Circle ≃ₜ C) {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁)
  (hlt : t₁ < t₀ + 2 * Real.pi) (ht₀ : GM19.cuffPoint f t₀ ∈ Γ.V ∩ C)
  (ht₁ : GM19.cuffPoint f t₁ ∈ Γ.V) (hF : F_star j = GM19.cuffPoint f '' Icc t₀ t₁)
include h_pres hC hle hlt ht₀ ht₁ hF

omit hle in
/-- **The edge part of (V4).** If `t₀ ≤ a ≤ c ≤ b ≤ t₁` and the points of angles `a, c, b` are
vertices of `Γ`, then `μ` of the part of `F_j*` between angles `a, c` and `μ` of the part between
angles `c, b` have no common edge. -/
theorem supportGraph_edgeSet_disjoint_of_angles {a c b : ℝ} (ha : t₀ ≤ a) (hac : a ≤ c)
    (hcb : c ≤ b) (hb : b ≤ t₁) (haV : GM19.cuffPoint f a ∈ Γ.V)
    (hcV : GM19.cuffPoint f c ∈ Γ.V) :
    Disjoint (supportGraph G Γ μ (GM19.cuffPoint f '' Icc a c)).edgeSet
      (supportGraph G Γ μ (GM19.cuffPoint f '' Icc c b)).edgeSet := by
  have hS := h_pres.is_surface
  have hge2 := h_pres.cuff_vertices_ge_two
  have hI₁ := image_Icc_subset j f hF ha (hcb.trans hb)
  have hI₂ := image_Icc_subset j f hF (ha.trans hac) hb
  rw [Set.disjoint_left]
  intro e he₁ he₂
  obtain ⟨s₁, hs₁, hs₁I, hes₁⟩ := exists_space_of_mem_edgeSet h_pres j hI₁ he₁
  obtain ⟨s₂, hs₂, hs₂I, hes₂⟩ := exists_space_of_mem_edgeSet h_pres j hI₂ he₂
  obtain ⟨a₁, b₁, ha₁, hab₁, hb₁, -, -, -, hs₁_eq, -⟩ := space_in_support_eq_Ioo hS hge2 hC f hac
    (by linarith) ⟨haV, GM17.cuffPoint_mem f a⟩ rfl hs₁ hs₁I
  obtain ⟨a₂, b₂, ha₂, hab₂, hb₂, -, -, -, hs₂_eq, -⟩ := space_in_support_eq_Ioo hS hge2 hC f hcb
    (by linarith) ⟨hcV, GM17.cuffPoint_mem f c⟩ rfl hs₂ hs₂I
  have hbetween : LiesBetweenInSupport Γ (F_star j) s₁ s₂ (GM19.cuffPoint f c) :=
    liesBetweenInSupport_of_angles hS hC f hlt ht₀.1 ht₁ hF hs₁ hs₂ (by linarith) hab₁ hb₁ ha₂
      hab₂ (by linarith) hs₁_eq hs₂_eq hcV
  have hcF : GM19.cuffPoint f c ∈ Γ.V ∩ F_star j :=
    ⟨hcV, by rw [hF]; exact ⟨c, ⟨by linarith, by linarith⟩, rfl⟩⟩
  have hle' := h_pres.v4_between j s₁ s₂ (GM19.cuffPoint f c) hbetween
  have : e ∈ (μ (.vertex (GM19.cuffPoint f c))).edgeSet := hle'.edgeSet_subset ⟨hes₁, hes₂⟩
  rw [(h_pres.μ_vertex_sub j _ hcF).2.1] at this
  exact this

end angles

/-- A point of a space is not a vertex of `Γ`. -/
theorem notMem_V_of_mem_space {s : Set S} (hs : s ∈ drawingSpaces Γ) {x : S} (hx : x ∈ s) :
    x ∉ Γ.V :=
  (subset_bd_diff_of_mem_drawingSpaces hs hx).2

end GM21
end GraphMinor
