module

public import GraphMinor.GM21.Section6DiscSetup
import GraphMinor.GM10.TangleLemmas

/-!
# Graph Minors XXI, proofs of (6.4)–(6.7): the separations cut by a line

We keep the setting of `Section6DiscSetup`: a presentation of `G` in a disc `Σ`, read in a window
of angles in which `F_j*` is the set of points with angles in `[a j, b j]`. The paper cuts `Σ` by
good lines. In the proof of (6.4) (page 24 of the preprint):
"A line $F \subseteq \Sigma$ is *good* if it is proper, both its ends are in $V(\Gamma)$, and no
internal point is in $U(\Gamma)$. ... Define
$$\begin{aligned}
A(F) &= (\Gamma \cap \overline{\Sigma \setminus \Delta(F)}) \cup \mu(J(F)) \\
B(F) &= (\Gamma \cap \Delta(F)) \cup \mu(K(F)) \\
X(F) &= V(A(F) \cap B(F)).
\end{aligned}$$"
The same separations appear in the proof of (6.5) for lines from `F_1*` to `F_2*`.

A good line meets `Γ` only in its two ends, so the part of `Γ` on one side of it is formed by
the `Σ`-jumps whose ends lie on that side. We describe a good line with ends at angles `x < y` by
a cut (`Cuts.Cut`): `B(c)` (`cutB`) is formed by the jumps inside `[x, y]` and by `μ` of the part
of each support with angles in `[x, y]` (`piece`); `A(c)` (`cutA`) is formed by everything else,
together with `X(c) = V(μ(u₁) ∪ μ(u₂))` (`cutX`), where `u₁, u₂` are the points of angles
`x, y`. A cut is admissible when no jump crosses it, which is what a good line gives.

- Claim (1) of (6.4), "(1) *(A(F), B(F)) is a separation of $G$, and
  $X(F) = V(\mu(u_1) \cup \mu(u_2))$ where $F$ has ends $u_1, u_2$.*", whose proof the paper omits,
  is `isSeparation_cut`.
- Claim (2) of (6.4), "$A(F) \subseteq A(F')$ and $B(F') \subseteq B(F)$", is `cut_nested`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace DiscCut

open Set Topology Hypergraph GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM21.Supports
open GraphMinor.GM21.Cuts

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-- The part of `F_j*` with angles between `x` and `y`. -/
def piece {r : ℕ} (f : Circle ≃ₜ bd S) (a b : Fin r → ℝ) (j : Fin r) (x y : ℝ) : Set S :=
  GM19.cuffPoint f '' Icc (max (a j) x) (min (b j) y)

/-- The vertices of `B(c)`: the vertices of the jumps inside `c` and of `μ` of the parts of the
supports between the angles `c.x` and `c.y`. -/
def cutW {r : ℕ} (G : Hypergraph α β) (Γ : Drawing S) (μ : BoundaryUnit S → Hypergraph α β)
    (f : Circle ≃ₜ bd S) (a b : Fin r → ℝ) (T : Set (Hypergraph α β))
    (lo hi : Hypergraph α β → ℝ) (c : Cut) : Set α :=
  (⋃ J ∈ insideSet lo hi T c, J.vertexSet) ∪
    ⋃ j, (supportGraph G Γ μ (piece f a b j c.x c.y)).vertexSet

/-- The edges of `B(c)`. -/
def cutF {r : ℕ} (G : Hypergraph α β) (Γ : Drawing S) (μ : BoundaryUnit S → Hypergraph α β)
    (f : Circle ≃ₜ bd S) (a b : Fin r → ℝ) (T : Set (Hypergraph α β))
    (lo hi : Hypergraph α β → ℝ) (c : Cut) : Set β :=
  (⋃ J ∈ insideSet lo hi T c, J.edgeSet) ∪
    ⋃ j, (supportGraph G Γ μ (piece f a b j c.x c.y)).edgeSet

/-- `X(c) = V(μ(u₁) ∪ μ(u₂))`, where `u₁, u₂` are the points of angles `c.x, c.y`. -/
def cutX (μ : BoundaryUnit S → Hypergraph α β) (f : Circle ≃ₜ bd S) (c : Cut) : Set α :=
  (μ (.vertex (GM19.cuffPoint f c.x))).vertexSet ∪ (μ (.vertex (GM19.cuffPoint f c.y))).vertexSet

/-- `B(c)`, the side of the separation inside the cut. -/
def cutB {r : ℕ} (G : Hypergraph α β) (Γ : Drawing S) (μ : BoundaryUnit S → Hypergraph α β)
    (f : Circle ≃ₜ bd S) (a b : Fin r → ℝ) (T : Set (Hypergraph α β))
    (lo hi : Hypergraph α β → ℝ) (c : Cut) : Hypergraph α β :=
  subOn G (cutW G Γ μ f a b T lo hi c) (cutF G Γ μ f a b T lo hi c)

/-- `A(c)`, the side of the separation outside the cut. -/
def cutA {r : ℕ} (G : Hypergraph α β) (Γ : Drawing S) (μ : BoundaryUnit S → Hypergraph α β)
    (f : Circle ≃ₜ bd S) (a b : Fin r → ℝ) (T : Set (Hypergraph α β))
    (lo hi : Hypergraph α β → ℝ) (c : Cut) : Hypergraph α β :=
  subOn G (G.vertexSet \ (cutW G Γ μ f a b T lo hi c \ cutX μ f c))
    (G.edgeSet \ cutF G Γ μ f a b T lo hi c)

private theorem nonempty_of_mem_drawingSpaces' {Γ : Drawing S} {s : Set S}
    (hs : s ∈ drawingSpaces Γ) : s.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := hs
  exact ⟨x, mem_connectedComponentIn hx⟩

section claims

variable {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
  (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
  (hC : bd S ∈ cuffs S) {f : Circle ≃ₜ bd S} {w₀ w₁ : ℝ} {a b : Fin r → ℝ}
  (hW : Window Γ F_star f w₀ w₁ a b)
  (hK : IsLinkage G Γ_sub)
  (hdeg : ∀ y ∈ Γ_sub.vertexSet, y ∉ ιV '' (Γ.V ∩ bd S) → (incidentEdges Γ_sub y).ncard = 2)

set_option hygiene false in
local notation "𝒯" => jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))
set_option hygiene false in
local notation "LO" => jumpLo f w₀ w₁ Γ.V ιV
set_option hygiene false in
local notation "HI" => jumpHi f w₀ w₁ Γ.V ιV
set_option hygiene false in
local notation "POS" => {t : ℝ | t ∈ Icc w₀ w₁ ∧ GM19.cuffPoint f t ∈ Γ.V}
set_option hygiene false in
local notation "cp" => GM19.cuffPoint f
set_option hygiene false in
local notation "WW" => cutW G Γ μ f a b 𝒯 LO HI
set_option hygiene false in
local notation "FF" => cutF G Γ μ f a b 𝒯 LO HI

omit [TopologicalSpace S] in
/-- The facts about an admissible cut that we use. -/
theorem admissible_bounds' {c : Cut} {T : Set (Hypergraph α β)} {lo hi : Hypergraph α β → ℝ}
    {V : Set S} {g : ℝ → S} (hc : Admissible lo hi T {t : ℝ | t ∈ Icc w₀ w₁ ∧ g t ∈ V} c) :
    w₀ ≤ c.x ∧ c.x < c.y ∧ c.y ≤ w₁ ∧ g c.x ∈ V ∧ g c.y ∈ V :=
  ⟨hc.1.1.1, hc.2.2.1, hc.2.1.1.2, hc.1.2, hc.2.1.2⟩

include hW

/-- `piece j x y` lies in `F_j*`. -/
theorem piece_subset (j : Fin r) (x y : ℝ) : piece f a b j x y ⊆ F_star j := by
  rw [hW.F_eq j]
  exact image_mono (Icc_subset_Icc (le_max_left _ _) (min_le_left _ _))

omit hW in
/-- `piece j x y` is closed. -/
theorem isClosed_piece [T2Space S] (j : Fin r) (x y : ℝ) : IsClosed (piece f a b j x y) :=
  (isCompact_Icc.image (GM17.cuffPoint_continuous f)).isClosed

omit hW in
/-- `piece j x y` grows with the interval `[x, y]`. -/
theorem piece_mono (j : Fin r) {x y x' y' : ℝ} (hx : x ≤ x') (hy : y' ≤ y) :
    piece f a b j x' y' ⊆ piece f a b j x y :=
  image_mono (Icc_subset_Icc (max_le_max le_rfl hx) (min_le_min le_rfl hy))

omit hW in
/-- If `[x, y] ⊆ [a j, b j]`, then `piece j x y` is the set of points with angles in `[x, y]`. -/
theorem piece_eq (j : Fin r) {x y : ℝ} (hx : a j ≤ x) (hy : y ≤ b j) :
    piece f a b j x y = cp '' Icc x y := by
  rw [piece, max_eq_right hx, min_eq_right hy]

include h_pres

/-- **(H2)** A vertex of `Γ` in `W(c)` is an inner vertex of a jump inside `c`, or `ιV` of a
vertex of `Γ` with angle between `c.x` and `c.y`. -/
theorem mem_cutW_of_mem_drawing {c : Cut} {v : α} (hv : v ∈ WW c) (hvΓ : v ∈ Γ_sub.vertexSet) :
    (∃ J ∈ insideSet LO HI 𝒯 c, v ∈ J.vertexSet ∧ v ∉ ιV '' (Γ.V ∩ bd S)) ∨
      ∃ t ∈ Icc c.x c.y, cp t ∈ Γ.V ∧ v = ιV (cp t) := by
  have : T2Space S := h_pres.is_surface.2.1
  rcases hv with hv | hv
  · rw [mem_iUnion₂] at hv
    obtain ⟨J, hJ, hvJ⟩ := hv
    by_cases hvB : v ∈ ιV '' (Γ.V ∩ bd S)
    · right
      have hspec := hW.jumpAngles_spec h_pres hJ.1
      obtain ⟨u, hu, rfl⟩ := hvB
      rcases hW.eq_end_of_mem_jump h_pres hJ.1 hu hvJ with h | h
      · exact ⟨LO J, ⟨hJ.2.1, hspec.2.1.le.trans hJ.2.2.1⟩, hspec.2.2.2.1, by rw [h]⟩
      · exact ⟨HI J, ⟨hJ.2.1.trans hspec.2.1.le, hJ.2.2.1⟩, hspec.2.2.2.2.1, by rw [h]⟩
    · exact Or.inl ⟨J, hJ, hvJ, hvB⟩
  · right
    rw [mem_iUnion] at hv
    obtain ⟨j, hv⟩ := hv
    obtain ⟨u, ⟨huV, t, ht, rfl⟩, rfl⟩ :=
      supportGraph_vertexSet_inter_subset h_pres j (piece_subset hW j c.x c.y)
        (isClosed_piece j c.x c.y) ⟨hv, hvΓ⟩
    exact ⟨t, ⟨(le_max_right _ _).trans ht.1, ht.2.trans (min_le_right _ _)⟩, huV, rfl⟩

/-- `ιV` of a vertex of `Γ` at an angle `t` of `F_j*` lies in `μ` of the part of `F_j*` between
angles `t` and `t`. -/
theorem ιV_mem_supportGraph {j : Fin r} {t : ℝ} (ht : t ∈ Icc (a j) (b j)) (htV : cp t ∈ Γ.V) :
    ιV (cp t) ∈ (supportGraph G Γ μ (cp '' Icc t t)).vertexSet := by
  have hsub : cp '' Icc t t ⊆ F_star j := by
    rw [hW.F_eq j]
    exact image_mono (Icc_subset_Icc ht.1 ht.2)
  have hmem : cp t ∈ Γ.V ∩ cp '' Icc t t := ⟨htV, t, ⟨le_rfl, le_rfl⟩, rfl⟩
  exact (μ_vertex_le_supportGraph_of_subset h_pres j hsub hmem).vertexSet_subset
    (ιV_mem_μ_vertex h_pres j ⟨htV, hsub hmem.2⟩)

omit hW in
/-- `μ` of a part of `F_j*` is a subgraph of `H_j`. -/
theorem supportGraph_le_H {j : Fin r} {I : Set S} (hI : I ⊆ F_star j) :
    supportGraph G Γ μ I ≤ H j := by
  rw [h_pres.v2_eq j]
  exact supportGraph_mono h_pres j subset_rfl hI

omit h_pres hW in
/-- `supportGraph` of the empty set has no vertex. -/
theorem supportGraph_empty : (supportGraph G Γ μ (∅ : Set S)).vertexSet = ∅ := by
  ext v
  simp only [supportGraph, mem_empty_iff_false, iff_false]
  rintro ⟨-, hv | hv⟩
  · rw [mem_iUnion₂] at hv
    obtain ⟨s, ⟨hs, hs0⟩, -⟩ := hv
    obtain ⟨x, hx⟩ := nonempty_of_mem_drawingSpaces' hs
    exact hs0 hx
  · rw [mem_iUnion₂] at hv
    obtain ⟨u, hu, -⟩ := hv
    exact hu.2

/-- **(H5)** A vertex of `H_j` in `W(c)` lies in `μ` of a part of `F_j*` between angles
`p ≤ p'` with `c.x ≤ p` and `p' ≤ c.y`. -/
theorem exists_part_of_mem_cutW {c : Cut} {j : Fin r} {v : α} (hv : v ∈ WW c)
    (hvH : v ∈ (H j).vertexSet) :
    ∃ p p' : ℝ, max (a j) c.x ≤ p ∧ p ≤ p' ∧ p' ≤ min (b j) c.y ∧
      v ∈ (supportGraph G Γ μ (cp '' Icc p p')).vertexSet := by
  rcases hv with hv | hv
  · rw [mem_iUnion₂] at hv
    obtain ⟨J, hJ, hvJ⟩ := hv
    have hvΓ : v ∈ Γ_sub.vertexSet := hJ.1.1.vertexSet_subset hvJ
    have h : v ∈ (H j).vertexSet ∩ Γ_sub.vertexSet := ⟨hvH, hvΓ⟩
    rw [h_pres.v1_inter_V j] at h
    obtain ⟨u, ⟨huV, huF⟩, rfl⟩ := h
    have huF' := huF
    rw [hW.F_eq j] at huF'
    obtain ⟨t, ht, rfl⟩ := huF'
    have htW := hW.Icc_subset j ht
    have hspec := hW.jumpAngles_spec h_pres hJ.1
    have htc : t ∈ Icc c.x c.y := by
      rcases hW.eq_angle_of_mem_jump h_pres hJ.1 htW huV hvJ with h | h
      · exact ⟨h ▸ hJ.2.1, h ▸ hspec.2.1.le.trans hJ.2.2.1⟩
      · exact ⟨h ▸ hJ.2.1.trans hspec.2.1.le, h ▸ hJ.2.2.1⟩
    exact ⟨t, t, max_le ht.1 htc.1, le_rfl, le_min ht.2 htc.2,
      ιV_mem_supportGraph h_pres hW ht huV⟩
  · rw [mem_iUnion] at hv
    obtain ⟨j', hv⟩ := hv
    have hvH' : v ∈ (H j').vertexSet :=
      (supportGraph_le_H h_pres (piece_subset hW j' c.x c.y)).vertexSet_subset hv
    have hjj : j' = j := by
      by_contra hne
      exact Set.disjoint_left.mp (h_pres.v1_disjoint hne) hvH' hvH
    subst hjj
    refine ⟨max (a j') c.x, min (b j') c.y, le_rfl, ?_, le_rfl, hv⟩
    by_contra hlt
    push Not at hlt
    have : piece f a b j' c.x c.y = ∅ := by
      rw [piece, Icc_eq_empty (not_le.2 hlt), image_empty]
    rw [this, supportGraph_empty] at hv
    exact hv

include hC

/-- **(H4)** A vertex of `μ` of a part of `F_j*` outside the cut `c` and of `μ` of a part of
`F_j*` inside `c` is in `X(c)`. -/
theorem mem_cutX_of_outside {c : Cut} (hc : Admissible LO HI 𝒯 POS c) {j : Fin r}
    {a' b' p p' : ℝ} (ha : a j ≤ a') (hab : a' ≤ b') (hb : b' ≤ b j)
    (hout : b' ≤ c.x ∨ c.y ≤ a') (hp : max (a j) c.x ≤ p)
    (hpp : p ≤ p') (hp' : p' ≤ min (b j) c.y) {v : α}
    (hv : v ∈ (supportGraph G Γ μ (cp '' Icc a' b')).vertexSet)
    (hv' : v ∈ (supportGraph G Γ μ (cp '' Icc p p')).vertexSet) :
    v ∈ cutX μ f c := by
  have hcb := admissible_bounds' hc
  have hlt : b j < a j + 2 * Real.pi := by
    linarith [hW.lt_add, hW.le_a j, hW.b_le j]
  have haj : cp (a j) ∈ Γ.V ∩ bd S := ⟨hW.a_mem j, GM17.cuffPoint_mem f _⟩
  rcases hout with h | h
  · exact Or.inl (supportGraph_inter_vertexSet_subset_of_angle_between h_pres j hC f haj
      (hW.b_mem j) (hW.a_le_b j) hlt (hW.F_eq j) ha hab h ((le_max_right _ _).trans hp) hpp
      (hp'.trans (min_le_left _ _)) rfl rfl hcb.2.2.2.1 ⟨hv, hv'⟩)
  · exact Or.inr (supportGraph_inter_vertexSet_subset_of_angle_between h_pres j hC f haj
      (hW.b_mem j) (hW.a_le_b j) hlt (hW.F_eq j) ((le_max_left _ _).trans hp) hpp
      (hp'.trans (min_le_right _ _)) h hab hb rfl rfl hcb.2.2.2.2 ⟨hv', hv⟩)

omit hC hW in
/-- The vertices of `B(c)` are vertices of `G`. -/
theorem cutW_subset {c : Cut} : WW c ⊆ G.vertexSet := by
  rintro v (hv | hv)
  · rw [mem_iUnion₂] at hv
    obtain ⟨J, hJ, hvJ⟩ := hv
    exact h_pres.drawing_subgraph.vertexSet_subset (hJ.1.1.vertexSet_subset hvJ)
  · rw [mem_iUnion] at hv
    obtain ⟨j, hv⟩ := hv
    exact hv.1

omit hC in
/-- The point of angle `t` of a vertex position lies in the piece of its support for any cut
around `t`. -/
theorem exists_piece_of_pos {t x y : ℝ} (ht : t ∈ Icc w₀ w₁) (htV : cp t ∈ Γ.V) (hx : x ≤ t)
    (hy : t ≤ y) : ∃ j, t ∈ Icc (a j) (b j) ∧ cp t ∈ Γ.V ∩ piece f a b j x y := by
  obtain ⟨j, hj⟩ := hW.exists_support h_pres ht htV
  exact ⟨j, hj, htV, t, ⟨max_le hj.1 hx, le_min hj.2 hy⟩, rfl⟩

omit hC in
/-- `X(c) ⊆ V(B(c))`. -/
theorem cutX_subset_cutW {c : Cut} (hc : Admissible LO HI 𝒯 POS c) : cutX μ f c ⊆ WW c := by
  have hb := admissible_bounds' hc
  rintro v (hv | hv)
  · obtain ⟨j, -, hmem⟩ := exists_piece_of_pos h_pres hW ⟨hb.1, hb.2.1.le.trans hb.2.2.1⟩
      hb.2.2.2.1 le_rfl hb.2.1.le
    refine Or.inr (mem_iUnion.2 ⟨j, ?_⟩)
    exact (μ_vertex_le_supportGraph_of_subset h_pres j (piece_subset hW j _ _) hmem).vertexSet_subset hv
  · obtain ⟨j, -, hmem⟩ := exists_piece_of_pos h_pres hW ⟨hb.1.trans hb.2.1.le, hb.2.2.1⟩
      hb.2.2.2.2 hb.2.1.le le_rfl
    refine Or.inr (mem_iUnion.2 ⟨j, ?_⟩)
    exact (μ_vertex_le_supportGraph_of_subset h_pres j (piece_subset hW j _ _) hmem).vertexSet_subset hv

omit hC in
/-- The ends of the edges of `B(c)` are vertices of `B(c)`. -/
theorem ends_subset_cutW {c : Cut} :
    ∀ e ∈ FF c, e ∈ G.edgeSet → G.ends e ⊆ WW c := by
  rintro e (he | he) _ x hx
  · rw [mem_iUnion₂] at he
    obtain ⟨J, hJ, heJ⟩ := he
    have hJG : J ≤ G := hJ.1.1.trans h_pres.drawing_subgraph
    exact Or.inl (mem_biUnion hJ (J.vertex_mem_of_inc ((GM10.inc_iff_of_le hJG heJ).2 hx)))
  · rw [mem_iUnion] at he
    obtain ⟨j, he⟩ := he
    have hle' := supportGraph_le h_pres j (piece_subset hW j c.x c.y)
    exact Or.inr (mem_iUnion.2 ⟨j,
      (supportGraph G Γ μ _).vertex_mem_of_inc ((GM10.inc_iff_of_le hle' he).2 hx)⟩)

include hK hdeg in
/-- No edge of `G` outside `B(c)` has an end in `V(B(c)) \ X(c)`. This is the heart of claim
(1) of (6.4): an edge of `Γ` at such a vertex belongs to a jump inside `c`, since jumps do not
cross the cut, and an edge of `μ(F_j*)` at such a vertex belongs to `μ` of the part of `F_j*`
inside the cut, by (V4). -/
theorem not_mem_of_not_mem_cutF {c : Cut} (hc : Admissible LO HI 𝒯 POS c) :
    ∀ e ∈ G.edgeSet, e ∉ FF c → ∀ x, G.Inc e x → x ∉ WW c \ cutX μ f c := by
  have hb := admissible_bounds' hc
  intro e he heF x hx ⟨hxW, hxX⟩
  rw [h_pres.v1_union_E] at he
  rcases he with heH | heΓ
  · -- An edge of `μ(F_j*)`.
    rw [mem_iUnion] at heH
    obtain ⟨j, hj⟩ := heH
    rw [h_pres.v2_eq j] at hj
    have hlt : b j < a j + 2 * Real.pi := by
      linarith [hW.lt_add, hW.le_a j, hW.b_le j]
    obtain ⟨s, hs, hsF, hes⟩ := exists_space_of_mem_edgeSet h_pres j subset_rfl hj
    obtain ⟨a', b', ha, hab, hb', -, -, -, hs_eq, -⟩ := space_in_support_eq_Ioo h_pres.is_surface
      h_pres.cuff_vertices_ge_two hC f (hW.a_le_b j) hlt
      ⟨hW.a_mem j, GM17.cuffPoint_mem f _⟩ (hW.F_eq j) hs hsF
    have hsG := μ_space_le h_pres j hs hsF
    have hxs : x ∈ (μ (.space s)).vertexSet :=
      (μ (.space s)).vertex_mem_of_inc ((GM10.inc_iff_of_le hsG hes).2 hx)
    have hnotin : ¬ (c.x ≤ a' ∧ b' ≤ c.y) := by
      rintro ⟨h1, h2⟩
      apply heF
      refine Or.inr (mem_iUnion.2 ⟨j, hj.1, Or.inl (mem_biUnion (x := s) ⟨hs, ?_⟩ hes)⟩)
      rw [hs_eq]
      exact image_mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc (max_le ha h1) (le_min hb' h2)))
    have hnotV : ∀ t ∈ Ioo a' b', cp t ∉ Γ.V := fun t ht =>
      notMem_V_of_mem_space hs (by rw [hs_eq]; exact mem_image_of_mem _ ht)
    have hout : b' ≤ c.x ∨ c.y ≤ a' := by
      by_contra hcon
      push Not at hcon
      have h1 : c.x ≤ a' := by
        by_contra h
        exact hnotV c.x ⟨lt_of_not_ge h, hcon.1⟩ hb.2.2.2.1
      have h2 : b' ≤ c.y := by
        by_contra h
        exact hnotV c.y ⟨hcon.2, lt_of_not_ge h⟩ hb.2.2.2.2
      exact hnotin ⟨h1, h2⟩
    have hv_ab : x ∈ (supportGraph G Γ μ (cp '' Icc a' b')).vertexSet := by
      refine ⟨hsG.vertexSet_subset hxs, Or.inl (mem_biUnion (x := s) ⟨hs, ?_⟩ hxs)⟩
      rw [hs_eq]
      exact image_mono Ioo_subset_Icc_self
    have hxH : x ∈ (H j).vertexSet := (h_pres.μ_space_sub j s hs hsF).vertexSet_subset hxs
    obtain ⟨p, p', hp, hpp, hp', hv'⟩ := exists_part_of_mem_cutW h_pres hW hxW hxH
    exact hxX (mem_cutX_of_outside h_pres hC hW hc ha hab.le hb' hout hp hpp hp' hv_ab hv')
  · -- An edge of `Γ`.
    have hxΓ' : Γ_sub.Inc e x := (GM10.inc_iff_of_le h_pres.drawing_subgraph heΓ).2 hx
    have hxΓ : x ∈ Γ_sub.vertexSet := Γ_sub.vertex_mem_of_inc hxΓ'
    obtain ⟨J₀, hJ₀, heJ₀⟩ := exists_jump_of_edge hK hdeg heΓ
    have hxJ₀ : x ∈ J₀.vertexSet := J₀.vertex_mem_of_inc ((GM10.inc_iff_of_le hJ₀.1 heJ₀).2 hxΓ')
    have hJ₀out : J₀ ∉ insideSet LO HI 𝒯 c := fun h => heF (Or.inl (mem_biUnion h heJ₀))
    rcases mem_cutW_of_mem_drawing h_pres hW hxW hxΓ with ⟨J, hJ, hxJ, hxB⟩ |
      ⟨t, ht, htV, rfl⟩
    · obtain rfl := jump_eq_of_vertex hdeg hJ.1 hJ₀ hxJ hxJ₀ hxB
      exact hJ₀out hJ
    · have htW : t ∈ Icc w₀ w₁ := ⟨hb.1.trans ht.1, ht.2.trans hb.2.2.1⟩
      obtain ⟨j, -, htF⟩ := exists_piece_of_pos h_pres hW htW htV le_rfl le_rfl
      have htFs : cp t ∈ Γ.V ∩ F_star j := ⟨htV, piece_subset hW j t t htF.2⟩
      have hxt : c.x < t := by
        rcases eq_or_lt_of_le ht.1 with h | h
        · subst h
          exact absurd (Or.inl (ιV_mem_μ_vertex h_pres j htFs)) hxX
        · exact h
      have hty : t < c.y := by
        rcases eq_or_lt_of_le ht.2 with h | h
        · rw [h] at htFs hxX
          exact absurd (Or.inr (ιV_mem_μ_vertex h_pres j htFs)) hxX
        · exact h
      have hspec := hW.jumpAngles_spec h_pres hJ₀
      have hadm := hc.2.2.2 J₀ hJ₀
      rcases hW.eq_angle_of_mem_jump h_pres hJ₀ htW htV hxJ₀ with h | h
      · subst h
        by_cases hhi : HI J₀ ≤ c.y
        · exact hJ₀out ⟨hJ₀, hxt.le, hhi, Or.inr (Or.inl hxt.ne')⟩
        · exact hadm.1 ⟨hxt, hty, lt_of_not_ge hhi⟩
      · subst h
        by_cases hlo : c.x ≤ LO J₀
        · exact hJ₀out ⟨hJ₀, hlo, hty.le, Or.inr (Or.inr hty.ne)⟩
        · exact hadm.2 ⟨lt_of_not_ge hlo, hxt, hty⟩

include hK hdeg in
/-- **Claim (1) of the proof of (6.4)**: "(1) *(A(F), B(F)) is a separation of $G$, and
$X(F) = V(\mu(u_1) \cup \mu(u_2))$ where $F$ has ends $u_1, u_2$.*" -/
theorem isSeparation_cut {c : Cut} (hc : Admissible LO HI 𝒯 POS c) :
    G.IsSeparation (cutA G Γ μ f a b 𝒯 LO HI c) (cutB G Γ μ f a b 𝒯 LO HI c) ∧
      (cutA G Γ μ f a b 𝒯 LO HI c ∩ cutB G Γ μ f a b 𝒯 LO HI c).vertexSet = cutX μ f c :=
  isSeparation_subOn (cutW_subset h_pres) (cutX_subset_cutW h_pres hW hc)
    (ends_subset_cutW h_pres hW)
    (not_mem_of_not_mem_cutF h_pres hC hW hK hdeg hc)

/-- If `c'` is nested in `c`, a vertex of `X(c)` in `V(B(c'))` is in `X(c')`. -/
theorem mem_cutX_of_nested {c c' : Cut} (hc : Admissible LO HI 𝒯 POS c)
    (hc' : Admissible LO HI 𝒯 POS c') (hn : Nested LO HI 𝒯 c c') {v : α}
    (hv : v ∈ cutX μ f c) (hv' : v ∈ WW c') : v ∈ cutX μ f c' := by
  have hb := admissible_bounds' hc
  rcases hv with hv | hv
  · obtain ⟨j, hj, hmem⟩ := exists_piece_of_pos h_pres hW ⟨hb.1, hb.2.1.le.trans hb.2.2.1⟩
      hb.2.2.2.1 le_rfl le_rfl
    have hxF : cp c.x ∈ Γ.V ∩ F_star j := ⟨hmem.1, piece_subset hW j _ _ hmem.2⟩
    have hvH : v ∈ (H j).vertexSet := (h_pres.μ_vertex_sub j _ hxF).1.vertexSet_subset hv
    obtain ⟨p, p', hp, hpp, hp', hvp⟩ := exists_part_of_mem_cutW h_pres hW hv' hvH
    rcases eq_or_lt_of_le hn.1 with h | h
    · show v ∈ (μ (.vertex (cp c'.x))).vertexSet ∪ _
      rw [← h]
      exact Or.inl hv
    · have hsub : cp '' Icc c.x c.x ⊆ F_star j := by
        rw [hW.F_eq j]
        exact image_mono (Icc_subset_Icc hj.1 hj.2)
      have hvx : v ∈ (supportGraph G Γ μ (cp '' Icc c.x c.x)).vertexSet :=
        (μ_vertex_le_supportGraph_of_subset h_pres j hsub
          ⟨hb.2.2.2.1, c.x, ⟨le_rfl, le_rfl⟩, rfl⟩).vertexSet_subset hv
      exact mem_cutX_of_outside h_pres hC hW hc' hj.1 le_rfl hj.2 (Or.inl h.le) hp hpp hp' hvx hvp
  · obtain ⟨j, hj, hmem⟩ := exists_piece_of_pos h_pres hW ⟨hb.1.trans hb.2.1.le, hb.2.2.1⟩
      hb.2.2.2.2 le_rfl le_rfl
    have hyF : cp c.y ∈ Γ.V ∩ F_star j := ⟨hmem.1, piece_subset hW j _ _ hmem.2⟩
    have hvH : v ∈ (H j).vertexSet := (h_pres.μ_vertex_sub j _ hyF).1.vertexSet_subset hv
    obtain ⟨p, p', hp, hpp, hp', hvp⟩ := exists_part_of_mem_cutW h_pres hW hv' hvH
    rcases eq_or_lt_of_le hn.2.1 with h | h
    · show v ∈ _ ∪ (μ (.vertex (cp c'.y))).vertexSet
      rw [h]
      exact Or.inr hv
    · have hsub : cp '' Icc c.y c.y ⊆ F_star j := by
        rw [hW.F_eq j]
        exact image_mono (Icc_subset_Icc hj.1 hj.2)
      have hvy : v ∈ (supportGraph G Γ μ (cp '' Icc c.y c.y)).vertexSet :=
        (μ_vertex_le_supportGraph_of_subset h_pres j hsub
          ⟨hb.2.2.2.2, c.y, ⟨le_rfl, le_rfl⟩, rfl⟩).vertexSet_subset hv
      exact mem_cutX_of_outside h_pres hC hW hc' hj.1 le_rfl hj.2 (Or.inr h.le) hp hpp hp' hvy hvp

omit hC in
/-- `V(B(c')) ⊆ V(B(c))` and `E(B(c')) ⊆ E(B(c))` when `c'` is nested in `c`. -/
theorem cutW_cutF_mono {c c' : Cut} (hn : Nested LO HI 𝒯 c c') :
    WW c' ⊆ WW c ∧ FF c' ⊆ FF c := by
  have hmono : ∀ j, supportGraph G Γ μ (piece f a b j c'.x c'.y) ≤
      supportGraph G Γ μ (piece f a b j c.x c.y) := fun j =>
    supportGraph_mono h_pres j (piece_subset hW j _ _) (piece_mono j hn.1 hn.2.1)
  constructor
  · rintro v (hv | hv)
    · rw [mem_iUnion₂] at hv
      obtain ⟨J, hJ, hvJ⟩ := hv
      exact Or.inl (mem_biUnion (hn.2.2 hJ) hvJ)
    · rw [mem_iUnion] at hv
      obtain ⟨j, hv⟩ := hv
      exact Or.inr (mem_iUnion.2 ⟨j, (hmono j).vertexSet_subset hv⟩)
  · rintro e (he | he)
    · rw [mem_iUnion₂] at he
      obtain ⟨J, hJ, heJ⟩ := he
      exact Or.inl (mem_biUnion (hn.2.2 hJ) heJ)
    · rw [mem_iUnion] at he
      obtain ⟨j, he⟩ := he
      exact Or.inr (mem_iUnion.2 ⟨j, (hmono j).edgeSet_subset he⟩)

include hK hdeg in
/-- **Claim (2) of the proof of (6.4)**: "$A(F) \subseteq A(F')$ and $B(F') \subseteq B(F)$",
for `c'` nested in `c`. -/
theorem cut_nested {c c' : Cut} (hc : Admissible LO HI 𝒯 POS c)
    (hc' : Admissible LO HI 𝒯 POS c') (hn : Nested LO HI 𝒯 c c') :
    cutA G Γ μ f a b 𝒯 LO HI c ≤ cutA G Γ μ f a b 𝒯 LO HI c' ∧
      cutB G Γ μ f a b 𝒯 LO HI c' ≤ cutB G Γ μ f a b 𝒯 LO HI c := by
  obtain ⟨hW', hFm⟩ := cutW_cutF_mono h_pres hW hn
  constructor
  · apply subOn_mono
    · intro e he heG x hx
      exact ⟨G.vertex_mem_of_inc hx,
        not_mem_of_not_mem_cutF h_pres hC hW hK hdeg hc e heG he.2 x hx⟩
    · rintro v ⟨hvG, hv⟩
      refine ⟨hvG, fun ⟨hvW', hvX'⟩ => hv ⟨hW' hvW', fun hvX => hvX' ?_⟩⟩
      exact mem_cutX_of_nested h_pres hC hW hc hc' hn hvX hvW'
    · exact fun e he => ⟨he.1, fun h => he.2 (hFm h)⟩
  · exact subOn_mono (ends_subset_cutW h_pres hW) hW' hFm

end claims

end DiscCut
end GM21
end GraphMinor
