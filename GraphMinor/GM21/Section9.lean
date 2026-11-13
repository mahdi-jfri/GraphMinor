module

public import GraphMinor.GM21.Defs
public import GraphMinor.GM21.Parallel
public import GraphMinor.GM21.PortraitDefs
public import GraphMinor.GM21.LinkagePaths
public import GraphMinor.GM21.CuffSpaces
public import GraphMinor.GM21.CellDrawing
public import GraphMinor.GM21.Section3
public import GraphMinor.GM21.Section8
public import GraphMinor.GM21.Section8Free
import GraphMinor.GM21.Section2
import GraphMinor.Surface.DiscArcs

/-!
# Graph Minors XXI, Section 9: Paintings and portraits

Formalization of Section 9 (pages 37–41 of the preprint) of
N. Robertson and P. D. Seymour,
*Graph Minors. XXI. Graphs with unique linkages*,
J. Combin. Theory Ser. B 99 (2009), 583–616.

Proves:
- `theorem_9_1` (Graph Minors XXI, (9.1)): for every internal cell `c` of a portrait `(Γ, α)` of `G`
  in `Σ` and every vital linkage `L` in `G`, either `V(α(c)) \ c̃` contains a terminal of `L` or
  `α(c)` can be drawn in a disc with `c̃` in the boundary.
- `theorem_9_2` (Graph Minors XXI, (9.2)): for every surface `Σ` and integers `p ≥ 0` and `q ≥ 1`,
  there exists `θ ≥ 1` such that if `G` has a portrait in `Σ` of depth `≤ q` surrounding a tangle of
  order `≥ θ`, then `G` has no vital `p`-linkage.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Function Topology Metric Hypergraph GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM17 Classical
open GraphMinor.GM19 (cuffPoint)

universe u v

local notation "𝕀" => unitInterval

/-! ## 1. Internal Cell Separation `B(c)` and Proof of `(9.1)` -/

/-- For an internal cell `c` of a portrait `(Γ, α)` of `G`, the complementary subgraph `B(c)` of
`α(c)` in `G` has vertex set `(V(G) \ V(α(c))) ∪ ιN(c̃)` and edge set `E(G) \ E(α(c))`
(Graph Minors XXI, Section 9, page 40 of the preprint). -/
def internalCellCompl {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {c : Set S} (hc : IsInternalCell Γ c) : Hypergraph α β where
  vertexSet := (G.vertexSet \ (α_cell c).vertexSet) ∪ (ιN '' tilde c)
  edgeSet := G.edgeSet \ (α_cell c).edgeSet
  Inc e w := e ∈ G.edgeSet \ (α_cell c).edgeSet ∧ G.Inc e w
  vertex_mem_of_inc e w h := by
    rcases h with ⟨⟨heG, he_not_c⟩, hincG⟩
    have hwG : w ∈ G.vertexSet := G.vertex_mem_of_inc hincG
    by_cases hw_c : w ∈ (α_cell c).vertexSet
    · right
      have he_union : e ∈ ⋃ c' ∈ Γ.C, (α_cell c').edgeSet := hport.r3_union_E ▸ heG
      rw [mem_iUnion₂] at he_union
      rcases he_union with ⟨c', hc', he_c'⟩
      have hc'_ne : c ≠ c' := fun h_eq => he_not_c (h_eq ▸ he_c')
      have hc'_le : α_cell c' ≤ G := hport.r2_cell_le c' hc'
      have hinc_c' : (α_cell c').Inc e w :=
        (GM10.inc_iff_of_le hc'_le he_c').mpr hincG
      have hw_c' : w ∈ (α_cell c').vertexSet := (α_cell c').vertex_mem_of_inc hinc_c'
      have hno_cuff : ∀ C ∈ cuffs S, ¬ ((c ∩ C).Nonempty ∧ (c' ∩ C).Nonempty) := by
        intro C hC ⟨⟨x, hxc, hxC⟩, _⟩
        have hx_bd : x ∈ bd S := by
          rw [← sUnion_cuffs (S := S)]
          exact ⟨C, hC, hxC⟩
        exact Set.disjoint_left.mp hc.2 hxc hx_bd
      have hw_inter : w ∈ (α_cell c ∩ α_cell c').vertexSet := ⟨hw_c, hw_c'⟩
      rw [hport.r7_inter c hc.1 c' hc' hc'_ne hno_cuff] at hw_inter
      exact image_mono inter_subset_left hw_inter
    · exact Or.inl ⟨hwG, hw_c⟩
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := by
    refine (G.vertexSet_finite.sdiff.union ?_)
    exact (Γ.finite_tilde_cell hc.1).image ιN
  edgeSet_finite := G.edgeSet_finite.sdiff

theorem tilde_image_subset_cell_vertexSet {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {c : Set S} (hc : c ∈ Γ.C) :
    ιN '' tilde c ⊆ (α_cell c).vertexSet := by
  rw [← hport.r2_cell_inter c hc]
  exact inter_subset_left

theorem internalCellCompl_le {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {c : Set S} (hc : IsInternalCell Γ c) :
    internalCellCompl hport hc ≤ G := by
  refine ⟨?_, sdiff_subset, fun e he => ?_⟩
  · refine union_subset sdiff_subset ?_
    exact (tilde_image_subset_cell_vertexSet hport hc.1).trans (hport.r2_cell_le c hc.1).1
  · ext w
    exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩

theorem isSeparation_internalCellCompl {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {c : Set S} (hc : IsInternalCell Γ c) :
    G.IsSeparation (α_cell c) (internalCellCompl hport hc) := by
  have hle_c : α_cell c ≤ G := hport.r2_cell_le c hc.1
  have hle_B : internalCellCompl hport hc ≤ G := internalCellCompl_le hport hc
  rw [GM10.isSeparation_iff_of_le hle_c hle_B]
  refine ⟨?_, ?_, ?_⟩
  · ext w
    simp only [internalCellCompl, mem_union, mem_sdiff]
    constructor
    · rintro (hwc | ⟨hwG, _⟩ | hwt)
      · exact hle_c.1 hwc
      · exact hwG
      · exact hle_c.1 (tilde_image_subset_cell_vertexSet hport hc.1 hwt)
    · intro hwG
      by_cases hwc : w ∈ (α_cell c).vertexSet
      · exact Or.inl hwc
      · exact Or.inr (Or.inl ⟨hwG, hwc⟩)
  · ext e
    simp only [internalCellCompl, mem_union, mem_sdiff]
    constructor
    · rintro (hec | ⟨heG, _⟩)
      · exact hle_c.2 hec
      · exact heG
    · intro heG
      by_cases hec : e ∈ (α_cell c).edgeSet
      · exact Or.inl hec
      · exact Or.inr ⟨heG, hec⟩
  · ext e
    simp only [internalCellCompl, mem_inter_iff, mem_sdiff, mem_empty_iff_false, iff_false]
    rintro ⟨hec, _, he_not_c⟩
    exact he_not_c hec

theorem inter_vertexSet_internalCellCompl {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {c : Set S} (hc : IsInternalCell Γ c) :
    (α_cell c ∩ internalCellCompl hport hc).vertexSet = ιN '' tilde c := by
  ext w
  simp only [GM10.inter_vertexSet, internalCellCompl, mem_inter_iff, mem_union, mem_sdiff]
  constructor
  · rintro ⟨hwc, ⟨_, hnot_c⟩ | hwt⟩
    · exact (hnot_c hwc).elim
    · exact hwt
  · intro hwt
    exact ⟨tilde_image_subset_cell_vertexSet hport hc.1 hwt, Or.inr hwt⟩

theorem separationOrder_internalCellCompl_le {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {c : Set S} (hc : IsInternalCell Γ c) :
    separationOrder (α_cell c) (internalCellCompl hport hc) ≤ 3 := by
  unfold separationOrder
  rw [inter_vertexSet_internalCellCompl hport hc]
  calc (ιN '' tilde c).ncard
      ≤ (tilde c).ncard := ncard_image_le (Γ.finite_tilde_cell hc.1)
    _ ≤ 3 := Γ.ncard_tilde_cell_le hc.1

/-- The south pole `(0, -1)` in `ℂ`. -/
def apexC : ℂ := ⟨0, -1⟩

/-- Stereographic projection from `apexC = (0, -1)` onto the unit circle in `ℂ`:
`stereoC s = (2s / (1 + s²), (1 - s²) / (1 + s²))`. -/
noncomputable def stereoC (s : ℝ) : ℂ :=
  ⟨2 * s / (1 + s ^ 2), (1 - s ^ 2) / (1 + s ^ 2)⟩

theorem norm_apexC : ‖apexC‖ = 1 := by
  have h1 : ‖apexC‖ ^ 2 = apexC.re ^ 2 + apexC.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have h2 : ‖apexC‖ ^ 2 = 1 ^ 2 := by rw [h1]; dsimp [apexC]; ring
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp h2

theorem norm_stereoC (s : ℝ) : ‖stereoC s‖ = 1 := by
  have hpos : 0 < 1 + s ^ 2 := by positivity
  have hne : 1 + s ^ 2 ≠ 0 := hpos.ne'
  have h1 : ‖stereoC s‖ ^ 2 = (stereoC s).re ^ 2 + (stereoC s).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have h2 : ‖stereoC s‖ ^ 2 = 1 ^ 2 := by
    rw [h1]; dsimp [stereoC]; field_simp; ring
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp h2

theorem stereoC_im_add_one_pos (s : ℝ) : 0 < (stereoC s).im + 1 := by
  have hpos : 0 < 1 + s ^ 2 := by positivity
  have hne : 1 + s ^ 2 ≠ 0 := hpos.ne'
  have h_eq : (stereoC s).im + 1 = 2 / (1 + s ^ 2) := by
    dsimp [stereoC]; field_simp; ring
  rw [h_eq]
  positivity

theorem stereoC_re_eq (s : ℝ) : (stereoC s).re = s * ((stereoC s).im + 1) := by
  have hpos : 0 < 1 + s ^ 2 := by positivity
  have hne : 1 + s ^ 2 ≠ 0 := hpos.ne'
  dsimp [stereoC]; field_simp; ring

theorem stereoC_ne_apexC (s : ℝ) : stereoC s ≠ apexC := by
  intro h
  have him : (stereoC s).im + 1 = apexC.im + 1 := congrArg (fun z : ℂ => z.im + 1) h
  have h0 : apexC.im + 1 = 0 := by dsimp [apexC]; ring
  linarith [stereoC_im_add_one_pos s]

theorem stereoC_injective : Function.Injective stereoC := by
  intro s₁ s₂ h
  have hre : (stereoC s₁).re = (stereoC s₂).re := congrArg Complex.re h
  have him : (stereoC s₁).im + 1 = (stereoC s₂).im + 1 := congrArg (fun z : ℂ => z.im + 1) h
  have h1 := stereoC_re_eq s₁
  have h2 := stereoC_re_eq s₂
  have hpos := stereoC_im_add_one_pos s₂
  rw [hre, him, h2] at h1
  nlinarith

noncomputable def fanComplex (n : ℕ) : Option (Fin n) → ℂ
  | none => apexC
  | some i => stereoC (i.1 : ℝ)

theorem norm_fanComplex (n : ℕ) (a : Option (Fin n)) : ‖fanComplex n a‖ = 1 := by
  cases a with
  | none => exact norm_apexC
  | some i => exact norm_stereoC (i.1 : ℝ)

theorem fanComplex_injective (n : ℕ) : Function.Injective (fanComplex n) := by
  rintro (_ | i) (_ | j) h
  · rfl
  · exact (stereoC_ne_apexC (j.1 : ℝ) h.symm).elim
  · exact (stereoC_ne_apexC (i.1 : ℝ) h).elim
  · have hij : (i.1 : ℝ) = (j.1 : ℝ) := stereoC_injective h
    exact congrArg some (Fin.ext (Nat.cast_injective hij))

noncomputable def toClosedUnitDisc (z : ℂ) (hz : ‖z‖ ≤ 1) : ClosedUnitDisc :=
  ⟨complexPlane z, by
    rw [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
    exact hz⟩

noncomputable def fanDisc (n : ℕ) (a : Option (Fin n)) : ClosedUnitDisc :=
  toClosedUnitDisc (fanComplex n a) (norm_fanComplex n a).le

theorem fanDisc_injective (n : ℕ) : Function.Injective (fanDisc n) := by
  intro a b h
  have hC : fanComplex n a = fanComplex n b :=
    complexPlane.injective (congrArg Subtype.val h)
  exact fanComplex_injective n hC

theorem fanDisc_mem_bd (n : ℕ) (a : Option (Fin n)) : fanDisc n a ∈ bd ClosedUnitDisc := by
  rw [bd_closedUnitDisc]
  show complexPlane (fanComplex n a) ∈ UnitCircle
  rw [UnitCircle, mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
  exact norm_fanComplex n a

private theorem norm_convex_combo_eq' {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (u : ℝ) :
    ‖(1 - (u : ℂ)) * z + (u : ℂ) * w‖ ^ 2 + u * (1 - u) * ‖z - w‖ ^ 2 = 1 := by
  have h1 : ∀ a : ℂ, ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := fun a => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hz2 : z.re ^ 2 + z.im ^ 2 = 1 := by rw [← h1 z, hz, one_pow]
  have hw2 : w.re ^ 2 + w.im ^ 2 = 1 := by rw [← h1 w, hw, one_pow]
  rw [h1, h1]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
    Complex.ofReal_re, Complex.ofReal_im]
  linear_combination (1 - u) * hz2 + u * hw2

noncomputable def chordMapC (n : ℕ) (a b : Option (Fin n)) (u : ℝ) : ℂ :=
  (1 - (u : ℂ)) * fanComplex n a + (u : ℂ) * fanComplex n b

theorem norm_chordMapC_le_one (n : ℕ) (a b : Option (Fin n)) (u : 𝕀) :
    ‖chordMapC n a b u‖ ≤ 1 := by
  have hid := norm_convex_combo_eq' (norm_fanComplex n a) (norm_fanComplex n b) (u : ℝ)
  have hnonneg : 0 ≤ (u : ℝ) * (1 - (u : ℝ)) * ‖fanComplex n a - fanComplex n b‖ ^ 2 :=
    mul_nonneg (mul_nonneg u.2.1 (sub_nonneg.mpr u.2.2)) (sq_nonneg _)
  have hsq : ‖chordMapC n a b u‖ ^ 2 ≤ 1 ^ 2 := by dsimp [chordMapC]; linarith
  exact (abs_le_of_sq_le_sq' hsq zero_le_one).2

theorem norm_chordMapC_lt_one {n : ℕ} {a b : Option (Fin n)} (hab : a ≠ b)
    {u : 𝕀} (hu0 : 0 < (u : ℝ)) (hu1 : (u : ℝ) < 1) :
    ‖chordMapC n a b u‖ < 1 := by
  have hid := norm_convex_combo_eq' (norm_fanComplex n a) (norm_fanComplex n b) (u : ℝ)
  have hz_ne : fanComplex n a ≠ fanComplex n b := (fanComplex_injective n).ne hab
  have hdiff_pos : 0 < ‖fanComplex n a - fanComplex n b‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne))
  have hpos : 0 < (u : ℝ) * (1 - (u : ℝ)) * ‖fanComplex n a - fanComplex n b‖ ^ 2 :=
    mul_pos (mul_pos hu0 (sub_pos.mpr hu1)) hdiff_pos
  have hsq : ‖chordMapC n a b u‖ ^ 2 < 1 ^ 2 := by dsimp [chordMapC]; linarith
  nlinarith [norm_nonneg (chordMapC n a b u)]

noncomputable def chordMapDisc (n : ℕ) (a b : Option (Fin n)) (u : 𝕀) : ClosedUnitDisc :=
  toClosedUnitDisc (chordMapC n a b u) (norm_chordMapC_le_one n a b u)

theorem continuous_chordMapDisc (n : ℕ) (a b : Option (Fin n)) :
    Continuous (chordMapDisc n a b) := by
  have hc : Continuous fun u : 𝕀 => chordMapC n a b u :=
    ((continuous_const.sub (Complex.continuous_ofReal.comp continuous_subtype_val)).mul
      continuous_const).add
      ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const)
  exact Continuous.subtype_mk (complexPlane.continuous.comp hc) _

theorem injective_chordMapDisc {n : ℕ} {a b : Option (Fin n)} (hab : a ≠ b) :
    Function.Injective (chordMapDisc n a b) := by
  intro u₁ u₂ h
  have hC : chordMapC n a b u₁ = chordMapC n a b u₂ :=
    complexPlane.injective (congrArg Subtype.val h)
  have hsub : ((u₁ : ℝ) - (u₂ : ℝ) : ℂ) * (fanComplex n b - fanComplex n a) = 0 := by
    calc ((u₁ : ℝ) - (u₂ : ℝ) : ℂ) * (fanComplex n b - fanComplex n a)
      _ = chordMapC n a b u₁ - chordMapC n a b u₂ := by dsimp [chordMapC]; ring
      _ = 0 := sub_eq_zero.mpr hC
  have hdiff : fanComplex n b - fanComplex n a ≠ 0 :=
    sub_ne_zero.mpr ((fanComplex_injective n).ne hab.symm)
  have hu : ((u₁ : ℝ) - (u₂ : ℝ) : ℂ) = 0 := (mul_eq_zero.mp hsub).resolve_right hdiff
  have hu' : (u₁ : ℝ) - (u₂ : ℝ) = 0 := Complex.ofReal_eq_zero.mp (by simpa using hu)
  exact Subtype.ext (sub_eq_zero.mp hu')

theorem chordMapDisc_zero (n : ℕ) (a b : Option (Fin n)) :
    chordMapDisc n a b 0 = fanDisc n a := by
  apply Subtype.ext
  show complexPlane (chordMapC n a b 0) = complexPlane (fanComplex n a)
  congr 1
  dsimp [chordMapC]
  simp

theorem chordMapDisc_one (n : ℕ) (a b : Option (Fin n)) :
    chordMapDisc n a b 1 = fanDisc n b := by
  apply Subtype.ext
  show complexPlane (chordMapC n a b 1) = complexPlane (fanComplex n b)
  congr 1
  dsimp [chordMapC]
  simp

def closedChord (n : ℕ) (a b : Option (Fin n)) : Set ClosedUnitDisc :=
  range (chordMapDisc n a b)

def openChord (n : ℕ) (a b : Option (Fin n)) : Set ClosedUnitDisc :=
  chordMapDisc n a b '' {u : 𝕀 | 0 < (u : ℝ) ∧ (u : ℝ) < 1}

theorem isClosed_closedChord (n : ℕ) (a b : Option (Fin n)) :
    IsClosed (closedChord n a b) :=
  (isCompact_range (continuous_chordMapDisc n a b)).isClosed

theorem isLineWithEnds_closedChord {n : ℕ} {a b : Option (Fin n)} (hab : a ≠ b) :
    IsLineWithEnds (closedChord n a b) (fanDisc n a) (fanDisc n b) := by
  let ev : 𝕀 ≃ₜ closedChord n a b :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofInjective (chordMapDisc n a b) (injective_chordMapDisc hab))
      (continuous_chordMapDisc n a b).rangeFactorization
  exact ⟨ev, chordMapDisc_zero n a b, chordMapDisc_one n a b⟩

theorem openChord_disjoint_bd {n : ℕ} {a b : Option (Fin n)} (hab : a ≠ b) :
    Disjoint (openChord n a b) (bd ClosedUnitDisc) := by
  rw [Set.disjoint_left]
  rintro _ ⟨u, ⟨hu0, hu1⟩, rfl⟩ hbd
  rw [bd_closedUnitDisc] at hbd
  change complexPlane (chordMapC n a b u) ∈ UnitCircle at hbd
  rw [UnitCircle, mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map] at hbd
  exact (norm_chordMapC_lt_one hab hu0 hu1).ne hbd

theorem closedChord_eq_openChord_union (n : ℕ) (a b : Option (Fin n)) :
    closedChord n a b = openChord n a b ∪ {fanDisc n a, fanDisc n b} := by
  ext x
  simp only [closedChord, openChord, mem_range, mem_union, mem_image, mem_ofPred_eq,
    mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨u, rfl⟩
    by_cases hu0 : (u : ℝ) = 0
    · have hu : u = 0 := Subtype.ext hu0
      subst hu
      exact Or.inr (Or.inl (chordMapDisc_zero n a b))
    · by_cases hu1 : (u : ℝ) = 1
      · have hu : u = 1 := Subtype.ext hu1
        subst hu
        exact Or.inr (Or.inr (chordMapDisc_one n a b))
      · exact Or.inl ⟨u, ⟨lt_of_le_of_ne u.2.1 (Ne.symm hu0), lt_of_le_of_ne u.2.2 hu1⟩, rfl⟩
  · rintro (⟨u, _, rfl⟩ | rfl | rfl)
    · exact ⟨u, rfl⟩
    · exact ⟨0, chordMapDisc_zero n a b⟩
    · exact ⟨1, chordMapDisc_one n a b⟩

theorem closedChord_inter_bd {n : ℕ} {a b : Option (Fin n)} (hab : a ≠ b) :
    closedChord n a b ∩ bd ClosedUnitDisc = {fanDisc n a, fanDisc n b} := by
  rw [closedChord_eq_openChord_union, union_inter_distrib_right,
    (openChord_disjoint_bd hab).inter_eq, empty_union, inter_eq_left]
  rintro x (rfl | rfl) <;> exact fanDisc_mem_bd n _

theorem openChord_eq_closedChord_diff {n : ℕ} {a b : Option (Fin n)} (hab : a ≠ b)
    {V : Set ClosedUnitDisc} (hV_bd : V ⊆ bd ClosedUnitDisc)
    (ha : fanDisc n a ∈ V) (hb : fanDisc n b ∈ V) :
    closedChord n a b \ V = openChord n a b := by
  ext x
  simp only [mem_sdiff]
  constructor
  · intro ⟨hx, hxV⟩
    rcases (closedChord_eq_openChord_union n a b ▸ hx) with hxo | rfl | rfl
    · exact hxo
    · exact (hxV ha).elim
    · exact (hxV hb).elim
  · intro hxo
    refine ⟨closedChord_eq_openChord_union n a b ▸ Or.inl hxo, fun hxV => ?_⟩
    exact Set.disjoint_left.mp (openChord_disjoint_bd hab) hxo (hV_bd hxV)

theorem closure_openChord (n : ℕ) (a b : Option (Fin n)) :
    closure (openChord n a b) = closedChord n a b := by
  refine Subset.antisymm ?_ ?_
  · refine closure_minimal ?_ (isClosed_closedChord n a b)
    rintro _ ⟨u, _, rfl⟩
    exact ⟨u, rfl⟩
  · have h_sub_cl : closure {u : 𝕀 | 0 < (u : ℝ) ∧ (u : ℝ) < 1} = univ := by
      rw [IsInducing.subtypeVal.closure_eq_preimage_closure_image]
      have himg : Subtype.val '' {u : 𝕀 | 0 < (u : ℝ) ∧ (u : ℝ) < 1} = Ioo (0 : ℝ) 1 := by
        ext t
        simp only [mem_image, mem_ofPred_eq, mem_Ioo]
        exact ⟨by rintro ⟨u, hu, rfl⟩; exact hu,
          fun ht => ⟨⟨t, Ioo_subset_Icc_self ht⟩, ht, rfl⟩⟩
      rw [himg, closure_Ioo (zero_ne_one : (0 : ℝ) ≠ 1)]
      ext u
      simp
    calc closedChord n a b
        = chordMapDisc n a b '' univ := (image_univ).symm
      _ = chordMapDisc n a b '' closure {u : 𝕀 | 0 < (u : ℝ) ∧ (u : ℝ) < 1} := by rw [h_sub_cl]
      _ ⊆ closure (openChord n a b) :=
          image_closure_subset_closure_image (continuous_chordMapDisc n a b)

theorem nonempty_openChord (n : ℕ) (a b : Option (Fin n)) :
    (openChord n a b).Nonempty := by
  refine ⟨chordMapDisc n a b ⟨1 / 2, by constructor <;> norm_num⟩, ?_⟩
  exact ⟨⟨1 / 2, by constructor <;> norm_num⟩, by constructor <;> norm_num, rfl⟩

theorem isPathConnected_openChord (n : ℕ) (a b : Option (Fin n)) :
    IsPathConnected (openChord n a b) := by
  have hconv : IsPathConnected (Ioo (0 : ℝ) 1) :=
    (convex_Ioo (0 : ℝ) 1).isPathConnected ⟨1 / 2, by constructor <;> norm_num⟩
  let g : ℝ → ClosedUnitDisc := fun t => chordMapDisc n a b (projIcc 0 1 zero_le_one t)
  have hg_eq : openChord n a b = g '' Ioo (0 : ℝ) 1 := by
    ext x
    simp only [openChord, g, mem_image, mem_ofPred_eq, mem_Ioo]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨(u : ℝ), hu, ?_⟩
      rw [projIcc_of_mem zero_le_one u.2]
    · rintro ⟨t, ht, rfl⟩
      have ht_icc : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
      refine ⟨⟨t, ht_icc⟩, ht, ?_⟩
      rw [projIcc_of_mem zero_le_one ht_icc]
  have hg_cont : Continuous g := (continuous_chordMapDisc n a b).comp continuous_projIcc
  rw [hg_eq]
  exact hconv.image hg_cont

theorem openChord_apex_slope {n : ℕ} (i : Fin n) {x : ClosedUnitDisc}
    (hx : x ∈ openChord n none (some i)) :
    0 < (complexPlane.symm x.1).im + 1 ∧
      (complexPlane.symm x.1).re = (i.1 : ℝ) * ((complexPlane.symm x.1).im + 1) := by
  rcases hx with ⟨u, ⟨hu0, _⟩, rfl⟩
  have hsymm : complexPlane.symm (chordMapDisc n none (some i) u).1 = chordMapC n none (some i) u :=
    complexPlane.symm_apply_apply _
  rw [hsymm]
  have him_pos := stereoC_im_add_one_pos (i.1 : ℝ)
  have hre_eq := stereoC_re_eq (i.1 : ℝ)
  have him_c : (chordMapC n none (some i) u).im + 1 = (u : ℝ) * ((stereoC (i.1 : ℝ)).im + 1) := by
    have h1 : (chordMapC n none (some i) u).im = -(1 - (u : ℝ)) + (u : ℝ) * (stereoC (i.1 : ℝ)).im := by
      dsimp [chordMapC, fanComplex, apexC]; simp
    linarith
  have hre_c : (chordMapC n none (some i) u).re = (u : ℝ) * (stereoC (i.1 : ℝ)).re := by
    dsimp [chordMapC, fanComplex, apexC]; simp
  refine ⟨by rw [him_c]; exact mul_pos hu0 him_pos, ?_⟩
  rw [him_c, hre_c, hre_eq]
  ring

theorem openChord_step_slope {n : ℕ} {i j : Fin n} (hij : i.1 + 1 = j.1) {x : ClosedUnitDisc}
    (hx : x ∈ openChord n (some i) (some j)) :
    0 < (complexPlane.symm x.1).im + 1 ∧
      (i.1 : ℝ) * ((complexPlane.symm x.1).im + 1) < (complexPlane.symm x.1).re ∧
      (complexPlane.symm x.1).re < ((i.1 : ℝ) + 1) * ((complexPlane.symm x.1).im + 1) := by
  rcases hx with ⟨u, ⟨hu0, hu1⟩, rfl⟩
  have hsymm : complexPlane.symm (chordMapDisc n (some i) (some j) u).1 =
      chordMapC n (some i) (some j) u :=
    complexPlane.symm_apply_apply _
  rw [hsymm]
  have him_i := stereoC_im_add_one_pos (i.1 : ℝ)
  have him_j := stereoC_im_add_one_pos (j.1 : ℝ)
  have hre_i := stereoC_re_eq (i.1 : ℝ)
  have hj_cast : (j.1 : ℝ) = (i.1 : ℝ) + 1 := by exact_mod_cast hij.symm
  have hre_j : (stereoC (j.1 : ℝ)).re = ((i.1 : ℝ) + 1) * ((stereoC (j.1 : ℝ)).im + 1) := by
    rw [stereoC_re_eq (j.1 : ℝ), hj_cast]
  have him_c : (chordMapC n (some i) (some j) u).im + 1 =
      (1 - (u : ℝ)) * ((stereoC (i.1 : ℝ)).im + 1) + (u : ℝ) * ((stereoC (j.1 : ℝ)).im + 1) := by
    have h1 : (chordMapC n (some i) (some j) u).im =
        (1 - (u : ℝ)) * (stereoC (i.1 : ℝ)).im + (u : ℝ) * (stereoC (j.1 : ℝ)).im := by
      dsimp [chordMapC, fanComplex]; simp
    linarith
  have hre_c : (chordMapC n (some i) (some j) u).re =
      (1 - (u : ℝ)) * (stereoC (i.1 : ℝ)).re + (u : ℝ) * (stereoC (j.1 : ℝ)).re := by
    dsimp [chordMapC, fanComplex]; simp
  have hpos1 : 0 < (1 - (u : ℝ)) * ((stereoC (i.1 : ℝ)).im + 1) :=
    mul_pos (sub_pos.mpr hu1) him_i
  have hpos2 : 0 < (u : ℝ) * ((stereoC (j.1 : ℝ)).im + 1) :=
    mul_pos hu0 him_j
  refine ⟨by rw [him_c]; linarith, ?_, ?_⟩
  · rw [him_c, hre_c, hre_i, hre_j]
    linarith [hpos2]
  · rw [him_c, hre_c, hre_i, hre_j]
    linarith [hpos1]

def IsCanonicalFanEdge (n : ℕ) (p : Option (Fin n) × Option (Fin n)) : Prop :=
  (p.1 = none ∧ ∃ i : Fin n, p.2 = some i) ∨
  (∃ i j : Fin n, p.1 = some i ∧ p.2 = some j ∧ i.1 + 1 = j.1)

theorem IsCanonicalFanEdge.ne {n : ℕ} {p : Option (Fin n) × Option (Fin n)}
    (hp : IsCanonicalFanEdge n p) : p.1 ≠ p.2 := by
  rcases hp with ⟨hp1, i, hp2⟩ | ⟨i, j, hp1, hp2, hij⟩
  · rw [hp1, hp2]; rintro ⟨⟩
  · rw [hp1, hp2]
    intro h
    have : i.1 = j.1 := congrArg Fin.val (Option.some.inj h)
    omega

theorem disjoint_openChord_of_isCanonicalFanEdge {n : ℕ}
    {p q : Option (Fin n) × Option (Fin n)}
    (hp : IsCanonicalFanEdge n p) (hq : IsCanonicalFanEdge n q) (hne : p ≠ q) :
    Disjoint (openChord n p.1 p.2) (openChord n q.1 q.2) := by
  rw [Set.disjoint_left]
  intro x hxp hxq
  rcases hp with ⟨hp1, i, hp2⟩ | ⟨i, j, hp1, hp2, hij⟩ <;>
    rcases hq with ⟨hq1, i', hq2⟩ | ⟨i', j', hq1, hq2, hij'⟩
  · rw [hp1, hp2] at hxp
    rw [hq1, hq2] at hxq
    obtain ⟨hpos, hre1⟩ := openChord_apex_slope i hxp
    obtain ⟨_, hre2⟩ := openChord_apex_slope i' hxq
    have hii' : (i.1 : ℝ) = (i'.1 : ℝ) := by nlinarith
    have hi_eq : i = i' := Fin.ext (Nat.cast_injective hii')
    exact hne (Prod.ext (hp1.trans hq1.symm) (hp2.trans (hi_eq ▸ hq2.symm)))
  · rw [hp1, hp2] at hxp
    rw [hq1, hq2] at hxq
    obtain ⟨hpos, hre1⟩ := openChord_apex_slope i hxp
    obtain ⟨_, hlt1, hlt2⟩ := openChord_step_slope hij' hxq
    rcases le_or_gt i.1 i'.1 with hle | hgt
    · have hle_r : (i.1 : ℝ) ≤ (i'.1 : ℝ) := Nat.cast_le.mpr hle
      nlinarith
    · have hge_r : (i'.1 : ℝ) + 1 ≤ (i.1 : ℝ) := by exact_mod_cast hgt
      nlinarith
  · rw [hp1, hp2] at hxp
    rw [hq1, hq2] at hxq
    obtain ⟨hpos, hlt1, hlt2⟩ := openChord_step_slope hij hxp
    obtain ⟨_, hre2⟩ := openChord_apex_slope i' hxq
    rcases le_or_gt i'.1 i.1 with hle | hgt
    · have hle_r : (i'.1 : ℝ) ≤ (i.1 : ℝ) := Nat.cast_le.mpr hle
      nlinarith
    · have hge_r : (i.1 : ℝ) + 1 ≤ (i'.1 : ℝ) := by exact_mod_cast hgt
      nlinarith
  · rw [hp1, hp2] at hxp
    rw [hq1, hq2] at hxq
    obtain ⟨hpos, hlt1, hlt2⟩ := openChord_step_slope hij hxp
    obtain ⟨_, hlt1', hlt2'⟩ := openChord_step_slope hij' hxq
    have hii' : i ≠ i' := by
      intro h_eq
      subst h_eq
      have hj_eq : j = j' := Fin.ext (by omega)
      exact hne (Prod.ext (hp1.trans hq1.symm) (hp2.trans (hj_eq ▸ hq2.symm)))
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hii') with hlt | hgt
    · have hle_r : (i.1 : ℝ) + 1 ≤ (i'.1 : ℝ) := by exact_mod_cast hlt
      nlinarith
    · have hle_r : (i'.1 : ℝ) + 1 ≤ (i.1 : ℝ) := by exact_mod_cast hgt
      nlinarith

/-- Any hypergraph `H` whose vertices can be indexed by a subset `S ⊆ Option (Fin n)` such that
every edge of `H.skeleton` is either incident with `none` or connects consecutive indices
`some i, some j` (`|i - j| = 1`) can be drawn in `ClosedUnitDisc` with all vertices on the boundary
(and hence with any `X ⊆ V(H)` on the boundary). -/
theorem canBeDrawnInDiscWithBoundary_of_fanEmbedding {α : Type u} {β : Type v}
    {H : Hypergraph α β} {X : Set α} (hX_sub : X ⊆ H.vertexSet) (x₀ : α)
    {n : ℕ} {S : Set (Option (Fin n))} {f : Option (Fin n) → α}
    (hf_inj : InjOn f S) (hf_img : f '' S = H.vertexSet)
    (hadj : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → H.skeleton.Adj (f a) (f b) →
      a = none ∨ b = none ∨ ∃ i j : Fin n, a = some i ∧ b = some j ∧ (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1)) :
    CanBeDrawnInDiscWithBoundary H X := by
  let E_pairs : Set (Option (Fin n) × Option (Fin n)) :=
    {p | p.1 ∈ S ∧ p.2 ∈ S ∧ H.skeleton.Adj (f p.1) (f p.2) ∧ IsCanonicalFanEdge n p}
  have hE_fin : E_pairs.Finite := Set.toFinite E_pairs
  have hS_fin : S.Finite := Set.toFinite S
  let V : Set ClosedUnitDisc := fanDisc n '' S
  have hV_fin : V.Finite := hS_fin.image (fanDisc n)
  have hV_bd : V ⊆ bd ClosedUnitDisc := by
    rintro _ ⟨a, _, rfl⟩; exact fanDisc_mem_bd n a
  let U : Set ClosedUnitDisc := V ∪ ⋃ p ∈ E_pairs, closedChord n p.1 p.2
  have hU_closed : IsClosed U :=
    hV_fin.isClosed.union (hE_fin.isClosed_biUnion fun p _ => isClosed_closedChord n p.1 p.2)
  let 𝒥 : Set (Set ClosedUnitDisc) := (fun p => openChord n p.1 p.2) '' E_pairs
  have h𝒥_fin : 𝒥.Finite := hE_fin.image _
  have hp_diff : ∀ p ∈ E_pairs, closedChord n p.1 p.2 \ V = openChord n p.1 p.2 := by
    intro p hp
    exact openChord_eq_closedChord_diff hp.2.2.2.ne hV_bd ⟨p.1, hp.1, rfl⟩ ⟨p.2, hp.2.1, rfl⟩
  have hp_inter : ∀ p ∈ E_pairs, closedChord n p.1 p.2 ∩ V = {fanDisc n p.1, fanDisc n p.2} := by
    intro p hp
    refine Subset.antisymm ?_ ?_
    · calc closedChord n p.1 p.2 ∩ V
          ⊆ closedChord n p.1 p.2 ∩ bd ClosedUnitDisc := inter_subset_inter_right _ hV_bd
        _ = {fanDisc n p.1, fanDisc n p.2} := closedChord_inter_bd hp.2.2.2.ne
    · rintro x (rfl | rfl)
      · exact ⟨⟨0, chordMapDisc_zero n p.1 p.2⟩, p.1, hp.1, rfl⟩
      · exact ⟨⟨1, chordMapDisc_one n p.1 p.2⟩, p.2, hp.2.1, rfl⟩
  have hcov : ⋃₀ 𝒥 = U \ V := by
    ext x
    simp only [𝒥, U, mem_sUnion, mem_image, exists_exists_and_eq_and, mem_sdiff, mem_union,
      mem_iUnion]
    constructor
    · rintro ⟨p, hp, hxo⟩
      rw [← hp_diff p hp] at hxo
      exact ⟨Or.inr ⟨p, hp, hxo.1⟩, hxo.2⟩
    · rintro ⟨hxV | ⟨p, hp, hxc⟩, hx_not_V⟩
      · exact (hx_not_V hxV).elim
      · refine ⟨p, hp, ?_⟩
        rw [← hp_diff p hp]
        exact ⟨hxc, hx_not_V⟩
  have hE_eq : arcComponentsIn (U \ V) = 𝒥 := by
    apply arcComponentsIn_eq_of_finite_cover h𝒥_fin hcov
    · rintro _ ⟨p, _, rfl⟩
      exact nonempty_openChord n p.1 p.2
    · rintro _ ⟨p, _, rfl⟩
      exact isPathConnected_openChord n p.1 p.2
    · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne
      have hpq : p ≠ q := fun h => hne (h ▸ rfl)
      exact disjoint_openChord_of_isCanonicalFanEdge hp.2.2.2 hq.2.2.2 hpq
    · rintro _ ⟨p, hp, rfl⟩
      dsimp only
      rw [closure_openChord]
      refine Subset.antisymm ?_ ?_
      · rintro x ⟨hxc, _, hx_not_V⟩
        rw [← hp_diff p hp]
        exact ⟨hxc, hx_not_V⟩
      · intro x hxo
        rw [← hp_diff p hp] at hxo
        exact ⟨hxo.1, ⟨Or.inr (mem_biUnion hp hxo.1), hxo.2⟩⟩
  let D : Drawing ClosedUnitDisc :=
    { U := U
      V := V
      V_subset_U := subset_union_left
      isClosed_U := hU_closed
      finite_V := hV_fin
      finite_edges := hE_eq ▸ h𝒥_fin
      edge_cond := by
        intro e he
        rw [hE_eq] at he
        rcases he with ⟨p, hp, rfl⟩
        left
        refine ⟨fanDisc n p.1, fanDisc n p.2, (fanDisc_injective n).ne hp.2.2.2.ne, ?_, ?_⟩
        · rw [closure_openChord, hp_inter p hp]
        · rw [closure_openChord]
          exact isLineWithEnds_closedChord hp.2.2.2.ne }
  let ι : ClosedUnitDisc → α := fun x =>
    if hx : ∃ a ∈ S, fanDisc n a = x then f (Classical.choose hx) else x₀
  have hι_fan : ∀ a ∈ S, ι (fanDisc n a) = f a := by
    intro a ha
    have hx : ∃ a' ∈ S, fanDisc n a' = fanDisc n a := ⟨a, ha, rfl⟩
    simp only [ι, hx, ↓reduceDIte]
    have h_spec := Classical.choose_spec hx
    exact congrArg f (fanDisc_injective n h_spec.2)
  have hι_bij : BijOn ι D.V H.vertexSet := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      rw [hι_fan a ha, ← hf_img]
      exact ⟨a, ha, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h_eq
      rw [hι_fan a ha, hι_fan b hb] at h_eq
      exact congrArg (fanDisc n) (hf_inj ha hb h_eq)
    · intro w hw
      rw [← hf_img] at hw
      rcases hw with ⟨a, ha, rfl⟩
      exact ⟨fanDisc n a, ⟨a, ha, rfl⟩, hι_fan a ha⟩
  have hX_bd : X ⊆ ι '' (D.V ∩ bd ClosedUnitDisc) := by
    have h_inter : D.V ∩ bd ClosedUnitDisc = D.V := inter_eq_left.mpr hV_bd
    rw [h_inter, hι_bij.image_eq]
    exact hX_sub
  refine ⟨D, ι, hι_bij, hX_bd, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ huv_ne
  have hab : a ≠ b := fun h => huv_ne (congrArg (fanDisc n) h)
  rw [hι_fan a ha, hι_fan b hb]
  constructor
  · intro hadj_ab
    have h_pair : (a, b) ∈ E_pairs ∨ (b, a) ∈ E_pairs := by
      rcases hadj a ha b hb hab hadj_ab with rfl | rfl | ⟨i, j, rfl, rfl, hij | hji⟩
      · cases b with
        | none => exact (hab rfl).elim
        | some i =>
          exact Or.inl ⟨ha, hb, hadj_ab, Or.inl ⟨rfl, i, rfl⟩⟩
      · cases a with
        | none => exact (hab rfl).elim
        | some i =>
          exact Or.inr ⟨hb, ha, hadj_ab.symm, Or.inl ⟨rfl, i, rfl⟩⟩
      · exact Or.inl ⟨ha, hb, hadj_ab, Or.inr ⟨i, j, rfl, rfl, hij⟩⟩
      · exact Or.inr ⟨hb, ha, hadj_ab.symm, Or.inr ⟨j, i, rfl, rfl, hji⟩⟩
    refine ⟨huv_ne, ?_⟩
    rcases h_pair with hp | hp
    · refine ⟨openChord n a b, ?_, ?_⟩
      · refine ⟨?_, ⟨a, ha, rfl⟩, ?_⟩
        · change openChord n a b ∈ arcComponentsIn (U \ V)
          rw [hE_eq]; exact ⟨(a, b), hp, rfl⟩
        · rw [closure_openChord]
          exact ⟨0, chordMapDisc_zero n a b⟩
      · refine ⟨?_, ⟨b, hb, rfl⟩, ?_⟩
        · change openChord n a b ∈ arcComponentsIn (U \ V)
          rw [hE_eq]; exact ⟨(a, b), hp, rfl⟩
        · rw [closure_openChord]
          exact ⟨1, chordMapDisc_one n a b⟩
    · refine ⟨openChord n b a, ?_, ?_⟩
      · refine ⟨?_, ⟨a, ha, rfl⟩, ?_⟩
        · change openChord n b a ∈ arcComponentsIn (U \ V)
          rw [hE_eq]; exact ⟨(b, a), hp, rfl⟩
        · rw [closure_openChord]
          exact ⟨1, chordMapDisc_one n b a⟩
      · refine ⟨?_, ⟨b, hb, rfl⟩, ?_⟩
        · change openChord n b a ∈ arcComponentsIn (U \ V)
          rw [hE_eq]; exact ⟨(b, a), hp, rfl⟩
        · rw [closure_openChord]
          exact ⟨0, chordMapDisc_zero n b a⟩
  · rintro ⟨_, e, ⟨heE, _, ha_cl⟩, ⟨_, _, hb_cl⟩⟩
    change e ∈ arcComponentsIn (U \ V) at heE
    rw [hE_eq] at heE
    rcases heE with ⟨p, hp, rfl⟩
    rw [closure_openChord] at ha_cl hb_cl
    have ha_pair : fanDisc n a ∈ ({fanDisc n p.1, fanDisc n p.2} : Set ClosedUnitDisc) := by
      rw [← hp_inter p hp]; exact ⟨ha_cl, a, ha, rfl⟩
    have hb_pair : fanDisc n b ∈ ({fanDisc n p.1, fanDisc n p.2} : Set ClosedUnitDisc) := by
      rw [← hp_inter p hp]; exact ⟨hb_cl, b, hb, rfl⟩
    rcases ha_pair with ha1 | ha2 <;> rcases hb_pair with hb1 | hb2
    · exact (huv_ne (ha1.trans hb1.symm)).elim
    · have ha_eq : a = p.1 := fanDisc_injective n ha1
      have hb_eq : b = p.2 := fanDisc_injective n hb2
      rw [ha_eq, hb_eq]
      exact hp.2.2.1
    · have ha_eq : a = p.2 := fanDisc_injective n ha2
      have hb_eq : b = p.1 := fanDisc_injective n hb1
      rw [ha_eq, hb_eq]
      exact hp.2.2.1.symm
    · exact (huv_ne (ha2.trans hb2.symm)).elim

/-- Shape 1 of `CanBeDrawnInDisc21`: if `V(H) = X` and `|X| ≤ 3`, then `H` can be drawn in the
closed unit disc with `X` in the boundary. -/
theorem canBeDrawnInDiscWithBoundary_of_vertexSet_eq {α : Type u} {β : Type v}
    {H : Hypergraph α β} {X : Set α} (hVX : H.vertexSet = X)
    (hX_card : X.ncard ≤ 3) (x₀ : α) :
    CanBeDrawnInDiscWithBoundary H X := by
  have hX_sub : X ⊆ H.vertexSet := hVX.symm.subset
  have hfin : H.vertexSet.Finite := H.vertexSet_finite
  have : Finite ↑H.vertexSet := hfin.to_subtype
  rcases Finite.exists_equiv_fin ↑H.vertexSet with ⟨k, ⟨e⟩⟩
  let g_fin : Fin k → α := fun i => (e.symm i).1
  have hg_inj : Function.Injective g_fin := fun i j h => e.symm.injective (Subtype.ext h)
  have hg_img : g_fin '' univ = H.vertexSet := by
    ext w
    simp only [g_fin, image_univ, mem_range]
    exact ⟨by rintro ⟨i, rfl⟩; exact (e.symm i).2, fun hw => ⟨e ⟨w, hw⟩, by simp⟩⟩
  have hk_eq : H.vertexSet.ncard = k := by
    rw [← hg_img, hg_inj.injOn.ncard_image, ncard_univ, Nat.card_fin]
  have hk_le : k ≤ 3 := by rw [← hk_eq, hVX]; exact hX_card
  let idx : Fin k → Option (Fin 2) := fun i =>
    if i.1 = 0 then none else if i.1 = 1 then some 0 else some 1
  have hidx_inj : Function.Injective idx := by
    intro i j h
    have hi : i.1 < 3 := lt_of_lt_of_le i.2 hk_le
    have hj : j.1 < 3 := lt_of_lt_of_le j.2 hk_le
    dsimp [idx] at h
    split_ifs at h <;>
      first | exact Fin.ext (by omega) | cases h
  let S : Set (Option (Fin 2)) := range idx
  let f : Option (Fin 2) → α := fun a =>
    if ha : a ∈ S then (e.symm (Classical.choose ha)).1 else x₀
  have hf_idx : ∀ i : Fin k, f (idx i) = (e.symm i).1 := by
    intro i
    have ha : idx i ∈ S := ⟨i, rfl⟩
    simp only [f, ha, ↓reduceDIte]
    have h_spec : idx (Classical.choose ha) = idx i := Classical.choose_spec ha
    rw [hidx_inj h_spec]
  have hf_inj : InjOn f S := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h_eq
    rw [hf_idx i, hf_idx j] at h_eq
    exact congrArg idx (e.symm.injective (Subtype.ext h_eq))
  have hf_img : f '' S = H.vertexSet := by
    ext w
    simp only [S, mem_image, mem_range, exists_exists_eq_and, hf_idx]
    constructor
    · rintro ⟨i, rfl⟩; exact (e.symm i).2
    · intro hw; exact ⟨e ⟨w, hw⟩, by simp⟩
  refine canBeDrawnInDiscWithBoundary_of_fanEmbedding hX_sub x₀ hf_inj hf_img ?_
  rintro (_ | i) _ (_ | j) _ hab _
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · right; right
    refine ⟨i, j, rfl, rfl, ?_⟩
    fin_cases i <;> fin_cases j
    · exact (hab rfl).elim
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (hab rfl).elim

/-- Shape 2 of `CanBeDrawnInDisc21`: if `H` is an indexed path and `X ⊆ V(H)`, then `H` can be
drawn in the closed unit disc with `X` in the boundary. -/
theorem canBeDrawnInDiscWithBoundary_of_isIndexedPath {α : Type u} {β : Type v}
    {H : Hypergraph α β} {X : Set α} (hX_sub : X ⊆ H.vertexSet)
    {x₁ x₂ : α} (hpath : IsIndexedPath H x₁ x₂) :
    CanBeDrawnInDiscWithBoundary H X := by
  rcases hpath with ⟨m, _, v, hv_inj, _, _, hV, hadj_v⟩
  let S : Set (Option (Fin (m + 1))) := range some
  let f : Option (Fin (m + 1)) → α := fun a =>
    match a with
    | none => x₁
    | some i => v i
  have hf_inj : InjOn f S := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h_eq
    exact congrArg some (hv_inj h_eq)
  have hf_img : f '' S = H.vertexSet := by
    rw [hV]
    ext w
    simp [S, f]
  refine canBeDrawnInDiscWithBoundary_of_fanEmbedding hX_sub x₁ hf_inj hf_img ?_
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ hadj_ij
  exact Or.inr (Or.inr ⟨i, j, rfl, rfl, (hadj_v i j).mp hadj_ij⟩)

/-- Shape 3 of `CanBeDrawnInDisc21`: if `H` is a graph, `X ⊆ V(H)`, `v₀ ∈ X`, and `H \ {v₀}` is an
indexed path, then `H` can be drawn in the closed unit disc with `X` in the boundary. -/
theorem canBeDrawnInDiscWithBoundary_of_deleteVertices_isIndexedPath {α : Type u} {β : Type v}
    {H : Hypergraph α β} (hH : H.IsGraph) {X : Set α} (hX_sub : X ⊆ H.vertexSet)
    {v₀ x₁ x₂ : α} (hv₀ : v₀ ∈ X) (hpath : IsIndexedPath (H.deleteVertices {v₀}) x₁ x₂) :
    CanBeDrawnInDiscWithBoundary H X := by
  rcases hpath with ⟨m, _, v, hv_inj, _, _, hV_del, hadj_del⟩
  have hv_mem_del : ∀ i : Fin (m + 1), v i ∈ H.vertexSet \ {v₀} := by
    intro i
    change v i ∈ (H.deleteVertices {v₀}).vertexSet
    rw [hV_del]
    exact ⟨i, rfl⟩
  let S : Set (Option (Fin (m + 1))) := univ
  let f : Option (Fin (m + 1)) → α := fun a =>
    match a with
    | none => v₀
    | some i => v i
  have hf_inj : InjOn f S := by
    rintro (_ | i) _ (_ | j) _ h_eq
    · rfl
    · exfalso; exact (hv_mem_del j).2 h_eq.symm
    · exfalso; exact (hv_mem_del i).2 h_eq
    · exact congrArg some (hv_inj h_eq)
  have hf_img : f '' S = H.vertexSet := by
    ext w
    simp only [S, f, image_univ, mem_range]
    constructor
    · rintro ⟨_ | i, rfl⟩
      · exact hX_sub hv₀
      · exact (hv_mem_del i).1
    · intro hw
      by_cases hw_v₀ : w = v₀
      · subst hw_v₀; exact ⟨none, rfl⟩
      · have hw_del : w ∈ (H.deleteVertices {v₀}).vertexSet := ⟨hw, hw_v₀⟩
        rw [hV_del] at hw_del
        rcases hw_del with ⟨i, rfl⟩
        exact ⟨some i, rfl⟩
  refine canBeDrawnInDiscWithBoundary_of_fanEmbedding hX_sub v₀ hf_inj hf_img ?_
  rintro (_ | i) _ (_ | j) _ _ hadj_ij
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · right; right
    refine ⟨i, j, rfl, rfl, (hadj_del i j).mp ?_⟩
    rcases hadj_ij with ⟨hne_v, e, ha, hb⟩
    have heH : e ∈ H.edgeSet := H.edge_mem_of_inc ha
    have hfin_ends : (H.ends e).Finite :=
      H.vertexSet_finite.subset fun _ hw => H.vertex_mem_of_inc hw
    have hends_eq : H.ends e = {v i, v j} :=
      eq_pair_of_mem_of_ncard_le_two hfin_ends (hH e heH).2 ha hb hne_v
    have hno_v₀ : ∀ w ∈ ({v₀} : Set α), ¬ H.Inc e w := by
      intro w hw_eq hinc_w
      have hw_ends : w ∈ H.ends e := hinc_w
      rw [hends_eq, mem_singleton_iff.mp hw_eq] at hw_ends
      rcases hw_ends with h1 | h2
      · exact (hv_mem_del i).2 h1.symm
      · exact (hv_mem_del j).2 h2.symm
    exact ⟨hne_v, e, ⟨ha, hno_v₀⟩, ⟨hb, hno_v₀⟩⟩

/-- Each of the three shapes of `CanBeDrawnInDisc21 H X` implies `CanBeDrawnInDiscWithBoundary H X`
when `H` is a graph and `1 ≤ |X| ≤ 3`. -/
theorem canBeDrawnInDiscWithBoundary_of_canBeDrawnInDisc21 {α : Type u} {β : Type v}
    {H : Hypergraph α β} (hH : H.IsGraph) {X : Set α}
    (hX_ne : X.Nonempty) (hX_card : X.ncard ≤ 3)
    (h : CanBeDrawnInDisc21 H X) :
    CanBeDrawnInDiscWithBoundary H X := by
  rcases h with hVX | ⟨hX_sub, x₁, _, x₂, _, _, hpath⟩ | ⟨hX_sub, v₀, hv₀, x₁, _, x₂, _, _, hpath⟩
  · exact canBeDrawnInDiscWithBoundary_of_vertexSet_eq hVX hX_card hX_ne.some
  · exact canBeDrawnInDiscWithBoundary_of_isIndexedPath hX_sub hpath
  · exact canBeDrawnInDiscWithBoundary_of_deleteVertices_isIndexedPath hH hX_sub hv₀ hpath

/-- Every `IsPortrait` (with `CanBeDrawnInDiscWithBoundary` in (R9)) of a graph `G` is an
`IsPortrait21` (with `CanBeDrawnInDisc21` in (R9)). -/
theorem IsPortrait.toIsPortrait21 {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
    {G : Hypergraph α β} (hG : G.IsGraph)
    {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait G Γ ιN α_cell α_vert q_cuff) :
    IsPortrait21 G Γ ιN α_cell α_vert q_cuff where
  is_surface := hport.is_surface
  is_connected_surface := hport.is_connected_surface
  r1_painting := hport.r1_painting
  r1_injOn := hport.r1_injOn
  r1_subset := hport.r1_subset
  r2_cell_le := hport.r2_cell_le
  r2_cell_inter := hport.r2_cell_inter
  r3_union_V := hport.r3_union_V
  r3_union_E := hport.r3_union_E
  r3_edge_disjoint := hport.r3_edge_disjoint
  r4_vert := hport.r4_vert
  r5_cuff_pos := hport.r5_cuff_pos
  r5_cuff_card := hport.r5_cuff_card
  r6_border := hport.r6_border
  r7_inter := hport.r7_inter
  r8_order := hport.r8_order
  r9_three := fun c hc hcard3 h21 => by
    have hle := hport.r2_cell_le c hc
    have hHc : (α_cell c).IsGraph := fun e he => by
      rw [← hle.3 e he]
      exact hG e (hle.2 he)
    have htc_ne : (tilde c).Nonempty := nonempty_of_ncard_ne_zero (by omega)
    have hX_ne : (ιN '' tilde c).Nonempty := htc_ne.image ιN
    have hX_card : (ιN '' tilde c).ncard ≤ 3 :=
      (ncard_image_le (Γ.finite_tilde_cell hc)).trans hcard3.le
    exact hport.r9_three c hc hcard3
      (canBeDrawnInDiscWithBoundary_of_canBeDrawnInDisc21 hHc hX_ne hX_card h21)
  r10_null := hport.r10_null

/-- Every `PortraitHasDepthLe` of a graph `G` is a `PortraitHasDepthLe21`. -/
theorem PortraitHasDepthLe.toPortraitHasDepthLe21 {α : Type u} {β : Type v}
    {S : Type} [TopologicalSpace S]
    {G : Hypergraph α β} (hG : G.IsGraph)
    {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q : ℕ}
    (hd : PortraitHasDepthLe G Γ ιN α_cell α_vert q) :
    PortraitHasDepthLe21 G Γ ιN α_cell α_vert q := by
  rcases hd with ⟨q_cuff, hport, hq⟩
  exact ⟨q_cuff, hport.toIsPortrait21 hG, hq⟩

/-- Shape-based form of **Graph Minors XXI, (9.1)** (page 38 of the preprint) concluding
`CanBeDrawnInDisc21`. -/
theorem theorem_9_1_shapes {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
    {G L : Hypergraph α β} (hG : G.IsGraph)
    {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    (hL : IsVitalLinkage G L)
    {c : Set S} (hc : IsInternalCell Γ c) :
    (((α_cell c).vertexSet \ (ιN '' tilde c)) ∩ terminals L).Nonempty ∨
      CanBeDrawnInDisc21 (α_cell c) (ιN '' tilde c) := by
  by_cases hnonempty : (((α_cell c).vertexSet \ (ιN '' tilde c)) ∩ terminals L).Nonempty
  · exact Or.inl hnonempty
  · right
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hnonempty
    let B := internalCellCompl hport hc
    have hsep : G.IsSeparation B (α_cell c) := (isSeparation_internalCellCompl hport hc).symm
    have hM_vital : IsVitalLinkage (α_cell c) (L ∩ α_cell c) := (theorem_2_3_proof hL.1 hsep).2 hL
    have hM_term : terminals (L ∩ α_cell c) ⊆
        (terminals L \ B.vertexSet) ∪ (B ∩ α_cell c).vertexSet :=
      (theorem_2_2_proof hL.1 hsep).2
    have hHc_graph : (α_cell c).IsGraph := by
      have hle := hport.r2_cell_le c hc.1
      intro e he
      rw [← hle.3 e he]
      exact hG e (hle.2 he)
    have hX_sub : ιN '' tilde c ⊆ (α_cell c).vertexSet :=
      tilde_image_subset_cell_vertexSet hport hc.1
    have hX_card : (ιN '' tilde c).ncard ≤ 3 :=
      (ncard_image_le (Γ.finite_tilde_cell hc.1)).trans (Γ.ncard_tilde_cell_le hc.1)
    have hterm_sub_X : terminals (L ∩ α_cell c) ⊆ ιN '' tilde c := by
      intro w hw
      have hw_c : w ∈ (α_cell c).vertexSet := hw.1.2
      rcases hM_term hw with ⟨hw_termL, hw_not_B⟩ | hw_inter
      · exfalso
        have hw_not_tilde : w ∉ ιN '' tilde c := fun hwt => hw_not_B (Or.inr hwt)
        exact Set.disjoint_left.mp hnonempty ⟨hw_c, hw_not_tilde⟩ hw_termL
      · have hw_inter' : w ∈ (α_cell c ∩ B).vertexSet := ⟨hw_inter.2, hw_inter.1⟩
        rwa [inter_vertexSet_internalCellCompl hport hc] at hw_inter'
    exact canBeDrawnInDisc21_of_isVitalLinkage hHc_graph hM_vital hX_sub hX_card hterm_sub_X

/-- **Graph Minors XXI, (9.1)** (page 38 of the preprint):
"**9.1** *If $\Gamma, \alpha$ is a portrait in a surface $\Sigma$ of a graph $G$, and $L$ is a vital
linkage in $G$, then for every cell $c$ of $\Gamma$ which is not a border cell, either
$V(\alpha(c)) \setminus \tilde{c}$ contains a terminal of $L$, or $\alpha(c)$ can be drawn in a
disc with the members of $\tilde{c}$ drawn in the boundary.*" -/
theorem theorem_9_1_proof {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
    {G L : Hypergraph α β} (hG : G.IsGraph)
    {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait G Γ ιN α_cell α_vert q_cuff)
    (hL : IsVitalLinkage G L)
    {c : Set S} (hc : IsInternalCell Γ c) :
    (((α_cell c).vertexSet \ (ιN '' tilde c)) ∩ terminals L).Nonempty ∨
      CanBeDrawnInDiscWithBoundary (α_cell c) (ιN '' tilde c) := by
  have hport21 : IsPortrait21 G Γ ιN α_cell α_vert q_cuff := hport.toIsPortrait21 hG
  rcases theorem_9_1_shapes hG hport21 hL hc with hterm | hdraw
  · exact Or.inl hterm
  · right
    have hle := hport.r2_cell_le c hc.1
    have hHc : (α_cell c).IsGraph := fun e he => by
      rw [← hle.3 e he]
      exact hG e (hle.2 he)
    have htc_23 := hport.r1_painting c hc.1
    have htc_ne : (tilde c).Nonempty := nonempty_of_ncard_ne_zero (by omega)
    have hX_ne : (ιN '' tilde c).Nonempty := htc_ne.image ιN
    have hX_card : (ιN '' tilde c).ncard ≤ 3 :=
      (ncard_image_le (Γ.finite_tilde_cell hc.1)).trans (Γ.ncard_tilde_cell_le hc.1)
    exact canBeDrawnInDiscWithBoundary_of_canBeDrawnInDisc21 hHc hX_ne hX_card hdraw

/-! ## 2. Painting Cells, Border Spaces, and Cuff Supports -/

variable {S : Type} [TopologicalSpace S]

theorem exists_two_distinct_of_ncard_ge_two {γ : Type*} {X : Set γ} (h : 2 ≤ X.ncard) :
    ∃ u ∈ X, ∃ v ∈ X, u ≠ v := by
  obtain ⟨u, hu⟩ : X.Nonempty := nonempty_of_ncard_ne_zero (by omega)
  have hdiff_ne : (X \ {u}).ncard ≠ 0 := by
    by_cases hfin : X.Finite
    · have hcard_u : ({u} : Set γ).ncard = 1 := ncard_singleton u
      have hsub : {u} ⊆ X := singleton_subset_iff.mpr hu
      have := ncard_sdiff_add_ncard_of_subset hsub hfin
      omega
    · rw [Infinite.ncard hfin] at h
      omega
  obtain ⟨v, hv, hvu⟩ := nonempty_of_ncard_ne_zero hdiff_ne
  exact ⟨u, hu, v, hv, Ne.symm (mem_singleton_iff.not.mp hvu)⟩

/-- Every cell `c ∈ Γ.C` of a Section 9 painting `Γ` in a surface `S` is infinite. -/
theorem infinite_cell_of_painting (hS : IsSurface S) {Γ : GM17.Painting S}
    (hpaint : IsPainting21 Γ) {c : Set S} (hc : c ∈ Γ.C) :
    c.Infinite := by
  have : T2Space S := hS.2.1
  have hcard_ge2 : 2 ≤ (tilde c).ncard := by
    rcases hpaint c hc with h2 | h3 <;> omega
  obtain ⟨u, hu, v, hv, huv⟩ := exists_two_distinct_of_ncard_ge_two hcard_ge2
  have hdisc : IsClosedDisc (closure c) := Γ.isClosedDisc_closure_cell hc
  have hu_bd : u ∈ discBd (closure c) := Γ.tilde_subset_discBd hc hu
  have hv_bd : v ∈ discBd (closure c) := Γ.tilde_subset_discBd hc hv
  obtain ⟨F, hF_sub, hF_line, _, _⟩ := exists_chord_in_closedDisc hdisc hu_bd hv_bd huv
  rcases hF_line with ⟨f, _, _⟩
  have hF_inf : F.Infinite := by
    have : Infinite unitInterval := by
      let g : ℕ → unitInterval := fun n =>
        ⟨1 / (n + 2 : ℝ), by positivity, by rw [div_le_one (by positivity)]; linarith⟩
      refine Infinite.of_injective g fun m n h => ?_
      have hval : (1 : ℝ) / (m + 2 : ℝ) = 1 / (n + 2 : ℝ) := congrArg Subtype.val h
      have hm : (0 : ℝ) < m + 2 := by positivity
      have hn : (0 : ℝ) < n + 2 := by positivity
      have h_eq : (m : ℝ) + 2 = (n : ℝ) + 2 := by
        have := (div_eq_div_iff hm.ne' hn.ne').mp hval
        linarith
      have hmn : (m : ℝ) = (n : ℝ) := by linarith
      exact Nat.cast_injective hmn
    have hinj : Function.Injective (fun t : unitInterval => (f t).1) :=
      fun t₁ t₂ h => f.injective (Subtype.ext h)
    have hrange : Set.range (fun t : unitInterval => (f t).1) ⊆ F := by
      rintro _ ⟨t, rfl⟩; exact (f t).2
    exact (Set.infinite_range_of_injective hinj).mono hrange
  have hcl_inf : (closure c).Infinite := hF_inf.mono hF_sub
  have hc_eq : c = closure c \ tilde c := by
    ext x
    simp only [tilde, mem_sdiff, not_and, not_not]
    exact ⟨fun hxc => ⟨subset_closure hxc, fun _ => hxc⟩, fun ⟨hxcl, h⟩ => h hxcl⟩
  rw [hc_eq]
  exact hcl_inf.sdiff (Γ.finite_tilde_cell hc)

/-- Every cuff `C ∈ cuffs S` contains at least 2 nodes of a painting `Γ`. -/
theorem cuff_nodes_ge_two_of_painting (hS : IsSurface S) (Γ : GM17.Painting S) :
    ∀ C ∈ cuffs S, 2 ≤ (Γ.N ∩ C).ncard := by
  have : T2Space S := hS.2.1
  intro C hC
  let f := cuffHomeo hS hC
  have hC_inf : C.Infinite := by
    have hinj : InjOn (cuffPoint f) (Ico 0 (0 + 2 * Real.pi)) := cuffPoint_injOn_Ico f 0
    have hIco_inf : (Ico (0 : ℝ) (0 + 2 * Real.pi)).Infinite :=
      Ico_infinite (by linarith [Real.pi_pos])
    have himg_inf : (cuffPoint f '' Ico 0 (0 + 2 * Real.pi)).Infinite := hIco_inf.image hinj
    refine himg_inf.mono ?_
    rintro _ ⟨t, _, rfl⟩
    exact GM19.cuffPoint_mem f t
  obtain ⟨x, hxC, hx_notN⟩ := (hC_inf.sdiff Γ.finite_N).nonempty
  have hx_bd : x ∈ bd S \ Γ.N := by
    refine ⟨?_, hx_notN⟩
    rw [← sUnion_cuffs (S := S)]
    exact ⟨C, hC, hxC⟩
  obtain ⟨c, ⟨hc, hxc⟩, _⟩ := Γ.exists_border_cell_of_mem_bd hx_bd
  have hbd_c : (c ∩ bd S).Nonempty := ⟨x, hxc, hx_bd.1⟩
  have hC_c : (c ∩ C).Nonempty := ⟨x, hxc, hxC⟩
  obtain ⟨u, v, huv, htilde, _, _, _, _⟩ := Γ.border_cell_exists_ends hc hbd_c
  have htilde_sub : tilde c ⊆ Γ.N ∩ C := (Γ.border_cell_subset_cuff hc hC hC_c).2.2.2.1
  rw [htilde] at htilde_sub
  have hfin : (Γ.N ∩ C).Finite := Γ.finite_N.subset inter_subset_left
  calc 2 = ({u, v} : Set S).ncard := (ncard_pair huv).symm
    _ ≤ (Γ.N ∩ C).ncard := ncard_le_ncard htilde_sub hfin

/-- For every border cell `c ∈ Γ.C`, `closure (c ∩ bd S) = closure c ∩ bd S`. -/
theorem closure_border_cell_inter_bd (hS : IsSurface S) (Γ : GM17.Painting S)
    {c : Set S} (hc : c ∈ Γ.C) (hbd : (c ∩ bd S).Nonempty) :
    closure (c ∩ bd S) = closure c ∩ bd S := by
  have : T2Space S := hS.2.1
  obtain ⟨u, v, _, _, hL₀, hdiff, _, _⟩ := Γ.border_cell_exists_ends hc hbd
  refine Subset.antisymm (closure_minimal (inter_subset_inter_left _ subset_closure)
    hL₀.isCompact.isClosed) ?_
  rcases hL₀ with ⟨f, rfl, rfl⟩
  intro z hz
  let t : unitInterval := f.symm ⟨z, hz⟩
  have hft : (f t).1 = z := congrArg Subtype.val (f.apply_symm_apply ⟨z, hz⟩)
  have hcont : Continuous (fun s : unitInterval => (f s).1) :=
    continuous_subtype_val.comp f.continuous
  have hIoo_sub : (fun s : unitInterval => (f s).1) '' Ioo (0 : unitInterval) 1 ⊆ c ∩ bd S := by
    rw [hdiff]
    rintro _ ⟨s, ⟨hs0, hs1⟩, rfl⟩
    refine ⟨(f s).2, ?_⟩
    rintro (h0 | h1)
    · exact hs0.ne (f.injective (Subtype.ext h0)).symm
    · exact hs1.ne (f.injective (Subtype.ext h1))
  have ht_cl : t ∈ closure (Ioo (0 : unitInterval) 1) := by
    have hcl_eq : closure (Ioo (0 : unitInterval) 1) = univ := by
      ext s
      simp only [mem_univ, iff_true]
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
      have hs1 : (s : ℝ) ≤ 1 := s.2.2
      let r : ℝ := min (ε / 2) (1 / 2)
      have hr_pos : 0 < r := lt_min (half_pos hε) (by norm_num)
      have hr_le : r ≤ 1 / 2 := min_le_right _ _
      let y_real : ℝ := (1 - r) * (s : ℝ) + r * (1 / 2)
      have hy0 : 0 < y_real := by
        have h1 : 0 ≤ (1 - r) * (s : ℝ) := mul_nonneg (by linarith) hs0
        have h2 : 0 < r * (1 / 2) := mul_pos hr_pos (by norm_num)
        dsimp [y_real]
        linarith
      have hy1 : y_real < 1 := by
        have h1 : (1 - r) * (s : ℝ) ≤ 1 - r := mul_le_of_le_one_right (by linarith) hs1
        dsimp [y_real]
        linarith
      let y : unitInterval := ⟨y_real, hy0.le, hy1.le⟩
      refine ⟨y, ⟨Subtype.mk_lt_mk.mpr hy0, Subtype.mk_lt_mk.mpr hy1⟩, ?_⟩
      change |(s : ℝ) - y_real| < ε
      have hdiff_y : (s : ℝ) - y_real = r * ((s : ℝ) - 1 / 2) := by dsimp [y_real]; ring
      have habs_s : |(s : ℝ) - 1 / 2| ≤ 1 / 2 := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
      rw [hdiff_y, abs_mul, abs_of_pos hr_pos]
      have hle1 : r * |(s : ℝ) - 1 / 2| ≤ r * (1 / 2) :=
        mul_le_mul_of_nonneg_left habs_s hr_pos.le
      have hle2 : r ≤ ε / 2 := min_le_left _ _
      linarith
    rw [hcl_eq]
    exact mem_univ t
  have hz_cl := image_closure_subset_closure_image hcont ⟨t, ht_cl, hft⟩
  exact closure_mono hIoo_sub hz_cl

/-- If a drawing `Γ'` has `Γ'.V ∩ bd S = Γ.N ∩ bd S`, then for every border cell `c ∈ Γ.C`,
`c ∩ bd S ∈ drawingSpaces Γ'`, and for its ends `tilde c = {u, v}`,
`SpaceHasEnds Γ' (c ∩ bd S) u v`. -/
theorem border_cell_space_mem_drawingSpaces (hS : IsSurface S)
    {Γ : GM17.Painting S} {Γ' : Surface.Drawing S}
    (hV_bd : Γ'.V ∩ bd S = Γ.N ∩ bd S)
    {c : Set S} (hc : c ∈ Γ.C) (hbd : (c ∩ bd S).Nonempty) :
    c ∩ bd S ∈ drawingSpaces Γ' ∧
    ∀ u v : S, u ≠ v → tilde c = {u, v} → SpaceHasEnds Γ' (c ∩ bd S) u v := by
  have : T2Space S := hS.2.1
  have hbd_diff_eq : bd S \ Γ'.V = bd S \ Γ.N := by
    ext x
    simp only [mem_sdiff]
    exact ⟨fun ⟨hxbd, hxV⟩ => ⟨hxbd, fun hxN => hxV ((Set.ext_iff.mp hV_bd x).mpr ⟨hxN, hxbd⟩).1⟩,
           fun ⟨hxbd, hxN⟩ => ⟨hxbd, fun hxV => hxN ((Set.ext_iff.mp hV_bd x).mp ⟨hxV, hxbd⟩).1⟩⟩
  obtain ⟨u₀, v₀, huv₀, htilde₀, hL₀, hdiff₀, hu₀_mem, hv₀_mem⟩ :=
    Γ.border_cell_exists_ends hc hbd
  have hc_conn : IsConnected (c ∩ bd S) := by
    rcases hL₀ with ⟨f, rfl, rfl⟩
    rw [hdiff₀]
    have h_img : (closure c ∩ bd S) \ {(f 0).1, (f 1).1} =
        (fun t : unitInterval => (f t).1) '' Ioo (0 : unitInterval) 1 := by
      ext z
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or, mem_image, mem_Ioo]
      constructor
      · rintro ⟨hz, hz0, hz1⟩
        refine ⟨f.symm ⟨z, hz⟩, ⟨?_, ?_⟩, congrArg Subtype.val (f.apply_symm_apply ⟨z, hz⟩)⟩
        · refine lt_of_le_of_ne (f.symm ⟨z, hz⟩).2.1 fun h_eq => hz0 ?_
          have h0 : (f (0 : unitInterval)).1 = (f (f.symm ⟨z, hz⟩)).1 :=
            congrArg (fun t => (f t).1) h_eq
          rw [h0]
          exact (congrArg Subtype.val (f.apply_symm_apply ⟨z, hz⟩)).symm
        · refine lt_of_le_of_ne (f.symm ⟨z, hz⟩).2.2 fun h_eq => hz1 ?_
          have h1 : (f (f.symm ⟨z, hz⟩)).1 = (f (1 : unitInterval)).1 :=
            congrArg (fun t => (f t).1) h_eq
          rw [← h1]
          exact (congrArg Subtype.val (f.apply_symm_apply ⟨z, hz⟩)).symm
      · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
        refine ⟨(f t).2, ?_, ?_⟩
        · intro h0; exact ht0.ne (f.injective (Subtype.ext h0)).symm
        · intro h1; exact ht1.ne (f.injective (Subtype.ext h1))
    rw [h_img]
    exact isConnected_Ioo (by exact Subtype.mk_lt_mk.mpr zero_lt_one) |>.image _
      (continuous_subtype_val.comp f.continuous).continuousOn
  have hc_sub_diff : c ∩ bd S ⊆ bd S \ Γ'.V := by
    rw [hbd_diff_eq]
    rintro x ⟨hxc, hxbd⟩
    exact ⟨hxbd, Set.disjoint_left.mp (Γ.cell_disjoint_N hc) hxc⟩
  rcases hbd with ⟨x₀, hx₀c, hx₀bd⟩
  have hx₀_diff : x₀ ∈ bd S \ Γ'.V := hc_sub_diff ⟨hx₀c, hx₀bd⟩
  let s := connectedComponentIn (bd S \ Γ'.V) x₀
  have hs_mem : s ∈ drawingSpaces Γ' := ⟨x₀, hx₀_diff, rfl⟩
  have hc_sub_s : c ∩ bd S ⊆ s :=
    hc_conn.isPreconnected.subset_connectedComponentIn ⟨hx₀c, hx₀bd⟩ hc_sub_diff
  have hs_sub_c : s ⊆ c ∩ bd S := by
    have hs_pre : IsPreconnected s := (isConnected_of_mem_drawingSpaces hs_mem).isPreconnected
    have hs_sub_N : s ⊆ bd S \ Γ.N := by
      rw [← hbd_diff_eq]
      exact connectedComponentIn_subset (bd S \ Γ'.V) x₀
    let F₁ : Set S := closure c
    let F₂ : Set S := ⋃ c' ∈ Γ.C \ {c}, closure c'
    have hcF₁ : IsClosed F₁ := isClosed_closure
    have hcF₂ : IsClosed F₂ := (Γ.finite_cells.sdiff).isClosed_biUnion fun _ _ => isClosed_closure
    have hs_cov : s ⊆ F₁ ∪ F₂ := by
      intro z hzs
      obtain ⟨c', ⟨hc', hzc'⟩, _⟩ := Γ.exists_border_cell_of_mem_bd (hs_sub_N hzs)
      by_cases h_eq : c' = c
      · subst h_eq; exact Or.inl (subset_closure hzc')
      · exact Or.inr (mem_biUnion ⟨hc', h_eq⟩ (subset_closure hzc'))
    have hs_disj_F₂ : Disjoint s F₂ := by
      rw [disjoint_iff_inter_eq_empty]
      ext z
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hzs hzF₂
      have hz_N : z ∈ bd S \ Γ.N := hs_sub_N hzs
      have hz_not_F₁ : z ∉ F₁ := by
        intro hzF₁
        rw [mem_iUnion₂] at hzF₂
        rcases hzF₂ with ⟨c', ⟨hc', hc'_ne⟩, hzc'_cl⟩
        have hzc : z ∈ c := by rw [← Γ.closure_cell_diff_N hc]; exact ⟨hzF₁, hz_N.2⟩
        have hzc' : z ∈ c' := by rw [← Γ.closure_cell_diff_N hc']; exact ⟨hzc'_cl, hz_N.2⟩
        exact hc'_ne (Γ.cell_eq_of_mem hc' hc hzc' hzc)
      obtain ⟨w, hws, hwF₁, hwF₂⟩ := isPreconnected_closed_iff.mp hs_pre F₁ F₂ hcF₁ hcF₂ hs_cov
        ⟨x₀, hc_sub_s ⟨hx₀c, hx₀bd⟩, subset_closure hx₀c⟩ ⟨z, hzs, hzF₂⟩
      have hw_N : w ∈ bd S \ Γ.N := hs_sub_N hws
      rw [mem_iUnion₂] at hwF₂
      rcases hwF₂ with ⟨c', ⟨hc', hc'_ne⟩, hwc'_cl⟩
      have hwc : w ∈ c := by rw [← Γ.closure_cell_diff_N hc]; exact ⟨hwF₁, hw_N.2⟩
      have hwc' : w ∈ c' := by rw [← Γ.closure_cell_diff_N hc']; exact ⟨hwc'_cl, hw_N.2⟩
      exact hc'_ne (Γ.cell_eq_of_mem hc' hc hwc' hwc)
    intro z hzs
    have hzF₁ : z ∈ F₁ := (hs_cov hzs).resolve_right (Set.disjoint_left.mp hs_disj_F₂ hzs)
    have hz_N : z ∈ bd S \ Γ.N := hs_sub_N hzs
    have hzc : z ∈ c := by rw [← Γ.closure_cell_diff_N hc]; exact ⟨hzF₁, hz_N.2⟩
    exact ⟨hzc, hz_N.1⟩
  have hc_eq_s : c ∩ bd S = s := Subset.antisymm hc_sub_s hs_sub_c
  have hc_mem_spaces : c ∩ bd S ∈ drawingSpaces Γ' := hc_eq_s ▸ hs_mem
  refine ⟨hc_mem_spaces, ?_⟩
  intro u v huv htilde
  have hpair_eq : ({u, v} : Set S) = {u₀, v₀} := by rw [← htilde, htilde₀]
  have hu_in : u ∈ ({u₀, v₀} : Set S) := by rw [← hpair_eq]; exact Or.inl rfl
  have hv_in : v ∈ ({u₀, v₀} : Set S) := by rw [← hpair_eq]; exact Or.inr rfl
  have hcl_eq : closure (c ∩ bd S) = closure c ∩ bd S :=
    closure_border_cell_inter_bd hS Γ hc ⟨x₀, hx₀c, hx₀bd⟩
  have hcl_union : closure (c ∩ bd S) = c ∩ bd S ∪ {u₀, v₀} := by
    rw [hcl_eq, hdiff₀]
    ext z
    simp only [mem_union, mem_sdiff, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro hz
      by_cases h : z = u₀ ∨ z = v₀
      · exact Or.inr h
      · exact Or.inl ⟨hz, h⟩
    · rintro (⟨hz, _⟩ | rfl | rfl)
      · exact hz
      · exact hL₀.left_mem
      · exact hL₀.right_mem
  have hu₀_V : u₀ ∈ Γ'.V ∩ bd S := hV_bd.symm ▸ hu₀_mem
  have hv₀_V : v₀ ∈ Γ'.V ∩ bd S := hV_bd.symm ▸ hv₀_mem
  rcases hu_in with rfl | rfl <;> rcases hv_in with rfl | rfl
  · exact (huv rfl).elim
  · exact ⟨hc_mem_spaces, hu₀_V, hv₀_V, huv, hcl_union ▸ hcl_eq ▸ hL₀, hcl_union⟩
  · have hcl_union' : closure (c ∩ bd S) = c ∩ bd S ∪ {u, v} := by
      rw [hcl_union, pair_comm]
    exact ⟨hc_mem_spaces, hv₀_V, hu₀_V, huv, hcl_union' ▸ hcl_eq ▸ hL₀.symm, hcl_union'⟩
  · exact (huv rfl).elim

theorem nonempty_of_mem_drawingSpaces {Γ : Surface.Drawing S} {s : Set S}
    (hs : s ∈ drawingSpaces Γ) : s.Nonempty :=
  (isConnected_of_mem_drawingSpaces hs).1

/-- Every space `s ∈ drawingSpaces Γ'` is of the form `c ∩ bd S` for a unique border cell `c ∈ Γ.C`. -/
theorem exists_border_cell_of_mem_drawingSpaces (hS : IsSurface S)
    {Γ : GM17.Painting S} {Γ' : Surface.Drawing S}
    (hV_bd : Γ'.V ∩ bd S = Γ.N ∩ bd S)
    {s : Set S} (hs : s ∈ drawingSpaces Γ') :
    ∃! c, c ∈ Γ.C ∧ (c ∩ bd S).Nonempty ∧ c ∩ bd S = s := by
  rcases hs with ⟨x, hx_diff', rfl⟩
  have hxs : x ∈ connectedComponentIn (bd S \ Γ'.V) x := mem_connectedComponentIn hx_diff'
  have hx_diff : x ∈ bd S \ Γ.N :=
    ⟨hx_diff'.1, fun hxN => hx_diff'.2 ((Set.ext_iff.mp hV_bd x).mpr ⟨hxN, hx_diff'.1⟩).1⟩
  obtain ⟨c, ⟨hc, hxc⟩, hc_uniq⟩ := Γ.exists_border_cell_of_mem_bd hx_diff
  have hbd : (c ∩ bd S).Nonempty := ⟨x, hxc, hx_diff.1⟩
  have hc_space : c ∩ bd S ∈ drawingSpaces Γ' :=
    (border_cell_space_mem_drawingSpaces hS hV_bd hc hbd).1
  rcases hc_space with ⟨y₂, hy₂, h_eq₂⟩
  have h_eq : c ∩ bd S = connectedComponentIn (bd S \ Γ'.V) x := by
    have hxy₂ : x ∈ connectedComponentIn (bd S \ Γ'.V) y₂ := h_eq₂.symm ▸ ⟨hxc, hx_diff.1⟩
    rw [← h_eq₂]
    exact connectedComponentIn_eq hxy₂
  refine ⟨c, ⟨hc, hbd, h_eq⟩, ?_⟩
  rintro c' ⟨hc', _, hc'_eq⟩
  have hxc' : x ∈ c' := (hc'_eq.symm ▸ hxs).1
  exact hc_uniq c' ⟨hc', hxc'⟩

/-- If `c' ∈ Γ.C` has `(tilde c').ncard = 3`, then at most 3 border cells `c ∈ Γ.C` satisfy
`tilde c ⊆ tilde c'`. -/
theorem ncard_border_cells_subset_three_le (hS : IsSurface S) (Γ : GM17.Painting S)
    {c' : Set S} (hc' : c' ∈ Γ.C) (hcard3 : (tilde c').ncard = 3) :
    {c ∈ Γ.C | (c ∩ bd S).Nonempty ∧ tilde c ⊆ tilde c'}.ncard ≤ 3 := by
  have : T2Space S := hS.2.1
  let V := Γ.N ∩ bd S
  have hV_fin : V.Finite := Γ.finite_N.subset inter_subset_left
  have hempty_arc : arcComponentsIn (V \ V) = ∅ := by
    ext e
    simp only [arcComponentsIn, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨⟨x, hxe⟩, he_sub, _⟩
    exact (he_sub hxe).2 (he_sub hxe).1
  let Γ₀ : Surface.Drawing S :=
    { U := V
      V := V
      V_subset_U := Subset.rfl
      isClosed_U := hV_fin.isClosed
      finite_V := hV_fin
      finite_edges := by rw [hempty_arc]; exact finite_empty
      edge_cond := by rw [hempty_arc]; rintro _ ⟨⟩ }
  have hV₀_bd : Γ₀.V ∩ bd S = Γ.N ∩ bd S := by
    ext x; simp only [Γ₀, V, mem_inter_iff]; tauto
  have hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ₀.V ∩ C).ncard := by
    intro C hC
    have h_eq : Γ₀.V ∩ C = Γ.N ∩ C := by
      ext x
      simp only [Γ₀, V, mem_inter_iff]
      refine ⟨fun ⟨⟨hxN, _⟩, hxC⟩ => ⟨hxN, hxC⟩, fun ⟨hxN, hxC⟩ => ⟨⟨hxN, ?_⟩, hxC⟩⟩
      rw [← sUnion_cuffs (S := S)]
      exact ⟨C, hC, hxC⟩
    rw [h_eq]
    exact cuff_nodes_ge_two_of_painting hS Γ C hC
  obtain ⟨w₁, w₂, w₃, hw₁₂, hw₁₃, hw₂₃, htilde_c'⟩ :
      ∃ w₁ w₂ w₃ : S, w₁ ≠ w₂ ∧ w₁ ≠ w₃ ∧ w₂ ≠ w₃ ∧ tilde c' = {w₁, w₂, w₃} := by
    have hfin := Γ.finite_tilde_cell hc'
    obtain ⟨w₁, hw₁⟩ : (tilde c').Nonempty := nonempty_of_ncard_ne_zero (by omega)
    have hsub₁ : {w₁} ⊆ tilde c' := singleton_subset_iff.mpr hw₁
    have hcard_diff : (tilde c' \ {w₁}).ncard = 2 := by
      have := ncard_sdiff_add_ncard_of_subset hsub₁ hfin
      rw [ncard_singleton] at this
      omega
    obtain ⟨w₂, ⟨hw₂, hw₂₁⟩, w₃, ⟨hw₃, hw₃₁⟩, hw₂₃⟩ :=
      exists_two_distinct_of_ncard_ge_two (by omega : 2 ≤ (tilde c' \ {w₁}).ncard)
    have hw₁₂ : w₁ ≠ w₂ := Ne.symm (mem_singleton_iff.not.mp hw₂₁)
    have hw₁₃ : w₁ ≠ w₃ := Ne.symm (mem_singleton_iff.not.mp hw₃₁)
    have hsub3 : ({w₁, w₂, w₃} : Set S) ⊆ tilde c' := by
      rintro z (rfl | rfl | rfl) <;> assumption
    have hcard_triple : ({w₁, w₂, w₃} : Set S).ncard = 3 := by
      rw [ncard_insert_of_notMem, ncard_pair hw₂₃]
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨hw₁₂, hw₁₃⟩
    exact ⟨w₁, w₂, w₃, hw₁₂, hw₁₃, hw₂₃,
      (eq_of_subset_of_ncard_le hsub3 (by omega) hfin).symm⟩
  let B := {c ∈ Γ.C | (c ∩ bd S).Nonempty ∧ tilde c ⊆ tilde c'}
  have hB_fin : B.Finite := Γ.finite_cells.subset fun _ h => h.1
  -- Case split on whether two distinct cells c₁, c₂ ∈ B have the same tilde
  by_cases h_dup : ∃ c₁ ∈ B, ∃ c₂ ∈ B, c₁ ≠ c₂ ∧ tilde c₁ = tilde c₂
  · rcases h_dup with ⟨c₁, ⟨hc₁, hbd₁, hsub₁⟩, c₂, ⟨hc₂, hbd₂, _⟩, hne₁₂, htilde_eq⟩
    obtain ⟨u, v, huv, htilde₁, _, _, hu_mem, hv_mem⟩ := Γ.border_cell_exists_ends hc₁ hbd₁
    have htilde₂ : tilde c₂ = {u, v} := htilde_eq.symm ▸ htilde₁
    obtain ⟨hs₁_mem, hs₁_ends⟩ := border_cell_space_mem_drawingSpaces hS hV₀_bd hc₁ hbd₁
    obtain ⟨hs₂_mem, hs₂_ends⟩ := border_cell_space_mem_drawingSpaces hS hV₀_bd hc₂ hbd₂
    have hs₁ := hs₁_ends u v huv htilde₁
    have hs₂ := hs₂_ends u v huv htilde₂
    obtain ⟨C, hC, hs₁C, _⟩ := exists_cuff_of_mem_drawingSpaces hS hge2 hs₁_mem
    have hu_C : u ∈ C := by
      have hcl_sub : closure (c₁ ∩ bd S) ⊆ C :=
        closure_minimal hs₁C (isClosed_cuff_univ hS hC)
      exact hcl_sub (hs₁.2.2.2.2.2.symm ▸ Or.inr (Or.inl rfl))
    obtain ⟨C₂, hC₂, hs₂C₂, _⟩ := exists_cuff_of_mem_drawingSpaces hS hge2 hs₂_mem
    have hu_C₂ : u ∈ C₂ := by
      have hcl_sub : closure (c₂ ∩ bd S) ⊆ C₂ :=
        closure_minimal hs₂C₂ (isClosed_cuff_univ hS hC₂)
      exact hcl_sub (hs₂.2.2.2.2.2.symm ▸ Or.inr (Or.inl rfl))
    have hC_eq : C = C₂ := by
      by_contra hne_C
      exact Set.disjoint_left.mp (cuffs_disjoint hC hC₂ hne_C) hu_C hu_C₂
    subst hC_eq
    let f := cuffHomeo hS hC
    have hk := hge2 C hC
    obtain ⟨i₁, hi₁_eq⟩ := exists_index_of_mem_drawingSpaces_subset_cuff hS hge2 hs₁_mem hC hs₁C f
    obtain ⟨i₂, hi₂_eq⟩ := exists_index_of_mem_drawingSpaces_subset_cuff hS hge2 hs₂_mem hC hs₂C₂ f
    have hi₁₂_ne : i₁ ≠ i₂ := by
      intro h_eq
      have hs_eq : c₁ ∩ bd S = c₂ ∩ bd S := by rw [hi₁_eq, hi₂_eq, h_eq]
      rcases hbd₁ with ⟨x, hxc₁, hxbd⟩
      have hxc₂_bd : x ∈ c₂ ∩ bd S := hs_eq ▸ ⟨hxc₁, hxbd⟩
      exact hne₁₂ (Γ.cell_eq_of_mem hc₁ hc₂ hxc₁ hxc₂_bd.1)
    have hends₁ := spaceHasEnds_vSpaceArc hS hge2 hC f i₁
    have hends₂ := spaceHasEnds_vSpaceArc hS hge2 hC f i₂
    have hpair₁ := ends_pair_eq_of_spaceHasEnds (hi₁_eq ▸ hs₁) hends₁
    have hpair₂ := ends_pair_eq_of_spaceHasEnds (hi₂_eq ▸ hs₂) hends₂
    have hnodes_eq :
        ({vNode Γ₀.V Γ₀.finite_V f i₁, vNode Γ₀.V Γ₀.finite_V f (nextFin hk i₁)} : Set S) =
        {vNode Γ₀.V Γ₀.finite_V f i₂, vNode Γ₀.V Γ₀.finite_V f (nextFin hk i₂)} :=
      hpair₁.symm.trans hpair₂
    have hi₁_in : vNode Γ₀.V Γ₀.finite_V f i₁ ∈
        ({vNode Γ₀.V Γ₀.finite_V f i₂, vNode Γ₀.V Γ₀.finite_V f (nextFin hk i₂)} : Set S) := by
      rw [← hnodes_eq]; exact Or.inl rfl
    have hnext₁_in : vNode Γ₀.V Γ₀.finite_V f (nextFin hk i₁) ∈
        ({vNode Γ₀.V Γ₀.finite_V f i₂, vNode Γ₀.V Γ₀.finite_V f (nextFin hk i₂)} : Set S) := by
      rw [← hnodes_eq]; exact Or.inr rfl
    have hi₁_eq_next₂ : i₁ = nextFin hk i₂ := by
      rcases hi₁_in with h | h
      · exact (hi₁₂_ne (injective_vNode Γ₀.V Γ₀.finite_V f h)).elim
      · exact injective_vNode Γ₀.V Γ₀.finite_V f h
    have hnext₁_eq_i₂ : nextFin hk i₁ = i₂ := by
      rcases hnext₁_in with h | h
      · exact injective_vNode Γ₀.V Γ₀.finite_V f h
      · exfalso
        have := (bijective_nextFin hk).1 (injective_vNode Γ₀.V Γ₀.finite_V f h)
        exact hi₁₂_ne this
    have hk_eq_2 : (Γ₀.V ∩ C).ncard = 2 := by
      have h1 : i₁.1 = (i₂.1 + 1) % (Γ₀.V ∩ C).ncard := by
        simpa [nextFin] using congrArg Fin.val hi₁_eq_next₂
      have h2 : i₂.1 = (i₁.1 + 1) % (Γ₀.V ∩ C).ncard := by
        simpa [nextFin] using congrArg Fin.val hnext₁_eq_i₂.symm
      have hi₁_lt := i₁.2
      have hi₂_lt := i₂.2
      have hmod₁ : (i₁.1 + 1) % (Γ₀.V ∩ C).ncard =
          if i₁.1 + 1 < (Γ₀.V ∩ C).ncard then i₁.1 + 1 else 0 := by
        split_ifs with hlt
        · exact Nat.mod_eq_of_lt hlt
        · have heq : i₁.1 + 1 = (Γ₀.V ∩ C).ncard := by omega
          rw [heq, Nat.mod_self]
      have hmod₂ : (i₂.1 + 1) % (Γ₀.V ∩ C).ncard =
          if i₂.1 + 1 < (Γ₀.V ∩ C).ncard then i₂.1 + 1 else 0 := by
        split_ifs with hlt
        · exact Nat.mod_eq_of_lt hlt
        · have heq : i₂.1 + 1 = (Γ₀.V ∩ C).ncard := by omega
          rw [heq, Nat.mod_self]
      rw [hmod₂] at h1
      rw [hmod₁] at h2
      split_ifs at h1 h2 <;> omega
    have hV₀C_eq_uv : Γ₀.V ∩ C = {u, v} := by
      have hsub_uv : {u, v} ⊆ Γ₀.V ∩ C := by
        rw [hpair₁]
        rintro z (rfl | rfl) <;> exact vNode_mem Γ₀.V Γ₀.finite_V f _
      exact (eq_of_subset_of_ncard_le hsub_uv (by rw [hk_eq_2, ncard_pair huv])
        (Γ₀.finite_V.inter_of_left C)).symm
    -- Every cell c ∈ B must have tilde c = {u, v} and hence c ∈ {c₁, c₂}
    have hB_sub_pair : B ⊆ {c₁, c₂} := by
      rintro c ⟨hc, hbd, hsub⟩
      obtain ⟨x, y, hxy, htilde_c, _, _, hx_mem, hy_mem⟩ := Γ.border_cell_exists_ends hc hbd
      obtain ⟨hs_mem, hs_ends⟩ := border_cell_space_mem_drawingSpaces hS hV₀_bd hc hbd
      obtain ⟨C', hC', hsC', _⟩ := exists_cuff_of_mem_drawingSpaces hS hge2 hs_mem
      have htilde_C' : tilde c ⊆ Γ.N ∩ C' := by
        rcases nonempty_of_mem_drawingSpaces hs_mem with ⟨z, hzs⟩
        exact (Γ.border_cell_subset_cuff hc hC' ⟨z, hzs.1, hsC' hzs⟩).2.2.2.1
      have hxy_sub_uv_or : ({x, y} : Set S) ⊆ tilde c' := htilde_c ▸ hsub
      have hx_in_uv_or_not : x ∈ ({u, v} : Set S) ∨ y ∈ ({u, v} : Set S) := by
        by_contra hnot
        push Not at hnot
        have h4 : ({u, v, x, y} : Set S) ⊆ tilde c' := by
          rintro z (rfl | rfl | rfl | rfl)
          · exact hsub₁ (htilde₁ ▸ Or.inl rfl)
          · exact hsub₁ (htilde₁ ▸ Or.inr rfl)
          · exact hxy_sub_uv_or (Or.inl rfl)
          · exact hxy_sub_uv_or (Or.inr rfl)
        have hcard4 : ({u, v, x, y} : Set S).ncard = 4 := by
          rw [ncard_insert_of_notMem, ncard_insert_of_notMem, ncard_pair hxy]
          · simp only [mem_insert_iff, mem_singleton_iff, not_or]
            exact ⟨fun h => hnot.1 (Or.inr h.symm), fun h => hnot.2 (Or.inr h.symm)⟩
          · simp only [mem_insert_iff, mem_singleton_iff, not_or]
            exact ⟨huv, fun h => hnot.1 (Or.inl h.symm), fun h => hnot.2 (Or.inl h.symm)⟩
        have hle3 : ({u, v, x, y} : Set S).ncard ≤ 3 :=
          hcard3 ▸ ncard_le_ncard h4 (Γ.finite_tilde_cell hc')
        omega
      have hC_eq_C' : C = C' := by
        rcases hx_in_uv_or_not with hx_uv | hy_uv
        · have hx_C' : x ∈ C' := (htilde_C' (htilde_c ▸ Or.inl rfl)).2
          have hx_C : x ∈ C := (hV₀C_eq_uv.symm ▸ hx_uv).2
          by_contra hne_C
          exact Set.disjoint_left.mp (cuffs_disjoint hC hC' hne_C) hx_C hx_C'
        · have hy_C' : y ∈ C' := (htilde_C' (htilde_c ▸ Or.inr rfl)).2
          have hy_C : y ∈ C := (hV₀C_eq_uv.symm ▸ hy_uv).2
          by_contra hne_C
          exact Set.disjoint_left.mp (cuffs_disjoint hC hC' hne_C) hy_C hy_C'
      subst hC_eq_C'
      obtain ⟨ic, hic_eq⟩ := exists_index_of_mem_drawingSpaces_subset_cuff hS hge2 hs_mem hC hsC' f
      have hic_cases : ic = i₁ ∨ ic = i₂ := by
        have hlt2 : ic.1 < 2 := hk_eq_2 ▸ ic.2
        have hi₁_lt2 : i₁.1 < 2 := hk_eq_2 ▸ i₁.2
        have hi₂_lt2 : i₂.1 < 2 := hk_eq_2 ▸ i₂.2
        have hi₁₂_val : i₁.1 ≠ i₂.1 := fun h => hi₁₂_ne (Fin.ext h)
        rcases (by omega : ic.1 = i₁.1 ∨ ic.1 = i₂.1) with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases hic_cases with rfl | rfl
      · left
        have hs_eq : c ∩ bd S = c₁ ∩ bd S := hic_eq.trans hi₁_eq.symm
        rcases hbd with ⟨z, hzc, hzbd⟩
        have hzc₁_bd : z ∈ c₁ ∩ bd S := hs_eq ▸ ⟨hzc, hzbd⟩
        exact Γ.cell_eq_of_mem hc hc₁ hzc hzc₁_bd.1
      · right
        have hs_eq : c ∩ bd S = c₂ ∩ bd S := hic_eq.trans hi₂_eq.symm
        rcases hbd with ⟨z, hzc, hzbd⟩
        have hzc₂_bd : z ∈ c₂ ∩ bd S := hs_eq ▸ ⟨hzc, hzbd⟩
        exact Γ.cell_eq_of_mem hc hc₂ hzc hzc₂_bd.1
    calc B.ncard
        ≤ ({c₁, c₂} : Set (Set S)).ncard := ncard_le_ncard hB_sub_pair ((finite_singleton _).insert _)
      _ ≤ ({c₂} : Set (Set S)).ncard + 1 := ncard_insert_le c₁ {c₂}
      _ ≤ 3 := by rw [ncard_singleton]; omega
  · -- No two distinct cells in B have the same tilde!
    push Not at h_dup
    let pairs : Set (Set S) := {{w₁, w₂}, {w₂, w₃}, {w₁, w₃}}
    have hpairs_fin : pairs.Finite :=
      ((finite_singleton _).insert _).insert _
    have hpairs_card : pairs.ncard ≤ 3 := by
      calc pairs.ncard
          ≤ ({{w₂, w₃}, {w₁, w₃}} : Set (Set S)).ncard + 1 := ncard_insert_le _ _
        _ ≤ ({({w₁, w₃} : Set S)} : Set (Set S)).ncard + 1 + 1 :=
          Nat.add_le_add_right (ncard_insert_le _ _) 1
        _ = 3 := by rw [ncard_singleton]
    have htilde_maps : MapsTo tilde B pairs := by
      rintro c ⟨hc, hbd, hsub⟩
      obtain ⟨u, v, huv, htilde_c, _, _, _, _⟩ := Γ.border_cell_exists_ends hc hbd
      have hu_in : u ∈ ({w₁, w₂, w₃} : Set S) := htilde_c' ▸ hsub (htilde_c ▸ Or.inl rfl)
      have hv_in : v ∈ ({w₁, w₂, w₃} : Set S) := htilde_c' ▸ hsub (htilde_c ▸ Or.inr rfl)
      rw [htilde_c]
      simp only [pairs, mem_insert_iff, mem_singleton_iff]
      rcases hu_in with rfl | rfl | rfl <;> rcases hv_in with rfl | rfl | rfl
      · exact (huv rfl).elim
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl (pair_comm _ _)
      · exact (huv rfl).elim
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (pair_comm _ _))
      · exact Or.inr (Or.inl (pair_comm _ _))
      · exact (huv rfl).elim
    have hinj : InjOn tilde B := fun c₁ hc₁ c₂ hc₂ h_eq =>
      by_contra fun hne => h_dup c₁ hc₁ c₂ hc₂ hne h_eq
    calc B.ncard
        = (tilde '' B).ncard := (hinj.ncard_image).symm
      _ ≤ pairs.ncard := ncard_le_ncard (htilde_maps.image_subset) hpairs_fin
      _ ≤ 3 := hpairs_card

/-- Removing a single space `s₀ ∈ drawingSpaces Γ` on a cuff `C ∈ cuffs S` leaves a support
`C \ s₀` (`IsSupportOfDrawing Γ (C \ s₀)`) covering `Γ.V ∩ C` and containing all spaces `s ⊆ C`
except `s₀`. -/
theorem isSupportOfDrawing_cuff_diff_space (hS : IsSurface S) {Γ : Surface.Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard)
    {C s₀ : Set S} (hC : C ∈ cuffs S) (hs₀ : s₀ ∈ drawingSpaces Γ) (hs₀C : s₀ ⊆ C) :
    IsSupportOfDrawing Γ (C \ s₀) ∧
    C \ s₀ ⊆ C ∧
    Γ.V ∩ C ⊆ C \ s₀ ∧
    ∀ s ∈ drawingSpaces Γ, s ⊆ C → (s ⊆ C \ s₀ ↔ s ≠ s₀) := by
  have : T2Space S := hS.2.1
  let f := cuffHomeo hS hC
  have hk := hge2 C hC
  have hC_sub_bd : C ⊆ bd S := fun z hz => by rw [← sUnion_cuffs (S := S)]; exact ⟨C, hC, hz⟩
  obtain ⟨i₀, rfl⟩ := exists_index_of_mem_drawingSpaces_subset_cuff hS hge2 hs₀ hC hs₀C f
  set a₀ := vAngle Γ.V Γ.finite_V f i₀
  set b₀ := vUpperAngle Γ.V Γ.finite_V f hk i₀
  have ha₀_lt_b₀ : a₀ < b₀ := vAngle_lt_vUpperAngle Γ.V Γ.finite_V f hk i₀
  have hb₀_lt : b₀ < a₀ + 2 * Real.pi := vUpperAngle_lt_add_two_pi Γ.V Γ.finite_V f hk i₀
  have hends_i₀ := spaceHasEnds_vSpaceArc hS hge2 hC f i₀
  have hdiff_eq : C \ vSpaceArc Γ.V Γ.finite_V f hk i₀ = cuffPoint f '' Icc b₀ (a₀ + 2 * Real.pi) := by
    ext z
    constructor
    · rintro ⟨hzC, hz_not⟩
      obtain ⟨t, ht, rfl⟩ := exists_cuffPoint_mem_Ico f a₀ hzC
      rcases eq_or_lt_of_le ht.1 with rfl | ht_gt
      · exact ⟨a₀ + 2 * Real.pi, ⟨hb₀_lt.le, le_rfl⟩, by rw [GM19.cuffPoint_add_two_pi]⟩
      · have hge_b₀ : b₀ ≤ t := by
          by_contra hlt_b₀
          push Not at hlt_b₀
          exact hz_not ⟨t, ⟨ht_gt, hlt_b₀⟩, rfl⟩
        exact ⟨t, ⟨hge_b₀, ht.2.le⟩, rfl⟩
    · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
      refine ⟨GM19.cuffPoint_mem f t, ?_⟩
      rintro ⟨s, ⟨hs1, hs2⟩, h_eq⟩
      rcases eq_or_lt_of_le ht2 with rfl | ht2_lt
      · rw [GM19.cuffPoint_add_two_pi] at h_eq
        have := cuffPoint_injOn_Ico f a₀ ⟨hs1.le, hs2.trans hb₀_lt⟩ ⟨le_rfl, by linarith [Real.pi_pos]⟩ h_eq
        linarith
      · have := cuffPoint_injOn_Ico f a₀ ⟨hs1.le, hs2.trans hb₀_lt⟩ ⟨ha₀_lt_b₀.le.trans ht1, ht2_lt⟩ h_eq
        linarith
  have hline : IsLineWithEnds (C \ vSpaceArc Γ.V Γ.finite_V f hk i₀)
      (vNode Γ.V Γ.finite_V f (nextFin hk i₀)) (vNode Γ.V Γ.finite_V f i₀) := by
    rw [hdiff_eq, ← cuffPoint_vUpperAngle Γ.V Γ.finite_V f hk i₀]
    have ha₀_2pi : cuffPoint f (a₀ + 2 * Real.pi) = vNode Γ.V Γ.finite_V f i₀ := by
      rw [GM19.cuffPoint_add_two_pi]; rfl
    rw [← ha₀_2pi]
    exact isLineWithEnds_cuffPoint_Icc f hb₀_lt (by linarith [ha₀_lt_b₀])
  have hsupp : IsSupportOfDrawing Γ (C \ vSpaceArc Γ.V Γ.finite_V f hk i₀) :=
    ⟨vNode Γ.V Γ.finite_V f (nextFin hk i₀), vNode Γ.V Γ.finite_V f i₀,
      Or.inr ⟨sdiff_subset.trans hC_sub_bd, hends_i₀.2.2.2.1.symm, hends_i₀.2.2.1, hends_i₀.2.1, hline⟩⟩
  refine ⟨hsupp, sdiff_subset, ?_, ?_⟩
  · rintro z ⟨hzV, hzC⟩
    exact ⟨hzC, fun hzs => (subset_bd_diff_of_mem_drawingSpaces hs₀ hzs).2 hzV⟩
  · intro s hs hsC
    constructor
    · intro hsub h_eq
      subst h_eq
      obtain ⟨z, hzs⟩ := nonempty_of_mem_drawingSpaces hs
      exact (hsub hzs).2 hzs
    · intro hne
      obtain ⟨j, rfl⟩ := exists_index_of_mem_drawingSpaces_subset_cuff hS hge2 hs hC hsC f
      have hij : j ≠ i₀ := fun h => hne (h ▸ rfl)
      exact subset_sdiff.mpr ⟨hsC, disjoint_vSpaceArc Γ.V Γ.finite_V f hk hij⟩

/-- Removing a space `s_new ∈ drawingSpaces Γ` from a support `F` (`s_new ⊆ F`) splits `F \ s_new`
into two disjoint supports `F₁, F₂`. -/
theorem split_support_at_space (hS : IsSurface S) {Γ : Surface.Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard)
    {F s_new : Set S} (hF : IsSupportOfDrawing Γ F)
    (hs_new : s_new ∈ drawingSpaces Γ) (hs_sub : s_new ⊆ F) :
    ∃ F₁ F₂ : Set S,
      IsSupportOfDrawing Γ F₁ ∧
      IsSupportOfDrawing Γ F₂ ∧
      Disjoint F₁ F₂ ∧
      F₁ ∪ F₂ = F \ s_new ∧
      Γ.V ∩ F ⊆ F₁ ∪ F₂ ∧
      ∀ s ∈ drawingSpaces Γ, ((s ⊆ F₁ ∨ s ⊆ F₂) ↔ (s ⊆ F ∧ s ≠ s_new)) := by
  have : T2Space S := hS.2.1
  rcases hF with ⟨endA, endB, hF_ends⟩
  obtain ⟨C, hC, hFC⟩ := exists_cuff_of_supportHasEnds hF_ends
  have hC_sub_bd : C ⊆ bd S := fun z hz => by rw [← sUnion_cuffs (S := S)]; exact ⟨C, hC, hz⟩
  let f := cuffHomeo hS hC
  have hk := hge2 C hC
  have hends_mem := ends_mem_of_supportHasEnds hF_ends
  obtain ⟨t₀, ht₀_Ico, t₁, ⟨ht₀_le_t₁, ht₁_lt⟩, h_ab_eq, hF_eq, _⟩ :=
    support_eq_cuffPoint_Icc hS hC f hF_ends hFC
  have ht₀_mem : cuffPoint f t₀ ∈ Γ.V ∩ C := by
    refine ⟨?_, GM19.cuffPoint_mem f t₀⟩
    rcases h_ab_eq with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
    · exact hends_mem.2.2.1.1
    · exact hends_mem.2.2.2.1.1
  have ht₁_mem : cuffPoint f t₁ ∈ Γ.V ∩ C := by
    refine ⟨?_, GM19.cuffPoint_mem f t₁⟩
    rcases h_ab_eq with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2]
    · exact hends_mem.2.2.2.1.1
    · exact hends_mem.2.2.1.1
  have hs_C : s_new ⊆ C := hs_sub.trans hFC
  obtain ⟨i₀, rfl⟩ := exists_index_of_mem_drawingSpaces_subset_cuff hS hge2 hs_new hC hs_C f
  obtain ⟨a', b', ha', hab', hb', ha'_eq, hb'_eq, hs_eq, _⟩ :=
    vSpaceArc_eq_Ioo_from_vertex_angle hS hC f hk ht₀_mem i₀
  have hb'_le_t₁ : b' ≤ t₁ := by
    apply right_end_le_of_Ioo_subset_Icc f ht₀_le_t₁ ht₁_lt ha' hab' hb'
    rw [← hs_eq, ← hF_eq]; exact hs_sub
  let F₁ : Set S := cuffPoint f '' Icc t₀ a'
  let F₂ : Set S := cuffPoint f '' Icc b' t₁
  have hF₁_supp : IsSupportOfDrawing Γ F₁ := by
    rcases eq_or_lt_of_le ha' with rfl | hlt_a'
    · refine ⟨cuffPoint f t₀, cuffPoint f t₀,
        Or.inl ⟨cuffPoint f t₀, ⟨ht₀_mem.1, hC_sub_bd ht₀_mem.2⟩, ?_, rfl, rfl⟩⟩
      dsimp [F₁]; rw [Icc_self, image_singleton]
    · have hline₁ : IsLineWithEnds F₁ (cuffPoint f t₀) (cuffPoint f a') :=
        isLineWithEnds_cuffPoint_Icc f hlt_a' (by linarith [hab', hb'_le_t₁, ht₁_lt])
      have ha'_mem := vNode_mem Γ.V Γ.finite_V f i₀
      rw [← ha'_eq] at ha'_mem
      exact ⟨cuffPoint f t₀, cuffPoint f a', Or.inr ⟨(by rintro _ ⟨t, _, rfl⟩; exact hC_sub_bd (GM19.cuffPoint_mem f t)),
        hline₁.ne', ⟨ht₀_mem.1, hC_sub_bd ht₀_mem.2⟩, ⟨ha'_mem.1, hC_sub_bd ha'_mem.2⟩, hline₁⟩⟩
  have hF₂_supp : IsSupportOfDrawing Γ F₂ := by
    rcases eq_or_lt_of_le hb'_le_t₁ with rfl | hlt_b'
    · refine ⟨cuffPoint f b', cuffPoint f b',
        Or.inl ⟨cuffPoint f b', ⟨ht₁_mem.1, hC_sub_bd ht₁_mem.2⟩, ?_, rfl, rfl⟩⟩
      dsimp [F₂]; rw [Icc_self, image_singleton]
    · have hline₂ : IsLineWithEnds F₂ (cuffPoint f b') (cuffPoint f t₁) :=
        isLineWithEnds_cuffPoint_Icc f hlt_b' (by linarith [ha', hab', ht₁_lt])
      have hb'_mem := vNode_mem Γ.V Γ.finite_V f (nextFin hk i₀)
      rw [← hb'_eq] at hb'_mem
      exact ⟨cuffPoint f b', cuffPoint f t₁, Or.inr ⟨(by rintro _ ⟨t, _, rfl⟩; exact hC_sub_bd (GM19.cuffPoint_mem f t)),
        hline₂.ne', ⟨hb'_mem.1, hC_sub_bd hb'_mem.2⟩, ⟨ht₁_mem.1, hC_sub_bd ht₁_mem.2⟩, hline₂⟩⟩
  have hdisj₁₂ : Disjoint F₁ F₂ := by
    rw [disjoint_iff_inter_eq_empty]
    ext z
    simp only [F₁, F₂, mem_inter_iff, mem_image, mem_Icc, mem_empty_iff_false, iff_false, not_and]
    rintro ⟨s₁, ⟨hs₁_1, hs₁_2⟩, rfl⟩ ⟨s₂, ⟨hs₂_1, hs₂_2⟩, h_eq⟩
    have h_s₁_s₂ := cuffPoint_injOn_Ico f t₀ ⟨hs₁_1, by linarith⟩ ⟨by linarith, by linarith⟩ h_eq.symm
    linarith
  have hunion₁₂ : F₁ ∪ F₂ = F \ vSpaceArc Γ.V Γ.finite_V f hk i₀ := by
    rw [hF_eq, hs_eq]
    ext z
    constructor
    · rintro (⟨t, ⟨ht1, ht2⟩, rfl⟩ | ⟨t, ⟨ht1, ht2⟩, rfl⟩)
      · refine ⟨⟨t, ⟨ht1, by linarith⟩, rfl⟩, ?_⟩
        rintro ⟨s, ⟨hs1, hs2⟩, h_eq⟩
        have := cuffPoint_injOn_Ico f t₀ ⟨by linarith, by linarith⟩ ⟨ht1, by linarith⟩ h_eq
        linarith
      · refine ⟨⟨t, ⟨by linarith, ht2⟩, rfl⟩, ?_⟩
        rintro ⟨s, ⟨hs1, hs2⟩, h_eq⟩
        have := cuffPoint_injOn_Ico f t₀ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h_eq
        linarith
    · rintro ⟨⟨t, ⟨ht1, ht2⟩, rfl⟩, hz_not⟩
      by_cases ht_le_a' : t ≤ a'
      · exact Or.inl ⟨t, ⟨ht1, ht_le_a'⟩, rfl⟩
      · right
        push Not at ht_le_a'
        have hge_b' : b' ≤ t := by
          by_contra hlt_b'
          push Not at hlt_b'
          exact hz_not ⟨t, ⟨ht_le_a', hlt_b'⟩, rfl⟩
        exact ⟨t, ⟨hge_b', ht2⟩, rfl⟩
  refine ⟨F₁, F₂, hF₁_supp, hF₂_supp, hdisj₁₂, hunion₁₂, ?_, ?_⟩
  · rintro z ⟨hzV, hzF⟩
    rw [hunion₁₂]
    exact ⟨hzF, fun hzs => (subset_bd_diff_of_mem_drawingSpaces hs_new hzs).2 hzV⟩
  · intro s hs
    constructor
    · rintro (hs₁ | hs₂)
      · have hs_diff : s ⊆ F \ vSpaceArc Γ.V Γ.finite_V f hk i₀ :=
          hs₁.trans (hunion₁₂ ▸ subset_union_left)
        refine ⟨hs_diff.trans sdiff_subset, fun h_eq => ?_⟩
        subst h_eq
        obtain ⟨z, hzs⟩ := nonempty_of_mem_drawingSpaces hs
        exact (hs_diff hzs).2 hzs
      · have hs_diff : s ⊆ F \ vSpaceArc Γ.V Γ.finite_V f hk i₀ :=
          hs₂.trans (hunion₁₂ ▸ subset_union_right)
        refine ⟨hs_diff.trans sdiff_subset, fun h_eq => ?_⟩
        subst h_eq
        obtain ⟨z, hzs⟩ := nonempty_of_mem_drawingSpaces hs
        exact (hs_diff hzs).2 hzs
    · rintro ⟨hsF, hne⟩
      have hs_C' : s ⊆ C := hsF.trans hFC
      obtain ⟨j, rfl⟩ := exists_index_of_mem_drawingSpaces_subset_cuff hS hge2 hs hC hs_C' f
      have hij : j ≠ i₀ := fun h => hne (h ▸ rfl)
      have hs_union : vSpaceArc Γ.V Γ.finite_V f hk j ⊆ F₁ ∪ F₂ := by
        rw [hunion₁₂]
        exact subset_sdiff.mpr ⟨hsF, disjoint_vSpaceArc Γ.V Γ.finite_V f hk hij⟩
      rcases space_subset_or_disjoint_of_isSupportOfDrawing hS hs hF₁_supp with ⟨h1, _⟩ | hdisj₁
      · exact Or.inl h1
      · exact Or.inr fun z hzs => (hs_union hzs).resolve_left (Set.disjoint_left.mp hdisj₁ hzs)

/-- Given any set of spaces `M ⊆ drawingSpaces Γ` containing at least one space on each cuff
`C ∈ cuffs S`, the complement `bd S \ ⋃₀ M` decomposes into `M.ncard` pairwise disjoint supports
`F_star : Fin M.ncard → Set S` covering `Γ.V ∩ bd S` and containing all spaces `s ∉ M`. -/
theorem exists_supports_of_removed_spaces (hS : IsSurface S) {Γ : Surface.Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard)
    {M : Set (Set S)} (hM_sub : M ⊆ drawingSpaces Γ)
    (hM_cuff : ∀ C ∈ cuffs S, ∃ s ∈ M, s ⊆ C) :
    ∃ (F_star : Fin M.ncard → Set S),
      (∀ j : Fin M.ncard, IsSupportOfDrawing Γ (F_star j)) ∧
      Pairwise (fun i j : Fin M.ncard => Disjoint (F_star i) (F_star j)) ∧
      Γ.V ∩ bd S ⊆ ⋃ j : Fin M.ncard, F_star j ∧
      ∀ s ∈ drawingSpaces Γ, (∃ j : Fin M.ncard, s ⊆ F_star j) ↔ s ∉ M := by
  have : T2Space S := hS.2.1
  have hspaces_fin : (drawingSpaces Γ).Finite := drawingSpaces_finite hS hge2
  have hM_fin : M.Finite := hspaces_fin.subset hM_sub
  -- Pick one representative space rep C ∈ M for each C ∈ cuffs S
  let rep : Set S → Set S := fun C =>
    if hC : C ∈ cuffs S then Classical.choose (hM_cuff C hC) else ∅
  have hrep_spec : ∀ C ∈ cuffs S, rep C ∈ M ∧ rep C ⊆ C := fun C hC => by
    simp only [rep, hC, ↓reduceDIte]; exact Classical.choose_spec (hM_cuff C hC)
  let M₀ : Set (Set S) := rep '' cuffs S
  have hM₀_sub_M : M₀ ⊆ M := by
    rintro _ ⟨C, hC, rfl⟩; exact (hrep_spec C hC).1
  have hrep_inj : InjOn rep (cuffs S) := by
    intro C₁ hC₁ C₂ hC₂ h_eq
    obtain ⟨z, hz⟩ := nonempty_of_mem_drawingSpaces (hM_sub (hrep_spec C₁ hC₁).1)
    have hz₁ : z ∈ C₁ := (hrep_spec C₁ hC₁).2 hz
    have hz₂ : z ∈ C₂ := (hrep_spec C₂ hC₂).2 (h_eq ▸ hz)
    by_contra hne
    exact Set.disjoint_left.mp (cuffs_disjoint hC₁ hC₂ hne) hz₁ hz₂
  -- Base case for M₀ = rep '' cuffs S
  have h_base : ∃ (F_star : Fin M₀.ncard → Set S),
      (∀ j : Fin M₀.ncard, IsSupportOfDrawing Γ (F_star j)) ∧
      Pairwise (fun i j : Fin M₀.ncard => Disjoint (F_star i) (F_star j)) ∧
      Γ.V ∩ bd S ⊆ ⋃ j : Fin M₀.ncard, F_star j ∧
      ∀ s ∈ drawingSpaces Γ, (∃ j : Fin M₀.ncard, s ⊆ F_star j) ↔ s ∉ M₀ := by
    have hcuffs_fin : (cuffs S).Finite := (cuff_statement.{0} S hS).2.1
    have hcard_eq : M₀.ncard = (cuffs S).ncard := hrep_inj.ncard_image
    have : Finite ↑(cuffs S) := hcuffs_fin.to_subtype
    let e_cuff : ↑(cuffs S) ≃ Fin M₀.ncard :=
      (Finite.equivFin ↑(cuffs S)).trans (finCongr hcard_eq.symm)
    let C_of : Fin M₀.ncard → Set S := fun j => (e_cuff.symm j).1
    have hC_of_mem : ∀ j, C_of j ∈ cuffs S := fun j => (e_cuff.symm j).2
    have hC_of_inj : Function.Injective C_of :=
      fun i j h => e_cuff.symm.injective (Subtype.ext h)
    have hC_of_surj : ∀ C ∈ cuffs S, ∃ j, C_of j = C :=
      fun C hC => ⟨e_cuff ⟨C, hC⟩, congrArg Subtype.val (e_cuff.symm_apply_apply ⟨C, hC⟩)⟩
    let F_star : Fin M₀.ncard → Set S := fun j => C_of j \ rep (C_of j)
    have hF_props : ∀ j : Fin M₀.ncard,
        IsSupportOfDrawing Γ (F_star j) ∧
        F_star j ⊆ C_of j ∧
        Γ.V ∩ C_of j ⊆ F_star j ∧
        ∀ s ∈ drawingSpaces Γ, s ⊆ C_of j → (s ⊆ F_star j ↔ s ≠ rep (C_of j)) :=
      fun j => isSupportOfDrawing_cuff_diff_space hS hge2 (hC_of_mem j)
        (hM_sub (hrep_spec (C_of j) (hC_of_mem j)).1) (hrep_spec (C_of j) (hC_of_mem j)).2
    refine ⟨F_star, fun j => (hF_props j).1, ?_, ?_, ?_⟩
    · intro i j hij
      exact (cuffs_disjoint (hC_of_mem i) (hC_of_mem j) (hC_of_inj.ne hij)).mono
        (hF_props i).2.1 (hF_props j).2.1
    · rintro z ⟨hzV, hzbd⟩
      rw [← sUnion_cuffs (S := S)] at hzbd
      rcases hzbd with ⟨C, hC, hzC⟩
      obtain ⟨j, rfl⟩ := hC_of_surj C hC
      exact mem_iUnion.mpr ⟨j, (hF_props j).2.2.1 ⟨hzV, hzC⟩⟩
    · intro s hs
      obtain ⟨C, hC, hsC, _⟩ := exists_cuff_of_mem_drawingSpaces hS hge2 hs
      obtain ⟨j₀, rfl⟩ := hC_of_surj C hC
      constructor
      · rintro ⟨j, hsF⟩ hs_M₀
        have hj_eq : j = j₀ := by
          by_contra hne
          obtain ⟨z, hzs⟩ := nonempty_of_mem_drawingSpaces hs
          exact Set.disjoint_left.mp
            (cuffs_disjoint (hC_of_mem j) (hC_of_mem j₀) (hC_of_inj.ne hne))
            ((hF_props j).2.1 (hsF hzs)) (hsC hzs)
        subst hj_eq
        rcases hs_M₀ with ⟨C', hC', hrep_eq⟩
        have hC'_eq : C' = C_of j := by
          obtain ⟨z, hzs⟩ := nonempty_of_mem_drawingSpaces hs
          have hz1 : z ∈ C' := (hrep_spec C' hC').2 (hrep_eq.symm ▸ hzs)
          have hz2 : z ∈ C_of j := hsC hzs
          by_contra hne
          exact Set.disjoint_left.mp (cuffs_disjoint hC' (hC_of_mem j) hne) hz1 hz2
        subst hC'_eq
        exact ((hF_props j).2.2.2 s hs hsC).mp hsF hrep_eq.symm
      · intro hs_not_M₀
        refine ⟨j₀, ((hF_props j₀).2.2.2 s hs hsC).mpr fun h_eq => hs_not_M₀ ⟨C_of j₀, hC_of_mem j₀, h_eq.symm⟩⟩
  -- Inductive step adding the finite set D = M \ M₀ one space at a time
  have hD_fin : (M \ M₀).Finite := hM_fin.sdiff
  have h_step : ∀ (D : Set (Set S)), D.Finite → D ⊆ drawingSpaces Γ → Disjoint D M₀ →
      ∃ (r' : ℕ) (F_star : Fin r' → Set S),
        r' = (M₀ ∪ D).ncard ∧
        (∀ j : Fin r', IsSupportOfDrawing Γ (F_star j)) ∧
        Pairwise (fun i j : Fin r' => Disjoint (F_star i) (F_star j)) ∧
        Γ.V ∩ bd S ⊆ ⋃ j : Fin r', F_star j ∧
        ∀ s ∈ drawingSpaces Γ, (∃ j : Fin r', s ⊆ F_star j) ↔ s ∉ (M₀ ∪ D) := by
    intro D hD_fin
    refine @Set.Finite.induction_on (Set S)
      (fun D _ => D ⊆ drawingSpaces Γ → Disjoint D M₀ →
        ∃ (r' : ℕ) (F_star : Fin r' → Set S),
          r' = (M₀ ∪ D).ncard ∧
          (∀ j : Fin r', IsSupportOfDrawing Γ (F_star j)) ∧
          Pairwise (fun i j : Fin r' => Disjoint (F_star i) (F_star j)) ∧
          Γ.V ∩ bd S ⊆ ⋃ j : Fin r', F_star j ∧
          ∀ s ∈ drawingSpaces Γ, (∃ j : Fin r', s ⊆ F_star j) ↔ s ∉ (M₀ ∪ D))
      D hD_fin ?_ ?_
    · intro _ _
      obtain ⟨F_star, h1, h2, h3, h4⟩ := h_base
      refine ⟨M₀.ncard, F_star, by rw [union_empty], h1, h2, h3, ?_⟩
      simpa only [union_empty] using h4
    · intro s_new D' hs_not_D' hD'_fin ih hD'_sub hD'_disj
      have hs_new_space : s_new ∈ drawingSpaces Γ := hD'_sub (mem_insert s_new D')
      have hs_not_M₀ : s_new ∉ M₀ :=
        Set.disjoint_left.mp hD'_disj (mem_insert s_new D')
      have hs_not_union : s_new ∉ M₀ ∪ D' := by
        rintro (h1 | h2)
        · exact hs_not_M₀ h1
        · exact hs_not_D' h2
      obtain ⟨r', F_old, hr'_eq, hF_old_supp, hF_old_disj, hF_old_cov, hF_old_iff⟩ :=
        ih (subset_insert s_new D' |>.trans hD'_sub)
          (hD'_disj.mono_left (subset_insert s_new D'))
      obtain ⟨j₀, hs_sub_j₀⟩ := (hF_old_iff s_new hs_new_space).mpr hs_not_union
      obtain ⟨F₁, F₂, hF₁_supp, hF₂_supp, hdisj₁₂, hunion₁₂, hV_sub₁₂, hspace_iff₁₂⟩ :=
        split_support_at_space hS hge2 (hF_old_supp j₀) hs_new_space hs_sub_j₀
      have h_union_eq : M₀ ∪ insert s_new D' = insert s_new (M₀ ∪ D') := by
        ext x; simp only [mem_union, mem_insert_iff]; tauto
      have hM₀_fin : M₀.Finite := hM_fin.subset hM₀_sub_M
      have hcard_succ : r' + 1 = (M₀ ∪ insert s_new D').ncard := by
        rw [h_union_eq, ncard_insert_of_notMem hs_not_union (hM₀_fin.union hD'_fin), hr'_eq]
      let F_new : Fin (r' + 1) → Set S := fun k =>
        if hk : k.1 < r' then
          if (⟨k.1, hk⟩ : Fin r') = j₀ then F₁ else F_old ⟨k.1, hk⟩
        else F₂
      have hF₁_sub : F₁ ⊆ F_old j₀ :=
        subset_union_left.trans (hunion₁₂.le.trans sdiff_subset)
      have hF₂_sub : F₂ ⊆ F_old j₀ :=
        subset_union_right.trans (hunion₁₂.le.trans sdiff_subset)
      refine ⟨r' + 1, F_new, hcard_succ, ?_, ?_, ?_, ?_⟩
      · intro k
        dsimp [F_new]
        split_ifs with hk h_eq
        · exact hF₁_supp
        · exact hF_old_supp _
        · exact hF₂_supp
      · intro k₁ k₂ hk_ne
        dsimp [F_new]
        by_cases hk₁ : k₁.1 < r' <;> by_cases hk₂ : k₂.1 < r'
        · simp only [hk₁, hk₂, ↓reduceDIte]
          split_ifs with h₁ h₂ h₂
          · exfalso
            have hval : k₁.1 = k₂.1 := Fin.mk.inj_iff.mp (h₁.trans h₂.symm)
            exact hk_ne (Fin.ext hval)
          · exact (hF_old_disj (fun h => h₂ (h.symm.trans h₁))).mono_left
              (h₁.symm ▸ hF₁_sub)
          · exact (hF_old_disj (fun h => h₁ (h.trans h₂))).mono_right
              (h₂.symm ▸ hF₁_sub)
          · exact hF_old_disj (fun h => hk_ne (Fin.ext (Fin.mk.inj_iff.mp h)))
        · simp only [hk₁, hk₂, ↓reduceDIte]
          split_ifs with h₁
          · exact hdisj₁₂
          · exact (hF_old_disj h₁).mono_right hF₂_sub
        · simp only [hk₁, hk₂, ↓reduceDIte]
          split_ifs with h₂
          · exact hdisj₁₂.symm
          · exact (hF_old_disj (Ne.symm h₂)).mono_left hF₂_sub
        · exfalso
          have hval₁ : k₁.1 = r' := by omega
          have hval₂ : k₂.1 = r' := by omega
          exact hk_ne (Fin.ext (hval₁.trans hval₂.symm))
      · rintro z hz
        have hz_old := hF_old_cov hz
        rw [mem_iUnion] at hz_old ⊢
        rcases hz_old with ⟨j, hzj⟩
        by_cases hj : j = j₀
        · subst hj
          rcases hV_sub₁₂ ⟨hz.1, hzj⟩ with hz₁ | hz₂
          · refine ⟨⟨j.1, Nat.lt_succ_of_lt j.2⟩, ?_⟩
            simp only [F_new, j.2, ↓reduceDIte, ↓reduceIte]
            exact hz₁
          · refine ⟨⟨r', Nat.lt_succ_self r'⟩, ?_⟩
            simp only [F_new, lt_irrefl, ↓reduceDIte]
            exact hz₂
        · refine ⟨⟨j.1, Nat.lt_succ_of_lt j.2⟩, ?_⟩
          simp only [F_new, j.2, ↓reduceDIte, hj, ↓reduceIte]
          exact hzj
      · intro s hs
        rw [h_union_eq, mem_insert_iff, not_or]
        constructor
        · rintro ⟨k, hsk⟩
          dsimp [F_new] at hsk
          split_ifs at hsk with hk h_eq
          · obtain ⟨hs_j₀, hs_ne⟩ := (hspace_iff₁₂ s hs).mp (Or.inl hsk)
            exact ⟨hs_ne, (hF_old_iff s hs).mp ⟨j₀, hs_j₀⟩⟩
          · have hs_not_old : s ∉ M₀ ∪ D' := (hF_old_iff s hs).mp ⟨⟨k.1, hk⟩, hsk⟩
            refine ⟨?_, hs_not_old⟩
            rintro rfl
            obtain ⟨z, hzs⟩ := nonempty_of_mem_drawingSpaces hs
            exact Set.disjoint_left.mp (hF_old_disj h_eq) (hsk hzs) (hs_sub_j₀ hzs)
          · obtain ⟨hs_j₀, hs_ne⟩ := (hspace_iff₁₂ s hs).mp (Or.inr hsk)
            exact ⟨hs_ne, (hF_old_iff s hs).mp ⟨j₀, hs_j₀⟩⟩
        · rintro ⟨hs_ne, hs_not_old⟩
          obtain ⟨j, hsj⟩ := (hF_old_iff s hs).mpr hs_not_old
          by_cases hj : j = j₀
          · subst hj
            rcases (hspace_iff₁₂ s hs).mpr ⟨hsj, hs_ne⟩ with hs₁ | hs₂
            · refine ⟨⟨j.1, Nat.lt_succ_of_lt j.2⟩, ?_⟩
              simp only [F_new, j.2, ↓reduceDIte, ↓reduceIte]
              exact hs₁
            · refine ⟨⟨r', Nat.lt_succ_self r'⟩, ?_⟩
              simp only [F_new, lt_irrefl, ↓reduceDIte]
              exact hs₂
          · refine ⟨⟨j.1, Nat.lt_succ_of_lt j.2⟩, ?_⟩
            simp only [F_new, j.2, ↓reduceDIte, hj, ↓reduceIte]
            exact hsj
  have hM_eq : M₀ ∪ (M \ M₀) = M := union_sdiff_cancel hM₀_sub_M
  obtain ⟨r', F_star, hr'_eq, h1, h2, h3, h4⟩ :=
    h_step (M \ M₀) hD_fin (sdiff_subset.trans hM_sub) disjoint_sdiff_self_left
  rw [hM_eq] at hr'_eq h4
  subst hr'_eq
  exact ⟨F_star, h1, h2, h3, h4⟩

/-! ## 3. Border Cell Separation `B(c)` and Subgraph Union/Intersection Lemmas -/

theorem tilde_subset_N_bd_of_border_cell {Γ : GM17.Painting S} {c : Set S}
    (hc : c ∈ Γ.C) (hbd : (c ∩ bd S).Nonempty) :
    tilde c ⊆ Γ.N ∩ bd S := by
  obtain ⟨u, v, _, htilde, _, _, hu, hv⟩ := Γ.border_cell_exists_ends hc hbd
  rw [htilde]
  rintro z (rfl | rfl) <;> assumption

theorem vert_le_cell_of_mem_tilde {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {c : Set S} (hc : c ∈ Γ.C) (hbd : (c ∩ bd S).Nonempty)
    {u : S} (hu : u ∈ tilde c) :
    α_vert u ≤ α_cell c := by
  obtain ⟨u₁, u₂, hne, htilde, _, _, _, _⟩ := Γ.border_cell_exists_ends hc hbd
  have h6 := hport.r6_border c hc hbd u₁ u₂ hne htilde
  rw [htilde] at hu
  rcases hu with rfl | rfl
  · exact h6.1
  · exact h6.2.1

theorem ιN_mem_vert_of_mem_N_bd {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {u : S} (hu : u ∈ Γ.N ∩ bd S) :
    ιN u ∈ (α_vert u).vertexSet := by
  have h4 := (hport.r4_vert u hu).2.2
  have hmem : ιN u ∈ (α_vert u).vertexSet ∩ (ιN '' Γ.N) := by
    rw [h4]; exact rfl
  exact hmem.1

theorem inCuffOrder_iff_border_cell_inter_bd (hS : IsSurface S) (Γ : GM17.Painting S)
    {C c₁ c₂ : Set S} (hC : C ∈ cuffs S)
    (hc₁ : c₁ ∈ Γ.C) (hc₂ : c₂ ∈ Γ.C)
    (hc₁C : (c₁ ∩ C).Nonempty) (hc₂C : (c₂ ∩ C).Nonempty)
    (u₁ u₂ : S) :
    InCuffOrder C (c₁ ∩ bd S) u₁ (c₂ ∩ bd S) u₂ ↔ InCuffOrder C c₁ u₁ c₂ u₂ := by
  have hC_sub_bd : C ⊆ bd S := fun z hz => by rw [← sUnion_cuffs (S := S)]; exact ⟨C, hC, hz⟩
  have hbd₁ : (c₁ ∩ bd S).Nonempty := hc₁C.mono (inter_subset_inter_right _ hC_sub_bd)
  have hbd₂ : (c₂ ∩ bd S).Nonempty := hc₂C.mono (inter_subset_inter_right _ hC_sub_bd)
  have hcl₁ : closure (c₁ ∩ bd S) ∩ C = closure c₁ ∩ C := by
    rw [closure_border_cell_inter_bd hS Γ hc₁ hbd₁, Set.inter_assoc, inter_eq_self_of_subset_right hC_sub_bd]
  have hcl₂ : closure (c₂ ∩ bd S) ∩ C = closure c₂ ∩ C := by
    rw [closure_border_cell_inter_bd hS Γ hc₂ hbd₂, Set.inter_assoc, inter_eq_self_of_subset_right hC_sub_bd]
  unfold InCuffOrder
  simp only [hcl₁, hcl₂]

theorem cell_inter_other_cell_vertex_subset_border {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {c c' : Set S} (hc : c ∈ Γ.C) (hbd : (c ∩ bd S).Nonempty)
    (hc' : c' ∈ Γ.C) (hne : c ≠ c') :
    (α_cell c ∩ α_cell c').vertexSet ⊆ ⋃ u ∈ tilde c, (α_vert u).vertexSet := by
  have hS := hport.is_surface
  have : T2Space S := hS.2.1
  by_cases hsame : ∃ C ∈ cuffs S, (c ∩ C).Nonempty ∧ (c' ∩ C).Nonempty
  · rcases hsame with ⟨C, hC, hcC, hc'C⟩
    have hC_sub_bd : C ⊆ bd S := fun z hz => by rw [← sUnion_cuffs (S := S)]; exact ⟨C, hC, hz⟩
    have hbd' : (c' ∩ bd S).Nonempty := hc'C.mono (inter_subset_inter_right _ hC_sub_bd)
    obtain ⟨u₁, u₂, hu₁₂, htilde, _, _, _, _⟩ := Γ.border_cell_exists_ends hc hbd
    have htilde_C : tilde c ⊆ Γ.N ∩ C := (Γ.border_cell_subset_cuff hc hC hcC).2.2.2.1
    have hc_sub_C : c ∩ bd S ⊆ C :=
      (inter_subset_inter_left (bd S) subset_closure).trans (Γ.border_cell_subset_cuff hc hC hcC).1
    have hc'_sub_C : c' ∩ bd S ⊆ C :=
      (inter_subset_inter_left (bd S) subset_closure).trans (Γ.border_cell_subset_cuff hc' hC hc'C).1
    have hu₁_NC : u₁ ∈ Γ.N ∩ C := htilde_C (htilde ▸ Or.inl rfl)
    have hu₂_NC : u₂ ∈ Γ.N ∩ C := htilde_C (htilde ▸ Or.inr rfl)
    let V := Γ.N ∩ bd S
    have hV_fin : V.Finite := Γ.finite_N.subset inter_subset_left
    have hempty_arc : arcComponentsIn (V \ V) = ∅ := by
      ext e
      simp only [arcComponentsIn, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨⟨x, hxe⟩, he_sub, _⟩
      exact (he_sub hxe).2 (he_sub hxe).1
    let Γ₀ : Surface.Drawing S :=
      { U := V
        V := V
        V_subset_U := Subset.rfl
        isClosed_U := hV_fin.isClosed
        finite_V := hV_fin
        finite_edges := by rw [hempty_arc]; exact finite_empty
        edge_cond := by rw [hempty_arc]; rintro _ ⟨⟩ }
    have hV₀_bd : Γ₀.V ∩ bd S = Γ.N ∩ bd S := by
      ext x; simp only [Γ₀, V, mem_inter_iff]; tauto
    have hge2 : ∀ C' ∈ cuffs S, 2 ≤ (Γ₀.V ∩ C').ncard := by
      intro C' hC'
      have h_eq : Γ₀.V ∩ C' = Γ.N ∩ C' := by
        ext x
        simp only [Γ₀, V, mem_inter_iff]
        refine ⟨fun ⟨⟨hxN, _⟩, hxC'⟩ => ⟨hxN, hxC'⟩, fun ⟨hxN, hxC'⟩ => ⟨⟨hxN, ?_⟩, hxC'⟩⟩
        rw [← sUnion_cuffs (S := S)]
        exact ⟨C', hC', hxC'⟩
      rw [h_eq]
      exact cuff_nodes_ge_two_of_painting hS Γ C' hC'
    obtain ⟨hs_mem, hs_ends⟩ := border_cell_space_mem_drawingSpaces hS hV₀_bd hc hbd
    obtain ⟨hs'_mem, _⟩ := border_cell_space_mem_drawingSpaces hS hV₀_bd hc' hbd'
    have hs_u₁u₂ := hs_ends u₁ u₂ hu₁₂ htilde
    have hs_ne_s' : c ∩ bd S ≠ c' ∩ bd S := by
      intro h_eq
      rcases hbd with ⟨x, hxc, hxbd⟩
      have hxc'_bd : x ∈ c' ∩ bd S := h_eq ▸ ⟨hxc, hxbd⟩
      exact hne (Γ.cell_eq_of_mem hc hc' hxc hxc'_bd.1)
    have hord_spaces :=
      inCuffOrder_of_ne_space hS hge2 hC hs_u₁u₂ hs'_mem hc_sub_C hc'_sub_C hs_ne_s'
    rw [htilde]
    intro w hw
    rcases hord_spaces with hord₁ | hord₂
    · rw [inCuffOrder_iff_border_cell_inter_bd hS Γ hC hc hc' hcC hc'C] at hord₁
      have hle := hport.r8_order C hC c hc c' hc' hcC hc'C u₁ hu₁_NC u₂ hu₂_NC hord₁
      have hw_union := hle.1 hw
      rcases hw_union with hw₁ | hw₂
      · exact mem_biUnion (Or.inl rfl) hw₁
      · exact mem_biUnion (Or.inr rfl) hw₂
    · rw [inCuffOrder_iff_border_cell_inter_bd hS Γ hC hc hc' hcC hc'C] at hord₂
      have hle := hport.r8_order C hC c hc c' hc' hcC hc'C u₂ hu₂_NC u₁ hu₁_NC hord₂
      have hw_union := hle.1 hw
      rcases hw_union with hw₂ | hw₁
      · exact mem_biUnion (Or.inr rfl) hw₂
      · exact mem_biUnion (Or.inl rfl) hw₁
  · have hsame' : ∀ C ∈ cuffs S, ¬ ((c ∩ C).Nonempty ∧ (c' ∩ C).Nonempty) :=
      fun C hC h => hsame ⟨C, hC, h⟩
    rw [hport.r7_inter c hc c' hc' hne hsame']
    rintro _ ⟨u, ⟨hu_c, _⟩, rfl⟩
    exact mem_biUnion hu_c (ιN_mem_vert_of_mem_N_bd hport (tilde_subset_N_bd_of_border_cell hc hbd hu_c))

/-- Complementary subgraph `B(c)` for a border cell `c ∈ Γ.C`
(Graph Minors XXI, Section 9, page 40 of the preprint). -/
def borderCellCompl {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {c : Set S} (hc : c ∈ Γ.C) (hbd : (c ∩ bd S).Nonempty) : Hypergraph α β where
  vertexSet := (G.vertexSet \ (α_cell c).vertexSet) ∪ (⋃ u ∈ tilde c, (α_vert u).vertexSet)
  edgeSet := G.edgeSet \ (α_cell c).edgeSet
  Inc e w := e ∈ G.edgeSet \ (α_cell c).edgeSet ∧ G.Inc e w
  vertex_mem_of_inc e w h := by
    rcases h with ⟨⟨heG, he_not_c⟩, hincG⟩
    have hwG : w ∈ G.vertexSet := G.vertex_mem_of_inc hincG
    by_cases hw_c : w ∈ (α_cell c).vertexSet
    · right
      have he_union : e ∈ ⋃ c' ∈ Γ.C, (α_cell c').edgeSet := hport.r3_union_E ▸ heG
      rw [mem_iUnion₂] at he_union
      rcases he_union with ⟨c', hc', he_c'⟩
      have hc'_ne : c ≠ c' := fun h_eq => he_not_c (h_eq ▸ he_c')
      have hc'_le : α_cell c' ≤ G := hport.r2_cell_le c' hc'
      have hinc_c' : (α_cell c').Inc e w :=
        (GM10.inc_iff_of_le hc'_le he_c').mpr hincG
      have hw_c' : w ∈ (α_cell c').vertexSet := (α_cell c').vertex_mem_of_inc hinc_c'
      exact cell_inter_other_cell_vertex_subset_border hport hc hbd hc' hc'_ne ⟨hw_c, hw_c'⟩
    · exact Or.inl ⟨hwG, hw_c⟩
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := by
    refine G.vertexSet_finite.sdiff.union ?_
    exact (Γ.finite_tilde_cell hc).biUnion fun u _ => (α_vert u).vertexSet_finite
  edgeSet_finite := G.edgeSet_finite.sdiff

theorem borderCellCompl_le {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {c : Set S} (hc : c ∈ Γ.C) (hbd : (c ∩ bd S).Nonempty) :
    borderCellCompl hport hc hbd ≤ G := by
  refine ⟨?_, sdiff_subset, fun e he => ?_⟩
  · refine union_subset sdiff_subset (iUnion₂_subset fun u hu => ?_)
    exact (vert_le_cell_of_mem_tilde hport hc hbd hu).1.trans (hport.r2_cell_le c hc).1
  · ext w
    exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩

theorem isSeparation_borderCellCompl {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {c : Set S} (hc : c ∈ Γ.C) (hbd : (c ∩ bd S).Nonempty) :
    G.IsSeparation (α_cell c) (borderCellCompl hport hc hbd) := by
  have hle_c : α_cell c ≤ G := hport.r2_cell_le c hc
  have hle_B : borderCellCompl hport hc hbd ≤ G := borderCellCompl_le hport hc hbd
  rw [GM10.isSeparation_iff_of_le hle_c hle_B]
  refine ⟨?_, ?_, ?_⟩
  · ext w
    simp only [borderCellCompl, mem_union, mem_sdiff]
    constructor
    · rintro (hwc | ⟨hwG, _⟩ | hwt)
      · exact hle_c.1 hwc
      · exact hwG
      · exact hle_B.1 (Or.inr hwt)
    · intro hwG
      by_cases hwc : w ∈ (α_cell c).vertexSet
      · exact Or.inl hwc
      · exact Or.inr (Or.inl ⟨hwG, hwc⟩)
  · ext e
    simp only [borderCellCompl, mem_union, mem_sdiff]
    constructor
    · rintro (hec | ⟨heG, _⟩)
      · exact hle_c.2 hec
      · exact heG
    · intro heG
      by_cases hec : e ∈ (α_cell c).edgeSet
      · exact Or.inl hec
      · exact Or.inr ⟨heG, hec⟩
  · ext e
    simp only [borderCellCompl, mem_inter_iff, mem_sdiff, mem_empty_iff_false, iff_false]
    rintro ⟨hec, _, he_not_c⟩
    exact he_not_c hec

theorem inter_vertexSet_borderCellCompl {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {c : Set S} (hc : c ∈ Γ.C) (hbd : (c ∩ bd S).Nonempty) :
    (α_cell c ∩ borderCellCompl hport hc hbd).vertexSet = ⋃ u ∈ tilde c, (α_vert u).vertexSet := by
  ext w
  simp only [GM10.inter_vertexSet, borderCellCompl, mem_inter_iff, mem_union, mem_sdiff]
  constructor
  · rintro ⟨hwc, ⟨_, hnot_c⟩ | hwt⟩
    · exact (hnot_c hwc).elim
    · exact hwt
  · intro hwt
    refine ⟨?_, Or.inr hwt⟩
    rw [mem_iUnion₂] at hwt
    rcases hwt with ⟨u, hu, hwu⟩
    exact (vert_le_cell_of_mem_tilde hport hc hbd hu).1 hwu

theorem separationOrder_borderCellCompl_le {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ} {q : ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    (hq : ∀ C ∈ cuffs S, q_cuff C ≤ q)
    {c : Set S} (hc : c ∈ Γ.C) (hbd : (c ∩ bd S).Nonempty) :
    separationOrder (α_cell c) (borderCellCompl hport hc hbd) ≤ 2 * q := by
  unfold separationOrder
  rw [inter_vertexSet_borderCellCompl hport hc hbd]
  rcases hbd with ⟨x, hxc, hxbd⟩
  rw [← sUnion_cuffs (S := S)] at hxbd
  rcases hxbd with ⟨C, hC, hxC⟩
  have hcC : (c ∩ C).Nonempty := ⟨x, hxc, hxC⟩
  have htilde_C : tilde c ⊆ Γ.N ∩ C := (Γ.border_cell_subset_cuff hc hC hcC).2.2.2.1
  obtain ⟨u₁, u₂, _, htilde, _, _, _, _⟩ := Γ.border_cell_exists_ends hc ⟨x, hxc, by rw [← sUnion_cuffs (S := S)]; exact ⟨C, hC, hxC⟩⟩
  have hu₁ : u₁ ∈ Γ.N ∩ C := htilde_C (htilde ▸ Or.inl rfl)
  have hu₂ : u₂ ∈ Γ.N ∩ C := htilde_C (htilde ▸ Or.inr rfl)
  have h_biunion : (⋃ u ∈ tilde c, (α_vert u).vertexSet) =
      (α_vert u₁).vertexSet ∪ (α_vert u₂).vertexSet := by
    rw [htilde, biUnion_insert, biUnion_singleton]
  rw [h_biunion]
  have hcard₁ : (α_vert u₁).vertexSet.ncard ≤ q := by
    rw [hport.r5_cuff_card C hC u₁ hu₁]; exact hq C hC
  have hcard₂ : (α_vert u₂).vertexSet.ncard ≤ q := by
    rw [hport.r5_cuff_card C hC u₂ hu₂]; exact hq C hC
  calc ((α_vert u₁).vertexSet ∪ (α_vert u₂).vertexSet).ncard
      ≤ (α_vert u₁).vertexSet.ncard + (α_vert u₂).vertexSet.ncard := ncard_union_le _ _
    _ ≤ q + q := Nat.add_le_add hcard₁ hcard₂
    _ = 2 * q := by ring

/-- Unified complementary subgraph `B(c)` for any cell `c ∈ Γ.C`. -/
noncomputable def cellCompl {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    (c : Set S) (hc : c ∈ Γ.C) : Hypergraph α β :=
  if hbd : (c ∩ bd S).Nonempty then
    borderCellCompl hport hc hbd
  else
    internalCellCompl hport ⟨hc, disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hbd)⟩

theorem cellCompl_eq_border {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {c : Set S} (hc : c ∈ Γ.C) (hbd : (c ∩ bd S).Nonempty) :
    cellCompl hport c hc = borderCellCompl hport hc hbd := by
  simp only [cellCompl, hbd, ↓reduceDIte]

theorem cellCompl_eq_internal {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {c : Set S} (hc : IsInternalCell Γ c) :
    cellCompl hport c hc.1 = internalCellCompl hport hc := by
  have hnot_bd : ¬ (c ∩ bd S).Nonempty := by
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty]
    exact hc.2
  simp only [cellCompl, hnot_bd, ↓reduceDIte]

theorem cellCompl_le {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {c : Set S} (hc : c ∈ Γ.C) :
    cellCompl hport c hc ≤ G := by
  by_cases hbd : (c ∩ bd S).Nonempty
  · rw [cellCompl_eq_border hport hc hbd]
    exact borderCellCompl_le hport hc hbd
  · have hc_int : IsInternalCell Γ c :=
      ⟨hc, disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hbd)⟩
    rw [cellCompl_eq_internal hport hc_int]
    exact internalCellCompl_le hport hc_int

theorem isSeparation_cellCompl {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {c : Set S} (hc : c ∈ Γ.C) :
    G.IsSeparation (α_cell c) (cellCompl hport c hc) := by
  by_cases hbd : (c ∩ bd S).Nonempty
  · rw [cellCompl_eq_border hport hc hbd]
    exact isSeparation_borderCellCompl hport hc hbd
  · have hc_int : IsInternalCell Γ c :=
      ⟨hc, disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hbd)⟩
    rw [cellCompl_eq_internal hport hc_int]
    exact isSeparation_internalCellCompl hport hc_int

theorem ncard_biUnion_le_mul {γ δ : Type*} {I : Set γ} (hI : I.Finite)
    (F : γ → Set δ) (k : ℕ) (hF_fin : ∀ i ∈ I, (F i).Finite)
    (hF_card : ∀ i ∈ I, (F i).ncard ≤ k) :
    (⋃ i ∈ I, F i).ncard ≤ k * I.ncard := by
  refine @Set.Finite.induction_on γ
    (fun s _ => (∀ i ∈ s, (F i).Finite) → (∀ i ∈ s, (F i).ncard ≤ k) →
      (⋃ i ∈ s, F i).ncard ≤ k * s.ncard)
    I hI ?_ ?_ hF_fin hF_card
  · intro _ _
    simp
  · intro a s ha_not hs_fin ih hfin' hcard'
    rw [biUnion_insert, ncard_insert_of_notMem ha_not hs_fin, Nat.mul_add, Nat.mul_one]
    have h_ih := ih (fun i hi => hfin' i ( mem_insert_of_mem a hi))
      (fun i hi => hcard' i (mem_insert_of_mem a hi))
    have ha_card := hcard' a (mem_insert a s)
    calc (F a ∪ ⋃ i ∈ s, F i).ncard
        ≤ (F a).ncard + (⋃ i ∈ s, F i).ncard := ncard_union_le _ _
      _ ≤ k + k * s.ncard := Nat.add_le_add ha_card h_ih
      _ = k * s.ncard + k := Nat.add_comm _ _

/-- Union of cell subgraphs `⋃ c ∈ D, α_cell c` as a subhypergraph of `G`. -/
def cellUnionSubgraph {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    (D : Set (Set S)) (hD : D ⊆ Γ.C) : Hypergraph α β where
  vertexSet := ⋃ c ∈ D, (α_cell c).vertexSet
  edgeSet := ⋃ c ∈ D, (α_cell c).edgeSet
  Inc e w := (∃ c ∈ D, e ∈ (α_cell c).edgeSet) ∧ G.Inc e w
  vertex_mem_of_inc e w h := by
    rcases h with ⟨⟨c, hcD, hec⟩, hincG⟩
    have hle := hport.r2_cell_le c (hD hcD)
    have hinc_c := (GM10.inc_iff_of_le hle hec).mpr hincG
    exact mem_biUnion hcD ((α_cell c).vertex_mem_of_inc hinc_c)
  edge_mem_of_inc _ _ h := by
    rcases h.1 with ⟨c, hcD, hec⟩
    exact mem_biUnion hcD hec
  vertexSet_finite := by
    refine G.vertexSet_finite.subset (iUnion₂_subset fun c hcD => ?_)
    exact (hport.r2_cell_le c (hD hcD)).1
  edgeSet_finite := by
    refine G.edgeSet_finite.subset (iUnion₂_subset fun c hcD => ?_)
    exact (hport.r2_cell_le c (hD hcD)).2

theorem cellUnionSubgraph_le {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {D : Set (Set S)} (hD : D ⊆ Γ.C) :
    cellUnionSubgraph hport D hD ≤ G := by
  refine ⟨iUnion₂_subset fun c hcD => (hport.r2_cell_le c (hD hcD)).1,
    iUnion₂_subset fun c hcD => (hport.r2_cell_le c (hD hcD)).2,
    fun e he => ?_⟩
  simp only [cellUnionSubgraph, mem_iUnion₂] at he
  rcases he with ⟨c, hcD, hec⟩
  ext w
  exact ⟨fun h => ⟨⟨c, hcD, hec⟩, h⟩, fun h => h.2⟩

/-- Intersection of complementary subgraphs `G ∩ ⋂ c ∈ D, B(c)` as a subhypergraph of `G`. -/
noncomputable def cellComplInterSubgraph {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    (D : Set (Set S)) (hD : D ⊆ Γ.C) : Hypergraph α β where
  vertexSet := G.vertexSet ∩ ⋂ c ∈ D, (cellCompl hport c (hD ‹_›)).vertexSet
  edgeSet := G.edgeSet ∩ ⋂ c ∈ D, (cellCompl hport c (hD ‹_›)).edgeSet
  Inc e w := (e ∈ G.edgeSet ∧ ∀ c (hcD : c ∈ D), e ∈ (cellCompl hport c (hD hcD)).edgeSet) ∧ G.Inc e w
  vertex_mem_of_inc e w h := by
    refine ⟨G.vertex_mem_of_inc h.2, mem_iInter₂.mpr fun c hcD => ?_⟩
    have hle := cellCompl_le hport (hD hcD)
    have hinc := (GM10.inc_iff_of_le hle (h.1.2 c hcD)).mpr h.2
    exact (cellCompl hport c (hD hcD)).vertex_mem_of_inc hinc
  edge_mem_of_inc _ _ h := ⟨h.1.1, mem_iInter₂.mpr h.1.2⟩
  vertexSet_finite := G.vertexSet_finite.subset inter_subset_left
  edgeSet_finite := G.edgeSet_finite.subset inter_subset_left

theorem cellComplInterSubgraph_le {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {D : Set (Set S)} (hD : D ⊆ Γ.C) :
    cellComplInterSubgraph hport D hD ≤ G := by
  refine ⟨inter_subset_left, inter_subset_left, fun e he => ?_⟩
  ext w
  exact ⟨fun h => ⟨⟨he.1, fun c hcD => mem_iInter₂.mp he.2 c hcD⟩, h⟩, fun h => h.2⟩

theorem isSeparation_cellUnion_cellComplInter {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {D : Set (Set S)} (hD : D ⊆ Γ.C) :
    G.IsSeparation (cellUnionSubgraph hport D hD) (cellComplInterSubgraph hport D hD) := by
  have hle₁ := cellUnionSubgraph_le hport hD
  have hle₂ := cellComplInterSubgraph_le hport hD
  rw [GM10.isSeparation_iff_of_le hle₁ hle₂]
  refine ⟨?_, ?_, ?_⟩
  · refine Subset.antisymm (union_subset hle₁.1 hle₂.1) fun w hwG => ?_
    by_cases hw₁ : w ∈ (cellUnionSubgraph hport D hD).vertexSet
    · exact Or.inl hw₁
    · right
      refine ⟨hwG, mem_iInter₂.mpr fun c hcD => ?_⟩
      have hnot_c : w ∉ (α_cell c).vertexSet := fun hwc => hw₁ (mem_biUnion hcD hwc)
      have hsep_c := isSeparation_cellCompl hport (hD hcD)
      rcases (hsep_c.vertexSet_union.symm ▸ hwG) with hwc | hwB
      · exact (hnot_c hwc).elim
      · exact hwB
  · refine Subset.antisymm (union_subset hle₁.2 hle₂.2) fun e heG => ?_
    by_cases he₁ : e ∈ (cellUnionSubgraph hport D hD).edgeSet
    · exact Or.inl he₁
    · right
      refine ⟨heG, mem_iInter₂.mpr fun c hcD => ?_⟩
      have hnot_c : e ∉ (α_cell c).edgeSet := fun hec => he₁ (mem_biUnion hcD hec)
      have hsep_c := isSeparation_cellCompl hport (hD hcD)
      rcases (hsep_c.edgeSet_union.symm ▸ heG) with hec | heB
      · exact (hnot_c hec).elim
      · exact heB
  · ext e
    simp only [cellUnionSubgraph, cellComplInterSubgraph, mem_inter_iff, mem_iUnion₂,
      mem_iInter₂, mem_empty_iff_false, iff_false, not_and]
    rintro ⟨c, hcD, hec⟩ _ hB
    have hsep_c := isSeparation_cellCompl hport (hD hcD)
    exact hsep_c.notMem_edgeSet_right hec (hB c hcD)

theorem inter_vertexSet_cellUnion_cellComplInter_subset {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {D : Set (Set S)} (hD : D ⊆ Γ.C) :
    (cellUnionSubgraph hport D hD ∩ cellComplInterSubgraph hport D hD).vertexSet ⊆
      ⋃ c ∈ D, (α_cell c ∩ cellCompl hport c (hD ‹_›)).vertexSet := by
  rintro w ⟨hw₁, _, hw₂⟩
  simp only [cellUnionSubgraph, mem_iUnion₂] at hw₁
  rcases hw₁ with ⟨c, hcD, hwc⟩
  have hwB : w ∈ (cellCompl hport c (hD hcD)).vertexSet := mem_iInter₂.mp hw₂ c hcD
  rw [mem_iUnion₂]
  exact ⟨c, hcD, hwc, hwB⟩

theorem cellUnion_cellComplInter_mem_tangle {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ} {θ_G : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    (h𝒯 : IsTangle G θ_G 𝒯)
    (hsurr : PortraitSurroundsTangle21 Γ α_cell 𝒯)
    {D : Set (Set S)} (hD : D ⊆ Γ.C)
    (hord_D : (⋃ c ∈ D, (α_cell c ∩ cellCompl hport c (hD ‹_›)).vertexSet).ncard < θ_G) :
    (cellUnionSubgraph hport D hD, cellComplInterSubgraph hport D hD) ∈ 𝒯 := by
  have hD_fin : D.Finite := Γ.finite_cells.subset hD
  refine @Set.Finite.induction_on (Set S)
    (fun S_sub _ => ∀ (hS_sub : S_sub ⊆ D),
      (cellUnionSubgraph hport S_sub (hS_sub.trans hD),
       cellComplInterSubgraph hport S_sub (hS_sub.trans hD)) ∈ 𝒯)
    D hD_fin ?_ ?_ Subset.rfl
  · intro h_empty
    have hsep₀ := isSeparation_cellUnion_cellComplInter hport (h_empty.trans hD)
    have hord₀ : separationOrder (cellUnionSubgraph hport ∅ (h_empty.trans hD))
        (cellComplInterSubgraph hport ∅ (h_empty.trans hD)) < θ_G := by
      have hempty_V : (cellUnionSubgraph hport ∅ (h_empty.trans hD) ∩
          cellComplInterSubgraph hport ∅ (h_empty.trans hD)).vertexSet = ∅ := by
        ext w; simp [cellUnionSubgraph]
      unfold separationOrder
      rw [hempty_V, ncard_empty]
      exact h𝒯.one_le
    rcases h𝒯.axiom1 hsep₀ hord₀ with h_in | h_rev
    · exact h_in
    · exfalso
      apply h𝒯.axiom3 h_rev
      ext w
      simp only [cellComplInterSubgraph, mem_inter_iff, mem_iInter, mem_empty_iff_false,
        IsEmpty.forall_iff, implies_true, and_true]
  · intro c S_sub hc_not hS_fin ih h_ins
    have hcD : c ∈ D := h_ins (mem_insert c S_sub)
    have hcC : c ∈ Γ.C := hD hcD
    have hS_sub : S_sub ⊆ D := (subset_insert c S_sub).trans h_ins
    have h_ih := ih hS_sub
    have hsep_c := isSeparation_cellCompl hport hcC
    have h_sub_c : (α_cell c ∩ cellCompl hport c hcC).vertexSet ⊆
        ⋃ c' ∈ D, (α_cell c' ∩ cellCompl hport c' (hD ‹_›)).vertexSet := by
      intro w hw
      rw [mem_iUnion₂]
      exact ⟨c, hcD, hw⟩
    have hfin_big : (⋃ c' ∈ D, (α_cell c' ∩ cellCompl hport c' (hD ‹_›)).vertexSet).Finite :=
      G.vertexSet_finite.subset (iUnion₂_subset fun c' hc'D =>
        inter_subset_left.trans (hport.r2_cell_le c' (hD hc'D)).1)
    have hord_c : separationOrder (α_cell c) (cellCompl hport c hcC) < θ_G :=
      (ncard_le_ncard h_sub_c hfin_big).trans_lt hord_D
    have hc_in_T : (α_cell c, cellCompl hport c hcC) ∈ 𝒯 :=
      GM17.theorem_4_1_i h𝒯 (hsurr c hcC) hsep_c hord_c
    have hA_eq : α_cell c ∪ cellUnionSubgraph hport S_sub (hS_sub.trans hD) =
        cellUnionSubgraph hport (insert c S_sub) (h_ins.trans hD) := by
      refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
        (GM10.union_le (hport.r2_cell_le c hcC) (cellUnionSubgraph_le hport (hS_sub.trans hD)))
        (cellUnionSubgraph_le hport (h_ins.trans hD)) ?_ ?_
      · simp only [GM10.union_vertexSet, cellUnionSubgraph, biUnion_insert]
      · simp only [GM10.union_edgeSet, cellUnionSubgraph, biUnion_insert]
    have hB_eq : cellCompl hport c hcC ∩ cellComplInterSubgraph hport S_sub (hS_sub.trans hD) =
        cellComplInterSubgraph hport (insert c S_sub) (h_ins.trans hD) := by
      refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
        (GM10.inter_le (cellCompl_le hport hcC) (cellComplInterSubgraph_le hport (hS_sub.trans hD)))
        (cellComplInterSubgraph_le hport (h_ins.trans hD)) ?_ ?_
      · ext w
        simp only [GM10.inter_vertexSet, cellComplInterSubgraph, mem_inter_iff, mem_iInter₂,
          mem_insert_iff]
        refine ⟨fun ⟨hwc, hwG, hS⟩ => ⟨hwG, ?_⟩,
          fun ⟨hwG, h_all⟩ => ⟨h_all c (Or.inl rfl), hwG, fun i hi => h_all i (Or.inr hi)⟩⟩
        rintro i (rfl | hi)
        · exact hwc
        · exact hS i hi
      · ext e
        simp only [GM10.inter_edgeSet, cellComplInterSubgraph, mem_inter_iff, mem_iInter₂,
          mem_insert_iff]
        refine ⟨fun ⟨hec, heG, hS⟩ => ⟨heG, ?_⟩,
          fun ⟨heG, h_all⟩ => ⟨h_all c (Or.inl rfl), heG, fun i hi => h_all i (Or.inr hi)⟩⟩
        rintro i (rfl | hi)
        · exact hec
        · exact hS i hi
    have hord_ins : separationOrder
        (α_cell c ∪ cellUnionSubgraph hport S_sub (hS_sub.trans hD))
        (cellCompl hport c hcC ∩ cellComplInterSubgraph hport S_sub (hS_sub.trans hD)) < θ_G := by
      rw [hA_eq, hB_eq]
      unfold separationOrder
      have hsub_ins : (cellUnionSubgraph hport (insert c S_sub) (h_ins.trans hD) ∩
          cellComplInterSubgraph hport (insert c S_sub) (h_ins.trans hD)).vertexSet ⊆
          ⋃ c' ∈ D, (α_cell c' ∩ cellCompl hport c' (hD ‹_›)).vertexSet := by
        refine (inter_vertexSet_cellUnion_cellComplInter_subset hport (h_ins.trans hD)).trans ?_
        rintro w hw
        rw [mem_iUnion₂] at hw ⊢
        rcases hw with ⟨c', hc'_ins, hwc'⟩
        exact ⟨c', h_ins hc'_ins, hwc'⟩
      exact (ncard_le_ncard hsub_ins hfin_big).trans_lt hord_D
    rw [← hA_eq, ← hB_eq]
    exact GM10.theorem_2_2_proof h𝒯 hc_in_T h_ih hord_ins

/-! ## 4. Proof of `(9.2)` -/

/-- The explicit separation-order bound `n = 3p + 2q(3p + c(Σ))` in the proof of Graph Minors XXI,
(9.2) (page 39 of the preprint). -/
noncomputable def portraitSeparationBound (S : Type) [TopologicalSpace S] (p q : ℕ) : ℕ :=
  3 * p + 2 * q * (3 * p + (cuffs S).ncard)

/-- For every cuff `C ∈ cuffs S` and every boundary vertex `u ∈ Γ.N ∩ C`, there is a border cell
`c ∈ Γ.C` bordering `C` with `u ∈ tilde c` and `α_vert u ≤ α_cell c`. -/
theorem exists_border_cell_of_mem_N_cuff {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {C : Set S} (hC : C ∈ cuffs S) {u : S} (hu : u ∈ Γ.N ∩ C) :
    ∃ c ∈ Γ.C, (c ∩ C).Nonempty ∧ (c ∩ bd S).Nonempty ∧ u ∈ tilde c ∧ α_vert u ≤ α_cell c := by
  have hS := hport.is_surface
  have : T2Space S := hS.2.1
  let V := Γ.N ∩ bd S
  have hV_fin : V.Finite := Γ.finite_N.subset inter_subset_left
  have hempty_arc : arcComponentsIn (V \ V) = ∅ := by
    ext e
    simp only [arcComponentsIn, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨⟨x, hxe⟩, he_sub, _⟩
    exact (he_sub hxe).2 (he_sub hxe).1
  let Γ₀ : Surface.Drawing S :=
    { U := V
      V := V
      V_subset_U := Subset.rfl
      isClosed_U := hV_fin.isClosed
      finite_V := hV_fin
      finite_edges := by rw [hempty_arc]; exact finite_empty
      edge_cond := by rw [hempty_arc]; rintro _ ⟨⟩ }
  have hV₀_bd : Γ₀.V ∩ bd S = Γ.N ∩ bd S := by
    ext x; simp only [Γ₀, V, mem_inter_iff]; tauto
  have hge2 : ∀ C' ∈ cuffs S, 2 ≤ (Γ₀.V ∩ C').ncard := by
    intro C' hC'
    have h_eq : Γ₀.V ∩ C' = Γ.N ∩ C' := by
      ext x
      simp only [Γ₀, V, mem_inter_iff]
      refine ⟨fun ⟨⟨hxN, _⟩, hxC'⟩ => ⟨hxN, hxC'⟩, fun ⟨hxN, hxC'⟩ => ⟨⟨hxN, ?_⟩, hxC'⟩⟩
      rw [← sUnion_cuffs (S := S)]
      exact ⟨C', hC', hxC'⟩
    rw [h_eq]
    exact cuff_nodes_ge_two_of_painting hS Γ C' hC'
  let f := cuffHomeo hS hC
  have hk := hge2 C hC
  have hu_V₀C : u ∈ Γ₀.V ∩ C := by
    refine ⟨⟨hu.1, ?_⟩, hu.2⟩
    rw [← sUnion_cuffs (S := S)]
    exact ⟨C, hC, hu.2⟩
  have hu_range : u ∈ Set.range (vNode Γ₀.V Γ₀.finite_V f) := by
    rwa [range_vNode Γ₀.V Γ₀.finite_V f]
  rcases hu_range with ⟨i, hi_eq⟩
  have hends_i := spaceHasEnds_vSpaceArc hS hge2 hC f i
  obtain ⟨c, ⟨hc, hbd, hc_eq⟩, _⟩ :=
    exists_border_cell_of_mem_drawingSpaces hS hV₀_bd hends_i.1
  have hs_C : c ∩ bd S ⊆ C := by
    rw [hc_eq]
    exact (vSpaceArc_subset_diff Γ₀.V Γ₀.finite_V f hk i).trans sdiff_subset
  have hcC : (c ∩ C).Nonempty := by
    rcases hbd with ⟨x, hxc, hxbd⟩
    exact ⟨x, hxc, hs_C ⟨hxc, hxbd⟩⟩
  obtain ⟨u₁, u₂, hu₁₂, htilde, _, _, _, _⟩ := Γ.border_cell_exists_ends hc hbd
  have hs_ends := (border_cell_space_mem_drawingSpaces hS hV₀_bd hc hbd).2 u₁ u₂ hu₁₂ htilde
  have hpair := ends_pair_eq_of_spaceHasEnds (hc_eq ▸ hs_ends) hends_i
  have hu_tilde : u ∈ tilde c := by
    rw [htilde, hpair, ← hi_eq]
    exact Or.inl rfl
  exact ⟨c, hc, hcC, hbd, hu_tilde, vert_le_cell_of_mem_tilde hport hc hbd hu_tilde⟩

/-- Helper for `(P3)` in Claim (1) of `(9.2)`: any unit `x` on a cuff `C` whose closure lies in
`cuffPoint f '' Icc a b` (with `a ≤ b ≤ t_end ≤ a + 2π` and `cuffPoint f t_end ∈ Γ'.V ∩ C`) either
has `μ x = ⊥`, equals `.vertex (cuffPoint f t_end)`, or is bounded by `α_cell c` for a border cell
`c` whose closure on `C` lies in `cuffPoint f '' Icc a' b'` with `a ≤ a' ≤ b' ≤ t_end`. -/
theorem exists_border_cell_for_unit_in_cuff_arc {α : Type u} {β : Type v}
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β}
    {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff)
    {Γ' : Surface.Drawing S} (hV_bd : Γ'.V ∩ bd S = Γ.N ∩ bd S)
    (hge2 : ∀ C' ∈ cuffs S, 2 ≤ (Γ'.V ∩ C').ncard)
    {μ : BoundaryUnit S → Hypergraph α β}
    (hμ_vert : ∀ u, μ (.vertex u) = if u ∈ Γ.N ∩ bd S then α_vert u else ⊥)
    (hμ_space : ∀ s, μ (.space s) =
      if hs : ∃ c ∈ Γ.C, (c ∩ bd S).Nonempty ∧ c ∩ bd S = s then α_cell (Classical.choose hs) else ⊥)
    {C : Set S} (hC : C ∈ cuffs S) (f : Circle ≃ₜ C)
    {a b t_end : ℝ} (hab : a ≤ b) (hbt : b ≤ t_end) (ht_le : t_end ≤ a + 2 * Real.pi)
    (ht_end_mem : cuffPoint f t_end ∈ Γ'.V ∩ C)
    {x : BoundaryUnit S} (hxC : x.InSet C)
    (hx_ne : (closure x.toSet ∩ C).Nonempty)
    (hx_sub : closure x.toSet ∩ C ⊆ cuffPoint f '' Icc a b) :
    μ x = ⊥ ∨
    x = .vertex (cuffPoint f t_end) ∨
    ∃ (c : Set S) (a' b' : ℝ),
      c ∈ Γ.C ∧ (c ∩ C).Nonempty ∧ μ x ≤ α_cell c ∧
      a ≤ a' ∧ a' ≤ b' ∧ b' ≤ t_end ∧
      (closure c ∩ C).Nonempty ∧ closure c ∩ C ⊆ cuffPoint f '' Icc a' b' := by
  have hS := hport.is_surface
  have : T2Space S := hS.2.1
  have hC_sub_bd : C ⊆ bd S := fun z hz => by rw [← sUnion_cuffs (S := S)]; exact ⟨C, hC, hz⟩
  cases x with
  | space s =>
    by_cases hs_ex : ∃ c ∈ Γ.C, (c ∩ bd S).Nonempty ∧ c ∩ bd S = s
    · right; right
      let c := Classical.choose hs_ex
      obtain ⟨hc, hbd, hc_eq⟩ := Classical.choose_spec hs_ex
      have hμ_eq : μ (.space s) = α_cell c := by simp only [hμ_space, hs_ex, ↓reduceDIte, c]
      have hsC : s ⊆ C := hxC
      have hcC : (c ∩ C).Nonempty := by
        rcases hbd with ⟨z, hzc, hzbd⟩
        exact ⟨z, hzc, hsC (hc_eq ▸ ⟨hzc, hzbd⟩)⟩
      have hcl_eq : closure c ∩ C = closure s ∩ C := by
        rw [← hc_eq, closure_border_cell_inter_bd hS Γ hc hbd, Set.inter_assoc,
          inter_eq_self_of_subset_right hC_sub_bd]
      refine ⟨c, a, b, hc, hcC, hμ_eq ▸ le_rfl, le_rfl, hab, hbt, ?_, ?_⟩
      · rwa [hcl_eq]
      · rwa [hcl_eq]
    · left
      simp only [hμ_space, hs_ex, ↓reduceDIte]
  | vertex v =>
    by_cases hv_N : v ∈ Γ.N ∩ bd S
    · by_cases hv_end : v = cuffPoint f t_end
      · exact Or.inr (Or.inl (congrArg BoundaryUnit.vertex hv_end))
      · right; right
        have hvC : v ∈ C := hxC
        have hv_V'C : v ∈ Γ'.V ∩ C := by
          have hv_V'bd : v ∈ Γ'.V ∩ bd S := hV_bd.symm ▸ hv_N
          exact ⟨hv_V'bd.1, hvC⟩
        have hv_cl : v ∈ closure ({v} : Set S) ∩ C := ⟨subset_closure rfl, hvC⟩
        obtain ⟨τ, ⟨ha_le_τ, hτ_le_b⟩, hτ_eq⟩ := hx_sub hv_cl
        have hτ_lt_tend : τ < t_end :=
          lt_of_le_of_ne (hτ_le_b.trans hbt) (fun h => hv_end (hτ_eq.symm.trans (congrArg _ h)))
        have htend_lt_2pi : t_end < τ + 2 * Real.pi := by
          refine lt_of_le_of_ne (ht_le.trans (by linarith)) fun h => hv_end ?_
          rw [h, GM19.cuffPoint_add_two_pi, hτ_eq]
        have hk := hge2 C hC
        have hv_range : v ∈ Set.range (vNode Γ'.V Γ'.finite_V f) := by
          rwa [range_vNode Γ'.V Γ'.finite_V f]
        rcases hv_range with ⟨i, hi_eq⟩
        have hτ_mem : cuffPoint f τ ∈ Γ'.V ∩ C := hτ_eq.symm ▸ hv_V'C
        obtain ⟨α_ang, β_ang, hτ_le_α, hα_lt_β, hβ_le_2pi, hα_eq, _, hs_eq, hcl_s_eq⟩ :=
          vSpaceArc_eq_Ioo_from_vertex_angle hS hC f hk hτ_mem i
        have hτ_eq_α : τ = α_ang := by
          apply (cuffPoint_injOn_Ico f τ ⟨hτ_le_α, hα_lt_β.trans_le hβ_le_2pi⟩ ⟨le_rfl, by linarith [Real.pi_pos]⟩ ?_).symm
          rw [hα_eq, hi_eq, hτ_eq]
        subst hτ_eq_α
        have hβ_le_tend : β_ang ≤ t_end := by
          by_contra hlt_β
          push Not at hlt_β
          have ht_in_s : cuffPoint f t_end ∈ vSpaceArc Γ'.V Γ'.finite_V f hk i := by
            rw [hs_eq]
            exact ⟨t_end, ⟨hτ_lt_tend, hlt_β⟩, rfl⟩
          exact (vSpaceArc_subset_diff Γ'.V Γ'.finite_V f hk i ht_in_s).2 ht_end_mem.1
        have hends_i := spaceHasEnds_vSpaceArc hS hge2 hC f i
        obtain ⟨c, ⟨hc, hbd, hc_eq⟩, _⟩ :=
          exists_border_cell_of_mem_drawingSpaces hS hV_bd hends_i.1
        have hs_C : c ∩ bd S ⊆ C := by
          rw [hc_eq]
          exact (vSpaceArc_subset_diff Γ'.V Γ'.finite_V f hk i).trans sdiff_subset
        have hcC : (c ∩ C).Nonempty := by
          rcases hbd with ⟨z, hzc, hzbd⟩
          exact ⟨z, hzc, hs_C ⟨hzc, hzbd⟩⟩
        obtain ⟨u₁, u₂, hu₁₂, htilde, _, _, _, _⟩ := Γ.border_cell_exists_ends hc hbd
        have hs_ends := (border_cell_space_mem_drawingSpaces hS hV_bd hc hbd).2 u₁ u₂ hu₁₂ htilde
        have hpair := ends_pair_eq_of_spaceHasEnds (hc_eq ▸ hs_ends) hends_i
        have hv_tilde : v ∈ tilde c := by
          rw [htilde, hpair, ← hi_eq]
          exact Or.inl rfl
        have hμ_le : μ (.vertex v) ≤ α_cell c := by
          simp only [hμ_vert, hv_N, ↓reduceIte]
          exact vert_le_cell_of_mem_tilde hport hc hbd hv_tilde
        have hcl_c_C : closure c ∩ C = cuffPoint f '' Icc τ β_ang := by
          calc closure c ∩ C
              = closure c ∩ (bd S ∩ C) := by rw [inter_eq_self_of_subset_right hC_sub_bd]
            _ = (closure c ∩ bd S) ∩ C := (Set.inter_assoc _ _ _).symm
            _ = closure (c ∩ bd S) ∩ C := by rw [← closure_border_cell_inter_bd hS Γ hc hbd]
            _ = closure (vSpaceArc Γ'.V Γ'.finite_V f hk i) ∩ C := by rw [hc_eq]
            _ = (cuffPoint f '' Icc τ β_ang) ∩ C := by rw [hcl_s_eq]
            _ = cuffPoint f '' Icc τ β_ang := by
              rw [inter_eq_left]
              rintro _ ⟨t, _, rfl⟩
              exact GM19.cuffPoint_mem f t
        refine ⟨c, τ, β_ang, hc, hcC, hμ_le, ha_le_τ, hα_lt_β.le, hβ_le_tend, ?_, ?_⟩
        · rw [hcl_c_C]
          exact ⟨cuffPoint f τ, ⟨τ, ⟨le_rfl, hα_lt_β.le⟩, rfl⟩⟩
        · rw [hcl_c_C]
    · left
      simp only [hμ_vert, hv_N, ↓reduceIte]

/-- Shape-based form of **Graph Minors XXI, (9.2)** (page 38 of the preprint) using
`PortraitHasDepthLe21` and `PortraitSurroundsTangle21`. -/
theorem theorem_9_2_shapes
    (S : Type) [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) (p q : ℕ) (hq : 1 ≤ q) :
    ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ {α : Type u} {β : Type v} (G : Hypergraph α β), G.IsGraph →
        ∀ (Γ : GM17.Painting S) (ιN : S → α)
          (α_cell : Set S → Hypergraph α β) (α_vert : S → Hypergraph α β)
          (θ_G : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
          PortraitHasDepthLe21 G Γ ιN α_cell α_vert q →
          θ ≤ θ_G →
          IsTangle G θ_G 𝒯 →
          PortraitSurroundsTangle21 Γ α_cell 𝒯 →
          ¬ HasVitalPLinkage G p := by
  have : T2Space S := hS.2.1
  let n := portraitSeparationBound S p q
  let r := 3 * p + (cuffs S).ncard
  obtain ⟨θ₈₄, hθ₈₄_pos, h84⟩ := theorem_8_4_proof S hS (p + n) r q hq
  let θ' := max θ₈₄ (2 * q + 4)
  let θ := θ' + n
  have hθ'_gt_2q : 2 * q + 3 < θ' := Nat.lt_of_succ_le (le_max_right θ₈₄ (2 * q + 4))
  have hθ'_ge_84 : θ₈₄ ≤ θ' := le_max_left θ₈₄ (2 * q + 4)
  have hθ_pos : 1 ≤ θ := le_trans hθ₈₄_pos (le_trans hθ'_ge_84 (Nat.le_add_right θ' n))
  refine ⟨θ, hθ_pos, ?_⟩
  intro α β G hG Γ ιN α_cell α_vert θ_G 𝒯 ⟨q_cuff, hport, hq_cuff⟩ hθ_le h𝒯 hsurr ⟨L, hL⟩
  -- `G` has an edge, since its tangle has order at least 2, so `α` is not empty.
  have : Nonempty α := by
    obtain ⟨e, he⟩ := exists_edge_of_isTangle h𝒯 (by omega)
    obtain ⟨x, -⟩ := (hG e he).1
    exact ⟨x⟩
  -- Define A₁: internal cells containing a terminal of L outside tilde c
  let 𝒜₁ : Set (Set S) :=
    {c ∈ Γ.C | IsInternalCell Γ c ∧ (((α_cell c).vertexSet \ (ιN '' tilde c)) ∩ terminals L).Nonempty}
  have h𝒜₁_sub : 𝒜₁ ⊆ Γ.C := fun _ h => h.1
  have h𝒜₁_fin : 𝒜₁.Finite := Γ.finite_cells.subset h𝒜₁_sub
  -- |𝒜₁| ≤ p
  have h𝒜₁_card_le : 𝒜₁.ncard ≤ p := by
    let term_of : Set S → α := fun c =>
      if hc : c ∈ 𝒜₁ then Classical.choose hc.2.2 else Classical.arbitrary α
    have hterm_spec : ∀ c ∈ 𝒜₁,
        term_of c ∈ ((α_cell c).vertexSet \ (ιN '' tilde c)) ∩ terminals L := fun c hc => by
      simp only [term_of, hc, ↓reduceDIte]
      exact Classical.choose_spec hc.2.2
    have hterm_maps : MapsTo term_of 𝒜₁ (terminals L) :=
      fun c hc => (hterm_spec c hc).2
    have hterm_inj : InjOn term_of 𝒜₁ := by
      intro c₁ hc₁ c₂ hc₂ h_eq
      by_contra hne
      have hno_cuff : ∀ C ∈ cuffs S, ¬ ((c₁ ∩ C).Nonempty ∧ (c₂ ∩ C).Nonempty) := by
        intro C hC ⟨⟨x, hxc₁, hxC⟩, _⟩
        have hxbd : x ∈ bd S := by rw [← sUnion_cuffs (S := S)]; exact ⟨C, hC, hxC⟩
        exact Set.disjoint_left.mp hc₁.2.1.2 hxc₁ hxbd
      have hw₁ := (hterm_spec c₁ hc₁).1
      have hw₂ := (hterm_spec c₂ hc₂).1.1
      rw [← h_eq] at hw₂
      have hw_inter : term_of c₁ ∈ (α_cell c₁ ∩ α_cell c₂).vertexSet := ⟨hw₁.1, hw₂⟩
      rw [hport.r7_inter c₁ hc₁.1 c₂ hc₂.1 hne hno_cuff] at hw_inter
      exact hw₁.2 (image_mono inter_subset_left hw_inter)
    have hterm_fin : (terminals L).Finite := L.vertexSet_finite.subset fun _ h => h.1
    calc 𝒜₁.ncard
        = (term_of '' 𝒜₁).ncard := hterm_inj.ncard_image.symm
      _ ≤ (terminals L).ncard := ncard_le_ncard hterm_maps.image_subset hterm_fin
      _ ≤ p := hL.2.2
  -- Every cell c ∈ Γ.C with |tilde c| = 3 belongs to 𝒜₁
  have h_three_in_𝒜₁ : ∀ c ∈ Γ.C, (tilde c).ncard = 3 → c ∈ 𝒜₁ := by
    intro c hc hcard3
    have hc_int : IsInternalCell Γ c := by
      refine ⟨hc, disjoint_iff_inter_eq_empty.mpr ?_⟩
      by_contra hne_empty
      have hbd : (c ∩ bd S).Nonempty := nonempty_iff_ne_empty.mpr hne_empty
      have h2 := (Γ.border_cell c hc hbd).1
      omega
    rcases theorem_9_1_shapes hG hport hL.1 hc_int with hterm | hdraw
    · exact ⟨hc, hc_int, hterm⟩
    · exact (hport.r9_three c hc hcard3 hdraw).elim
  -- Unlinked border cells 𝒰
  let 𝒰 : Set (Set S) :=
    {c ∈ Γ.C | (c ∩ bd S).Nonempty ∧
      ¬ (∀ u v : S, u ≠ v → tilde c = {u, v} →
          HasDisjointPaths (α_cell c).skeleton (α_vert u).vertexSet (α_vert v).vertexSet
            (α_vert u).vertexSet.ncard)}
  have h𝒰_sub_biUnion : 𝒰 ⊆ ⋃ c' ∈ {c' ∈ 𝒜₁ | (tilde c').ncard = 3},
      {c ∈ Γ.C | (c ∩ bd S).Nonempty ∧ tilde c ⊆ tilde c'} := by
    rintro c ⟨hc, hbd, hnot_link⟩
    push Not at hnot_link
    rcases hnot_link with ⟨u, v, huv, htilde_c, hnot_paths⟩
    rcases (hport.r6_border c hc hbd u v huv htilde_c).2.2 with hpaths | ⟨c', hc', hcard3, hu', hv'⟩
    · exact (hnot_paths hpaths).elim
    · refine mem_biUnion ⟨h_three_in_𝒜₁ c' hc' hcard3, hcard3⟩ ⟨hc, hbd, ?_⟩
      rw [htilde_c]
      rintro z (rfl | rfl) <;> assumption
  have h𝒰_fin : 𝒰.Finite := Γ.finite_cells.subset fun _ h => h.1
  have h𝒰_card_le : 𝒰.ncard ≤ 3 * p := by
    let 𝒜₁_three := {c' ∈ 𝒜₁ | (tilde c').ncard = 3}
    have h𝒜₁_three_fin : 𝒜₁_three.Finite := h𝒜₁_fin.subset fun _ h => h.1
    have hbi_fin : (⋃ c' ∈ 𝒜₁_three, {c ∈ Γ.C | (c ∩ bd S).Nonempty ∧ tilde c ⊆ tilde c'}).Finite :=
      h𝒜₁_three_fin.biUnion fun _ _ => Γ.finite_cells.subset fun _ h => h.1
    calc 𝒰.ncard
        ≤ (⋃ c' ∈ 𝒜₁_three, {c ∈ Γ.C | (c ∩ bd S).Nonempty ∧ tilde c ⊆ tilde c'}).ncard :=
          ncard_le_ncard h𝒰_sub_biUnion hbi_fin
      _ ≤ 3 * 𝒜₁_three.ncard :=
          ncard_biUnion_le_mul h𝒜₁_three_fin _ 3
            (fun _ _ => Γ.finite_cells.subset fun _ h => h.1)
            (fun c' hc' => ncard_border_cells_subset_three_le hS Γ hc'.1.1 hc'.2)
      _ ≤ 3 * 𝒜₁.ncard := Nat.mul_le_mul_left 3 (ncard_le_ncard (fun _ h => h.1) h𝒜₁_fin)
      _ ≤ 3 * p := Nat.mul_le_mul_left 3 h𝒜₁_card_le
  -- Pick one representative border cell per cuff C ∈ cuffs S
  have h_cuff_cell : ∀ C ∈ cuffs S, ∃ c ∈ Γ.C, (c ∩ bd S).Nonempty ∧ c ∩ bd S ⊆ C := by
    intro C hC
    have hge2_N := cuff_nodes_ge_two_of_painting hS Γ C hC
    obtain ⟨u, hu, _, _, _⟩ := exists_two_distinct_of_ncard_ge_two hge2_N
    obtain ⟨c, hc, hcC, hbd, _, _⟩ := exists_border_cell_of_mem_N_cuff hport hC hu
    exact ⟨c, hc, hbd, (inter_subset_inter_left (bd S) subset_closure).trans
      (Γ.border_cell_subset_cuff hc hC hcC).1⟩
  let c_rep : Set S → Set S := fun C =>
    if hC : C ∈ cuffs S then Classical.choose (h_cuff_cell C hC) else ∅
  have hc_rep_spec : ∀ C ∈ cuffs S,
      c_rep C ∈ Γ.C ∧ (c_rep C ∩ bd S).Nonempty ∧ c_rep C ∩ bd S ⊆ C := fun C hC => by
    simp only [c_rep, hC, ↓reduceDIte]
    exact Classical.choose_spec (h_cuff_cell C hC)
  let 𝒜₂ : Set (Set S) := 𝒰 ∪ (c_rep '' cuffs S)
  have h𝒜₂_border : ∀ c ∈ 𝒜₂, c ∈ Γ.C ∧ (c ∩ bd S).Nonempty := by
    rintro c (hc𝒰 | ⟨C, hC, rfl⟩)
    · exact ⟨hc𝒰.1, hc𝒰.2.1⟩
    · exact ⟨(hc_rep_spec C hC).1, (hc_rep_spec C hC).2.1⟩
  have h𝒜₂_sub : 𝒜₂ ⊆ Γ.C := fun c hc => (h𝒜₂_border c hc).1
  have h𝒜₂_fin : 𝒜₂.Finite := Γ.finite_cells.subset h𝒜₂_sub
  have hcuffs_fin : (cuffs S).Finite := (cuff_statement.{0} S hS).2.1
  have h𝒜₂_card_le : 𝒜₂.ncard ≤ r := by
    calc 𝒜₂.ncard
        ≤ 𝒰.ncard + (c_rep '' cuffs S).ncard := ncard_union_le _ _
      _ ≤ 3 * p + (cuffs S).ncard := Nat.add_le_add h𝒰_card_le (ncard_image_le hcuffs_fin)
      _ = r := rfl
  have h𝒜₁_𝒜₂_disj : Disjoint 𝒜₁ 𝒜₂ := by
    rw [disjoint_iff_inter_eq_empty]
    ext c
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hc₁ hc₂
    rcases (h𝒜₂_border c hc₂).2 with ⟨x, hxc, hxbd⟩
    exact Set.disjoint_left.mp hc₁.2.1.2 hxc hxbd
  -- Remaining internal cells ℐ = {c ∈ Γ.C | IsInternalCell Γ c ∧ c ∉ 𝒜₁}
  let ℐ : Set (Set S) := {c ∈ Γ.C | IsInternalCell Γ c ∧ c ∉ 𝒜₁}
  -- Construct G' and Γ'_sub
  let G'_V : Set α :=
    (ιN '' Γ.N) ∪ (⋃ u ∈ Γ.N ∩ bd S, (α_vert u).vertexSet) ∪
      (⋃ c ∈ Γ.C \ (𝒜₁ ∪ 𝒜₂), (α_cell c).vertexSet)
  let G'_E : Set β := ⋃ c ∈ Γ.C \ (𝒜₁ ∪ 𝒜₂), (α_cell c).edgeSet
  have hG'_V_sub : G'_V ⊆ G.vertexSet := by
    refine union_subset (union_subset hport.r1_subset ?_) ?_
    · exact iUnion₂_subset fun u hu => (hport.r4_vert u hu).1.1
    · exact iUnion₂_subset fun c hc => (hport.r2_cell_le c hc.1).1
  have hG'_E_sub : G'_E ⊆ G.edgeSet :=
    iUnion₂_subset fun c hc => (hport.r2_cell_le c hc.1).2
  let G' : Hypergraph α β :=
    { vertexSet := G'_V
      edgeSet := G'_E
      Inc e w := e ∈ G'_E ∧ G.Inc e w
      vertex_mem_of_inc e w h := by
        rcases h with ⟨he, hincG⟩
        rw [mem_iUnion₂] at he
        rcases he with ⟨c, hc, hec⟩
        have hinc_c := (GM10.inc_iff_of_le (hport.r2_cell_le c hc.1) hec).mpr hincG
        exact Or.inr (mem_biUnion hc ((α_cell c).vertex_mem_of_inc hinc_c))
      edge_mem_of_inc _ _ h := h.1
      vertexSet_finite := G.vertexSet_finite.subset hG'_V_sub
      edgeSet_finite := G.edgeSet_finite.subset hG'_E_sub }
  have hG'_le : G' ≤ G :=
    ⟨hG'_V_sub, hG'_E_sub, fun e he => by ext w; exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩⟩
  have hG'_graph : G'.IsGraph := fun e he => by
    rw [← hG'_le.3 e he]
    exact hG e (hG'_le.2 he)
  let Γ'_sub_V : Set α := (ιN '' Γ.N) ∪ (⋃ c ∈ ℐ, (α_cell c).vertexSet)
  let Γ'_sub_E : Set β := ⋃ c ∈ ℐ, (α_cell c).edgeSet
  have hℐ_sub_diff : ℐ ⊆ Γ.C \ (𝒜₁ ∪ 𝒜₂) := by
    rintro c ⟨hc, hc_int, hc_not₁⟩
    refine ⟨hc, ?_⟩
    rintro (h1 | h2)
    · exact hc_not₁ h1
    · rcases (h𝒜₂_border c h2).2 with ⟨x, hxc, hxbd⟩
      exact Set.disjoint_left.mp hc_int.2 hxc hxbd
  have hΓ'_sub_V_sub : Γ'_sub_V ⊆ G'.vertexSet := by
    refine union_subset (subset_union_left.trans subset_union_left) ?_
    exact (biUnion_mono hℐ_sub_diff fun _ _ => Subset.rfl).trans subset_union_right
  have hΓ'_sub_E_sub : Γ'_sub_E ⊆ G'.edgeSet :=
    biUnion_mono hℐ_sub_diff fun _ _ => Subset.rfl
  let Γ'_sub : Hypergraph α β :=
    { vertexSet := Γ'_sub_V
      edgeSet := Γ'_sub_E
      Inc e w := e ∈ Γ'_sub_E ∧ G.Inc e w
      vertex_mem_of_inc e w h := by
        rcases h with ⟨he, hincG⟩
        rw [mem_iUnion₂] at he
        rcases he with ⟨c, hc, hec⟩
        have hinc_c := (GM10.inc_iff_of_le (hport.r2_cell_le c hc.1) hec).mpr hincG
        exact Or.inr (mem_biUnion hc ((α_cell c).vertex_mem_of_inc hinc_c))
      edge_mem_of_inc _ _ h := h.1
      vertexSet_finite := G'.vertexSet_finite.subset hΓ'_sub_V_sub
      edgeSet_finite := G'.edgeSet_finite.subset hΓ'_sub_E_sub }
  have hΓ'_sub_le : Γ'_sub ≤ G' :=
    ⟨hΓ'_sub_V_sub, hΓ'_sub_E_sub, fun e he => by
      ext w
      exact ⟨fun h => ⟨he, h.2⟩, fun h => ⟨hΓ'_sub_E_sub he, h.2⟩⟩⟩
  -- Construct the drawing Γ' and isomorphism maps (ιV', ιE') by drawing α_cell c in closure c
  -- for each internal cell c ∈ ℐ (c ∉ 𝒜₁), using (9.1)
  have hℐ_card : ∀ c ∈ ℐ, (tilde c).ncard = 2 := fun c hc =>
    (hport.r1_painting c hc.1).resolve_right (fun h3 => hc.2.2 (h_three_in_𝒜₁ c hc.1 h3))
  have hℐ_draw : ∀ c ∈ ℐ, CanBeDrawnInDisc21 (α_cell c) (ιN '' tilde c) := fun c hc =>
    (theorem_9_1_shapes hG hport hL.1 hc.2.1).resolve_left (fun hterm => hc.2.2 ⟨hc.1, hc.2.1, hterm⟩)
  obtain ⟨e₀, _⟩ := exists_edge_of_isTangle h𝒯 (by omega)
  obtain ⟨Γ', ιV', ιE', hΓ'_proper, hV'_bd, hιV'_N, hiso⟩ :=
    exists_drawing_of_internal_cells (Γ'_sub := Γ'_sub) hS hG hport
      (fun _ h => h.1) (fun _ h => h.2.1)
      hℐ_card hℐ_draw (Classical.arbitrary α) e₀ rfl rfl
      (fun e he w => ⟨fun h => h.2, fun h => ⟨he, h⟩⟩)
  have hge2_Γ' : ∀ C ∈ cuffs S, 2 ≤ (Γ'.V ∩ C).ncard := by
    intro C hC
    have hC_sub_bd : C ⊆ bd S := fun z hz => by rw [← sUnion_cuffs (S := S)]; exact ⟨C, hC, hz⟩
    have h_eq : Γ'.V ∩ C = Γ.N ∩ C := by
      calc Γ'.V ∩ C
          = (Γ'.V ∩ bd S) ∩ C := by rw [Set.inter_assoc, inter_eq_self_of_subset_right hC_sub_bd]
        _ = (Γ.N ∩ bd S) ∩ C := by rw [hV'_bd]
        _ = Γ.N ∩ C := by rw [Set.inter_assoc, inter_eq_self_of_subset_right hC_sub_bd]
    rw [h_eq]
    exact cuff_nodes_ge_two_of_painting hS Γ C hC
  -- Construct M and F_star from 𝒜₂
  let M : Set (Set S) := (fun c => c ∩ bd S) '' 𝒜₂
  have hM_sub : M ⊆ drawingSpaces Γ' := by
    rintro _ ⟨c, hc₂, rfl⟩
    obtain ⟨hc, hbd⟩ := h𝒜₂_border c hc₂
    exact (border_cell_space_mem_drawingSpaces hS hV'_bd hc hbd).1
  have hM_cuff : ∀ C ∈ cuffs S, ∃ s ∈ M, s ⊆ C := by
    intro C hC
    refine ⟨c_rep C ∩ bd S, ⟨c_rep C, Or.inr ⟨C, hC, rfl⟩, rfl⟩, (hc_rep_spec C hC).2.2⟩
  have hM_inj : InjOn (fun c => c ∩ bd S) 𝒜₂ := by
    intro c₁ hc₁ c₂ hc₂ h_eq
    change c₁ ∩ bd S = c₂ ∩ bd S at h_eq
    obtain ⟨hc₁_C, hbd₁⟩ := h𝒜₂_border c₁ hc₁
    obtain ⟨hc₂_C, _⟩ := h𝒜₂_border c₂ hc₂
    rcases hbd₁ with ⟨x, hxc₁, hxbd⟩
    have hxc₂_bd : x ∈ c₂ ∩ bd S := h_eq ▸ ⟨hxc₁, hxbd⟩
    exact Γ.cell_eq_of_mem hc₁_C hc₂_C hxc₁ hxc₂_bd.1
  let r' := M.ncard
  have hr'_eq : r' = 𝒜₂.ncard := hM_inj.ncard_image
  have hr'_le_r : r' ≤ r := hr'_eq ▸ h𝒜₂_card_le
  obtain ⟨F_star, hF_supp, hF_disj, hF_cov, hF_iff⟩ :=
    exists_supports_of_removed_spaces hS hge2_Γ' hM_sub hM_cuff
  -- Define μ and q_vec
  let μ : BoundaryUnit S → Hypergraph α β := fun x =>
    match x with
    | .vertex u => if u ∈ Γ.N ∩ bd S then α_vert u else ⊥
    | .space s =>
        if hs : ∃ c ∈ Γ.C, (c ∩ bd S).Nonempty ∧ c ∩ bd S = s then
          α_cell (Classical.choose hs)
        else ⊥
  have hμ_vert : ∀ u, μ (.vertex u) = if u ∈ Γ.N ∩ bd S then α_vert u else ⊥ := fun _ => rfl
  have hμ_space_def : ∀ s, μ (.space s) =
      if hs : ∃ c ∈ Γ.C, (c ∩ bd S).Nonempty ∧ c ∩ bd S = s then
        α_cell (Classical.choose hs)
      else ⊥ := fun _ => rfl
  have hμ_border_cell : ∀ c ∈ Γ.C, (c ∩ bd S).Nonempty → μ (.space (c ∩ bd S)) = α_cell c := by
    intro c hc hbd
    have hs_ex : ∃ c' ∈ Γ.C, (c' ∩ bd S).Nonempty ∧ c' ∩ bd S = c ∩ bd S := ⟨c, hc, hbd, rfl⟩
    simp only [hμ_space_def, hs_ex, ↓reduceDIte]
    obtain ⟨hc', _, hc'_eq⟩ := Classical.choose_spec hs_ex
    rcases hbd with ⟨x, hxc, hxbd⟩
    have hxc'_bd : x ∈ Classical.choose hs_ex ∩ bd S := hc'_eq.symm ▸ ⟨hxc, hxbd⟩
    rw [Γ.cell_eq_of_mem hc' hc hxc'_bd.1 hxc]
  have h_cell_in_M_iff : ∀ c ∈ Γ.C, (c ∩ bd S).Nonempty → (c ∩ bd S ∈ M ↔ c ∈ 𝒜₂) := by
    intro c hc hbd
    constructor
    · rintro ⟨c', hc'₂, h_eq⟩
      change c' ∩ bd S = c ∩ bd S at h_eq
      obtain ⟨hc', _⟩ := h𝒜₂_border c' hc'₂
      rcases hbd with ⟨x, hxc, hxbd⟩
      have hxc'_bd : x ∈ c' ∩ bd S := h_eq.symm ▸ ⟨hxc, hxbd⟩
      rwa [Γ.cell_eq_of_mem hc hc' hxc hxc'_bd.1]
    · intro hc₂
      exact ⟨c, hc₂, rfl⟩
  -- For each j : Fin r', choose the unique cuff C_of_j containing F_star j
  have hF_cuff : ∀ j : Fin r', ∃ C ∈ cuffs S, F_star j ⊆ C := by
    intro j
    rcases hF_supp j with ⟨a, b, hends⟩
    exact exists_cuff_of_supportHasEnds hends
  let C_of_j : Fin r' → Set S := fun j => Classical.choose (hF_cuff j)
  have hC_of_j_spec : ∀ j : Fin r', C_of_j j ∈ cuffs S ∧ F_star j ⊆ C_of_j j :=
    fun j => Classical.choose_spec (hF_cuff j)
  let q_vec : Fin r' → ℕ := fun j => q_cuff (C_of_j j)
  -- Helper: (α_cell c).vertexSet ∩ Γ'_sub.vertexSet = ιN '' tilde c for every border cell c
  have h_border_inter_Γ'_sub : ∀ c ∈ Γ.C, (c ∩ bd S).Nonempty →
      (α_cell c).vertexSet ∩ Γ'_sub.vertexSet = ιN '' tilde c := by
    intro c hc hbd
    refine Subset.antisymm ?_ ?_
    · rintro w ⟨hwc, hw_N | hw_ℐ⟩
      · rw [← hport.r2_cell_inter c hc]
        exact ⟨hwc, hw_N⟩
      · rw [mem_iUnion₂] at hw_ℐ
        rcases hw_ℐ with ⟨c', ⟨hc', hc'_int, _⟩, hwc'⟩
        have hne : c ≠ c' := by
          rintro rfl
          rcases hbd with ⟨x, hxc, hxbd⟩
          exact Set.disjoint_left.mp hc'_int.2 hxc hxbd
        have hno_cuff : ∀ C ∈ cuffs S, ¬ ((c ∩ C).Nonempty ∧ (c' ∩ C).Nonempty) := by
          intro C hC ⟨_, ⟨x, hxc', hxC⟩⟩
          have hxbd : x ∈ bd S := by rw [← sUnion_cuffs (S := S)]; exact ⟨C, hC, hxC⟩
          exact Set.disjoint_left.mp hc'_int.2 hxc' hxbd
        have hw_inter : w ∈ (α_cell c ∩ α_cell c').vertexSet := ⟨hwc, hwc'⟩
        rw [hport.r7_inter c hc c' hc' hne hno_cuff] at hw_inter
        exact image_mono inter_subset_left hw_inter
    · intro w hwt
      exact ⟨tilde_image_subset_cell_vertexSet hport hc hwt,
        Or.inl (image_mono (Γ.tilde_subset_N hc) hwt)⟩
  -- Helper: (α_vert u).vertexSet ∩ Γ'_sub.vertexSet = {ιV' u} for u ∈ Γ.N ∩ bd S
  have h_vert_inter_Γ'_sub : ∀ u ∈ Γ.N ∩ bd S,
      (α_vert u).vertexSet ∩ Γ'_sub.vertexSet = {ιV' u} := by
    intro u hu
    rw [hιV'_N u hu.1]
    have h4 := (hport.r4_vert u hu).2.2
    refine Subset.antisymm ?_ ?_
    · rintro w ⟨hwu, hw_N | hw_ℐ⟩
      · rw [← h4]; exact ⟨hwu, hw_N⟩
      · rw [mem_iUnion₂] at hw_ℐ
        rcases hw_ℐ with ⟨c', ⟨hc', hc'_int, _⟩, hwc'⟩
        have hubd := hu.2
        rw [← sUnion_cuffs (S := S)] at hubd
        rcases hubd with ⟨C, hC, huC⟩
        obtain ⟨c, hc, _, hbd, _, hu_le⟩ := exists_border_cell_of_mem_N_cuff hport hC ⟨hu.1, huC⟩
        have hwc : w ∈ (α_cell c).vertexSet := hu_le.1 hwu
        have hw_tilde : w ∈ ιN '' tilde c :=
          (h_border_inter_Γ'_sub c hc hbd) ▸ ⟨hwc, Or.inr (mem_biUnion ⟨hc', hc'_int, ‹_›⟩ hwc')⟩
        have hw_N : w ∈ ιN '' Γ.N := image_mono (Γ.tilde_subset_N hc) hw_tilde
        rw [← h4]
        exact ⟨hwu, hw_N⟩
    · rintro w rfl
      exact ⟨ιN_mem_vert_of_mem_N_bd hport hu, Or.inl ⟨u, hu.1, rfl⟩⟩
  -- Helper: α_cell c ≤ G' for c ∈ Γ.C \ (𝒜₁ ∪ 𝒜₂)
  have h_cell_le_G' : ∀ c ∈ Γ.C \ (𝒜₁ ∪ 𝒜₂), α_cell c ≤ G' := by
    intro c hc
    have hle_G := hport.r2_cell_le c hc.1
    refine ⟨fun w hwc => Or.inr (mem_biUnion hc hwc),
      fun e hec => mem_biUnion hc hec,
      fun e hec => ?_⟩
    rw [← hle_G.3 e hec]
    ext w
    exact ⟨fun h => h.2, fun h => ⟨mem_biUnion hc hec, h⟩⟩
  -- Helper: α_vert u ≤ G' for u ∈ Γ.N ∩ bd S
  have h_vert_le_G' : ∀ u ∈ Γ.N ∩ bd S, α_vert u ≤ G' := by
    intro u hu
    have h4 := hport.r4_vert u hu
    refine ⟨fun w hwu => Or.inl (Or.inr (mem_biUnion hu hwu)),
      fun e he => (h4.2.1 ▸ he).elim,
      fun e he => (h4.2.1 ▸ he).elim⟩
  -- Claim (1): (Γ', Γ'_sub, ιV', ιE', r', F_star, μ, q_vec) is a pseudo-presentation of G'
  have hpp : IsPseudoPresentation G' Γ' Γ'_sub ιV' ιE' r' F_star μ q_vec := by
    refine
      { is_surface := hS
        is_connected_surface := inferInstance
        is_proper_drawing := hΓ'_proper
        cuff_vertices_ge_two := hge2_Γ'
        drawing_subgraph := hΓ'_sub_le
        drawing_iso := hiso
        supports_isSupport := hF_supp
        supports_disjoint := hF_disj
        bd_vertices_covered := hF_cov
        q_pos := fun j => hport.r5_cuff_pos (C_of_j j) (hC_of_j_spec j).1
        μ_vertex := ?_
        μ_space := ?_
        p1_union_V := ?_
        p1_union_E := ?_
        p1_edge_disjoint_drawing := ?_
        p1_edge_disjoint_spaces := ?_
        p1_diff_cuff_disjoint := ?_
        p2_space := ?_
        p3_order := ?_
        p4_inter_null := ?_ }
    · intro j u hu
      have hu_F_bd : F_star j ⊆ bd S := by
        refine (hC_of_j_spec j).2.trans ?_
        intro z hz; rw [← sUnion_cuffs (S := S)]; exact ⟨C_of_j j, (hC_of_j_spec j).1, hz⟩
      have hu_Nbd : u ∈ Γ.N ∩ bd S := hV'_bd ▸ ⟨hu.1, hu_F_bd hu.2⟩
      have hu_NC : u ∈ Γ.N ∩ C_of_j j := ⟨hu_Nbd.1, (hC_of_j_spec j).2 hu.2⟩
      simp only [hμ_vert, hu_Nbd, ↓reduceIte]
      exact ⟨h_vert_le_G' u hu_Nbd, (hport.r4_vert u hu_Nbd).2.1,
        hport.r5_cuff_card (C_of_j j) (hC_of_j_spec j).1 u hu_NC,
        h_vert_inter_Γ'_sub u hu_Nbd⟩
    · intro j s hs hsF
      obtain ⟨c, ⟨hc, hbd, rfl⟩, _⟩ := exists_border_cell_of_mem_drawingSpaces hS hV'_bd hs
      rw [hμ_border_cell c hc hbd]
      have hs_not_M : c ∩ bd S ∉ M := (hF_iff (c ∩ bd S) hs).mp ⟨j, hsF⟩
      have hc_not₂ : c ∉ 𝒜₂ := (h_cell_in_M_iff c hc hbd).not.mp hs_not_M
      have hc_not₁ : c ∉ 𝒜₁ := by
        intro hc₁
        rcases hbd with ⟨x, hxc, hxbd⟩
        exact Set.disjoint_left.mp hc₁.2.1.2 hxc hxbd
      exact h_cell_le_G' c ⟨hc, fun h => h.elim hc_not₁ hc_not₂⟩
    · refine Subset.antisymm ?_ ?_
      · rintro w ((hw_N | hw_u) | hw_c)
        · exact Or.inl (Or.inl hw_N)
        · rw [mem_iUnion₂] at hw_u
          rcases hw_u with ⟨u, hu, hwu⟩
          have hu_V' : u ∈ Γ'.V ∩ bd S := hV'_bd.symm ▸ hu
          have hu_cov := hF_cov hu_V'
          rw [mem_iUnion] at hu_cov
          rcases hu_cov with ⟨j, huj⟩
          right
          rw [mem_iUnion]
          refine ⟨j, Or.inl (Or.inr (mem_biUnion hu hwu)), Or.inr ?_⟩
          rw [mem_iUnion₂]
          refine ⟨u, ⟨hu_V'.1, huj⟩, ?_⟩
          simp only [hμ_vert, hu, ↓reduceIte]
          exact hwu
        · rw [mem_iUnion₂] at hw_c
          rcases hw_c with ⟨c, ⟨hc, hc_not⟩, hwc⟩
          by_cases hbd : (c ∩ bd S).Nonempty
          · have hc_not₂ : c ∉ 𝒜₂ := fun h => hc_not (Or.inr h)
            have hs_space : c ∩ bd S ∈ drawingSpaces Γ' :=
              (border_cell_space_mem_drawingSpaces hS hV'_bd hc hbd).1
            have hs_not_M : c ∩ bd S ∉ M := (h_cell_in_M_iff c hc hbd).not.mpr hc_not₂
            obtain ⟨j, hsF⟩ := (hF_iff (c ∩ bd S) hs_space).mpr hs_not_M
            right
            rw [mem_iUnion]
            refine ⟨j, Or.inr (mem_biUnion ⟨hc, hc_not⟩ hwc), Or.inl ?_⟩
            rw [mem_iUnion₂]
            refine ⟨c ∩ bd S, ⟨hs_space, hsF⟩, ?_⟩
            rwa [hμ_border_cell c hc hbd]
          · have hc_int : IsInternalCell Γ c :=
              ⟨hc, disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hbd)⟩
            have hc_ℐ : c ∈ ℐ := ⟨hc, hc_int, fun h => hc_not (Or.inl h)⟩
            exact Or.inl (Or.inr (mem_biUnion hc_ℐ hwc))
      · rintro w (hw_Γ' | hw_supp)
        · exact hΓ'_sub_le.1 hw_Γ'
        · rw [mem_iUnion] at hw_supp
          rcases hw_supp with ⟨j, hwG', _⟩
          exact hwG'
    · refine Subset.antisymm ?_ ?_
      · rintro e he
        rw [mem_iUnion₂] at he
        rcases he with ⟨c, ⟨hc, hc_not⟩, hec⟩
        by_cases hbd : (c ∩ bd S).Nonempty
        · have hc_not₂ : c ∉ 𝒜₂ := fun h => hc_not (Or.inr h)
          have hs_space : c ∩ bd S ∈ drawingSpaces Γ' :=
            (border_cell_space_mem_drawingSpaces hS hV'_bd hc hbd).1
          have hs_not_M : c ∩ bd S ∉ M := (h_cell_in_M_iff c hc hbd).not.mpr hc_not₂
          obtain ⟨j, hsF⟩ := (hF_iff (c ∩ bd S) hs_space).mpr hs_not_M
          right
          rw [mem_iUnion]
          refine ⟨j, mem_biUnion ⟨hc, hc_not⟩ hec, Or.inl ?_⟩
          rw [mem_iUnion₂]
          refine ⟨c ∩ bd S, ⟨hs_space, hsF⟩, ?_⟩
          rwa [hμ_border_cell c hc hbd]
        · have hc_int : IsInternalCell Γ c :=
            ⟨hc, disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hbd)⟩
          have hc_ℐ : c ∈ ℐ := ⟨hc, hc_int, fun h => hc_not (Or.inl h)⟩
          exact Or.inl (mem_biUnion hc_ℐ hec)
      · rintro e (he_Γ' | he_supp)
        · exact hΓ'_sub_le.2 he_Γ'
        · rw [mem_iUnion] at he_supp
          rcases he_supp with ⟨j, heG', _⟩
          exact heG'
    · intro j s hs _
      obtain ⟨c, ⟨hc, hbd, rfl⟩, _⟩ := exists_border_cell_of_mem_drawingSpaces hS hV'_bd hs
      rw [hμ_border_cell c hc hbd, disjoint_iff_inter_eq_empty]
      ext e
      simp only [Γ'_sub, Γ'_sub_E, mem_inter_iff, mem_iUnion₂, mem_empty_iff_false, iff_false, not_and]
      rintro ⟨c', ⟨hc', hc'_int, _⟩, hec'⟩ hec
      have hne : c' ≠ c := by
        rintro rfl
        rcases hbd with ⟨x, hxc, hxbd⟩
        exact Set.disjoint_left.mp hc'_int.2 hxc hxbd
      exact Set.disjoint_left.mp (hport.r3_edge_disjoint c' hc' c hc hne) hec' hec
    · intro s₁ hs₁ s₂ hs₂ _ _ hne
      obtain ⟨c₁, ⟨hc₁, hbd₁, rfl⟩, _⟩ := exists_border_cell_of_mem_drawingSpaces hS hV'_bd hs₁
      obtain ⟨c₂, ⟨hc₂, hbd₂, rfl⟩, _⟩ := exists_border_cell_of_mem_drawingSpaces hS hV'_bd hs₂
      rw [hμ_border_cell c₁ hc₁ hbd₁, hμ_border_cell c₂ hc₂ hbd₂]
      exact hport.r3_edge_disjoint c₁ hc₁ c₂ hc₂ (fun h => hne (h ▸ rfl))
    · intro C₁ hC₁ C₂ hC₂ hC_ne x₁ x₂ hx₁ hx₂
      -- Show that for i = 1, 2, either μ xᵢ = ⊥ or μ xᵢ ≤ α_cell cᵢ for a border cell cᵢ on Cᵢ
      have h_unit_cell : ∀ (C : Set S) (hC : C ∈ cuffs S) (x : BoundaryUnit S),
          x.InSet C → μ x = ⊥ ∨ ∃ c ∈ Γ.C, (c ∩ C).Nonempty ∧ (c ∩ bd S).Nonempty ∧ μ x ≤ α_cell c := by
        intro C hC x hx
        cases x with
        | space s =>
          by_cases hs_ex : ∃ c ∈ Γ.C, (c ∩ bd S).Nonempty ∧ c ∩ bd S = s
          · right
            let c := Classical.choose hs_ex
            obtain ⟨hc, hbd, hc_eq⟩ := Classical.choose_spec hs_ex
            have hμ_eq : μ (.space s) = α_cell c := by simp only [hμ_space_def, hs_ex, ↓reduceDIte, c]
            rcases hbd with ⟨z, hzc, hzbd⟩
            exact ⟨c, hc, ⟨z, hzc, hx (hc_eq ▸ ⟨hzc, hzbd⟩)⟩, ⟨z, hzc, hzbd⟩, hμ_eq ▸ le_rfl⟩
          · left
            simp only [hμ_space_def, hs_ex, ↓reduceDIte]
        | vertex u =>
          by_cases hu_N : u ∈ Γ.N ∩ bd S
          · right
            obtain ⟨c, hc, hcC, hbd, _, hu_le⟩ :=
              exists_border_cell_of_mem_N_cuff hport hC ⟨hu_N.1, hx⟩
            simp only [hμ_vert, hu_N, ↓reduceIte]
            exact ⟨c, hc, hcC, hbd, hu_le⟩
          · left
            simp only [hμ_vert, hu_N, ↓reduceIte]
      rcases h_unit_cell C₁ hC₁ x₁ hx₁ with hbot₁ | ⟨c₁, hc₁, hc₁C₁, hbd₁, hle₁⟩
      · rw [hbot₁]; exact disjoint_bot_left
      · rcases h_unit_cell C₂ hC₂ x₂ hx₂ with hbot₂ | ⟨c₂, hc₂, hc₂C₂, hbd₂, hle₂⟩
        · rw [hbot₂]; exact disjoint_bot_right
        · have hc₁_sub : c₁ ∩ bd S ⊆ C₁ :=
            (inter_subset_inter_left (bd S) subset_closure).trans (Γ.border_cell_subset_cuff hc₁ hC₁ hc₁C₁).1
          have hc₂_sub : c₂ ∩ bd S ⊆ C₂ :=
            (inter_subset_inter_left (bd S) subset_closure).trans (Γ.border_cell_subset_cuff hc₂ hC₂ hc₂C₂).1
          have htilde₁_C₁ : tilde c₁ ⊆ Γ.N ∩ C₁ := (Γ.border_cell_subset_cuff hc₁ hC₁ hc₁C₁).2.2.2.1
          have htilde₂_C₂ : tilde c₂ ⊆ Γ.N ∩ C₂ := (Γ.border_cell_subset_cuff hc₂ hC₂ hc₂C₂).2.2.2.1
          have hc_ne : c₁ ≠ c₂ := by
            rintro rfl
            rcases hc₁C₁ with ⟨z, hzc₁, hzC₁⟩
            rcases hc₂C₂ with ⟨w, hwc₁, hwC₂⟩
            have hC₁_sub_bd : C₁ ⊆ bd S := fun y hy => by rw [← sUnion_cuffs (S := S)]; exact ⟨C₁, hC₁, hy⟩
            have hC₂_sub_bd : C₂ ⊆ bd S := fun y hy => by rw [← sUnion_cuffs (S := S)]; exact ⟨C₂, hC₂, hy⟩
            have hw_C₁ : w ∈ C₁ := hc₁_sub ⟨hwc₁, hC₂_sub_bd hwC₂⟩
            exact Set.disjoint_left.mp (cuffs_disjoint hC₁ hC₂ hC_ne) hw_C₁ hwC₂
          have hno_same_cuff : ∀ C ∈ cuffs S, ¬ ((c₁ ∩ C).Nonempty ∧ (c₂ ∩ C).Nonempty) := by
            intro C hC ⟨⟨z₁, hzc₁, hz₁C⟩, ⟨z₂, hzc₂, hz₂C⟩⟩
            have hC_sub_bd : C ⊆ bd S := fun y hy => by rw [← sUnion_cuffs (S := S)]; exact ⟨C, hC, hy⟩
            have hz₁_C₁ : z₁ ∈ C₁ := hc₁_sub ⟨hzc₁, hC_sub_bd hz₁C⟩
            have hz₂_C₂ : z₂ ∈ C₂ := hc₂_sub ⟨hzc₂, hC_sub_bd hz₂C⟩
            have hC_eq₁ : C = C₁ := by
              by_contra hne₁
              exact Set.disjoint_left.mp (cuffs_disjoint hC hC₁ hne₁) hz₁C hz₁_C₁
            have hC_eq₂ : C = C₂ := by
              by_contra hne₂
              exact Set.disjoint_left.mp (cuffs_disjoint hC hC₂ hne₂) hz₂C hz₂_C₂
            exact hC_ne (hC_eq₁.symm.trans hC_eq₂)
          have htilde_disj : tilde c₁ ∩ tilde c₂ = ∅ := by
            rw [← disjoint_iff_inter_eq_empty]
            exact (cuffs_disjoint hC₁ hC₂ hC_ne).mono
              (htilde₁_C₁.trans inter_subset_right) (htilde₂_C₂.trans inter_subset_right)
          have hinter_empty : (α_cell c₁ ∩ α_cell c₂).vertexSet = ∅ := by
            rw [hport.r7_inter c₁ hc₁ c₂ hc₂ hc_ne hno_same_cuff, htilde_disj, image_empty]
          refine Disjoint.mono hle₁.1 hle₂.1 ?_
          rw [disjoint_iff_inter_eq_empty]
          exact hinter_empty
    · intro j s hs u₁ u₂ hsF hs_ends
      obtain ⟨c, ⟨hc, hbd, rfl⟩, _⟩ := exists_border_cell_of_mem_drawingSpaces hS hV'_bd hs
      rw [hμ_border_cell c hc hbd]
      obtain ⟨u₁', u₂', hu₁₂', htilde⟩ := Γ.border_cell_exists_ends hc hbd
      have hs_ends' := (border_cell_space_mem_drawingSpaces hS hV'_bd hc hbd).2 u₁' u₂' hu₁₂' htilde.1
      have hpair := ends_pair_eq_of_spaceHasEnds hs_ends hs_ends'
      have htilde_u₁u₂ : tilde c = {u₁, u₂} := by rw [htilde.1, ← hpair]
      have hu₁_Nbd : u₁ ∈ Γ.N ∩ bd S := hV'_bd ▸ hs_ends.2.1
      have hu₂_Nbd : u₂ ∈ Γ.N ∩ bd S := hV'_bd ▸ hs_ends.2.2.1
      simp only [hμ_vert, hu₁_Nbd, hu₂_Nbd, ↓reduceIte]
      have hs_not_M : c ∩ bd S ∉ M := (hF_iff (c ∩ bd S) hs).mp ⟨j, hsF⟩
      have hc_not₂ : c ∉ 𝒜₂ := (h_cell_in_M_iff c hc hbd).not.mp hs_not_M
      have hc_not_𝒰 : c ∉ 𝒰 := fun h => hc_not₂ (Or.inl h)
      have h_linked : HasDisjointPaths (α_cell c).skeleton (α_vert u₁).vertexSet (α_vert u₂).vertexSet
          (α_vert u₁).vertexSet.ncard := by
        by_contra hnot_p
        exact hc_not_𝒰 ⟨hc, hbd, fun h => hnot_p (h u₁ u₂ hs_ends.2.2.2.1 htilde_u₁u₂)⟩
      have hu₁_C : u₁ ∈ C_of_j j := by
        have hcl_sub : closure (c ∩ bd S) ⊆ C_of_j j :=
          closure_minimal (hsF.trans (hC_of_j_spec j).2) (isClosed_cuff_univ hS (hC_of_j_spec j).1)
        exact hcl_sub (hs_ends.2.2.2.2.2.symm ▸ Or.inr (Or.inl rfl))
      have hcard_u₁ : (α_vert u₁).vertexSet.ncard = q_vec j :=
        hport.r5_cuff_card (C_of_j j) (hC_of_j_spec j).1 u₁ ⟨hu₁_Nbd.1, hu₁_C⟩
      have h6 := hport.r6_border c hc hbd u₁ u₂ hs_ends.2.2.2.1 htilde_u₁u₂
      refine ⟨?_, h6.1, h6.2.1, hcard_u₁ ▸ h_linked⟩
      rw [h_border_inter_Γ'_sub c hc hbd, htilde_u₁u₂, image_pair,
        hιV'_N u₁ hu₁_Nbd.1, hιV'_N u₂ hu₂_Nbd.1]
    · intro C hC x₁ x₂ u₁ hu₁ u₂ hu₂ hx₁C hx₂C hord
      have hC_sub_bd : C ⊆ bd S := fun z hz => by rw [← sUnion_cuffs (S := S)]; exact ⟨C, hC, hz⟩
      have hu₁_Nbd : u₁ ∈ Γ.N ∩ bd S := hV'_bd ▸ ⟨hu₁.2, hC_sub_bd hu₁.1⟩
      have hu₂_Nbd : u₂ ∈ Γ.N ∩ bd S := hV'_bd ▸ ⟨hu₂.2, hC_sub_bd hu₂.1⟩
      have hu₁_NC : u₁ ∈ Γ.N ∩ C := ⟨hu₁_Nbd.1, hu₁.1⟩
      have hu₂_NC : u₂ ∈ Γ.N ∩ C := ⟨hu₂_Nbd.1, hu₂.1⟩
      have hu₁_V'C : u₁ ∈ Γ'.V ∩ C := ⟨hu₁.2, hu₁.1⟩
      have hu₂_V'C : u₂ ∈ Γ'.V ∩ C := ⟨hu₂.2, hu₂.1⟩
      have hμ_u₁_empty : (μ (.vertex u₁)).edgeSet = ∅ := by
        simp only [hμ_vert, hu₁_Nbd, ↓reduceIte]; exact (hport.r4_vert u₁ hu₁_Nbd).2.1
      have hμ_u₂_empty : (μ (.vertex u₂)).edgeSet = ∅ := by
        simp only [hμ_vert, hu₂_Nbd, ↓reduceIte]; exact (hport.r4_vert u₂ hu₂_Nbd).2.1
      by_cases hx₁_u₂ : x₁ = .vertex u₂
      · subst hx₁_u₂
        refine ⟨fun w hw => Or.inr hw.1, fun e he => (hμ_u₂_empty ▸ he.1).elim,
          fun e he => (hμ_u₂_empty ▸ he.1).elim⟩
      by_cases hx₂_u₁ : x₂ = .vertex u₁
      · subst hx₂_u₁
        refine ⟨fun w hw => Or.inl hw.2, fun e he => (hμ_u₁_empty ▸ he.2).elim,
          fun e he => (hμ_u₁_empty ▸ he.2).elim⟩
      rcases hord with ⟨f, a₁, b₁, t₁, a₂, b₂, t₂, ha₁b₁, hb₁t₁, ht₁a₂, ha₂b₂, hb₂t₂, ht₂_le,
        ht₁_eq, ht₂_eq, hx₁_ne, hx₁_sub, hx₂_ne, hx₂_sub⟩
      rcases exists_border_cell_for_unit_in_cuff_arc hport hV'_bd hge2_Γ' hμ_vert hμ_space_def
          hC f ha₁b₁ hb₁t₁ (by linarith) (ht₁_eq.symm ▸ hu₁_V'C) hx₁C hx₁_ne hx₁_sub with
        hbot₁ | hx₁_u₁ | ⟨c₁, a₁', b₁', hc₁, hc₁C, hle₁, ha₁_le, ha₁'b₁', hb₁'t₁, hcl₁_ne, hcl₁_sub⟩
      · rw [hbot₁]
        refine ⟨fun w hw => (hw.1).elim, fun e he => (he.1).elim, fun e he => (he.1).elim⟩
      · rw [ht₁_eq] at hx₁_u₁
        subst hx₁_u₁
        refine ⟨fun w hw => Or.inl hw.1, fun e he => (hμ_u₁_empty ▸ he.1).elim,
          fun e he => (hμ_u₁_empty ▸ he.1).elim⟩
      · rcases exists_border_cell_for_unit_in_cuff_arc hport hV'_bd hge2_Γ' hμ_vert hμ_space_def
            hC f ha₂b₂ hb₂t₂ (by linarith) (ht₂_eq.symm ▸ hu₂_V'C) hx₂C hx₂_ne hx₂_sub with
          hbot₂ | hx₂_u₂ | ⟨c₂, a₂', b₂', hc₂, hc₂C, hle₂, ha₂_le, ha₂'b₂', hb₂'t₂, hcl₂_ne, hcl₂_sub⟩
        · rw [hbot₂]
          refine ⟨fun w hw => (hw.2).elim, fun e he => (he.2).elim, fun e he => (he.2).elim⟩
        · rw [ht₂_eq] at hx₂_u₂
          subst hx₂_u₂
          refine ⟨fun w hw => Or.inr hw.2, fun e he => (hμ_u₂_empty ▸ he.2).elim,
            fun e he => (hμ_u₂_empty ▸ he.2).elim⟩
        · have hord_cells : InCuffOrder C c₁ u₁ c₂ u₂ :=
            ⟨f, a₁', b₁', t₁, a₂', b₂', t₂,
              ha₁'b₁', hb₁'t₁, ht₁a₂.trans ha₂_le, ha₂'b₂', hb₂'t₂, ht₂_le.trans (by linarith),
              ht₁_eq, ht₂_eq, hcl₁_ne, hcl₁_sub, hcl₂_ne, hcl₂_sub⟩
          have hr8 := hport.r8_order C hC c₁ hc₁ c₂ hc₂ hc₁C hc₂C u₁ hu₁_NC u₂ hu₂_NC hord_cells
          simp only [hμ_vert, hu₁_Nbd, hu₂_Nbd, ↓reduceIte]
          refine ⟨fun w hw => hr8.1 ⟨hle₁.1 hw.1, hle₂.1 hw.2⟩,
            fun e he => hr8.2 ⟨hle₁.2 he.1, hle₂.2 he.2⟩,
            fun e he => ?_⟩
          have he_False : False := by
            have := hr8.2 ⟨hle₁.2 he.1, hle₂.2 he.2⟩
            simp only [GM10.union_edgeSet, (hport.r4_vert u₁ hu₁_Nbd).2.1,
              (hport.r4_vert u₂ hu₂_Nbd).2.1, Set.union_self, mem_empty_iff_false] at this
          exact he_False.elim
    · intro C hC
      have hC_sub_bd : C ⊆ bd S := fun z hz => by rw [← sUnion_cuffs (S := S)]; exact ⟨C, hC, hz⟩
      have h_eq_NC : Γ'.V ∩ C = Γ.N ∩ C := by
        calc Γ'.V ∩ C
            = (Γ'.V ∩ bd S) ∩ C := by rw [Set.inter_assoc, inter_eq_self_of_subset_right hC_sub_bd]
          _ = (Γ.N ∩ bd S) ∩ C := by rw [hV'_bd]
          _ = Γ.N ∩ C := by rw [Set.inter_assoc, inter_eq_self_of_subset_right hC_sub_bd]
      rw [h_eq_NC, ← hport.r10_null C hC]
      ext w
      simp only [mem_iInter₂]
      refine forall₂_congr fun u hu => ?_
      have hu_Nbd : u ∈ Γ.N ∩ bd S := ⟨hu.1, hC_sub_bd hu.2⟩
      simp only [hμ_vert, hu_Nbd, ↓reduceIte]
  have hpp_depth : PseudoPresentationHasDepthLe G' Γ' Γ'_sub ιV' ιE' r' F_star μ q := by
    refine ⟨q_vec, hpp, fun j => hq_cuff (C_of_j j) (hC_of_j_spec j).1, fun hr'0 => ?_⟩
    by_contra hbd_ne
    have hbd_nonempty : (bd S).Nonempty := nonempty_iff_ne_empty.mpr hbd_ne
    rcases hbd_nonempty with ⟨z, hzbd⟩
    rw [← sUnion_cuffs (S := S)] at hzbd
    rcases hzbd with ⟨C, hC, _⟩
    obtain ⟨s, hsM, _⟩ := hM_cuff C hC
    have hM_fin : M.Finite := (drawingSpaces_finite hS hge2_Γ').subset hM_sub
    have hpos : 0 < M.ncard := ncard_pos hM_fin |>.mpr ⟨s, hsM⟩
    omega
  -- Claim (2): G' = cellComplInterSubgraph hport (𝒜₁ ∪ 𝒜₂) h𝒜_sub
  have h𝒜_sub : 𝒜₁ ∪ 𝒜₂ ⊆ Γ.C := union_subset h𝒜₁_sub h𝒜₂_sub
  let A₀ := cellUnionSubgraph hport (𝒜₁ ∪ 𝒜₂) h𝒜_sub
  have hG'_eq_inter : G' = cellComplInterSubgraph hport (𝒜₁ ∪ 𝒜₂) h𝒜_sub := by
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hG'_le
      (cellComplInterSubgraph_le hport h𝒜_sub) ?_ ?_
    · ext w
      simp only [G', G'_V, cellComplInterSubgraph, mem_inter_iff, mem_iInter₂]
      constructor
      · intro hwG'
        refine ⟨hG'_le.1 hwG', fun c hc => ?_⟩
        by_cases hwc : w ∈ (α_cell c).vertexSet
        · rcases hc with hc₁ | hc₂
          · rw [cellCompl_eq_internal hport hc₁.2.1]
            right
            rcases hwG' with (hw_N | hw_u) | hw_c'
            · rw [← hport.r2_cell_inter c hc₁.1]
              exact ⟨hwc, hw_N⟩
            · rw [mem_iUnion₂] at hw_u
              rcases hw_u with ⟨u, hu, hwu⟩
              have hu_bd := hu.2
              rw [← sUnion_cuffs (S := S)] at hu_bd
              rcases hu_bd with ⟨C, hC, huC⟩
              obtain ⟨c_u, hc_u, _, hbd_u, _, hu_le⟩ :=
                exists_border_cell_of_mem_N_cuff hport hC ⟨hu.1, huC⟩
              have hwc_u : w ∈ (α_cell c_u).vertexSet := hu_le.1 hwu
              have hne : c ≠ c_u := by
                rintro rfl
                rcases hbd_u with ⟨x, hxc, hxbd⟩
                exact Set.disjoint_left.mp hc₁.2.1.2 hxc hxbd
              have hno_cuff : ∀ C' ∈ cuffs S, ¬ ((c ∩ C').Nonempty ∧ (c_u ∩ C').Nonempty) := by
                intro C' hC' ⟨⟨x, hxc, hxC'⟩, _⟩
                have hxbd : x ∈ bd S := by rw [← sUnion_cuffs (S := S)]; exact ⟨C', hC', hxC'⟩
                exact Set.disjoint_left.mp hc₁.2.1.2 hxc hxbd
              have hw_inter : w ∈ (α_cell c ∩ α_cell c_u).vertexSet := ⟨hwc, hwc_u⟩
              rw [hport.r7_inter c hc₁.1 c_u hc_u hne hno_cuff] at hw_inter
              exact image_mono inter_subset_left hw_inter
            · rw [mem_iUnion₂] at hw_c'
              rcases hw_c' with ⟨c', ⟨hc', hc'_not⟩, hwc'⟩
              have hne : c ≠ c' := fun h => hc'_not (h ▸ Or.inl hc₁)
              have hno_cuff : ∀ C' ∈ cuffs S, ¬ ((c ∩ C').Nonempty ∧ (c' ∩ C').Nonempty) := by
                intro C' hC' ⟨⟨x, hxc, hxC'⟩, _⟩
                have hxbd : x ∈ bd S := by rw [← sUnion_cuffs (S := S)]; exact ⟨C', hC', hxC'⟩
                exact Set.disjoint_left.mp hc₁.2.1.2 hxc hxbd
              have hw_inter : w ∈ (α_cell c ∩ α_cell c').vertexSet := ⟨hwc, hwc'⟩
              rw [hport.r7_inter c hc₁.1 c' hc' hne hno_cuff] at hw_inter
              exact image_mono inter_subset_left hw_inter
          · obtain ⟨hc_C, hbd⟩ := h𝒜₂_border c hc₂
            rw [cellCompl_eq_border hport hc_C hbd]
            right
            rcases hwG' with (hw_N | hw_u) | hw_c'
            · have hw_tilde : w ∈ ιN '' tilde c := by
                rw [← hport.r2_cell_inter c hc_C]; exact ⟨hwc, hw_N⟩
              rcases hw_tilde with ⟨u, hu_c, rfl⟩
              exact mem_biUnion hu_c
                (ιN_mem_vert_of_mem_N_bd hport (tilde_subset_N_bd_of_border_cell hc_C hbd hu_c))
            · rw [mem_iUnion₂] at hw_u
              rcases hw_u with ⟨u, hu, hwu⟩
              have hu_bd := hu.2
              rw [← sUnion_cuffs (S := S)] at hu_bd
              rcases hu_bd with ⟨C, hC, huC⟩
              obtain ⟨c_u, hc_u, _, hbd_u, hu_tilde_u, hu_le⟩ :=
                exists_border_cell_of_mem_N_cuff hport hC ⟨hu.1, huC⟩
              by_cases h_eq : c = c_u
              · subst h_eq
                exact mem_biUnion hu_tilde_u hwu
              · exact cell_inter_other_cell_vertex_subset_border hport hc_C hbd hc_u h_eq
                  ⟨hwc, hu_le.1 hwu⟩
            · rw [mem_iUnion₂] at hw_c'
              rcases hw_c' with ⟨c', ⟨hc', hc'_not⟩, hwc'⟩
              have hne : c ≠ c' := fun h => hc'_not (h ▸ Or.inr hc₂)
              exact cell_inter_other_cell_vertex_subset_border hport hc_C hbd hc' hne ⟨hwc, hwc'⟩
        · by_cases hbd : (c ∩ bd S).Nonempty
          · rw [cellCompl_eq_border hport (h𝒜_sub hc) hbd]
            exact Or.inl ⟨hG'_le.1 hwG', hwc⟩
          · have hc_int : IsInternalCell Γ c :=
              ⟨h𝒜_sub hc, disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hbd)⟩
            rw [cellCompl_eq_internal hport hc_int]
            exact Or.inl ⟨hG'_le.1 hwG', hwc⟩
      · rintro ⟨hwG, hwB⟩
        have hw_union : w ∈ ⋃ c ∈ Γ.C, (α_cell c).vertexSet := hport.r3_union_V ▸ hwG
        rw [mem_iUnion₂] at hw_union
        rcases hw_union with ⟨c, hc, hwc⟩
        by_cases hc_in : c ∈ 𝒜₁ ∪ 𝒜₂
        · have hwBc := hwB c hc_in
          rcases hc_in with hc₁ | hc₂
          · rw [cellCompl_eq_internal hport hc₁.2.1] at hwBc
            rcases hwBc with ⟨_, hnot_c⟩ | hwt
            · exact (hnot_c hwc).elim
            · exact Or.inl (Or.inl (image_mono (Γ.tilde_subset_N hc) hwt))
          · obtain ⟨_, hbd⟩ := h𝒜₂_border c hc₂
            rw [cellCompl_eq_border hport hc hbd] at hwBc
            rcases hwBc with ⟨_, hnot_c⟩ | hwt
            · exact (hnot_c hwc).elim
            · rw [mem_iUnion₂] at hwt
              rcases hwt with ⟨u, hu_c, hwu⟩
              exact Or.inl (Or.inr (mem_biUnion (tilde_subset_N_bd_of_border_cell hc hbd hu_c) hwu))
        · exact Or.inr (mem_biUnion ⟨hc, hc_in⟩ hwc)
    · ext e
      simp only [G', G'_E, cellComplInterSubgraph, mem_inter_iff, mem_iInter₂, mem_iUnion₂]
      constructor
      · rintro ⟨c, ⟨hc, hc_not⟩, hec⟩
        refine ⟨(hport.r2_cell_le c hc).2 hec, fun c' hc' => ?_⟩
        have hne : c ≠ c' := fun h => hc_not (h ▸ hc')
        have he_not_c' : e ∉ (α_cell c').edgeSet :=
          Set.disjoint_left.mp (hport.r3_edge_disjoint c hc c' (h𝒜_sub hc') hne) hec
        by_cases hbd' : (c' ∩ bd S).Nonempty
        · rw [cellCompl_eq_border hport (h𝒜_sub hc') hbd']
          exact ⟨(hport.r2_cell_le c hc).2 hec, he_not_c'⟩
        · have hc'_int : IsInternalCell Γ c' :=
            ⟨h𝒜_sub hc', disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hbd')⟩
          rw [cellCompl_eq_internal hport hc'_int]
          exact ⟨(hport.r2_cell_le c hc).2 hec, he_not_c'⟩
      · rintro ⟨heG, heB⟩
        have he_union : e ∈ ⋃ c ∈ Γ.C, (α_cell c).edgeSet := hport.r3_union_E ▸ heG
        rw [mem_iUnion₂] at he_union
        rcases he_union with ⟨c, hc, hec⟩
        by_cases hc_in : c ∈ 𝒜₁ ∪ 𝒜₂
        · have heBc := heB c hc_in
          by_cases hbd : (c ∩ bd S).Nonempty
          · rw [cellCompl_eq_border hport hc hbd] at heBc
            exact (heBc.2 hec).elim
          · have hc_int : IsInternalCell Γ c :=
              ⟨hc, disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hbd)⟩
            rw [cellCompl_eq_internal hport hc_int] at heBc
            exact (heBc.2 hec).elim
        · exact ⟨c, ⟨hc, hc_in⟩, hec⟩
  -- Bound the union of separation vertices over 𝒜₁ ∪ 𝒜₂ by n
  have h_sep_union_le_n :
      (⋃ c ∈ 𝒜₁ ∪ 𝒜₂, (α_cell c ∩ cellCompl hport c (h𝒜_sub ‹_›)).vertexSet).ncard ≤ n := by
    have h_split :
        (⋃ c ∈ 𝒜₁ ∪ 𝒜₂, (α_cell c ∩ cellCompl hport c (h𝒜_sub ‹_›)).vertexSet) =
        (⋃ c ∈ 𝒜₁, (α_cell c ∩ cellCompl hport c (h𝒜₁_sub ‹_›)).vertexSet) ∪
        (⋃ c ∈ 𝒜₂, (α_cell c ∩ cellCompl hport c (h𝒜₂_sub ‹_›)).vertexSet) := by
      ext w
      simp only [mem_union, mem_iUnion]
      constructor
      · rintro ⟨c, hc₁ | hc₂, hwc⟩
        · exact Or.inl ⟨c, hc₁, hwc⟩
        · exact Or.inr ⟨c, hc₂, hwc⟩
      · rintro (⟨c, hc₁, hwc⟩ | ⟨c, hc₂, hwc⟩)
        · exact ⟨c, Or.inl hc₁, hwc⟩
        · exact ⟨c, Or.inr hc₂, hwc⟩
    rw [h_split]
    have h_card₁ :
        (⋃ c ∈ 𝒜₁, (α_cell c ∩ cellCompl hport c (h𝒜₁_sub ‹_›)).vertexSet).ncard ≤ 3 * p := by
      calc (⋃ c ∈ 𝒜₁, (α_cell c ∩ cellCompl hport c (h𝒜₁_sub ‹_›)).vertexSet).ncard
          ≤ 3 * 𝒜₁.ncard := by
            refine ncard_biUnion_le_mul h𝒜₁_fin
              (fun c => if hc : c ∈ 𝒜₁ then (α_cell c ∩ cellCompl hport c (h𝒜₁_sub hc)).vertexSet else ∅) 3
              (fun c hc => by simp only [hc, ↓reduceDIte]; exact (α_cell c ∩ _).vertexSet_finite)
              (fun c hc => by
                simp only [hc, ↓reduceDIte, cellCompl_eq_internal hport hc.2.1]
                exact separationOrder_internalCellCompl_le hport hc.2.1)
              |>.trans' ?_
            apply le_of_eq; congr 1; ext w; simp only [mem_iUnion, exists_prop]
            exact ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, by simp only [hc, ↓reduceDIte]; exact h⟩,
              fun ⟨c, hc, h⟩ => ⟨c, hc, by simp only [hc, ↓reduceDIte] at h; exact h⟩⟩
        _ ≤ 3 * p := Nat.mul_le_mul_left 3 h𝒜₁_card_le
    have h_card₂ :
        (⋃ c ∈ 𝒜₂, (α_cell c ∩ cellCompl hport c (h𝒜₂_sub ‹_›)).vertexSet).ncard ≤ 2 * q * r := by
      calc (⋃ c ∈ 𝒜₂, (α_cell c ∩ cellCompl hport c (h𝒜₂_sub ‹_›)).vertexSet).ncard
          ≤ (2 * q) * 𝒜₂.ncard := by
            refine ncard_biUnion_le_mul h𝒜₂_fin
              (fun c => if hc : c ∈ 𝒜₂ then (α_cell c ∩ cellCompl hport c (h𝒜₂_sub hc)).vertexSet else ∅) (2 * q)
              (fun c hc => by simp only [hc, ↓reduceDIte]; exact (α_cell c ∩ _).vertexSet_finite)
              (fun c hc => by
                obtain ⟨hcC, hbd⟩ := h𝒜₂_border c hc
                simp only [hc, ↓reduceDIte, cellCompl_eq_border hport hcC hbd]
                exact separationOrder_borderCellCompl_le hport hq_cuff hcC hbd)
              |>.trans' ?_
            apply le_of_eq; congr 1; ext w; simp only [mem_iUnion, exists_prop]
            exact ⟨fun ⟨c, hc, h⟩ => ⟨c, hc, by simp only [hc, ↓reduceDIte]; exact h⟩,
              fun ⟨c, hc, h⟩ => ⟨c, hc, by simp only [hc, ↓reduceDIte] at h; exact h⟩⟩
        _ ≤ (2 * q) * r := Nat.mul_le_mul_left (2 * q) h𝒜₂_card_le
    calc ((⋃ c ∈ 𝒜₁, (α_cell c ∩ cellCompl hport c (h𝒜₁_sub ‹_›)).vertexSet) ∪
          (⋃ c ∈ 𝒜₂, (α_cell c ∩ cellCompl hport c (h𝒜₂_sub ‹_›)).vertexSet)).ncard
        ≤ (⋃ c ∈ 𝒜₁, (α_cell c ∩ cellCompl hport c (h𝒜₁_sub ‹_›)).vertexSet).ncard +
          (⋃ c ∈ 𝒜₂, (α_cell c ∩ cellCompl hport c (h𝒜₂_sub ‹_›)).vertexSet).ncard :=
          ncard_union_le _ _
      _ ≤ 3 * p + 2 * q * r := Nat.add_le_add h_card₁ h_card₂
      _ = n := rfl
  have hsep_A₀G' : G.IsSeparation A₀ G' := by
    rw [hG'_eq_inter]
    exact isSeparation_cellUnion_cellComplInter hport h𝒜_sub
  have hord_A₀G' : separationOrder A₀ G' ≤ n := by
    rw [hG'_eq_inter]
    unfold separationOrder
    have hfin_big :
        (⋃ c ∈ 𝒜₁ ∪ 𝒜₂, (α_cell c ∩ cellCompl hport c (h𝒜_sub ‹_›)).vertexSet).Finite :=
      G.vertexSet_finite.subset (iUnion₂_subset fun c hc =>
        inter_subset_left.trans (hport.r2_cell_le c (h𝒜_sub hc)).1)
    exact (ncard_le_ncard (inter_vertexSet_cellUnion_cellComplInter_subset hport h𝒜_sub) hfin_big).trans
      h_sep_union_le_n
  have hA₀G'_in_T : (A₀, G') ∈ 𝒯 := by
    rw [hG'_eq_inter]
    exact cellUnion_cellComplInter_mem_tangle hport h𝒯 hsurr h𝒜_sub
      (h_sep_union_le_n.trans_lt (by omega))
  -- Claim (3): By (3.5), G' has a tangle 𝒯' of order θ_G - separationOrder A₀ G' ≥ θ'
  obtain ⟨𝒯', h𝒯', h𝒯'_restrict⟩ := theorem_3_5_proof hG h𝒯 hA₀G'_in_T
  have hθ'_le_ord : θ' ≤ θ_G - separationOrder A₀ G' := by omega
  -- Claim (4): The pseudo-presentation surrounds 𝒯'
  have hsurr' : PseudoPresentationSurroundsTangle Γ' r' F_star μ 𝒯' := by
    intro s hs ⟨j, hsF⟩
    obtain ⟨c, ⟨hc, hbd, rfl⟩, _⟩ := exists_border_cell_of_mem_drawingSpaces hS hV'_bd hs
    rw [hμ_border_cell c hc hbd]
    have hs_not_M : c ∩ bd S ∉ M := (hF_iff (c ∩ bd S) hs).mp ⟨j, hsF⟩
    have hc_not₂ : c ∉ 𝒜₂ := (h_cell_in_M_iff c hc hbd).not.mp hs_not_M
    have hc_not₁ : c ∉ 𝒜₁ := by
      intro hc₁
      rcases hbd with ⟨x, hxc, hxbd⟩
      exact Set.disjoint_left.mp hc₁.2.1.2 hxc hxbd
    have hc_le_G' : α_cell c ≤ G' := h_cell_le_G' c ⟨hc, fun h => h.elim hc_not₁ hc_not₂⟩
    have hc_inter_G' : α_cell c ∩ G' = α_cell c := by
      refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
        (GM10.inter_le_left hc_le_G' le_rfl) le_rfl
        (inter_eq_left.mpr hc_le_G'.1) (inter_eq_left.mpr hc_le_G'.2)
    have hsep_c := isSeparation_borderCellCompl hport hc hbd
    have hord_c : separationOrder (α_cell c) (borderCellCompl hport hc hbd) ≤ 2 * q :=
      separationOrder_borderCellCompl_le hport hq_cuff hc hbd
    have hc_in_T : (α_cell c, borderCellCompl hport hc hbd) ∈ 𝒯 :=
      GM17.theorem_4_1_i h𝒯 (hsurr c hc) hsep_c (by omega)
    have hc_in_T' : (α_cell c ∩ G', borderCellCompl hport hc hbd ∩ G') ∈ 𝒯' :=
      h𝒯'_restrict (α_cell c) (borderCellCompl hport hc hbd) hc_in_T (by omega)
    rw [hc_inter_G'] at hc_in_T'
    exact ⟨borderCellCompl hport hc hbd ∩ G', hc_in_T'⟩
  -- Claim (5): By (8.4), G' has no vital (p + n)-linkage
  have hno_vital_G' : ¬ HasVitalPLinkage G' (p + n) :=
    h84 G' hG'_graph Γ' Γ'_sub ιV' ιE' r' F_star μ (θ_G - separationOrder A₀ G') 𝒯'
      hr'_le_r hpp_depth (hθ'_ge_84.trans hθ'_le_ord) h𝒯' hsurr'
  -- Yet by (2.2) and (2.3), L ∩ G' is a vital (p + n)-linkage in G'!
  apply hno_vital_G'
  refine ⟨L ∩ G', (theorem_2_3_proof hL.1.1 hsep_A₀G').2 hL.1, (theorem_2_2_proof hL.1.1 hsep_A₀G').1, ?_⟩
  have hterm_sub := (theorem_2_2_proof hL.1.1 hsep_A₀G').2
  have hfin_union : ((terminals L \ A₀.vertexSet) ∪ (A₀ ∩ G').vertexSet).Finite :=
    ((L.vertexSet_finite.subset fun _ h => h.1).sdiff).union (A₀ ∩ G').vertexSet_finite
  have hterm_fin : (terminals L).Finite := L.vertexSet_finite.subset fun _ h => h.1
  calc (terminals (L ∩ G')).ncard
      ≤ ((terminals L \ A₀.vertexSet) ∪ (A₀ ∩ G').vertexSet).ncard :=
        ncard_le_ncard hterm_sub hfin_union
    _ ≤ (terminals L \ A₀.vertexSet).ncard + (A₀ ∩ G').vertexSet.ncard :=
        ncard_union_le _ _
    _ ≤ (terminals L).ncard + separationOrder A₀ G' :=
        Nat.add_le_add (ncard_le_ncard sdiff_subset hterm_fin) le_rfl
    _ ≤ p + n := Nat.add_le_add hL.2.2 hord_A₀G'

/-- **Graph Minors XXI, (9.2)** (page 38 of the preprint):
"**9.2** *For every surface $\Sigma$, and all integers $p \ge 0$ and $q \ge 1$, there exists
$\theta \ge 1$ such that, if a graph $G$ has a portrait in $\Sigma$ of depth $\le q$ which
surrounds a tangle of order $\ge \theta$, then $G$ has no vital $p$-linkage.*" -/
theorem theorem_9_2_proof
    (S : Type) [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) (p q : ℕ) (hq : 1 ≤ q) :
    ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ {α : Type u} {β : Type v} (G : Hypergraph α β), G.IsGraph →
        ∀ (Γ : GM17.Painting S) (ιN : S → α)
          (α_cell : Set S → Hypergraph α β) (α_vert : S → Hypergraph α β)
          (θ_G : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
          PortraitHasDepthLe G Γ ιN α_cell α_vert q →
          θ ≤ θ_G →
          IsTangle G θ_G 𝒯 →
          PortraitSurroundsTangle Γ α_cell 𝒯 →
          ¬ HasVitalPLinkage G p := by
  obtain ⟨θ, hθ_pos, h92⟩ := theorem_9_2_shapes S hS p q hq
  refine ⟨θ, hθ_pos, ?_⟩
  intro α β G hG Γ ιN α_cell α_vert θ_G 𝒯 hdepth hθ_le h𝒯 hsurr
  exact h92 G hG Γ ιN α_cell α_vert θ_G 𝒯 (hdepth.toPortraitHasDepthLe21 hG) hθ_le h𝒯 hsurr

end GM21
end GraphMinor
