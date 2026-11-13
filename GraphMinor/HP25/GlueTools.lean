module

public import GraphMinor.HP25.SplitTools
public import GraphMinor.Surface.DiscUnion
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.Schoenflies
import GraphMinor.Surface.SurfaceGraph

/-!
# Tools for gluing two plane embeddings

Proposition 3.1 of Humeau and Pous glues two rib embeddings along a common path of their frames.
This file prepares the topology.

* `PlaneEmbedding.exists_pathMatch`: for a path list `l` drawn by two embeddings `φ₁` and `φ₂`,
  a map from the image of `l` under `φ₁` onto its image under `φ₂`, continuous and injective, that
  sends the point of each vertex of `l` to its point under `φ₂` and the line of each edge of `l` onto
  its line under `φ₂`. It is built line by line.
* `exists_sideMatch`: an `O`-arc made of two arcs `c` and `d` has a homeomorphism of closed inner
  domains onto the closed inner domain of another such `O`-arc, sending `c` to `c'` and `d` to `d'`
  with the same parameters (Schoenflies, through `Surface.exists_bdMatch_closedInner`).
* `exists_cut_unit`: the unit circle with the diameter from `-1` to `1` as a cross-cut.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface Metric

local notation "𝕀" => unitInterval

variable {V : Type*} {G : SimpleGraph V}

/-- The image of a line under a map that is continuous and injective on it is a line. -/
theorem isLineWithEnds_image {L : Set ℂ} {u v : ℂ} (hL : IsLineWithEnds L u v) {f : ℂ → ℂ}
    (hc : ContinuousOn f L) (hi : InjOn f L) : IsLineWithEnds (f '' L) (f u) (f v) := by
  obtain ⟨a, ha, hr, h0, h1⟩ := hL.exists_arc
  have hm : ∀ t, a t ∈ L := fun t => hr ▸ mem_range_self t
  have hb : IsArcMap (f ∘ a) :=
    ⟨hc.comp_continuous ha.1 hm, fun s t h => ha.2 (hi (hm s) (hm t) h)⟩
  have := hb.isLineWithEnds
  rwa [range_comp, hr, Function.comp_apply, Function.comp_apply, h0, h1] at this

/-- Two lines are matched by a map that is continuous and injective on the first, sends it onto the
second, and sends ends to ends. -/
theorem exists_lineMatch {L₁ L₂ : Set ℂ} {p₁ q₁ p₂ q₂ : ℂ} (h₁ : IsLineWithEnds L₁ p₁ q₁)
    (h₂ : IsLineWithEnds L₂ p₂ q₂) :
    ∃ g : ℂ → ℂ, ContinuousOn g L₁ ∧ InjOn g L₁ ∧ g '' L₁ = L₂ ∧ g p₁ = p₂ ∧ g q₁ = q₂ := by
  obtain ⟨a₁, ha₁, hr₁, h0₁, h1₁⟩ := h₁.exists_arc
  obtain ⟨a₂, ha₂, hr₂, h0₂, h1₂⟩ := h₂.exists_arc
  obtain ⟨ι, hι, hιc⟩ := ha₁.exists_inv
  subst hr₁ hr₂ h0₁ h1₁ h0₂ h1₂
  refine ⟨fun z => a₂ (ι z), ha₂.1.comp_continuousOn hιc, ?_, ?_, by simp [hι], by simp [hι]⟩
  · rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ h
    simp only [hι] at h
    rw [ha₂.2 h]
  · ext z
    simp [hι]

namespace PlaneEmbedding

variable {R₁ R₂ : Set V}

/-- The image of a path list is compact. -/
theorem isCompact_pathImage (φ : PlaneEmbedding G R₁) :
    ∀ {l : List V}, IsPathList G R₁ l → IsCompact (φ.pathImage l)
  | [], _ => by simp
  | [_], _ => by simp
  | x :: y :: l, h => by
    rw [pathImage_cons_cons]
    exact (φ.isLine x (h.2.2 x (by simp)) y (h.2.2 y (by simp))
      (List.isChain_cons_cons.mp h.2.1).1).isCompact.union (φ.isCompact_pathImage h.tail)

/-- **Matching two drawings of a path, line by line.** If a path list `x t` is drawn by `φ₁` and by
`φ₂`, some map is continuous and injective on its image under `φ₁`, sends it onto its image under
`φ₂`, sends the point of each vertex to its point under `φ₂`, and sends the line of each edge onto
its line under `φ₂`. -/
theorem exists_pathMatch (φ₁ : PlaneEmbedding G R₁) (φ₂ : PlaneEmbedding G R₂) :
    ∀ (x : V) (t : List V), IsPathList G R₁ (x :: t) → IsPathList G R₂ (x :: t) →
      ∃ k : ℂ → ℂ, ContinuousOn k (φ₁.pathImage (x :: t)) ∧ InjOn k (φ₁.pathImage (x :: t)) ∧
        k '' φ₁.pathImage (x :: t) = φ₂.pathImage (x :: t) ∧
        (∀ y ∈ x :: t, k (φ₁.pt y) = φ₂.pt y) ∧
        ∀ p ∈ (x :: t).zip t, k '' φ₁.line p.1 p.2 = φ₂.line p.1 p.2 := by
  intro x t
  induction t generalizing x with
  | nil =>
    intro _ _
    refine ⟨fun _ => φ₂.pt x, continuousOn_const, by simp, by simp, ?_, by simp⟩
    intro y hy
    rw [List.mem_singleton.mp hy]
  | cons y t ih =>
    intro h₁ h₂
    obtain ⟨k', hc', hi', him', hpt', hl'⟩ := ih y h₁.tail h₂.tail
    have hxy := (List.isChain_cons_cons.mp h₁.2.1).1
    have hx₁ := h₁.2.2 x (by simp)
    have hy₁ := h₁.2.2 y (by simp)
    have hx₂ := h₂.2.2 x (by simp)
    have hy₂ := h₂.2.2 y (by simp)
    have hxl : x ∉ y :: t := (List.nodup_cons.mp h₁.1).1
    have L₁ := φ₁.isLine x hx₁ y hy₁ hxy
    have L₂ := φ₂.isLine x hx₂ y hy₂ hxy
    obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := exists_lineMatch L₁ L₂
    classical
    set P₁ := φ₁.pathImage (y :: t)
    set P₂ := φ₂.pathImage (y :: t)
    have I₁ : φ₁.line x y ∩ P₁ ⊆ {φ₁.pt y} := φ₁.line_inter_pathImage hx₁ hxy h₁.tail hxl
    have I₂ : φ₂.line x y ∩ P₂ ⊆ {φ₂.pt y} := φ₂.line_inter_pathImage hx₂ hxy h₂.tail hxl
    let k : ℂ → ℂ := fun z => if z ∈ φ₁.line x y then g z else k' z
    have hkL : EqOn k g (φ₁.line x y) := fun z hz => by simp only [k, hz, ↓reduceIte]
    have hkP : EqOn k k' P₁ := by
      intro z hz
      by_cases hzL : z ∈ φ₁.line x y
      · have hzy : z = φ₁.pt y := I₁ ⟨hzL, hz⟩
        simp only [k, hzL, ↓reduceIte]
        rw [hzy, hg1, hpt' y (by simp)]
      · simp only [k, hzL, ↓reduceIte]
    have hyP : P₁.Nonempty → φ₁.pt y ∈ P₁ := by
      rintro ⟨z, hz⟩
      rcases t with _ | ⟨w, t⟩
      · simp [P₁] at hz
      · exact φ₁.pt_mem_pathImage h₁.tail (by simp) (by simp)
    refine ⟨k, ?_, ?_, ?_, ?_, ?_⟩
    · rw [pathImage_cons_cons]
      exact ContinuousOn.union_of_isClosed (hgc.congr hkL) (hc'.congr hkP) L₁.isCompact.isClosed
        (φ₁.isCompact_pathImage h₁.tail).isClosed
    · rw [pathImage_cons_cons]
      have key : ∀ z ∈ φ₁.line x y, ∀ w ∈ P₁, k z = k w → z = w := by
        intro z hz w hw he
        rw [hkL hz, hkP hw] at he
        by_cases hwL : w ∈ φ₁.line x y
        · rw [← hkP hw, hkL hwL] at he
          exact hgi hz hwL he
        · have hm : k' w ∈ φ₂.line x y ∩ P₂ :=
            ⟨he ▸ hgim ▸ mem_image_of_mem g hz, him' ▸ mem_image_of_mem k' hw⟩
          have h1 : k' w = k' (φ₁.pt y) := by
            rw [hpt' y (by simp)]
            exact I₂ hm
          have := hi' hw (hyP ⟨w, hw⟩) h1
          exact absurd (this ▸ L₁.right_mem) hwL
      rintro z (hz | hz) w (hw | hw) he
      · exact hgi hz hw (by rwa [hkL hz, hkL hw] at he)
      · exact key z hz w hw he
      · exact (key w hw z hz he.symm).symm
      · exact hi' hz hw (by rwa [hkP hz, hkP hw] at he)
    · rw [pathImage_cons_cons, pathImage_cons_cons, image_union, image_congr hkL, image_congr hkP,
        hgim, him']
    · intro w hw
      by_cases hwL : φ₁.pt w ∈ φ₁.line x y
      · rw [hkL hwL]
        have hwR : w ∈ R₁ := h₁.2.2 w hw
        rcases φ₁.avoid x hx₁ y hy₁ hxy w hwR hwL with rfl | rfl
        · exact hg0
        · exact hg1
      · simp only [k, hwL, ↓reduceIte]
        rcases List.mem_cons.mp hw with rfl | hw
        · exact absurd L₁.left_mem hwL
        · exact hpt' w hw
    · intro p hp
      rw [List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · rw [image_congr hkL, hgim]
      · have hsub : φ₁.line p.1 p.2 ⊆ P₁ := by
          intro z hz
          simp only [P₁, pathImage, mem_iUnion]
          exact ⟨p, hp, hz⟩
        rw [image_congr (hkP.mono hsub), hl' p hp]

end PlaneEmbedding

/-- **Matching two closed discs along two arcs each.** Let `F = c ∪ d` and `F' = c' ∪ d'` be
`O`-arcs made of two arcs with the same ends that meet only at their ends. Then some homeomorphism
of the closed inner domain of `F` onto that of `F'` sends `c s` to `c' s` and `d s` to `d' s`. -/
theorem exists_sideMatch {c d c' d' : 𝕀 → ℂ} (hc : IsArcMap c) (hd : IsArcMap d)
    (hc' : IsArcMap c') (hd' : IsArcMap d') (h0 : d 0 = c 0) (h1 : d 1 = c 1) (h0' : d' 0 = c' 0)
    (h1' : d' 1 = c' 1) (hm : ∀ s t, c s = d t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hm' : ∀ s t, c' s = d' t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    ∃ ψ χ : ℂ → ℂ, BdMatch (closedInner (range c ∪ range d)) (closedInner (range c' ∪ range d'))
      ψ χ ∧ (∀ s, ψ (c s) = c' s) ∧ ∀ s, ψ (d s) = d' s := by
  obtain ⟨h, k, m, hhc, hhd⟩ := exists_bdMatch_of_arcs hc hd hc' hd' h0 h1 h0' h1' hm hm'
  have hF := oArc_of_two_arcs hc hd h0.symm h1.symm hm
  have hF' := oArc_of_two_arcs hc' hd' h0'.symm h1'.symm hm'
  obtain ⟨ψ, χ, m', heq⟩ := exists_bdMatch_closedInner hF hF' m
  refine ⟨ψ, χ, m', fun s => ?_, fun s => ?_⟩
  · rw [heq (Or.inl ⟨s, rfl⟩), hhc]
  · rw [heq (Or.inr ⟨s, rfl⟩), hhd]

/-- The diameter of the unit disc from `-1` to `1`. -/
noncomputable def unitDiameter (u : 𝕀) : ℂ := ((2 * u.1 - 1 : ℝ) : ℂ)

theorem isArcMap_unitDiameter : IsArcMap unitDiameter := by
  refine ⟨Complex.continuous_ofReal.comp (by fun_prop), fun u v h => ?_⟩
  have h1 : 2 * u.1 - 1 = 2 * v.1 - 1 := Complex.ofReal_injective h
  exact Subtype.ext (by linarith)

/-- The diameter is a cross-cut of the unit circle. -/
theorem exists_cut_unit : ∃ a b, IsCut (sphere (0 : ℂ) 1) a b unitDiameter := by
  obtain ⟨φ₀⟩ := oArc_sphere
  refine exists_isCut φ₀ isArcMap_unitDiameter ?_ ?_ ?_ ?_
  · intro h
    have h1 : 2 * (0 : ℝ) - 1 = 2 * 1 - 1 := Complex.ofReal_injective h
    norm_num at h1
  · rw [mem_sphere_zero_iff_norm, unitDiameter, Complex.norm_real]
    simp
  · rw [mem_sphere_zero_iff_norm, unitDiameter, Complex.norm_real]
    norm_num
  · intro t h0 h1
    rw [inner_sphere, mem_ball_zero_iff, unitDiameter, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    have h2 : 0 < t.1 := lt_of_le_of_ne t.2.1 fun h => h0 (Subtype.ext h.symm)
    have h3 : t.1 < 1 := lt_of_le_of_ne t.2.2 fun h => h1 (Subtype.ext h)
    constructor <;> linarith

end GraphMinor.HP25
