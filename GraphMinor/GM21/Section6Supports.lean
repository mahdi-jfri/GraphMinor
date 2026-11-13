module

public import GraphMinor.GM21.Defs
public import GraphMinor.Surface.Classification
public import GraphMinor.Surface.ChartCells
public import GraphMinor.Surface.CutLift
public import GraphMinor.GM17.ArcDisc
public import GraphMinor.GM17.CuffOrder
import Mathlib.Analysis.Convex.PathConnected

/-!
# Spaces, Supports, and Interval Representations on Cuffs (Graph Minors XXI, Sections 6 and 7)

This file develops the topological and combinatorial properties of boundary spaces
(`drawingSpaces Γ = componentsIn (bd S \ Γ.V)`), supports (`IsSupportOfDrawing Γ F`), and
sub-support intervals on a support `F` of a drawing `Γ : Drawing S` satisfying
`∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard`.
-/

@[expose] public section

namespace GraphMinor.GM21.Supports

open Set Function Topology Classical
open GraphMinor.Surface
open GraphMinor.GM17
open GraphMinor.GM19

universe w

local notation "𝕀" => unitInterval

/-! ## 1. Complementary Lines on `O`-Arcs and Piece Decomposition -/

section CuffLines

variable {S : Type w} [TopologicalSpace S]

/-- Universe-polymorphic version of `GM17.oarc_split`: a line in an `O`-arc has a complementary line
with the same ends. -/
theorem oarc_split_univ [T2Space S] {O L : Set S} {x y : S}
    (hO : IsOArc O) (hL : IsLineWithEnds L x y) (hs : L ⊆ O) :
    ∃ L', IsLineWithEnds L' x y ∧ L ∪ L' = O ∧ L ∩ L' = {x, y} := by
  have hne := hL.ne'
  have hx := hs hL.left_mem
  have hy := hs hL.right_mem
  obtain ⟨A, B, hA, hB, hu, hi⟩ := hO.lines hx hy hne
  have hp := hL.isPreconnected_diff
  have hcA : IsClosed A := hA.isCompact.isClosed
  have hcB : IsClosed B := hB.isCompact.isClosed
  have hcov : L \ {x, y} ⊆ A ∪ B := hu ▸ sdiff_subset.trans hs
  have key : ¬ ((L \ {x, y}) ∩ A).Nonempty ∨ ¬ ((L \ {x, y}) ∩ B).Nonempty := by
    by_contra h
    push Not at h
    obtain ⟨z, hz, hz'⟩ := isPreconnected_closed_iff.mp hp A B hcA hcB hcov h.1 h.2
    rw [hi] at hz'
    exact hz.2 hz'
  have hend : ∀ {P : Set S}, IsLineWithEnds P x y → L \ {x, y} ⊆ P → L = P := fun {P} hP hsub => by
    have hLc : IsPreconnected L := by
      obtain ⟨a, ha, hr, -, -⟩ := hL.exists_arc
      rw [← hr]
      exact isPreconnected_range ha.1
    refine hP.eq_of_subset hLc (fun z hz => ?_) hL.left_mem hL.right_mem
    by_cases h : z ∈ ({x, y} : Set S)
    · rcases h with rfl | rfl
      · exact hP.left_mem
      · exact hP.right_mem
    · exact hsub ⟨hz, h⟩
  rcases key with h | h
  · have h1 : L \ {x, y} ⊆ B := fun z hz => (hcov hz).resolve_left fun hA' => h ⟨z, hz, hA'⟩
    obtain rfl := hend hB h1
    exact ⟨A, hA, by rwa [union_comm], by rwa [inter_comm]⟩
  · have h1 : L \ {x, y} ⊆ A := fun z hz => (hcov hz).resolve_right fun hB' => h ⟨z, hz, hB'⟩
    obtain rfl := hend hA h1
    exact ⟨B, hB, hu, hi⟩

/-- Universe-polymorphic version of `GM17.circle_lines`: a pair of complementary lines of a circle
are the two arcs between two angles, and in fact equal those two arcs. -/
theorem circle_lines_univ [T2Space S] {Θ I I' : Set S} (f : Circle ≃ₜ Θ) {t₁ t₃ : ℝ}
    (hlt : t₁ < t₃) (ht₃ : t₃ < t₁ + 2 * Real.pi)
    (hI : IsLineWithEnds I (cuffPoint f t₁) (cuffPoint f t₃))
    (hI' : IsLineWithEnds I' (cuffPoint f t₁) (cuffPoint f t₃))
    (hu : I ∪ I' = Θ) (hi_eq : I ∩ I' = {cuffPoint f t₁, cuffPoint f t₃}) :
    cuffPoint f '' Icc t₁ t₃ ∩ cuffPoint f '' Icc t₃ (t₁ + 2 * Real.pi) =
      {cuffPoint f t₁, cuffPoint f t₃} ∧
    ((I = cuffPoint f '' Icc t₁ t₃ ∧ I' = cuffPoint f '' Icc t₃ (t₁ + 2 * Real.pi)) ∨
      (I = cuffPoint f '' Icc t₃ (t₁ + 2 * Real.pi) ∧ I' = cuffPoint f '' Icc t₁ t₃)) := by
  have hpi := Real.pi_pos
  set n₁ := cuffPoint f t₁ with e₁
  set n₂ := cuffPoint f t₃ with e₃
  let A : Set S := cuffPoint f '' Icc t₁ t₃
  let B : Set S := cuffPoint f '' Icc t₃ (t₁ + 2 * Real.pi)
  have cc := cuffPoint_continuous f
  have hcA : IsClosed A := (isCompact_Icc.image cc).isClosed
  have hcB : IsClosed B := (isCompact_Icc.image cc).isClosed
  have hAB : A ∪ B = Θ := by
    ext x
    constructor
    · rintro (⟨t, -, rfl⟩ | ⟨t, -, rfl⟩) <;> exact cuffPoint_mem f t
    · intro hx
      obtain ⟨t, ht, rfl⟩ := exists_cuffPoint_mem_Ico f t₁ hx
      rcases le_total t t₃ with h | h
      · exact .inl ⟨t, ⟨ht.1, h⟩, rfl⟩
      · exact .inr ⟨t, ⟨h, ht.2.le⟩, rfl⟩
  have hend₁ : n₁ ∈ A ∧ n₁ ∈ B :=
    ⟨⟨t₁, ⟨le_rfl, hlt.le⟩, rfl⟩, ⟨t₁ + 2 * Real.pi, ⟨ht₃.le, le_rfl⟩, by rw [cuffPoint_add_two_pi]⟩⟩
  have hend₂ : n₂ ∈ A ∧ n₂ ∈ B :=
    ⟨⟨t₃, ⟨hlt.le, le_rfl⟩, rfl⟩, ⟨t₃, ⟨le_rfl, ht₃.le⟩, rfl⟩⟩
  have hABi_sub : A ∩ B ⊆ {n₁, n₂} := by
    rintro _ ⟨⟨t, ht, rfl⟩, ⟨t', ht', he⟩⟩
    rcases eq_or_lt_of_le ht'.2 with h | h
    · left
      rw [e₁, ← he, h, cuffPoint_add_two_pi]
    · have := cuffPoint_injOn_Ico f t₁ ⟨ht.1, by linarith [ht.2]⟩ ⟨by linarith [ht'.1], h⟩ he.symm
      right
      have h6 : t = t₃ := by linarith [this, ht.2, ht'.1]
      rw [e₃]
      exact congrArg _ h6
  have hABi : A ∩ B = {n₁, n₂} := by
    refine Subset.antisymm hABi_sub ?_
    rintro z (rfl | rfl)
    · exact hend₁
    · exact hend₂
  have key : ∀ {L : Set S}, IsLineWithEnds L n₁ n₂ → L ⊆ Θ → L ⊆ A ∨ L ⊆ B := fun {L} hL hs => by
    have hcov : L \ {n₁, n₂} ⊆ A ∪ B := hAB ▸ sdiff_subset.trans hs
    have hsub : ∀ {P : Set S}, n₁ ∈ P → n₂ ∈ P → L \ {n₁, n₂} ⊆ P → L ⊆ P :=
      fun {P} h1 h2 h3 z hz => by
        by_cases h : z ∈ ({n₁, n₂} : Set S)
        · rcases h with rfl | rfl
          · exact h1
          · exact h2
        · exact h3 ⟨hz, h⟩
    by_contra hc
    push Not at hc
    have h1 : ((L \ {n₁, n₂}) ∩ A).Nonempty := by
      by_contra h
      exact hc.2 (hsub hend₁.2 hend₂.2 fun z hz => (hcov hz).resolve_left fun hA' => h ⟨z, hz, hA'⟩)
    have h2 : ((L \ {n₁, n₂}) ∩ B).Nonempty := by
      by_contra h
      exact hc.1 (hsub hend₁.1 hend₂.1 fun z hz => (hcov hz).resolve_right fun hB' => h ⟨z, hz, hB'⟩)
    obtain ⟨z, hz, hz'⟩ := isPreconnected_closed_iff.mp hL.isPreconnected_diff A B hcA hcB hcov h1 h2
    exact hz.2 (hABi_sub hz')
  have hmid₁ : ∃ z ∈ A, z ∉ B := by
    refine ⟨cuffPoint f ((t₁ + t₃) / 2), ⟨_, ⟨by linarith, by linarith⟩, rfl⟩, fun h => ?_⟩
    have h1 := hABi_sub ⟨⟨_, ⟨by linarith, by linarith⟩, rfl⟩, h⟩
    have h3 : ((t₁ + t₃) / 2) ∈ Ico t₁ (t₁ + 2 * Real.pi) := ⟨by linarith, by linarith⟩
    rcases h1 with h1 | h1
    · have := cuffPoint_injOn_Ico f t₁ h3 ⟨le_rfl, by linarith⟩ h1
      linarith
    · have := cuffPoint_injOn_Ico f t₁ h3 ⟨hlt.le, ht₃⟩ h1
      linarith
  have hmid₂ : ∃ z ∈ B, z ∉ A := by
    refine ⟨cuffPoint f ((t₃ + (t₁ + 2 * Real.pi)) / 2), ⟨_, ⟨by linarith, by linarith⟩, rfl⟩, fun h => ?_⟩
    have h1 := hABi_sub ⟨h, ⟨_, ⟨by linarith, by linarith⟩, rfl⟩⟩
    have h3 : ((t₃ + (t₁ + 2 * Real.pi)) / 2) ∈ Ico t₁ (t₁ + 2 * Real.pi) := ⟨by linarith, by linarith⟩
    rcases h1 with h1 | h1
    · have := cuffPoint_injOn_Ico f t₁ h3 ⟨le_rfl, by linarith⟩ h1
      linarith
    · have := cuffPoint_injOn_Ico f t₁ h3 ⟨hlt.le, ht₃⟩ h1
      linarith
  have hI1 : I ⊆ Θ := fun z hz => hu ▸ .inl hz
  have hI2 : I' ⊆ Θ := fun z hz => hu ▸ .inr hz
  have heq_of_sub : ∀ {P Q R W : Set S}, P ⊆ R → Q ⊆ W → P ∪ Q = Θ → R ∩ W ⊆ P ∩ Q →
      R ⊆ Θ → W ⊆ Θ → P = R ∧ Q = W := by
    intro P Q R W hPR hQW hPQ hRW hRΘ hWΘ
    refine ⟨Subset.antisymm hPR fun z hzR => ?_, Subset.antisymm hQW fun z hzW => ?_⟩
    · rcases (hPQ ▸ hRΘ hzR : z ∈ P ∪ Q) with hzP | hzQ
      · exact hzP
      · exact (hRW ⟨hzR, hQW hzQ⟩).1
    · rcases (hPQ ▸ hWΘ hzW : z ∈ P ∪ Q) with hzP | hzQ
      · exact (hRW ⟨hPR hzP, hzW⟩).2
      · exact hzQ
  have hAΘ : A ⊆ Θ := fun z hz => hAB ▸ .inl hz
  have hBΘ : B ⊆ Θ := fun z hz => hAB ▸ .inr hz
  refine ⟨hABi, ?_⟩
  rcases key hI hI1 with h1 | h1
  · rcases key hI' hI2 with h2 | h2
    · obtain ⟨z, hz, hz'⟩ := hmid₂
      exact absurd ((hu ▸ hAB ▸ .inr hz : z ∈ I ∪ I').elim (fun h => h1 h) fun h => h2 h) hz'
    · exact .inl (heq_of_sub h1 h2 hu (by rw [hABi, hi_eq]) hAΘ hBΘ)
  · rcases key hI' hI2 with h2 | h2
    · exact .inr (heq_of_sub h1 h2 hu (by rw [inter_comm B A, hABi, hi_eq]) hBΘ hAΘ)
    · obtain ⟨z, hz, hz'⟩ := hmid₁
      exact absurd ((hu ▸ hAB ▸ .inl hz : z ∈ I ∪ I').elim (fun h => h1 h) fun h => h2 h) hz'

/-- For any cuff parametrization `f : Circle ≃ₜ Θ` and `a < b < a + 2 * Real.pi`, the arc
`cuffPoint f '' Icc a b` is a line with ends `cuffPoint f a` and `cuffPoint f b`. -/
theorem isLineWithEnds_cuffPoint_Icc [T2Space S] {Θ : Set S} (f : Circle ≃ₜ Θ)
    {a b : ℝ} (hab : a < b) (hb : b < a + 2 * Real.pi) :
    IsLineWithEnds (cuffPoint f '' Icc a b) (cuffPoint f a) (cuffPoint f b) := by
  let φ : 𝕀 → S := fun t => cuffPoint f (a + t.1 * (b - a))
  have hφ_cont : Continuous φ :=
    (cuffPoint_continuous f).comp (continuous_const.add (continuous_subtype_val.mul continuous_const))
  have hφ_mem : ∀ t : 𝕀, a + t.1 * (b - a) ∈ Icc a b := fun t => by
    constructor <;> nlinarith [t.2.1, t.2.2]
  have hφ_inj : Function.Injective φ := fun s t heq => by
    have hs : a + s.1 * (b - a) ∈ Ico a (a + 2 * Real.pi) :=
      ⟨(hφ_mem s).1, (hφ_mem s).2.trans_lt hb⟩
    have ht : a + t.1 * (b - a) ∈ Ico a (a + 2 * Real.pi) :=
      ⟨(hφ_mem t).1, (hφ_mem t).2.trans_lt hb⟩
    have hval := cuffPoint_injOn_Ico f a hs ht heq
    have hmul : (s.1 - t.1) * (b - a) = 0 := by linarith
    have hsub := (mul_eq_zero.mp hmul).resolve_right (by linarith)
    exact Subtype.ext (by linarith)
  have hrange : Set.range φ = cuffPoint f '' Icc a b := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨a + t.1 * (b - a), hφ_mem t, rfl⟩
    · rintro ⟨u, ⟨hu1, hu2⟩, rfl⟩
      have hd : 0 < b - a := by linarith
      let t : 𝕀 := ⟨(u - a) / (b - a), div_nonneg (by linarith) hd.le,
        (div_le_one hd).mpr (by linarith)⟩
      refine ⟨t, ?_⟩
      dsimp [φ, t]
      congr 1
      field_simp
      ring
  let ev : 𝕀 ≃ₜ Set.range φ :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective φ hφ_inj)
      hφ_cont.rangeFactorization
  refine ⟨ev.trans (Homeomorph.setCongr hrange), ?_, ?_⟩
  · show φ 0 = cuffPoint f a
    dsimp [φ]; ring_nf
  · show φ 1 = cuffPoint f b
    dsimp [φ]; ring_nf

/-- If a set `W` is the union of finitely many pairwise disjoint connected pieces `P`, each closed
in `W`, then `componentsIn W = P`. -/
theorem componentsIn_of_pieces {W : Set S} {P : Set (Set S)} (hP : P.Finite)
    (hconn : ∀ p ∈ P, IsConnected p) (hd : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint p q)
    (hcl : ∀ p ∈ P, closure p ∩ W ⊆ p) (hW : W = ⋃₀ P) : componentsIn W = P := by
  have hsub : ∀ p ∈ P, p ⊆ W := fun p hp => hW ▸ subset_sUnion_of_mem hp
  have hmem : ∀ p ∈ P, p ∈ componentsIn W := by
    intro p hp
    obtain ⟨x₀, hx₀⟩ := (hconn p hp).nonempty
    refine ⟨x₀, hsub p hp hx₀, Subset.antisymm ?_ ?_⟩
    · let Q : Set S := ⋃ q ∈ P \ {p}, closure q
      have hQ : IsClosed Q := (hP.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure
      have hcov : connectedComponentIn W x₀ ⊆ closure p ∪ Q := fun x hx => by
        have hxW := connectedComponentIn_subset W x₀ hx
        rw [hW] at hxW
        obtain ⟨q, hq, hxq⟩ := hxW
        by_cases hqp : q = p
        · exact Or.inl (subset_closure (hqp ▸ hxq))
        · exact Or.inr (mem_biUnion (show q ∈ P \ {p} from ⟨hq, hqp⟩) (subset_closure hxq))
      intro x hx
      by_contra hxp
      have hxW := connectedComponentIn_subset W x₀ hx
      have hxQ : x ∈ Q := (hcov hx).resolve_left fun h => hxp (hcl p hp ⟨h, hxW⟩)
      have hcomp_pre : IsPreconnected (connectedComponentIn W x₀) :=
        isPreconnected_connectedComponentIn
      have hx₀_comp : x₀ ∈ connectedComponentIn W x₀ := mem_connectedComponentIn (hsub p hp hx₀)
      obtain ⟨y, hyC, hy₁, hy₂⟩ := isPreconnected_closed_iff.mp hcomp_pre _ _
        isClosed_closure hQ hcov ⟨x₀, hx₀_comp, subset_closure hx₀⟩ ⟨x, hx, hxQ⟩
      have hyW := connectedComponentIn_subset W x₀ hyC
      have hyp := hcl p hp ⟨hy₁, hyW⟩
      obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.mp hy₂
      have hyq' := hcl q hq.1 ⟨hyq, hyW⟩
      exact disjoint_left.mp (hd p hp q hq.1 (Ne.symm hq.2)) hyp hyq'
    · exact (hconn p hp).isPreconnected.subset_connectedComponentIn hx₀ (hsub p hp)
  ext C
  refine ⟨fun hC => ?_, hmem C⟩
  rcases hC with ⟨x, hxW, rfl⟩
  have hxW' := hxW
  rw [hW] at hxW'
  obtain ⟨p, hp, hxp⟩ := hxW'
  rcases hmem p hp with ⟨y, hyW, hp_eq⟩
  have hxy : connectedComponentIn W x = connectedComponentIn W y := by
    refine (connectedComponentIn_eq ?_).symm
    rw [hp_eq]
    exact hxp
  rw [hxy, hp_eq]
  exact hp

end CuffLines

/-! ## 2. Vertex and Space Enumeration Around a Cuff -/

section VertexCuffDecomp

variable {S : Type w} [TopologicalSpace S] (V : Set S) (hV : V.Finite) {Θ : Set S}

/-- Canonical angle in `[0, 2π)` of a point `x ∈ Θ` under `f : Circle ≃ₜ Θ`. -/
noncomputable def vAngleOf (f : Circle ≃ₜ Θ) (x : S) : ℝ :=
  if hx : x ∈ Θ then Classical.choose (exists_cuffPoint_mem_Ico f 0 hx) else 0

theorem vAngleOf_mem_Ico (f : Circle ≃ₜ Θ) {x : S} (hx : x ∈ Θ) :
    vAngleOf f x ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) := by
  simp only [vAngleOf, hx, dite_true]
  exact (Classical.choose_spec (exists_cuffPoint_mem_Ico f 0 hx)).1

theorem cuffPoint_vAngleOf (f : Circle ≃ₜ Θ) {x : S} (hx : x ∈ Θ) :
    cuffPoint f (vAngleOf f x) = x := by
  simp only [vAngleOf, hx, dite_true]
  exact (Classical.choose_spec (exists_cuffPoint_mem_Ico f 0 hx)).2

theorem vAngleOf_cuffPoint (f : Circle ≃ₜ Θ) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) (0 + 2 * Real.pi)) :
    vAngleOf f (cuffPoint f t) = t := by
  have hx : cuffPoint f t ∈ Θ := cuffPoint_mem f t
  exact cuffPoint_injOn_Ico f 0 (vAngleOf_mem_Ico f hx) ht (cuffPoint_vAngleOf f hx)

theorem vAngleOf_injOn (f : Circle ≃ₜ Θ) : InjOn (vAngleOf f) Θ := by
  intro x hx y hy h
  rw [← cuffPoint_vAngleOf f hx, ← cuffPoint_vAngleOf f hy, h]

/-- The finset of angles of `V ∩ Θ` in `[0, 2π)`. -/
noncomputable def vAngleFinset (f : Circle ≃ₜ Θ) : Finset ℝ :=
  ((hV.inter_of_left Θ).toFinset).image (vAngleOf f)

theorem card_vAngleFinset (f : Circle ≃ₜ Θ) :
    (vAngleFinset V hV f).card = (V ∩ Θ).ncard := by
  unfold vAngleFinset
  have hinj : InjOn (vAngleOf f) ((hV.inter_of_left Θ).toFinset : Set S) := by
    refine (vAngleOf_injOn f).mono ?_
    rw [Set.Finite.coe_toFinset]
    exact inter_subset_right
  rw [Finset.card_image_of_injOn hinj, ← ncard_eq_toFinset_card (V ∩ Θ) (hV.inter_of_left Θ)]

/-- The `i`-th angle of `V ∩ Θ` in `[0, 2π)` in increasing order. -/
noncomputable def vAngle (f : Circle ≃ₜ Θ) (i : Fin (V ∩ Θ).ncard) : ℝ :=
  (vAngleFinset V hV f).orderEmbOfFin (card_vAngleFinset V hV f) i

theorem strictMono_vAngle (f : Circle ≃ₜ Θ) : StrictMono (vAngle V hV f) :=
  ((vAngleFinset V hV f).orderEmbOfFin (card_vAngleFinset V hV f)).strictMono

theorem range_vAngle (f : Circle ≃ₜ Θ) :
    Set.range (vAngle V hV f) = vAngleOf f '' (V ∩ Θ) := by
  unfold vAngle
  rw [Finset.range_orderEmbOfFin, vAngleFinset, Finset.coe_image, Set.Finite.coe_toFinset]

theorem vAngle_mem_Ico (f : Circle ≃ₜ Θ) (i : Fin (V ∩ Θ).ncard) :
    vAngle V hV f i ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) := by
  have hmem : vAngle V hV f i ∈ Set.range (vAngle V hV f) := mem_range_self i
  rw [range_vAngle] at hmem
  rcases hmem with ⟨x, ⟨_, hxΘ⟩, h_eq⟩
  rw [← h_eq]
  exact vAngleOf_mem_Ico f hxΘ

/-- The `i`-th vertex of `V ∩ Θ` around `Θ`. -/
noncomputable def vNode (f : Circle ≃ₜ Θ) (i : Fin (V ∩ Θ).ncard) : S :=
  cuffPoint f (vAngle V hV f i)

theorem injective_vNode (f : Circle ≃ₜ Θ) : Function.Injective (vNode V hV f) := by
  intro i j h
  have h_eq : vAngle V hV f i = vAngle V hV f j :=
    cuffPoint_injOn_Ico f 0 (vAngle_mem_Ico V hV f i) (vAngle_mem_Ico V hV f j) h
  exact (strictMono_vAngle V hV f).injective h_eq

theorem range_vNode (f : Circle ≃ₜ Θ) :
    Set.range (vNode V hV f) = V ∩ Θ := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    have hmem : vAngle V hV f i ∈ Set.range (vAngle V hV f) := mem_range_self i
    rw [range_vAngle] at hmem
    rcases hmem with ⟨y, hy, hy_eq⟩
    unfold vNode
    rw [← hy_eq, cuffPoint_vAngleOf f hy.2]
    exact hy
  · intro hx
    have hmem : vAngleOf f x ∈ Set.range (vAngle V hV f) := by
      rw [range_vAngle]
      exact ⟨x, hx, rfl⟩
    rcases hmem with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    unfold vNode
    rw [hi, cuffPoint_vAngleOf f hx.2]

theorem vNode_mem (f : Circle ≃ₜ Θ) (i : Fin (V ∩ Θ).ncard) :
    vNode V hV f i ∈ V ∩ Θ := by
  rw [← range_vNode V hV f]
  exact mem_range_self i

/-- The upper endpoint angle of the `i`-th space arc on `Θ`. -/
noncomputable def vUpperAngle (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard)
    (i : Fin (V ∩ Θ).ncard) : ℝ :=
  if h : i.1 + 1 < (V ∩ Θ).ncard then
    vAngle V hV f ⟨i.1 + 1, h⟩
  else
    vAngle V hV f ⟨0, by omega⟩ + 2 * Real.pi

theorem vAngle_lt_vUpperAngle (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard)
    (i : Fin (V ∩ Θ).ncard) :
    vAngle V hV f i < vUpperAngle V hV f hk i := by
  unfold vUpperAngle
  split_ifs with h
  · exact strictMono_vAngle V hV f (Nat.lt_succ_self i.1)
  · have hi := (vAngle_mem_Ico V hV f i).2
    have h0 := (vAngle_mem_Ico V hV f ⟨0, by omega⟩).1
    linarith

theorem vUpperAngle_lt_add_two_pi (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard)
    (i : Fin (V ∩ Θ).ncard) :
    vUpperAngle V hV f hk i < vAngle V hV f i + 2 * Real.pi := by
  unfold vUpperAngle
  split_ifs with h
  · have hi := (vAngle_mem_Ico V hV f i).1
    have h1 := (vAngle_mem_Ico V hV f ⟨i.1 + 1, h⟩).2
    linarith
  · have hi_pos : (⟨0, by omega⟩ : Fin (V ∩ Θ).ncard) < i := by
      change 0 < i.1
      have := i.2
      omega
    have hmono := strictMono_vAngle V hV f hi_pos
    linarith

/-- Cyclic successor index `(i + 1) % k` in `Fin k`. -/
def nextFin {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : Fin k :=
  ⟨(i.1 + 1) % k, Nat.mod_lt _ (by omega)⟩

theorem ne_nextFin {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : i ≠ nextFin hk i := by
  intro h_eq
  have hval : i.1 = (i.1 + 1) % k := congrArg Fin.val h_eq
  have hi_lt := i.2
  by_cases h1 : i.1 + 1 < k
  · rw [Nat.mod_eq_of_lt h1] at hval; omega
  · have heq : i.1 + 1 = k := by omega
    rw [heq, Nat.mod_self] at hval; omega

theorem bijective_nextFin {k : ℕ} (hk : 2 ≤ k) : Function.Bijective (nextFin hk) := by
  have hinj : Function.Injective (nextFin hk) := by
    intro i j h
    have hval : (i.1 + 1) % k = (j.1 + 1) % k := congrArg Fin.val h
    have hi := i.2; have hj := j.2
    apply Fin.ext
    by_cases h1 : i.1 + 1 < k <;> by_cases h2 : j.1 + 1 < k
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hval; omega
    · have hj_eq : j.1 + 1 = k := by omega
      rw [Nat.mod_eq_of_lt h1, hj_eq, Nat.mod_self] at hval; omega
    · have hi_eq : i.1 + 1 = k := by omega
      rw [hi_eq, Nat.mod_self, Nat.mod_eq_of_lt h2] at hval; omega
    · omega
  exact Finite.injective_iff_bijective.mp hinj

theorem cuffPoint_vUpperAngle (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard)
    (i : Fin (V ∩ Θ).ncard) :
    cuffPoint f (vUpperAngle V hV f hk i) = vNode V hV f (nextFin hk i) := by
  unfold vUpperAngle vNode nextFin
  split_ifs with h
  · congr 2
    apply Fin.ext
    dsimp
    exact (Nat.mod_eq_of_lt h).symm
  · rw [cuffPoint_add_two_pi]
    congr 2
    apply Fin.ext
    dsimp
    have heq : i.1 + 1 = (V ∩ Θ).ncard := by have := i.2; omega
    rw [heq, Nat.mod_self]

theorem notMem_V_of_mem_Ioo (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard)
    (i : Fin (V ∩ Θ).ncard) {t : ℝ}
    (ht : t ∈ Ioo (vAngle V hV f i) (vUpperAngle V hV f hk i)) :
    cuffPoint f t ∉ V := by
  intro hxV
  have hx : cuffPoint f t ∈ V ∩ Θ := ⟨hxV, cuffPoint_mem f t⟩
  rcases ht with ⟨ht₁, ht₂⟩
  unfold vUpperAngle at ht₂
  split_ifs at ht₂ with h
  · have ht_Ico : t ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
      ⟨(vAngle_mem_Ico V hV f i).1.trans ht₁.le,
       ht₂.trans (vAngle_mem_Ico V hV f ⟨i.1 + 1, h⟩).2⟩
    have ht_eq : vAngleOf f (cuffPoint f t) = t := vAngleOf_cuffPoint f ht_Ico
    have hmem : t ∈ Set.range (vAngle V hV f) := by
      rw [range_vAngle]
      exact ⟨cuffPoint f t, hx, ht_eq⟩
    rcases hmem with ⟨j, rfl⟩
    have hij : i < j := (strictMono_vAngle V hV f).lt_iff_lt.mp ht₁
    have hji : j < ⟨i.1 + 1, h⟩ := (strictMono_vAngle V hV f).lt_iff_lt.mp ht₂
    have hij' : i.1 < j.1 := hij
    have hji' : j.1 < i.1 + 1 := hji
    omega
  · by_cases hlt : t < 2 * Real.pi
    · have ht_Ico : t ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
        ⟨(vAngle_mem_Ico V hV f i).1.trans ht₁.le, by linarith⟩
      have ht_eq : vAngleOf f (cuffPoint f t) = t := vAngleOf_cuffPoint f ht_Ico
      have hmem : t ∈ Set.range (vAngle V hV f) := by
        rw [range_vAngle]
        exact ⟨cuffPoint f t, hx, ht_eq⟩
      rcases hmem with ⟨j, rfl⟩
      have hij : i < j := (strictMono_vAngle V hV f).lt_iff_lt.mp ht₁
      have hij' : i.1 < j.1 := hij
      have hj_lt := j.2
      omega
    · have ht_Ico : t - 2 * Real.pi ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
        ⟨by linarith, by linarith [(vAngle_mem_Ico V hV f ⟨0, by omega⟩).2]⟩
      have hcp : cuffPoint f (t - 2 * Real.pi) = cuffPoint f t := cuffPoint_sub_two_pi f t
      have ht_eq : vAngleOf f (cuffPoint f t) = t - 2 * Real.pi := by
        rw [← hcp]
        exact vAngleOf_cuffPoint f ht_Ico
      have hmem : t - 2 * Real.pi ∈ Set.range (vAngle V hV f) := by
        rw [range_vAngle]
        exact ⟨cuffPoint f t, hx, ht_eq⟩
      rcases hmem with ⟨j, hj⟩
      have hj0 : vAngle V hV f j < vAngle V hV f ⟨0, by omega⟩ := by linarith
      have hj_lt : j < ⟨0, by omega⟩ := (strictMono_vAngle V hV f).lt_iff_lt.mp hj0
      exact Nat.not_lt_zero j.1 hj_lt

/-- The `i`-th open space arc on `Θ \ V`. -/
noncomputable def vSpaceArc (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard)
    (i : Fin (V ∩ Θ).ncard) : Set S :=
  cuffPoint f '' Ioo (vAngle V hV f i) (vUpperAngle V hV f hk i)

/-- The midpoint angle of the `i`-th space arc on `Θ`. -/
noncomputable def vMidAngle (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard)
    (i : Fin (V ∩ Θ).ncard) : ℝ :=
  (vAngle V hV f i + vUpperAngle V hV f hk i) / 2

theorem vMidAngle_mem_Ioo (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard)
    (i : Fin (V ∩ Θ).ncard) :
    vMidAngle V hV f hk i ∈ Ioo (vAngle V hV f i) (vUpperAngle V hV f hk i) := by
  have hlt := vAngle_lt_vUpperAngle V hV f hk i
  unfold vMidAngle
  exact ⟨by linarith, by linarith⟩

/-- The midpoint of the `i`-th space arc on `Θ`. -/
noncomputable def vMidpoint (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard)
    (i : Fin (V ∩ Θ).ncard) : S :=
  cuffPoint f (vMidAngle V hV f hk i)

theorem vMidpoint_mem_vSpaceArc (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard)
    (i : Fin (V ∩ Θ).ncard) :
    vMidpoint V hV f hk i ∈ vSpaceArc V hV f hk i :=
  ⟨vMidAngle V hV f hk i, vMidAngle_mem_Ioo V hV f hk i, rfl⟩

theorem vSpaceArc_subset_diff (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard)
    (i : Fin (V ∩ Θ).ncard) :
    vSpaceArc V hV f hk i ⊆ Θ \ V := by
  rintro x ⟨t, ht, rfl⟩
  exact ⟨cuffPoint_mem f t, notMem_V_of_mem_Ioo V hV f hk i ht⟩

theorem isPathConnected_vSpaceArc (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard)
    (i : Fin (V ∩ Θ).ncard) :
    IsPathConnected (vSpaceArc V hV f hk i) :=
  ((convex_Ioo _ _).isPathConnected ⟨_, vMidAngle_mem_Ioo V hV f hk i⟩).image
    (cuffPoint_continuous f)

theorem vAngleOf_mem_of_mem_vSpaceArc (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard)
    (i : Fin (V ∩ Θ).ncard) {x : S} (hx : x ∈ vSpaceArc V hV f hk i) :
    if h : i.1 + 1 < (V ∩ Θ).ncard then
      vAngle V hV f i < vAngleOf f x ∧ vAngleOf f x < vAngle V hV f ⟨i.1 + 1, h⟩
    else
      vAngle V hV f i < vAngleOf f x ∨ vAngleOf f x < vAngle V hV f ⟨0, by omega⟩ := by
  rcases hx with ⟨t, ⟨ht₁, ht₂⟩, rfl⟩
  unfold vUpperAngle at ht₂
  split_ifs with h
  · simp only [h, ↓reduceDIte] at ht₂
    have ht_Ico : t ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
      ⟨(vAngle_mem_Ico V hV f i).1.trans ht₁.le,
       ht₂.trans (vAngle_mem_Ico V hV f ⟨i.1 + 1, h⟩).2⟩
    rw [vAngleOf_cuffPoint f ht_Ico]
    exact ⟨ht₁, ht₂⟩
  · simp only [h, ↓reduceDIte] at ht₂
    by_cases hlt : t < 2 * Real.pi
    · have ht_Ico : t ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
        ⟨(vAngle_mem_Ico V hV f i).1.trans ht₁.le, by linarith⟩
      rw [vAngleOf_cuffPoint f ht_Ico]
      exact Or.inl ht₁
    · have ht_Ico : t - 2 * Real.pi ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) :=
        ⟨by linarith, by linarith [(vAngle_mem_Ico V hV f ⟨0, by omega⟩).2]⟩
      have hcp : cuffPoint f (t - 2 * Real.pi) = cuffPoint f t := cuffPoint_sub_two_pi f t
      rw [← hcp, vAngleOf_cuffPoint f ht_Ico]
      exact Or.inr (by linarith)

theorem disjoint_vSpaceArc (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard)
    {i j : Fin (V ∩ Θ).ncard} (hij : i ≠ j) :
    Disjoint (vSpaceArc V hV f hk i) (vSpaceArc V hV f hk j) := by
  have hlt_disj : ∀ {a b : Fin (V ∩ Θ).ncard}, a < b →
      Disjoint (vSpaceArc V hV f hk a) (vSpaceArc V hV f hk b) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro x hxa hxb
    have ha := vAngleOf_mem_of_mem_vSpaceArc V hV f hk a hxa
    have hb := vAngleOf_mem_of_mem_vSpaceArc V hV f hk b hxb
    have ha_lt : a.1 + 1 < (V ∩ Θ).ncard := by have := b.2; omega
    simp only [ha_lt, ↓reduceDIte] at ha
    have hle1 : (⟨a.1 + 1, ha_lt⟩ : Fin (V ∩ Θ).ncard) ≤ b := hab
    have hmono1 := (strictMono_vAngle V hV f).monotone hle1
    have hle0 : (⟨0, by omega⟩ : Fin (V ∩ Θ).ncard) ≤ a := Nat.zero_le a.1
    have hmono0 := (strictMono_vAngle V hV f).monotone hle0
    split_ifs at hb with hb_lt
    · linarith
    · rcases hb with hb | hb <;> linarith
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt_disj h
  · exact (hlt_disj h).symm

theorem iUnion_vSpaceArc (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard) :
    (⋃ i, vSpaceArc V hV f hk i) = Θ \ V := by
  refine Subset.antisymm (iUnion_subset fun i => vSpaceArc_subset_diff V hV f hk i) ?_
  rintro x ⟨hxΘ, hxV⟩
  rw [mem_iUnion]
  set t := vAngleOf f x
  have ht_Ico : t ∈ Ico (0 : ℝ) (0 + 2 * Real.pi) := vAngleOf_mem_Ico f hxΘ
  have hcp : cuffPoint f t = x := cuffPoint_vAngleOf f hxΘ
  have hnot_range : t ∉ Set.range (vAngle V hV f) := by
    rw [range_vAngle]
    rintro ⟨y, ⟨hyV, hyΘ⟩, hy_eq⟩
    have hxy : y = x := vAngleOf_injOn f hyΘ hxΘ hy_eq
    exact hxV (hxy ▸ hyV)
  by_cases h0 : t < vAngle V hV f ⟨0, by omega⟩
  · let i_last : Fin (V ∩ Θ).ncard := ⟨(V ∩ Θ).ncard - 1, by omega⟩
    refine ⟨i_last, t + 2 * Real.pi, ?_, by rw [cuffPoint_add_two_pi, hcp]⟩
    have hi_last : ¬ (i_last.1 + 1 < (V ∩ Θ).ncard) := by dsimp [i_last]; omega
    have hup : vUpperAngle V hV f hk i_last = vAngle V hV f ⟨0, by omega⟩ + 2 * Real.pi := by
      unfold vUpperAngle
      simp only [hi_last, ↓reduceDIte]
    rw [hup]
    have hi_mem := (vAngle_mem_Ico V hV f i_last).2
    exact ⟨by linarith [ht_Ico.1], by linarith⟩
  · push Not at h0
    have h0_lt : vAngle V hV f ⟨0, by omega⟩ < t :=
      lt_of_le_of_ne h0 (fun h_eq => hnot_range ⟨⟨0, by omega⟩, h_eq⟩)
    let S_lt : Finset (Fin (V ∩ Θ).ncard) :=
      Finset.univ.filter (fun i => vAngle V hV f i < t)
    have hS_ne : S_lt.Nonempty :=
      ⟨⟨0, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0_lt⟩⟩
    let i := S_lt.max' hS_ne
    have hi_mem : i ∈ S_lt := Finset.max'_mem S_lt hS_ne
    have hi_lt : vAngle V hV f i < t := (Finset.mem_filter.mp hi_mem).2
    refine ⟨i, t, ⟨hi_lt, ?_⟩, hcp⟩
    unfold vUpperAngle
    split_ifs with h
    · by_contra hge
      push Not at hge
      have hlt_next : vAngle V hV f ⟨i.1 + 1, h⟩ < t :=
        lt_of_le_of_ne hge (fun h_eq => hnot_range ⟨⟨i.1 + 1, h⟩, h_eq⟩)
      have hmem_next : (⟨i.1 + 1, h⟩ : Fin (V ∩ Θ).ncard) ∈ S_lt :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_next⟩
      have hle_max : (⟨i.1 + 1, h⟩ : Fin (V ∩ Θ).ncard) ≤ i :=
        Finset.le_max' S_lt _ hmem_next
      have hle_val : i.1 + 1 ≤ i.1 := hle_max
      omega
    · have h0_nonneg := (vAngle_mem_Ico V hV f ⟨0, by omega⟩).1
      linarith [ht_Ico.2]

theorem closure_vSpaceArc [T2Space S] (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard)
    (i : Fin (V ∩ Θ).ncard) :
    closure (vSpaceArc V hV f hk i) =
      cuffPoint f '' Icc (vAngle V hV f i) (vUpperAngle V hV f hk i) := by
  have hlt := vAngle_lt_vUpperAngle V hV f hk i
  have hcl_closed : IsClosed (cuffPoint f '' Icc (vAngle V hV f i) (vUpperAngle V hV f hk i)) :=
    (isCompact_Icc.image (cuffPoint_continuous f)).isClosed
  refine Subset.antisymm (closure_minimal (image_mono Ioo_subset_Icc_self) hcl_closed) ?_
  rw [← closure_Ioo (ne_of_lt hlt)]
  exact image_closure_subset_closure_image (cuffPoint_continuous f)

theorem closure_vSpaceArc_eq_union [T2Space S] (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard)
    (i : Fin (V ∩ Θ).ncard) :
    closure (vSpaceArc V hV f hk i) =
      vSpaceArc V hV f hk i ∪ {vNode V hV f i, vNode V hV f (nextFin hk i)} := by
  rw [closure_vSpaceArc V hV f hk i]
  have hlt := vAngle_lt_vUpperAngle V hV f hk i
  ext x
  constructor
  · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
    rcases eq_or_lt_of_le ht1 with rfl | h1
    · exact Or.inr (Or.inl rfl)
    · rcases eq_or_lt_of_le ht2 with rfl | h2
      · rw [cuffPoint_vUpperAngle V hV f hk i]
        exact Or.inr (Or.inr rfl)
      · exact Or.inl ⟨t, ⟨h1, h2⟩, rfl⟩
  · rintro (⟨t, ⟨ht1, ht2⟩, rfl⟩ | rfl | rfl)
    · exact ⟨t, ⟨ht1.le, ht2.le⟩, rfl⟩
    · exact ⟨vAngle V hV f i, ⟨le_rfl, hlt.le⟩, rfl⟩
    · rw [← cuffPoint_vUpperAngle V hV f hk i]
      exact ⟨vUpperAngle V hV f hk i, ⟨hlt.le, le_rfl⟩, rfl⟩

theorem isLineWithEnds_closure_vSpaceArc [T2Space S] (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard)
    (i : Fin (V ∩ Θ).ncard) :
    IsLineWithEnds (closure (vSpaceArc V hV f hk i))
      (vNode V hV f i) (vNode V hV f (nextFin hk i)) := by
  rw [closure_vSpaceArc V hV f hk i, ← cuffPoint_vUpperAngle V hV f hk i]
  exact isLineWithEnds_cuffPoint_Icc f (vAngle_lt_vUpperAngle V hV f hk i)
    (vUpperAngle_lt_add_two_pi V hV f hk i)

end VertexCuffDecomp

/-! ## 3. Characterization of `drawingSpaces Γ` -/

section DrawingSpaces

variable {S : Type w} [TopologicalSpace S]

/-- Canonical homeomorphism `Circle ≃ₜ C` for a cuff `C ∈ cuffs S`. -/
noncomputable def cuffHomeo (hS : IsSurface S) {C : Set S} (hC : C ∈ cuffs S) : Circle ≃ₜ C :=
  Classical.choice ((cuff_statement.{w} S hS).2.2 C hC)

/-- The set of all `vSpaceArc` pieces across all cuffs `C ∈ cuffs S`. -/
def allCuffSpacePieces (hS : IsSurface S) (V : Set S) (hV : V.Finite)
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (V ∩ C).ncard) : Set (Set S) :=
  {s : Set S | ∃ (C : Set S) (hC : C ∈ cuffs S) (i : Fin (V ∩ C).ncard),
    s = vSpaceArc V hV (cuffHomeo hS hC) (hge2 C hC) i}

theorem finite_allCuffSpacePieces (hS : IsSurface S) (V : Set S) (hV : V.Finite)
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (V ∩ C).ncard) :
    (allCuffSpacePieces hS V hV hge2).Finite := by
  have hfin_cuffs : (cuffs S).Finite := (cuff_statement.{w} S hS).2.1
  have heq : allCuffSpacePieces hS V hV hge2 =
      ⋃ C ∈ cuffs S,
        if hC : C ∈ cuffs S then
          Set.range (vSpaceArc V hV (cuffHomeo hS hC) (hge2 C hC))
        else ∅ := by
    ext s
    simp only [allCuffSpacePieces, mem_ofPred_eq, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨C, hC, i, rfl⟩
      exact ⟨C, hC, by simp [hC]⟩
    · rintro ⟨C, hC, hs⟩
      simp only [hC, dite_true, mem_range] at hs
      rcases hs with ⟨i, rfl⟩
      exact ⟨C, hC, i, rfl⟩
  rw [heq]
  refine hfin_cuffs.biUnion fun C hC => ?_
  simp only [hC, dite_true]
  exact Set.finite_range _

theorem componentsIn_bd_diff_eq (hS : IsSurface S) (V : Set S) (hV : V.Finite)
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (V ∩ C).ncard) :
    componentsIn (bd S \ V) = allCuffSpacePieces hS V hV hge2 := by
  have : T2Space S := hS.2.1
  apply componentsIn_of_pieces (finite_allCuffSpacePieces hS V hV hge2)
  · rintro s ⟨C, hC, i, rfl⟩
    exact (isPathConnected_vSpaceArc V hV (cuffHomeo hS hC) (hge2 C hC) i).isConnected
  · rintro s₁ ⟨C₁, hC₁, i₁, rfl⟩ s₂ ⟨C₂, hC₂, i₂, rfl⟩ hne
    by_cases hC_eq : C₁ = C₂
    · subst hC_eq
      have hi_ne : i₁ ≠ i₂ := fun h => hne (h ▸ rfl)
      exact disjoint_vSpaceArc V hV (cuffHomeo hS hC₁) (hge2 C₁ hC₁) hi_ne
    · refine Disjoint.mono ?_ ?_ (cuffs_disjoint hC₁ hC₂ hC_eq)
      · exact (vSpaceArc_subset_diff V hV _ _ i₁).trans sdiff_subset
      · exact (vSpaceArc_subset_diff V hV _ _ i₂).trans sdiff_subset
  · rintro s ⟨C, hC, i, rfl⟩ x ⟨hx_cl, hx_bd, hx_notV⟩
    rw [closure_vSpaceArc_eq_union V hV (cuffHomeo hS hC) (hge2 C hC) i] at hx_cl
    rcases hx_cl with hx_s | rfl | rfl
    · exact hx_s
    · exact (hx_notV (vNode_mem V hV (cuffHomeo hS hC) i).1).elim
    · exact (hx_notV (vNode_mem V hV (cuffHomeo hS hC) (nextFin (hge2 C hC) i)).1).elim
  · ext x
    simp only [mem_sUnion, allCuffSpacePieces, mem_ofPred_eq]
    constructor
    · rintro ⟨hx_bd, hx_notV⟩
      rw [← sUnion_cuffs (S := S), mem_sUnion] at hx_bd
      rcases hx_bd with ⟨C, hC, hxC⟩
      have hx_diff : x ∈ C \ V := ⟨hxC, hx_notV⟩
      rw [← iUnion_vSpaceArc V hV (cuffHomeo hS hC) (hge2 C hC), mem_iUnion] at hx_diff
      rcases hx_diff with ⟨i, hxi⟩
      exact ⟨_, ⟨C, hC, i, rfl⟩, hxi⟩
    · rintro ⟨s, ⟨C, hC, i, rfl⟩, hxs⟩
      have hx_diff := vSpaceArc_subset_diff V hV (cuffHomeo hS hC) (hge2 C hC) i hxs
      refine ⟨?_, hx_diff.2⟩
      rw [← sUnion_cuffs (S := S), mem_sUnion]
      exact ⟨C, hC, hx_diff.1⟩

theorem componentsIn_cuff_diff_eq (hS : IsSurface S) (V : Set S) (hV : V.Finite)
    {C : Set S} (_hC : C ∈ cuffs S) (f : Circle ≃ₜ C) (hk : 2 ≤ (V ∩ C).ncard) :
    componentsIn (C \ V) = Set.range (vSpaceArc V hV f hk) := by
  have : T2Space S := hS.2.1
  apply componentsIn_of_pieces (Set.finite_range _)
  · rintro s ⟨i, rfl⟩
    exact (isPathConnected_vSpaceArc V hV f hk i).isConnected
  · rintro s₁ ⟨i₁, rfl⟩ s₂ ⟨i₂, rfl⟩ hne
    have hi_ne : i₁ ≠ i₂ := fun h => hne (h ▸ rfl)
    exact disjoint_vSpaceArc V hV f hk hi_ne
  · rintro s ⟨i, rfl⟩ x ⟨hx_cl, _, hx_notV⟩
    rw [closure_vSpaceArc_eq_union V hV f hk i] at hx_cl
    rcases hx_cl with hx_s | rfl | rfl
    · exact hx_s
    · exact (hx_notV (vNode_mem V hV f i).1).elim
    · exact (hx_notV (vNode_mem V hV f (nextFin hk i)).1).elim
  · ext x
    simp only [mem_sUnion, mem_range, exists_exists_eq_and]
    rw [← mem_iUnion, iUnion_vSpaceArc V hV f hk]

theorem vSpaceArc_mem_componentsIn_bd_diff (hS : IsSurface S) (V : Set S) (hV : V.Finite)
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (V ∩ C).ncard) {C : Set S} (hC : C ∈ cuffs S)
    (f : Circle ≃ₜ C) (i : Fin (V ∩ C).ncard) :
    vSpaceArc V hV f (hge2 C hC) i ∈ componentsIn (bd S \ V) := by
  have hmem_C : vSpaceArc V hV f (hge2 C hC) i ∈ componentsIn (C \ V) := by
    rw [componentsIn_cuff_diff_eq hS V hV hC f (hge2 C hC)]
    exact mem_range_self i
  have hmem_C' : componentsIn (C \ V) =
      Set.range (vSpaceArc V hV (cuffHomeo hS hC) (hge2 C hC)) :=
    componentsIn_cuff_diff_eq hS V hV hC (cuffHomeo hS hC) (hge2 C hC)
  rw [hmem_C'] at hmem_C
  rcases hmem_C with ⟨j, hj⟩
  rw [componentsIn_bd_diff_eq hS V hV hge2]
  exact ⟨C, hC, j, hj.symm⟩

theorem drawingSpaces_finite (hS : IsSurface S) {Γ : Surface.Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) :
    (drawingSpaces Γ).Finite := by
  unfold drawingSpaces
  rw [componentsIn_bd_diff_eq hS Γ.V Γ.finite_V hge2]
  exact finite_allCuffSpacePieces hS Γ.V Γ.finite_V hge2

theorem exists_cuff_of_mem_drawingSpaces (hS : IsSurface S) {Γ : Surface.Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) {s : Set S} (hs : s ∈ drawingSpaces Γ) :
    ∃ C ∈ cuffs S, s ⊆ C ∧ s.Nonempty := by
  unfold drawingSpaces at hs
  rw [componentsIn_bd_diff_eq hS Γ.V Γ.finite_V hge2] at hs
  rcases hs with ⟨C, hC, i, rfl⟩
  exact ⟨C, hC, (vSpaceArc_subset_diff Γ.V Γ.finite_V _ _ i).trans sdiff_subset,
    ⟨_, vMidpoint_mem_vSpaceArc Γ.V Γ.finite_V _ _ i⟩⟩

theorem exists_index_of_mem_drawingSpaces_subset_cuff (hS : IsSurface S) {Γ : Surface.Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) {s C : Set S}
    (hs : s ∈ drawingSpaces Γ) (hC : C ∈ cuffs S) (hsC : s ⊆ C) (f : Circle ≃ₜ C) :
    ∃ i : Fin (Γ.V ∩ C).ncard, s = vSpaceArc Γ.V Γ.finite_V f (hge2 C hC) i := by
  unfold drawingSpaces at hs
  rw [componentsIn_bd_diff_eq hS Γ.V Γ.finite_V hge2] at hs
  rcases hs with ⟨C'', hC'', j, rfl⟩
  have hmid := vMidpoint_mem_vSpaceArc Γ.V Γ.finite_V (cuffHomeo hS hC'') (hge2 C'' hC'') j
  have hC''_eq : C'' = C := by
    by_contra hne
    exact Set.disjoint_left.mp (cuffs_disjoint hC'' hC hne)
      ((vSpaceArc_subset_diff Γ.V Γ.finite_V _ _ j hmid).1) (hsC hmid)
  subst hC''_eq
  have hmem : vSpaceArc Γ.V Γ.finite_V (cuffHomeo hS hC'') (hge2 C'' hC'') j ∈
      componentsIn (C'' \ Γ.V) := by
    rw [componentsIn_cuff_diff_eq hS Γ.V Γ.finite_V hC'' (cuffHomeo hS hC'') (hge2 C'' hC'')]
    exact mem_range_self j
  rw [componentsIn_cuff_diff_eq hS Γ.V Γ.finite_V hC f (hge2 C'' hC)] at hmem
  rcases hmem with ⟨i, hi⟩
  exact ⟨i, hi.symm⟩

theorem spaceHasEnds_vSpaceArc (hS : IsSurface S) {Γ : Surface.Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) {C : Set S} (hC : C ∈ cuffs S)
    (f : Circle ≃ₜ C) (i : Fin (Γ.V ∩ C).ncard) :
    SpaceHasEnds Γ (vSpaceArc Γ.V Γ.finite_V f (hge2 C hC) i)
      (vNode Γ.V Γ.finite_V f i) (vNode Γ.V Γ.finite_V f (nextFin (hge2 C hC) i)) := by
  have : T2Space S := hS.2.1
  have hk := hge2 C hC
  have hC_sub_bd : C ⊆ bd S := by
    intro x hx
    rw [← sUnion_cuffs (S := S)]
    exact ⟨C, hC, hx⟩
  have hn1 := vNode_mem Γ.V Γ.finite_V f i
  have hn2 := vNode_mem Γ.V Γ.finite_V f (nextFin hk i)
  have hne : vNode Γ.V Γ.finite_V f i ≠ vNode Γ.V Γ.finite_V f (nextFin hk i) :=
    fun h => ne_nextFin hk i (injective_vNode Γ.V Γ.finite_V f h)
  have hcl := closure_vSpaceArc_eq_union Γ.V Γ.finite_V f hk i
  have hline := isLineWithEnds_closure_vSpaceArc Γ.V Γ.finite_V f hk i
  rw [hcl] at hline
  exact ⟨vSpaceArc_mem_componentsIn_bd_diff hS Γ.V Γ.finite_V hge2 hC f i,
    ⟨hn1.1, hC_sub_bd hn1.2⟩, ⟨hn2.1, hC_sub_bd hn2.2⟩, hne, hline, hcl⟩

theorem exists_spaceHasEnds_of_mem_drawingSpaces (hS : IsSurface S) {Γ : Surface.Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) {s : Set S} (hs : s ∈ drawingSpaces Γ) :
    ∃ u₁ u₂ : S, SpaceHasEnds Γ s u₁ u₂ := by
  obtain ⟨C, hC, hsC, _⟩ := exists_cuff_of_mem_drawingSpaces hS hge2 hs
  obtain ⟨i, rfl⟩ := exists_index_of_mem_drawingSpaces_subset_cuff hS hge2 hs hC hsC
    (cuffHomeo hS hC)
  exact ⟨_, _, spaceHasEnds_vSpaceArc hS hge2 hC (cuffHomeo hS hC) i⟩

theorem closure_diff_eq_of_spaceHasEnds {Γ : Surface.Drawing S} {s : Set S} {u₁ u₂ : S}
    (h : SpaceHasEnds Γ s u₁ u₂) :
    closure s \ s = {u₁, u₂} := by
  have hs_sub : s ⊆ bd S \ Γ.V := by
    rcases h.1 with ⟨x, hx, rfl⟩
    exact connectedComponentIn_subset _ _
  rw [h.2.2.2.2.2]
  ext x
  simp only [mem_sdiff, mem_union, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hxs | rfl | rfl, hnot_s⟩
    · exact (hnot_s hxs).elim
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Or.inr (Or.inl rfl), fun hxs => (hs_sub hxs).2 h.2.1.1⟩
    · exact ⟨Or.inr (Or.inr rfl), fun hxs => (hs_sub hxs).2 h.2.2.1.1⟩

theorem ends_pair_eq_of_spaceHasEnds {Γ : Surface.Drawing S} {s : Set S} {u₁ u₂ u₁' u₂' : S}
    (h : SpaceHasEnds Γ s u₁ u₂) (h' : SpaceHasEnds Γ s u₁' u₂') :
    ({u₁, u₂} : Set S) = {u₁', u₂'} := by
  rw [← closure_diff_eq_of_spaceHasEnds h, closure_diff_eq_of_spaceHasEnds h']

theorem isConnected_of_mem_drawingSpaces {Γ : Surface.Drawing S} {s : Set S}
    (hs : s ∈ drawingSpaces Γ) : IsConnected s := by
  rcases hs with ⟨x, hx, rfl⟩
  exact ⟨⟨x, mem_connectedComponentIn hx⟩, isPreconnected_connectedComponentIn⟩

theorem subset_bd_diff_of_mem_drawingSpaces {Γ : Surface.Drawing S} {s : Set S}
    (hs : s ∈ drawingSpaces Γ) : s ⊆ bd S \ Γ.V := by
  rcases hs with ⟨x, hx, rfl⟩
  exact connectedComponentIn_subset _ _

end DrawingSpaces

/-! ## 4. Supports and Interval Representations -/

section SupportsAndIntervals

variable {S : Type w} [TopologicalSpace S]

theorem cuff_diff_cuffPoint_Icc {Θ : Set S} (f : Circle ≃ₜ Θ) {t₀ t₁ : ℝ}
    (hle : t₀ ≤ t₁) (hlt : t₁ < t₀ + 2 * Real.pi) :
    Θ \ (cuffPoint f '' Icc t₀ t₁) = cuffPoint f '' Ioo t₁ (t₀ + 2 * Real.pi) := by
  ext x
  constructor
  · rintro ⟨hxΘ, hx_not⟩
    obtain ⟨t, ht, rfl⟩ := exists_cuffPoint_mem_Ico f t₀ hxΘ
    have ht_gt : t₁ < t := by
      by_contra hle'
      push Not at hle'
      exact hx_not ⟨t, ⟨ht.1, hle'⟩, rfl⟩
    exact ⟨t, ⟨ht_gt, ht.2⟩, rfl⟩
  · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
    refine ⟨cuffPoint_mem f t, ?_⟩
    rintro ⟨s, ⟨hs1, hs2⟩, h_eq⟩
    have hs_Ico : s ∈ Ico t₀ (t₀ + 2 * Real.pi) := ⟨hs1, hs2.trans_lt hlt⟩
    have ht_Ico : t ∈ Ico t₀ (t₀ + 2 * Real.pi) := ⟨(hle.trans_lt ht1).le, ht2⟩
    have hst := cuffPoint_injOn_Ico f t₀ hs_Ico ht_Ico h_eq
    linarith

theorem ends_mem_of_supportHasEnds {Γ : Surface.Drawing S} {F : Set S} {a b : S}
    (h : SupportHasEnds Γ F a b) :
    a ∈ F ∧ b ∈ F ∧ a ∈ Γ.V ∩ bd S ∧ b ∈ Γ.V ∩ bd S ∧ F ⊆ bd S := by
  rcases h with ⟨v, hv, rfl, rfl, rfl⟩ | ⟨hsub, _, ha, hb, hline⟩
  · exact ⟨rfl, rfl, hv, hv, singleton_subset_iff.mpr hv.2⟩
  · exact ⟨hline.left_mem, hline.right_mem, ha, hb, hsub⟩

theorem isClosed_of_supportHasEnds (hS : IsSurface S) {Γ : Surface.Drawing S} {F : Set S} {a b : S}
    (h : SupportHasEnds Γ F a b) : IsClosed F := by
  have : T2Space S := hS.2.1
  rcases h with ⟨v, _, rfl, _, _⟩ | ⟨_, _, _, _, hline⟩
  · exact isClosed_singleton
  · exact hline.isCompact.isClosed

theorem isClosed_of_isSupportOfDrawing (hS : IsSurface S) {Γ : Surface.Drawing S} {F : Set S}
    (h : IsSupportOfDrawing Γ F) : IsClosed F := by
  rcases h with ⟨a, b, hab⟩
  exact isClosed_of_supportHasEnds hS hab

theorem isConnected_of_supportHasEnds {Γ : Surface.Drawing S} {F : Set S} {a b : S}
    (h : SupportHasEnds Γ F a b) : IsConnected F := by
  rcases h with ⟨v, _, rfl, _, _⟩ | ⟨_, _, _, _, hline⟩
  · exact isConnected_singleton
  · refine ⟨⟨a, hline.left_mem⟩, ?_⟩
    obtain ⟨φ, hφ, hrange, -, -⟩ := hline.exists_arc
    rw [← hrange]
    exact isPreconnected_range hφ.1

theorem isConnected_of_isSupportOfDrawing {Γ : Surface.Drawing S} {F : Set S}
    (h : IsSupportOfDrawing Γ F) : IsConnected F := by
  rcases h with ⟨a, b, hab⟩
  exact isConnected_of_supportHasEnds hab

theorem subset_bd_of_isSupportOfDrawing {Γ : Surface.Drawing S} {F : Set S}
    (h : IsSupportOfDrawing Γ F) : F ⊆ bd S := by
  rcases h with ⟨a, b, hab⟩
  exact (ends_mem_of_supportHasEnds hab).2.2.2.2

theorem exists_cuff_of_supportHasEnds {Γ : Surface.Drawing S} {F : Set S} {a b : S}
    (h : SupportHasEnds Γ F a b) : ∃ C ∈ cuffs S, F ⊆ C := by
  have hends := ends_mem_of_supportHasEnds h
  have hconn := isConnected_of_supportHasEnds h
  refine ⟨connectedComponentIn (bd S) a, ⟨a, hends.2.2.1.2, rfl⟩, ?_⟩
  exact hconn.isPreconnected.subset_connectedComponentIn hends.1 hends.2.2.2.2

theorem exists_cuff_of_isSupportOfDrawing {Γ : Surface.Drawing S} {F : Set S}
    (h : IsSupportOfDrawing Γ F) : ∃ C ∈ cuffs S, F ⊆ C ∧ F.Nonempty := by
  rcases h with ⟨a, b, hab⟩
  obtain ⟨C, hC, hFC⟩ := exists_cuff_of_supportHasEnds hab
  exact ⟨C, hC, hFC, ⟨a, (ends_mem_of_supportHasEnds hab).1⟩⟩

/-- For any space `s ∈ drawingSpaces Γ` and any support `F` of `Γ`, either `s ⊆ F` (and hence
`closure s ⊆ F`) or `Disjoint s F`. -/
theorem space_subset_or_disjoint_of_supportHasEnds (hS : IsSurface S) {Γ : Surface.Drawing S}
    {s F : Set S} {a b : S} (hs : s ∈ drawingSpaces Γ) (hF : SupportHasEnds Γ F a b) :
    (s ⊆ F ∧ closure s ⊆ F) ∨ Disjoint s F := by
  have : T2Space S := hS.2.1
  by_cases hdisj : Disjoint s F
  · exact Or.inr hdisj
  · left
    rw [not_disjoint_iff] at hdisj
    rcases hdisj with ⟨x₀, hx₀s, hx₀F⟩
    have hs_sub := subset_bd_diff_of_mem_drawingSpaces hs
    rcases hF with ⟨v, hv, rfl, _, _⟩ | ⟨hF_bd, hab, ha, hb, hline⟩
    · exfalso
      have : x₀ = v := mem_singleton_iff.mp hx₀F
      subst this
      exact (hs_sub hx₀s).2 hv.1
    · obtain ⟨C, hC, hFC⟩ := exists_cuff_of_supportHasEnds (Or.inr ⟨hF_bd, hab, ha, hb, hline⟩)
      have hC_arc : IsOArc C := (cuff_statement.{w} S hS).2.2 C hC
      obtain ⟨F', hline', hu, hi⟩ := oarc_split_univ hC_arc hline hFC
      have hsC : s ⊆ C := by
        rcases hs with ⟨y, hy, rfl⟩
        have hx₀_comp : x₀ ∈ connectedComponentIn (bd S \ Γ.V) y := hx₀s
        have hconn_s : IsPreconnected (connectedComponentIn (bd S \ Γ.V) y) :=
          isPreconnected_connectedComponentIn
        have hC_eq : C = connectedComponentIn (bd S) x₀ := by
          rcases hC with ⟨z, hz, rfl⟩
          exact connectedComponentIn_eq (hFC hx₀F)
        rw [hC_eq]
        exact hconn_s.subset_connectedComponentIn hx₀_comp
          (connectedComponentIn_subset (bd S \ Γ.V) y |>.trans sdiff_subset)
      have hs_cov : s ⊆ F ∪ F' := hu ▸ hsC
      have hs_not_ab : Disjoint s (F ∩ F') := by
        rw [hi, disjoint_iff_inter_eq_empty]
        ext z
        simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, mem_empty_iff_false,
          iff_false, not_and]
        rintro hzs (rfl | rfl)
        · exact (hs_sub hzs).2 ha.1
        · exact (hs_sub hzs).2 hb.1
      have hcF : IsClosed F := hline.isCompact.isClosed
      have hcF' : IsClosed F' := hline'.isCompact.isClosed
      have hs_sub_F : s ⊆ F := by
        by_contra hnot
        obtain ⟨z, hzs, hz_notF⟩ := not_subset.mp hnot
        have hzF' : z ∈ F' := (hs_cov hzs).resolve_left hz_notF
        have hpre := (isConnected_of_mem_drawingSpaces hs).isPreconnected
        obtain ⟨w, hws, hwF, hwF'⟩ := isPreconnected_closed_iff.mp hpre F F' hcF hcF' hs_cov
          ⟨x₀, hx₀s, hx₀F⟩ ⟨z, hzs, hzF'⟩
        exact Set.disjoint_left.mp hs_not_ab hws ⟨hwF, hwF'⟩
      exact ⟨hs_sub_F, closure_minimal hs_sub_F hcF⟩

theorem space_subset_or_disjoint_of_isSupportOfDrawing (hS : IsSurface S) {Γ : Surface.Drawing S}
    {s F : Set S} (hs : s ∈ drawingSpaces Γ) (hF : IsSupportOfDrawing Γ F) :
    (s ⊆ F ∧ closure s ⊆ F) ∨ Disjoint s F := by
  rcases hF with ⟨a, b, hab⟩
  exact space_subset_or_disjoint_of_supportHasEnds hS hs hab

/-- Every support `F` on a cuff `C` with ends `a, b` (`SupportHasEnds Γ F a b`) can be represented
as `cuffPoint f '' Icc t₀ t₁` for some `t₀ ∈ Ico 0 (2 * Real.pi)` and `t₁ ∈ Ico t₀ (t₀ + 2 * Real.pi)`
whose images are `{a, b}`. -/
theorem support_eq_cuffPoint_Icc (hS : IsSurface S) {Γ : Surface.Drawing S}
    {C F : Set S} {a b : S} (hC : C ∈ cuffs S) (f : Circle ≃ₜ C)
    (hF : SupportHasEnds Γ F a b) (hFC : F ⊆ C) :
    ∃ t₀ ∈ Ico (0 : ℝ) (0 + 2 * Real.pi), ∃ t₁ ∈ Ico t₀ (t₀ + 2 * Real.pi),
      ((cuffPoint f t₀ = a ∧ cuffPoint f t₁ = b) ∨
       (cuffPoint f t₀ = b ∧ cuffPoint f t₁ = a)) ∧
      F = cuffPoint f '' Icc t₀ t₁ ∧
      C \ F = cuffPoint f '' Ioo t₁ (t₀ + 2 * Real.pi) := by
  have : T2Space S := hS.2.1
  have hpi := Real.pi_pos
  rcases hF with ⟨v, hv, rfl, ha_eq, hb_eq⟩ | ⟨hF_bd, hab, ha, hb, hline⟩
  · have hvC : v ∈ C := hFC (mem_singleton v)
    obtain ⟨t₀, ht₀, hv_eq⟩ := exists_cuffPoint_mem_Ico f 0 hvC
    have hF_eq : ({v} : Set S) = cuffPoint f '' Icc t₀ t₀ := by
      rw [Icc_self, image_singleton, hv_eq]
    refine ⟨t₀, ht₀, t₀, ⟨le_rfl, by linarith⟩,
      Or.inl ⟨hv_eq.trans ha_eq.symm, hv_eq.trans hb_eq.symm⟩, hF_eq, ?_⟩
    rw [hF_eq]
    exact cuff_diff_cuffPoint_Icc f le_rfl (by linarith)
  · have haC : a ∈ C := hFC hline.left_mem
    have hbC : b ∈ C := hFC hline.right_mem
    obtain ⟨ua, hua, ha_eq⟩ := exists_cuffPoint_mem_Ico f 0 haC
    obtain ⟨ub, hub, hb_eq⟩ := exists_cuffPoint_mem_Ico f 0 hbC
    have hu_ne : ua ≠ ub := fun h => hab (by rw [← ha_eq, ← hb_eq, h])
    have hC_arc : IsOArc C := (cuff_statement.{w} S hS).2.2 C hC
    obtain ⟨F', hline', hu, hi⟩ := oarc_split_univ hC_arc hline hFC
    rcases lt_or_gt_of_ne hu_ne with hlt | hgt
    · have hline_u : IsLineWithEnds F (cuffPoint f ua) (cuffPoint f ub) := by
        rwa [ha_eq, hb_eq]
      have hline'_u : IsLineWithEnds F' (cuffPoint f ua) (cuffPoint f ub) := by
        rwa [ha_eq, hb_eq]
      have hi_u : F ∩ F' = {cuffPoint f ua, cuffPoint f ub} := by
        rwa [ha_eq, hb_eq]
      have hcir := circle_lines_univ f hlt (by linarith [hua.1, hub.2]) hline_u hline'_u hu hi_u
      rcases hcir.2 with ⟨hF_eq, _⟩ | ⟨hF_eq, _⟩
      · refine ⟨ua, hua, ub, ⟨hlt.le, by linarith [hua.1, hub.2]⟩,
          Or.inl ⟨ha_eq, hb_eq⟩, hF_eq, ?_⟩
        rw [hF_eq]
        exact cuff_diff_cuffPoint_Icc f hlt.le (by linarith [hua.1, hub.2])
      · refine ⟨ub, hub, ua + 2 * Real.pi, ⟨by linarith [hua.1, hub.2], by linarith [hlt]⟩,
          Or.inr ⟨hb_eq, by rw [cuffPoint_add_two_pi, ha_eq]⟩, hF_eq, ?_⟩
        rw [hF_eq]
        exact cuff_diff_cuffPoint_Icc f (by linarith [hua.1, hub.2]) (by linarith [hlt])
    · have hline_symm : IsLineWithEnds F b a := hline.symm
      have hline'_symm : IsLineWithEnds F' b a := hline'.symm
      have hline_u : IsLineWithEnds F (cuffPoint f ub) (cuffPoint f ua) := by
        rwa [hb_eq, ha_eq]
      have hline'_u : IsLineWithEnds F' (cuffPoint f ub) (cuffPoint f ua) := by
        rwa [hb_eq, ha_eq]
      have hi_u : F ∩ F' = {cuffPoint f ub, cuffPoint f ua} := by
        rw [hi, pair_comm, hb_eq, ha_eq]
      have hcir := circle_lines_univ f hgt (by linarith [hub.1, hua.2]) hline_u hline'_u hu hi_u
      rcases hcir.2 with ⟨hF_eq, _⟩ | ⟨hF_eq, _⟩
      · refine ⟨ub, hub, ua, ⟨hgt.le, by linarith [hub.1, hua.2]⟩,
          Or.inr ⟨hb_eq, ha_eq⟩, hF_eq, ?_⟩
        rw [hF_eq]
        exact cuff_diff_cuffPoint_Icc f hgt.le (by linarith [hub.1, hua.2])
      · refine ⟨ua, hua, ub + 2 * Real.pi, ⟨by linarith [hub.1, hua.2], by linarith [hgt]⟩,
          Or.inl ⟨ha_eq, by rw [cuffPoint_add_two_pi, hb_eq]⟩, hF_eq, ?_⟩
        rw [hF_eq]
        exact cuff_diff_cuffPoint_Icc f (by linarith [hub.1, hua.2]) (by linarith [hgt])

/-- Relative to any angle `t₀ : ℝ` of a vertex `cuffPoint f t₀ ∈ Γ.V ∩ C`, every space
`s = vSpaceArc Γ.V Γ.finite_V f hk i` on `C` has a unique interval representation `Ioo a' b'`
with `t₀ ≤ a' < b' ≤ t₀ + 2 * Real.pi`. -/
theorem vSpaceArc_eq_Ioo_from_vertex_angle (hS : IsSurface S) {Γ : Surface.Drawing S}
    {C : Set S} (_hC : C ∈ cuffs S) (f : Circle ≃ₜ C) (hk : 2 ≤ (Γ.V ∩ C).ncard)
    {t₀ : ℝ} (ht₀ : cuffPoint f t₀ ∈ Γ.V ∩ C) (i : Fin (Γ.V ∩ C).ncard) :
    ∃ a' b' : ℝ,
      t₀ ≤ a' ∧ a' < b' ∧ b' ≤ t₀ + 2 * Real.pi ∧
      cuffPoint f a' = vNode Γ.V Γ.finite_V f i ∧
      cuffPoint f b' = vNode Γ.V Γ.finite_V f (nextFin hk i) ∧
      vSpaceArc Γ.V Γ.finite_V f hk i = cuffPoint f '' Ioo a' b' ∧
      closure (vSpaceArc Γ.V Γ.finite_V f hk i) = cuffPoint f '' Icc a' b' := by
  have : T2Space S := hS.2.1
  set a := vAngle Γ.V Γ.finite_V f i
  set b := vUpperAngle Γ.V Γ.finite_V f hk i
  have hab : a < b := vAngle_lt_vUpperAngle Γ.V Γ.finite_V f hk i
  have hb_lt : b < a + 2 * Real.pi := vUpperAngle_lt_add_two_pi Γ.V Γ.finite_V f hk i
  obtain ⟨t₀', ht₀'_Ico, ht₀'_eq⟩ := exists_cuffPoint_mem_Ico f a ht₀.2
  have ht₀'_not_Ioo : t₀' ∉ Ioo a b := by
    intro hmem
    have hx_arc : cuffPoint f t₀ ∈ vSpaceArc Γ.V Γ.finite_V f hk i := by
      rw [← ht₀'_eq]
      exact ⟨t₀', hmem, rfl⟩
    exact (vSpaceArc_subset_diff Γ.V Γ.finite_V f hk i hx_arc).2 ht₀.1
  have ht₀'_ge_b_or_eq_a : t₀' = a ∨ b ≤ t₀' := by
    rcases eq_or_lt_of_le ht₀'_Ico.1 with h_eq | h_lt
    · exact Or.inl h_eq.symm
    · right
      by_contra h_lt_b
      push Not at h_lt_b
      exact ht₀'_not_Ioo ⟨h_lt, h_lt_b⟩
  obtain ⟨m, hm⟩ := (cuffPoint_eq_iff f).mp ht₀'_eq
  have hshift_Ioo : ∀ k : ℤ,
      cuffPoint f '' Ioo (a + k * (2 * Real.pi)) (b + k * (2 * Real.pi)) =
        cuffPoint f '' Ioo a b := by
    intro k
    ext x
    constructor
    · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
      refine ⟨t - k * (2 * Real.pi), ⟨by linarith, by linarith⟩, ?_⟩
      exact (cuffPoint_eq_iff f).mpr ⟨-k, by push_cast; ring⟩
    · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
      refine ⟨t + k * (2 * Real.pi), ⟨by linarith, by linarith⟩, ?_⟩
      exact (cuffPoint_eq_iff f).mpr ⟨k, by ring⟩
  have hshift_Icc : ∀ k : ℤ,
      cuffPoint f '' Icc (a + k * (2 * Real.pi)) (b + k * (2 * Real.pi)) =
        cuffPoint f '' Icc a b := by
    intro k
    ext x
    constructor
    · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
      refine ⟨t - k * (2 * Real.pi), ⟨by linarith, by linarith⟩, ?_⟩
      exact (cuffPoint_eq_iff f).mpr ⟨-k, by push_cast; ring⟩
    · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
      refine ⟨t + k * (2 * Real.pi), ⟨by linarith, by linarith⟩, ?_⟩
      exact (cuffPoint_eq_iff f).mpr ⟨k, by ring⟩
  rcases ht₀'_ge_b_or_eq_a with rfl | hb_le
  · refine ⟨a - m * (2 * Real.pi), b - m * (2 * Real.pi),
      by linarith, by linarith, by linarith, ?_, ?_, ?_, ?_⟩
    · exact (cuffPoint_eq_iff f).mpr ⟨-m, by push_cast; ring⟩
    · rw [← cuffPoint_vUpperAngle Γ.V Γ.finite_V f hk i]
      exact (cuffPoint_eq_iff f).mpr ⟨-m, by push_cast; ring⟩
    · unfold vSpaceArc
      have h := hshift_Ioo (-m)
      push_cast at h
      have ha_eq : a + -m * (2 * Real.pi) = a - m * (2 * Real.pi) := by ring
      have hb_eq : b + -m * (2 * Real.pi) = b - m * (2 * Real.pi) := by ring
      rw [ha_eq, hb_eq] at h
      exact h.symm
    · rw [closure_vSpaceArc Γ.V Γ.finite_V f hk i]
      have h := hshift_Icc (-m)
      push_cast at h
      have ha_eq : a + -m * (2 * Real.pi) = a - m * (2 * Real.pi) := by ring
      have hb_eq : b + -m * (2 * Real.pi) = b - m * (2 * Real.pi) := by ring
      rw [ha_eq, hb_eq] at h
      exact h.symm
  · refine ⟨a + (1 - m) * (2 * Real.pi), b + (1 - m) * (2 * Real.pi),
      by linarith [ht₀'_Ico.2], by linarith, by linarith, ?_, ?_, ?_, ?_⟩
    · exact (cuffPoint_eq_iff f).mpr ⟨1 - m, by push_cast; ring⟩
    · rw [← cuffPoint_vUpperAngle Γ.V Γ.finite_V f hk i]
      exact (cuffPoint_eq_iff f).mpr ⟨1 - m, by push_cast; ring⟩
    · unfold vSpaceArc
      have h := hshift_Ioo (1 - m)
      push_cast at h
      exact h.symm
    · rw [closure_vSpaceArc Γ.V Γ.finite_V f hk i]
      have h := hshift_Icc (1 - m)
      push_cast at h
      exact h.symm

/-- If `s = cuffPoint f '' Ioo a' b'` with `t₀ ≤ a' < b' ≤ t₀ + 2 * Real.pi` is contained in
`cuffPoint f '' Icc t₀ t₁` (`t₀ ≤ t₁ < t₀ + 2 * Real.pi`), then `b' ≤ t₁`. -/
theorem right_end_le_of_Ioo_subset_Icc {Θ : Set S} (f : Circle ≃ₜ Θ)
    {t₀ t₁ a' b' : ℝ} (_hle : t₀ ≤ t₁) (hlt : t₁ < t₀ + 2 * Real.pi)
    (ha' : t₀ ≤ a') (hab' : a' < b') (hb' : b' ≤ t₀ + 2 * Real.pi)
    (hsub : cuffPoint f '' Ioo a' b' ⊆ cuffPoint f '' Icc t₀ t₁) :
    b' ≤ t₁ := by
  by_contra hgt
  push Not at hgt
  set m := (max t₁ a' + b') / 2 with hm_def
  have hm_Ioo : m ∈ Ioo a' b' := ⟨by linarith [le_max_right t₁ a'], by linarith [max_lt hgt hab']⟩
  have hm_mem := hsub ⟨m, hm_Ioo, rfl⟩
  rcases hm_mem with ⟨s, ⟨hs1, hs2⟩, h_eq⟩
  have hs_Ico : s ∈ Ico t₀ (t₀ + 2 * Real.pi) := ⟨hs1, hs2.trans_lt hlt⟩
  have hm_Ico : m ∈ Ico t₀ (t₀ + 2 * Real.pi) :=
    ⟨by linarith [le_max_right t₁ a'], by linarith [max_lt hgt hab']⟩
  have hsm := cuffPoint_injOn_Ico f t₀ hs_Ico hm_Ico h_eq
  linarith [le_max_left t₁ a']

/-- If `s = cuffPoint f '' Ioo a' b'` with `t₀ ≤ a' < b' ≤ t₀ + 2 * Real.pi` is disjoint from
`cuffPoint f '' Icc t₀ t₁` (`t₀ ≤ t₁ < t₀ + 2 * Real.pi`), then `t₁ ≤ a'`. -/
theorem left_end_ge_of_Ioo_disjoint_Icc {Θ : Set S} (f : Circle ≃ₜ Θ)
    {t₀ t₁ a' b' : ℝ} (_hle : t₀ ≤ t₁) (_hlt : t₁ < t₀ + 2 * Real.pi)
    (ha' : t₀ ≤ a') (hab' : a' < b') (_hb' : b' ≤ t₀ + 2 * Real.pi)
    (hdisj : Disjoint (cuffPoint f '' Ioo a' b') (cuffPoint f '' Icc t₀ t₁)) :
    t₁ ≤ a' := by
  by_contra hlt'
  push Not at hlt'
  set m := (a' + min t₁ b') / 2 with hm_def
  have hm_Ioo : m ∈ Ioo a' b' := ⟨by linarith [lt_min hlt' hab'], by linarith [min_le_right t₁ b']⟩
  have hm_Icc : m ∈ Icc t₀ t₁ := ⟨by linarith [lt_min hlt' hab'], by linarith [min_le_left t₁ b']⟩
  exact Set.disjoint_left.mp hdisj ⟨m, hm_Ioo, rfl⟩ ⟨m, hm_Icc, rfl⟩

/-- Any sub-interval `cuffPoint f '' Icc α β` (`t₀ ≤ α ≤ β ≤ t₁ < t₀ + 2π`) whose endpoints lie in
`Γ.V` is a support of `Γ` with ends `cuffPoint f α` and `cuffPoint f β`. -/
theorem supportHasEnds_cuffPoint_Icc (hS : IsSurface S) {Γ : Surface.Drawing S}
    {C : Set S} (hC : C ∈ cuffs S) (f : Circle ≃ₜ C)
    {t₀ t₁ α β : ℝ} (ht₀ : t₀ ≤ α) (hαβ : α ≤ β) (hβ : β ≤ t₁) (ht₁ : t₁ < t₀ + 2 * Real.pi)
    (hαV : cuffPoint f α ∈ Γ.V) (hβV : cuffPoint f β ∈ Γ.V) :
    SupportHasEnds Γ (cuffPoint f '' Icc α β) (cuffPoint f α) (cuffPoint f β) := by
  have : T2Space S := hS.2.1
  have hC_bd : C ⊆ bd S := fun z hz => by
    rw [← sUnion_cuffs (S := S)]
    exact ⟨C, hC, hz⟩
  rcases eq_or_lt_of_le hαβ with rfl | hlt
  · left
    refine ⟨cuffPoint f α, ⟨hαV, hC_bd (cuffPoint_mem f α)⟩, ?_, rfl, rfl⟩
    rw [Icc_self, image_singleton]
  · right
    have hlt_2pi : β < α + 2 * Real.pi := by linarith
    have hne : cuffPoint f α ≠ cuffPoint f β := by
      intro h_eq
      have h := cuffPoint_injOn_Ico f t₀ ⟨ht₀, by linarith⟩ ⟨ht₀.trans hlt.le, by linarith⟩ h_eq
      linarith
    refine ⟨?_, hne, ⟨hαV, hC_bd (cuffPoint_mem f α)⟩, ⟨hβV, hC_bd (cuffPoint_mem f β)⟩,
      isLineWithEnds_cuffPoint_Icc f hlt hlt_2pi⟩
    rintro _ ⟨t, _, rfl⟩
    exact hC_bd (cuffPoint_mem f t)

/-- For `t₀ ≤ α ≤ γ ≤ β ≤ t₁ < t₀ + 2π`, the two sub-intervals `Icc α γ` and `Icc γ β` cover
`Icc α β` and meet only at `{cuffPoint f γ}`. -/
theorem cuffPoint_Icc_split {Θ : Set S} (f : Circle ≃ₜ Θ)
    {t₀ t₁ α γ β : ℝ} (ht₀ : t₀ ≤ α) (hαγ : α ≤ γ) (hγβ : γ ≤ β)
    (hβ : β ≤ t₁) (ht₁ : t₁ < t₀ + 2 * Real.pi) :
    (cuffPoint f '' Icc α γ) ∪ (cuffPoint f '' Icc γ β) = cuffPoint f '' Icc α β ∧
    (cuffPoint f '' Icc α γ) ∩ (cuffPoint f '' Icc γ β) = {cuffPoint f γ} := by
  refine ⟨?_, ?_⟩
  · rw [← image_union, Icc_union_Icc_eq_Icc hαγ hγβ]
  · ext z
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨s₁, ⟨hs₁_1, hs₁_2⟩, rfl⟩, ⟨s₂, ⟨hs₂_1, hs₂_2⟩, h_eq⟩⟩
      have h1 : s₁ ∈ Ico t₀ (t₀ + 2 * Real.pi) := ⟨ht₀.trans hs₁_1, by linarith⟩
      have h2 : s₂ ∈ Ico t₀ (t₀ + 2 * Real.pi) := ⟨(ht₀.trans hαγ).trans hs₂_1, by linarith⟩
      have hs_eq := cuffPoint_injOn_Ico f t₀ h1 h2 h_eq.symm
      have hs₁_γ : s₁ = γ := by linarith
      rw [hs₁_γ]
    · rintro rfl
      exact ⟨⟨γ, ⟨hαγ, le_rfl⟩, rfl⟩, ⟨γ, ⟨le_rfl, hγβ⟩, rfl⟩⟩

/-- If `F = cuffPoint f '' Icc t₀ t₁` (`t₀ ≤ t₁ < t₀ + 2π`, with `cuffPoint f t₀, cuffPoint f t₁ ∈ Γ.V`),
then every space `s ∈ drawingSpaces Γ` with `s ⊆ F` is of the form `cuffPoint f '' Ioo α β` for some
`t₀ ≤ α < β ≤ t₁` with `SpaceHasEnds Γ s (cuffPoint f α) (cuffPoint f β)`. -/
theorem space_in_support_eq_Ioo (hS : IsSurface S) {Γ : Surface.Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard)
    {C F s : Set S} (hC : C ∈ cuffs S) (f : Circle ≃ₜ C)
    {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁) (hlt : t₁ < t₀ + 2 * Real.pi)
    (ht₀ : cuffPoint f t₀ ∈ Γ.V ∩ C) (hF_eq : F = cuffPoint f '' Icc t₀ t₁)
    (hs : s ∈ drawingSpaces Γ) (hsF : s ⊆ F) :
    ∃ α β : ℝ,
      t₀ ≤ α ∧ α < β ∧ β ≤ t₁ ∧
      cuffPoint f α ∈ Γ.V ∩ F ∧
      cuffPoint f β ∈ Γ.V ∩ F ∧
      SpaceHasEnds Γ s (cuffPoint f α) (cuffPoint f β) ∧
      s = cuffPoint f '' Ioo α β ∧
      closure s = cuffPoint f '' Icc α β := by
  have hk := hge2 C hC
  have hsC : s ⊆ C := by
    refine hsF.trans ?_
    rw [hF_eq]
    rintro _ ⟨t, _, rfl⟩
    exact cuffPoint_mem f t
  obtain ⟨i, rfl⟩ := exists_index_of_mem_drawingSpaces_subset_cuff hS hge2 hs hC hsC f
  obtain ⟨α, β, hα, hαβ, hβ_2pi, hα_eq, hβ_eq, hs_eq, hcl_eq⟩ :=
    vSpaceArc_eq_Ioo_from_vertex_angle hS hC f hk ht₀ i
  have hβ_le_t₁ : β ≤ t₁ := by
    apply right_end_le_of_Ioo_subset_Icc f hle hlt hα hαβ hβ_2pi
    rw [← hs_eq, ← hF_eq]
    exact hsF
  have hends : SpaceHasEnds Γ (vSpaceArc Γ.V Γ.finite_V f hk i) (cuffPoint f α) (cuffPoint f β) := by
    rw [hα_eq, hβ_eq]
    exact spaceHasEnds_vSpaceArc hS hge2 hC f i
  have hαF : cuffPoint f α ∈ F := by
    rw [hF_eq]; exact ⟨α, ⟨hα, hαβ.le.trans hβ_le_t₁⟩, rfl⟩
  have hβF : cuffPoint f β ∈ F := by
    rw [hF_eq]; exact ⟨β, ⟨hα.trans hαβ.le, hβ_le_t₁⟩, rfl⟩
  exact ⟨α, β, hα, hαβ, hβ_le_t₁, ⟨hends.2.1.1, hαF⟩, ⟨hends.2.2.1.1, hβF⟩,
    hends, hs_eq, hcl_eq⟩

/-- If `s₁ = cuffPoint f '' Ioo α₁ β₁` and `s₂ = cuffPoint f '' Ioo α₂ β₂` are spaces in `F = cuffPoint f '' Icc t₀ t₁`
with `β₁ ≤ γ ≤ α₂` and `cuffPoint f γ ∈ Γ.V`, then `LiesBetweenInSupport Γ F s₁ s₂ (cuffPoint f γ)`. -/
theorem liesBetweenInSupport_of_angles (hS : IsSurface S) {Γ : Surface.Drawing S}
    {C F s₁ s₂ : Set S} (hC : C ∈ cuffs S) (f : Circle ≃ₜ C)
    {t₀ t₁ α₁ β₁ α₂ β₂ γ : ℝ} (ht₁ : t₁ < t₀ + 2 * Real.pi)
    (ht₀V : cuffPoint f t₀ ∈ Γ.V) (ht₁V : cuffPoint f t₁ ∈ Γ.V)
    (hF_eq : F = cuffPoint f '' Icc t₀ t₁)
    (hs₁ : s₁ ∈ drawingSpaces Γ) (hs₂ : s₂ ∈ drawingSpaces Γ)
    (hα₁ : t₀ ≤ α₁) (hαβ₁ : α₁ < β₁) (hβ₁γ : β₁ ≤ γ)
    (hγα₂ : γ ≤ α₂) (hαβ₂ : α₂ < β₂) (hβ₂ : β₂ ≤ t₁)
    (hs₁_eq : s₁ = cuffPoint f '' Ioo α₁ β₁)
    (hs₂_eq : s₂ = cuffPoint f '' Ioo α₂ β₂)
    (hγV : cuffPoint f γ ∈ Γ.V) :
    LiesBetweenInSupport Γ F s₁ s₂ (cuffPoint f γ) := by
  have ht₀γ : t₀ ≤ γ := hα₁.trans (hαβ₁.le.trans hβ₁γ)
  have hγt₁ : γ ≤ t₁ := hγα₂.trans (hαβ₂.le.trans hβ₂)
  have huF : cuffPoint f γ ∈ F := by
    rw [hF_eq]; exact ⟨γ, ⟨ht₀γ, hγt₁⟩, rfl⟩
  have hs₁F : s₁ ⊆ F := by
    rw [hs₁_eq, hF_eq]
    exact image_mono (fun t ht => ⟨hα₁.trans ht.1.le, ht.2.le.trans (hβ₁γ.trans hγt₁)⟩)
  have hs₂F : s₂ ⊆ F := by
    rw [hs₂_eq, hF_eq]
    exact image_mono (fun t ht => ⟨(ht₀γ.trans hγα₂).trans ht.1.le, ht.2.le.trans hβ₂⟩)
  let I₁ := cuffPoint f '' Icc t₀ γ
  let I₂ := cuffPoint f '' Icc γ t₁
  have hI₁_supp : IsSupportOfDrawing Γ I₁ :=
    ⟨_, _, supportHasEnds_cuffPoint_Icc hS hC f le_rfl ht₀γ hγt₁ ht₁ ht₀V hγV⟩
  have hI₂_supp : IsSupportOfDrawing Γ I₂ :=
    ⟨_, _, supportHasEnds_cuffPoint_Icc hS hC f ht₀γ hγt₁ le_rfl ht₁ hγV ht₁V⟩
  obtain ⟨hunion, hinter⟩ := cuffPoint_Icc_split f le_rfl ht₀γ hγt₁ le_rfl ht₁
  rw [← hF_eq] at hunion
  have hs₁I₁ : s₁ ⊆ I₁ := by
    rw [hs₁_eq]
    exact image_mono (fun t ht => ⟨hα₁.trans ht.1.le, ht.2.le.trans hβ₁γ⟩)
  have hs₂I₂ : s₂ ⊆ I₂ := by
    rw [hs₂_eq]
    exact image_mono (fun t ht => ⟨hγα₂.trans ht.1.le, ht.2.le.trans hβ₂⟩)
  exact ⟨⟨huF, hγV⟩, hs₁, hs₂, hs₁F, hs₂F, I₁, I₂, hI₁_supp, hI₂_supp,
    hunion, hinter, hs₁I₁, hs₂I₂⟩

/-- Every support `I ⊆ F` (where `F = cuffPoint f '' Icc t₀ t₁` with `t₀ ≤ t₁ < t₀ + 2π`) with
`SupportHasEnds Γ I a b` is equal to `cuffPoint f '' Icc α β` for the unique angles `α, β ∈ Icc t₀ t₁`
with `α ≤ β` and `{cuffPoint f α, cuffPoint f β} = {a, b}`. -/
theorem subsupport_eq_cuffPoint_Icc (hS : IsSurface S) {Γ : Surface.Drawing S}
    {C F I : Set S} {a b : S} (hC : C ∈ cuffs S) (f : Circle ≃ₜ C)
    {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁) (hlt : t₁ < t₀ + 2 * Real.pi)
    (hF_eq : F = cuffPoint f '' Icc t₀ t₁)
    (hIF : I ⊆ F) (hI : SupportHasEnds Γ I a b) :
    ∃ α β : ℝ,
      t₀ ≤ α ∧ α ≤ β ∧ β ≤ t₁ ∧
      ((cuffPoint f α = a ∧ cuffPoint f β = b) ∨
       (cuffPoint f α = b ∧ cuffPoint f β = a)) ∧
      I = cuffPoint f '' Icc α β := by
  have : T2Space S := hS.2.1
  have hpi := Real.pi_pos
  have hends := ends_mem_of_supportHasEnds hI
  have haF : a ∈ cuffPoint f '' Icc t₀ t₁ := hF_eq ▸ hIF hends.1
  have hbF : b ∈ cuffPoint f '' Icc t₀ t₁ := hF_eq ▸ hIF hends.2.1
  rcases haF with ⟨τa, ⟨hτa1, hτa2⟩, hτa_eq⟩
  rcases hbF with ⟨τb, ⟨hτb1, hτb2⟩, hτb_eq⟩
  rcases hI with ⟨v, hv, rfl, rfl, rfl⟩ | ⟨hI_bd, hab, ha, hb, hline⟩
  · refine ⟨τa, τa, hτa1, le_rfl, hτa2, Or.inl ⟨hτa_eq, hτa_eq⟩, ?_⟩
    rw [Icc_self, image_singleton, hτa_eq]
  · have hτ_ne : τa ≠ τb := fun h => hab (by rw [← hτa_eq, ← hτb_eq, h])
    have hIC : I ⊆ C := by
      refine hIF.trans ?_
      rw [hF_eq]
      rintro _ ⟨t, _, rfl⟩
      exact cuffPoint_mem f t
    have hC_arc : IsOArc C := (cuff_statement.{w} S hS).2.2 C hC
    obtain ⟨I', hline', hu, hi⟩ := oarc_split_univ hC_arc hline hIC
    rcases lt_or_gt_of_ne hτ_ne with hτ_lt | hτ_gt
    · have hline_u : IsLineWithEnds I (cuffPoint f τa) (cuffPoint f τb) := by
        rwa [hτa_eq, hτb_eq]
      have hline'_u : IsLineWithEnds I' (cuffPoint f τa) (cuffPoint f τb) := by
        rwa [hτa_eq, hτb_eq]
      have hi_u : I ∩ I' = {cuffPoint f τa, cuffPoint f τb} := by
        rwa [hτa_eq, hτb_eq]
      have hcir := circle_lines_univ f hτ_lt (by linarith) hline_u hline'_u hu hi_u
      rcases hcir.2 with ⟨hI_eq, _⟩ | ⟨hI_eq, _⟩
      · exact ⟨τa, τb, hτa1, hτ_lt.le, hτb2, Or.inl ⟨hτa_eq, hτb_eq⟩, hI_eq⟩
      · exfalso
        set m := (t₁ + (t₀ + 2 * Real.pi)) / 2 with hm_def
        have hm_in_I : cuffPoint f m ∈ I := by
          rw [hI_eq]
          exact ⟨m, ⟨by linarith, by linarith⟩, rfl⟩
        have hm_in_F : cuffPoint f m ∈ cuffPoint f '' Icc t₀ t₁ := hF_eq ▸ hIF hm_in_I
        rcases hm_in_F with ⟨s, ⟨hs1, hs2⟩, hs_eq⟩
        have hs_Ico : s ∈ Ico t₀ (t₀ + 2 * Real.pi) := ⟨hs1, hs2.trans_lt hlt⟩
        have hm_Ico : m ∈ Ico t₀ (t₀ + 2 * Real.pi) := ⟨by linarith, by linarith⟩
        have hsm := cuffPoint_injOn_Ico f t₀ hs_Ico hm_Ico hs_eq
        linarith
    · have hline_u : IsLineWithEnds I (cuffPoint f τb) (cuffPoint f τa) := by
        rw [hτb_eq, hτa_eq]; exact hline.symm
      have hline'_u : IsLineWithEnds I' (cuffPoint f τb) (cuffPoint f τa) := by
        rw [hτb_eq, hτa_eq]; exact hline'.symm
      have hi_u : I ∩ I' = {cuffPoint f τb, cuffPoint f τa} := by
        rw [hi, pair_comm, hτb_eq, hτa_eq]
      have hcir := circle_lines_univ f hτ_gt (by linarith) hline_u hline'_u hu hi_u
      rcases hcir.2 with ⟨hI_eq, _⟩ | ⟨hI_eq, _⟩
      · exact ⟨τb, τa, hτb1, hτ_gt.le, hτa2, Or.inr ⟨hτb_eq, hτa_eq⟩, hI_eq⟩
      · exfalso
        set m := (t₁ + (t₀ + 2 * Real.pi)) / 2 with hm_def
        have hm_in_I : cuffPoint f m ∈ I := by
          rw [hI_eq]
          exact ⟨m, ⟨by linarith, by linarith⟩, rfl⟩
        have hm_in_F : cuffPoint f m ∈ cuffPoint f '' Icc t₀ t₁ := hF_eq ▸ hIF hm_in_I
        rcases hm_in_F with ⟨s, ⟨hs1, hs2⟩, hs_eq⟩
        have hs_Ico : s ∈ Ico t₀ (t₀ + 2 * Real.pi) := ⟨hs1, hs2.trans_lt hlt⟩
        have hm_Ico : m ∈ Ico t₀ (t₀ + 2 * Real.pi) := ⟨by linarith, by linarith⟩
        have hsm := cuffPoint_injOn_Ico f t₀ hs_Ico hm_Ico hs_eq
        linarith

/-- Given a vertex angle `α ∈ Icc t₀ t₁` (`cuffPoint f α ∈ Γ.V ∩ C`) with `α < t₁`, there is a space
`s ∈ drawingSpaces Γ` with `s ⊆ F = cuffPoint f '' Icc t₀ t₁` whose left endpoint angle is `α`
(`s = cuffPoint f '' Ioo α β` with `α < β ≤ t₁`). -/
theorem exists_space_starting_at_angle (hS : IsSurface S) {Γ : Surface.Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard)
    {C F : Set S} (hC : C ∈ cuffs S) (f : Circle ≃ₜ C)
    {t₀ t₁ α : ℝ} (ht₀ : cuffPoint f t₀ ∈ Γ.V ∩ C)
    (_hle : t₀ ≤ t₁) (hlt : t₁ < t₀ + 2 * Real.pi)
    (hF_eq : F = cuffPoint f '' Icc t₀ t₁)
    (hα_ge : t₀ ≤ α) (hα_lt : α < t₁) (hαV : cuffPoint f α ∈ Γ.V)
    (ht₁V : cuffPoint f t₁ ∈ Γ.V) :
    ∃ s ∈ drawingSpaces Γ, ∃ β : ℝ,
      α < β ∧ β ≤ t₁ ∧
      s ⊆ F ∧
      SpaceHasEnds Γ s (cuffPoint f α) (cuffPoint f β) ∧
      s = cuffPoint f '' Ioo α β := by
  have hk := hge2 C hC
  have hα_range : cuffPoint f α ∈ Set.range (vNode Γ.V Γ.finite_V f) := by
    rw [range_vNode]; exact ⟨hαV, cuffPoint_mem f α⟩
  rcases hα_range with ⟨i, hi⟩
  obtain ⟨a', b', ha', hab', hb', ha'_eq, hb'_eq, hs_eq, _⟩ :=
    vSpaceArc_eq_Ioo_from_vertex_angle hS hC f hk ht₀ i
  have ha'_eq_α : a' = α := by
    apply cuffPoint_injOn_Ico f t₀ ⟨ha', hab'.trans_le hb'⟩ ⟨hα_ge, hα_lt.trans hlt⟩
    rw [ha'_eq, hi]
  subst a'
  have hb'_le_t₁ : b' ≤ t₁ := by
    by_contra hgt
    push Not at hgt
    have ht₁_in_s : cuffPoint f t₁ ∈ vSpaceArc Γ.V Γ.finite_V f hk i := by
      rw [hs_eq]; exact ⟨t₁, ⟨hα_lt, hgt⟩, rfl⟩
    exact (vSpaceArc_subset_diff Γ.V Γ.finite_V f hk i ht₁_in_s).2 ht₁V
  have hs_mem : vSpaceArc Γ.V Γ.finite_V f hk i ∈ drawingSpaces Γ :=
    vSpaceArc_mem_componentsIn_bd_diff hS Γ.V Γ.finite_V hge2 hC f i
  have hs_sub_F : vSpaceArc Γ.V Γ.finite_V f hk i ⊆ F := by
    rw [hs_eq, hF_eq]
    exact image_mono (fun t ht => ⟨hα_ge.trans ht.1.le, ht.2.le.trans hb'_le_t₁⟩)
  have hends : SpaceHasEnds Γ (vSpaceArc Γ.V Γ.finite_V f hk i) (cuffPoint f α) (cuffPoint f b') := by
    rw [ha'_eq, hb'_eq]
    exact spaceHasEnds_vSpaceArc hS hge2 hC f i
  exact ⟨vSpaceArc Γ.V Γ.finite_V f hk i, hs_mem, b', hab', hb'_le_t₁, hs_sub_F, hends, hs_eq⟩

/-- Given a vertex angle `β ∈ Icc t₀ t₁` (`cuffPoint f β ∈ Γ.V ∩ C`) with `t₀ < β`, there is a space
`s ∈ drawingSpaces Γ` with `s ⊆ F = cuffPoint f '' Icc t₀ t₁` whose right endpoint angle is `β`
(`s = cuffPoint f '' Ioo α β` with `t₀ ≤ α < β`). -/
theorem exists_space_ending_at_angle (hS : IsSurface S) {Γ : Surface.Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard)
    {C F : Set S} (hC : C ∈ cuffs S) (f : Circle ≃ₜ C)
    {t₀ t₁ β : ℝ} (ht₀ : cuffPoint f t₀ ∈ Γ.V ∩ C)
    (_hle : t₀ ≤ t₁) (hlt : t₁ < t₀ + 2 * Real.pi)
    (hF_eq : F = cuffPoint f '' Icc t₀ t₁)
    (hβ_gt : t₀ < β) (hβ_le : β ≤ t₁) (hβV : cuffPoint f β ∈ Γ.V) :
    ∃ s ∈ drawingSpaces Γ, ∃ α : ℝ,
      t₀ ≤ α ∧ α < β ∧
      s ⊆ F ∧
      SpaceHasEnds Γ s (cuffPoint f α) (cuffPoint f β) ∧
      s = cuffPoint f '' Ioo α β := by
  have hk := hge2 C hC
  have hβ_range : cuffPoint f β ∈ Set.range (vNode Γ.V Γ.finite_V f) := by
    rw [range_vNode]; exact ⟨hβV, cuffPoint_mem f β⟩
  rcases hβ_range with ⟨i_next, hi_next⟩
  obtain ⟨i, hi⟩ := (bijective_nextFin hk).2 i_next
  obtain ⟨a', b', ha', hab', hb', ha'_eq, hb'_eq, hs_eq, _⟩ :=
    vSpaceArc_eq_Ioo_from_vertex_angle hS hC f hk ht₀ i
  have hb'_lt_2pi : b' < t₀ + 2 * Real.pi := by
    rcases eq_or_lt_of_le hb' with h_eq | h_lt
    · exfalso
      rw [h_eq, cuffPoint_add_two_pi] at hb'_eq
      have h_eq_β : t₀ = β := by
        apply cuffPoint_injOn_Ico f t₀ ⟨le_rfl, by linarith [Real.pi_pos]⟩ ⟨hβ_gt.le, hβ_le.trans_lt hlt⟩
        rw [hb'_eq, hi, hi_next]
      linarith
    · exact h_lt
  have hb'_eq_β : b' = β := by
    apply cuffPoint_injOn_Ico f t₀ ⟨ha'.trans hab'.le, hb'_lt_2pi⟩ ⟨hβ_gt.le, hβ_le.trans_lt hlt⟩
    rw [hb'_eq, hi, hi_next]
  subst b'
  have hs_mem : vSpaceArc Γ.V Γ.finite_V f hk i ∈ drawingSpaces Γ :=
    vSpaceArc_mem_componentsIn_bd_diff hS Γ.V Γ.finite_V hge2 hC f i
  have hs_sub_F : vSpaceArc Γ.V Γ.finite_V f hk i ⊆ F := by
    rw [hs_eq, hF_eq]
    exact image_mono (fun t ht => ⟨ha'.trans ht.1.le, ht.2.le.trans hβ_le⟩)
  have hends : SpaceHasEnds Γ (vSpaceArc Γ.V Γ.finite_V f hk i) (cuffPoint f a') (cuffPoint f β) := by
    rw [ha'_eq, hb'_eq]
    exact spaceHasEnds_vSpaceArc hS hge2 hC f i
  exact ⟨vSpaceArc Γ.V Γ.finite_V f hk i, hs_mem, a', ha', hab', hs_sub_F, hends, hs_eq⟩

/-- In a presentation `h_pres`, if `F_star j = cuffPoint f '' Icc t₀ t₁` (`t₀ ≤ t₁ < t₀ + 2π`),
`γ ∈ Icc t₀ t₁` with `cuffPoint f γ ∈ Γ.V`, `x₁` is a unit of `F_star j` to the left of `γ`, and
`x₂` is a unit of `F_star j` to the right of `γ`, then
`(μ x₁).vertexSet ∩ (μ x₂).vertexSet ⊆ (μ (.vertex (cuffPoint f γ))).vertexSet`. -/
theorem unit_inter_vertexSet_subset_of_angle_between
    {α_v : Type*} {β_e : Type*} {G : Hypergraph α_v β_e} {Γ : Surface.Drawing S}
    {Γ_sub : Hypergraph α_v β_e} {ιV : S → α_v} {ιE : Set S → β_e} {r : ℕ}
    {F_star : Fin r → Set S} {H : Fin r → Hypergraph α_v β_e}
    {μ : BoundaryUnit S → Hypergraph α_v β_e} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (j : Fin r) {C : Set S} (hC : C ∈ cuffs S) (f : Circle ≃ₜ C)
    {t₀ t₁ γ : ℝ} (ht₀ : cuffPoint f t₀ ∈ Γ.V ∩ C) (ht₁V : cuffPoint f t₁ ∈ Γ.V)
    (hle : t₀ ≤ t₁) (hlt : t₁ < t₀ + 2 * Real.pi)
    (hF_eq : F_star j = cuffPoint f '' Icc t₀ t₁)
    (hγ1 : t₀ ≤ γ) (hγ2 : γ ≤ t₁) (hγV : cuffPoint f γ ∈ Γ.V)
    {x₁ x₂ : BoundaryUnit S}
    (hx₁ : (∃ α₁ : ℝ, t₀ ≤ α₁ ∧ α₁ ≤ γ ∧ cuffPoint f α₁ ∈ Γ.V ∧ x₁ = .vertex (cuffPoint f α₁)) ∨
           (∃ s₁ ∈ drawingSpaces Γ, ∃ α₁ β₁ : ℝ,
             t₀ ≤ α₁ ∧ α₁ < β₁ ∧ β₁ ≤ γ ∧ s₁ = cuffPoint f '' Ioo α₁ β₁ ∧ x₁ = .space s₁))
    (hx₂ : (∃ α₂ : ℝ, γ ≤ α₂ ∧ α₂ ≤ t₁ ∧ cuffPoint f α₂ ∈ Γ.V ∧ x₂ = .vertex (cuffPoint f α₂)) ∨
           (∃ s₂ ∈ drawingSpaces Γ, ∃ α₂ β₂ : ℝ,
             γ ≤ α₂ ∧ α₂ < β₂ ∧ β₂ ≤ t₁ ∧ s₂ = cuffPoint f '' Ioo α₂ β₂ ∧ x₂ = .space s₂)) :
    (μ x₁).vertexSet ∩ (μ x₂).vertexSet ⊆ (μ (.vertex (cuffPoint f γ))).vertexSet := by
  have hS := h_pres.is_surface
  have hge2 := h_pres.cuff_vertices_ge_two
  -- Reduce `x₁` to either `x₁ = .vertex (cuffPoint f γ)` or a space `s₁` to the left of `γ`.
  have hx₁_red : x₁ = .vertex (cuffPoint f γ) ∨
      ∃ s₁ ∈ drawingSpaces Γ, ∃ α₁ β₁ : ℝ,
        t₀ ≤ α₁ ∧ α₁ < β₁ ∧ β₁ ≤ γ ∧
        s₁ = cuffPoint f '' Ioo α₁ β₁ ∧
        (μ x₁).vertexSet ⊆ (μ (.space s₁)).vertexSet := by
    rcases hx₁ with ⟨α₁, hα₁_ge, hα₁_le, hα₁V, rfl⟩ | ⟨s₁, hs₁, α₁, β₁, h1, h2, h3, hs₁_eq, rfl⟩
    · rcases eq_or_lt_of_le hα₁_le with rfl | hα₁_lt
      · exact Or.inl rfl
      · obtain ⟨s₁, hs₁, β₁, hαβ₁, hβ₁_le, hs₁F, hends, hs₁_eq⟩ :=
          exists_space_starting_at_angle hS hge2 hC f ht₀ hle hlt hF_eq
            hα₁_ge (hα₁_lt.trans_le hγ2) hα₁V ht₁V
        have hβ₁_le_γ : β₁ ≤ γ := by
          by_contra hgt
          push Not at hgt
          have hγ_in_s₁ : cuffPoint f γ ∈ s₁ := by
            rw [hs₁_eq]; exact ⟨γ, ⟨hα₁_lt, hgt⟩, rfl⟩
          exact (subset_bd_diff_of_mem_drawingSpaces hs₁ hγ_in_s₁).2 hγV
        have hle_space := (h_pres.v3_space j s₁ hs₁ _ _ hs₁F hends).2.1
        exact Or.inr ⟨s₁, hs₁, α₁, β₁, hα₁_ge, hαβ₁, hβ₁_le_γ, hs₁_eq, hle_space.vertexSet_subset⟩
    · exact Or.inr ⟨s₁, hs₁, α₁, β₁, h1, h2, h3, hs₁_eq, Subset.rfl⟩
  -- Reduce `x₂` to either `x₂ = .vertex (cuffPoint f γ)` or a space `s₂` to the right of `γ`.
  have hx₂_red : x₂ = .vertex (cuffPoint f γ) ∨
      ∃ s₂ ∈ drawingSpaces Γ, ∃ α₂ β₂ : ℝ,
        γ ≤ α₂ ∧ α₂ < β₂ ∧ β₂ ≤ t₁ ∧
        s₂ = cuffPoint f '' Ioo α₂ β₂ ∧
        (μ x₂).vertexSet ⊆ (μ (.space s₂)).vertexSet := by
    rcases hx₂ with ⟨α₂, hα₂_ge, hα₂_le, hα₂V, rfl⟩ | ⟨s₂, hs₂, α₂, β₂, h1, h2, h3, hs₂_eq, rfl⟩
    · rcases eq_or_lt_of_le hα₂_ge with rfl | hα₂_gt
      · exact Or.inl rfl
      · obtain ⟨s₂, hs₂, α₂', hα₂'_ge, hα₂'_lt, hs₂F, hends, hs₂_eq⟩ :=
          exists_space_ending_at_angle hS hge2 hC f ht₀ hle hlt hF_eq
            (hγ1.trans_lt hα₂_gt) hα₂_le hα₂V
        have hγ_le_α₂' : γ ≤ α₂' := by
          by_contra hlt'
          push Not at hlt'
          have hγ_in_s₂ : cuffPoint f γ ∈ s₂ := by
            rw [hs₂_eq]; exact ⟨γ, ⟨hlt', hα₂_gt⟩, rfl⟩
          exact (subset_bd_diff_of_mem_drawingSpaces hs₂ hγ_in_s₂).2 hγV
        have hle_space := (h_pres.v3_space j s₂ hs₂ _ _ hs₂F hends).2.2.1
        exact Or.inr ⟨s₂, hs₂, α₂', α₂, hγ_le_α₂', hα₂'_lt, hα₂_le, hs₂_eq, hle_space.vertexSet_subset⟩
    · exact Or.inr ⟨s₂, hs₂, α₂, β₂, h1, h2, h3, hs₂_eq, Subset.rfl⟩
  rcases hx₁_red with rfl | ⟨s₁, hs₁, α₁, β₁, hα₁, hαβ₁, hβ₁γ, hs₁_eq, hsub₁⟩
  · exact inter_subset_left
  · rcases hx₂_red with rfl | ⟨s₂, hs₂, α₂, β₂, hγα₂, hαβ₂, hβ₂, hs₂_eq, hsub₂⟩
    · exact inter_subset_right
    · have hbet : LiesBetweenInSupport Γ (F_star j) s₁ s₂ (cuffPoint f γ) :=
        liesBetweenInSupport_of_angles hS hC f hlt ht₀.1 ht₁V hF_eq hs₁ hs₂
          hα₁ hαβ₁ hβ₁γ hγα₂ hαβ₂ hβ₂ hs₁_eq hs₂_eq hγV
      have hv4 := (h_pres.v4_between j s₁ s₂ (cuffPoint f γ) hbet).vertexSet_subset
      exact (inter_subset_inter hsub₁ hsub₂).trans hv4

/-- For any two sub-intervals `I₁ = cuffPoint f '' Icc α₁ β₁` and `I₂ = cuffPoint f '' Icc α₂ β₂`
of `F_star j = cuffPoint f '' Icc t₀ t₁` with `t₀ ≤ α₁ ≤ β₁ ≤ γ ≤ α₂ ≤ β₂ ≤ t₁` and
`cuffPoint f γ ∈ Γ.V`,
`(supportGraph G Γ μ I₁).vertexSet ∩ (supportGraph G Γ μ I₂).vertexSet ⊆ (μ (.vertex (cuffPoint f γ))).vertexSet`. -/
theorem supportGraph_inter_vertexSet_subset_of_angle_between
    {α_v : Type*} {β_e : Type*} {G : Hypergraph α_v β_e} {Γ : Surface.Drawing S}
    {Γ_sub : Hypergraph α_v β_e} {ιV : S → α_v} {ιE : Set S → β_e} {r : ℕ}
    {F_star : Fin r → Set S} {H : Fin r → Hypergraph α_v β_e}
    {μ : BoundaryUnit S → Hypergraph α_v β_e} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (j : Fin r) {C I₁ I₂ : Set S} (hC : C ∈ cuffs S) (f : Circle ≃ₜ C)
    {t₀ t₁ α₁ β₁ γ α₂ β₂ : ℝ} (ht₀ : cuffPoint f t₀ ∈ Γ.V ∩ C) (ht₁V : cuffPoint f t₁ ∈ Γ.V)
    (hle : t₀ ≤ t₁) (hlt : t₁ < t₀ + 2 * Real.pi)
    (hF_eq : F_star j = cuffPoint f '' Icc t₀ t₁)
    (hα₁ : t₀ ≤ α₁) (hαβ₁ : α₁ ≤ β₁) (hβ₁γ : β₁ ≤ γ)
    (hγα₂ : γ ≤ α₂) (hαβ₂ : α₂ ≤ β₂) (hβ₂ : β₂ ≤ t₁)
    (hI₁_eq : I₁ = cuffPoint f '' Icc α₁ β₁)
    (hI₂_eq : I₂ = cuffPoint f '' Icc α₂ β₂)
    (hγV : cuffPoint f γ ∈ Γ.V) :
    (supportGraph G Γ μ I₁).vertexSet ∩ (supportGraph G Γ μ I₂).vertexSet ⊆
      (μ (.vertex (cuffPoint f γ))).vertexSet := by
  have hS := h_pres.is_surface
  have hge2 := h_pres.cuff_vertices_ge_two
  have hγ1 : t₀ ≤ γ := hα₁.trans (hαβ₁.trans hβ₁γ)
  have hγ2 : γ ≤ t₁ := hγα₂.trans (hαβ₂.trans hβ₂)
  have hI₁_sub_F : I₁ ⊆ F_star j := by
    rw [hI₁_eq, hF_eq]
    exact image_mono (fun t ht => ⟨hα₁.trans ht.1, ht.2.trans (hβ₁γ.trans hγ2)⟩)
  have hI₂_sub_F : I₂ ⊆ F_star j := by
    rw [hI₂_eq, hF_eq]
    exact image_mono (fun t ht => ⟨(hγ1.trans hγα₂).trans ht.1, ht.2.trans hβ₂⟩)
  -- Convert any membership in `supportGraph G Γ μ I₁` to the unit disjunction for `x₁`
  have hunit₁ : ∀ v ∈ (supportGraph G Γ μ I₁).vertexSet,
      ∃ x₁ : BoundaryUnit S, v ∈ (μ x₁).vertexSet ∧
        ((∃ τ₁ : ℝ, t₀ ≤ τ₁ ∧ τ₁ ≤ γ ∧ cuffPoint f τ₁ ∈ Γ.V ∧ x₁ = .vertex (cuffPoint f τ₁)) ∨
         (∃ s₁ ∈ drawingSpaces Γ, ∃ a₁ b₁ : ℝ,
           t₀ ≤ a₁ ∧ a₁ < b₁ ∧ b₁ ≤ γ ∧ s₁ = cuffPoint f '' Ioo a₁ b₁ ∧ x₁ = .space s₁)) := by
    rintro v ⟨_, hv_s | hv_u⟩
    · rw [mem_iUnion₂] at hv_s
      rcases hv_s with ⟨s₁, ⟨hs₁, hs₁I₁⟩, hv_s₁⟩
      obtain ⟨a₁, b₁, ha₁, hab₁, hb₁_t₁, _, _, _, hs₁_eq, _⟩ :=
        space_in_support_eq_Ioo hS hge2 hC f hle hlt ht₀ hF_eq hs₁ (hs₁I₁.trans hI₁_sub_F)
      have hb₁_le_β₁ : b₁ ≤ β₁ := by
        apply right_end_le_of_Ioo_subset_Icc f (hα₁.trans hαβ₁) (by linarith) ha₁ hab₁ (hb₁_t₁.trans hlt.le)
        rw [← hs₁_eq]
        refine hs₁I₁.trans ?_
        rw [hI₁_eq]
        exact image_mono (fun t ht => ⟨hα₁.trans ht.1, ht.2⟩)
      exact ⟨.space s₁, hv_s₁, Or.inr ⟨s₁, hs₁, a₁, b₁, ha₁, hab₁, hb₁_le_β₁.trans hβ₁γ, hs₁_eq, rfl⟩⟩
    · rw [mem_iUnion₂] at hv_u
      rcases hv_u with ⟨u₁, ⟨hu₁V, hu₁I₁⟩, hv_u₁⟩
      have hu₁_in : u₁ ∈ cuffPoint f '' Icc α₁ β₁ := hI₁_eq ▸ hu₁I₁
      rcases hu₁_in with ⟨τ₁, ⟨hτ₁_1, hτ₁_2⟩, rfl⟩
      exact ⟨.vertex (cuffPoint f τ₁), hv_u₁,
        Or.inl ⟨τ₁, hα₁.trans hτ₁_1, hτ₁_2.trans hβ₁γ, hu₁V, rfl⟩⟩
  -- Convert any membership in `supportGraph G Γ μ I₂` to the unit disjunction for `x₂`
  have hunit₂ : ∀ v ∈ (supportGraph G Γ μ I₂).vertexSet,
      ∃ x₂ : BoundaryUnit S, v ∈ (μ x₂).vertexSet ∧
        ((∃ τ₂ : ℝ, γ ≤ τ₂ ∧ τ₂ ≤ t₁ ∧ cuffPoint f τ₂ ∈ Γ.V ∧ x₂ = .vertex (cuffPoint f τ₂)) ∨
         (∃ s₂ ∈ drawingSpaces Γ, ∃ a₂ b₂ : ℝ,
           γ ≤ a₂ ∧ a₂ < b₂ ∧ b₂ ≤ t₁ ∧ s₂ = cuffPoint f '' Ioo a₂ b₂ ∧ x₂ = .space s₂)) := by
    rintro v ⟨_, hv_s | hv_u⟩
    · rw [mem_iUnion₂] at hv_s
      rcases hv_s with ⟨s₂, ⟨hs₂, hs₂I₂⟩, hv_s₂⟩
      obtain ⟨a₂, b₂, ha₂, hab₂, hb₂_t₁, _, _, _, hs₂_eq, _⟩ :=
        space_in_support_eq_Ioo hS hge2 hC f hle hlt ht₀ hF_eq hs₂ (hs₂I₂.trans hI₂_sub_F)
      have hα₂_le_a₂ : α₂ ≤ a₂ := by
        by_contra hlt'
        push Not at hlt'
        set m := (a₂ + min α₂ b₂) / 2 with hm_def
        have hm_s₂ : cuffPoint f m ∈ s₂ := by
          rw [hs₂_eq]; exact ⟨m, ⟨by linarith [lt_min hlt' hab₂], by linarith [min_le_right α₂ b₂]⟩, rfl⟩
        have hm_I₂ : cuffPoint f m ∈ cuffPoint f '' Icc α₂ β₂ := hI₂_eq ▸ hs₂I₂ hm_s₂
        rcases hm_I₂ with ⟨tm, ⟨htm1, htm2⟩, htm_eq⟩
        have htm_eq_m : tm = m :=
          cuffPoint_injOn_Ico f t₀ ⟨(hγ1.trans hγα₂).trans htm1, (htm2.trans hβ₂).trans_lt hlt⟩
            ⟨by linarith [lt_min hlt' hab₂], by linarith [min_le_right α₂ b₂]⟩ htm_eq
        linarith [min_le_left α₂ b₂]
      exact ⟨.space s₂, hv_s₂, Or.inr ⟨s₂, hs₂, a₂, b₂, hγα₂.trans hα₂_le_a₂, hab₂, hb₂_t₁, hs₂_eq, rfl⟩⟩
    · rw [mem_iUnion₂] at hv_u
      rcases hv_u with ⟨u₂, ⟨hu₂V, hu₂I₂⟩, hv_u₂⟩
      have hu₂_in : u₂ ∈ cuffPoint f '' Icc α₂ β₂ := hI₂_eq ▸ hu₂I₂
      rcases hu₂_in with ⟨τ₂, ⟨hτ₂_1, hτ₂_2⟩, rfl⟩
      exact ⟨.vertex (cuffPoint f τ₂), hv_u₂,
        Or.inl ⟨τ₂, hγα₂.trans hτ₂_1, hτ₂_2.trans hβ₂, hu₂V, rfl⟩⟩
  rintro v ⟨hv₁, hv₂⟩
  obtain ⟨x₁, hv_x₁, hx₁⟩ := hunit₁ v hv₁
  obtain ⟨x₂, hv_x₂, hx₂⟩ := hunit₂ v hv₂
  exact unit_inter_vertexSet_subset_of_angle_between h_pres j hC f ht₀ ht₁V hle hlt hF_eq
    hγ1 hγ2 hγV hx₁ hx₂ ⟨hv_x₁, hv_x₂⟩

end SupportsAndIntervals

end GraphMinor.GM21.Supports
