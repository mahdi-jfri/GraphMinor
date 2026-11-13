module

public import GraphMinor.GM21.Defs
public import GraphMinor.Surface.Classification
public import GraphMinor.Surface.ChartCells
public import GraphMinor.Surface.CutLift
public import GraphMinor.GM17.ArcDisc
public import GraphMinor.GM17.CuffOrder
import Mathlib.Analysis.Convex.PathConnected

/-!
# Spaces, Supports, and Circular Order on Cuffs (Graph Minors XXI, Sections 6, 8, and 9)

This file develops the topological and combinatorial properties of boundary spaces
(`drawingSpaces Γ = componentsIn (bd S \ Γ.V)`), supports (`IsSupportOfDrawing Γ F`), and circular
order (`InCuffOrder`) on the cuffs of a surface `S` for any drawing `Γ : Drawing S` satisfying
`∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard`.
-/

@[expose] public section

namespace GraphMinor.GM21

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

/-- Every cuff of a surface is closed. -/
theorem isClosed_cuff_univ (hS : IsSurface S) {C : Set S} (hC : C ∈ cuffs S) : IsClosed C := by
  have : T2Space S := hS.2.1
  exact (IsOArc.isCompact ((cuff_statement.{w} S hS).2.2 C hC)).isClosed

/-- Every cuff of a surface is nonempty and preconnected. -/
theorem isConnected_cuff_univ {C : Set S} (hC : C ∈ cuffs S) : IsConnected C := by
  rcases hC with ⟨x, hx, rfl⟩
  exact ⟨⟨x, mem_connectedComponentIn hx⟩, isPreconnected_connectedComponentIn⟩

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

theorem injective_vSpaceArc (f : Circle ≃ₜ Θ) (hk : 2 ≤ (V ∩ Θ).ncard) :
    Function.Injective (vSpaceArc V hV f hk) := by
  intro i j h
  by_contra hij
  exact Set.disjoint_left.mp (disjoint_vSpaceArc V hV f hk hij)
    (vMidpoint_mem_vSpaceArc V hV f hk i) (h ▸ vMidpoint_mem_vSpaceArc V hV f hk i)

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

/-- For any cuff `C ∈ cuffs S` and any parametrization `f : Circle ≃ₜ C`, the spaces of `Γ` in `C`
are precisely `vSpaceArc Γ.V Γ.finite_V f (hge2 C hC) i`. -/
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

/-- Every `vSpaceArc` for any parametrization `f : Circle ≃ₜ C` belongs to `componentsIn (bd S \ V)`. -/
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

/-- Every space `s ∈ drawingSpaces Γ` is finite in count, nonempty, connected, contained in a
unique cuff `C ∈ cuffs S`, and given by `vSpaceArc` for any `f : Circle ≃ₜ C`. -/
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

/-! ## 4. Supports, Interval Representations, and Circular Order -/

section SupportsAndOrder

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

/-- Any two distinct spaces `s, s' ∈ drawingSpaces Γ` on the same cuff `C ∈ cuffs S` occur in circular
order around `C` with the two ends `a, b` of `s`: either `InCuffOrder C s a s' b` or
`InCuffOrder C s b s' a`. -/
theorem inCuffOrder_of_ne_space (hS : IsSurface S) {Γ : Surface.Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) {C s s' : Set S} {a b : S}
    (hC : C ∈ cuffs S) (hs : SpaceHasEnds Γ s a b) (hs' : s' ∈ drawingSpaces Γ)
    (hsC : s ⊆ C) (hs'C : s' ⊆ C) (hne : s ≠ s') :
    InCuffOrder C s a s' b ∨ InCuffOrder C s b s' a := by
  have : T2Space S := hS.2.1
  let f := cuffHomeo hS hC
  have hk := hge2 C hC
  obtain ⟨i, rfl⟩ := exists_index_of_mem_drawingSpaces_subset_cuff hS hge2 hs.1 hC hsC f
  obtain ⟨j, rfl⟩ := exists_index_of_mem_drawingSpaces_subset_cuff hS hge2 hs' hC hs'C f
  have hij : i ≠ j := fun h => hne (h ▸ rfl)
  set a₀ := vAngle Γ.V Γ.finite_V f i with ha₀_def
  set b₀ := vUpperAngle Γ.V Γ.finite_V f hk i with hb₀_def
  have ha₀_lt_b₀ : a₀ < b₀ := vAngle_lt_vUpperAngle Γ.V Γ.finite_V f hk i
  have hb₀_lt : b₀ < a₀ + 2 * Real.pi := vUpperAngle_lt_add_two_pi Γ.V Γ.finite_V f hk i
  have ha₀_mem : cuffPoint f a₀ ∈ Γ.V ∩ C := vNode_mem Γ.V Γ.finite_V f i
  obtain ⟨a', b', ha', hab', hb', _, _, hs'_eq, hcl'_eq⟩ :=
    vSpaceArc_eq_Ioo_from_vertex_angle hS hC f hk ha₀_mem j
  have hdisj : Disjoint (vSpaceArc Γ.V Γ.finite_V f hk i) (vSpaceArc Γ.V Γ.finite_V f hk j) :=
    disjoint_vSpaceArc Γ.V Γ.finite_V f hk hij
  have hb₀_le_a' : b₀ ≤ a' := by
    by_contra hlt'
    push Not at hlt'
    set m := (max a₀ a' + min b₀ b') / 2 with hm_def
    have hmax_lt_min : max a₀ a' < min b₀ b' := max_lt (lt_min ha₀_lt_b₀ (ha'.trans_lt hab')) (lt_min hlt' hab')
    have hm_i : cuffPoint f m ∈ vSpaceArc Γ.V Γ.finite_V f hk i :=
      ⟨m, ⟨by rw [← ha₀_def]; linarith [le_max_left a₀ a'], by rw [← hb₀_def]; linarith [min_le_left b₀ b']⟩, rfl⟩
    have hm_j : cuffPoint f m ∈ vSpaceArc Γ.V Γ.finite_V f hk j := by
      rw [hs'_eq]
      exact ⟨m, ⟨by linarith [le_max_right a₀ a'], by linarith [min_le_right b₀ b']⟩, rfl⟩
    exact Set.disjoint_left.mp hdisj hm_i hm_j
  have hcl_i : closure (vSpaceArc Γ.V Γ.finite_V f hk i) = cuffPoint f '' Icc a₀ b₀ :=
    closure_vSpaceArc Γ.V Γ.finite_V f hk i
  have hcl_i_C : closure (vSpaceArc Γ.V Γ.finite_V f hk i) ∩ C = cuffPoint f '' Icc a₀ b₀ := by
    rw [hcl_i, inter_eq_left]
    rintro _ ⟨t, _, rfl⟩
    exact cuffPoint_mem f t
  have hcl_j_C : closure (vSpaceArc Γ.V Γ.finite_V f hk j) ∩ C = cuffPoint f '' Icc a' b' := by
    rw [hcl'_eq, inter_eq_left]
    rintro _ ⟨t, _, rfl⟩
    exact cuffPoint_mem f t
  have hord : InCuffOrder C (vSpaceArc Γ.V Γ.finite_V f hk i)
      (vNode Γ.V Γ.finite_V f (nextFin hk i))
      (vSpaceArc Γ.V Γ.finite_V f hk j)
      (vNode Γ.V Γ.finite_V f i) := by
    refine ⟨f, a₀, b₀, b₀, a', b', a₀ + 2 * Real.pi,
      ha₀_lt_b₀.le, le_rfl, hb₀_le_a', hab'.le, hb', le_rfl,
      cuffPoint_vUpperAngle Γ.V Γ.finite_V f hk i, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cuffPoint_add_two_pi]; rfl
    · rw [hcl_i_C]; exact ⟨cuffPoint f a₀, ⟨a₀, ⟨le_rfl, ha₀_lt_b₀.le⟩, rfl⟩⟩
    · rw [hcl_i_C]
    · rw [hcl_j_C]; exact ⟨cuffPoint f a', ⟨a', ⟨le_rfl, hab'.le⟩, rfl⟩⟩
    · rw [hcl_j_C]
  have hends_i := spaceHasEnds_vSpaceArc hS hge2 hC f i
  have hpair := ends_pair_eq_of_spaceHasEnds hs hends_i
  have ha_mem : a ∈ ({vNode Γ.V Γ.finite_V f i, vNode Γ.V Γ.finite_V f (nextFin hk i)} : Set S) := by
    rw [← hpair]; exact Or.inl rfl
  have hb_mem : b ∈ ({vNode Γ.V Γ.finite_V f i, vNode Γ.V Γ.finite_V f (nextFin hk i)} : Set S) := by
    rw [← hpair]; exact Or.inr rfl
  rcases ha_mem with rfl | rfl <;> rcases hb_mem with rfl | rfl
  · exact (hs.2.2.2.1 rfl).elim
  · exact Or.inr hord
  · exact Or.inl hord
  · exact (hs.2.2.2.1 rfl).elim

/-- Given pairwise disjoint supports `F_star : Fin r → Set S`, for each `j₁ : Fin r` with
`F_star j₁ ⊆ C` (`C ∈ cuffs S`), the two spaces `s_r, s_l` immediately adjacent to `F_star j₁` in
`C` are uncovered (`∀ j, ¬ s_r ⊆ F_star j` and `∀ j, ¬ s_l ⊆ F_star j`), separate `F_star j₁` in
circular order from every other `F_star j₂ ⊆ C` (`j₁ ≠ j₂`), and witness circular order for
`LiesBetweenInSupport Γ (F_star j₁) s₁ s₂ u`. -/
theorem exists_adjacent_uncovered_spaces_of_support (hS : IsSurface S) {Γ : Surface.Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard)
    {r : ℕ} {F_star : Fin r → Set S}
    (hF_supp : ∀ j : Fin r, IsSupportOfDrawing Γ (F_star j))
    (hF_disj : Pairwise (fun i j : Fin r => Disjoint (F_star i) (F_star j)))
    (j₁ : Fin r) {C : Set S} (hC : C ∈ cuffs S) (hF₁C : F_star j₁ ⊆ C) :
    ∃ (s_r s_l : Set S) (a_r b_r a_l b_l : S),
      s_r ⊆ C ∧ s_l ⊆ C ∧
      SpaceHasEnds Γ s_r a_r b_r ∧
      SpaceHasEnds Γ s_l a_l b_l ∧
      (∀ j : Fin r, ¬ s_r ⊆ F_star j) ∧
      (∀ j : Fin r, ¬ s_l ⊆ F_star j) ∧
      (∀ (j₂ : Fin r), j₁ ≠ j₂ → F_star j₂ ⊆ C →
        ∀ (X₁ X₂ : Set S),
          (closure X₁ ∩ C).Nonempty → closure X₁ ∩ C ⊆ F_star j₁ →
          (closure X₂ ∩ C).Nonempty → closure X₂ ∩ C ⊆ F_star j₂ →
          ∀ u₁ ∈ ({a_r, b_r} : Set S), ∀ u₂ ∈ ({a_l, b_l} : Set S),
            InCuffOrder C X₁ u₁ X₂ u₂) ∧
      (∀ (s₁ s₂ : Set S) (u : S),
        LiesBetweenInSupport Γ (F_star j₁) s₁ s₂ u →
        ∀ u₀ ∈ ({a_r, b_r} : Set S),
          InCuffOrder C s₁ u s₂ u₀ ∨ InCuffOrder C s₂ u s₁ u₀) := by
  have : T2Space S := hS.2.1
  let f := cuffHomeo hS hC
  have hk := hge2 C hC
  rcases hF_supp j₁ with ⟨endA, endB, hF₁_ends⟩
  have hends_mem := ends_mem_of_supportHasEnds hF₁_ends
  obtain ⟨t₀, ht₀_Ico, t₁, ⟨ht₀_le_t₁, ht₁_lt⟩, h_ab_eq, hF₁_eq, hC_diff_F₁⟩ :=
    support_eq_cuffPoint_Icc hS hC f hF₁_ends hF₁C
  have ht₀_in_F₁ : cuffPoint f t₀ ∈ F_star j₁ := by
    rw [hF₁_eq]; exact ⟨t₀, ⟨le_rfl, ht₀_le_t₁⟩, rfl⟩
  have ht₁_in_F₁ : cuffPoint f t₁ ∈ F_star j₁ := by
    rw [hF₁_eq]; exact ⟨t₁, ⟨ht₀_le_t₁, le_rfl⟩, rfl⟩
  have ht₀_mem : cuffPoint f t₀ ∈ Γ.V ∩ C := by
    refine ⟨?_, cuffPoint_mem f t₀⟩
    rcases h_ab_eq with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
    · exact hends_mem.2.2.1.1
    · exact hends_mem.2.2.2.1.1
  have ht₁_mem : cuffPoint f t₁ ∈ Γ.V ∩ C := by
    refine ⟨?_, cuffPoint_mem f t₁⟩
    rcases h_ab_eq with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2]
    · exact hends_mem.2.2.2.1.1
    · exact hends_mem.2.2.1.1
  -- Construct s_r: the space starting at cuffPoint f t₁
  have ht₁_range : cuffPoint f t₁ ∈ Set.range (vNode Γ.V Γ.finite_V f) := by
    rw [range_vNode]; exact ht₁_mem
  rcases ht₁_range with ⟨i_r, hi_r⟩
  set s_r := vSpaceArc Γ.V Γ.finite_V f hk i_r with hs_r_def
  obtain ⟨a_r', b_r', ha_r', hab_r', hb_r', ha_r'_eq, hb_r'_eq, hs_r_eq, hcl_r_eq⟩ :=
    vSpaceArc_eq_Ioo_from_vertex_angle hS hC f hk ht₀_mem i_r
  have ha_r'_eq_t₁ : t₁ = a_r' := by
    apply cuffPoint_injOn_Ico f t₀ ⟨ht₀_le_t₁, ht₁_lt⟩ ⟨ha_r', hab_r'.trans_le hb_r'⟩
    rw [ha_r'_eq, hi_r]
  subst a_r'
  have hs_r_ends : SpaceHasEnds Γ s_r (cuffPoint f t₁) (cuffPoint f b_r') := by
    rw [ha_r'_eq, hb_r'_eq]
    exact spaceHasEnds_vSpaceArc hS hge2 hC f i_r
  have hs_r_uncov : ∀ j : Fin r, ¬ s_r ⊆ F_star j := by
    intro j hsub
    by_cases hj : j = j₁
    · subst hj
      set m := (t₁ + b_r') / 2 with hm_def
      have hm_s : cuffPoint f m ∈ s_r := by
        rw [hs_r_def, hs_r_eq]; exact ⟨m, ⟨by linarith, by linarith⟩, rfl⟩
      have hm_diff : cuffPoint f m ∈ C \ F_star j := by
        rw [hC_diff_F₁]; exact ⟨m, ⟨by linarith, by linarith⟩, rfl⟩
      exact hm_diff.2 (hsub hm_s)
    · have hcl_sub : closure s_r ⊆ F_star j :=
        closure_minimal hsub (isClosed_of_isSupportOfDrawing hS (hF_supp j))
      have ht₁_cl : cuffPoint f t₁ ∈ closure s_r := by
        rw [hs_r_def, hcl_r_eq]; exact ⟨t₁, ⟨le_rfl, hab_r'.le⟩, rfl⟩
      exact Set.disjoint_left.mp (hF_disj (Ne.symm hj)) ht₁_in_F₁ (hcl_sub ht₁_cl)
  -- Construct s_l: the space ending at cuffPoint f t₀
  have ht₀_range : cuffPoint f t₀ ∈ Set.range (vNode Γ.V Γ.finite_V f) := by
    rw [range_vNode]; exact ht₀_mem
  rcases ht₀_range with ⟨i_0, hi_0⟩
  obtain ⟨i_l, hi_l⟩ := (bijective_nextFin hk).2 i_0
  set s_l := vSpaceArc Γ.V Γ.finite_V f hk i_l with hs_l_def
  obtain ⟨a_l', b_l', ha_l', hab_l', hb_l', ha_l'_eq, hb_l'_eq, hs_l_eq, hcl_l_eq⟩ :=
    vSpaceArc_eq_Ioo_from_vertex_angle hS hC f hk ht₀_mem i_l
  have hb_l'_eq_2pi : b_l' = t₀ + 2 * Real.pi := by
    rcases eq_or_lt_of_le hb_l' with h_eq | h_lt
    · exact h_eq
    · exfalso
      have h_eq_t₀ : b_l' = t₀ := by
        apply cuffPoint_injOn_Ico f t₀ ⟨ha_l'.trans hab_l'.le, h_lt⟩ ⟨le_rfl, by linarith [Real.pi_pos]⟩
        rw [hb_l'_eq, hi_l, hi_0]
      linarith
  subst b_l'
  have hs_l_ends : SpaceHasEnds Γ s_l (cuffPoint f a_l') (cuffPoint f (t₀ + 2 * Real.pi)) := by
    rw [ha_l'_eq, hb_l'_eq]
    exact spaceHasEnds_vSpaceArc hS hge2 hC f i_l
  have hs_l_uncov : ∀ j : Fin r, ¬ s_l ⊆ F_star j := by
    intro j hsub
    by_cases hj : j = j₁
    · subst hj
      set m := (max t₁ a_l' + (t₀ + 2 * Real.pi)) / 2 with hm_def
      have hmax : max t₁ a_l' < t₀ + 2 * Real.pi := max_lt ht₁_lt hab_l'
      have hm_s : cuffPoint f m ∈ s_l := by
        rw [hs_l_def, hs_l_eq]; exact ⟨m, ⟨by linarith [le_max_right t₁ a_l'], by linarith⟩, rfl⟩
      have hm_diff : cuffPoint f m ∈ C \ F_star j := by
        rw [hC_diff_F₁]; exact ⟨m, ⟨by linarith [le_max_left t₁ a_l'], by linarith⟩, rfl⟩
      exact hm_diff.2 (hsub hm_s)
    · have hcl_sub : closure s_l ⊆ F_star j :=
        closure_minimal hsub (isClosed_of_isSupportOfDrawing hS (hF_supp j))
      have ht₀_cl : cuffPoint f t₀ ∈ closure s_l := by
        rw [← cuffPoint_add_two_pi f t₀, hs_l_def, hcl_l_eq]
        exact ⟨t₀ + 2 * Real.pi, ⟨hab_l'.le, le_rfl⟩, rfl⟩
      exact Set.disjoint_left.mp (hF_disj (Ne.symm hj)) ht₀_in_F₁ (hcl_sub ht₀_cl)
  have ht₁_le_al' : t₁ ≤ a_l' := by
    have hdisj : Disjoint s_l (F_star j₁) :=
      (space_subset_or_disjoint_of_isSupportOfDrawing hS hs_l_ends.1 (hF_supp j₁)).resolve_left
        (fun h => hs_l_uncov j₁ h.1)
    rw [hs_l_def, hs_l_eq, hF₁_eq] at hdisj
    exact left_end_ge_of_Ioo_disjoint_Icc f ht₀_le_t₁ ht₁_lt ha_l' hab_l' le_rfl hdisj
  refine ⟨s_r, s_l, cuffPoint f t₁, cuffPoint f b_r', cuffPoint f a_l',
    cuffPoint f (t₀ + 2 * Real.pi),
    (vSpaceArc_subset_diff Γ.V Γ.finite_V f hk i_r).trans sdiff_subset,
    (vSpaceArc_subset_diff Γ.V Γ.finite_V f hk i_l).trans sdiff_subset,
    hs_r_ends, hs_l_ends, hs_r_uncov, hs_l_uncov, ?_, ?_⟩
  · -- Part 1: separating F_star j₁ from F_star j₂ (j₁ ≠ j₂)
    intro j₂ hj₁₂ hF₂C X₁ X₂ hX₁_ne hX₁_sub hX₂_ne hX₂_sub u₁ hu₁ u₂ hu₂
    have hF₂_disj_F₁ : Disjoint (F_star j₂) (F_star j₁) := hF_disj hj₁₂.symm
    have hF₂_disj_sr : Disjoint s_r (F_star j₂) :=
      (space_subset_or_disjoint_of_isSupportOfDrawing hS hs_r_ends.1 (hF_supp j₂)).resolve_left
        (fun h => hs_r_uncov j₂ h.1)
    have hF₂_disj_sl : Disjoint s_l (F_star j₂) :=
      (space_subset_or_disjoint_of_isSupportOfDrawing hS hs_l_ends.1 (hF_supp j₂)).resolve_left
        (fun h => hs_l_uncov j₂ h.1)
    have hF₂_sub_Icc : F_star j₂ ⊆ cuffPoint f '' Icc b_r' a_l' := by
      intro z hz
      obtain ⟨tz, htz, rfl⟩ := exists_cuffPoint_mem_Ico f t₀ (hF₂C hz)
      have htz_gt_t₁ : t₁ < tz := by
        by_contra hle
        push Not at hle
        have hz_F₁ : cuffPoint f tz ∈ F_star j₁ := by
          rw [hF₁_eq]; exact ⟨tz, ⟨htz.1, hle⟩, rfl⟩
        exact Set.disjoint_left.mp hF₂_disj_F₁ hz hz_F₁
      have htz_ge_br : b_r' ≤ tz := by
        by_contra hlt
        push Not at hlt
        have hz_sr : cuffPoint f tz ∈ s_r := by
          rw [hs_r_def, hs_r_eq]; exact ⟨tz, ⟨htz_gt_t₁, hlt⟩, rfl⟩
        exact Set.disjoint_left.mp hF₂_disj_sr hz_sr hz
      have htz_le_al : tz ≤ a_l' := by
        by_contra hgt
        push Not at hgt
        have hz_sl : cuffPoint f tz ∈ s_l := by
          rw [hs_l_def, hs_l_eq]; exact ⟨tz, ⟨hgt, htz.2⟩, rfl⟩
        exact Set.disjoint_left.mp hF₂_disj_sl hz_sl hz
      exact ⟨tz, ⟨htz_ge_br, htz_le_al⟩, rfl⟩
    have hbr_le_al : b_r' ≤ a_l' := by
      rcases hX₂_ne with ⟨z₀, hz₀⟩
      rcases hF₂_sub_Icc (hX₂_sub hz₀) with ⟨tz₀, ⟨h1, h2⟩, _⟩
      exact h1.trans h2
    have hu₁_angle : ∃ τ₁ : ℝ, t₁ ≤ τ₁ ∧ τ₁ ≤ b_r' ∧ cuffPoint f τ₁ = u₁ := by
      rcases hu₁ with rfl | rfl
      · exact ⟨t₁, le_rfl, hab_r'.le, rfl⟩
      · exact ⟨b_r', hab_r'.le, le_rfl, rfl⟩
    have hu₂_angle : ∃ τ₂ : ℝ, a_l' ≤ τ₂ ∧ τ₂ ≤ t₀ + 2 * Real.pi ∧ cuffPoint f τ₂ = u₂ := by
      rcases hu₂ with rfl | rfl
      · exact ⟨a_l', le_rfl, hab_l'.le, rfl⟩
      · exact ⟨t₀ + 2 * Real.pi, hab_l'.le, le_rfl, rfl⟩
    rcases hu₁_angle with ⟨τ₁, hτ₁_ge, hτ₁_le, hτ₁_eq⟩
    rcases hu₂_angle with ⟨τ₂, hτ₂_ge, hτ₂_le, hτ₂_eq⟩
    exact ⟨f, t₀, t₁, τ₁, b_r', a_l', τ₂,
      ht₀_le_t₁, hτ₁_ge, hτ₁_le, hbr_le_al, hτ₂_ge, hτ₂_le,
      hτ₁_eq, hτ₂_eq,
      hX₁_ne, hX₁_sub.trans (by rw [hF₁_eq]),
      hX₂_ne, hX₂_sub.trans hF₂_sub_Icc⟩
  · -- Part 2: LiesBetweenInSupport Γ (F_star j₁) s₁ s₂ u
    rintro s₁ s₂ u ⟨⟨huF₁, huV⟩, hs₁, hs₂, hs₁F₁, hs₂F₁, I₁, I₂, hI₁, hI₂, hI_union, hI_inter,
      hs₁I₁, hs₂I₂⟩ u₀ hu₀
    have hs₁C : s₁ ⊆ C := hs₁F₁.trans hF₁C
    have hs₂C : s₂ ⊆ C := hs₂F₁.trans hF₁C
    obtain ⟨k₁, rfl⟩ := exists_index_of_mem_drawingSpaces_subset_cuff hS hge2 hs₁ hC hs₁C f
    obtain ⟨k₂, rfl⟩ := exists_index_of_mem_drawingSpaces_subset_cuff hS hge2 hs₂ hC hs₂C f
    obtain ⟨α₁, β₁, hα₁, hαβ₁, hβ₁, _, _, hs₁_eq, hcl₁_eq⟩ :=
      vSpaceArc_eq_Ioo_from_vertex_angle hS hC f hk ht₀_mem k₁
    obtain ⟨α₂, β₂, hα₂, hαβ₂, hβ₂, _, _, hs₂_eq, hcl₂_eq⟩ :=
      vSpaceArc_eq_Ioo_from_vertex_angle hS hC f hk ht₀_mem k₂
    have hβ₁_le_t₁ : β₁ ≤ t₁ := by
      apply right_end_le_of_Ioo_subset_Icc f ht₀_le_t₁ ht₁_lt hα₁ hαβ₁ hβ₁
      rw [← hs₁_eq, ← hF₁_eq]; exact hs₁F₁
    have hβ₂_le_t₁ : β₂ ≤ t₁ := by
      apply right_end_le_of_Ioo_subset_Icc f ht₀_le_t₁ ht₁_lt hα₂ hαβ₂ hβ₂
      rw [← hs₂_eq, ← hF₁_eq]; exact hs₂F₁
    have hu_in_Icc : u ∈ cuffPoint f '' Icc t₀ t₁ := by rwa [← hF₁_eq]
    rcases hu_in_Icc with ⟨tu, ⟨htu_ge, htu_le⟩, htu_eq⟩
    have htu_not_1 : tu ∉ Ioo α₁ β₁ := by
      intro hmem
      have hu_s₁ : u ∈ vSpaceArc Γ.V Γ.finite_V f hk k₁ := by
        rw [← htu_eq, hs₁_eq]; exact ⟨tu, hmem, rfl⟩
      exact (subset_bd_diff_of_mem_drawingSpaces hs₁ hu_s₁).2 huV
    have htu_not_2 : tu ∉ Ioo α₂ β₂ := by
      intro hmem
      have hu_s₂ : u ∈ vSpaceArc Γ.V Γ.finite_V f hk k₂ := by
        rw [← htu_eq, hs₂_eq]; exact ⟨tu, hmem, rfl⟩
      exact (subset_bd_diff_of_mem_drawingSpaces hs₂ hu_s₂).2 huV
    have h1_side : β₁ ≤ tu ∨ tu ≤ α₁ := by
      by_cases h : β₁ ≤ tu
      · exact Or.inl h
      · right
        by_contra h'
        push Not at h h'
        exact htu_not_1 ⟨h', h⟩
    have h2_side : β₂ ≤ tu ∨ tu ≤ α₂ := by
      by_cases h : β₂ ≤ tu
      · exact Or.inl h
      · right
        by_contra h'
        push Not at h h'
        exact htu_not_2 ⟨h', h⟩
    have hcI₁ : IsClosed I₁ := isClosed_of_isSupportOfDrawing hS hI₁
    have hcI₂ : IsClosed I₂ := isClosed_of_isSupportOfDrawing hS hI₂
    have hnot_both_left : ¬ (β₁ ≤ tu ∧ β₂ ≤ tu) := by
      rintro ⟨h1, h2⟩
      let J : Set S := cuffPoint f '' Ico (min α₁ α₂) tu
      have hJ_pre : IsPreconnected J := isPreconnected_Ico.image _ (cuffPoint_continuous f).continuousOn
      have hJ_cov : J ⊆ I₁ ∪ I₂ := by
        rw [hI_union, hF₁_eq]
        exact image_mono (fun t ht => ⟨le_min hα₁ hα₂ |>.trans ht.1, ht.2.le.trans htu_le⟩)
      have hJ_not_u : u ∉ J := by
        rintro ⟨t, ht, h_eq⟩
        have h_eq' : cuffPoint f t = cuffPoint f tu := h_eq.trans htu_eq.symm
        have ht_Ico : t ∈ Ico t₀ (t₀ + 2 * Real.pi) :=
          ⟨(le_min hα₁ hα₂).trans ht.1, ht.2.trans_le (htu_le.trans ht₁_lt.le)⟩
        have htu_Ico : tu ∈ Ico t₀ (t₀ + 2 * Real.pi) := ⟨htu_ge, htu_le.trans_lt ht₁_lt⟩
        have h_t_tu := cuffPoint_injOn_Ico f t₀ ht_Ico htu_Ico h_eq'
        exact ht.2.ne h_t_tu
      set m₁ := (α₁ + β₁) / 2 with hm₁_def
      have hm₁_J : cuffPoint f m₁ ∈ J :=
        ⟨m₁, ⟨by linarith [min_le_left α₁ α₂], by linarith⟩, rfl⟩
      have hm₁_I₁ : cuffPoint f m₁ ∈ I₁ := by
        apply hs₁I₁; rw [hs₁_eq]; exact ⟨m₁, ⟨by linarith, by linarith⟩, rfl⟩
      set m₂ := (α₂ + β₂) / 2 with hm₂_def
      have hm₂_J : cuffPoint f m₂ ∈ J :=
        ⟨m₂, ⟨by linarith [min_le_right α₁ α₂], by linarith⟩, rfl⟩
      have hm₂_I₂ : cuffPoint f m₂ ∈ I₂ := by
        apply hs₂I₂; rw [hs₂_eq]; exact ⟨m₂, ⟨by linarith, by linarith⟩, rfl⟩
      obtain ⟨z, hzJ, hzI₁, hzI₂⟩ := isPreconnected_closed_iff.mp hJ_pre I₁ I₂ hcI₁ hcI₂ hJ_cov
        ⟨_, hm₁_J, hm₁_I₁⟩ ⟨_, hm₂_J, hm₂_I₂⟩
      have hzu : z = u := by
        have : z ∈ I₁ ∩ I₂ := ⟨hzI₁, hzI₂⟩
        rwa [hI_inter, mem_singleton_iff] at this
      exact hJ_not_u (hzu ▸ hzJ)
    have hnot_both_right : ¬ (tu ≤ α₁ ∧ tu ≤ α₂) := by
      rintro ⟨h1, h2⟩
      let J : Set S := cuffPoint f '' Ioc tu (max β₁ β₂)
      have hJ_pre : IsPreconnected J := isPreconnected_Ioc.image _ (cuffPoint_continuous f).continuousOn
      have hJ_cov : J ⊆ I₁ ∪ I₂ := by
        rw [hI_union, hF₁_eq]
        exact image_mono (fun t ht => ⟨htu_ge.trans ht.1.le, ht.2.trans (max_le hβ₁_le_t₁ hβ₂_le_t₁)⟩)
      have hJ_not_u : u ∉ J := by
        rintro ⟨t, ht, h_eq⟩
        have h_eq' : cuffPoint f t = cuffPoint f tu := h_eq.trans htu_eq.symm
        have ht_Ico : t ∈ Ico t₀ (t₀ + 2 * Real.pi) :=
          ⟨htu_ge.trans ht.1.le, (ht.2.trans (max_le hβ₁_le_t₁ hβ₂_le_t₁)).trans_lt ht₁_lt⟩
        have htu_Ico : tu ∈ Ico t₀ (t₀ + 2 * Real.pi) := ⟨htu_ge, htu_le.trans_lt ht₁_lt⟩
        have h_t_tu := cuffPoint_injOn_Ico f t₀ ht_Ico htu_Ico h_eq'
        exact ht.1.ne' h_t_tu
      set m₁ := (α₁ + β₁) / 2 with hm₁_def
      have hm₁_J : cuffPoint f m₁ ∈ J :=
        ⟨m₁, ⟨by linarith, by linarith [le_max_left β₁ β₂]⟩, rfl⟩
      have hm₁_I₁ : cuffPoint f m₁ ∈ I₁ := by
        apply hs₁I₁; rw [hs₁_eq]; exact ⟨m₁, ⟨by linarith, by linarith⟩, rfl⟩
      set m₂ := (α₂ + β₂) / 2 with hm₂_def
      have hm₂_J : cuffPoint f m₂ ∈ J :=
        ⟨m₂, ⟨by linarith, by linarith [le_max_right β₁ β₂]⟩, rfl⟩
      have hm₂_I₂ : cuffPoint f m₂ ∈ I₂ := by
        apply hs₂I₂; rw [hs₂_eq]; exact ⟨m₂, ⟨by linarith, by linarith⟩, rfl⟩
      obtain ⟨z, hzJ, hzI₁, hzI₂⟩ := isPreconnected_closed_iff.mp hJ_pre I₁ I₂ hcI₁ hcI₂ hJ_cov
        ⟨_, hm₁_J, hm₁_I₁⟩ ⟨_, hm₂_J, hm₂_I₂⟩
      have hzu : z = u := by
        have : z ∈ I₁ ∩ I₂ := ⟨hzI₁, hzI₂⟩
        rwa [hI_inter, mem_singleton_iff] at this
      exact hJ_not_u (hzu ▸ hzJ)
    have hu₀_angle : ∃ τ₀ : ℝ, t₁ ≤ τ₀ ∧ τ₀ ≤ b_r' ∧ cuffPoint f τ₀ = u₀ := by
      rcases hu₀ with rfl | rfl
      · exact ⟨t₁, le_rfl, hab_r'.le, rfl⟩
      · exact ⟨b_r', hab_r'.le, le_rfl, rfl⟩
    rcases hu₀_angle with ⟨τ₀, hτ₀_ge, hτ₀_le, hτ₀_eq⟩
    have hcl₁_C : closure (vSpaceArc Γ.V Γ.finite_V f hk k₁) ∩ C = cuffPoint f '' Icc α₁ β₁ := by
      rw [hcl₁_eq, inter_eq_left]; rintro _ ⟨t, _, rfl⟩; exact cuffPoint_mem f t
    have hcl₂_C : closure (vSpaceArc Γ.V Γ.finite_V f hk k₂) ∩ C = cuffPoint f '' Icc α₂ β₂ := by
      rw [hcl₂_eq, inter_eq_left]; rintro _ ⟨t, _, rfl⟩; exact cuffPoint_mem f t
    rcases h1_side with h1 | h1 <;> rcases h2_side with h2 | h2
    · exact (hnot_both_left ⟨h1, h2⟩).elim
    · left
      refine ⟨f, α₁, β₁, tu, α₂, β₂, τ₀,
        hαβ₁.le, h1, h2, hαβ₂.le, hβ₂_le_t₁.trans hτ₀_ge, by linarith [hb_r', hα₁],
        htu_eq, hτ₀_eq, ?_, ?_, ?_, ?_⟩
      · rw [hcl₁_C]; exact ⟨cuffPoint f α₁, ⟨α₁, ⟨le_rfl, hαβ₁.le⟩, rfl⟩⟩
      · rw [hcl₁_C]
      · rw [hcl₂_C]; exact ⟨cuffPoint f α₂, ⟨α₂, ⟨le_rfl, hαβ₂.le⟩, rfl⟩⟩
      · rw [hcl₂_C]
    · right
      refine ⟨f, α₂, β₂, tu, α₁, β₁, τ₀,
        hαβ₂.le, h2, h1, hαβ₁.le, hβ₁_le_t₁.trans hτ₀_ge, by linarith [hb_r', hα₂],
        htu_eq, hτ₀_eq, ?_, ?_, ?_, ?_⟩
      · rw [hcl₂_C]; exact ⟨cuffPoint f α₂, ⟨α₂, ⟨le_rfl, hαβ₂.le⟩, rfl⟩⟩
      · rw [hcl₂_C]
      · rw [hcl₁_C]; exact ⟨cuffPoint f α₁, ⟨α₁, ⟨le_rfl, hαβ₁.le⟩, rfl⟩⟩
      · rw [hcl₁_C]
    · exact (hnot_both_right ⟨h1, h2⟩).elim

/-- If `F_star : Fin r → Set S` are supports covering `Γ.V ∩ bd S`, then there are at most `r`
uncovered spaces `{s ∈ drawingSpaces Γ | ∀ j : Fin r, ¬ s ⊆ F_star j}`. -/
theorem ncard_uncovered_spaces_le (hS : IsSurface S) {Γ : Surface.Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard)
    {r : ℕ} {F_star : Fin r → Set S}
    (hF_supp : ∀ j : Fin r, IsSupportOfDrawing Γ (F_star j))
    (hF_cov : Γ.V ∩ bd S ⊆ ⋃ j : Fin r, F_star j) :
    {s ∈ drawingSpaces Γ | ∀ j : Fin r, ¬ s ⊆ F_star j}.ncard ≤ r := by
  have : T2Space S := hS.2.1
  -- For each j : Fin r, pick the unique space s_left_of j ending at the start angle t₀(j) of F_star j
  have hex_left : ∀ j : Fin r, ∃ s_j : Set S,
      ∀ s ∈ drawingSpaces Γ, (¬ s ⊆ F_star j) →
        (∃ C ∈ cuffs S, ∃ (hC : C ∈ cuffs S) (i : Fin (Γ.V ∩ C).ncard),
          s = vSpaceArc Γ.V Γ.finite_V (cuffHomeo hS hC) (hge2 C hC) i ∧
          vNode Γ.V Γ.finite_V (cuffHomeo hS hC) (nextFin (hge2 C hC) i) ∈ F_star j) →
        s = s_j := by
    intro j
    rcases hF_supp j with ⟨endA, endB, hFj_ends⟩
    obtain ⟨Cj, hCj, hFjC⟩ := exists_cuff_of_supportHasEnds hFj_ends
    let fj := cuffHomeo hS hCj
    have hkj := hge2 Cj hCj
    have hends_mem := ends_mem_of_supportHasEnds hFj_ends
    obtain ⟨t₀, ht₀_Ico, t₁, ⟨ht₀_le_t₁, ht₁_lt⟩, h_ab_eq, hFj_eq, _⟩ :=
      support_eq_cuffPoint_Icc hS hCj fj hFj_ends hFjC
    have ht₀_mem : cuffPoint fj t₀ ∈ Γ.V ∩ Cj := by
      refine ⟨?_, cuffPoint_mem fj t₀⟩
      rcases h_ab_eq with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
      · exact hends_mem.2.2.1.1
      · exact hends_mem.2.2.2.1.1
    have ht₀_range : cuffPoint fj t₀ ∈ Set.range (vNode Γ.V Γ.finite_V fj) := by
      rw [range_vNode]; exact ht₀_mem
    rcases ht₀_range with ⟨i_0, hi_0⟩
    obtain ⟨i_l, hi_l⟩ := (bijective_nextFin hkj).2 i_0
    refine ⟨vSpaceArc Γ.V Γ.finite_V fj hkj i_l, ?_⟩
    rintro s hs hnot_sub ⟨C, _, hC, i, rfl, hnode_in_Fj⟩
    have hC_eq : C = Cj := by
      by_contra hne
      have hnode_C : vNode Γ.V Γ.finite_V (cuffHomeo hS hC) (nextFin (hge2 C hC) i) ∈ C :=
        (vNode_mem Γ.V Γ.finite_V (cuffHomeo hS hC) (nextFin (hge2 C hC) i)).2
      exact Set.disjoint_left.mp (cuffs_disjoint hC hCj hne) hnode_C (hFjC hnode_in_Fj)
    subst hC_eq
    obtain ⟨a', b', ha', hab', hb', _, hb'_eq, hs_eq, _⟩ :=
      vSpaceArc_eq_Ioo_from_vertex_angle hS hC fj hkj ht₀_mem i
    have hdisj : Disjoint (vSpaceArc Γ.V Γ.finite_V fj hkj i) (F_star j) :=
      (space_subset_or_disjoint_of_supportHasEnds hS hs hFj_ends).resolve_left
        (fun h => hnot_sub h.1)
    have ht₁_le_a' : t₁ ≤ a' := by
      rw [hs_eq, hFj_eq] at hdisj
      exact left_end_ge_of_Ioo_disjoint_Icc fj ht₀_le_t₁ ht₁_lt ha' hab' hb' hdisj
    have hb'_eq_2pi : b' = t₀ + 2 * Real.pi := by
      rcases eq_or_lt_of_le hb' with h_eq | h_lt
      · exact h_eq
      · exfalso
        have hb'_in_Fj : cuffPoint fj b' ∈ cuffPoint fj '' Icc t₀ t₁ := by
          rw [← hFj_eq, hb'_eq]; exact hnode_in_Fj
        rcases hb'_in_Fj with ⟨tb, ⟨htb1, htb2⟩, htb_eq⟩
        have h_eq_tb : tb = b' :=
          cuffPoint_injOn_Ico fj t₀ ⟨htb1, htb2.trans_lt ht₁_lt⟩ ⟨ha'.trans hab'.le, h_lt⟩ htb_eq
        linarith
    have hnode_eq : vNode Γ.V Γ.finite_V fj (nextFin hkj i) = vNode Γ.V Γ.finite_V fj i_0 := by
      rw [← hb'_eq, hb'_eq_2pi, cuffPoint_add_two_pi, hi_0]
    have hnext_eq : nextFin hkj i = nextFin hkj i_l := by
      rw [hi_l]
      exact injective_vNode Γ.V Γ.finite_V fj hnode_eq
    have hi_eq : i = i_l := (bijective_nextFin hkj).1 hnext_eq
    rw [hi_eq]
  let s_left_of : Fin r → Set S := fun j => Classical.choose (hex_left j)
  have hsub_range : {s ∈ drawingSpaces Γ | ∀ j : Fin r, ¬ s ⊆ F_star j} ⊆ Set.range s_left_of := by
    rintro s ⟨hs, huncov⟩
    obtain ⟨C, hC, hsC, _⟩ := exists_cuff_of_mem_drawingSpaces hS hge2 hs
    obtain ⟨i, rfl⟩ := exists_index_of_mem_drawingSpaces_subset_cuff hS hge2 hs hC hsC (cuffHomeo hS hC)
    have hnode_bd : vNode Γ.V Γ.finite_V (cuffHomeo hS hC) (nextFin (hge2 C hC) i) ∈ Γ.V ∩ bd S := by
      have hn := vNode_mem Γ.V Γ.finite_V (cuffHomeo hS hC) (nextFin (hge2 C hC) i)
      refine ⟨hn.1, ?_⟩
      rw [← sUnion_cuffs (S := S)]
      exact ⟨C, hC, hn.2⟩
    have hnode_union := hF_cov hnode_bd
    rw [mem_iUnion] at hnode_union
    rcases hnode_union with ⟨j, hj⟩
    refine ⟨j, ((Classical.choose_spec (hex_left j)) _ hs (huncov j) ⟨C, hC, hC, i, rfl, hj⟩).symm⟩
  have hfin_range : (Set.range s_left_of).Finite := Set.finite_range s_left_of
  calc {s ∈ drawingSpaces Γ | ∀ j : Fin r, ¬ s ⊆ F_star j}.ncard
      ≤ (Set.range s_left_of).ncard := ncard_le_ncard hsub_range hfin_range
    _ = (s_left_of '' Set.univ).ncard := by rw [image_univ]
    _ ≤ (Set.univ : Set (Fin r)).ncard := ncard_image_le finite_univ
    _ = r := by rw [ncard_univ, Nat.card_fin]

/-- For any boundary unit `x` in `C` (`x = .vertex w` with `w ∈ C` or `x = .space s` with
`s ∈ drawingSpaces Γ` and `s ⊆ C`), if `closure x.toSet ∩ C ⊆ cuffPoint g '' Icc L R` where
`t₀ ≤ L ≤ R ≤ t₀ + 2 * Real.pi` and `cuffPoint g t₀, cuffPoint g L, cuffPoint g R ∈ Γ.V ∩ C`, then
there exist `α β : ℝ` with `L ≤ α ≤ β ≤ R` such that `closure x.toSet ∩ C = cuffPoint g '' Icc α β`. -/
theorem unit_closure_eq_Icc_in_interval (hS : IsSurface S) {Γ : Surface.Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) {C : Set S} (hC : C ∈ cuffs S)
    (g : Circle ≃ₜ C) {t₀ L R : ℝ} (hL : t₀ ≤ L) (_hLR : L ≤ R) (hR : R ≤ t₀ + 2 * Real.pi)
    (ht₀ : cuffPoint g t₀ ∈ Γ.V ∩ C) (hL_mem : cuffPoint g L ∈ Γ.V ∩ C)
    (hR_mem : cuffPoint g R ∈ Γ.V ∩ C) (x : BoundaryUnit S)
    (hx_unit : (∃ w ∈ C, x = .vertex w) ∨ (∃ s ∈ drawingSpaces Γ, s ⊆ C ∧ x = .space s))
    (hx_sub : closure x.toSet ∩ C ⊆ cuffPoint g '' Icc L R) :
    ∃ α β : ℝ, L ≤ α ∧ α ≤ β ∧ β ≤ R ∧ closure x.toSet ∩ C = cuffPoint g '' Icc α β := by
  have : T2Space S := hS.2.1
  rcases hx_unit with ⟨w, hwC, rfl⟩ | ⟨s, hs, hsC, rfl⟩
  · have hw_cl : w ∈ closure (BoundaryUnit.vertex w).toSet ∩ C :=
      ⟨subset_closure (mem_singleton w), hwC⟩
    rcases hx_sub hw_cl with ⟨α, ⟨hα1, hα2⟩, hα_eq⟩
    refine ⟨α, α, hα1, le_rfl, hα2, ?_⟩
    simp only [BoundaryUnit.toSet, closure_singleton, Icc_self, image_singleton, hα_eq]
    exact inter_eq_left.mpr (singleton_subset_iff.mpr hwC)
  · have hk := hge2 C hC
    obtain ⟨i, rfl⟩ := exists_index_of_mem_drawingSpaces_subset_cuff hS hge2 hs hC hsC g
    obtain ⟨α, β, hα, hαβ, hβ, _, _, hs_eq, hcl_eq⟩ :=
      vSpaceArc_eq_Ioo_from_vertex_angle hS hC g hk ht₀ i
    have hcl_C : closure (BoundaryUnit.space (vSpaceArc Γ.V Γ.finite_V g hk i)).toSet ∩ C =
        cuffPoint g '' Icc α β := by
      simp only [BoundaryUnit.toSet]
      rw [hcl_eq, inter_eq_left]
      rintro _ ⟨t, _, rfl⟩
      exact cuffPoint_mem g t
    set m := (α + β) / 2 with hm_def
    have hm_s : cuffPoint g m ∈ vSpaceArc Γ.V Γ.finite_V g hk i := by
      rw [hs_eq]; exact ⟨m, ⟨by linarith, by linarith⟩, rfl⟩
    have hm_notV : cuffPoint g m ∉ Γ.V :=
      (subset_bd_diff_of_mem_drawingSpaces hs hm_s).2
    have hm_cl : cuffPoint g m ∈
        closure (BoundaryUnit.space (vSpaceArc Γ.V Γ.finite_V g hk i)).toSet ∩ C := by
      rw [hcl_C]; exact ⟨m, ⟨by linarith, by linarith⟩, rfl⟩
    rcases hx_sub hm_cl with ⟨t, ⟨ht1, ht2⟩, ht_eq⟩
    have ht_lt_2pi : t < t₀ + 2 * Real.pi := by
      rcases eq_or_lt_of_le (ht2.trans hR) with h_eq | h_lt
      · exfalso
        rw [h_eq, cuffPoint_add_two_pi] at ht_eq
        exact hm_notV (ht_eq ▸ ht₀.1)
      · exact h_lt
    have htm : t = m :=
      cuffPoint_injOn_Ico g t₀ ⟨hL.trans ht1, ht_lt_2pi⟩ ⟨by linarith, by linarith⟩ ht_eq
    have hL_not_Ioo : L ∉ Ioo α β := by
      intro hmem
      have hL_s : cuffPoint g L ∈ vSpaceArc Γ.V Γ.finite_V g hk i := by
        rw [hs_eq]; exact ⟨L, hmem, rfl⟩
      exact (subset_bd_diff_of_mem_drawingSpaces hs hL_s).2 hL_mem.1
    have hR_not_Ioo : R ∉ Ioo α β := by
      intro hmem
      have hR_s : cuffPoint g R ∈ vSpaceArc Γ.V Γ.finite_V g hk i := by
        rw [hs_eq]; exact ⟨R, hmem, rfl⟩
      exact (subset_bd_diff_of_mem_drawingSpaces hs hR_s).2 hR_mem.1
    have hL_le_α : L ≤ α := by
      by_contra hlt
      push Not at hlt
      exact hL_not_Ioo ⟨hlt, by linarith⟩
    have hβ_le_R : β ≤ R := by
      by_contra hgt
      push Not at hgt
      exact hR_not_Ioo ⟨by linarith, hgt⟩
    exact ⟨α, β, hL_le_α, hαβ.le, hβ_le_R, hcl_C⟩

/-- Given a space `s_star ∈ drawingSpaces Γ` on a cuff `C ∈ cuffs S` with ends `u₁, u₂` and a third
vertex `u_star ∈ (Γ.V ∩ C) \ {u₁, u₂}`, there exist two supports `F₁, F₂ ⊆ C` with ends
`(u₁, u_star)` and `(u₂, u_star)` disjoint from `s_star` that partition `C \ s_star`, meet at
`{u_star}`, and satisfy the circular-order property needed for `(8.2)` `(P3)`. -/
theorem exists_split_supports_of_uncovered_space (hS : IsSurface S) {Γ : Surface.Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard)
    {C s_star : Set S} {u₁ u₂ u_star : S}
    (hC : C ∈ cuffs S) (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (hu_star : u_star ∈ Γ.V ∩ C) (hu_star_ne₁ : u_star ≠ u₁) (hu_star_ne₂ : u_star ≠ u₂) :
    ∃ F₁ F₂ : Set S,
      F₁ ⊆ C ∧ F₂ ⊆ C ∧
      SupportHasEnds Γ F₁ u₁ u_star ∧
      SupportHasEnds Γ F₂ u₂ u_star ∧
      u₁ ∈ F₁ ∧ u₁ ∉ F₂ ∧ u₂ ∈ F₂ ∧ u₂ ∉ F₁ ∧
      F₁ ∪ F₂ = C \ s_star ∧
      F₁ ∩ F₂ = {u_star} ∧
      Disjoint F₁ s_star ∧ Disjoint F₂ s_star ∧
      (∀ s ∈ drawingSpaces Γ, s ⊆ C → s ≠ s_star →
        (s ⊆ F₁ ∧ closure s ⊆ F₁ ∧ Disjoint s F₂) ∨
        (s ⊆ F₂ ∧ closure s ⊆ F₂ ∧ Disjoint s F₁)) ∧
      (∀ F ∈ ({F₁, F₂} : Set (Set S)),
        ∀ (x₁ x₂ : BoundaryUnit S) (a b : S),
          a ∈ C ∩ Γ.V → b ∈ C ∩ Γ.V →
          ((∃ w ∈ F, x₁ = .vertex w) ∨ (∃ s ∈ drawingSpaces Γ, s ⊆ F ∧ x₁ = .space s)) →
          ((∃ w ∈ F, x₂ = .vertex w) ∨ (∃ s ∈ drawingSpaces Γ, s ⊆ F ∧ x₂ = .space s)) →
          InCuffOrder C x₁.toSet a x₂.toSet b →
          (a ∈ F ∧ InCuffOrder C x₁.toSet a x₂.toSet u_star) ∨
          (b ∈ F ∧ InCuffOrder C x₁.toSet u_star x₂.toSet b)) := by
  have : T2Space S := hS.2.1
  let f := cuffHomeo hS hC
  have hk := hge2 C hC
  have hC_sub_bd : C ⊆ bd S := by
    intro z hz; rw [← sUnion_cuffs (S := S)]; exact ⟨C, hC, hz⟩
  obtain ⟨i₀, rfl⟩ := exists_index_of_mem_drawingSpaces_subset_cuff hS hge2 hs_star.1 hC hs_star_C f
  set a₀ := vAngle Γ.V Γ.finite_V f i₀
  set b₀ := vUpperAngle Γ.V Γ.finite_V f hk i₀
  have ha₀_lt_b₀ : a₀ < b₀ := vAngle_lt_vUpperAngle Γ.V Γ.finite_V f hk i₀
  have hb₀_lt : b₀ < a₀ + 2 * Real.pi := vUpperAngle_lt_add_two_pi Γ.V Γ.finite_V f hk i₀
  have hends_i₀ := spaceHasEnds_vSpaceArc hS hge2 hC f i₀
  have hpair := ends_pair_eq_of_spaceHasEnds hs_star hends_i₀
  have hu_star_ne_a₀_node : u_star ≠ vNode Γ.V Γ.finite_V f i₀ := by
    intro hu_eq
    have hmem : u_star ∈ ({u₁, u₂} : Set S) := by
      rw [hpair, hu_eq]; exact Or.inl rfl
    rcases hmem with rfl | rfl
    · exact hu_star_ne₁ rfl
    · exact hu_star_ne₂ rfl
  have hu_star_ne_b₀_node : u_star ≠ vNode Γ.V Γ.finite_V f (nextFin hk i₀) := by
    intro hu_eq
    have hmem : u_star ∈ ({u₁, u₂} : Set S) := by
      rw [hpair, hu_eq]; exact Or.inr rfl
    rcases hmem with rfl | rfl
    · exact hu_star_ne₁ rfl
    · exact hu_star_ne₂ rfl
  -- Locate u_star in Ioo b₀ (a₀ + 2 * Real.pi)
  obtain ⟨t_star, ht_star_Ico, ht_star_eq⟩ := exists_cuffPoint_mem_Ico f a₀ hu_star.2
  have ht_star_not_Ioo : t_star ∉ Ioo a₀ b₀ := by
    intro hmem
    have hu_s : u_star ∈ vSpaceArc Γ.V Γ.finite_V f hk i₀ := by
      rw [← ht_star_eq]; exact ⟨t_star, hmem, rfl⟩
    exact (subset_bd_diff_of_mem_drawingSpaces hs_star.1 hu_s).2 hu_star.1
  have ht_star_ne_a₀ : t_star ≠ a₀ := by
    intro h_eq
    exact hu_star_ne_a₀_node (by rw [← ht_star_eq, h_eq]; rfl)
  have ht_star_ne_b₀ : t_star ≠ b₀ := by
    intro h_eq
    exact hu_star_ne_b₀_node (by rw [← ht_star_eq, h_eq, cuffPoint_vUpperAngle])
  have hb₀_lt_t_star : b₀ < t_star := by
    by_contra hle
    push Not at hle
    have hlt_b₀ : t_star < b₀ := lt_of_le_of_ne hle ht_star_ne_b₀
    have hgt_a₀ : a₀ < t_star := lt_of_le_of_ne ht_star_Ico.1 (Ne.symm ht_star_ne_a₀)
    exact ht_star_not_Ioo ⟨hgt_a₀, hlt_b₀⟩
  have ht_star_lt : t_star < a₀ + 2 * Real.pi := ht_star_Ico.2
  -- Define the two arcs I_b (from b₀ to t_star) and I_a (from t_star to a₀ + 2 * Real.pi)
  let I_b : Set S := cuffPoint f '' Icc b₀ t_star
  let I_a : Set S := cuffPoint f '' Icc t_star (a₀ + 2 * Real.pi)
  have hIb_C : I_b ⊆ C := by rintro _ ⟨t, _, rfl⟩; exact cuffPoint_mem f t
  have hIa_C : I_a ⊆ C := by rintro _ ⟨t, _, rfl⟩; exact cuffPoint_mem f t
  have hIb_line : IsLineWithEnds I_b (vNode Γ.V Γ.finite_V f (nextFin hk i₀)) u_star := by
    rw [← cuffPoint_vUpperAngle Γ.V Γ.finite_V f hk i₀, ← ht_star_eq]
    exact isLineWithEnds_cuffPoint_Icc f hb₀_lt_t_star (by linarith [Real.pi_pos])
  have hIa_line : IsLineWithEnds I_a u_star (vNode Γ.V Γ.finite_V f i₀) := by
    have ha₀_2pi : cuffPoint f (a₀ + 2 * Real.pi) = vNode Γ.V Γ.finite_V f i₀ := by
      rw [cuffPoint_add_two_pi]; rfl
    rw [← ht_star_eq, ← ha₀_2pi]
    exact isLineWithEnds_cuffPoint_Icc f ht_star_lt (by linarith [ha₀_lt_b₀, hb₀_lt_t_star])
  have hIb_supp : SupportHasEnds Γ I_b (vNode Γ.V Γ.finite_V f (nextFin hk i₀)) u_star := by
    refine Or.inr ⟨hIb_C.trans hC_sub_bd, hu_star_ne_b₀_node.symm, hends_i₀.2.2.1, ⟨hu_star.1, hC_sub_bd hu_star.2⟩, hIb_line⟩
  have hIa_supp : SupportHasEnds Γ I_a (vNode Γ.V Γ.finite_V f i₀) u_star := by
    refine Or.inr ⟨hIa_C.trans hC_sub_bd, hu_star_ne_a₀_node.symm, hends_i₀.2.1, ⟨hu_star.1, hC_sub_bd hu_star.2⟩, hIa_line.symm⟩
  have hIb_Ia_union : I_b ∪ I_a = C \ vSpaceArc Γ.V Γ.finite_V f hk i₀ := by
    have hunion_Icc : I_b ∪ I_a = cuffPoint f '' Icc b₀ (a₀ + 2 * Real.pi) := by
      dsimp [I_b, I_a]
      rw [← image_union, Icc_union_Icc_eq_Icc hb₀_lt_t_star.le ht_star_lt.le]
    rw [hunion_Icc]
    ext z
    constructor
    · rintro ⟨t, ⟨ht1, ht2⟩, rfl⟩
      refine ⟨cuffPoint_mem f t, ?_⟩
      rintro ⟨s, ⟨hs1, hs2⟩, h_eq⟩
      rcases eq_or_lt_of_le ht2 with rfl | ht2_lt
      · rw [cuffPoint_add_two_pi] at h_eq
        have h_s_a₀ := cuffPoint_injOn_Ico f a₀ ⟨hs1.le, hs2.trans hb₀_lt⟩
          ⟨le_rfl, by linarith [Real.pi_pos]⟩ h_eq
        linarith
      · have h_s_t := cuffPoint_injOn_Ico f a₀ ⟨hs1.le, hs2.trans hb₀_lt⟩
          ⟨ha₀_lt_b₀.le.trans ht1, ht2_lt⟩ h_eq
        linarith
    · rintro ⟨hzC, hz_not⟩
      obtain ⟨t, ht, rfl⟩ := exists_cuffPoint_mem_Ico f a₀ hzC
      rcases eq_or_lt_of_le ht.1 with rfl | ht1_gt
      · exact ⟨a₀ + 2 * Real.pi, ⟨hb₀_lt.le, le_rfl⟩, by rw [cuffPoint_add_two_pi]⟩
      · have hge_b₀ : b₀ ≤ t := by
          by_contra hlt_b₀
          push Not at hlt_b₀
          exact hz_not ⟨t, ⟨ht1_gt, hlt_b₀⟩, rfl⟩
        exact ⟨t, ⟨hge_b₀, ht.2.le⟩, rfl⟩
  have hIb_Ia_inter : I_b ∩ I_a = {u_star} := by
    ext z
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨t₁, ⟨ht₁_1, ht₁_2⟩, rfl⟩, ⟨t₂, ⟨ht₂_1, ht₂_2⟩, h_eq⟩⟩
      rcases eq_or_lt_of_le ht₂_2 with rfl | ht₂_lt
      · rw [cuffPoint_add_two_pi] at h_eq
        have h1 := cuffPoint_injOn_Ico f a₀ ⟨ha₀_lt_b₀.le.trans ht₁_1, ht₁_2.trans_lt ht_star_lt⟩
          ⟨le_rfl, by linarith [Real.pi_pos]⟩ h_eq.symm
        linarith
      · have h1 := cuffPoint_injOn_Ico f a₀ ⟨ha₀_lt_b₀.le.trans ht₁_1, ht₁_2.trans_lt ht_star_lt⟩
          ⟨(ha₀_lt_b₀.trans hb₀_lt_t_star).le.trans ht₂_1, ht₂_lt⟩ h_eq.symm
        have ht₁_eq : t₁ = t_star := by linarith
        rw [ht₁_eq, ht_star_eq]
    · rintro rfl
      exact ⟨⟨t_star, ⟨hb₀_lt_t_star.le, le_rfl⟩, ht_star_eq⟩,
             ⟨t_star, ⟨le_rfl, ht_star_lt.le⟩, ht_star_eq⟩⟩
  have hn_next_in_Ib : vNode Γ.V Γ.finite_V f (nextFin hk i₀) ∈ I_b :=
    hIb_line.left_mem
  have hn_i₀_in_Ia : vNode Γ.V Γ.finite_V f i₀ ∈ I_a :=
    hIa_line.right_mem
  have hn_next_not_Ia : vNode Γ.V Γ.finite_V f (nextFin hk i₀) ∉ I_a := by
    intro hmem
    have : vNode Γ.V Γ.finite_V f (nextFin hk i₀) ∈ I_b ∩ I_a := ⟨hn_next_in_Ib, hmem⟩
    rw [hIb_Ia_inter, mem_singleton_iff] at this
    exact hu_star_ne_b₀_node this.symm
  have hn_i₀_not_Ib : vNode Γ.V Γ.finite_V f i₀ ∉ I_b := by
    intro hmem
    have : vNode Γ.V Γ.finite_V f i₀ ∈ I_b ∩ I_a := ⟨hmem, hn_i₀_in_Ia⟩
    rw [hIb_Ia_inter, mem_singleton_iff] at this
    exact hu_star_ne_a₀_node this.symm
  -- Helper for both I_b and I_a: C \ I is connected, nonempty, and has u_star in its closure
  have h_comp_conn : ∀ F ∈ ({I_b, I_a} : Set (Set S)),
      IsClosed F ∧ IsPreconnected (C \ F) ∧ u_star ∈ closure (C \ F) := by
    intro F hF_mem
    rcases hF_mem with rfl | rfl
    · refine ⟨isClosed_of_supportHasEnds hS hIb_supp, ?_, ?_⟩
      · have hdiff : C \ I_b = cuffPoint f '' Ioo t_star (b₀ + 2 * Real.pi) :=
          cuff_diff_cuffPoint_Icc f hb₀_lt_t_star.le (by linarith [Real.pi_pos])
        rw [hdiff]
        exact isPreconnected_Ioo.image _ (cuffPoint_continuous f).continuousOn
      · have hdiff : C \ I_b = cuffPoint f '' Ioo t_star (b₀ + 2 * Real.pi) :=
          cuff_diff_cuffPoint_Icc f hb₀_lt_t_star.le (by linarith [Real.pi_pos])
        rw [hdiff, ← ht_star_eq]
        have hlt_2pi : t_star < b₀ + 2 * Real.pi := by linarith [ha₀_lt_b₀, ht_star_lt]
        have hcl_sub := image_closure_subset_closure_image (cuffPoint_continuous f)
          (s := Ioo t_star (b₀ + 2 * Real.pi))
        rw [closure_Ioo (ne_of_lt hlt_2pi)] at hcl_sub
        exact hcl_sub ⟨t_star, ⟨le_rfl, hlt_2pi.le⟩, rfl⟩
    · refine ⟨isClosed_of_supportHasEnds hS hIa_supp, ?_, ?_⟩
      · have hdiff : C \ I_a = cuffPoint f '' Ioo (a₀ + 2 * Real.pi) (t_star + 2 * Real.pi) :=
          cuff_diff_cuffPoint_Icc f ht_star_lt.le (by linarith [ha₀_lt_b₀, hb₀_lt_t_star])
        rw [hdiff]
        exact isPreconnected_Ioo.image _ (cuffPoint_continuous f).continuousOn
      · have hdiff : C \ I_a = cuffPoint f '' Ioo (a₀ + 2 * Real.pi) (t_star + 2 * Real.pi) :=
          cuff_diff_cuffPoint_Icc f ht_star_lt.le (by linarith [ha₀_lt_b₀, hb₀_lt_t_star])
        have hu_2pi : cuffPoint f (t_star + 2 * Real.pi) = u_star := by
          rw [cuffPoint_add_two_pi, ht_star_eq]
        rw [hdiff, ← hu_2pi]
        have hlt_2pi : a₀ + 2 * Real.pi < t_star + 2 * Real.pi := by linarith [ha₀_lt_b₀, hb₀_lt_t_star]
        have hcl_sub := image_closure_subset_closure_image (cuffPoint_continuous f)
          (s := Ioo (a₀ + 2 * Real.pi) (t_star + 2 * Real.pi))
        rw [closure_Ioo (ne_of_lt hlt_2pi)] at hcl_sub
        exact hcl_sub ⟨t_star + 2 * Real.pi, ⟨hlt_2pi.le, le_rfl⟩, rfl⟩
  -- Circular order helper for any F ∈ {I_b, I_a}
  have h_order_prop : ∀ F ∈ ({I_b, I_a} : Set (Set S)),
      ∀ (x₁ x₂ : BoundaryUnit S) (a b : S),
        a ∈ C ∩ Γ.V → b ∈ C ∩ Γ.V →
        ((∃ w ∈ F, x₁ = .vertex w) ∨ (∃ s ∈ drawingSpaces Γ, s ⊆ F ∧ x₁ = .space s)) →
        ((∃ w ∈ F, x₂ = .vertex w) ∨ (∃ s ∈ drawingSpaces Γ, s ⊆ F ∧ x₂ = .space s)) →
        InCuffOrder C x₁.toSet a x₂.toSet b →
        (a ∈ F ∧ InCuffOrder C x₁.toSet a x₂.toSet u_star) ∨
        (b ∈ F ∧ InCuffOrder C x₁.toSet u_star x₂.toSet b) := by
    intro F hF_mem x₁ x₂ a b ha hb hx₁ hx₂ hord
    have hFC : F ⊆ C := by
      rcases hF_mem with rfl | rfl
      · exact hIb_C
      · exact hIa_C
    obtain ⟨hcF, hpre_diff, hu_star_cl⟩ := h_comp_conn F hF_mem
    rcases hord with ⟨g, a₁, b₁, τ₁, a₂, b₂, τ₂, hab₁, hbτ₁, hτa₂, hab₂, hbτ₂, hτ₂_le,
      hτ₁_eq, hτ₂_eq, hX₁_ne, hX₁_sub, hX₂_ne, hX₂_sub⟩
    set t₀ := τ₂ - 2 * Real.pi with ht₀_def
    have ht₀_eq_b : cuffPoint g t₀ = b := by
      have : τ₂ = t₀ + 2 * Real.pi := by dsimp [t₀]; ring
      rw [← hτ₂_eq, this, cuffPoint_add_two_pi]
    have ht₀_mem : cuffPoint g t₀ ∈ Γ.V ∩ C := by rw [ht₀_eq_b]; exact ⟨hb.2, hb.1⟩
    have hτ₁_mem : cuffPoint g τ₁ ∈ Γ.V ∩ C := by rw [hτ₁_eq]; exact ⟨ha.2, ha.1⟩
    have hτ₂_mem : cuffPoint g τ₂ ∈ Γ.V ∩ C := by rw [hτ₂_eq]; exact ⟨hb.2, hb.1⟩
    have hx₁_C : (∃ w ∈ C, x₁ = .vertex w) ∨ (∃ s ∈ drawingSpaces Γ, s ⊆ C ∧ x₁ = .space s) := by
      rcases hx₁ with ⟨w, hwF, rfl⟩ | ⟨s, hs, hsF, rfl⟩
      · exact Or.inl ⟨w, hFC hwF, rfl⟩
      · exact Or.inr ⟨s, hs, hsF.trans hFC, rfl⟩
    have hx₂_C : (∃ w ∈ C, x₂ = .vertex w) ∨ (∃ s ∈ drawingSpaces Γ, s ⊆ C ∧ x₂ = .space s) := by
      rcases hx₂ with ⟨w, hwF, rfl⟩ | ⟨s, hs, hsF, rfl⟩
      · exact Or.inl ⟨w, hFC hwF, rfl⟩
      · exact Or.inr ⟨s, hs, hsF.trans hFC, rfl⟩
    have hX₁_in_t₀_τ₁ : closure x₁.toSet ∩ C ⊆ cuffPoint g '' Icc t₀ τ₁ :=
      hX₁_sub.trans (image_mono (fun t ht => ⟨by linarith [ht.1], ht.2.trans hbτ₁⟩))
    have hX₂_in_τ₁_τ₂ : closure x₂.toSet ∩ C ⊆ cuffPoint g '' Icc τ₁ τ₂ :=
      hX₂_sub.trans (image_mono (fun t ht => ⟨hτa₂.trans ht.1, ht.2.trans hbτ₂⟩))
    obtain ⟨α₁, β₁, ht₀_α₁, hαβ₁, hβ₁_τ₁, hcl₁_eq⟩ :=
      unit_closure_eq_Icc_in_interval hS hge2 hC g (by linarith) (by linarith)
        (by dsimp [t₀]; linarith) ht₀_mem ht₀_mem hτ₁_mem x₁ hx₁_C hX₁_in_t₀_τ₁
    obtain ⟨α₂, β₂, hτ₁_α₂, hαβ₂, hβ₂_τ₂, hcl₂_eq⟩ :=
      unit_closure_eq_Icc_in_interval hS hge2 hC g (by linarith) (by linarith)
        (by dsimp [t₀]; linarith) ht₀_mem hτ₁_mem hτ₂_mem x₂ hx₂_C hX₂_in_τ₁_τ₂
    have hcl₁_sub_F : cuffPoint g '' Icc α₁ β₁ ⊆ F := by
      rw [← hcl₁_eq]
      rcases hx₁ with ⟨w, hwF, rfl⟩ | ⟨s, _, hsF, rfl⟩
      · simp only [BoundaryUnit.toSet, closure_singleton]
        exact inter_subset_left.trans (singleton_subset_iff.mpr hwF)
      · exact inter_subset_left.trans (closure_minimal hsF hcF)
    have hcl₂_sub_F : cuffPoint g '' Icc α₂ β₂ ⊆ F := by
      rw [← hcl₂_eq]
      rcases hx₂ with ⟨w, hwF, rfl⟩ | ⟨s, _, hsF, rfl⟩
      · simp only [BoundaryUnit.toSet, closure_singleton]
        exact inter_subset_left.trans (singleton_subset_iff.mpr hwF)
      · exact inter_subset_left.trans (closure_minimal hsF hcF)
    -- The two gap arcs G₁ = Icc β₁ α₂ and G₂ = Icc β₂ (α₁ + 2 * Real.pi)
    let G₁ : Set S := cuffPoint g '' Icc β₁ α₂
    let G₂ : Set S := cuffPoint g '' Icc β₂ (α₁ + 2 * Real.pi)
    have hcG₁ : IsClosed G₁ := (isCompact_Icc.image (cuffPoint_continuous g)).isClosed
    have hcG₂ : IsClosed G₂ := (isCompact_Icc.image (cuffPoint_continuous g)).isClosed
    have hdiff_cov : C \ F ⊆ G₁ ∪ G₂ := by
      rintro z ⟨hzC, hz_notF⟩
      obtain ⟨t, ht, rfl⟩ := exists_cuffPoint_mem_Ico g α₁ hzC
      have ht_not_1 : t ∉ Icc α₁ β₁ := fun h => hz_notF (hcl₁_sub_F ⟨t, h, rfl⟩)
      have ht_not_2 : t ∉ Icc α₂ β₂ := fun h => hz_notF (hcl₂_sub_F ⟨t, h, rfl⟩)
      by_cases ht_le_α₂ : t ≤ α₂
      · left
        refine ⟨t, ⟨?_, ht_le_α₂⟩, rfl⟩
        by_contra hlt
        push Not at hlt
        exact ht_not_1 ⟨ht.1, hlt.le⟩
      · right
        push Not at ht_le_α₂
        refine ⟨t, ⟨?_, ht.2.le⟩, rfl⟩
        by_contra hlt
        push Not at hlt
        exact ht_not_2 ⟨ht_le_α₂.le, hlt.le⟩
    have hG₁_G₂_inter_sub_F : G₁ ∩ G₂ ⊆ F := by
      rintro z ⟨⟨t₁, ⟨ht₁_1, ht₁_2⟩, rfl⟩, ⟨t₂, ⟨ht₂_1, ht₂_2⟩, h_eq⟩⟩
      rcases eq_or_lt_of_le ht₂_2 with rfl | ht₂_lt
      · rw [cuffPoint_add_two_pi] at h_eq
        exact hcl₁_sub_F ⟨α₁, ⟨le_rfl, hαβ₁⟩, h_eq⟩
      · have h_eq_t : t₁ = t₂ :=
          cuffPoint_injOn_Ico g α₁ ⟨hαβ₁.trans ht₁_1, by linarith⟩ ⟨by linarith, ht₂_lt⟩ h_eq.symm
        subst h_eq_t
        rcases eq_or_lt_of_le ht₁_2 with rfl | hlt
        · exact hcl₂_sub_F ⟨t₁, ⟨le_rfl, hαβ₂⟩, rfl⟩
        · linarith
    have hdiff_cases : C \ F ⊆ G₁ ∨ C \ F ⊆ G₂ := by
      by_contra hnot
      push Not at hnot
      obtain ⟨z₁, hz₁_diff, hz₁_notG₁⟩ := not_subset.mp hnot.1
      obtain ⟨z₂, hz₂_diff, hz₂_notG₂⟩ := not_subset.mp hnot.2
      have hz₁_G₂ : z₁ ∈ G₂ := (hdiff_cov hz₁_diff).resolve_left hz₁_notG₁
      have hz₂_G₁ : z₂ ∈ G₁ := (hdiff_cov hz₂_diff).resolve_right hz₂_notG₂
      obtain ⟨w, hw_diff, hwG₁, hwG₂⟩ := isPreconnected_closed_iff.mp hpre_diff G₁ G₂ hcG₁ hcG₂
        hdiff_cov ⟨z₂, hz₂_diff, hz₂_G₁⟩ ⟨z₁, hz₁_diff, hz₁_G₂⟩
      exact hw_diff.2 (hG₁_G₂_inter_sub_F ⟨hwG₁, hwG₂⟩)
    rcases hdiff_cases with h_in_G₁ | h_in_G₂
    · right
      have hb_in_F : b ∈ F := by
        by_contra hb_notF
        have hb_diff : b ∈ C \ F := ⟨hb.1, hb_notF⟩
        have hb_G₁ : b ∈ G₁ := h_in_G₁ hb_diff
        rcases hb_G₁ with ⟨tb, ⟨htb1, htb2⟩, htb_eq⟩
        have hb_G₂ : b ∈ G₂ := ⟨τ₂, ⟨hβ₂_τ₂, by dsimp [t₀] at ht₀_α₁; linarith⟩, hτ₂_eq⟩
        exact hb_notF (hG₁_G₂_inter_sub_F ⟨⟨tb, ⟨htb1, htb2⟩, htb_eq⟩, hb_G₂⟩)
      have hu_star_G₁ : u_star ∈ G₁ := closure_minimal h_in_G₁ hcG₁ hu_star_cl
      rcases hu_star_G₁ with ⟨tu, ⟨htu1, htu2⟩, htu_eq⟩
      refine ⟨hb_in_F, g, α₁, β₁, tu, α₂, β₂, τ₂,
        hαβ₁, htu1, htu2, hαβ₂, hβ₂_τ₂, by dsimp [t₀] at ht₀_α₁; linarith,
        htu_eq, hτ₂_eq, hX₁_ne, ?_, hX₂_ne, ?_⟩
      · rw [hcl₁_eq]
      · rw [hcl₂_eq]
    · left
      have ha_in_F : a ∈ F := by
        by_contra ha_notF
        have ha_diff : a ∈ C \ F := ⟨ha.1, ha_notF⟩
        have ha_G₂ : a ∈ G₂ := h_in_G₂ ha_diff
        have ha_G₁ : a ∈ G₁ := ⟨τ₁, ⟨hβ₁_τ₁, hτ₁_α₂⟩, hτ₁_eq⟩
        exact ha_notF (hG₁_G₂_inter_sub_F ⟨ha_G₁, ha_G₂⟩)
      have hu_star_G₂ : u_star ∈ G₂ := closure_minimal h_in_G₂ hcG₂ hu_star_cl
      rcases hu_star_G₂ with ⟨tu, ⟨htu1, htu2⟩, htu_eq⟩
      refine ⟨ha_in_F, g, α₁, β₁, τ₁, α₂, β₂, tu,
        hαβ₁, hβ₁_τ₁, hτ₁_α₂, hαβ₂, htu1, htu2,
        hτ₁_eq, htu_eq, hX₁_ne, ?_, hX₂_ne, ?_⟩
      · rw [hcl₁_eq]
      · rw [hcl₂_eq]
  -- Space dichotomy helper for s ≠ s_star
  have h_space_dichot : ∀ s ∈ drawingSpaces Γ, s ⊆ C → s ≠ vSpaceArc Γ.V Γ.finite_V f hk i₀ →
      (s ⊆ I_b ∧ closure s ⊆ I_b ∧ Disjoint s I_a) ∨
      (s ⊆ I_a ∧ closure s ⊆ I_a ∧ Disjoint s I_b) := by
    intro s hs hsC hne
    obtain ⟨j, rfl⟩ := exists_index_of_mem_drawingSpaces_subset_cuff hS hge2 hs hC hsC f
    have hij : j ≠ i₀ := fun h => hne (h ▸ rfl)
    have hdisj_i₀ : Disjoint (vSpaceArc Γ.V Γ.finite_V f hk j) (vSpaceArc Γ.V Γ.finite_V f hk i₀) :=
      disjoint_vSpaceArc Γ.V Γ.finite_V f hk hij
    have hs_sub_union : vSpaceArc Γ.V Γ.finite_V f hk j ⊆ I_b ∪ I_a := by
      rw [hIb_Ia_union]
      exact subset_sdiff.mpr ⟨hsC, hdisj_i₀⟩
    rcases space_subset_or_disjoint_of_supportHasEnds hS hs hIb_supp with ⟨h1, h2⟩ | hdisj_Ib
    · refine Or.inl ⟨h1, h2, ?_⟩
      rw [disjoint_iff_inter_eq_empty]
      ext z
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hzs hzIa
      have hz_inter : z ∈ I_b ∩ I_a := ⟨h1 hzs, hzIa⟩
      rw [hIb_Ia_inter, mem_singleton_iff] at hz_inter
      subst hz_inter
      exact (subset_bd_diff_of_mem_drawingSpaces hs hzs).2 hu_star.1
    · have hs_sub_Ia : vSpaceArc Γ.V Γ.finite_V f hk j ⊆ I_a :=
        fun z hzs => (hs_sub_union hzs).resolve_left (Set.disjoint_left.mp hdisj_Ib hzs)
      exact Or.inr ⟨hs_sub_Ia, closure_minimal hs_sub_Ia (isClosed_of_supportHasEnds hS hIa_supp),
        hdisj_Ib⟩
  -- Match {u₁, u₂} with {vNode i₀, vNode (nextFin hk i₀)}
  have hu₁_mem : u₁ ∈ ({vNode Γ.V Γ.finite_V f i₀, vNode Γ.V Γ.finite_V f (nextFin hk i₀)} : Set S) := by
    rw [← hpair]; exact Or.inl rfl
  have hu₂_mem : u₂ ∈ ({vNode Γ.V Γ.finite_V f i₀, vNode Γ.V Γ.finite_V f (nextFin hk i₀)} : Set S) := by
    rw [← hpair]; exact Or.inr rfl
  have hIb_disj : Disjoint I_b (vSpaceArc Γ.V Γ.finite_V f hk i₀) := by
    rw [disjoint_iff_inter_eq_empty]
    ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hzIb hzs
    have hz_diff : z ∈ C \ vSpaceArc Γ.V Γ.finite_V f hk i₀ := by
      rw [← hIb_Ia_union]; exact Or.inl hzIb
    exact hz_diff.2 hzs
  have hIa_disj : Disjoint I_a (vSpaceArc Γ.V Γ.finite_V f hk i₀) := by
    rw [disjoint_iff_inter_eq_empty]
    ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hzIa hzs
    have hz_diff : z ∈ C \ vSpaceArc Γ.V Γ.finite_V f hk i₀ := by
      rw [← hIb_Ia_union]; exact Or.inr hzIa
    exact hz_diff.2 hzs
  rcases hu₁_mem with rfl | rfl <;> rcases hu₂_mem with rfl | rfl
  · exact (hs_star.2.2.2.1 rfl).elim
  · refine ⟨I_a, I_b, hIa_C, hIb_C, hIa_supp, hIb_supp,
      hn_i₀_in_Ia, hn_i₀_not_Ib, hn_next_in_Ib, hn_next_not_Ia,
      by rw [union_comm, hIb_Ia_union], by rw [inter_comm, hIb_Ia_inter],
      hIa_disj, hIb_disj,
      fun s hs hsC hne => (h_space_dichot s hs hsC hne).symm,
      fun F hF => h_order_prop F (by rwa [pair_comm] at hF)⟩
  · refine ⟨I_b, I_a, hIb_C, hIa_C, hIb_supp, hIa_supp,
      hn_next_in_Ib, hn_next_not_Ia, hn_i₀_in_Ia, hn_i₀_not_Ib,
      hIb_Ia_union, hIb_Ia_inter, hIb_disj, hIa_disj,
      h_space_dichot, h_order_prop⟩
  · exact (hs_star.2.2.2.1 rfl).elim

end SupportsAndOrder

end GraphMinor.GM21
