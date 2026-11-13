module

public import GraphMinor.GM21.Section6Angles
public import GraphMinor.GM21.Section6Cuts
public import GraphMinor.GM21.Section6Separation
public import GraphMinor.GM21.Section6Jumps
public import GraphMinor.GM06.Defs
import GraphMinor.GM21.Section6Disc
import GraphMinor.GM10.TangleLemmas
import GraphMinor.GM06.DiscRegions

/-!
# Graph Minors XXI, proofs of (6.4)–(6.7): a disc read by angles

Let `Γ, F_1*, ..., F_r*, H_1, ..., H_r, μ` be a presentation of `G` in a disc `Σ` (Section 6,
page 24 of the preprint). The boundary `bd(Σ)` is a circle, and we parametrize it by angles
(`GM19.cuffPoint f`). A *window* (`Window`) is an interval `[w₀, w₁]` of angles of length less
than `2π` such that every support `F_j*` is the set of points with angles in an interval
`[a j, b j] ⊆ [w₀, w₁]`. Every vertex of `Γ` in `bd(Σ)` lies in a support, so it has a unique
angle in `[w₀, w₁]`, and each `Σ`-jump `J` has two ends with angles `jumpLo J < jumpHi J`
(`jumpAngles_spec`).

A window exists that starts at any chosen support (`exists_window`). This file proves the facts
about the angles of the jumps that the counting needs: two jumps with the same angles of ends are
equal (`jump_eq_of_angles`), and two jumps never cross (`not_cross_of_mem_jumpSet`), which is
where we use that `Σ` is a disc.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace DiscCut

open Set Topology Hypergraph GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM21.Supports

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-- The angles of the two ends of `J`, if `J` has two terminals at points of angles
`t₀ ≤ a < c ≤ t₁` that are vertices in `V`; otherwise `(0, 0)`. -/
noncomputable def jumpAngles {C : Set S} (f : Circle ≃ₜ C) (t₀ t₁ : ℝ) (V : Set S)
    (ιV : S → α) (J : Hypergraph α β) : ℝ × ℝ :=
  open Classical in
  if h : ∃ p : ℝ × ℝ, t₀ ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ t₁ ∧ GM19.cuffPoint f p.1 ∈ V ∧
      GM19.cuffPoint f p.2 ∈ V ∧
      terminals J = {ιV (GM19.cuffPoint f p.1), ιV (GM19.cuffPoint f p.2)} then
    h.choose
  else (0, 0)

/-- The angle of the first end of a jump. -/
noncomputable def jumpLo {C : Set S} (f : Circle ≃ₜ C) (t₀ t₁ : ℝ) (V : Set S) (ιV : S → α)
    (J : Hypergraph α β) : ℝ :=
  (jumpAngles f t₀ t₁ V ιV J).1

/-- The angle of the second end of a jump. -/
noncomputable def jumpHi {C : Set S} (f : Circle ≃ₜ C) (t₀ t₁ : ℝ) (V : Set S) (ιV : S → α)
    (J : Hypergraph α β) : ℝ :=
  (jumpAngles f t₀ t₁ V ιV J).2

/-- A *window* of angles for the supports: `w₀ ≤ a j ≤ b j ≤ w₁ < w₀ + 2π`, the points of angles
`a j` and `b j` are vertices of `Γ`, and `F_j*` is the set of points with angles in `[a j, b j]`. -/
structure Window {r : ℕ} (Γ : Drawing S) (F_star : Fin r → Set S) (f : Circle ≃ₜ bd S)
    (w₀ w₁ : ℝ) (a b : Fin r → ℝ) : Prop where
  lt_add : w₁ < w₀ + 2 * Real.pi
  le_a : ∀ j, w₀ ≤ a j
  a_le_b : ∀ j, a j ≤ b j
  b_le : ∀ j, b j ≤ w₁
  a_mem : ∀ j, GM19.cuffPoint f (a j) ∈ Γ.V
  b_mem : ∀ j, GM19.cuffPoint f (b j) ∈ Γ.V
  F_eq : ∀ j, F_star j = GM19.cuffPoint f '' Icc (a j) (b j)

/-- The points of angles in an interval of length less than `2π` are determined by their angles. -/
theorem angle_injOn {C : Set S} (f : Circle ≃ₜ C) {w₀ w₁ : ℝ} (hlt : w₁ < w₀ + 2 * Real.pi) :
    InjOn (GM19.cuffPoint f) (Icc w₀ w₁) :=
  fun _ hs _ ht h => GM17.cuffPoint_injOn_Ico f w₀ ⟨hs.1, by linarith [hs.2]⟩
    ⟨ht.1, by linarith [ht.2]⟩ h

section setup

variable {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
  (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
  {f : Circle ≃ₜ bd S} {w₀ w₁ : ℝ} {a b : Fin r → ℝ} (hW : Window Γ F_star f w₀ w₁ a b)

set_option hygiene false in
local notation "cp" => GM19.cuffPoint f

include hW

/-- The angles of `F_j*` lie in the window. -/
theorem Window.Icc_subset (j : Fin r) : Icc (a j) (b j) ⊆ Icc w₀ w₁ :=
  Icc_subset_Icc (hW.le_a j) (hW.b_le j)

/-- An angle of the window whose point lies in `F_j*` is an angle of `F_j*`. -/
theorem Window.mem_Icc_of_mem {j : Fin r} {t : ℝ} (ht : t ∈ Icc w₀ w₁)
    (htF : cp t ∈ F_star j) : t ∈ Icc (a j) (b j) := by
  rw [hW.F_eq j] at htF
  obtain ⟨t', ht', heq⟩ := htF
  rw [angle_injOn f hW.lt_add ht (hW.Icc_subset j ht') heq.symm]
  exact ht'

include h_pres

/-- Every vertex of `Γ` in `bd(Σ)` has an angle in some `[a j, b j]`. -/
theorem Window.exists_angle {u : S} (hu : u ∈ Γ.V ∩ bd S) :
    ∃ j, ∃ t ∈ Icc (a j) (b j), cp t = u := by
  have h := h_pres.bd_vertices_covered hu
  rw [mem_iUnion] at h
  obtain ⟨j, hj⟩ := h
  rw [hW.F_eq j] at hj
  exact ⟨j, hj⟩

/-- Every vertex of `Γ` in `bd(Σ)` has an angle in the window. -/
theorem Window.exists_angle' {u : S} (hu : u ∈ Γ.V ∩ bd S) :
    ∃ t ∈ Icc w₀ w₁, cp t = u := by
  obtain ⟨j, t, ht, rfl⟩ := hW.exists_angle h_pres hu
  exact ⟨t, hW.Icc_subset j ht, rfl⟩

/-- A vertex position of the window lies in some `[a j, b j]`. -/
theorem Window.exists_support {t : ℝ} (ht : t ∈ Icc w₀ w₁) (htV : cp t ∈ Γ.V) :
    ∃ j, t ∈ Icc (a j) (b j) := by
  obtain ⟨j, t', ht', heq⟩ := hW.exists_angle h_pres ⟨htV, GM17.cuffPoint_mem f t⟩
  refine ⟨j, ?_⟩
  rw [angle_injOn f hW.lt_add ht (hW.Icc_subset j ht') heq.symm]
  exact ht'

/-- The defining property of the angles of the ends of a `Σ`-jump. -/
theorem Window.jumpAngles_spec {J : Hypergraph α β}
    (hJ : J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))) :
    w₀ ≤ jumpLo f w₀ w₁ Γ.V ιV J ∧ jumpLo f w₀ w₁ Γ.V ιV J < jumpHi f w₀ w₁ Γ.V ιV J ∧
      jumpHi f w₀ w₁ Γ.V ιV J ≤ w₁ ∧ cp (jumpLo f w₀ w₁ Γ.V ιV J) ∈ Γ.V ∧
      cp (jumpHi f w₀ w₁ Γ.V ιV J) ∈ Γ.V ∧
      terminals J = {ιV (cp (jumpLo f w₀ w₁ Γ.V ιV J)), ιV (cp (jumpHi f w₀ w₁ Γ.V ιV J))} := by
  have hex : ∃ p : ℝ × ℝ, w₀ ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ w₁ ∧ cp p.1 ∈ Γ.V ∧
      cp p.2 ∈ Γ.V ∧ terminals J = {ιV (cp p.1), ιV (cp p.2)} := by
    obtain ⟨a', ⟨u, hu, rfl⟩, b', ⟨w, hw, rfl⟩, hne, hterm, -, -⟩ :=
      terminals_eq_of_mem_jumpSet hJ
    obtain ⟨s, hs, rfl⟩ := hW.exists_angle' h_pres hu
    obtain ⟨t, ht, rfl⟩ := hW.exists_angle' h_pres hw
    rcases lt_trichotomy s t with hst | rfl | hts
    · exact ⟨(s, t), hs.1, hst, ht.2, hu.1, hw.1, hterm⟩
    · exact absurd rfl hne
    · refine ⟨(t, s), ht.1, hts, hs.2, hw.1, hu.1, ?_⟩
      rw [hterm, pair_comm]
  unfold jumpLo jumpHi jumpAngles
  rw [dite_eq_left hex]
  exact hex.choose_spec

/-- The angle of the first end of a jump lies in the window. -/
theorem Window.jumpLo_mem {J : Hypergraph α β} (hJ : J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))) :
    jumpLo f w₀ w₁ Γ.V ιV J ∈ Icc w₀ w₁ :=
  ⟨(hW.jumpAngles_spec h_pres hJ).1,
    (hW.jumpAngles_spec h_pres hJ).2.1.le.trans (hW.jumpAngles_spec h_pres hJ).2.2.1⟩

/-- The angle of the second end of a jump lies in the window. -/
theorem Window.jumpHi_mem {J : Hypergraph α β} (hJ : J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))) :
    jumpHi f w₀ w₁ Γ.V ιV J ∈ Icc w₀ w₁ :=
  ⟨(hW.jumpAngles_spec h_pres hJ).1.trans (hW.jumpAngles_spec h_pres hJ).2.1.le,
    (hW.jumpAngles_spec h_pres hJ).2.2.1⟩

/-- A vertex of `Γ` in `bd(Σ)` on a jump is one of its two ends. -/
theorem Window.eq_end_of_mem_jump {J : Hypergraph α β}
    (hJ : J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))) {u : S} (hu : u ∈ Γ.V ∩ bd S)
    (huJ : ιV u ∈ J.vertexSet) :
    u = cp (jumpLo f w₀ w₁ Γ.V ιV J) ∨ u = cp (jumpHi f w₀ w₁ Γ.V ιV J) := by
  obtain ⟨-, -, -, hloV, hhiV, hterm⟩ := hW.jumpAngles_spec h_pres hJ
  have ht := mem_terminals_of_mem_jumpSet hJ huJ (mem_image_of_mem ιV hu)
  rw [hterm] at ht
  rcases ht with h | h
  · exact Or.inl (h_pres.ιV_injOn hu.1 hloV h)
  · exact Or.inr (h_pres.ιV_injOn hu.1 hhiV h)

/-- A vertex of `Γ` in `bd(Σ)` on a jump, given by its angle, is at one of the two angles of the
ends of the jump. -/
theorem Window.eq_angle_of_mem_jump {J : Hypergraph α β}
    (hJ : J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))) {t : ℝ} (ht : t ∈ Icc w₀ w₁) (htV : cp t ∈ Γ.V)
    (htJ : ιV (cp t) ∈ J.vertexSet) :
    t = jumpLo f w₀ w₁ Γ.V ιV J ∨ t = jumpHi f w₀ w₁ Γ.V ιV J := by
  rcases hW.eq_end_of_mem_jump h_pres hJ ⟨htV, GM17.cuffPoint_mem f t⟩ htJ with h | h
  · exact Or.inl (angle_injOn f hW.lt_add ht (hW.jumpLo_mem h_pres hJ) h)
  · exact Or.inr (angle_injOn f hW.lt_add ht (hW.jumpHi_mem h_pres hJ) h)

/-- Two jumps with the same angles of ends are equal. -/
theorem Window.jump_eq_of_angles (hK : IsLinkage G Γ_sub)
    (hdeg : ∀ y ∈ Γ_sub.vertexSet, y ∉ ιV '' (Γ.V ∩ bd S) → (incidentEdges Γ_sub y).ncard = 2)
    {J J' : Hypergraph α β} (hJ : J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S)))
    (hJ' : J' ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S)))
    (hlo : jumpLo f w₀ w₁ Γ.V ιV J = jumpLo f w₀ w₁ Γ.V ιV J')
    (hhi : jumpHi f w₀ w₁ Γ.V ιV J = jumpHi f w₀ w₁ Γ.V ιV J') : J = J' := by
  apply jump_eq_of_terminals_eq hK hdeg hJ hJ'
  rw [(hW.jumpAngles_spec h_pres hJ).2.2.2.2.2,
    (hW.jumpAngles_spec h_pres hJ').2.2.2.2.2, hlo, hhi]

/-- **Jumps in a disc do not cross**: there are no two jumps `J, J'` whose ends have angles
`lo J < lo J' < hi J < hi J'`. -/
theorem Window.not_cross_of_mem_jumpSet (hS : GM06.IsClosedDiscSpace S) (hK : IsLinkage G Γ_sub)
    (hdeg : ∀ y ∈ Γ_sub.vertexSet, y ∉ ιV '' (Γ.V ∩ bd S) → (incidentEdges Γ_sub y).ncard = 2)
    {J J' : Hypergraph α β} (hJ : J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S)))
    (hJ' : J' ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))) :
    ¬ (jumpLo f w₀ w₁ Γ.V ιV J < jumpLo f w₀ w₁ Γ.V ιV J' ∧
      jumpLo f w₀ w₁ Γ.V ιV J' < jumpHi f w₀ w₁ Γ.V ιV J ∧
      jumpHi f w₀ w₁ Γ.V ιV J < jumpHi f w₀ w₁ Γ.V ιV J') := by
  have : T2Space S := h_pres.is_surface.2.1
  rintro ⟨h1, h2, h3⟩
  obtain ⟨hlo₀, -, -, hloV, hhiV, hterm⟩ := hW.jumpAngles_spec h_pres hJ
  obtain ⟨-, -, hhi₁', hloV', hhiV', hterm'⟩ := hW.jumpAngles_spec h_pres hJ'
  have hcross := pairsCrossOn_of_angles f h1 h2 h3 (by linarith [hW.lt_add])
  have heq := jumps_not_cross hS h_pres.drawing_iso hK hdeg hJ hJ' hloV hloV' hhiV hhiV'
    (by rw [hterm]; exact Or.inl rfl) (by rw [hterm]; exact Or.inr rfl)
    (by rw [hterm']; exact Or.inl rfl) (by rw [hterm']; exact Or.inr rfl) hcross
  subst heq
  exact lt_irrefl _ h1

end setup

/-- In a disc, `bd(Σ)` is a cuff. -/
theorem bd_mem_cuffs (hS : GM06.IsClosedDiscSpace S) : bd S ∈ cuffs S := by
  obtain ⟨g⟩ := hS.isOArc_bd
  have hconn : IsConnected (bd S) := by
    have : bd S = range (fun z => (g z : S)) := by
      ext x
      constructor
      · intro hx
        exact ⟨g.symm ⟨x, hx⟩, by simp⟩
      · rintro ⟨z, rfl⟩
        exact (g z).2
    rw [this]
    exact isConnected_range (continuous_subtype_val.comp g.continuous)
  obtain ⟨x, hx⟩ := hconn.nonempty
  exact ⟨x, hx, hconn.isPreconnected.connectedComponentIn hx⟩

/-- A set of points with angles in `[s, e]` that misses the point of angle `w₀`, is
the set of points with angles in `[s', e']` for some `w₀ < s' ≤ e' < w₀ + 2π`. -/
theorem exists_shift_Icc {C : Set S} (f : Circle ≃ₜ C) {s e w₀ : ℝ} (hse : s ≤ e)
    (hw : GM19.cuffPoint f w₀ ∉ GM19.cuffPoint f '' Icc s e) :
    ∃ s' e', w₀ < s' ∧ s' ≤ e' ∧ e' < w₀ + 2 * Real.pi ∧ GM19.cuffPoint f s' = GM19.cuffPoint f s ∧
      GM19.cuffPoint f e' = GM19.cuffPoint f e ∧
      GM19.cuffPoint f '' Icc s e = GM19.cuffPoint f '' Icc s' e' := by
  obtain ⟨t, ht, hts⟩ := GM17.exists_cuffPoint_mem_Ico f w₀ (GM17.cuffPoint_mem f s)
  obtain ⟨m, hm⟩ := (GM17.cuffPoint_eq_iff f).1 hts
  have himg : GM19.cuffPoint f '' Icc s e = GM19.cuffPoint f '' Icc t (e + m * (2 * Real.pi)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y + m * (2 * Real.pi), ⟨by linarith [hy.1], by linarith [hy.2]⟩, ?_⟩
      exact (GM17.cuffPoint_eq_iff f).2 ⟨m, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y - m * (2 * Real.pi), ⟨by linarith [hy.1], by linarith [hy.2]⟩, ?_⟩
      exact (GM17.cuffPoint_eq_iff f).2 ⟨-m, by push_cast; ring⟩
  have hpi := Real.pi_pos
  have ht0 : w₀ < t := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · exfalso
      apply hw
      exact ⟨s, ⟨le_rfl, hse⟩, by rw [← hts, h]⟩
    · exact h
  have he' : e + m * (2 * Real.pi) < w₀ + 2 * Real.pi := by
    by_contra hcon
    push Not at hcon
    apply hw
    rw [himg]
    refine ⟨w₀ + 2 * Real.pi, ⟨ht.2.le, hcon⟩, GM17.cuffPoint_add_two_pi f w₀⟩
  refine ⟨t, e + m * (2 * Real.pi), ht0, by linarith, he', hts, ?_, himg⟩
  exact (GM17.cuffPoint_eq_iff f).2 ⟨m, rfl⟩

/-- **A window exists**, starting at any chosen support `F_{j₀}*`. -/
theorem exists_window {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (hD : GM06.IsClosedDiscSpace S)
    (j₀ : Fin r) :
    ∃ (f : Circle ≃ₜ bd S) (w₀ w₁ : ℝ) (a b : Fin r → ℝ), Window Γ F_star f w₀ w₁ a b ∧
      a j₀ = w₀ := by
  classical
  have hS := h_pres.is_surface
  have hC := bd_mem_cuffs hD
  obtain ⟨g⟩ := hD.isOArc_bd
  have hpi := Real.pi_pos
  -- Each support is an interval of angles.
  have hsupp : ∀ j, ∃ s e : ℝ, s ≤ e ∧ e < s + 2 * Real.pi ∧ GM19.cuffPoint g s ∈ Γ.V ∧
      GM19.cuffPoint g e ∈ Γ.V ∧ F_star j = GM19.cuffPoint g '' Icc s e := by
    intro j
    obtain ⟨x, y, hxy⟩ := h_pres.supports_isSupport j
    have hends := ends_mem_of_supportHasEnds hxy
    obtain ⟨s, -, e, ⟨hle, hlt⟩, h_ab, hF, -⟩ :=
      support_eq_cuffPoint_Icc hS hC g hxy hends.2.2.2.2
    refine ⟨s, e, hle, hlt, ?_, ?_, hF⟩
    · rcases h_ab with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
      exacts [hends.2.2.1.1, hends.2.2.2.1.1]
    · rcases h_ab with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
      exacts [hends.2.2.2.1.1, hends.2.2.1.1]
  choose s e hse hes hsV heV hF using hsupp
  set w₀ := s j₀ with hw₀
  -- Shift every other support into `(w₀, w₀ + 2π)`.
  have hshift : ∀ j, ∃ s' e' : ℝ, w₀ ≤ s' ∧ s' ≤ e' ∧ e' < w₀ + 2 * Real.pi ∧
      GM19.cuffPoint g s' ∈ Γ.V ∧ GM19.cuffPoint g e' ∈ Γ.V ∧
      F_star j = GM19.cuffPoint g '' Icc s' e' ∧ (j = j₀ → s' = w₀) := by
    intro j
    by_cases hj : j = j₀
    · subst hj
      exact ⟨s j, e j, le_rfl, hse j, hes j, hsV j, heV j, hF j, fun _ => rfl⟩
    · have hw : GM19.cuffPoint g w₀ ∉ GM19.cuffPoint g '' Icc (s j) (e j) := by
        rw [← hF j]
        intro hmem
        have h0 : GM19.cuffPoint g w₀ ∈ F_star j₀ := by
          rw [hF j₀]
          exact ⟨s j₀, ⟨le_rfl, hse j₀⟩, rfl⟩
        exact Set.disjoint_left.mp (h_pres.supports_disjoint hj) hmem h0
      obtain ⟨s', e', h1, h2, h3, h4, h5, h6⟩ := exists_shift_Icc g (hse j) hw
      refine ⟨s', e', h1.le, h2, h3, h4 ▸ hsV j, h5 ▸ heV j, (hF j).trans h6, fun h => ?_⟩
      exact absurd h hj
  choose a b hwa hab hbw haV hbV hFab ha₀ using hshift
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨j₀, Finset.mem_univ _⟩
  set w₁ := Finset.univ.sup' hne b with hw₁
  have hbw₁ : ∀ j, b j ≤ w₁ := fun j => Finset.le_sup' b (Finset.mem_univ j)
  have hw₁lt : w₁ < w₀ + 2 * Real.pi := by
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' hne b
    rw [hw₁, hj]
    exact hbw j
  exact ⟨g, w₀, w₁, a, b, ⟨hw₁lt, hwa, hab, hbw₁, haV, hbV, hFab⟩, ha₀ j₀ rfl⟩

end DiscCut
end GM21
end GraphMinor
