module

public import GraphMinor.GM21.Section6DiscSetup
public import GraphMinor.GM21.Section6LastCover
import GraphMinor.GM21.Section6DiscSides
import GraphMinor.GM21.Section6TwoEdges
import GraphMinor.GM21.Section6SideJumps
import GraphMinor.GM21.LinkageLemmas
import GraphMinor.GM06.DiscRegions
import GraphMinor.GM11.Regions
import GraphMinor.GM17.CuffOrder
import GraphMinor.GM10.TangleLemmas
import GraphMinor.Surface.DiscArcs
import GraphMinor.Surface.ArcTools
import GraphMinor.Surface.SurfaceGraph

/-!
# Graph Minors XXI, proof of (6.4): the two sides of a jump

The last step of the proof of (6.4) (page 25 of the preprint) looks at the regions of `Γ` in
the disc `Σ`: "Let us say that two distinct regions $r_1, r_2$ of $\Gamma$ in $\Sigma$ *touch* if
there is an edge $e$ of $\Gamma$ with $e \subseteq \bar{r}_1 \cap \bar{r}_2$. It follows that if
$r_1, r_2$ touch then $\bar{r}_1 \cap \bar{r}_2 = U(J)$ for some $\Sigma$-jump $J$". This file
proves the facts about one jump that this needs.

A jump `J` is drawn as a line `U(J)` across the disc (`LastStep.jumpLine`), with its ends at the
angles `lo J < hi J` of `bd(Σ)`. The line cuts `Σ` into two closed discs (`exists_lineSplit`, from
`disc_iArc`): the *inner side*, which meets `bd(Σ)` in the angles `[lo J, hi J]`, and the *outer
side*, which meets it in the angles `[hi J, lo J + 2π]`. We keep only what we use of the two
discs (`Halves`, `LineSplit`): they are closed, they cover `Σ`, they meet in `U(J)`, and every
point of `U(J)` is a limit of points of each side off `U(J)`.

* A connected set that misses `U(J)` lies on one side (`Halves.subset_or_subset`); in particular
  so does each region of `Γ`.
* Each edge of `J` lies in the closure of a region on each side (`Halves.exists_region_right`),
  and of only one region on each side (`Halves.region_eq_right`), since an edge is in the closure
  of at most two regions (`GM06.disc_region_incident_two`).
* A region whose closure holds one edge of `J` holds all of `U(J)` in its closure
  (`jumpLine_subset_closure`). We walk along `J`: each inner vertex of `J` has exactly two edges,
  and a region next to one of them is next to the other (`DiscLine.subset_closure_of_two_edges`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace RegionTree

open Set Topology Hypergraph GraphMinor.Surface GraphMinor.GM21.DiscCut

universe u v w

section halves

variable {S : Type w} [TopologicalSpace S]

/-- Two closed sets `P, Q` that cover the space and meet in `U`, such that every point of `U` is a
limit of points of `P \ U` and of points of `Q \ U`. These are the two sides of a line `U` across
a disc. -/
structure Halves (U P Q : Set S) : Prop where
  isClosed_left : IsClosed P
  isClosed_right : IsClosed Q
  union_eq : P ∪ Q = univ
  inter_eq : P ∩ Q = U
  subset_closure_left : U ⊆ closure (P \ U)
  subset_closure_right : U ⊆ closure (Q \ U)

namespace Halves

variable {U P Q : Set S} (h : Halves U P Q)
include h

theorem symm : Halves U Q P :=
  ⟨h.isClosed_right, h.isClosed_left, by rw [Set.union_comm]; exact h.union_eq,
    by rw [Set.inter_comm]; exact h.inter_eq, h.subset_closure_right, h.subset_closure_left⟩

theorem subset_right : U ⊆ Q := fun z hz => (h.inter_eq ▸ hz : z ∈ P ∩ Q).2

theorem subset_left : U ⊆ P := fun z hz => (h.inter_eq ▸ hz : z ∈ P ∩ Q).1

/-- The points off `Q` are the points of `P` off `U`. -/
theorem compl_right_eq : Qᶜ = P \ U := by
  ext z
  constructor
  · intro hz
    have hzP : z ∈ P := by
      have : z ∈ P ∪ Q := h.union_eq ▸ mem_univ z
      exact this.resolve_right hz
    exact ⟨hzP, fun hzU => hz (h.subset_right hzU)⟩
  · rintro ⟨hzP, hzU⟩ hzQ
    exact hzU (h.inter_eq ▸ ⟨hzP, hzQ⟩)

/-- No point is off both `P` and `Q`. -/
theorem not_mem_both {z : S} (hP : z ∉ P) (hQ : z ∉ Q) : False := by
  have : z ∈ P ∪ Q := h.union_eq ▸ mem_univ z
  exact this.elim hP hQ

/-- Every point of `U` is a limit of points off `Q`. -/
theorem subset_closure_compl_right : U ⊆ closure Qᶜ := by
  rw [h.compl_right_eq]
  exact h.subset_closure_left

/-- **A connected set off the line lies on one side.** -/
theorem subset_or_subset {A : Set S} (hA : IsPreconnected A) (hAU : Disjoint A U) :
    A ⊆ Qᶜ ∨ A ⊆ Pᶜ := by
  refine hA.subset_or_subset h.isClosed_right.isOpen_compl h.isClosed_left.isOpen_compl
    (disjoint_left.mpr fun z hzQ hzP => h.not_mem_both hzP hzQ) ?_
  intro z hz
  by_contra hcon
  simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
  exact disjoint_left.mp hAU hz (h.inter_eq ▸ ⟨hcon.2, hcon.1⟩)

variable {Γ : Drawing S}

/-- A region of `Γ`, where `U ⊆ U(Γ)`, lies on one side. -/
theorem region_subset_or (hUΓ : U ⊆ Γ.U) {ρ : Set S} (hρ : ρ ∈ Γ.R) : ρ ⊆ Qᶜ ∨ ρ ⊆ Pᶜ :=
  h.subset_or_subset (GM11.region_isPreconnected hρ)
    (disjoint_left.mpr fun _ hz hzU => GM11.region_subset hρ hz (hUΓ hzU))

/-- A region with a point off `Q` lies off `Q`. -/
theorem region_subset_right_of_mem (hUΓ : U ⊆ Γ.U) {ρ : Set S} (hρ : ρ ∈ Γ.R) {z : S}
    (hzρ : z ∈ ρ) (hzQ : z ∉ Q) : ρ ⊆ Qᶜ :=
  (h.region_subset_or hUΓ hρ).resolve_right fun hP => h.not_mem_both (hP hzρ) hzQ

/-- A region whose closure has a point off `Q` lies off `Q`. -/
theorem region_subset_right_of_closure (hUΓ : U ⊆ Γ.U) {ρ : Set S} (hρ : ρ ∈ Γ.R) {z : S}
    (hzρ : z ∈ closure ρ) (hzQ : z ∉ Q) : ρ ⊆ Qᶜ := by
  obtain ⟨y, hyQ, hyρ⟩ := mem_closure_iff.mp hzρ _ h.isClosed_right.isOpen_compl hzQ
  exact h.region_subset_right_of_mem hUΓ hρ hyρ hyQ

/-- No region lies off both sides. -/
theorem region_not_subset_both {ρ : Set S} (hρ : ρ ∈ Γ.R) (hQ : ρ ⊆ Qᶜ) (hP : ρ ⊆ Pᶜ) : False := by
  obtain ⟨z, hz⟩ := GM11.region_nonempty hρ
  exact h.not_mem_both (hP hz) (hQ hz)

/-- **A region on each side of an edge of the line.** In a disc, an edge `e ⊆ U` of a proper
drawing `Γ` with `U ⊆ U(Γ)` lies in the closure of a region off `Q`. -/
theorem exists_region_right (hD : GM06.IsClosedDiscSpace S) (hprop : Γ.IsProper) (hUΓ : U ⊆ Γ.U)
    {e : Set S} (he : e ∈ Γ.E) (heU : e ⊆ U) : ∃ ρ ∈ Γ.R, ρ ⊆ Qᶜ ∧ e ⊆ closure ρ := by
  obtain ⟨p, hp⟩ := he.1
  obtain ⟨W, A₁, A₂, hW, hpW, hWU, hsub, c₁, c₂, d₁, d₂, cl₁, cl₂⟩ :=
    GM06.disc_exists_edge_sides hD Γ hprop he hp
  obtain ⟨x, hxW, hxQ⟩ := mem_closure_iff.mp (h.subset_closure_compl_right (heU hp)) W hW hpW
  have hxU : x ∉ Γ.U := fun hxU => hxQ (h.subset_right (heU (hWU ⟨hxW, hxU⟩)))
  obtain ⟨ρ, hρ, hxρ⟩ := GM11.exists_region_of_notMem hxU
  have hpρ : p ∈ closure ρ := by
    rcases hsub ⟨hxW, hxU⟩ with hx | hx
    · exact closure_mono (GM11.subset_region hρ c₁ d₁ hx hxρ) (cl₁ ⟨hp, hpW⟩)
    · exact closure_mono (GM11.subset_region hρ c₂ d₂ hx hxρ) (cl₂ ⟨hp, hpW⟩)
  exact ⟨ρ, hρ, h.region_subset_right_of_mem hUΓ hρ hxρ hxQ,
    GM06.disc_edge_subset_closure_of_incident hD hprop he hρ ⟨p, hp, hpρ⟩⟩

/-- **Only one region on each side of an edge of the line.** -/
theorem region_eq_right (hD : GM06.IsClosedDiscSpace S) (hprop : Γ.IsProper) (hUΓ : U ⊆ Γ.U)
    {e : Set S} (he : e ∈ Γ.E) (heU : e ⊆ U) {ρ ρ' : Set S} (hρ : ρ ∈ Γ.R) (hρ' : ρ' ∈ Γ.R)
    (hρQ : ρ ⊆ Qᶜ) (hρ'Q : ρ' ⊆ Qᶜ) (heρ : e ⊆ closure ρ) (heρ' : e ⊆ closure ρ') : ρ = ρ' := by
  obtain ⟨σ, hσ, hσP, heσ⟩ := h.symm.exists_region_right hD hprop hUΓ he heU
  rcases GM06.disc_region_incident_two hD hprop he hρ hρ' hσ heρ heρ' heσ with h1 | h1 | h1
  · exact h1
  · exact (h.region_not_subset_both hρ hρQ (h1 ▸ hσP)).elim
  · exact (h.region_not_subset_both hρ' hρ'Q (h1 ▸ hσP)).elim

end Halves

/-- **The two sides of a line across a disc**, read by angles. The line `U` has its ends at the
points of angles `θx < θy` of `bd(Σ)`. The inner side `P` meets `bd(Σ)` in the angles `[θx, θy]`
and the outer side `Q` in the angles `[θy, θx + 2π]`. -/
structure LineSplit (f : Circle ≃ₜ bd S) (U : Set S) (θx θy : ℝ) (P Q : Set S) : Prop
    extends Halves U P Q where
  isLine : IsLineWithEnds U (GM19.cuffPoint f θx) (GM19.cuffPoint f θy)
  left_inter_bd : P ∩ bd S = GM19.cuffPoint f '' Icc θx θy
  right_inter_bd : Q ∩ bd S = GM19.cuffPoint f '' Icc θy (θx + 2 * Real.pi)

/-- **A line cuts a disc into two sides** (from `disc_iArc`, as in `Side.exists_disc_sides`). -/
theorem exists_lineSplit (hD : GM06.IsClosedDiscSpace S) (f : Circle ≃ₜ bd S) {U : Set S}
    {θx θy : ℝ} (hxy : θx < θy) (hyx : θy < θx + 2 * Real.pi)
    (hU : IsLineWithEnds U (GM19.cuffPoint f θx) (GM19.cuffPoint f θy))
    (hUbd : U ∩ bd S = {GM19.cuffPoint f θx, GM19.cuffPoint f θy}) :
    ∃ P Q : Set S, LineSplit f U θx θy P Q := by
  have : T2Space S := GM06.t2Space_of_isClosedDiscSpace hD
  have hpi := Real.pi_pos
  set x := GM19.cuffPoint f θx with hx
  set y := GM19.cuffPoint f θy with hy
  have hne : x ≠ y := by
    intro h
    have := GM17.cuffPoint_injOn_Ico f θx ⟨le_rfl, by linarith⟩ ⟨hxy.le, hyx⟩ h
    linarith
  obtain ⟨A₁, A₂, Δ₁, Δ₂, -, hcomp, hD₁, hD₂, hun, hint, hbd₁, hbd₂, -⟩ :=
    disc_iArc (univ : Set S) U x y hD.isClosedDisc_univ (subset_univ _) hne hU
      (by rw [GM06.discBd_univ]; exact hUbd)
  rw [GM06.discBd_univ, Side.componentsIn_diff_pair f hxy hyx] at hcomp
  set Pa := GM19.cuffPoint f '' Ioo θx θy
  set Qa := GM19.cuffPoint f '' Ioo θy (θx + 2 * Real.pi)
  have hPQ : bd S \ {x, y} = Pa ∪ Qa := Side.diff_pair_eq f hxy hyx
  have hPbd : Pa ⊆ bd S := fun z hz => (hPQ ▸ Or.inl hz : z ∈ bd S \ {x, y}).1
  have hQbd : Qa ⊆ bd S := fun z hz => (hPQ ▸ Or.inr hz : z ∈ bd S \ {x, y}).1
  have hdiscBd : ∀ D : Set S, discBd D ⊆ D := by
    rintro D _ ⟨z, -, rfl⟩
    exact z.2
  -- A side meets `bd(Σ)` in its arc and the ends of `U`.
  have hside : ∀ {D D' A A' : Set S}, D ∩ D' = U → discBd D = A ∪ U → discBd D' = A' ∪ U →
      bd S \ {x, y} ⊆ A ∪ A' → A ⊆ bd S → D ∩ bd S = A ∪ {x, y} := by
    intro D D' A A' hDD' hbdD hbdD' hcov hAbd
    have hUD : U ⊆ D := hDD' ▸ inter_subset_left
    ext z
    constructor
    · rintro ⟨hzD, hzbd⟩
      by_cases hz : z ∈ ({x, y} : Set S)
      · exact Or.inr hz
      rcases hcov ⟨hzbd, hz⟩ with h | h
      · exact Or.inl h
      · have hzD' : z ∈ D' := hdiscBd D' (hbdD' ▸ Or.inl h)
        have hzU : z ∈ U := hDD' ▸ ⟨hzD, hzD'⟩
        exact (hz (hUbd ▸ ⟨hzU, hzbd⟩)).elim
    · rintro (h | h)
      · exact ⟨hdiscBd D (hbdD ▸ Or.inl h), hAbd h⟩
      · have hzU : z ∈ U ∩ bd S := hUbd ▸ h
        exact ⟨hUD hzU.1, hzU.2⟩
  -- Every point of `U` is a limit of inner points of a side.
  have hcl : ∀ {D A : Set S}, IsClosedDisc D → discBd D = A ∪ U → U ⊆ closure (D \ U) := by
    intro D A hD hbd z hz
    have hUD : U ⊆ D := fun z hz => hdiscBd D (hbd ▸ Or.inr hz)
    refine closure_mono ?_ (hD.subset_closure_discInt (hUD hz))
    rintro w ⟨hwD, hwbd⟩
    exact ⟨hwD, fun hwU => hwbd (hbd ▸ Or.inr hwU)⟩
  have hIccP : Pa ∪ {x, y} = GM19.cuffPoint f '' Icc θx θy :=
    (Side.image_Icc_eq_union f hxy.le).symm
  have hIccQ : Qa ∪ {x, y} = GM19.cuffPoint f '' Icc θy (θx + 2 * Real.pi) := by
    rw [Side.image_Icc_eq_union f hyx.le, GM17.cuffPoint_add_two_pi, pair_comm]
  rcases pair_eq_pair_iff.mp hcomp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨Δ₁, Δ₂, ⟨⟨hD₁.isClosed, hD₂.isClosed, hun, hint, hcl hD₁ hbd₁, hcl hD₂ hbd₂⟩, hU,
      ?_, ?_⟩⟩
    · rw [hside hint hbd₁ hbd₂ hPQ.subset hPbd, hIccP]
    · rw [hside (by rw [Set.inter_comm]; exact hint) hbd₂ hbd₁ (hPQ ▸ by rw [Set.union_comm]) hQbd,
        hIccQ]
  · refine ⟨Δ₂, Δ₁, ⟨⟨hD₂.isClosed, hD₁.isClosed, by rw [Set.union_comm]; exact hun,
      by rw [Set.inter_comm]; exact hint, hcl hD₂ hbd₂, hcl hD₁ hbd₁⟩, hU, ?_, ?_⟩⟩
    · rw [hside (by rw [Set.inter_comm]; exact hint) hbd₂ hbd₁ hPQ.subset hPbd, hIccP]
    · rw [hside hint hbd₁ hbd₂ (hPQ ▸ by rw [Set.union_comm]) hQbd, hIccQ]

end halves

/-! ## The sides of a jump -/

section jumps

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
  (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
  {f : Circle ≃ₜ bd S} {w₀ w₁ : ℝ} {a b : Fin r → ℝ} (hW : Window Γ F_star f w₀ w₁ a b)
  (hK : IsLinkage G Γ_sub)
  (hdeg : ∀ y ∈ Γ_sub.vertexSet, y ∉ ιV '' (Γ.V ∩ bd S) → (incidentEdges Γ_sub y).ncard = 2)

set_option hygiene false in
local notation "𝒯" => jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))
set_option hygiene false in
local notation "LO" => jumpLo f w₀ w₁ Γ.V ιV
set_option hygiene false in
local notation "HI" => jumpHi f w₀ w₁ Γ.V ιV
set_option hygiene false in
local notation "cp" => GM19.cuffPoint f
set_option hygiene false in
local notation "UJ" => LastStep.jumpLine Γ ιE

/-- The closure of an edge of a jump lies in the line of the jump. -/
theorem closure_subset_jumpLine {J : Hypergraph α β} {e : Set S} (he : e ∈ Γ.E)
    (heJ : ιE e ∈ J.edgeSet) : closure e ⊆ UJ J :=
  fun _ hz => LastStep.mem_jumpLine.2 ⟨e, he, heJ, hz⟩

/-- The line of a jump lies in `U(Γ)`. -/
theorem jumpLine_subset_U (J : Hypergraph α β) : UJ J ⊆ Γ.U := by
  intro z hz
  obtain ⟨e, he, -, hze⟩ := LastStep.mem_jumpLine.1 hz
  exact closure_minimal (fun y hy => (he.2.1 hy).1) Γ.isClosed_U hze

include h_pres hK in
/-- An edge of `Γ` at a vertex `x` has `x` as one of its two ends. -/
theorem exists_other_end {e : Set S} (he : e ∈ Γ.E) {x : S} (hx : x ∈ closure e ∩ Γ.V) :
    ∃ u, u ≠ x ∧ closure e ∩ Γ.V = {x, u} := by
  have hiso := h_pres.drawing_iso
  have heE : ιE e ∈ Γ_sub.edgeSet := hiso.ιE_image ▸ mem_image_of_mem ιE he
  have h2 := hK.ends_ncard_eq_two heE
  obtain ⟨a', b', hab', hends⟩ := ncard_eq_two.1 h2
  have ha' : Γ_sub.Inc (ιE e) a' := show a' ∈ Γ_sub.ends (ιE e) from hends ▸ Or.inl rfl
  have hb' : Γ_sub.Inc (ιE e) b' := show b' ∈ Γ_sub.ends (ιE e) from hends ▸ Or.inr rfl
  obtain ⟨a, ha, rfl⟩ : a' ∈ ιV '' Γ.V := hiso.ιV_image ▸ Γ_sub.vertex_mem_of_inc ha'
  obtain ⟨b, hb, rfl⟩ : b' ∈ ιV '' Γ.V := hiso.ιV_image ▸ Γ_sub.vertex_mem_of_inc hb'
  have hab : a ≠ b := fun h => hab' (congrArg ιV h)
  have hcl := LastStep.closure_inter_V_eq hiso he ha hb hab h2 ha' hb'
  rw [hcl] at hx ⊢
  rcases hx with rfl | h
  · exact ⟨b, hab.symm, rfl⟩
  · rw [mem_singleton_iff] at h
    subst h
    exact ⟨a, hab, pair_comm _ _⟩

include h_pres hW hK

/-- **The line of a jump** is a line from the point of angle `lo J` to the point of angle `hi J`,
and it meets `bd(Σ)` only in these two points. -/
theorem jumpLine_spec' {J : Hypergraph α β} (hJ : J ∈ 𝒯) :
    IsLineWithEnds (UJ J) (cp (LO J)) (cp (HI J)) ∧ UJ J ∩ bd S = {cp (LO J), cp (HI J)} := by
  have : T2Space S := h_pres.is_surface.2.1
  obtain ⟨-, -, -, hloV, hhiV, hterm⟩ := hW.jumpAngles_spec h_pres hJ
  have hiso := h_pres.drawing_iso
  have h2 : ∀ e ∈ Γ_sub.edgeSet, (Γ_sub.ends e).ncard = 2 := fun e he => hK.ends_ncard_eq_two he
  obtain ⟨x, hx, y, hy, hxy, hterm', hline, -⟩ :=
    LastStep.jumpLine_spec hiso h2 hJ.1 hJ.2.1 (edgeSet_nonempty_of_mem_jumpSet hJ)
  have hmem : ∀ z ∈ Γ.V, ιV z ∈ terminals J → z = cp (LO J) ∨ z = cp (HI J) := by
    intro z hz hzt
    rw [hterm] at hzt
    rcases hzt with h | h
    · exact Or.inl (hiso.ιV_injOn hz hloV h)
    · exact Or.inr (hiso.ιV_injOn hz hhiV (mem_singleton_iff.mp h))
  have hxt : ιV x ∈ terminals J := by rw [hterm']; exact Or.inl rfl
  have hyt : ιV y ∈ terminals J := by rw [hterm']; exact Or.inr rfl
  have hline' : IsLineWithEnds (UJ J) (cp (LO J)) (cp (HI J)) := by
    rcases hmem x hx hxt with rfl | rfl <;> rcases hmem y hy hyt with rfl | rfl
    · exact absurd rfl hxy
    · exact hline
    · exact hline.symm
    · exact absurd rfl hxy
  refine ⟨hline', Subset.antisymm ?_ ?_⟩
  · intro z hz
    obtain ⟨hzV, hzt⟩ := LastStep.jumpLine_inter_bd_subset h_pres.is_proper_drawing hiso hJ hz
    exact hmem z hzV hzt
  · rintro z (rfl | h)
    · exact ⟨hline'.left_mem, GM17.cuffPoint_mem f _⟩
    · rw [mem_singleton_iff] at h
      subst h
      exact ⟨hline'.right_mem, GM17.cuffPoint_mem f _⟩

/-- **The two sides of a jump.** -/
theorem exists_jumpSplit (hD : GM06.IsClosedDiscSpace S) {J : Hypergraph α β} (hJ : J ∈ 𝒯) :
    ∃ P Q : Set S, LineSplit f (UJ J) (LO J) (HI J) P Q := by
  obtain ⟨hlo₀, hlohi, hhi₁, -⟩ := hW.jumpAngles_spec h_pres hJ
  obtain ⟨hline, hbd⟩ := jumpLine_spec' h_pres hW hK hJ
  exact exists_lineSplit hD f hlohi (by linarith [hW.lt_add]) hline hbd

/-- Sides for all jumps at once. -/
theorem exists_jumpSplits (hD : GM06.IsClosedDiscSpace S) :
    ∃ P Q : Hypergraph α β → Set S, ∀ J ∈ 𝒯, LineSplit f (UJ J) (LO J) (HI J) (P J) (Q J) := by
  classical
  refine ⟨fun J => if hJ : J ∈ 𝒯 then (exists_jumpSplit h_pres hW hK hD hJ).choose else ∅,
    fun J => if hJ : J ∈ 𝒯 then (exists_jumpSplit h_pres hW hK hD hJ).choose_spec.choose else ∅,
    fun J hJ => ?_⟩
  simp only [hJ, ↓reduceDIte]
  exact (exists_jumpSplit h_pres hW hK hD hJ).choose_spec.choose_spec

omit hW
include hdeg

/-- **A region along a jump.** In a disc, a region whose closure holds one edge of a jump `J`
holds every edge of `J` in its closure. Otherwise some vertex `w` of `J` is an end of an edge
`e₁` of `J` in the closure and of an edge `e₂` of `J` that is not. Then `w` is not an end of `J`,
so it is not in `bd(Σ)` and its only edges are `e₁` and `e₂`, and a region next to `e₁` is next to
`e₂` (`DiscLine.subset_closure_of_two_edges`). -/
theorem edge_subset_closure_of_jump (hD : GM06.IsClosedDiscSpace S) {J : Hypergraph α β}
    (hJ : J ∈ 𝒯) {ρ : Set S} (hρ : ρ ∈ Γ.R) {e₀ : Set S} (he₀ : e₀ ∈ Γ.E)
    (he₀J : ιE e₀ ∈ J.edgeSet) (he₀ρ : e₀ ⊆ closure ρ) {e : Set S} (he : e ∈ Γ.E)
    (heJ : ιE e ∈ J.edgeSet) : e ⊆ closure ρ := by
  classical
  have : T2Space S := GM06.t2Space_of_isClosedDiscSpace hD
  have hiso := h_pres.drawing_iso
  have hprop := h_pres.is_proper_drawing
  by_contra hcon
  let Pp : β → Prop := fun g => ∃ e' ∈ Γ.E, ιE e' = g ∧ e' ⊆ closure ρ
  have hP₀ : Pp (ιE e₀) := ⟨e₀, he₀, rfl, he₀ρ⟩
  have hP₁ : ¬ Pp (ιE e) := by
    rintro ⟨e', he', heq, h⟩
    rw [hiso.ιE_injOn he' he heq] at h
    exact hcon h
  -- An end of an edge of `J`.
  have hend : ∀ g ∈ J.edgeSet, ∃ x, J.Inc g x := by
    intro g hg
    obtain ⟨x, hx⟩ := nonempty_of_ncard_ne_zero
      (by rw [hK.ends_ncard_eq_two (hJ.1.edgeSet_subset hg)]; omega : (Γ_sub.ends g).ncard ≠ 0)
    exact ⟨x, (GM10.inc_iff_of_le hJ.1 hg).2 hx⟩
  obtain ⟨x₀, hx₀⟩ := hend _ he₀J
  obtain ⟨x₁, hx₁⟩ := hend _ heJ
  obtain ⟨w, g, g', hgw, hg'w, hPg, hPg'⟩ :=
    Side.exists_inc_of_reachable Pp hJ.2.1.2.2.1 hx₀ hx₁ hP₀ hP₁
  have hgg : g ≠ g' := fun h => hPg' (h ▸ hPg)
  have hwJ : w ∈ J.vertexSet := J.vertex_mem_of_inc hgw
  have hwB : w ∉ ιV '' (Γ.V ∩ bd S) := fun hB =>
    Side.not_mem_terminals_of_inc hgw hg'w hgg (mem_terminals_of_mem_jumpSet hJ hwJ hB)
  have hinc := incidentEdges_jump_eq hdeg hJ hwJ hwB
  have h2 := hdeg w (hJ.1.vertexSet_subset hwJ) hwB
  obtain ⟨w₀, hw₀, rfl⟩ : w ∈ ιV '' Γ.V := hiso.ιV_image ▸ hJ.1.vertexSet_subset hwJ
  have hw₀bd : w₀ ∉ bd S := fun h => hwB ⟨w₀, ⟨hw₀, h⟩, rfl⟩
  have hgK : g ∈ incidentEdges Γ_sub (ιV w₀) := hinc ▸ ⟨J.edge_mem_of_inc hgw, hgw⟩
  have hg'K : g' ∈ incidentEdges Γ_sub (ιV w₀) := hinc ▸ ⟨J.edge_mem_of_inc hg'w, hg'w⟩
  obtain ⟨e₁, he₁, rfl⟩ : g ∈ ιE '' Γ.E := hiso.ιE_image ▸ hgK.1
  obtain ⟨e₂, he₂, rfl⟩ : g' ∈ ιE '' Γ.E := hiso.ιE_image ▸ hg'K.1
  have he₁ρ : e₁ ⊆ closure ρ := by
    obtain ⟨e', he', heq, h⟩ := hPg
    rwa [hiso.ιE_injOn he' he₁ heq] at h
  have hee : e₁ ≠ e₂ := fun h => hgg (h ▸ rfl)
  have hwe₁ : w₀ ∈ closure e₁ := (hiso.inc_iff e₁ he₁ w₀ hw₀).mp hgK.2
  have hwe₂ : w₀ ∈ closure e₂ := (hiso.inc_iff e₂ he₂ w₀ hw₀).mp hg'K.2
  obtain ⟨u, huw, hcl₁⟩ := exists_other_end h_pres hK he₁ ⟨hwe₁, hw₀⟩
  obtain ⟨v, hvw, hcl₂⟩ := exists_other_end h_pres hK he₂ ⟨hwe₂, hw₀⟩
  have hends : ∀ {e' : Set S}, e' ∈ Γ.E → Γ_sub.ends (ιE e') = ιV '' (closure e' ∩ Γ.V) := by
    intro e' he'
    ext y
    simp only [Hypergraph.ends, mem_ofPred_eq]
    constructor
    · intro hy
      obtain ⟨z, hz, rfl⟩ : y ∈ ιV '' Γ.V := hiso.ιV_image ▸ Γ_sub.vertex_mem_of_inc hy
      exact ⟨z, ⟨(hiso.inc_iff e' he' z hz).mp hy, hz⟩, rfl⟩
    · rintro ⟨z, ⟨hze, hz⟩, rfl⟩
      exact (hiso.inc_iff e' he' z hz).mpr hze
  -- The two other ends differ, since `J` has no parallel edges.
  have huv : u ≠ v := by
    rintro rfl
    have h1 : J.ends (ιE e₁) = J.ends (ιE e₂) := by
      rw [← hJ.1.ends_eq _ (J.edge_mem_of_inc hgw), ← hJ.1.ends_eq _ (J.edge_mem_of_inc hg'w),
        hends he₁, hends he₂, hcl₁, hcl₂]
    exact hgg (hJ.2.1.2.2.2.2.1 _ (J.edge_mem_of_inc hgw) _ (J.edge_mem_of_inc hg'w) h1)
  have hdeg' : ∀ f' ∈ Γ.E, w₀ ∈ closure f' → f' = e₁ ∨ f' = e₂ := by
    intro f' hf' hwf
    have hf'K : ιE f' ∈ incidentEdges Γ_sub (ιV w₀) :=
      ⟨hiso.ιE_image ▸ mem_image_of_mem ιE hf', (hiso.inc_iff f' hf' w₀ hw₀).mpr hwf⟩
    obtain ⟨g₁, g₂, hg12, hg12'⟩ := ncard_eq_two.mp h2
    rw [hg12'] at hf'K hgK hg'K
    simp only [mem_insert_iff, mem_singleton_iff] at hf'K hgK hg'K
    have hcases : ιE f' = ιE e₁ ∨ ιE f' = ιE e₂ := by
      rcases hf'K with h₀ | h₀ <;> rcases hgK with h₁ | h₁ <;> rcases hg'K with h₂ | h₂ <;>
        first
        | exact Or.inl (h₀.trans h₁.symm)
        | exact Or.inr (h₀.trans h₂.symm)
        | exact absurd (h₁.trans h₂.symm) hgg
    rcases hcases with h | h
    · exact Or.inl (hiso.ιE_injOn hf' he₁ h)
    · exact Or.inr (hiso.ιE_injOn hf' he₂ h)
  obtain ⟨z, hz⟩ := he₁.1
  have := DiscLine.subset_closure_of_two_edges hD hprop he₁ he₂ hee
    (by rw [hcl₁, pair_comm]) hcl₂ huw hvw huv hdeg' hw₀bd hρ ⟨z, hz, he₁ρ hz⟩
  exact hPg' ⟨e₂, he₂, rfl, this⟩

/-- A region whose closure holds one edge of a jump `J` holds all of `U(J)` in its closure. -/
theorem jumpLine_subset_closure (hD : GM06.IsClosedDiscSpace S) {J : Hypergraph α β}
    (hJ : J ∈ 𝒯) {ρ : Set S} (hρ : ρ ∈ Γ.R) {e₀ : Set S} (he₀ : e₀ ∈ Γ.E)
    (he₀J : ιE e₀ ∈ J.edgeSet) (he₀ρ : e₀ ⊆ closure ρ) : UJ J ⊆ closure ρ := by
  intro z hz
  obtain ⟨e, he, heJ, hze⟩ := LastStep.mem_jumpLine.1 hz
  exact closure_minimal (edge_subset_closure_of_jump h_pres hK hdeg hD hJ hρ he₀ he₀J he₀ρ he heJ)
    isClosed_closure hze

omit hK hdeg in
/-- A jump has an edge of `Γ`. -/
theorem exists_edge_of_jump {J : Hypergraph α β} (hJ : J ∈ 𝒯) :
    ∃ e ∈ Γ.E, ιE e ∈ J.edgeSet := by
  obtain ⟨g, hg⟩ := edgeSet_nonempty_of_mem_jumpSet hJ
  obtain ⟨e, he, rfl⟩ : g ∈ ιE '' Γ.E := h_pres.drawing_iso.ιE_image ▸ hJ.1.edgeSet_subset hg
  exact ⟨e, he, hg⟩

/-- **The regions of a jump.** For sides `P, Q` of a jump `J`, there is a region off `Q` with all
of `U(J)` in its closure (the inner region of `J`). -/
theorem exists_region_of_jump (hD : GM06.IsClosedDiscSpace S) {J : Hypergraph α β} (hJ : J ∈ 𝒯)
    {P Q : Set S} (hs : Halves (UJ J) P Q) : ∃ ρ ∈ Γ.R, ρ ⊆ Qᶜ ∧ UJ J ⊆ closure ρ := by
  obtain ⟨e, he, heJ⟩ := exists_edge_of_jump h_pres hJ
  obtain ⟨ρ, hρ, hρQ, heρ⟩ := hs.exists_region_right hD h_pres.is_proper_drawing
    (jumpLine_subset_U J) he (subset_closure.trans (closure_subset_jumpLine he heJ))
  exact ⟨ρ, hρ, hρQ, jumpLine_subset_closure h_pres hK hdeg hD hJ hρ he heJ heρ⟩

omit hK hdeg in
/-- Only one region off `Q` has `U(J)` in its closure. -/
theorem region_eq_of_jump (hD : GM06.IsClosedDiscSpace S) {J : Hypergraph α β} (hJ : J ∈ 𝒯)
    {P Q : Set S} (hs : Halves (UJ J) P Q) {ρ ρ' : Set S} (hρ : ρ ∈ Γ.R) (hρ' : ρ' ∈ Γ.R)
    (hρQ : ρ ⊆ Qᶜ) (hρ'Q : ρ' ⊆ Qᶜ) (hUρ : UJ J ⊆ closure ρ) (hUρ' : UJ J ⊆ closure ρ') :
    ρ = ρ' := by
  obtain ⟨e, he, heJ⟩ := exists_edge_of_jump h_pres hJ
  have heU : e ⊆ UJ J := subset_closure.trans (closure_subset_jumpLine he heJ)
  exact hs.region_eq_right hD h_pres.is_proper_drawing (jumpLine_subset_U J) he heU hρ hρ' hρQ
    hρ'Q (heU.trans hUρ) (heU.trans hUρ')

end jumps

end RegionTree
end GM21
end GraphMinor
