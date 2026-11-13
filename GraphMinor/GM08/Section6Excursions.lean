module

public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM08.Section6Components
import GraphMinor.Surface.DiscMerge
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Excursion components on the parameter circle

For VIII (6.2), page 264, the second curve is split into the components
outside the first closed disc. This file identifies each component with
the open part of an arc, whose two endpoints lie on the closed barrier.
There is no assumption that only finitely many such components exist.
-/

public section

namespace GraphMinor.GM08

open Set Topology Surface

universe u

local notation "𝕀" => unitInterval

/-- If two arcs make up a circle and one open arc avoids a barrier while
its endpoints lie on that barrier, the open arc is a whole complementary
component. Connectivity prevents a component from switching between the
two arcs without passing an endpoint. -/
theorem open_arc_eq_component_of_two_arcs {X : Type u} [TopologicalSpace X] [T2Space X]
    {T : Set X} {a b : 𝕀 → X} (hab : IsTwoArcs a b)
    (hcover : range a ∪ range b = univ) (ha0 : a 0 ∈ T) (ha1 : a 1 ∈ T)
    (havoid : ∀ r, r ≠ 0 → r ≠ 1 → a r ∉ T)
    {z : X} (hzT : z ∉ T) (hza : z ∈ range a) :
    a '' Ioo (0 : 𝕀) 1 = connectedComponentIn Tᶜ z := by
  have hPsub : a '' Ioo (0 : 𝕀) 1 ⊆ Tᶜ := by
    rintro _ ⟨r, hr, rfl⟩
    exact havoid r (ne_of_gt hr.1) (ne_of_lt hr.2)
  have hzP : z ∈ a '' Ioo (0 : 𝕀) 1 := by
    obtain ⟨r, rfl⟩ := hza
    have hr0 : r ≠ 0 := fun h => hzT (h ▸ ha0)
    have hr1 : r ≠ 1 := fun h => hzT (h ▸ ha1)
    exact ⟨r, ⟨lt_of_le_of_ne (unitInterval.nonneg r) hr0.symm,
      lt_of_le_of_ne (unitInterval.le_one r) hr1⟩, rfl⟩
  have hPpre : IsPreconnected (a '' Ioo (0 : 𝕀) 1) :=
    isPreconnected_Ioo.image a hab.1.1.continuousOn
  have hcomp_sub : connectedComponentIn Tᶜ z ⊆ (range b)ᶜ := by
    have hdis : Disjoint ((range b)ᶜ) ((range a)ᶜ) := by
      apply Set.disjoint_left.mpr
      intro x hxb hxa
      have hx : x ∈ range a ∪ range b := hcover.symm ▸ mem_univ x
      exact hx.elim hxa hxb
    have hcov : connectedComponentIn Tᶜ z ⊆ (range b)ᶜ ∪ (range a)ᶜ := by
      intro x hx
      by_cases hxb : x ∈ range b
      · right
        rintro ⟨s, hs⟩
        obtain ⟨t, ht⟩ := hxb
        rcases hab.5 s t (hs.trans ht.symm) with h | h
        · exact connectedComponentIn_subset Tᶜ z hx (hs ▸ (h.1 ▸ ha0))
        · exact connectedComponentIn_subset Tᶜ z hx (hs ▸ (h.1 ▸ ha1))
      · exact Or.inl hxb
    rcases isPreconnected_connectedComponentIn.subset_or_subset
      (isCompact_range hab.2.1).isClosed.isOpen_compl
      (isCompact_range hab.1.1).isClosed.isOpen_compl hdis hcov with h | h
    · exact h
    · exact False.elim (h (mem_connectedComponentIn hzT) hza)
  apply subset_antisymm
  · exact hPpre.subset_connectedComponentIn hzP hPsub
  · intro x hx
    have hxT : x ∉ T := connectedComponentIn_subset Tᶜ z hx
    have hxa : x ∈ range a := by
      have hxu : x ∈ range a ∪ range b := hcover.symm ▸ mem_univ x
      exact hxu.resolve_right (hcomp_sub hx)
    obtain ⟨r, rfl⟩ := hxa
    have hr0 : r ≠ 0 := fun h => hxT (h ▸ ha0)
    have hr1 : r ≠ 1 := fun h => hxT (h ▸ ha1)
    exact ⟨r, ⟨lt_of_le_of_ne (unitInterval.nonneg r) hr0.symm,
      lt_of_le_of_ne (unitInterval.le_one r) hr1⟩, rfl⟩

/-- Every complementary component of a closed subset of a circle with at
least two points is an open arc with endpoints in that closed set.
This supplies the individual excursions for VIII (6.2). -/
theorem exists_circle_excursion_component {T : Set Circle} (hT : IsClosed T)
    {x y z : Circle} (hx : x ∈ T) (hy : y ∈ T) (hxy : x ≠ y) (hz : z ∉ T) :
    ∃ a b : 𝕀 → Circle, IsTwoArcs a b ∧ range a ∪ range b = univ ∧
      a 0 ∈ T ∧ a 1 ∈ T ∧ a '' Ioo (0 : 𝕀) 1 = connectedComponentIn Tᶜ z := by
  obtain ⟨a, b, hab, hcover, ha0, ha1, havoid, hza⟩ :=
    exists_circle_chord hT hz hx hy hxy
  exact ⟨a, b, hab, hcover, ha0, ha1,
    open_arc_eq_component_of_two_arcs hab hcover ha0 ha1 havoid hz hza⟩

/-- A connected subset of a circle avoiding the two common endpoints of
its defining arcs lies in one of those arcs. -/
theorem preconnected_subset_one_of_two_arcs {X : Type u} [TopologicalSpace X] [T2Space X]
    {a b : 𝕀 → X} (hab : IsTwoArcs a b) {P : Set X} (hP : IsPreconnected P)
    (hsub : P ⊆ range a ∪ range b) (hp0 : a 0 ∉ P) (hp1 : a 1 ∉ P) :
    P ⊆ range a ∨ P ⊆ range b := by
  by_cases hPa : P ⊆ range a
  · exact Or.inl hPa
  by_cases hPb : P ⊆ range b
  · exact Or.inr hPb
  obtain ⟨x, hxP, hxa⟩ := not_subset.mp hPa
  obtain ⟨y, hyP, hyb⟩ := not_subset.mp hPb
  have hcov : P ⊆ (range b)ᶜ ∪ (range a)ᶜ := by
    intro z hz
    by_cases hzb : z ∈ range b
    · right
      rintro ⟨s, hs⟩
      obtain ⟨t, ht⟩ := hzb
      rcases hab.5 s t (hs.trans ht.symm) with h | h
      · exact hp0 ((hs.symm.trans (congrArg a h.1)) ▸ hz)
      · exact hp1 ((hs.symm.trans (congrArg a h.1)) ▸ hz)
    · exact Or.inl hzb
  obtain ⟨z, hzP, hzb, hza⟩ := hP (range b)ᶜ (range a)ᶜ
    (isCompact_range hab.2.1).isClosed.isOpen_compl
    (isCompact_range hab.1.1).isClosed.isOpen_compl hcov
    ⟨y, hyP, hyb⟩ ⟨x, hxP, hxa⟩
  exact False.elim ((hsub hzP).elim hza hzb)

/-- Disjoint connected subsets of a circle have only finitely many large
members at each positive scale. At most two members contain the chosen
arc endpoints. Every remaining member lies in one of the two embedded
arcs, where the parameter-interval bound applies. -/
theorem finite_large_disjoint_preconnected_subsets_of_two_arcs
    {Y : Type u} [MetricSpace Y] {a b : 𝕀 → Y} (hab : IsTwoArcs a b)
    {A : Set (Set Y)} (hA : ∀ J ∈ A, IsPreconnected J)
    (hsub : ∀ J ∈ A, J ⊆ range a ∪ range b) (hdis : A.PairwiseDisjoint id)
    {ε : ℝ} (hε : 0 < ε) :
    {J ∈ A | ∃ x ∈ J, ∃ y ∈ J, ε ≤ dist x y}.Finite := by
  have hexc : ∀ x : Y, {J ∈ A | x ∈ J}.Finite := by
    intro x
    apply Set.Subsingleton.finite
    intro J hJ K hK
    by_contra hne
    exact Set.disjoint_left.mp (hdis hJ.1 hK.1 hne) hJ.2 hK.2
  have hleft := finite_large_disjoint_preconnected_subsets_of_arc hab.1
    (fun J (hJ : J ∈ A ∧ J ⊆ range a) => hA J hJ.1)
    (fun _ (hJ : _ ∈ A ∧ _ ⊆ range a) => hJ.2)
    (fun _ hJ _ hK hne => hdis hJ.1 hK.1 hne) hε
  have hright := finite_large_disjoint_preconnected_subsets_of_arc hab.2
    (fun J (hJ : J ∈ A ∧ J ⊆ range b) => hA J hJ.1)
    (fun _ (hJ : _ ∈ A ∧ _ ⊆ range b) => hJ.2)
    (fun _ hJ _ hK hne => hdis hJ.1 hK.1 hne) hε
  refine ((hexc (a 0)).union (hexc (a 1))).union hleft |>.union hright |>.subset ?_
  rintro J ⟨hJA, hlarge⟩
  by_cases h0 : a 0 ∈ J
  · exact Or.inl (Or.inl (Or.inl ⟨hJA, h0⟩))
  by_cases h1 : a 1 ∈ J
  · exact Or.inl (Or.inl (Or.inr ⟨hJA, h1⟩))
  rcases preconnected_subset_one_of_two_arcs hab (hA J hJA) (hsub J hJA) h0 h1 with h | h
  · exact Or.inl (Or.inr ⟨⟨hJA, h⟩, hlarge⟩)
  · exact Or.inr ⟨⟨hJA, h⟩, hlarge⟩

/-- A disjoint family of connected subsets of an `O`-arc has only finitely
many large members at each positive scale. This applies to all excursion
components of the second curve in VIII (6.2). -/
theorem finite_large_disjoint_preconnected_subsets_of_oArc
    {Y : Type u} [MetricSpace Y] {F : Set Y} (hF : IsOArc F)
    {A : Set (Set Y)} (hA : ∀ J ∈ A, IsPreconnected J)
    (hsub : ∀ J ∈ A, J ⊆ F) (hdis : A.PairwiseDisjoint id)
    {ε : ℝ} (hε : 0 < ε) :
    {J ∈ A | ∃ x ∈ J, ∃ y ∈ J, ε ≤ dist x y}.Finite := by
  obtain ⟨φ⟩ := hF
  have hne : (φ (1 : Circle)).1 ≠ (φ (-1 : Circle)).1 := by
    intro he
    have hc : (1 : Circle) = -1 := φ.injective (Subtype.ext he)
    have hn := congrArg (fun w : Circle => (w : ℂ)) hc
    norm_num at hn
  obtain ⟨a, b, hab, _, _, hr⟩ :=
    IsOArc.exists_arcs ⟨φ⟩ (φ (1 : Circle)).2 (φ (-1 : Circle)).2 hne
  exact finite_large_disjoint_preconnected_subsets_of_two_arcs hab hA
    (fun J hJ => hr.symm ▸ hsub J hJ) hdis hε

/-- The excursion size bound also holds for closures, so it controls the
complete replacement arcs, including their endpoints. Taking closures
leaves the diameter unchanged. -/
theorem finite_large_closures_of_disjoint_preconnected_subsets_of_oArc
    {Y : Type u} [MetricSpace Y] {F : Set Y} (hF : IsOArc F)
    {A : Set (Set Y)} (hA : ∀ J ∈ A, IsPreconnected J)
    (hsub : ∀ J ∈ A, J ⊆ F) (hdis : A.PairwiseDisjoint id)
    {ε : ℝ} (hε : 0 < ε) :
    {J ∈ A | ∃ x ∈ closure J, ∃ y ∈ closure J, ε ≤ dist x y}.Finite := by
  refine (finite_large_disjoint_preconnected_subsets_of_oArc hF hA hsub hdis
    (half_pos hε)).subset ?_
  rintro J ⟨hJA, x, hx, y, hy, hdist⟩
  refine ⟨hJA, ?_⟩
  by_contra hn
  have hbound : Metric.diam J ≤ ε / 2 := by
    apply Metric.diam_le_of_forall_dist_le (half_pos hε).le
    intro s hs t ht
    exact (lt_of_not_ge (fun h => hn ⟨s, hs, t, ht, h⟩)).le
  have hbounded : Bornology.IsBounded (closure J) := hF.isCompact.isBounded.subset
    (closure_minimal (hsub J hJA) hF.isCompact.isClosed)
  have hxy : dist x y ≤ ε / 2 := (Metric.dist_le_diam_of_mem hbounded hx hy).trans
    (by rwa [Metric.diam_closure])
  exact (not_lt_of_ge hdist) (hxy.trans_lt (half_lt_self hε))

/-- Adding the two endpoint values to an open arc gives its closure.
This identifies the closure of an excursion component with the complete
replacement arc. -/
theorem closure_open_arc_image_eq_range {X : Type u} [TopologicalSpace X] [T2Space X]
    {a : 𝕀 → X} (ha : Continuous a) :
    closure (a '' Ioo (0 : 𝕀) 1) = range a := by
  apply subset_antisymm
  · exact closure_minimal (image_subset_range _ _) (isCompact_range ha).isClosed
  · rintro _ ⟨t, rfl⟩
    apply mem_closure_image ha.continuousAt
    rw [closure_Ioo zero_ne_one]
    exact ⟨unitInterval.nonneg t, unitInterval.le_one t⟩

/-- The closures of all components of a curve outside any set form a null
family. Thus the complete excursion arcs used in VIII (6.2) have the size
control required by the infinite gluing lemma. -/
theorem finite_large_closures_of_excursion_components
    {Y : Type u} [MetricSpace Y] {F : Set Y} (hF : IsOArc F) (D : Set Y)
    {ε : ℝ} (hε : 0 < ε) :
    {J ∈ componentsIn (F \ D) |
      ∃ x ∈ closure J, ∃ y ∈ closure J, ε ≤ dist x y}.Finite := by
  apply finite_large_closures_of_disjoint_preconnected_subsets_of_oArc hF
  · rintro _ ⟨x, hx, rfl⟩
    exact isPreconnected_connectedComponentIn
  · rintro _ ⟨x, hx, rfl⟩
    exact (connectedComponentIn_subset (F \ D) x).trans sdiff_subset
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    exact hne ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm)
  · exact hε

/-- A connected arc that avoids the two splitting endpoints and meets the
retained side stays on that side. Taking its closure also retains its own
endpoints. In VIII (6.2), this shows that the common exterior access arc
is retained by every excursion enlargement. -/
theorem range_subset_arc_of_open_arc_avoids_endpoints
    {X : Type u} [TopologicalSpace X] [T2Space X] {a b q : 𝕀 → X}
    (hab : IsTwoArcs a b) (hq : Continuous q)
    (hsub : range q ⊆ range a ∪ range b)
    (h0 : a 0 ∉ q '' Ioo (0 : 𝕀) 1) (h1 : a 1 ∉ q '' Ioo (0 : 𝕀) 1)
    (hmeet : (q '' Ioo (0 : 𝕀) 1 ∩ range a).Nonempty) : range q ⊆ range a := by
  have hPsub : q '' Ioo (0 : 𝕀) 1 ⊆ range a := by
    rcases preconnected_subset_one_of_two_arcs hab
      (isPreconnected_Ioo.image q hq.continuousOn)
      ((image_subset_range _ _).trans hsub) h0 h1 with h | h
    · exact h
    · obtain ⟨x, hxq, s, hs⟩ := hmeet
      obtain ⟨t, ht⟩ := h hxq
      rcases hab.5 s t (hs.trans ht.symm) with he | he
      · exact False.elim (h0 ((hs.symm.trans (congrArg a he.1)) ▸ hxq))
      · exact False.elim (h1 ((hs.symm.trans (congrArg a he.1)) ▸ hxq))
  rw [← closure_open_arc_image_eq_range hq]
  exact closure_minimal hPsub (isCompact_range hab.1.1).isClosed

/-- Endpoint pairs of excursion closures span only finitely many large
intervals on a fixed embedded arc. The inverse parameter modulus turns a
large parameter span into a large pair of points in the excursion closure. -/
theorem finite_large_parameter_spans_of_excursion_endpoints
    {Y : Type u} [MetricSpace Y] {F : Set Y} (hF : IsOArc F) (D : Set Y)
    {f : 𝕀 → Y} (hf : IsArcMap f)
    (s t : {J : Set Y // J ∈ componentsIn (F \ D)} → 𝕀)
    (hs : ∀ J, f (s J) ∈ closure J.1) (ht : ∀ J, f (t J) ∈ closure J.1)
    {ε : ℝ} (hε : 0 < ε) :
    {J | ε ≤ (t J).1 - (s J).1}.Finite := by
  obtain ⟨δ, hδ, hmod⟩ := uniform_parameter_control_of_arc hf ε hε
  have hfinite := finite_large_closures_of_excursion_components hF D hδ
  have hpre := hfinite.preimage_embedding
    (⟨Subtype.val, Subtype.val_injective⟩ : {J : Set Y // J ∈ componentsIn (F \ D)} ↪ Set Y)
  refine hpre.subset ?_
  intro J hspan
  change ε ≤ (t J).1 - (s J).1 at hspan
  have hst : (s J).1 ≤ (t J).1 := by linarith
  have hparam : ε ≤ dist (s J) (t J) := by
    change ε ≤ |(s J).1 - (t J).1|
    rw [abs_of_nonpos (sub_nonpos.mpr hst)]
    linarith
  have hd : δ ≤ dist (f (s J)) (f (t J)) := by
    apply le_of_not_gt
    intro hlt
    exact (not_lt_of_ge hparam) (hmod (s J) (t J) hlt)
  exact ⟨J.2, f (s J), hs J, f (t J), ht J, hd⟩

end GraphMinor.GM08
