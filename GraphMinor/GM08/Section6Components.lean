module

public import GraphMinor.Surface.Defs
public import GraphMinor.Surface.CrossCut
public import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.MetricSpace.Basic

/-!
# Compact sets and excursions in the proof of VIII (6.2)

The two curves in (6.2), page 264, can have infinitely many crossings.
In a locally connected parameter space, only finitely many components of
an open set meet a compact subset of that open set. Applied on the parameter
circle, this controls excursions away from the other curve without assuming
that there are only finitely many excursions in total.
-/

public section

namespace GraphMinor.GM08

open Set Topology Surface

universe u v

/-- A compact subset of an open set meets only finitely many of its connected
components in a locally connected space. In VIII (6.2), the open set is the
part of the parameter circle outside the first closed disc. -/
theorem finite_componentsIn_meeting_compact {X : Type u} [TopologicalSpace X]
    [LocallyConnectedSpace X] {U K : Set X} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) :
    {J ∈ componentsIn U | (J ∩ K).Nonempty}.Finite := by
  classical
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun x : U => connectedComponentIn U x.1) (fun _ => hU.connectedComponentIn)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hKU hx⟩, mem_connectedComponentIn (hKU hx)⟩)
  refine (t.finite_toSet.image (fun x : U => connectedComponentIn U x.1)).subset ?_
  rintro J ⟨⟨z, hzU, rfl⟩, y, hyJ, hyK⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht hyK)
  exact ⟨x, hxt, (connectedComponentIn_eq hyx).trans
    (connectedComponentIn_eq hyJ).symm⟩

/-- Among pairwise disjoint intervals in `[0,1]`, only finitely many have
length at least a fixed positive number. Small excursions in the proof of
VIII (6.2) can therefore be treated as a family whose lengths tend to zero. -/
theorem finite_long_disjoint_intervals {A : Set (Set ℝ)}
    (hA : ∀ J ∈ A, OrdConnected J) (hbound : ∀ J ∈ A, J ⊆ Icc 0 1)
    (hdis : A.PairwiseDisjoint id) {ε : ℝ} (hε : 0 < ε) :
    {J ∈ A | ∃ a ∈ J, ∃ b ∈ J, ε ≤ b - a}.Finite := by
  classical
  obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover
    (fun x : ℝ => Metric.ball x (ε / 3)) (fun _ => Metric.isOpen_ball)
    (fun x (_ : x ∈ Icc (0 : ℝ) 1) =>
      mem_iUnion.mpr ⟨x, Metric.mem_ball_self (by linarith)⟩)
  have hf : ∀ x : ℝ, {J ∈ A | x ∈ J}.Finite := by
    intro x
    apply Set.Subsingleton.finite
    intro J hJ K hK
    by_contra hne
    exact Set.disjoint_left.mp (hdis hJ.1 hK.1 hne) hJ.2 hK.2
  refine (t.finite_toSet.biUnion (fun x _ => hf x)).subset ?_
  rintro J ⟨hJA, a, ha, b, hb, hab⟩
  have ha01 := hbound J hJA ha
  have hb01 := hbound J hJA hb
  have hm : (a + b) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [ha01.1, ha01.2, hb01.1, hb01.2]
  obtain ⟨x, hxt, hx⟩ := mem_iUnion₂.mp (ht hm)
  have hx' : |(a + b) / 2 - x| < ε / 3 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hx
  have hxlo := (abs_lt.mp hx').1
  have hxhi := (abs_lt.mp hx').2
  refine mem_iUnion₂.mpr ⟨x, hxt, hJA, (hA J hJA).out ha hb ?_⟩
  constructor <;> linarith

/-- A continuous curve sends disjoint parameter intervals in `[0,1]` to
sets of small diameter, apart from finitely many exceptions at each scale.
This is the size control needed for infinitely many excursions in VIII (6.2). -/
theorem finite_large_images_of_disjoint_intervals {Y : Type v} [PseudoMetricSpace Y]
    {f : ℝ → Y} (hf : ContinuousOn f (Icc 0 1)) {A : Set (Set ℝ)}
    (hA : ∀ J ∈ A, OrdConnected J) (hbound : ∀ J ∈ A, J ⊆ Icc 0 1)
    (hdis : A.PairwiseDisjoint id) {ε : ℝ} (hε : 0 < ε) :
    {J ∈ A | ∃ a ∈ J, ∃ b ∈ J, ε ≤ dist (f a) (f b)}.Finite := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  refine (finite_long_disjoint_intervals hA hbound hdis hδ).subset ?_
  rintro J ⟨hJA, a, ha, b, hb, hab⟩
  have hd : δ ≤ dist a b := by
    by_contra hlt
    exact (not_lt_of_ge hab) (hmod a (hbound J hJA ha) b
      (hbound J hJA hb) (lt_of_not_ge hlt))
  rcases le_total a b with hle | hle
  · exact ⟨hJA, a, ha, b, hb, by simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hle)] using hd⟩
  · exact ⟨hJA, b, hb, a, ha, by simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hle)] using hd⟩

/-- The same size bound holds for the closed parameter intervals, even
though adjacent intervals may share endpoints. This form controls complete
excursions, including their ends, in VIII (6.2). -/
theorem finite_large_images_of_disjoint_closed_intervals {Y : Type v} [PseudoMetricSpace Y]
    {ι : Type u} {a b : ι → ℝ} {f : ℝ → Y}
    (hf : ContinuousOn f (Icc 0 1))
    (hbound : ∀ i, 0 ≤ a i ∧ b i ≤ 1)
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    {ε : ℝ} (hε : 0 < ε) :
    {i | ∃ s ∈ Icc (a i) (b i), ∃ t ∈ Icc (a i) (b i),
      ε ≤ dist (f s) (f t)}.Finite := by
  classical
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  obtain ⟨q, hq⟩ := isCompact_Icc.elim_finite_subcover
    (fun x : ℝ => Metric.ball x (δ / 3)) (fun _ => Metric.isOpen_ball)
    (fun x (_ : x ∈ Icc (0 : ℝ) 1) =>
      mem_iUnion.mpr ⟨x, Metric.mem_ball_self (by linarith)⟩)
  have hfinite : ∀ x : ℝ, {i | x ∈ Ioo (a i) (b i)}.Finite := by
    intro x
    apply Set.Subsingleton.finite
    intro i hi j hj
    by_contra hne
    exact Set.disjoint_left.mp (hdis hne) hi hj
  refine (q.finite_toSet.biUnion (fun x _ => hfinite x)).subset ?_
  rintro i ⟨s, hs, t, ht, hdist⟩
  have hlen : δ ≤ b i - a i := by
    by_contra hn
    have hst : dist s t < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
    exact (not_lt_of_ge hdist) (hmod s ⟨(hbound i).1.trans hs.1,
      hs.2.trans (hbound i).2⟩ t ⟨(hbound i).1.trans ht.1,
      ht.2.trans (hbound i).2⟩ hst)
  have hm : (a i + b i) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [(hbound i).1, (hbound i).2]
  obtain ⟨x, hxq, hxm⟩ := mem_iUnion₂.mp (hq hm)
  have hxm' : |(a i + b i) / 2 - x| < δ / 3 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hxm
  have hxlo := (abs_lt.mp hxm').1
  have hxhi := (abs_lt.mp hxm').2
  exact mem_iUnion₂.mpr ⟨x, hxq, by constructor <;> linarith⟩

/-- Every nontrivial member of an interval family with finitely many large
members is contained in a maximal member. Indeed, all its containers share
one fixed positive lower bound on their lengths. This justifies selecting
outermost excursions in the infinite-crossing case of VIII (6.2). -/
theorem exists_maximal_member_of_finite_large_intervals {A : Set (Set ℝ)}
    (hfinite : ∀ ε > 0, {J ∈ A | ∃ a ∈ J, ∃ b ∈ J, ε ≤ b - a}.Finite)
    {I : Set ℝ} (hI : I ∈ A) (hne : I.Nontrivial) :
    ∃ J ∈ A, I ⊆ J ∧ ∀ K ∈ A, J ⊆ K → K = J := by
  obtain ⟨a, ha, b, hb, hab⟩ := hne
  have hex : ∃ a ∈ I, ∃ b ∈ I, a < b := by
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact ⟨a, ha, b, hb, hlt⟩
    · exact ⟨b, hb, a, ha, hgt⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hex
  let B : Set (Set ℝ) := {J ∈ A | I ⊆ J}
  have hB : B.Finite := (hfinite (b - a) (sub_pos.mpr hab)).subset
    (fun J hJ => ⟨hJ.1, a, hJ.2 ha, b, hJ.2 hb, le_rfl⟩)
  obtain ⟨J, hJ, hmax⟩ := hB.exists_maximal ⟨I, hI, subset_rfl⟩
  refine ⟨J, hJ.1, hJ.2, ?_⟩
  intro K hK hJK
  exact subset_antisymm (hmax ⟨hK, hJ.2.trans hJK⟩ hJK) hJK

/-- The inverse parameter of an arc is uniformly continuous. Thus endpoints
that remain far apart in its parameter cannot approach one another in the
surface. This transfers the excursion size bound between the two curves
in VIII (6.2). -/
theorem uniform_parameter_control_of_arc {Y : Type v} [MetricSpace Y]
    {f : unitInterval → Y} (hf : IsArcMap f) :
    ∀ ε > 0, ∃ δ > 0, ∀ s t, dist (f s) (f t) < δ → dist s t < ε := by
  let E := (hf.1.isClosedEmbedding hf.2).isEmbedding.toHomeomorph
  have : CompactSpace (range f) := isCompact_iff_compactSpace.mp (isCompact_range hf.1)
  have hu := CompactSpace.uniformContinuous_of_continuous E.symm.continuous
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  refine ⟨δ, hδ, ?_⟩
  intro s t hst
  have hdist : dist (E s) (E t) < δ := hst
  simpa only [Homeomorph.symm_apply_apply] using hmod hdist

/-- Disjoint excursions of one curve have only finitely many endpoint
pairs that span a long interval of another embedded arc. The intervals on
the other arc may be nested. This supplies the finite-container argument
for choosing outermost excursions in VIII (6.2). -/
theorem finite_large_matched_endpoint_intervals {Y : Type v} [MetricSpace Y]
    {ι : Type u} {a b : ι → ℝ} {q : ℝ → Y} {f : unitInterval → Y}
    (hq : ContinuousOn q (Icc 0 1)) (hf : IsArcMap f)
    (hbound : ∀ i, 0 ≤ a i ∧ a i ≤ b i ∧ b i ≤ 1)
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (s t : ι → unitInterval) (hs : ∀ i, f (s i) = q (a i))
    (ht : ∀ i, f (t i) = q (b i)) {ε : ℝ} (hε : 0 < ε) :
    {i | ε ≤ dist (s i) (t i)}.Finite := by
  obtain ⟨δ, hδ, hmod⟩ := uniform_parameter_control_of_arc hf ε hε
  refine (finite_large_images_of_disjoint_closed_intervals hq
    (fun i => ⟨(hbound i).1, (hbound i).2.2⟩) hdis hδ).subset ?_
  intro i hi
  refine ⟨a i, ⟨le_rfl, (hbound i).2.1⟩, b i,
    ⟨(hbound i).2.1, le_rfl⟩, ?_⟩
  apply le_of_not_gt
  intro hlt
  have hnear : dist (f (s i)) (f (t i)) < δ := by rwa [hs i, ht i]
  exact (not_lt_of_ge hi) (hmod (s i) (t i) hnear)

/-- Pairwise disjoint connected subsets of the parameter interval have
only finitely many large images under a continuous map. This version does
not require choosing endpoints for the individual subsets. -/
theorem finite_large_images_of_disjoint_preconnected_subsets_unitInterval
    {Y : Type v} [PseudoMetricSpace Y] {f : unitInterval → Y} (hf : Continuous f)
    {A : Set (Set unitInterval)} (hA : ∀ J ∈ A, IsPreconnected J)
    (hdis : A.PairwiseDisjoint id) {ε : ℝ} (hε : 0 < ε) :
    {J ∈ A | ∃ s ∈ J, ∃ t ∈ J, ε ≤ dist (f s) (f t)}.Finite := by
  classical
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hf) ε hε
  obtain ⟨q, hq⟩ := isCompact_univ.elim_finite_subcover
    (fun x : unitInterval => Metric.ball x (δ / 3)) (fun _ => Metric.isOpen_ball)
    (fun x _ => mem_iUnion.mpr ⟨x, Metric.mem_ball_self (by linarith)⟩)
  have hfinite : ∀ x : unitInterval, {J ∈ A | x ∈ J}.Finite := by
    intro x
    apply Set.Subsingleton.finite
    intro J hJ K hK
    by_contra hne
    exact Set.disjoint_left.mp (hdis hJ.1 hK.1 hne) hJ.2 hK.2
  refine (q.finite_toSet.biUnion (fun x _ => hfinite x)).subset ?_
  rintro J ⟨hJA, s, hs, t, ht, hdist⟩
  have hd : δ ≤ dist s t := by
    apply le_of_not_gt
    intro hlt
    exact (not_lt_of_ge hdist) (hmod hlt)
  have hex : ∃ s ∈ J, ∃ t ∈ J, δ ≤ t.1 - s.1 := by
    change δ ≤ |s.1 - t.1| at hd
    rcases le_total s t with hst | hts
    · exact ⟨s, hs, t, ht, by simpa [abs_of_nonpos (sub_nonpos.mpr (show s.1 ≤ t.1 from hst))] using hd⟩
    · exact ⟨t, ht, s, hs, by simpa [abs_of_nonneg (sub_nonneg.mpr (show t.1 ≤ s.1 from hts))] using hd⟩
  obtain ⟨s, hs, t, ht, hlen⟩ := hex
  let m : unitInterval := ⟨(s.1 + t.1) / 2, by
    constructor <;> linarith [s.2.1, s.2.2, t.2.1, t.2.2]⟩
  obtain ⟨x, hxq, hxm⟩ := mem_iUnion₂.mp (hq (mem_univ m))
  have hxm' : |(s.1 + t.1) / 2 - x.1| < δ / 3 := hxm
  have hxlo := (abs_lt.mp hxm').1
  have hxhi := (abs_lt.mp hxm').2
  have hxJ : x ∈ J := (hA J hJA).ordConnected.out hs ht
    ⟨by change s.1 ≤ x.1; linarith, by change x.1 ≤ t.1; linarith⟩
  exact mem_iUnion₂.mpr ⟨x, hxq, hJA, hxJ⟩

/-- Disjoint connected subsets of an embedded arc have only finitely many
large members. Pulling them back to the parameter interval reduces this
to the interval size bound. -/
theorem finite_large_disjoint_preconnected_subsets_of_arc
    {Y : Type v} [MetricSpace Y] {f : unitInterval → Y} (hf : IsArcMap f)
    {A : Set (Set Y)} (hA : ∀ J ∈ A, IsPreconnected J)
    (hsub : ∀ J ∈ A, J ⊆ range f) (hdis : A.PairwiseDisjoint id)
    {ε : ℝ} (hε : 0 < ε) :
    {J ∈ A | ∃ x ∈ J, ∃ y ∈ J, ε ≤ dist x y}.Finite := by
  let P : Set Y → Set unitInterval := fun J => f ⁻¹' J
  have hemb := (hf.1.isClosedEmbedding hf.2).isEmbedding
  have hpre : ∀ J ∈ P '' A, IsPreconnected J := by
    rintro _ ⟨J, hJA, rfl⟩
    rw [← hemb.isInducing.isPreconnected_image,
      image_preimage_eq_of_subset (hsub J hJA)]
    exact hA J hJA
  have hpair : (P '' A).PairwiseDisjoint id := by
    rintro _ ⟨J, hJA, rfl⟩ _ ⟨K, hKA, rfl⟩ hne
    have hJK : J ≠ K := fun he => hne (congrArg P he)
    exact (hdis hJA hKA hJK).preimage f
  have hfinite := finite_large_images_of_disjoint_preconnected_subsets_unitInterval
    hf.1 hpre hpair hε
  have hfinimage : (P '' {J ∈ A | ∃ x ∈ J, ∃ y ∈ J, ε ≤ dist x y}).Finite := by
    apply hfinite.subset
    rintro _ ⟨J, ⟨hJA, x, hx, y, hy, hdist⟩, rfl⟩
    obtain ⟨s, rfl⟩ := hsub J hJA hx
    obtain ⟨t, rfl⟩ := hsub J hJA hy
    exact ⟨⟨J, hJA, rfl⟩, s, hx, t, hy, hdist⟩
  apply hfinimage.of_finite_image
  intro J hJ K hK he
  calc
    J = f '' (P J) := (image_preimage_eq_of_subset (hsub J hJ.1)).symm
    _ = f '' (P K) := congrArg (fun Q => f '' Q) he
    _ = K := image_preimage_eq_of_subset (hsub K hK.1)

/-- If each member of a family has only finitely many containers in that
family, every member lies in a maximal member. For VIII (6.2), positive
endpoint spans and the excursion size bound make these container sets
finite. -/
theorem exists_maximal_superset_of_finite_containers {X : Type u} {A : Set (Set X)}
    (hfinite : ∀ D ∈ A, {E ∈ A | D ⊆ E}.Finite) {D : Set X} (hD : D ∈ A) :
    ∃ E ∈ A, D ⊆ E ∧ ∀ F ∈ A, E ⊆ F → F = E := by
  obtain ⟨E, hE, hmax⟩ := (hfinite D hD).exists_maximal ⟨D, hD, subset_rfl⟩
  refine ⟨E, hE.1, hE.2, ?_⟩
  intro F hF hEF
  exact subset_antisymm (hmax ⟨hF, hE.2.trans hEF⟩ hEF) hEF

/-- The removed boundary parts of distinct maximal excursion discs are
disjoint once the two-disc comparison has been proved. -/
theorem maximal_members_pairwise_disjoint_on {X : Type u} {Z : Type v}
    {A : Set (Set X)} (r : Set X → Set Z)
    (hcompare : ∀ E ∈ A, ∀ F ∈ A, E ⊆ F ∨ F ⊆ E ∨ Disjoint (r E) (r F)) :
    {E ∈ A | ∀ F ∈ A, E ⊆ F → F = E}.PairwiseDisjoint r := by
  intro E hE F hF hne
  rcases hcompare E hE.1 F hF.1 with hEF | hFE | hdis
  · exact False.elim (hne (hE.2 F hF.1 hEF).symm)
  · exact False.elim (hne (hF.2 E hE.1 hFE))
  · exact hdis

/-- A nonempty open connected portion of the parameter interval is one
open interval, with its two endpoints giving its closure. This supplies
endpoint parameters for the removed boundary arcs in VIII (6.2). -/
theorem exists_endpoints_of_open_preconnected_subset_unitInterval
    {J : Set ℝ} (hJ : IsOpen J) (hpre : IsPreconnected J) (hne : J.Nonempty)
    (hsub : J ⊆ Icc 0 1) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ J = Ioo a b ∧ closure J = Icc a b := by
  have hb : BddBelow J := ⟨0, fun x hx => (hsub hx).1⟩
  have ha : BddAbove J := ⟨1, fun x hx => (hsub hx).2⟩
  have hinside : Ioo (sInf J) (sSup J) ⊆ J :=
    (show IsConnected J from ⟨hne, hpre⟩).Ioo_csInf_csSup_subset hb ha
  have hout : J ⊆ Ioo (sInf J) (sSup J) := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hJ x hx
    have hym : x - ε / 2 ∈ J := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith)]
      linarith
    have hyp : x + ε / 2 ∈ J := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith
    have hlo := csInf_le hb hym
    have hhi := le_csSup ha hyp
    constructor <;> linarith
  obtain ⟨x, hx⟩ := hne
  have hab : sInf J < sSup J := (hout hx).1.trans (hout hx).2
  have heq : J = Ioo (sInf J) (sSup J) := subset_antisymm hout hinside
  refine ⟨sInf J, sSup J, le_csInf ⟨x, hx⟩ (fun y hy => (hsub hy).1),
    hab, csSup_le ⟨x, hx⟩ (fun y hy => (hsub hy).2), heq, ?_⟩
  exact (congrArg closure heq).trans (closure_Ioo hab.ne)

/-- If disc inclusion implies inclusion of the removed parameter intervals,
the excursion size bound makes each set of containers finite. Two fixed
interior parameters of the smaller interval give a positive lower length
bound for every container. -/
theorem finite_containers_of_interval_witnesses {X : Type u} {ι : Type v}
    (R : ι → Set X) (a b : ι → ℝ) (hab : ∀ i, a i < b i)
    (hfinite : ∀ ε > 0, {i | ε ≤ b i - a i}.Finite)
    (hmono : ∀ i j, R i ⊆ R j → Ioo (a i) (b i) ⊆ Ioo (a j) (b j))
    (i : ι) : {j | R i ⊆ R j}.Finite := by
  have hpos : 0 < (b i - a i) / 2 := half_pos (sub_pos.mpr (hab i))
  refine (hfinite ((b i - a i) / 2) hpos).subset ?_
  intro j hij
  have hu := hmono i j hij (show (3 * a i + b i) / 4 ∈ Ioo (a i) (b i) by
    constructor <;> linarith [hab i])
  have hv := hmono i j hij (show (a i + 3 * b i) / 4 ∈ Ioo (a i) (b i) by
    constructor <;> linarith [hab i])
  change (b i - a i) / 2 ≤ b j - a j
  linarith [hu.1, hv.2]

/-- Every excursion disc is contained in a maximal one when the removed
intervals are monotone under disc inclusion and have finitely many large
members. Maximality concerns the discs themselves, so repeated indices do
not create a false strict inclusion. -/
theorem exists_maximal_region_of_interval_witnesses {X : Type u} {ι : Type v}
    (R : ι → Set X) (a b : ι → ℝ) (hab : ∀ i, a i < b i)
    (hfinite : ∀ ε > 0, {i | ε ≤ b i - a i}.Finite)
    (hmono : ∀ i j, R i ⊆ R j → Ioo (a i) (b i) ⊆ Ioo (a j) (b j))
    (i : ι) : ∃ j, R i ⊆ R j ∧ ∀ k, R j ⊆ R k → R k = R j := by
  have hcontainers : ∀ D ∈ range R, {E ∈ range R | D ⊆ E}.Finite := by
    rintro _ ⟨j, rfl⟩
    refine ((finite_containers_of_interval_witnesses R a b hab hfinite hmono j).image R).subset ?_
    rintro E ⟨⟨k, rfl⟩, hsub⟩
    exact ⟨k, hsub, rfl⟩
  obtain ⟨E, ⟨j, rfl⟩, hij, hmax⟩ :=
    exists_maximal_superset_of_finite_containers hcontainers (mem_range_self i)
  exact ⟨j, hij, fun k hk => hmax (R k) (mem_range_self k) hk⟩

end GraphMinor.GM08
