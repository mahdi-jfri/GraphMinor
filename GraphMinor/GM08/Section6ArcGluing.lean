module

public import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.ArcTools
import GraphMinor.GM08.Section6Gluing
import GraphMinor.GM08.Section6Reparam

/-!
# Gluing disjoint outside excursions into an embedded arc

The maximal excursion discs in VIII (6.2), page 264, remove disjoint
intervals of one old boundary arc. This file glues their reparametrized
excursions into that arc. The null-family bound proves continuity, and
disjointness of the open excursions proves injectivity.
-/

public section

namespace GraphMinor.GM08

open Set Topology Surface

universe u v

local notation "𝕀" => unitInterval

/-- Replacing disjoint parameter intervals by a null family of disjoint
embedded excursions gives an embedded arc with the original endpoints.
Each complete excursion is retained, and every interior point comes from
the old open arc or an open excursion. -/
theorem exists_arc_gluing_disjoint_excursions {Y : Type u} [MetricSpace Y]
    {ι : Type v} {f : 𝕀 → Y} (hf : IsArcMap f) (s t : ι → 𝕀)
    (hst : ∀ i, s i < t i)
    (hintervals : Pairwise (fun i j => Disjoint (Ioo (s i).1 (t i).1) (Ioo (s j).1 (t j).1)))
    (ℓ : ι → 𝕀 → Y) (hℓ : ∀ i, IsArcMap (ℓ i))
    (h0 : ∀ i, ℓ i 0 = f (s i)) (h1 : ∀ i, ℓ i 1 = f (t i))
    (havoid : ∀ i, Disjoint (ℓ i '' Ioo (0 : 𝕀) 1) (range f))
    (hpair : Pairwise (fun i j => Disjoint (ℓ i '' Ioo (0 : 𝕀) 1) (ℓ j '' Ioo (0 : 𝕀) 1)))
    (hsmall : ∀ ε > 0, {i | ∃ u v, ε ≤ dist (ℓ i u) (ℓ i v)}.Finite) :
    ∃ g : 𝕀 → Y, IsArcMap g ∧ g 0 = f 0 ∧ g 1 = f 1 ∧
      (∀ i, range (ℓ i) ⊆ range g) ∧
      g '' Ioo (0 : 𝕀) 1 ⊆ f '' Ioo (0 : 𝕀) 1 ∪ ⋃ i, ℓ i '' Ioo (0 : 𝕀) 1 := by
  classical
  choose p hpc hpa hpb hpinj hpic hpio using fun i =>
    exists_interval_arc_reparametrization (hℓ i) (show (s i).1 < (t i).1 from hst i)
  have hpavoid : ∀ i, Disjoint (p i '' Ioo (s i).1 (t i).1)
      ((extI f) '' Icc (0 : ℝ) 1) := by
    intro i
    rw [hpio i]
    apply Set.disjoint_left.mpr
    rintro y hy ⟨x, _, he⟩
    exact Set.disjoint_left.mp (havoid i) hy ⟨_, he⟩
  have hppair : Pairwise (fun i j => Disjoint (p i '' Ioo (s i).1 (t i).1)
      (p j '' Ioo (s j).1 (t j).1)) := by
    intro i j hij
    rw [hpio i, hpio j]
    exact hpair hij
  have hpnull : ∀ ε > 0,
      {i | ∃ x ∈ Icc (s i).1 (t i).1, ∃ y ∈ Icc (s i).1 (t i).1,
        ε ≤ dist (p i x) (p i y)}.Finite := by
    intro ε hε
    refine (hsmall ε hε).subset ?_
    rintro i ⟨x, hx, y, hy, hdist⟩
    obtain ⟨u, hu⟩ : p i x ∈ range (ℓ i) := hpic i ▸ ⟨x, hx, rfl⟩
    obtain ⟨v, hv⟩ : p i y ∈ range (ℓ i) := hpic i ▸ ⟨y, hy, rfl⟩
    exact ⟨u, v, by rwa [hu, hv]⟩
  obtain ⟨G, hGc, hGp, hGb⟩ := exists_continuous_interval_replacement
    (continuous_extI hf.1) (fun i => show (s i).1 < (t i).1 from hst i) hintervals p
    (fun i => (hpc i).continuousOn)
    (fun i => (hpa i).trans ((h0 i).trans (extI_coe f (s i)).symm))
    (fun i => (hpb i).trans ((h1 i).trans (extI_coe f (t i)).symm)) hpnull
  have hGinj : InjOn G (Icc (0 : ℝ) 1) := injOn_interval_replacement
    (extI_injOn hf.2) (fun i => (hpinj i).mono Ioo_subset_Icc_self) hpavoid hppair
    (fun i x hx => hGp i x ⟨hx.1.le, hx.2.le⟩) (fun x _ hx => hGb x hx)
  let g : 𝕀 → Y := fun x => G x.1
  have hg : IsArcMap g := ⟨hGc.comp continuous_subtype_val,
    fun x y he => Subtype.ext (hGinj x.2 y.2 he)⟩
  have hnot0 : ∀ i, (0 : ℝ) ∉ Ioo (s i).1 (t i).1 :=
    fun i h => (not_lt_of_ge (s i).2.1) h.1
  have hnot1 : ∀ i, (1 : ℝ) ∉ Ioo (s i).1 (t i).1 :=
    fun i h => (not_lt_of_ge (t i).2.2) h.2
  refine ⟨g, hg, (hGb 0 hnot0).trans (extI_coe f 0),
    (hGb 1 hnot1).trans (extI_coe f 1), ?_, ?_⟩
  · intro i
    rintro _ ⟨u, rfl⟩
    obtain ⟨x, hx, he⟩ : ℓ i u ∈ p i '' Icc (s i).1 (t i).1 :=
      (hpic i).symm ▸ mem_range_self u
    let v : 𝕀 := ⟨x, (s i).2.1.trans hx.1, hx.2.trans (t i).2.2⟩
    exact ⟨v, (hGp i x hx).trans he⟩
  · rintro _ ⟨x, hx, rfl⟩
    by_cases hi : ∃ i, x.1 ∈ Ioo (s i).1 (t i).1
    · obtain ⟨i, hi⟩ := hi
      right
      apply mem_iUnion.mpr
      refine ⟨i, ?_⟩
      have hpx : p i x.1 ∈ ℓ i '' Ioo (0 : 𝕀) 1 := hpio i ▸ ⟨x.1, hi, rfl⟩
      change G x.1 ∈ ℓ i '' Ioo (0 : 𝕀) 1
      rw [hGp i x.1 ⟨hi.1.le, hi.2.le⟩]
      exact hpx
    · left
      exact ⟨x, hx, ((hGb x.1 (not_exists.mp hi)).trans (extI_coe f x)).symm⟩

/-- The retained arc and the glued complementary arc still meet only at
their two endpoints. Open excursions avoid the retained arc, while the
unchanged portions obey the original two-arc intersection property. -/
theorem two_arcs_of_glued_excursions {Y : Type u} [TopologicalSpace Y]
    {ι : Type v} {q f g : 𝕀 → Y} (hqf : IsTwoArcs q f) (hg : IsArcMap g)
    (hg0 : g 0 = f 0) (hg1 : g 1 = f 1) (ℓ : ι → 𝕀 → Y)
    (hopen : g '' Ioo (0 : 𝕀) 1 ⊆ f '' Ioo (0 : 𝕀) 1 ∪ ⋃ i, ℓ i '' Ioo (0 : 𝕀) 1)
    (havoid : ∀ i, Disjoint (ℓ i '' Ioo (0 : 𝕀) 1) (range q)) : IsTwoArcs q g := by
  refine ⟨hqf.1, hg, hg0.trans hqf.3, hg1.trans hqf.4, ?_⟩
  intro s t he
  by_cases ht0 : t = 0
  · subst t
    exact Or.inl ⟨hqf.1.2 (he.trans (hg0.trans hqf.3)), rfl⟩
  by_cases ht1 : t = 1
  · subst t
    exact Or.inr ⟨hqf.1.2 (he.trans (hg1.trans hqf.4)), rfl⟩
  have ht : t ∈ Ioo (0 : 𝕀) 1 :=
    ⟨lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht0),
      lt_of_le_of_ne (unitInterval.le_one t) ht1⟩
  rcases hopen ⟨t, ht, rfl⟩ with ⟨r, hr, hre⟩ | hexc
  · rcases hqf.5 s r (he.trans hre.symm) with h | h
    · exact False.elim ((ne_of_gt hr.1) h.2)
    · exact False.elim ((ne_of_lt hr.2) h.2)
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hexc
    exact False.elim (Set.disjoint_left.mp (havoid i) hi ⟨s, he⟩)

end GraphMinor.GM08
