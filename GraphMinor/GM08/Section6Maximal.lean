module

public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM08.Section6Family
import GraphMinor.GM08.Section6Selection
import GraphMinor.GM08.Section6Chord
import GraphMinor.GM08.Section6Parameters
import GraphMinor.GM08.Section6Excursions
import GraphMinor.GM08.Section6ExcursionArcs

/-!
# The maximal excursions used to build the outer boundary

For VIII (6.2), page 264, every excursion enlargement lies in a maximal
one. Distinct maximal enlargements remove disjoint old boundary intervals.
This file orients their excursions to match those intervals and retains
the null-family bound and coverage of the second curve.
-/

public section

namespace GraphMinor.GM08

open Set Topology Metric Surface

local notation "𝕀" => unitInterval

/-- Select and orient the maximal excursions in the non-nested case of
VIII (6.2). Their disjoint intervals and null images are the inputs to the
embedded-arc gluing theorem, and their enlarged discs cover the second
curve together with the old disc. -/
theorem exists_maximal_plane_excursions {D F : Set ℂ} (hD : IsClosedDisc D)
    (hF : IsOArc F) (hinter : (discBd D ∩ F).Nontrivial)
    (hDu : D ⊆ closedBall 0 1) (hFu : F ⊆ closedBall 0 1)
    (hnot : ¬ D ⊆ closedInner F) :
    ∃ q f : 𝕀 → ℂ, ∃ p : ℂ,
      IsTwoArcs q f ∧ range q ∪ range f = discBd D ∧ p ∈ q '' Ioo (0 : 𝕀) 1 ∧
      p ∈ closure (connectedComponentIn ((D ∪ closedInner F)ᶜ) (2 : ℂ)) ∧
      ∃ (K : Type) (ℓ : K → 𝕀 → ℂ) (R : K → Set ℂ) (s t : K → 𝕀),
        (∀ i, IsArcMap (ℓ i)) ∧ (∀ i, s i < t i) ∧
        Pairwise (fun i j => Disjoint (Ioo (s i).1 (t i).1) (Ioo (s j).1 (t j).1)) ∧
        (∀ i, ℓ i 0 = f (s i)) ∧ (∀ i, ℓ i 1 = f (t i)) ∧
        (∀ i, range (ℓ i) ⊆ F) ∧
        (∀ i, ℓ i '' Ioo (0 : 𝕀) 1 ⊆ Dᶜ) ∧
        Pairwise (fun i j => Disjoint (ℓ i '' Ioo (0 : 𝕀) 1) (ℓ j '' Ioo (0 : 𝕀) 1)) ∧
        (∀ ε > 0, {i | ∃ u v, ε ≤ dist (ℓ i u) (ℓ i v)}.Finite) ∧
        (∀ i, IsClosedDisc (R i)) ∧ (∀ i, D ⊆ R i) ∧
        (∀ i, R i ⊆ closedBall 0 1) ∧
        (∀ i, discBd (R i) ⊆ D ∪ range (ℓ i)) ∧ F ⊆ D ∪ ⋃ i, R i := by
  classical
  let I := {J : Set ℂ // J ∈ componentsIn (F \ D)}
  obtain ⟨q, f, p, hqf, hqfr, _, hpq, hpcl, R, ℓ, a, b, s, t, hdata⟩ :=
    exists_plane_excursion_parameter_family hD hF hinter hDu hFu hnot
  simp only [forall_and] at hdata
  rcases hdata with ⟨hℓ, hℓF, hℓo, hℓr, hR, hDR, hRu, hab, ha0, ha1, har, hRb,
    hst, hP, _, hend⟩
  have haD : ∀ J, range (a J) ⊆ D := fun J =>
    (har J ▸ subset_union_left).trans (discBd_subset D)
  have hℓ0D : ∀ J, ℓ J 0 ∈ D := fun J => ha0 J ▸ haD J ⟨0, rfl⟩
  have hℓ1D : ∀ J, ℓ J 1 ∈ D := fun J => ha1 J ▸ haD J ⟨1, rfl⟩
  have hJD : ∀ J : I, J.1 ⊆ Dᶜ := by
    rintro ⟨J, x, hx, rfl⟩
    exact (connectedComponentIn_subset (F \ D) x).trans (fun _ h => h.2)
  have hdiff : ∀ J : I, discBd (R J) \ D = J.1 := fun J =>
    enlarged_boundary_sdiff_old_disc_eq_excursion (hRb J) (haD J)
      (hℓ0D J) (hℓ1D J) (hℓo J) (hJD J)
  have hRinj : Function.Injective R := by
    intro i j he
    apply Subtype.ext
    calc
      i.1 = discBd (R i) \ D := (hdiff i).symm
      _ = discBd (R j) \ D := congrArg (fun E => discBd E \ D) he
      _ = j.1 := hdiff j
  have hscl : ∀ J : I, f (s J) ∈ closure J.1 := by
    intro J
    have hx : f (s J) ∈ ({f (s J), f (t J)} : Set ℂ) := Or.inl rfl
    rw [hend J] at hx
    rw [← hℓr J]
    rcases hx with he | he
    · exact ⟨0, he.symm⟩
    · exact ⟨1, he.symm⟩
  have htcl : ∀ J : I, f (t J) ∈ closure J.1 := by
    intro J
    have hx : f (t J) ∈ ({f (s J), f (t J)} : Set ℂ) := Or.inr rfl
    rw [hend J] at hx
    rw [← hℓr J]
    rcases hx with he | he
    · exact ⟨0, he.symm⟩
    · exact ⟨1, he.symm⟩
  obtain ⟨_, hmax⟩ := excursion_enlargements_have_finite_containers_and_maxima
    hF hqf.2 R s t hR hst hP hscl htcl
  let M : Set I := {i | ∀ j, R i ⊆ R j → R j = R i}
  have hcompare := plane_excursion_enlargements_nested_or_removed_disjoint hD R ℓ a b
    hR hDR hRu hℓ hℓo hab ha0 ha1 har hRb
  have hintervals : Pairwise (fun i j : M =>
      Disjoint (Ioo (s i.1).1 (t i.1).1) (Ioo (s j.1).1 (t j.1).1)) := by
    intro i j hij
    have hij' : i.1 ≠ j.1 := fun he => hij (Subtype.ext he)
    rcases hcompare i.1 j.1 with h | h | hd
    · exact False.elim (hij' (hRinj (i.2 j.1 h).symm))
    · exact False.elim (hij' (hRinj (j.2 i.1 h)))
    · apply Set.disjoint_left.mpr
      intro x hxi hxj
      let u : 𝕀 := ⟨x, (s i.1).2.1.trans hxi.1.le, hxi.2.le.trans (t i.1).2.2⟩
      have hiP : f u ∈ discInt (R i.1) ∩ discBd D := by
        rw [hP i.1]
        exact ⟨u, hxi, rfl⟩
      have hjP : f u ∈ discInt (R j.1) ∩ discBd D := by
        rw [hP j.1]
        exact ⟨u, hxj, rfl⟩
      exact Set.disjoint_left.mp hd ⟨hiP.2, hiP.1⟩ ⟨hjP.2, hjP.1⟩
  choose o ho ho0 ho1 hor hoo using fun J => exists_oriented_arc_with_same_images
    (hℓ J) (fun he => (hst J).ne (hqf.2.2 he)) (hend J)
  have hoF : ∀ J, range (o J) ⊆ F := fun J => hor J ▸ hℓF J
  have hoJ : ∀ J, o J '' Ioo (0 : 𝕀) 1 = J.1 := fun J => (hoo J).trans (hℓo J)
  have hpair : Pairwise (fun i j : M => Disjoint (o i.1 '' Ioo (0 : 𝕀) 1)
      (o j.1 '' Ioo (0 : 𝕀) 1)) := by
    intro i j hij
    have hij' : i.1.1 ≠ j.1.1 := fun he => hij (Subtype.ext (Subtype.ext he))
    have hd := open_excursion_disjoint_complete_other i.1.2 j.1.2 hij'
      (hℓo i.1) (hℓo j.1) (hℓ0D j.1) (hℓ1D j.1)
    rw [hoJ i.1, hoJ j.1]
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact Set.disjoint_left.mp hd ((hℓo i.1).symm ▸ hxi)
      ((image_subset_range _ _) ((hℓo j.1).symm ▸ hxj))
  have hsmall : ∀ ε > 0, {i : M | ∃ u v, ε ≤ dist (o i.1 u) (o i.1 v)}.Finite := by
    intro ε hε
    have hfinite := finite_large_closures_of_excursion_components hF D hε
    have hinj : Function.Injective (fun J : M => J.1.1) :=
      Subtype.val_injective.comp Subtype.val_injective
    refine (hfinite.preimage_embedding ⟨_, hinj⟩).subset ?_
    rintro J ⟨u, v, hdist⟩
    have hru : o J.1 u ∈ closure J.1.1 := (hor J.1).trans (hℓr J.1) ▸ mem_range_self u
    have hrv : o J.1 v ∈ closure J.1.1 := (hor J.1).trans (hℓr J.1) ▸ mem_range_self v
    exact ⟨J.1.2, o J.1 u, hru, o J.1 v, hrv, hdist⟩
  have hbd : ∀ J, discBd (R J) ⊆ D ∪ range (o J) := by
    intro J
    rw [hRb J, hor J]
    exact union_subset_union (haD J) subset_rfl
  have hcover : F ⊆ D ∪ ⋃ J : M, R J.1 := by
    intro x hxF
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    let J : I := ⟨connectedComponentIn (F \ D) x, ⟨x, ⟨hxF, hxD⟩, rfl⟩⟩
    have hxJ : x ∈ J.1 := mem_connectedComponentIn ⟨hxF, hxD⟩
    have hxR : x ∈ R J := discBd_subset (R J)
      (hRb J ▸ Or.inr ((image_subset_range _ _) ((hℓo J).symm ▸ hxJ)))
    obtain ⟨j, hJj, hj⟩ := hmax J
    exact Or.inr (mem_iUnion.mpr ⟨⟨j, hj⟩, hJj hxR⟩)
  exact ⟨q, f, p, hqf, hqfr, hpq, hpcl, M, (fun J => o J.1), (fun J => R J.1),
    (fun J => s J.1), (fun J => t J.1), (fun J => ho J.1), (fun J => hst J.1),
    hintervals, (fun J => ho0 J.1), (fun J => ho1 J.1), (fun J => hoF J.1),
    (fun J => (hoJ J.1).symm ▸ hJD J.1), hpair, hsmall,
    (fun J => hR J.1), (fun J => hDR J.1), (fun J => hRu J.1), (fun J => hbd J.1), hcover⟩

end GraphMinor.GM08
