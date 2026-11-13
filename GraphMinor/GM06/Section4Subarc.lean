module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.PushOff
import GraphMinor.Surface.PlaneDisc
import GraphMinor.Surface.Collar

/-!
# Subarcs inside a closed cuff interval

A line in a cuff has two complementary open arcs between its ends. If
that line lies in a larger cuff interval, only its own open arc is
contained in the larger interval. Thus the closure of `cuffSubArc` is the
line itself. This identifies the subcurves used in VI (4.2), claim (1).
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

universe u

private theorem not_oArc_subset_line {S : Type u} [TopologicalSpace S]
    {C K : Set S} (hC : IsOArc C) (hK : IsLine K) (hCK : C ⊆ K) : False := by
  obtain ⟨φ⟩ := hC
  obtain ⟨e⟩ := hK
  let j : Circle → K := fun w => ⟨(φ w).1, hCK (φ w).2⟩
  have hj : Continuous j := by dsimp [j]; fun_prop
  have hji : Function.Injective j := by
    intro w z h
    exact φ.injective (Subtype.ext (congrArg (fun p : K => (p : S)) h))
  exact not_injective_circle_real
    ((continuous_subtype_val.comp e.symm.continuous).comp hj)
    (Subtype.val_injective.comp (e.symm.injective.comp hji))

private theorem closure_open_arc {S : Type u} [TopologicalSpace S] [T2Space S]
    {a : unitInterval → S} (ha : IsArcMap a) :
    closure (a '' Ioo 0 1) = range a := by
  rw [(ha.1.isClosedEmbedding ha.2).closure_image_eq,
    closure_Ioo (show (0 : unitInterval) ≠ 1 from zero_ne_one)]
  have hu : Icc (0 : unitInterval) 1 = univ := by
    ext x
    exact iff_true_intro ⟨x.2.1, x.2.2⟩
  rw [hu, image_univ]

private theorem arc_range_sdiff {S : Type u} [TopologicalSpace S]
    {a : unitInterval → S} (ha : IsArcMap a) :
    range a \ {a 0, a 1} = a '' Ioo 0 1 := by
  ext z
  constructor
  · rintro ⟨⟨t, rfl⟩, hz⟩
    refine ⟨t, ⟨?_, ?_⟩, rfl⟩
    · exact bot_lt_iff_ne_bot.mpr (fun h => hz (Or.inl (congrArg a h)))
    · exact lt_top_iff_ne_top.mpr (fun h => hz (Or.inr (congrArg a h)))
  · rintro ⟨t, ht, rfl⟩
    refine ⟨mem_range_self t, ?_⟩
    rintro (h | h)
    · exact (ne_of_gt ht.1) (ha.2 h)
    · exact (ne_of_lt ht.2) (ha.2 h)

/-- The two open arcs of a two-arc decomposition are precisely the
components obtained by removing their common ends. -/
theorem componentsIn_sdiff_pair_of_two_arcs
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C : Set S} {a b : unitInterval → S} (hab : IsTwoArcs a b)
    (hun : range a ∪ range b = C) :
    componentsIn (C \ {a 0, a 1}) = {a '' Ioo 0 1, b '' Ioo 0 1} := by
  let A := a '' Ioo 0 1
  let B := b '' Ioo 0 1
  have hAB : A ∪ B = C \ {a 0, a 1} := by
    change (a '' Ioo 0 1) ∪ (b '' Ioo 0 1) = _
    rw [← arc_range_sdiff hab.1,
      ← arc_range_sdiff hab.2, hab.3, hab.4, ← union_sdiff_distrib, hun]
  have hdisj₁ : Disjoint (closure A) B := by
    rw [closure_open_arc hab.1]
    refine disjoint_left.mpr ?_
    rintro z ⟨s, rfl⟩ ⟨t, ht, he⟩
    rcases hab.5 s t he.symm with h | h
    · exact (ne_of_gt ht.1) h.2
    · exact (ne_of_lt ht.2) h.2
  have hdisj₂ : Disjoint A (closure B) := by
    rw [closure_open_arc hab.2]
    refine disjoint_left.mpr ?_
    rintro z ⟨s, hs, rfl⟩ ⟨t, he⟩
    rcases hab.5 s t he.symm with h | h
    · exact (ne_of_gt hs.1) h.1
    · exact (ne_of_lt hs.2) h.1
  have hAn : A.Nonempty := by
    obtain ⟨t, ht0, ht1⟩ := exists_between (show (0 : unitInterval) < 1 from zero_lt_one)
    exact ⟨a t, t, ⟨ht0, ht1⟩, rfl⟩
  have hBn : B.Nonempty := by
    obtain ⟨t, ht0, ht1⟩ := exists_between (show (0 : unitInterval) < 1 from zero_lt_one)
    exact ⟨b t, t, ⟨ht0, ht1⟩, rfl⟩
  rw [← hAB]
  exact componentsIn_union_eq_pair
    (isPreconnected_Ioo.image a hab.1.1.continuousOn)
    (isPreconnected_Ioo.image b hab.2.1.continuousOn) hAn hBn hdisj₁ hdisj₂

/-- A line in a cuff has a complementary arc with the same ends. -/
theorem exists_complementary_arc_of_line
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C L : Set S} {c d : S} (hC : IsOArc C)
    (hL : IsLineWithEnds L c d) (hLC : L ⊆ C) :
    ∃ a b : unitInterval → S, IsTwoArcs a b ∧ range a = L ∧
      a 0 = c ∧ a 1 = d ∧ range a ∪ range b = C ∧ C \ L = b '' Ioo 0 1 := by
  obtain ⟨a, b, hab, haL, ha0, ha1, hun⟩ := exists_arcs_of_line hC hL hLC
  have hCL : C \ L = b '' Ioo 0 1 := by
    ext z
    constructor
    · rintro ⟨hzC, hzL⟩
      have hzU : z ∈ range a ∪ range b := hun ▸ hzC
      obtain ⟨t, rfl⟩ := hzU.resolve_left (by rwa [haL])
      refine ⟨t, ⟨?_, ?_⟩, rfl⟩
      · apply bot_lt_iff_ne_bot.mpr
        intro ht
        apply hzL
        rw [show t = 0 from ht, hab.3, ← haL]
        exact mem_range_self 0
      · apply lt_top_iff_ne_top.mpr
        intro ht
        apply hzL
        rw [show t = 1 from ht, hab.4, ← haL]
        exact mem_range_self 1
    · rintro ⟨t, ht, rfl⟩
      refine ⟨hun ▸ Or.inr (mem_range_self t), ?_⟩
      rw [← haL]
      rintro ⟨s, he⟩
      rcases hab.5 s t he with h | h
      · exact (ne_of_gt ht.1) h.2
      · exact (ne_of_lt ht.2) h.2
  exact ⟨a, b, hab, haL, ha0, ha1, hun, hCL⟩

/-- Removing a closed line from a cuff leaves the other open arc between
its ends. This gives the long cuff interval used in VI (4.2), claim (2). -/
theorem cuff_sdiff_line_mem_componentsIn
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C L : Set S} {c d : S} (hC : IsOArc C)
    (hL : IsLineWithEnds L c d) (hLC : L ⊆ C) :
    C \ L ∈ componentsIn (C \ {c, d}) := by
  obtain ⟨a, b, hab, _, ha0, ha1, hun, hCL⟩ :=
    exists_complementary_arc_of_line hC hL hLC
  rw [hCL, ← ha0, ← ha1, componentsIn_sdiff_pair_of_two_arcs hab hun]
  exact Or.inr rfl

/-- The closure of the complementary cuff arc meets the removed line
only at its ends. -/
theorem closure_cuff_sdiff_line_inter_subset_ends
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C L : Set S} {c d : S} (hC : IsOArc C)
    (hL : IsLineWithEnds L c d) (hLC : L ⊆ C) :
    closure (C \ L) ∩ L ⊆ {c, d} := by
  obtain ⟨a, b, hab, haL, ha0, ha1, _, hCL⟩ :=
    exists_complementary_arc_of_line hC hL hLC
  rw [hCL, closure_open_arc hab.2, ← haL]
  rintro z ⟨⟨t, ht⟩, ⟨s, hs⟩⟩
  rcases hab.5 s t (hs.trans ht.symm) with h | h
  · exact Or.inl (hs.symm.trans ((congrArg a h.1).trans ha0))
  · exact Or.inr (hs.symm.trans ((congrArg a h.1).trans ha1))

/-- Closing the complement of a cuff line gives a line with the same
ends. -/
theorem isLineWithEnds_closure_cuff_sdiff_line
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C L : Set S} {c d : S} (hC : IsOArc C)
    (hL : IsLineWithEnds L c d) (hLC : L ⊆ C) :
    IsLineWithEnds (closure (C \ L)) c d := by
  obtain ⟨a, b, hab, _, ha0, ha1, _, hCL⟩ :=
    exists_complementary_arc_of_line hC hL hLC
  rw [hCL, closure_open_arc hab.2]
  simpa only [hab.3, hab.4, ha0, ha1] using hab.2.isLineWithEnds

/-- The interior of a cuff line is a component after deleting its ends. -/
theorem cuff_line_sdiff_ends_mem_componentsIn
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C L : Set S} {c d : S} (hC : IsOArc C)
    (hL : IsLineWithEnds L c d) (hLC : L ⊆ C) :
    L \ {c, d} ∈ componentsIn (C \ {c, d}) := by
  obtain ⟨a, b, hab, haL, ha0, ha1, hun⟩ := exists_arcs_of_line hC hL hLC
  rw [← haL, ← ha0, ← ha1, arc_range_sdiff hab.1,
    componentsIn_sdiff_pair_of_two_arcs hab hun]
  exact Or.inl rfl

/-- Deleting a line's two ends and closing the result recovers the line. -/
theorem closure_line_sdiff_ends_eq
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {L : Set S} {c d : S} (hL : IsLineWithEnds L c d) :
    closure (L \ {c, d}) = L := by
  obtain ⟨a, ha, haL, ha0, ha1⟩ := hL.exists_arc
  rw [← haL, ← ha0, ← ha1, arc_range_sdiff ha, closure_open_arc ha]

/-- The closure of either component left by deleting two distinct cuff
points is a line with those ends. -/
theorem isLineWithEnds_closure_component_of_oArc
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C A : Set S} {s t : S} (hC : IsOArc C)
    (hs : s ∈ C) (ht : t ∈ C) (hst : s ≠ t)
    (hA : A ∈ componentsIn (C \ {s, t})) :
    IsLineWithEnds (closure A) s t := by
  obtain ⟨a, b, hab, ha0, ha1, hun⟩ := hC.exists_arcs hs ht hst
  rw [← ha0, ← ha1, componentsIn_sdiff_pair_of_two_arcs hab hun] at hA
  rcases hA with rfl | rfl
  · rw [closure_open_arc hab.1]
    simpa only [ha0, ha1] using hab.1.isLineWithEnds
  · rw [closure_open_arc hab.2]
    simpa only [hab.3, hab.4, ha0, ha1] using hab.2.isLineWithEnds

/-- The closure of the cuff subarc inside a closed cuff interval is the
line between its ends. This includes ends of the larger interval, as
required by Graph Minors VI (4.2), claim (1), page 125. -/
theorem closure_cuffSubArc_eq_of_subset_line
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C K L M : Set S} {c d : S}
    (hC : IsOArc C) (hM : IsLine M) (hMC : M ⊆ C) (hKM : K ⊆ M)
    (hL : IsLineWithEnds L c d) (hLK : L ⊆ K) :
    closure (cuffSubArc C K c d) = L := by
  obtain ⟨a, b, hab, haL, ha0, ha1, hun⟩ :=
    exists_arcs_of_line hC hL (hLK.trans (hKM.trans hMC))
  let A := a '' Ioo 0 1
  let B := b '' Ioo 0 1
  have hA : closure A = L := (closure_open_arc hab.1).trans haL
  have hB : closure B = range b := closure_open_arc hab.2
  have hAd : A = L \ {c, d} := by
    rw [← haL, ← ha0, ← ha1, arc_range_sdiff hab.1]
  have hcomp : componentsIn (C \ {c, d}) = {A, B} := by
    rw [← ha0, ← ha1]
    exact componentsIn_sdiff_pair_of_two_arcs hab hun
  have hAK : A ⊆ K := by rw [hAd]; exact sdiff_subset.trans hLK
  have hBK : ¬ B ⊆ K := by
    intro hBK
    have hMclosed : IsClosed M := by
      obtain ⟨e⟩ := hM
      have he : range (fun t => (e t).1) = M := by
        ext x
        constructor
        · rintro ⟨t, rfl⟩; exact (e t).2
        · intro hx; exact ⟨e.symm ⟨x, hx⟩, by simp⟩
      rw [← he]
      exact (isCompact_range (continuous_subtype_val.comp e.continuous)).isClosed
    have hbM : range b ⊆ M := by
      rw [← hB]
      exact closure_minimal (hBK.trans hKM) hMclosed
    exact not_oArc_subset_line hC hM (by
      rw [← hun, haL]; exact union_subset (hLK.trans hKM) hbM)
  have hsubarc : cuffSubArc C K c d = A := by
    unfold cuffSubArc
    rw [hcomp]
    have hfilter : {X ∈ ({A, B} : Set (Set S)) | X ⊆ K} = {A} := by
      ext X
      simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨rfl | rfl, hX⟩
        · rfl
        · exact (hBK hX).elim
      · rintro rfl
        exact ⟨Or.inl rfl, hAK⟩
    rw [hfilter, sUnion_singleton]
  rw [hsubarc, hA]

/-- The cuff subarc inside a subset of a line is that subline with its
two ends removed. -/
theorem cuffSubArc_eq_line_sdiff_ends_of_subset_line
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C K L M : Set S} {c d : S}
    (hC : IsOArc C) (hM : IsLine M) (hMC : M ⊆ C) (hKM : K ⊆ M)
    (hL : IsLineWithEnds L c d) (hLK : L ⊆ K) :
    cuffSubArc C K c d = L \ {c, d} := by
  have hcl := closure_cuffSubArc_eq_of_subset_line hC hM hMC hKM hL hLK
  have hsub : cuffSubArc C K c d ⊆ C \ {c, d} := by
    refine sUnion_subset ?_
    rintro T ⟨hT, _⟩
    obtain ⟨x, _, rfl⟩ := hT
    exact connectedComponentIn_subset _ x
  apply Subset.antisymm
  · intro x hx
    exact ⟨hcl ▸ subset_closure hx, (hsub hx).2⟩
  · intro x hx
    exact mem_sUnion.mpr ⟨L \ {c, d},
      ⟨cuff_line_sdiff_ends_mem_componentsIn hC hL (hLK.trans (hKM.trans hMC)),
        sdiff_subset.trans hLK⟩, hx⟩

/-- In a closed cuff interval, the closure of its subarc is the line
between the two specified ends. -/
theorem closure_cuffSubArc_eq_of_line
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C K L : Set S} {c d : S}
    (hC : IsOArc C) (hK : IsLine K) (hKC : K ⊆ C)
    (hL : IsLineWithEnds L c d) (hLK : L ⊆ K) :
    closure (cuffSubArc C K c d) = L :=
  closure_cuffSubArc_eq_of_subset_line hC hK hKC Subset.rfl hL hLK

end GraphMinor.GM06
