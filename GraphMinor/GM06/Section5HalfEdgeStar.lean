module

public import GraphMinor.GM11.Rotation

/-!
# A finite star neighbourhood from the edge parametrizations

The rotation input for VI (5.7), page 133, records directed ends at
a vertex. There is a neighbourhood in which every drawing point
other than the vertex lies on a short piece of one of those ends.
Remove the other vertices and the closed middle portions of the
edges. The remaining open set is such a neighbourhood, including
when a loop has both ends at the vertex.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- Close to a drawing vertex, every other drawing point is on an
incident directed end, at a parameter strictly below its midpoint. -/
theorem exists_halfedge_star_neighbourhood
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {γ : Set S → I → S} (hγ : EdgePar Γ γ)
    {v : S} (hv : v ∈ Γ.V) :
    ∃ O : Set S, IsOpen O ∧ v ∈ O ∧ ∀ y ∈ Γ.U ∩ O,
      y = v ∨ ∃ a : halfEdges Γ γ v, ∃ t : I,
        0 < t ∧ t < 1 ∧ spoke γ a.1 t = y := by
  classical
  let C : Set S → Set I := fun e => {t |
    (γ e 0 = v → (1 / 4 : ℝ) ≤ t.1) ∧
    (γ e 1 = v → t.1 ≤ (3 / 4 : ℝ))}
  have hCc (e) : IsClosed (C e) := by
    by_cases h0 : γ e 0 = v <;> by_cases h1 : γ e 1 = v
    · change IsClosed {t : I | (γ e 0 = v → (1 / 4 : ℝ) ≤ t.1) ∧
        (γ e 1 = v → t.1 ≤ (3 / 4 : ℝ))}
      simp only [h0, h1, forall_const]
      exact (isClosed_le continuous_const continuous_subtype_val).inter
        (isClosed_le continuous_subtype_val continuous_const)
    · simpa only [C, h0, h1, forall_const, false_implies, and_true] using
        (isClosed_le continuous_const continuous_subtype_val :
          IsClosed {t : I | (1 / 4 : ℝ) ≤ t.1})
    · simpa only [C, h0, h1, forall_const, false_implies, true_and] using
        (isClosed_le continuous_subtype_val continuous_const :
          IsClosed {t : I | t.1 ≤ (3 / 4 : ℝ)})
    · simp only [C, h0, h1, false_implies, true_and]
      exact isClosed_univ
  let K : Set S := (Γ.V \ {v}) ∪ ⋃ e ∈ Γ.E, γ e '' C e
  have hKc : IsClosed K :=
    ((Γ.finite_V.subset sdiff_subset).isClosed).union
      (Γ.finite_edges.isClosed_biUnion fun e he =>
        ((hCc e).isCompact.image (hγ.cont e he)).isClosed)
  have hvK : v ∉ K := by
    rintro (⟨_, h⟩ | hh)
    · exact h rfl
    · obtain ⟨e, he, t, ht, hte⟩ := mem_iUnion₂.mp hh
      by_cases ht0 : t = 0
      · have hh := ht.1 (ht0 ▸ hte)
        rw [ht0] at hh
        norm_num at hh
      by_cases ht1 : t = 1
      · have hh := ht.2 (ht1 ▸ hte)
        rw [ht1] at hh
        norm_num at hh
      have hte' : v ∈ e := by
        rw [← hγ.image e he]
        exact ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr ht0,
          unitInterval.lt_one_iff_ne_one.mpr ht1⟩, hte⟩
      exact edge_notMem_V he hte' hv
  refine ⟨Kᶜ, hKc.isOpen_compl, hvK, ?_⟩
  rintro y ⟨hyU, hyK⟩
  by_cases hyv : y = v
  · exact Or.inl hyv
  right
  rw [Γ.U_eq] at hyU
  rcases hyU with hyV | hyE
  · exact False.elim (hyK (Or.inl ⟨hyV, hyv⟩))
  obtain ⟨e, he, hye⟩ := mem_iUnion₂.mp hyE
  have hclosure : closure e ⊆ γ e '' univ := by
    apply closure_minimal _ ((isCompact_univ.image (hγ.cont e he)).isClosed)
    calc
      e = γ e '' Ioo 0 1 := (hγ.image e he).symm
      _ ⊆ γ e '' univ := image_mono (subset_univ _)
  obtain ⟨t, _, hty⟩ := hclosure hye
  have htC : t ∉ C e := fun hh => hyK (Or.inr (mem_iUnion₂.mpr ⟨e, he, t, hh, hty⟩))
  simp only [C, mem_ofPred_eq, not_and_or, not_forall, not_le] at htC
  rcases htC with ⟨h0, ht⟩ | ⟨h1, ht⟩
  · let a : halfEdges Γ γ v := ⟨(e, false), he, h0⟩
    have ht0 : 0 < t.1 := by
      apply lt_of_le_of_ne t.2.1
      intro hh
      have htzero : t = 0 := Subtype.ext hh.symm
      exact hyv (hty.symm.trans (htzero ▸ h0))
    let r : I := ⟨2 * t.1, by positivity, by linarith⟩
    refine ⟨a, r, by change 0 < 2 * t.1; positivity,
      by change 2 * t.1 < 1; linarith, ?_⟩
    change γ e (halfPar false r) = y
    have hr : halfPar false r = t := Subtype.ext (by simp [halfPar, halfT, r])
    rwa [hr]
  · let a : halfEdges Γ γ v := ⟨(e, true), he, h1⟩
    have ht1 : t.1 < 1 := by
      apply lt_of_le_of_ne t.2.2
      intro hh
      have htone : t = 1 := Subtype.ext hh
      exact hyv (hty.symm.trans (htone ▸ h1))
    let r : I := ⟨2 * (1 - t.1), by linarith, by linarith⟩
    refine ⟨a, r, by change 0 < 2 * (1 - t.1); linarith,
      by change 2 * (1 - t.1) < 1; linarith, ?_⟩
    change γ e (halfPar true r) = y
    have hr : halfPar true r = t := Subtype.ext (by
      change 1 - (2 * (1 - t.1)) / 2 = t.1
      ring)
    rwa [hr]


/-- Every drawing point sufficiently close to a vertex, other than the
vertex itself, belongs to exactly one incident directed end. -/
theorem exists_unique_halfedge_star_neighbourhood
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {γ : Set S → I → S} (hγ : EdgePar Γ γ)
    {v : S} (hv : v ∈ Γ.V) :
    ∃ O : Set S, IsOpen O ∧ v ∈ O ∧ ∀ y ∈ Γ.U ∩ O, y ≠ v →
      ∃! a : halfEdges Γ γ v, ∃ t : I,
        0 < t ∧ t < 1 ∧ spoke γ a.1 t = y := by
  obtain ⟨O, hOo, hvO, hstar⟩ := exists_halfedge_star_neighbourhood hγ hv
  refine ⟨O, hOo, hvO, ?_⟩
  intro y hy hyv
  obtain hyv' | ⟨a, t, ht0, ht1, hty⟩ := hstar y hy
  · exact (hyv hyv').elim
  refine ⟨a, ⟨t, ht0, ht1, hty⟩, ?_⟩
  rintro b ⟨r, hr0, _, hry⟩
  by_contra hba
  have hne : b.1 ≠ a.1 := fun hh => hba (Subtype.ext hh)
  have hh := spoke_eq_of_ne hγ b.2.1 a.2.1 hne hr0 ht0 (hry.trans hty.symm)
  exact ht1.ne hh.2

end GraphMinor.GM06
