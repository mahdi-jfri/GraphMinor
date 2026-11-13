module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM06.Section5GapEdge
import GraphMinor.GM06.Section5RegionGraphPath
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5Red
import GraphMinor.Surface.EdgeLoop
import GraphMinor.GM11.Walks
import Mathlib.Tactic

/-!
# Identifying a prescribed cuff arc with its entire drawing edge

For the drawing input of VI (5.11), page 134, the auxiliary cuff
edges must have fixed labels. A continuous arc with distinct vertex
ends whose interior lies in one edge traces that whole edge. Its
range is connected, contains both edge ends, and lies in the closed
edge, so it equals the closed edge. Removing the vertices gives the
exact open edge, rather than only an incidence inclusion.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface unitInterval
universe u

/-- A continuous arc with distinct drawing vertices as ends and
interior in one edge traverses precisely that entire open edge. -/
theorem alg511_edge_eq_arc_interior
    {S : Type u} [TopologicalSpace S] [T2Space S] {G : Drawing S}
    {e : Set S} (he : e ∈ G.E) (f : Curve S)
    (hf₀ : f 0 ∈ G.V) (hf₁ : f 1 ∈ G.V) (hne : f 0 ≠ f 1)
    (hf : f '' Ioo 0 1 ⊆ e) : e = f '' Ioo 0 1 := by
  let t : I := ⟨1 / 2, by norm_num⟩
  have ht : t ∈ Ioo (0 : I) 1 := by
    constructor
    · change (0 : ℝ) < 1 / 2
      norm_num
    · change (1 / 2 : ℝ) < 1
      norm_num
  have hrange : range f ⊆ closure e :=
    (arc_interior_subset_edge he (hf.trans he.2.1)
      ⟨f t, hf ⟨t, ht, rfl⟩, t, ht, rfl⟩).2
  have hcap₀ : f 0 ∈ closure e ∩ G.V := ⟨hrange (mem_range_self 0), hf₀⟩
  have hcap₁ : f 1 ∈ closure e ∩ G.V := ⟨hrange (mem_range_self 1), hf₁⟩
  have hclosed : range f = closure e := by
    rcases G.edge_cond e he with ⟨u, v, _, hcap, hline⟩ | ⟨u, hcap, _⟩
    · rw [hcap] at hcap₀ hcap₁
      have hpair : ({f 0, f 1} : Set S) = {u, v} := by
        rcases hcap₀ with h₀ | h₀ <;> rcases hcap₁ with h₁ | h₁
        · exact False.elim (hne (h₀.trans h₁.symm))
        · rw [h₀, mem_singleton_iff.mp h₁]
        · rw [mem_singleton_iff.mp h₀, h₁]
          exact pair_comm _ _
        · exact False.elim (hne ((mem_singleton_iff.mp h₀).trans (mem_singleton_iff.mp h₁).symm))
      have hends : {u, v} ⊆ range f := by
        rw [← hpair]
        rintro p (rfl | hp)
        · exact mem_range_self 0
        · exact mem_singleton_iff.mp hp ▸ mem_range_self 1
      exact hline.eq_of_subset (isPreconnected_range f.continuous) hrange
        (hends (mem_insert u {v})) (hends (mem_insert_of_mem u (mem_singleton v)))
    · rw [hcap] at hcap₀ hcap₁
      exact False.elim (hne ((mem_singleton_iff.mp hcap₀).trans (mem_singleton_iff.mp hcap₁).symm))
  rw [← G.closure_diff_V he, ← hclosed]
  apply subset_antisymm
  · rintro p ⟨⟨s, rfl⟩, hsV⟩
    have hs₀ : s ≠ 0 := fun h => hsV (h.symm ▸ hf₀)
    have hs₁ : s ≠ 1 := fun h => hsV (h.symm ▸ hf₁)
    exact ⟨s, ⟨unitInterval.pos_iff_ne_zero.mpr hs₀,
      unitInterval.lt_one_iff_ne_one.mpr hs₁⟩, rfl⟩
  · intro p hp
    exact ⟨image_subset_range _ _ hp, (he.2.1 (hf hp)).2⟩

/-- The open full gap of the one-vertex inner cuff is the cuff
minus that single prescribed vertex. -/
theorem alg511_one_initial_gap_image :
    initialCuffGapCurve 1 0 '' Ioo 0 1 = cylinderCuff1 \ {cylinderM1Point 1 0} := by
  apply subset_antisymm
  · rintro p ⟨t, ht, rfl⟩
    refine ⟨rfl, ?_⟩
    intro hp
    exact initialCuffGapCurve_interior_not_prescribed (by decide) 0 ht
      (Or.inl ⟨0, (mem_singleton_iff.mp hp).symm⟩)
  · rintro p ⟨hpC, hpM⟩
    have hz : p.val.2 ≠ 1 := by
      intro hpoint
      apply hpM
      apply mem_singleton_iff.mpr
      apply Subtype.ext
      apply Prod.ext
      · exact hpC
      · simpa [cylinderM1Point, cylinderPoint] using hpoint
    have hsurj : Circle.exp '' Ioc (0 : ℝ) (2 * Real.pi) = univ := by
      simpa only [zero_add, Circle.exp_surjective.range_eq] using
        Circle.periodic_exp.image_Ioc Real.two_pi_pos 0
    obtain ⟨a, ha, hap⟩ := (show p.val.2 ∈ Circle.exp '' Ioc (0 : ℝ) (2 * Real.pi) by
      rw [hsurj]; exact mem_univ _)
    have ha₁ : a < 2 * Real.pi := lt_of_le_of_ne ha.2 (by
      intro heq
      apply hz
      rw [heq, Circle.exp_two_pi] at hap
      exact hap.symm)
    let t : unitInterval := ⟨a / (2 * Real.pi),
      (div_pos ha.1 Real.two_pi_pos).le, (div_lt_one Real.two_pi_pos).mpr ha₁ |>.le⟩
    have ht : t ∈ Ioo (0 : unitInterval) 1 :=
      ⟨div_pos ha.1 Real.two_pi_pos, (div_lt_one Real.two_pi_pos).mpr ha₁⟩
    refine ⟨t, ht, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact hpC.symm
    · change (cylinderPoint 1 (by simp)
        (2 * ((((0 : Fin 1).val + 1 : ℕ) : ℝ) + (t : ℝ)) * Real.pi / (1 : ℕ))).val.2 = p.val.2
      have hangle : 2 * ((((0 : Fin 1).val + 1 : ℕ) : ℝ) + (t : ℝ)) * Real.pi / (1 : ℕ) =
          a + 2 * Real.pi := by
        norm_num only [Fin.val_zero, Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add, div_one]
        dsimp only [t]
        field_simp [Real.pi_ne_zero]
        ring
      rw [hangle]
      change Circle.exp (a + 2 * Real.pi) = p.val.2
      rw [Circle.exp_add_two_pi]
      exact hap

/-- The prescribed inner cuff gap is an entire edge of the drawing
with cuffs adjoined, including the single-vertex loop case. -/
theorem alg511_exists_exact_initial_gap_edge
    {k : ℕ} {G F : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G)
    (hGF : G.IsSubdrawing F) (hFU : F.U = G.U ∪ bd ClosedCylinder)
    (hFV : F.V = G.V) (i : Fin k) :
    ∃ e ∈ F.E, e = initialCuffGapCurve k i '' Ioo 0 1 := by
  obtain ⟨e, he, hNe, _, heBd, _, _, _, hgap⟩ :=
    exists_added_initial_gap_edge hG hGF hFU hFV i
  have hM (j : Fin k) : cylinderM1Point k j ∈ F.V := by
    rw [hFV]
    have hp : cylinderM1Point k j ∈ G.V ∩ bd ClosedCylinder := by
      rw [hG.2.2]
      exact Or.inl ⟨j, rfl⟩
    exact hp.1
  by_cases hk : 1 < k
  · have hp := initialCuffGapCurve_props hG i
    have hne : initialCuffGapCurve k i 0 ≠ initialCuffGapCurve k i 1 := by
      rw [hp.1, hp.2.1]
      intro heq
      exact finSuccCycle_ne_of_one_lt hk i ((cylinderM1Point_injective hG.1 heq).symm)
    exact ⟨e, he, alg511_edge_eq_arc_interior he (initialCuffGapCurve k i)
      (hp.1.symm ▸ hM i) (hp.2.1.symm ▸ hM (finSuccCycle i)) hne hgap⟩
  · have hpos : 0 < k := hG.1
    have hk₁ : k = 1 := by omega
    subst k
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hC₁ : IsClosed cylinderCuff1 := isClosed_eq
      (continuous_fst.comp continuous_subtype_val) continuous_const
    have hC₂ : IsClosed cylinderCuff2 := isClosed_eq
      (continuous_fst.comp continuous_subtype_val) continuous_const
    have hcover : e ⊆ cylinderCuff1 ∪ cylinderCuff2 := bd_closedCylinder ▸ heBd
    have hcut : e ∩ (cylinderCuff1 ∩ cylinderCuff2) = ∅ := by
      rw [disjoint_iff_inter_eq_empty.mp disjoint_cylinderCuffs, inter_empty]
    have heC : e ⊆ cylinderCuff1 := by
      rcases isPreconnected_iff_subset_of_disjoint_closed.mp he.2.2.1.isConnected.isPreconnected
        cylinderCuff1 cylinderCuff2 hC₁ hC₂ hcover hcut with h | h
      · exact h
      · exact False.elim (disjoint_left.mp disjoint_cylinderCuffs rfl (h hNe))
    refine ⟨e, he, subset_antisymm ?_ hgap⟩
    rw [alg511_one_initial_gap_image]
    intro p hp
    refine ⟨heC hp, ?_⟩
    intro hpM
    have hv : p ∈ F.V := (mem_singleton_iff.mp hpM).symm ▸ hM 0
    exact (he.2.1 hp).2 hv

end GraphMinor.GM06
