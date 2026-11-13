module

public import GraphMinor.GM06.Alg511CuffEdges
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5AdjoinedEdges
import GraphMinor.GM06.Section5StripDisjoint
import GraphMinor.GM07.NetExists
import Mathlib.Tactic

/-!
# Enumerating the auxiliary cuff edges

The drawing input of VI (5.11), page 134, uses the same cuff markers
as the successor procedure. Every nonvertex cuff point lies in an
open gap between consecutive prescribed vertices. An angular lift
and its integer part give the gap index. Consequently every edge
added by adjoining the cuffs is one of these fixed gaps. Distinct
gaps have distinct labels, and neither cuff contributes an old edge.
This proves the edge partition needed for the input bijection.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- The prescribed open inner gaps cover precisely the inner cuff
away from its prescribed vertices. The gap index comes from the
integer part of a normalized angular lift. -/
theorem alg511_initial_gaps_cover_cuff {k : ℕ} (hk : 0 < k)
    {p : ClosedCylinder} (hp : p ∈ cylinderCuff1) (hpM : p ∉ cylinderM1 k) :
    ∃ i : Fin k, p ∈ initialCuffGapCurve k i '' Ioo 0 1 := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  let b : ℝ := 2 * π / k
  have hsurj : Circle.exp '' Ico b (b + 2 * π) = univ := by
    have hIoc : Circle.exp '' Ioc b (b + 2 * π) = univ := by
      simpa only [Circle.exp_surjective.range_eq] using
        Circle.periodic_exp.image_Ioc Real.two_pi_pos b
    apply eq_univ_of_forall
    intro z
    obtain ⟨a, ha, haz⟩ := (show z ∈ Circle.exp '' Ioc b (b + 2 * π) by
      rw [hIoc]; exact mem_univ _)
    by_cases he : a = b + 2 * π
    · refine ⟨b, ⟨le_rfl, by linarith [Real.two_pi_pos]⟩, ?_⟩
      rw [he, Circle.exp_add_two_pi] at haz
      exact haz
    · exact ⟨a, ⟨ha.1.le, lt_of_le_of_ne ha.2 he⟩, haz⟩
  obtain ⟨a, ha, hap⟩ := (show p.val.2 ∈ Circle.exp '' Ico b (b + 2 * π) by
    rw [hsurj]; exact mem_univ _)
  let x : ℝ := a * k / (2 * π) - 1
  have hb : b * k / (2 * π) = 1 := by
    dsimp [b]
    field_simp [hkne, pi_ne_zero]
  have hx0 : 0 ≤ x := by
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ha.1 hkR.le)
      (le_of_lt Real.two_pi_pos)
    rw [hb] at h
    dsimp [x]
    linarith
  have hxk : x < k := by
    have h := div_lt_div_of_pos_right (mul_lt_mul_of_pos_right ha.2 hkR) Real.two_pi_pos
    have hb' : (b + 2 * π) * k / (2 * π) = 1 + k := by
      rw [add_mul, add_div, hb]
      congr 1
      field_simp [pi_ne_zero]
    rw [hb'] at h
    dsimp [x]
    linarith
  let i : Fin k := ⟨⌊x⌋₊, (Nat.floor_lt hx0).mpr hxk⟩
  have hi0 : (i.val : ℝ) ≤ x := Nat.floor_le hx0
  have hi1 : x < (i.val : ℝ) + 1 := Nat.lt_floor_add_one x
  let t : unitInterval := ⟨x - i.val, by constructor <;> linarith⟩
  have hangle : 2 * (((i.val + 1 : ℕ) : ℝ) + (t : ℝ)) * π / k = a := by
    change 2 * (((i.val + 1 : ℕ) : ℝ) + (x - i.val)) * π / k = a
    push_cast
    dsimp [x]
    field_simp [hkne, pi_ne_zero]
    ring
  have htp : initialCuffGapCurve k i t = p := by
    apply Subtype.ext
    apply Prod.ext
    · exact hp.symm
    · change (cylinderPoint 1 (by simp)
        (2 * (((i.val + 1 : ℕ) : ℝ) + (t : ℝ)) * π / k)).val.2 = p.val.2
      rw [hangle]
      exact hap
  have ht0 : 0 < (t : ℝ) := by
    apply lt_of_le_of_ne t.property.1
    intro hzero
    apply hpM
    refine ⟨i, ?_⟩
    have ht : t = 0 := Subtype.ext hzero.symm
    rw [ht] at htp
    calc
      cylinderM1Point k i = initialCuffGapCurve k i 0 := by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · change Circle.exp _ = Circle.exp _
          congr 1
          simp
      _ = p := htp
  exact ⟨i, t, ⟨ht0, by change x - i.val < 1; linarith⟩, htp⟩

private theorem cuffSwap_twice (p : ClosedCylinder) :
    alg511CuffSwap (alg511CuffSwap p) = p := by
  apply Subtype.ext
  apply Prod.ext <;> simp [alg511CuffSwap]

/-- The prescribed open outer gaps cover the outer cuff away from
its prescribed vertices, with the same increasing angular indices. -/
theorem alg511_outer_gaps_cover_cuff {k : ℕ} (hk : 0 < k)
    {p : ClosedCylinder} (hp : p ∈ cylinderCuff2) (hpM : p ∉ cylinderM2 k) :
    ∃ i : Fin k, p ∈ alg511OuterCuffGapCurve k i '' Ioo 0 1 := by
  have hq : alg511CuffSwap p ∈ cylinderCuff1 := by
    change 3 - p.val.1 = 1
    change p.val.1 = 2 at hp
    linarith
  have hqM : alg511CuffSwap p ∉ cylinderM1 k := by
    rintro ⟨i, hi⟩
    apply hpM
    refine ⟨i, ?_⟩
    simpa only [alg511CuffSwap_M1, cuffSwap_twice] using congrArg alg511CuffSwap hi
  obtain ⟨i, t, ht, htp⟩ := alg511_initial_gaps_cover_cuff hk hq hqM
  refine ⟨i, t, ht, ?_⟩
  change alg511CuffSwap (initialCuffGapCurve k i t) = p
  rw [htp, cuffSwap_twice]

/-- Each inner gap has a distinct edge label. Its midpoint cannot
lie on a closed gap with another index. -/
theorem alg511_initial_gap_injective {k : ℕ} {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) :
    Function.Injective (fun i : Fin k => initialCuffGapCurve k i '' Ioo 0 1) := by
  intro i j hij
  have hi := (initialCuffGapCurve_props hG i).2.2.2.1
  change initialCuffGapCurve k i '' Ioo 0 1 = initialCuffGapCurve k j '' Ioo 0 1 at hij
  rw [hij] at hi
  exact index_eq_of_dual_point_mem_initial_gap hG.1 (image_subset_range _ _ hi)

/-- Each outer gap has a distinct edge label as well. -/
theorem alg511_outer_gap_injective {k : ℕ} {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) :
    Function.Injective (fun i : Fin k => alg511OuterCuffGapCurve k i '' Ioo 0 1) := by
  intro i j hij
  apply alg511_initial_gap_injective hG
  have h := congrArg (image alg511CuffSwap) hij
  have hswap (a : Fin k) :
      alg511CuffSwap '' (alg511OuterCuffGapCurve k a '' Ioo 0 1) =
        initialCuffGapCurve k a '' Ioo 0 1 := by
    rw [image_image]
    have hf : (fun t => alg511CuffSwap (alg511OuterCuffGapCurve k a t)) =
        (initialCuffGapCurve k a : unitInterval → ClosedCylinder) := by
      funext t
      exact cuffSwap_twice _
    rw [hf]
  rwa [hswap, hswap] at h

/-- No other auxiliary edges occur: an edge is either an old edge,
an inner gap, or an outer gap. This classification uses no linkage. -/
theorem alg511_cuff_edge_cases {k : ℕ} {G F : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (hGF : G.IsSubdrawing F)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V)
    {e : Set ClosedCylinder} (he : e ∈ F.E) :
    e ∈ G.E ∨ (∃ i : Fin k, e = initialCuffGapCurve k i '' Ioo 0 1) ∨
      (∃ i : Fin k, e = alg511OuterCuffGapCurve k i '' Ioo 0 1) := by
  rcases edge_mem_or_subset_boundary_of_adjoining hGF hFU hFV he with hold | hbd
  · exact Or.inl hold
  obtain ⟨p, hp⟩ := he.1
  have hpV : p ∉ G.V := by
    rw [← hFV]
    exact (he.2.1 hp).2
  have hM (hm : p ∈ cylinderM1 k ∪ cylinderM2 k) : False :=
    hpV ((hG.2.2.symm ▸ hm : p ∈ G.V ∩ bd ClosedCylinder).1)
  rcases edge_subset_one_cuff_of_subset_boundary he hbd with hinner | houter
  · obtain ⟨i, hi⟩ := alg511_initial_gaps_cover_cuff hG.1 (hinner hp) (fun h => hM (Or.inl h))
    obtain ⟨d, hd, hdgap⟩ := alg511_exists_exact_initial_gap_edge hG hGF hFU hFV i
    exact Or.inr (Or.inl ⟨i, (GM07.arcComponentsIn_eq_of_mem he hd hp (hdgap ▸ hi)).trans hdgap⟩)
  · obtain ⟨i, hi⟩ := alg511_outer_gaps_cover_cuff hG.1 (houter hp) (fun h => hM (Or.inr h))
    obtain ⟨d, hd, hdgap⟩ := alg511_exists_exact_outer_gap_edge hG hGF hFU hFV i
    exact Or.inr (Or.inr ⟨i, (GM07.arcComponentsIn_eq_of_mem he hd hp (hdgap ▸ hi)).trans hdgap⟩)

/-- The augmented drawing has exactly the original edges and the
fixed inner and outer gap families. -/
theorem alg511_cuff_edges_eq {k : ℕ} {G F : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (hGF : G.IsSubdrawing F)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V) :
    F.E = G.E ∪ (range (fun i : Fin k => initialCuffGapCurve k i '' Ioo 0 1) ∪
      range (fun i : Fin k => alg511OuterCuffGapCurve k i '' Ioo 0 1)) := by
  ext e
  constructor
  · intro he
    rcases alg511_cuff_edge_cases hG hGF hFU hFV he with hold | ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Or.inl hold
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, rfl⟩)
  · rintro (he | ⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact hGF.2 he
    · obtain ⟨e, he, hgap⟩ := alg511_exists_exact_initial_gap_edge hG hGF hFU hFV i
      simpa only [hgap] using he
    · obtain ⟨e, he, hgap⟩ := alg511_exists_exact_outer_gap_edge hG hGF hFU hFV i
      simpa only [hgap] using he

/-- The three edge families are pairwise disjoint. Properness rules
out an original edge on either cuff, and the two cuffs are disjoint. -/
theorem alg511_cuff_edge_families_disjoint {k : ℕ} {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) :
    Disjoint G.E (range (fun i : Fin k => initialCuffGapCurve k i '' Ioo 0 1)) ∧
    Disjoint G.E (range (fun i : Fin k => alg511OuterCuffGapCurve k i '' Ioo 0 1)) ∧
    Disjoint (range (fun i : Fin k => initialCuffGapCurve k i '' Ioo 0 1))
      (range (fun i : Fin k => alg511OuterCuffGapCurve k i '' Ioo 0 1)) := by
  have hin (i : Fin k) : (initialCuffGapCurve k i '' Ioo 0 1).Nonempty :=
    ⟨_, (initialCuffGapCurve_props hG i).2.2.2.1⟩
  have hout (i : Fin k) : (alg511OuterCuffGapCurve k i '' Ioo 0 1).Nonempty := by
    obtain ⟨p, t, ht, rfl⟩ := hin i
    exact ⟨_, t, ht, rfl⟩
  have hinner (i : Fin k) : initialCuffGapCurve k i '' Ioo 0 1 ⊆ cylinderCuff1 :=
    fun _ hp => (initialCuffGapCurve_props hG i).2.2.1 (image_subset_range _ _ hp)
  have houter (i : Fin k) : alg511OuterCuffGapCurve k i '' Ioo 0 1 ⊆ cylinderCuff2 := by
    rintro p ⟨t, ht, rfl⟩
    change 3 - 1 = (2 : ℝ)
    norm_num
  have hproper {e : Set ClosedCylinder} (he : e ∈ G.E)
      {p : ClosedCylinder} (hp : p ∈ e) (hbd : p ∈ bd ClosedCylinder) : False :=
    (he.2.1 hp).2 (hG.2.1 ⟨hbd, (he.2.1 hp).1⟩)
  refine ⟨disjoint_left.mpr ?_, disjoint_left.mpr ?_, disjoint_left.mpr ?_⟩
  · rintro e he ⟨i, rfl⟩
    obtain ⟨p, hp⟩ := hin i
    apply hproper he hp
    rw [bd_closedCylinder]
    exact Or.inl (hinner i hp)
  · rintro e he ⟨i, rfl⟩
    obtain ⟨p, hp⟩ := hout i
    apply hproper he hp
    rw [bd_closedCylinder]
    exact Or.inr (houter i hp)
  · rintro e ⟨i, rfl⟩ ⟨j, hji⟩
    obtain ⟨p, hp⟩ := hin i
    have hpj : p ∈ alg511OuterCuffGapCurve k j '' Ioo 0 1 := by
      change alg511OuterCuffGapCurve k j '' Ioo 0 1 =
        initialCuffGapCurve k i '' Ioo 0 1 at hji
      rw [hji]
      exact hp
    exact disjoint_left.mp disjoint_cylinderCuffs (hinner i hp) (houter j hpj)

/-- The edge labels of the cuff-augmented drawing consist of the
original labels followed by one fixed label for every gap on each
cuff. The equivalence records the actual edges, rather than merely
their number. -/
theorem alg511_exists_cuff_edge_equiv {k : ℕ} {G F : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (hGF : G.IsSubdrawing F)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V) :
    ∃ e : G.E ⊕ (Fin k ⊕ Fin k) ≃ F.E,
      (∀ a : G.E, (e (.inl a)).val = a.val) ∧
      (∀ i : Fin k, (e (.inr (.inl i))).val = initialCuffGapCurve k i '' Ioo 0 1) ∧
      (∀ i : Fin k, (e (.inr (.inr i))).val = alg511OuterCuffGapCurve k i '' Ioo 0 1) := by
  classical
  have hi (i : Fin k) : initialCuffGapCurve k i '' Ioo 0 1 ∈ F.E := by
    obtain ⟨e, he, hgap⟩ := alg511_exists_exact_initial_gap_edge hG hGF hFU hFV i
    exact hgap ▸ he
  have ho (i : Fin k) : alg511OuterCuffGapCurve k i '' Ioo 0 1 ∈ F.E := by
    obtain ⟨e, he, hgap⟩ := alg511_exists_exact_outer_gap_edge hG hGF hFU hFV i
    exact hgap ▸ he
  let f : G.E ⊕ (Fin k ⊕ Fin k) → F.E := fun a => match a with
    | .inl e => ⟨e.val, hGF.2 e.property⟩
    | .inr (.inl i) => ⟨initialCuffGapCurve k i '' Ioo 0 1, hi i⟩
    | .inr (.inr i) => ⟨alg511OuterCuffGapCurve k i '' Ioo 0 1, ho i⟩
  obtain ⟨hdI, hdO, hdIO⟩ := alg511_cuff_edge_families_disjoint hG
  have hOI (a : G.E) (i : Fin k) : a.val ≠ initialCuffGapCurve k i '' Ioo 0 1 := by
    intro heq
    exact disjoint_left.mp hdI a.property ⟨i, heq.symm⟩
  have hOO (a : G.E) (i : Fin k) : a.val ≠ alg511OuterCuffGapCurve k i '' Ioo 0 1 := by
    intro heq
    exact disjoint_left.mp hdO a.property ⟨i, heq.symm⟩
  have hIO (i j : Fin k) : initialCuffGapCurve k i '' Ioo 0 1 ≠
      alg511OuterCuffGapCurve k j '' Ioo 0 1 := by
    intro heq
    exact disjoint_left.mp hdIO ⟨i, rfl⟩ ⟨j, heq.symm⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hv := congrArg Subtype.val hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext hv)
      | inr b =>
        cases b with
        | inl i => exact False.elim (hOI a i hv)
        | inr i => exact False.elim (hOO a i hv)
    | inr a =>
      cases a with
      | inl i =>
        cases b with
        | inl b => exact False.elim (hOI b i hv.symm)
        | inr b =>
          cases b with
          | inl j => exact congrArg (fun i => Sum.inr (Sum.inl i)) (alg511_initial_gap_injective hG hv)
          | inr j => exact False.elim (hIO i j hv)
      | inr i =>
        cases b with
        | inl b => exact False.elim (hOO b i hv.symm)
        | inr b =>
          cases b with
          | inl j => exact False.elim (hIO j i hv.symm)
          | inr j => exact congrArg (fun i => Sum.inr (Sum.inr i)) (alg511_outer_gap_injective hG hv)
  have hsurj : Function.Surjective f := by
    intro e
    rcases alg511_cuff_edge_cases hG hGF hFU hFV e.property with hold | ⟨i, hi⟩ | ⟨i, hi⟩
    · exact ⟨.inl ⟨e.val, hold⟩, Subtype.ext rfl⟩
    · exact ⟨.inr (.inl i), Subtype.ext hi.symm⟩
    · exact ⟨.inr (.inr i), Subtype.ext hi.symm⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

end GraphMinor.GM06
