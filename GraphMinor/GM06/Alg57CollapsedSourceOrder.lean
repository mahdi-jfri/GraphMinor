module

public import GraphMinor.GM06.Alg57SourceCuffGap
public import GraphMinor.GM06.Alg57CurrentEndClassification
import GraphMinor.GM06.Section5PolarRotationRow
import GraphMinor.GM06.Alg57RowRotation

/-!
# The retained target block in the actual source chart

For Lemma 8 of VI (5.7), page 133, all retained target rays have
positive half-angles in the full quotient chart. Choose one radius
below their finitely many sine bounds, and shrink the new positive
polar chart inside it. The negative cuff contact is outside the
collapsed target disc, so the positive coordinate loop reads every
ordered pair after that contact. The resulting block order holds
in the original new chart because radial shrinking keeps its labels.

The last lemma turns an actual half-edge/rim bijection into the
permanent directions and exact edge incidence used by a numeric row.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- A finite family of positive half-angles has a common radius
that is at most one and at most every half-angle sine. -/
theorem exists_common_half_angle_radius
    {J : Type*} [Fintype J] (θ : J → ℝ)
    (hθ0 : ∀ j, 0 < θ j) (hθP : ∀ j, θ j < 2 * Real.pi) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ j, δ ≤ Real.sin (θ j / 2) := by
  classical
  let δ : ℝ := Finset.univ.inf' (by simp : (Finset.univ : Finset (Option J)).Nonempty)
    (fun j => match j with | none => 1 | some j => Real.sin (θ j / 2))
  have hδ : 0 < δ := by
    apply (Finset.lt_inf'_iff _).2
    intro j _
    cases j with
    | none => exact zero_lt_one
    | some j => exact (section5RadiusCollapse_half_angle_bounds (hθ0 j) (hθP j)).2.2
  exact ⟨δ, hδ, Finset.inf'_le _ (Finset.mem_univ (none : Option J)),
    fun j => Finset.inf'_le _ (Finset.mem_univ (some j))⟩

/-- The order of the retained target ends, starting at a fixed
cuff end, is their old order after the incoming ray. All contacts
come from the actual pointwise quotient and strict half-spokes. -/
theorem collapsed_source_block_order
    {J : Type*} [Fintype J]
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar Γ γ) {p : OnePoint EuclideanPlane} (hpV : p ∈ Γ.V)
    {π : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane)}
    {A C : Set (OnePoint EuclideanPlane)}
    (hfibre : π ⁻¹' {p} = A) (hinj : InjOn π Aᶜ)
    (hfix : ∀ x ∈ C, π x = x)
    {Φ Ψ Φ₀ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (w : Circle)
    (hquot : ∀ x, Ψ (section5CollapsedRadiusDiscPoint x) =
      π (Φ (section5RotateDisc w x)))
    (hΨi : Function.Injective Ψ) (hΨpos : GM06PositivePolar Ψ)
    (hΨ0 : Ψ polarCentre = p) (hΨnhd : p ∈ interior (range Ψ))
    (hoff : Disjoint (range Φ) C)
    (hp : IsPolar Γ p Φ₀) (hpos : GM06PositivePolar Φ₀)
    (d : halfEdges Γ γ p ≃ {u : Circle | ∃ e ∈ Γ.E, polarRimMap Φ₀ u ∈ e})
    (hd : ∀ a, ∀ t : I, 0 < t → Φ₀ (polarDiscPoint t (d a).val) ∈ range (spoke γ a.val))
    (minus : halfEdges Γ γ p) (hcuff : range (spoke γ minus.val) ⊆ C)
    (a : J → halfEdges Γ γ p) (ha : Function.Injective a) (hma : ∀ j, minus ≠ a j)
    (g : J → I → OnePoint EuclideanPlane)
    (hg : ∀ j t, spoke γ (a j).val t = π (g j t))
    (θ : J → ℝ) (hθ0 : ∀ j, 0 < θ j) (hθP : ∀ j, θ j < 2 * Real.pi)
    (hray : ∀ j, ∀ t : I, 0 < t →
      Φ (polarDiscPoint t (w * Circle.exp (θ j))) ∈ g j '' Ioo (0 : I) 1)
    {js : List J} (horder : js.Pairwise (fun i j => θ i < θ j)) :
    js.Pairwise (fun i j => CircleCyclic (d minus).val (d (a i)).val (d (a j)).val) := by
  classical
  obtain ⟨δ, hδ, _, hδsin⟩ := exists_common_half_angle_radius θ hθ0 hθP
  have hrays (j : J) (r : I) (hr0 : 0 < (r : ℝ)) (hrδ : (r : ℝ) ≤ δ) :
      Ψ (polarDiscPoint r (Circle.exp (θ j / 2))) ∈ spoke γ (a j).val '' Ioo (0 : I) 1 :=
    retained_source_short_ray w hquot (hg j) (θ j) (hθ0 j) (hθP j)
      (hray j) r hr0 (hrδ.trans (hδsin j))
  obtain ⟨Φ', d', f, v, hp', _, _, hdir, hd', hf, hbound, hf0, hmap, hv, hvpos⟩ :=
    exists_labeled_bounded_source_rim_directions hΨi hΨpos hΨ0 hΨnhd hp hpos d hd hδ
  have hcontact (j : J) := source_coordinate_ray_contact hγ hpV hp' d' hd' f v hf hf0
    hmap hv hvpos (fun u => (hbound u).le) (a j) (Circle.exp (θ j / 2)) (hrays j)
  have hminusC : Φ' (polarDiscPoint 1 (d' minus).val) ∈ C :=
    hcuff (hd' minus 1 zero_lt_one)
  have hminusp : Φ' (polarDiscPoint 1 (d' minus).val) ≠ p := by
    intro hh
    have heq : polarDiscPoint 1 (d' minus).val = polarCentre :=
      hp'.inj (hh.trans hp'.centre.symm)
    exact polarDiscPoint_one_ne_centre _ heq
  have hminusoff : Φ' (polarDiscPoint 1 (d' minus).val) ∉ range (fun x => π (Φ x)) :=
    collapsed_target_chart_avoids_fixed_cuff hfibre hinj hfix Φ hoff hminusC hminusp
  have hdi : Function.Injective (fun b => (d' b).val) := Subtype.val_injective.comp d'.injective
  apply horder.imp
  intro i j hij
  have hijne : i ≠ j := fun hh => by subst j; exact (lt_irrefl _ hij)
  have hi := hcontact i
  have hj := hcontact j
  have hα : 0 < θ i / 2 := half_pos (hθ0 i)
  have hαβ : θ i / 2 < θ j / 2 := div_lt_div_of_pos_right hij (by norm_num)
  have hβ : θ j / 2 < Real.pi := (section5RadiusCollapse_half_angle_bounds (hθ0 j) (hθP j)).2.1
  have hh := source_anchor_precedes_retained_pair w hquot f v hmap hv hvpos
    (hdi.ne (ha.ne hijne)) (hdi.ne (Ne.symm (hma i))) (hdi.ne (Ne.symm (hma j)))
    hα hαβ hβ hi.1 hj.1
    (fun u hu => (hi.2 u).mp (hu.trans hi.1))
    (fun u hu => (hj.2 u).mp (hu.trans hj.1)) hminusoff
    ((hbound _).le.trans (hδsin i)) ((hbound _).le.trans (hδsin j))
  simpa only [hdir] using hh

/-- An actual half-edge/rim bijection assigns directions to the
permanent words of any exact incidence row. These directions are
injective on that row and describe each edge's rim contacts exactly. -/
theorem exists_permanent_directions_of_halfedge_equiv
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar Γ γ) {p : OnePoint EuclideanPlane}
    (label : Γ.E ↪ ℕ) {xs : List ℕ}
    (hmem : ∀ r, r ∈ xs ↔ ∃ a : halfEdges Γ γ p, gm06PersistentHalfEdgeLabel label a = r)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (hp : IsPolar Γ p Φ)
    (d : halfEdges Γ γ p ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e})
    (hd : ∀ a, ∀ t : I, 0 < t → Φ (polarDiscPoint t (d a).val) ∈ range (spoke γ a.val)) :
    ∃ z : ℕ → Circle,
      (∀ a, z (gm06PersistentHalfEdgeLabel label a) = (d a).val) ∧
      InjOn z {r | r ∈ xs} ∧
      (∀ a : halfEdges Γ γ p, ∀ t : I, 0 < t →
        Φ (polarDiscPoint t (z (gm06PersistentHalfEdgeLabel label a))) ∈ range (spoke γ a.val)) ∧
      ∀ (f : Γ.E) (w : Circle), polarRimMap Φ w ∈ f.val ↔ ∃ r ∈ xs,
        z r = w ∧ (r = 2 * label f ∨ r = 2 * label f + 1) := by
  classical
  obtain ⟨ys, z, _, hymem, hz, hzi, _, _⟩ := exists_polar_rotation_row d
    (gm06PersistentHalfEdgeLabel label) (gm06PersistentHalfEdgeLabel_injective label)
  have hxy (r : ℕ) : r ∈ xs ↔ r ∈ ys := (hmem r).trans (hymem r).symm
  refine ⟨z, hz, fun _ ha _ hb heq => hzi ((hxy _).mp ha) ((hxy _).mp hb) heq,
    fun a t ht => by rw [hz]; exact hd a t ht, ?_⟩
  intro f w
  constructor
  · intro hw
    obtain ⟨a, ha⟩ := d.surjective ⟨w, f.val, f.property, hw⟩
    have hwa : (d a).val = w := congrArg Subtype.val ha
    have hwe := polar_rim_mem_edge_of_halfedge_ray hγ hp a (d a).val (hd a)
    rw [hwa] at hwe
    have heq : a.val.1 = f.val := Γ.edge_eq_of_mem a.property.1 f.property hwe hw
    have hflabel : label ⟨a.val.1, a.property.1⟩ = label f :=
      congrArg label (Subtype.ext heq)
    refine ⟨gm06PersistentHalfEdgeLabel label a, (hmem _).mpr ⟨a, rfl⟩,
      (hz a).trans hwa, ?_⟩
    simp only [gm06PersistentHalfEdgeLabel, hflabel]
    cases a.val.2 <;> simp
  · rintro ⟨r, hr, hrw, hcode⟩
    obtain ⟨a, ha⟩ := (hmem r).mp hr
    have haw : (d a).val = w := (hz a).symm.trans ((congrArg z ha).trans hrw)
    have hcode' : label ⟨a.val.1, a.property.1⟩ = label f := by
      have hbit : a.val.2.toNat ≤ 1 := by cases a.val.2 <;> decide
      change 2 * label ⟨a.val.1, a.property.1⟩ + a.val.2.toNat = r at ha
      rcases hcode with hcode | hcode <;> omega
    have heq : a.val.1 = f.val := congrArg Subtype.val (label.injective hcode')
    have hw := polar_rim_mem_edge_of_halfedge_ray hγ hp a (d a).val (hd a)
    simpa only [haw, heq] using hw


/-- With the concrete signed cuff curves, the actual quotient
coordinates give the complete positive interpretation of all three
finite splice forms. The target block order is proved above and
the two cuff sides are read in the positive exponential chart. -/
theorem persistent_rotation_row_of_collapsed_source_block
    {J : Type*} [Fintype J]
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar Γ γ) {p : OnePoint EuclideanPlane} (hpV : p ∈ Γ.V)
    {q : ℂ} (hpc : p = toSph q) (hq : ‖q‖ = 1 / 2)
    {scale : ℝ} (hscale : 0 < scale)
    {π : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane)}
    {A C : Set (OnePoint EuclideanPlane)}
    (hfibre : π ⁻¹' {p} = A) (hinj : InjOn π Aᶜ) (hfix : ∀ x ∈ C, π x = x)
    {Φ Ψ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (w : Circle)
    (hquot : ∀ x, Ψ (section5CollapsedRadiusDiscPoint x) =
      π (Φ (section5RotateDisc w x)))
    (hΨi : Function.Injective Ψ) (hΨpos : GM06PositivePolar Ψ)
    (hΨ0 : Ψ polarCentre = p) (hΨnhd : p ∈ interior (range Ψ))
    (hoff : Disjoint (range Φ) C)
    (minus plus : halfEdges Γ γ p) (hmp : minus ≠ plus)
    (hcuff : range (spoke γ minus.val) ⊆ C)
    (hminus : ∀ t, spoke γ minus.val t = toSph (q * Complex.exp
      ((scale : ℂ) * (t : ℂ) * (Circle.exp (-(Real.pi / 2)) : ℂ))))
    (hplus : ∀ t, spoke γ plus.val t = toSph (q * Complex.exp
      ((scale : ℂ) * (t : ℂ) * (Circle.exp (Real.pi / 2) : ℂ))))
    (a : J → halfEdges Γ γ p) (ha : Function.Injective a)
    (hma : ∀ j, minus ≠ a j) (hpa : ∀ j, plus ≠ a j)
    {G : Drawing ClosedCylinder} (hG : G.IsProper)
    (hordinary : ∀ j, ∃ e ∈ G.E, (a j).val.1 = cylinderToSphere '' e)
    (g : J → I → OnePoint EuclideanPlane) (hg : ∀ j t, spoke γ (a j).val t = π (g j t))
    (θ : J → ℝ) (hθ0 : ∀ j, 0 < θ j) (hθP : ∀ j, θ j < 2 * Real.pi)
    (hray : ∀ j, ∀ t : I, 0 < t →
      Φ (polarDiscPoint t (w * Circle.exp (θ j))) ∈ g j '' Ioo (0 : I) 1)
    (label : Γ.E ↪ ℕ) {js : List J} (horder : js.Pairwise (fun i j => θ i < θ j))
    {xs : List ℕ} (hnd : xs.Nodup)
    (hmem : ∀ r, r ∈ xs ↔ ∃ b : halfEdges Γ γ p, gm06PersistentHalfEdgeLabel label b = r)
    (hforms :
      xs = gm06PersistentHalfEdgeLabel label minus ::
        (js.map (fun j => gm06PersistentHalfEdgeLabel label (a j)) ++ [gm06PersistentHalfEdgeLabel label plus]) ∨
      xs = js.map (fun j => gm06PersistentHalfEdgeLabel label (a j)) ++
        [gm06PersistentHalfEdgeLabel label plus, gm06PersistentHalfEdgeLabel label minus] ∨
      xs = gm06PersistentHalfEdgeLabel label plus :: gm06PersistentHalfEdgeLabel label minus ::
        js.map (fun j => gm06PersistentHalfEdgeLabel label (a j))) :
    GM06PersistentRotationRowRep label γ p xs := by
  obtain ⟨Φ₀, d, hp, hpos, hd⟩ := exists_positive_polar_chart hγ hpV
    ⟨complexPlane q, hpc.symm⟩
  obtain ⟨z, hz, hzi, hspoke, hlabel⟩ :=
    exists_permanent_directions_of_halfedge_equiv hγ label hmem hp d hd
  have hblock := collapsed_source_block_order hγ hpV hfibre hinj hfix w hquot hΨi hΨpos
    hΨ0 hΨnhd hoff hp hpos d hd minus hcuff a ha hma g hg θ hθ0 hθP hray horder
  have hblock' : (js.map (fun j => gm06PersistentHalfEdgeLabel label (a j))).Pairwise
      (fun i j => CircleCyclic (z (gm06PersistentHalfEdgeLabel label minus)) (z i) (z j)) := by
    apply List.pairwise_map.mpr
    simpa only [hz] using hblock
  have hlast : ∀ r ∈ js.map (fun j => gm06PersistentHalfEdgeLabel label (a j)),
      CircleCyclic (z (gm06PersistentHalfEdgeLabel label minus)) (z r)
        (z (gm06PersistentHalfEdgeLabel label plus)) := by
    intro r hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    obtain ⟨e, he, haje⟩ := hordinary j
    simpa only [hz] using source_signed_cuff_order hγ hq hpc hpV hscale hp hpos d hd
      minus plus (a j) hmp (hma j) (hpa j) hminus hplus hG he haje
  exact persistent_rotation_row_of_three_cuff_forms label hp hpos hforms z hnd hmem
    hzi hblock' hlast hspoke hlabel

end GraphMinor.GM06
