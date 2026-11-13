module

public import GraphMinor.GM06.Alg57PersistentRotations
public import GraphMinor.GM06.Alg57RotationRestriction
import GraphMinor.GM06.Section5ContractedEdgeParam
import GraphMinor.GM06.Section5CollapsePolar
import GraphMinor.GM06.Section5SmallPolar
import GraphMinor.GM06.Section5PolarShrink
import GraphMinor.GM06.Section5PolarDiscInterior

/-!
# Rotation rows at vertices moved by the rectangular collapse

In Lemma 8 of the implementation of VI (5.7), page 133, a retained
vertex may lie inside the support of the rectangular collapse.
First shrink its old positive chart away from the collapsed edge.
Move this chart by the collapse. Its rays are image spokes, its
positive winding follows along the explicit capped homotopy, and
the unchanged permanent words give exactly its new directed ends.
No fixed-chart assumption or new rotation order is supplied.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- A current permanent row can be read in a positive chart in any
prescribed open neighbourhood of its vertex. The same labels and
angles continue to interpret its rays and rim. -/
theorem GM06PersistentRotationRowRep.exists_small_chart
    {G : Drawing (OnePoint EuclideanPlane)} {label : G.E ↪ ℕ}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {v : OnePoint EuclideanPlane} {xs : List ℕ}
    (hrow : GM06PersistentRotationRowRep label γ v xs) (hlarge : 1 < xs.length)
    {O : Set (OnePoint EuclideanPlane)} (hO : IsOpen O) (hv : v ∈ O) :
    ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (z : ℕ → Circle),
      IsPolar G v Φ ∧ GM06PositivePolar Φ ∧ range Φ ⊆ O ∧
      Set.InjOn z {r | r ∈ xs} ∧
      xs.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)) ∧
      (∀ a : halfEdges G γ v, ∀ t : I, 0 < t →
        Φ (polarDiscPoint t (z (gm06PersistentHalfEdgeLabel label a))) ∈ range (spoke γ a.val)) ∧
      ∀ (f : G.E) (w : Circle), polarRimMap Φ w ∈ f.val ↔
        ∃ r ∈ xs, z r = w ∧ (r = 2 * label f ∨ r = 2 * label f + 1) := by
  rcases hrow.2.2 with hsmall | ⟨Φ, z, hp, hpos, hi, hs, hspoke, hlabel⟩
  · exact False.elim ((not_lt_of_ge hsmall) hlarge)
  obtain ⟨c, hc, Ψ, hΨ, hΨO, hscale⟩ := exists_small_polar_chart_with_factor
    (IsSphere.isClosedSurface
      (show IsSphere (OnePoint EuclideanPlane) from ⟨Homeomorph.refl _⟩)).1 hp hO hv
  refine ⟨Ψ, z, hΨ, hpos.radial_restriction hp.inj c hc hscale, hΨO, hi, hs, ?_, ?_⟩
  · intro a t ht
    rw [hscale, discScale_polarDiscPoint]
    exact hspoke a (c * t) (mul_pos hc ht)
  · intro f w
    have hn : IsGammaNice G f.val :=
      ⟨{f.val}, singleton_subset_iff.mpr (Or.inl (Or.inr f.property)), by simp⟩
    exact (polar_rim_mem_nice_iff_of_radial_restriction hp c hc hscale hn w).symm.trans (hlabel f w)

/-- The positive permanent row at every vertex off the collapsed
edge is unchanged, even if the rectangle moves that vertex. All
new chart and end data are derived from the actual collapse. -/
theorem persistent_rotation_row_of_capped_rectangle_collapse
    {G G' : Drawing (OnePoint EuclideanPlane)}
    {e : Set (OnePoint EuclideanPlane)} {s v w : OnePoint EuclideanPlane}
    (hl : G.toGraph.IsLink e s v) (hvs : v ≠ s)
    (π : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (hfibre : π ⁻¹' {s} = closure e) (hi : InjOn π (closure e)ᶜ)
    (hsurj : Function.Surjective π)
    (hopen : ∀ U : Set (OnePoint EuclideanPlane), IsOpen U →
      Disjoint U (closure e) → IsOpen (π '' U))
    (hV : G'.V = π '' G.V) (hE : G'.E = (image π) '' (G.E \ {e}))
    (hU : G'.U = π '' G.U)
    {γ γ' : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar G γ)
    (hpar : ∀ f ∈ G.E, f ≠ e → ∀ t, γ' (π '' f) t = π (γ f t))
    (hw : w ∉ closure e)
    {D : Set ClosedCylinder} (E : Section5CollapseRectangle ≃ₜ D)
    (H : C(I × ClosedCylinder, ClosedCylinder))
    (K : C(I × OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (hchart : ∀ t z, H (t, (E z).val) = (E (section5RectangleCollapseHomotopy (t, z))).val)
    (hout : ∀ x ∉ D, ∀ t, H (t, x) = x)
    (hK : ∀ t x, K (t, cylinderToSphere x) = cylinderToSphere (H (t, x)))
    (hoff : ∀ y ∉ range cylinderToSphere, ∀ t, K (t, y) = y)
    (hK0 : ∀ y, K (0, y) = y) (hK1 : ∀ y, K (1, y) = π y)
    (hsegment : closure e = cylinderToSphere ''
      ((fun z => (E z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1}))
    (label : G.E ↪ ℕ) (label' : G'.E ↪ ℕ)
    (hlabel' : ∀ f (hf : f ∈ G.E) (hne : f ≠ e),
      label' ⟨π '' f, hE ▸ mem_image_of_mem (image π) ⟨hf, hne⟩⟩ = label ⟨f, hf⟩)
    {xs : List ℕ} (hrow : GM06PersistentRotationRowRep label γ w xs) :
    GM06PersistentRotationRowRep label' γ' (π w) xs := by
  obtain ⟨η, hη, hspokes⟩ := exists_halfedge_equiv_of_closed_edge_collapse_mapped
    hl hvs π hfibre hi hE hγ hpar hw
  have hne : ∀ a : halfEdges G γ w, a.val.1 ≠ e := by
    intro a hae
    apply hw
    have hh : w ∈ range (γ e) := ⟨endOf a.val.2, hae ▸ a.property.2⟩
    rwa [range_eq_closure_of_edgePar hγ hl.edge_mem] at hh
  have hcode : ∀ a, gm06PersistentHalfEdgeLabel label' (η a) =
      gm06PersistentHalfEdgeLabel label a := by
    intro a
    have he : (⟨(η a).val.1, (η a).property.1⟩ : G'.E) =
        ⟨π '' a.val.1, hE ▸ mem_image_of_mem (image π) ⟨a.property.1, hne a⟩⟩ :=
      Subtype.ext (congrArg Prod.fst (hη a))
    have hb₀ := congrArg (fun p : Set (OnePoint EuclideanPlane) × Bool => p.2) (hη a)
    have hlabels := (congrArg label' he).trans (hlabel' a.val.1 a.property.1 (hne a))
    simp only [gm06PersistentHalfEdgeLabel, hlabels, hb₀]
  refine ⟨hrow.1, ?_, ?_⟩
  · intro r
    constructor
    · intro hr
      obtain ⟨a, ha⟩ := (hrow.2.1 r).mp hr
      exact ⟨η a, (hcode a).trans ha⟩
    · rintro ⟨b, hb⟩
      obtain ⟨a, rfl⟩ := η.surjective b
      exact (hrow.2.1 r).mpr ⟨a, (hcode a).symm.trans hb⟩
  · by_cases hsmall : xs.length ≤ 1
    · exact Or.inl hsmall
    obtain ⟨Φ, z, hp, hpos, hΦe, hzi, hs, hspoke, hlabel⟩ :=
      hrow.exists_small_chart (by omega) isClosed_closure.isOpen_compl hw
    have hdis : Disjoint (range Φ) (closure e) := disjoint_left.mpr (fun _ hx => hΦe hx)
    have hp' := isPolar_of_closed_edge_collapse_mapped_chart hl π hfibre hi hsurj
      hopen hV hE hU hp hdis
    have hpos' : GM06PositivePolar (π.comp Φ) := hpos.capped_rectangle_image E H K
      hchart hout hK hoff hK0 hp.inj (by
        rw [← hsegment]
        exact hΦe (mem_range_self polarCentre))
      (fun x => (hK1 (Φ x)).symm)
    refine Or.inr ⟨π.comp Φ, z, hp', hpos', hzi, hs, ?_, ?_⟩
    · intro b t ht
      obtain ⟨a, rfl⟩ := η.surjective b
      rw [hcode]
      obtain ⟨u, hu⟩ := hspoke a t ht
      exact ⟨u, (hspokes a u).trans (congrArg π hu)⟩
    · intro f q
      obtain ⟨ηE, hηE⟩ := exists_edge_equiv_of_closed_edge_collapse hl hvs π hi hE
      let a := ηE.symm f
      have he : π '' a.val = f.val := (hηE a).symm.trans
        (congrArg Subtype.val (ηE.apply_symm_apply f))
      have hlab : label' f = label ⟨a.val, a.property.1⟩ := by
        have hh : f = ⟨π '' a.val, hE ▸ mem_image_of_mem (image π) a.property⟩ :=
          Subtype.ext he.symm
        exact (congrArg label' hh).trans (hlabel' a.val a.property.1 a.property.2)
      have hRim : polarRimMap (π.comp Φ) q ∈ f.val ↔ polarRimMap Φ q ∈ a.val := by
        rw [← he]
        change π (polarRimMap Φ q) ∈ π '' a.val ↔ polarRimMap Φ q ∈ a.val
        constructor
        · rintro ⟨x, hx, hxeq⟩
          have hdisEdge := disjoint_open_edge_closed_link hl hvs a.property.1 a.property.2
          have hxNot := disjoint_left.mp hdisEdge hx
          have hyNot := hΦe (mem_range_self (polarDiscPoint 1 q))
          exact hi hxNot hyNot hxeq ▸ hx
        · intro hx
          exact mem_image_of_mem π hx
      rw [hRim, hlab]
      exact hlabel ⟨a.val, a.property.1⟩ q

end GraphMinor.GM06
