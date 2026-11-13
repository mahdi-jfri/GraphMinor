module

public import GraphMinor.GM06.Alg57InputRep
public import GraphMinor.Compute.GM06SpliceRotations
public import GraphMinor.Compute.GM06DartMate
import GraphMinor.Compute.GM06ContractRotationData
import GraphMinor.GM06.Section5CollapsePolar
import GraphMinor.GM06.Section5ContractedEdgeParam

/-!
# Rotation rows with permanent edge labels

The reductions of VI (5.7), page 133, leave gaps in the original
edge labels. A current row is therefore interpreted by an injection
from current edges into the permanent labels. The two directed ends
still have words twice that label and twice that label plus one.
The positive polar-chart meaning is the same as for the input.

At a vertex whose chart is fixed by a contraction, the old row
continues to describe its actual positive rotation. The proof uses
the surviving-edge and directed-end bijections, exact image spokes,
and fixed-chart transport. At the collapsed source, the computed
splice has exactly the surviving directed ends, with no duplicates.
The cyclic order at that source is a separate geometric assertion.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The directed word of an actual end, using permanent edge labels. -/
@[expose] def gm06PersistentHalfEdgeLabel
    {S : Type*} [TopologicalSpace S] {G : Drawing S}
    {γ : Set S → I → S} {v : S} (label : G.E ↪ ℕ) (a : halfEdges G γ v) : ℕ :=
  2 * label ⟨a.val.1, a.property.1⟩ + a.val.2.toNat

/-- Current edges may retain nonconsecutive original labels. The
row lists precisely their actual ends, in positive polar order. -/
@[expose] def GM06PersistentRotationRowRep
    {G : Drawing (OnePoint EuclideanPlane)} (label : G.E ↪ ℕ)
    (γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane)
    (v : OnePoint EuclideanPlane) (xs : List ℕ) : Prop :=
  xs.Nodup ∧
  (∀ r, r ∈ xs ↔ ∃ a : halfEdges G γ v, gm06PersistentHalfEdgeLabel label a = r) ∧
  (xs.length ≤ 1 ∨ ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (z : ℕ → Circle),
    IsPolar G v Φ ∧ GM06PositivePolar Φ ∧ Set.InjOn z {r | r ∈ xs} ∧
    xs.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)) ∧
    (∀ a : halfEdges G γ v, ∀ t : I, 0 < t →
      Φ (polarDiscPoint t (z (gm06PersistentHalfEdgeLabel label a))) ∈ range (spoke γ a.val)) ∧
    ∀ (f : G.E) (w : Circle),
      polarRimMap Φ w ∈ f.val ↔ ∃ r ∈ xs,
        z r = w ∧ (r = 2 * label f ∨ r = 2 * label f + 1))

/-- The input edge enumeration induces its ordinary permanent labels. -/
@[expose] def gm06InputEdgeLabels {S : Type*} [TopologicalSpace S]
    {G : Drawing S} {m : ℕ} (edge : Fin m ≃ G.E) : G.E ↪ ℕ :=
  ⟨fun f => (edge.symm f).val, Fin.val_injective.comp edge.symm.injective⟩

/-- The input rotation interpretation is the initial case of the
permanent-label interpretation used after reductions. -/
theorem GM06SuccessorRotationRowRep.to_persistent
    {G : Drawing (OnePoint EuclideanPlane)} {m : ℕ} {edge : Fin m ≃ G.E}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {v : OnePoint EuclideanPlane} {xs : List ℕ}
    (h : GM06SuccessorRotationRowRep edge γ v xs) :
    GM06PersistentRotationRowRep (gm06InputEdgeLabels edge) γ v xs := by
  refine ⟨h.1, h.2.1, ?_⟩
  rcases h.2.2 with hsmall | ⟨Φ, z, hp, hpos, hi, hs, hspoke, hlabel⟩
  · exact Or.inl hsmall
  · refine Or.inr ⟨Φ, z, hp, hpos, hi, hs, hspoke, ?_⟩
    intro f w
    have hh := hlabel (edge.symm f) w
    simpa only [edge.apply_symm_apply, gm06InputEdgeLabels, Function.Embedding.coeFn_mk] using hh

/-- Equal permanent directed words determine the edge and its
Boolean end, even when the two ends are viewed at different vertices. -/
theorem gm06PersistentHalfEdgeLabel_data_eq
    {S : Type*} [TopologicalSpace S] {G : Drawing S}
    {γ : Set S → I → S} {v w : S} (label : G.E ↪ ℕ)
    (a : halfEdges G γ v) (b : halfEdges G γ w)
    (hab : gm06PersistentHalfEdgeLabel label a = gm06PersistentHalfEdgeLabel label b) :
    a.val = b.val := by
  have ha : a.val.2.toNat ≤ 1 := by cases a.val.2 <;> decide
  have hb : b.val.2.toNat ≤ 1 := by cases b.val.2 <;> decide
  have hcode : 2 * label ⟨a.val.1, a.property.1⟩ + a.val.2.toNat =
      2 * label ⟨b.val.1, b.property.1⟩ + b.val.2.toNat := hab
  have heq : label ⟨a.val.1, a.property.1⟩ = label ⟨b.val.1, b.property.1⟩ := by omega
  have he : a.val.1 = b.val.1 := congrArg Subtype.val (label.injective heq)
  have hbool : a.val.2 = b.val.2 := by
    have hh : a.val.2.toNat = b.val.2.toNat := by omega
    cases h₁ : a.val.2 <;> cases h₂ : b.val.2 <;> simp_all
  exact Prod.ext he hbool

/-- Permanent directed labels distinguish both ends, including the
two ends of a loop, whenever the edge labels are injective. -/
theorem gm06PersistentHalfEdgeLabel_injective
    {S : Type*} [TopologicalSpace S] {G : Drawing S}
    {γ : Set S → I → S} {v : S} (label : G.E ↪ ℕ) :
    Function.Injective (gm06PersistentHalfEdgeLabel (γ := γ) (v := v) label) :=
  fun a b hab => Subtype.ext (gm06PersistentHalfEdgeLabel_data_eq label a b hab)

/-- A fixed old positive chart interprets the same permanent row
at an unchanged vertex of the actual contracted drawing. The
labels of surviving edges are kept, not renumbered. -/
theorem persistent_rotation_row_of_fixed_edge_collapse
    {G G' : Drawing (OnePoint EuclideanPlane)}
    {e : Set (OnePoint EuclideanPlane)} {s v w : OnePoint EuclideanPlane}
    (hl : G.toGraph.IsLink e s v) (hvs : v ≠ s)
    (π : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (hfibre : π ⁻¹' {s} = closure e) (hi : InjOn π (closure e)ᶜ)
    (hsurj : Function.Surjective π)
    (hV : G'.V = π '' G.V) (hE : G'.E = (image π) '' (G.E \ {e}))
    (hU : G'.U = π '' G.U)
    {γ γ' : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar G γ)
    (hpar : ∀ f ∈ G.E, f ≠ e → ∀ t, γ' (π '' f) t = π (γ f t))
    (hw : w ∉ closure e) (hπw : π w = w)
    (label : G.E ↪ ℕ) (label' : G'.E ↪ ℕ)
    (hlabel' : ∀ f (hf : f ∈ G.E) (hne : f ≠ e),
      label' ⟨π '' f, hE ▸ mem_image_of_mem (image π) ⟨hf, hne⟩⟩ = label ⟨f, hf⟩)
    {xs : List ℕ} (hnd : xs.Nodup)
    (hmem : ∀ r, r ∈ xs ↔ ∃ a : halfEdges G γ w, gm06PersistentHalfEdgeLabel label a = r)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {z : ℕ → Circle}
    (hp : IsPolar G w Φ) (hpos : GM06PositivePolar Φ)
    (hfixed : ∀ x, π (Φ x) = Φ x)
    (hzi : Set.InjOn z {r | r ∈ xs})
    (hs : xs.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)))
    (hspoke : ∀ a : halfEdges G γ w, ∀ t : I, 0 < t →
      Φ (polarDiscPoint t (z (gm06PersistentHalfEdgeLabel label a))) ∈ range (spoke γ a.val))
    (hlabel : ∀ (f : G.E) (q : Circle),
      polarRimMap Φ q ∈ f.val ↔ ∃ r ∈ xs,
        z r = q ∧ (r = 2 * label f ∨ r = 2 * label f + 1)) :
    GM06PersistentRotationRowRep label' γ' w xs := by
  obtain ⟨η, hη, hspokes⟩ := exists_halfedge_equiv_of_closed_edge_collapse
    hl hvs π hfibre hi hE hγ hpar hw hπw
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
    have hb : (η a).val.2 = a.val.2 := hb₀
    have hlabels : label' ⟨(η a).val.1, (η a).property.1⟩ =
        label ⟨a.val.1, a.property.1⟩ :=
      (congrArg label' he).trans (hlabel' a.val.1 a.property.1 (hne a))
    simp only [gm06PersistentHalfEdgeLabel, hlabels, hb]
  refine ⟨hnd, ?_, Or.inr ⟨Φ, z, ?_, hpos, hzi, hs, ?_, ?_⟩⟩
  · intro r
    constructor
    · intro hr
      obtain ⟨a, ha⟩ := (hmem r).mp hr
      exact ⟨η a, (hcode a).trans ha⟩
    · rintro ⟨b, hb⟩
      obtain ⟨a, rfl⟩ := η.surjective b
      exact (hmem r).mpr ⟨a, (hcode a).symm.trans hb⟩
  · exact isPolar_of_closed_edge_collapse_fixed_chart hl π hfibre hi hsurj hV hE hU hp hfixed
  · intro b t ht
    obtain ⟨a, rfl⟩ := η.surjective b
    rw [hcode]
    obtain ⟨u, hu⟩ := hspoke a t ht
    refine ⟨u, ?_⟩
    rw [hspokes, hu, hfixed]
  · intro f q
    obtain ⟨ηE, hηE⟩ := exists_edge_equiv_of_closed_edge_collapse hl hvs π hi hE
    let a := ηE.symm f
    have he : π '' a.val = f.val := (hηE a).symm.trans
      (congrArg Subtype.val (ηE.apply_symm_apply f))
    have hlab : label' f = label ⟨a.val, a.property.1⟩ := by
      have hh : f = ⟨π '' a.val, hE ▸ mem_image_of_mem (image π) a.property⟩ :=
        Subtype.ext he.symm
      exact (congrArg label' hh).trans (hlabel' a.val a.property.1 a.property.2)
    calc
      polarRimMap Φ q ∈ f.val ↔ polarRimMap Φ q ∈ π '' a.val := by rw [he]
      _ ↔ polarRimMap Φ q ∈ a.val := mem_image_iff_of_fixed_collapse hfibre hi
        (disjoint_open_edge_closed_link hl hvs a.property.1 a.property.2)
        (hfixed (polarDiscPoint 1 q))
      _ ↔ ∃ r ∈ xs, z r = q ∧
          (r = 2 * label' f ∨ r = 2 * label' f + 1) := by
        rw [hlab]
        exact hlabel ⟨a.val, a.property.1⟩ q

private theorem halfedge_vertex_eq_of_data_eq
    {S : Type*} [TopologicalSpace S] {G : Drawing S} {γ : Set S → I → S} {v w : S}
    (a : halfEdges G γ v) (b : halfEdges G γ w) (heq : a.val = b.val) : v = w :=
  a.property.2.symm.trans
    ((congrArg (fun p : Set S × Bool => γ p.1 (endOf p.2)) heq).trans b.property.2)

private theorem halfedge_unique_at_nonloop_end
    {S : Type*} [TopologicalSpace S] {G : Drawing S} {γ : Set S → I → S} {v w : S}
    (a b : halfEdges G γ v) (c : halfEdges G γ w) (hvw : v ≠ w)
    (hab : a.val.1 = b.val.1) (hbc : b.val.1 = c.val.1) : a = b := by
  have hne (u : halfEdges G γ v) (hu : u.val.1 = c.val.1) : u.val.2 ≠ c.val.2 := by
    intro hh
    exact hvw (halfedge_vertex_eq_of_data_eq u c (Prod.ext hu hh))
  have ha := hne a (hab.trans hbc)
  have hb := hne b hbc
  have hbool : a.val.2 = b.val.2 := by
    cases h₁ : a.val.2 <;> cases h₂ : b.val.2 <;> cases h₃ : c.val.2 <;> simp_all
  exact Subtype.ext (Prod.ext hab hbool)

/-- The two ends of a non-loop edge are exactly the two numeric
mate words. Distinct endpoint vertices force distinct Boolean ends. -/
theorem gm06PersistentHalfEdgeLabel_mate
    {S : Type*} [TopologicalSpace S] {G : Drawing S} {γ : Set S → I → S} {v w : S}
    (label : G.E ↪ ℕ) (a : halfEdges G γ v) (b : halfEdges G γ w)
    (hvw : v ≠ w) (he : a.val.1 = b.val.1) :
    gm06PersistentHalfEdgeLabel label b = Compute.gm06DartMate (gm06PersistentHalfEdgeLabel label a) := by
  have hbool : a.val.2 ≠ b.val.2 := fun hh =>
    hvw (halfedge_vertex_eq_of_data_eq a b (Prod.ext he hh))
  have hlabels : label ⟨a.val.1, a.property.1⟩ = label ⟨b.val.1, b.property.1⟩ :=
    congrArg label (Subtype.ext he)
  cases h₀ : a.val.2 <;> cases h₁ : b.val.2 <;>
    simp_all [gm06PersistentHalfEdgeLabel, Compute.gm06DartMate, Nat.add_mod]

/-- The computed source splice has exactly the directed words of
the actual contracted source, without duplicating a loop end.
This proves its incidence and uniqueness, separately from the
geometric cyclic-order part of Lemma 8. -/
theorem spliced_rotation_source_incidence
    {G G' : Drawing (OnePoint EuclideanPlane)}
    {e : Set (OnePoint EuclideanPlane)} {s v : OnePoint EuclideanPlane}
    (hl : G.toGraph.IsLink e s v) (hvs : v ≠ s)
    (π : OnePoint EuclideanPlane → OnePoint EuclideanPlane)
    (hfibre : π ⁻¹' {s} = closure e) (hi : InjOn π (closure e)ᶜ)
    (hE : G'.E = (image π) '' (G.E \ {e}))
    {γ γ' : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar G γ)
    (hpar : ∀ f ∈ G.E, f ≠ e → ∀ t, γ' (π '' f) t = π (γ f t))
    (label : G.E ↪ ℕ) (label' : G'.E ↪ ℕ)
    (hlabel' : ∀ f (hf : f ∈ G.E) (hne : f ≠ e),
      label' ⟨π '' f, hE ▸ mem_image_of_mem (image π) ⟨hf, hne⟩⟩ = label ⟨f, hf⟩)
    (a₀ : halfEdges G γ s) (a₁ : halfEdges G γ v)
    (ha₀ : a₀.val.1 = e) (ha₁ : a₁.val.1 = e)
    {xs ys : List ℕ} (hx : GM06PersistentRotationRowRep label γ s xs)
    (hy : GM06PersistentRotationRowRep label γ v ys) :
    let d := gm06PersistentHalfEdgeLabel label a₀
    let q := Compute.gm06DartMate d
    let row := Compute.gm06SplicedRotation xs ys (xs.idxOf d) (ys.idxOf q)
    row.Nodup ∧ ∀ r, r ∈ row ↔
      ∃ b : halfEdges G' γ' s, gm06PersistentHalfEdgeLabel label' b = r := by
  dsimp only
  rw [← gm06PersistentHalfEdgeLabel_mate label a₀ a₁ hvs.symm (ha₀.trans ha₁.symm)]
  let d := gm06PersistentHalfEdgeLabel label a₀
  let q := gm06PersistentHalfEdgeLabel label a₁
  have hd : d ∈ xs := (hx.2.1 d).mpr ⟨a₀, rfl⟩
  have hq : q ∈ ys := (hy.2.1 q).mpr ⟨a₁, rfl⟩
  have hp : xs.idxOf d < xs.length := List.idxOf_lt_length_iff.mpr hd
  have hq' : ys.idxOf q < ys.length := List.idxOf_lt_length_iff.mpr hq
  have hgetd : xs[xs.idxOf d] = d := List.getElem_idxOf hp
  have hgetq : ys[ys.idxOf q] = q := List.getElem_idxOf hq'
  have hdis : List.Disjoint xs ys := by
    intro r hr hs
    obtain ⟨a, ha⟩ := (hx.2.1 r).mp hr
    obtain ⟨b, hb⟩ := (hy.2.1 r).mp hs
    have he := gm06PersistentHalfEdgeLabel_data_eq label a b (ha.trans hb.symm)
    exact hvs (halfedge_vertex_eq_of_data_eq a b he).symm
  have hsource (a : halfEdges G γ s) : a.val.1 ≠ e ↔ gm06PersistentHalfEdgeLabel label a ≠ d := by
    constructor
    · intro hne heq
      have hh := gm06PersistentHalfEdgeLabel_injective label heq
      exact hne (hh ▸ ha₀)
    · intro hne heq
      have hh := halfedge_unique_at_nonloop_end a a₀ a₁ hvs.symm
        (heq.trans ha₀.symm) (ha₀.trans ha₁.symm)
      exact hne (congrArg (gm06PersistentHalfEdgeLabel label) hh)
  have htarget (a : halfEdges G γ v) : a.val.1 ≠ e ↔ gm06PersistentHalfEdgeLabel label a ≠ q := by
    constructor
    · intro hne heq
      have hh := gm06PersistentHalfEdgeLabel_injective label heq
      exact hne (hh ▸ ha₁)
    · intro hne heq
      have hh := halfedge_unique_at_nonloop_end a a₁ a₀ hvs
        (heq.trans ha₁.symm) (ha₁.trans ha₀.symm)
      exact hne (congrArg (gm06PersistentHalfEdgeLabel label) hh)
  obtain ⟨η, hη₀, hη₁, _, _⟩ := exists_contracted_source_halfedge_equiv hl hvs π hfibre hi hE hγ hpar
  have hcode {w : OnePoint EuclideanPlane} (a : halfEdges G γ w) (ha : a.val.1 ≠ e)
      (b : halfEdges G' γ' s) (heq : b.val = (π '' a.val.1, a.val.2)) :
      gm06PersistentHalfEdgeLabel label' b = gm06PersistentHalfEdgeLabel label a := by
    have hedge : (⟨b.val.1, b.property.1⟩ : G'.E) =
        ⟨π '' a.val.1, hE ▸ mem_image_of_mem (image π) ⟨a.property.1, ha⟩⟩ :=
      Subtype.ext (congrArg Prod.fst heq)
    have hb₀ := congrArg (fun p : Set (OnePoint EuclideanPlane) × Bool => p.2) heq
    have hlabels := (congrArg label' hedge).trans (hlabel' a.val.1 a.property.1 ha)
    simp only [gm06PersistentHalfEdgeLabel, hlabels, hb₀]
  refine ⟨Compute.gm06SplicedRotation_nodup hx.1 hy.1 hdis _ _, ?_⟩
  intro r
  have hm := Compute.gm06SplicedRotation_mem_iff hx.1 hy.1 hp hq' r
  rw [hgetd, hgetq] at hm
  constructor
  · intro hr
    rcases hm.mp hr with ⟨hr, hrd⟩ | ⟨hr, hrq⟩
    · obtain ⟨a, ha⟩ := (hx.2.1 r).mp hr
      have hne : a.val.1 ≠ e := (hsource a).mpr (ha.symm ▸ hrd)
      let a' := (⟨a, hne⟩ : {a : halfEdges G γ s // a.val.1 ≠ e})
      exact ⟨η (.inl a'), (hcode a hne _ (hη₀ a')).trans ha⟩
    · obtain ⟨a, ha⟩ := (hy.2.1 r).mp hr
      have hne : a.val.1 ≠ e := (htarget a).mpr (ha.symm ▸ hrq)
      let a' := (⟨a, hne⟩ : {a : halfEdges G γ v // a.val.1 ≠ e})
      exact ⟨η (.inr a'), (hcode a hne _ (hη₁ a')).trans ha⟩
  · rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := η.surjective b
    apply hm.mpr
    cases a with
    | inl a =>
      left
      have hc := hcode a.val a.property _ (hη₀ a)
      have hc' : gm06PersistentHalfEdgeLabel label a.val = r := hc.symm.trans hb
      exact ⟨(hx.2.1 r).mpr ⟨a.val, hc'⟩, hc' ▸ (hsource a.val).mp a.property⟩
    | inr a =>
      right
      have hc := hcode a.val a.property _ (hη₁ a)
      have hc' : gm06PersistentHalfEdgeLabel label a.val = r := hc.symm.trans hb
      exact ⟨(hy.2.1 r).mpr ⟨a.val, hc'⟩, hc' ▸ (htarget a.val).mp a.property⟩

end GraphMinor.GM06
