module

public import GraphMinor.GM06.Alg57CurrentCuffEnds
import GraphMinor.GM06.Alg511CuffEnumeration
import GraphMinor.GM06.Section5NextContact
public import GraphMinor.GM06.Alg57SourceRotationForms
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5ContractedEdgeParam
import GraphMinor.GM11.EvenCircuit

/-!
# The actual ends at a current source of valency one

For the source splice in Lemma 8 of VI (5.7), page 133, the current
cuff-augmented drawing has only ordinary edges and its two cuff
families. At an initial vertex an incident cuff end is one of the
two prescribed inner cuff ends. If the ordinary valency is one,
any ordinary incident end is the selected non-loop end. These
facts identify the three labels used by the source-row calculation
from the actual current drawing, allowing permanent label gaps.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- Every augmented current edge is an active ordinary edge or
one of the two concrete cuff families. -/
theorem GM06CurrentDrawingRep.edge_cases
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) (f : (cylinderSphereDrawing rep.cuffed).E) :
    (∃ j : Fin rep.tagged.length, rep.tagged[j].2 = 1 ∧ f.val = cylinderToSphere '' rep.edge j) ∨
      (∃ i : Fin k, f.val = cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) ∨
      ∃ i : Fin k, f.val = cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1) := by
  obtain ⟨e, heG, heI, heO⟩ := alg511_exists_cuff_edge_equiv hG rep.subdrawing
    rep.cuffed_U rep.cuffed_V
  have hf : f.val ∈ (image cylinderToSphere) '' rep.cuffed.E := by
    simpa only [cylinderSphereDrawing_E] using f.property
  obtain ⟨g, hg, hgf⟩ := hf
  obtain ⟨a, ha⟩ := e.surjective ⟨g, hg⟩
  cases a with
  | inl a =>
    have hga : g = a.val := (congrArg Subtype.val ha).symm.trans (heG a)
    obtain ⟨j, hj, hje⟩ := rep.edge_cover a.val a.property
    exact Or.inl ⟨j, hj, hgf.symm.trans (congrArg (image cylinderToSphere) (hga.trans hje.symm))⟩
  | inr a =>
    cases a with
    | inl i =>
      have hgi : g = initialCuffGapCurve k i '' Ioo 0 1 :=
        (congrArg Subtype.val ha).symm.trans (heI i)
      exact Or.inr (Or.inl ⟨i, hgf.symm.trans (congrArg (image cylinderToSphere) hgi)⟩)
    | inr i =>
      have hgi : g = alg511OuterCuffGapCurve k i '' Ioo 0 1 :=
        (congrArg Subtype.val ha).symm.trans (heO i)
      exact Or.inr (Or.inr ⟨i, hgf.symm.trans (congrArg (image cylinderToSphere) hgi)⟩)

/-- An end at a current initial vertex is ordinary, the positive
end of the following inner gap, or the negative end of its predecessor. -/
theorem GM06CurrentDrawingRep.initial_halfedge_cases
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    (a : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
      (cylinderToSphere (cylinderM1Point k i))) :
    (∃ j : Fin rep.tagged.length, rep.tagged[j].2 = 1 ∧ a.val.1 = cylinderToSphere '' rep.edge j) ∨
      a.val = (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1), false) ∨
      a.val = (cylinderToSphere '' (initialCuffGapCurve k (finPredCycle i) '' Ioo 0 1), true) := by
  rcases rep.edge_cases hG ⟨a.val.1, a.property.1⟩ with h | ⟨j, hj⟩ | ⟨j, hj⟩
  · exact Or.inl h
  · change a.val.1 = _ at hj
    have hpoint := a.property.2
    change rep.par a.val.1 (endOf a.val.2) = cylinderToSphere (cylinderM1Point k i) at hpoint
    rw [hj, rep.inner_par] at hpoint
    cases hb : a.val.2
    · have heq : cylinderM1Point k j = cylinderM1Point k i := by
        apply injective_cylinderToSphere
        simpa only [hb, endOf, Bool.false_eq_true, ite_false,
          (initialCuffGapCurve_props hG j).1] using hpoint
      have hji := cylinderM1Point_injective hG.1 heq
      exact Or.inr (Or.inl (Prod.ext (by simpa only [hji] using hj) hb))
    · have heq : cylinderM1Point k (finSuccCycle j) = cylinderM1Point k i := by
        apply injective_cylinderToSphere
        simpa only [hb, endOf, ite_true, (initialCuffGapCurve_props hG j).2.1] using hpoint
      have hji := cylinderM1Point_injective hG.1 heq
      have hjpred : j = finPredCycle i := by
        rw [← hji, finPredCycle_finSuccCycle]
      exact Or.inr (Or.inr (Prod.ext (by simpa only [hjpred] using hj) hb))
  · change a.val.1 = _ at hj
    have hpoint := a.property.2
    change rep.par a.val.1 (endOf a.val.2) = cylinderToSphere (cylinderM1Point k i) at hpoint
    rw [hj, rep.outer_par] at hpoint
    have hh := congrArg (fun p : ClosedCylinder => p.val.1) (injective_cylinderToSphere hpoint)
    cases hb : a.val.2 <;>
      norm_num [endOf, alg511OuterCuffGapCurve, alg511CuffSwap, initialCuffGapCurve,
        cylinderPoint, cylinderM1Point] at hh

/-- The cylinder embedding carries a drawing link to its actual sphere image. -/
theorem cylinderSphereDrawing_isLink
    {F : Drawing ClosedCylinder} {e : Set ClosedCylinder} {s v : ClosedCylinder}
    (hl : F.toGraph.IsLink e s v) :
    (cylinderSphereDrawing F).toGraph.IsLink (cylinderToSphere '' e)
      (cylinderToSphere s) (cylinderToSphere v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cylinderSphereDrawing_E]
    exact mem_image_of_mem (image cylinderToSphere) hl.edge_mem
  · rw [cylinderSphereDrawing_V]
    exact mem_image_of_mem cylinderToSphere hl.left_mem
  · rw [cylinderSphereDrawing_V]
    exact mem_image_of_mem cylinderToSphere hl.right_mem
  · rw [isClosedEmbedding_cylinderToSphere.closure_image_eq, cylinderSphereDrawing_V,
      ← image_inter injective_cylinderToSphere, hl.2.2.2]
    simp

/-- A non-loop edge has only one directed end at either endpoint,
for any actual parametrization of its drawing. -/
theorem halfedge_eq_of_nonloop_edge
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar Γ γ) {e : Set (OnePoint EuclideanPlane)} {s v : OnePoint EuclideanPlane}
    (hl : Γ.toGraph.IsLink e s v) (hvs : v ≠ s)
    (a b : halfEdges Γ γ s) (ha : a.val.1 = e) (hb : b.val.1 = e) : a = b := by
  by_cases hbit : a.val.2 = b.val.2
  · exact Subtype.ext (Prod.ext (ha.trans hb.symm) hbit)
  have hsa : γ e (endOf a.val.2) = s := by rw [← ha]; exact a.property.2
  have hsb : γ e (endOf b.val.2) = s := by rw [← hb]; exact b.property.2
  have hends : γ e (endOf false) = s ∧ γ e (endOf true) = s := by
    cases ha' : a.val.2 <;> cases hb' : b.val.2 <;> simp_all
  have hv : v ∈ closure e ∩ Γ.V := by
    rw [hl.2.2.2]
    exact mem_insert_of_mem _ (mem_singleton _)
  rw [closure_inter_V_eq hγ hl.edge_mem, hends.1, hends.2] at hv
  exact False.elim (hvs (by simpa using hv))

/-- At ordinary valency one, every current ordinary end is the
selected non-loop end. The cuff augmentation adds no other ordinary end. -/
theorem GM06CurrentDrawingRep.ordinary_initial_halfedge_unique
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L) (i : Fin k)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v) (hvs : v ≠ cylinderM1Point k i)
    (a b : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
      (cylinderToSphere (cylinderM1Point k i)))
    (hb : b.val.1 = cylinderToSphere '' e)
    (ha : ∃ j : Fin rep.tagged.length, rep.tagged[j].2 = 1 ∧ a.val.1 = cylinderToSphere '' rep.edge j) :
    a = b := by
  obtain ⟨j, hj, haj⟩ := ha
  have he := (rep.links j hj).edge_mem
  have hs : cylinderToSphere (cylinderM1Point k i) ∈ closure a.val.1 := by
    rw [← range_eq_closure_of_edgePar rep.edgePar a.property.1]
    exact ⟨endOf a.val.2, a.property.2⟩
  rw [haj, isClosedEmbedding_cylinderToSphere.closure_image_eq] at hs
  obtain ⟨y, hy, hys⟩ := hs
  have hys' := injective_cylinderToSphere hys
  have hscl : cylinderM1Point k i ∈ closure (rep.edge j) := hys' ▸ hy
  have hje : rep.edge j = e := by
    by_contra hne
    exact not_mem_closure_edge_of_ne_red3 hval hl hvs he hne hscl
  have hFlink := (rep.subdrawing.isLink_iff hl.edge_mem).mp hl
  exact halfedge_eq_of_nonloop_edge rep.edgePar (cylinderSphereDrawing_isLink hFlink)
    (fun hh => hvs (injective_cylinderToSphere hh)) a b
    (haj.trans (congrArg (image cylinderToSphere) hje)) hb


/-- An ordinary current end cannot equal either end of an inner
cuff edge, since proper ordinary edges miss the cuff. -/
theorem GM06CurrentDrawingRep.ordinary_end_ne_inner_end
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) {p : OnePoint EuclideanPlane}
    (a b : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par p)
    {e : Set ClosedCylinder} (he : e ∈ G.E)
    (ha : a.val.1 = cylinderToSphere '' e) (j : Fin k)
    (hb : b.val.1 = cylinderToSphere '' (initialCuffGapCurve k j '' Ioo 0 1)) : a ≠ b := by
  intro hab
  have hh : cylinderToSphere '' e =
      cylinderToSphere '' (initialCuffGapCurve k j '' Ioo 0 1) :=
    ha.symm.trans ((congrArg (fun c => c.val.1) hab).trans hb)
  have heq := (Set.image_injective.mpr injective_cylinderToSphere) hh
  exact Set.disjoint_left.mp (alg511_cuff_edge_families_disjoint hG).1 he ⟨j, heq.symm⟩

/-- The three actual ends at a source of ordinary valency one are
its selected non-loop end and its two signed cuff ends. The latter
remain distinct even if the inner cuff is a single loop. -/
theorem GM06CurrentDrawingRep.initial_three_halfedges
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v) (hvs : v ≠ cylinderM1Point k i)
    (b : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
      (cylinderToSphere (cylinderM1Point k i)))
    (hb : b.val.1 = cylinderToSphere '' e) :
    ∃ minus plus : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
        (cylinderToSphere (cylinderM1Point k i)),
      minus ≠ plus ∧ minus ≠ b ∧ plus ≠ b ∧
      minus.val = (cylinderToSphere '' (initialCuffGapCurve k (finPredCycle i) '' Ioo 0 1), true) ∧
      plus.val = (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1), false) ∧
      gm06PersistentHalfEdgeLabel rep.label minus = 2 * (rep.tagged.length + (finPredCycle i).val) + 1 ∧
      gm06PersistentHalfEdgeLabel rep.label plus = 2 * (rep.tagged.length + i.val) ∧
      ∀ a, a = minus ∨ a = b ∨ a = plus := by
  obtain ⟨minus, plus, hmp, hm, hp, hml, hpl, _⟩ := rep.inner_cuff_ends i
  have hbm : b ≠ minus := rep.ordinary_end_ne_inner_end hG b minus hl.edge_mem hb
    (finPredCycle i) (congrArg Prod.fst hm)
  have hbp : b ≠ plus := rep.ordinary_end_ne_inner_end hG b plus hl.edge_mem hb
    i (congrArg Prod.fst hp)
  refine ⟨minus, plus, hmp, Ne.symm hbm, Ne.symm hbp, hm, hp, hml, hpl, ?_⟩
  intro a
  rcases rep.initial_halfedge_cases hG i a with ha | ha | ha
  · exact Or.inr (Or.inl (rep.ordinary_initial_halfedge_unique i hval hl hvs a b hb ha))
  · exact Or.inr (Or.inr (Subtype.ext (ha.trans hp.symm)))
  · exact Or.inl (Subtype.ext (ha.trans hm.symm))

/-- The explicit directions in a persistent row give a bijection
between actual directed ends and rim contacts, with exactly the
row's permanent labels. No choice of a different chart is needed. -/
theorem persistent_row_halfedge_equiv
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar Γ γ) {p : OnePoint EuclideanPlane}
    (label : Γ.E ↪ ℕ) {xs : List ℕ}
    (hmem : ∀ r, r ∈ xs ↔ ∃ a : halfEdges Γ γ p, gm06PersistentHalfEdgeLabel label a = r)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {z : ℕ → Circle}
    (hp : IsPolar Γ p Φ) (hzi : InjOn z {r | r ∈ xs})
    (hspoke : ∀ a : halfEdges Γ γ p, ∀ t : I, 0 < t →
      Φ (polarDiscPoint t (z (gm06PersistentHalfEdgeLabel label a))) ∈ range (spoke γ a.val))
    (hlabel : ∀ (f : Γ.E) (w : Circle),
      polarRimMap Φ w ∈ f.val ↔ ∃ r ∈ xs,
        z r = w ∧ (r = 2 * label f ∨ r = 2 * label f + 1)) :
    ∃ d : halfEdges Γ γ p ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e},
      ∀ a, (d a).val = z (gm06PersistentHalfEdgeLabel label a) := by
  classical
  let d : halfEdges Γ γ p → {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e} := fun a =>
    ⟨z (gm06PersistentHalfEdgeLabel label a), a.val.1, a.property.1,
      polar_rim_mem_edge_of_halfedge_ray hγ hp a _ (hspoke a)⟩
  have hinj : Function.Injective d := by
    intro a b hab
    apply gm06PersistentHalfEdgeLabel_injective label
    apply hzi ((hmem _).mpr ⟨a, rfl⟩) ((hmem _).mpr ⟨b, rfl⟩)
    exact congrArg Subtype.val hab
  have hsurj : Function.Surjective d := by
    intro w
    obtain ⟨e, he, hw⟩ := w.property
    obtain ⟨r, hr, hrw, _⟩ := (hlabel ⟨e, he⟩ w.val).mp hw
    obtain ⟨a, ha⟩ := (hmem r).mp hr
    refine ⟨a, Subtype.ext ?_⟩
    change z (gm06PersistentHalfEdgeLabel label a) = w.val
    rw [ha, hrw]
  exact ⟨Equiv.ofBijective d ⟨hinj, hsurj⟩, fun _ => rfl⟩


/-- The actual current source row is one of the three positive
cyclic orders used by the contraction program. Properness and the
concrete signed cuff curves determine the order, including for one path. -/
theorem GM06CurrentDrawingRep.initial_source_row_forms
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v) (hvs : v ≠ cylinderM1Point k i)
    (b : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
      (cylinderToSphere (cylinderM1Point k i)))
    (hb : b.val.1 = cylinderToSphere '' e) :
    let xs := x.rotations.getD (rep.source i).val []
    let neg := 2 * (rep.tagged.length + (finPredCycle i).val) + 1
    let pos := 2 * (rep.tagged.length + i.val)
    let edge := gm06PersistentHalfEdgeLabel rep.label b
    xs = [neg, edge, pos] ∨ xs = [edge, pos, neg] ∨ xs = [pos, neg, edge] := by
  classical
  dsimp only
  let xs := x.rotations.getD (rep.source i).val []
  have hrow := rep.rows (rep.source i) (rep.source_live i)
  rw [rep.source_point] at hrow
  obtain ⟨minus, plus, hmp, hmb, hpb, hm, hp, hml, hpl, hcases⟩ :=
    rep.initial_three_halfedges hG i hval hl hvs b hb
  have hi := gm06PersistentHalfEdgeLabel_injective (γ := rep.par)
    (v := cylinderToSphere (cylinderM1Point k i)) rep.label
  have hne : gm06PersistentHalfEdgeLabel rep.label minus ≠ gm06PersistentHalfEdgeLabel rep.label b :=
    fun hh => hmb (hi hh)
  have hnp : gm06PersistentHalfEdgeLabel rep.label minus ≠ gm06PersistentHalfEdgeLabel rep.label plus :=
    fun hh => hmp (hi hh)
  have hep : gm06PersistentHalfEdgeLabel rep.label b ≠ gm06PersistentHalfEdgeLabel rep.label plus :=
    fun hh => hpb (hi hh.symm)
  have hmem : ∀ r, r ∈ xs ↔
      r = gm06PersistentHalfEdgeLabel rep.label minus ∨
      r = gm06PersistentHalfEdgeLabel rep.label b ∨
      r = gm06PersistentHalfEdgeLabel rep.label plus := by
    intro r
    rw [hrow.2.1]
    constructor
    · rintro ⟨a, ha⟩
      rcases hcases a with rfl | rfl | rfl
      · exact Or.inl ha.symm
      · exact Or.inr (Or.inl ha.symm)
      · exact Or.inr (Or.inr ha.symm)
    · rintro (rfl | rfl | rfl)
      · exact ⟨minus, rfl⟩
      · exact ⟨b, rfl⟩
      · exact ⟨plus, rfl⟩
  have htrip : ([gm06PersistentHalfEdgeLabel rep.label minus,
      gm06PersistentHalfEdgeLabel rep.label b, gm06PersistentHalfEdgeLabel rep.label plus] : List ℕ).Nodup := by
    simp [hne, hnp, hep]
  have hnd : xs.Nodup := hrow.1
  have hlen : xs.length = 3 := ((List.perm_ext_iff_of_nodup hnd htrip).2
    (fun r => by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hmem r)).length_eq
  rcases hrow.2.2 with hsmall | ⟨Φ, z, hpolar, hpositive, hzi, hs, hspoke, hlabel⟩
  · change xs.length ≤ 1 at hsmall
    omega
  obtain ⟨d, hd⟩ := persistent_row_halfedge_equiv rep.edgePar rep.label hrow.2.1
    hpolar hzi hspoke hlabel
  obtain ⟨minus', plus', _, hm', hp', _, _, hpc, hq, hminus', hplus'⟩ := rep.inner_cuff_ends i
  have hmeq : minus' = minus := Subtype.ext (hm'.trans hm.symm)
  have hpeq : plus' = plus := Subtype.ext (hp'.trans hp.symm)
  subst minus'; subst plus'
  have hpV : cylinderToSphere (cylinderM1Point k i) ∈ (cylinderSphereDrawing rep.cuffed).V := by
    rw [cylinderSphereDrawing_V, rep.cuffed_V]
    exact mem_image_of_mem cylinderToSphere hl.left_mem
  have hscale : 0 < Real.pi / (k : ℝ) := div_pos Real.pi_pos (Nat.cast_pos.mpr i.pos)
  have hcyc := source_signed_cuff_order rep.edgePar hq hpc hpV hscale hpolar hpositive d
    (fun a t ht => by rw [hd]; exact hspoke a t ht) minus plus b hmp hmb hpb
    hminus' hplus' hG.2.1 hl.edge_mem hb
  simp only [hd] at hcyc
  have hh := three_end_source_row_forms hne hnp hep hrow.1 hmem z hs hcyc
  simpa only [hml, hpl] using hh

end GraphMinor.GM06
