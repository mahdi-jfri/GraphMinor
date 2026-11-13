module

public import GraphMinor.GM06.Alg57CollapsedSourceOrder
public import GraphMinor.GM06.Alg57MappedRotations
public import GraphMinor.GM06.Section5ContractedEdgeParam
import GraphMinor.GM06.Alg57RowRotation
import GraphMinor.GM06.Alg511CuffEnumeration

/-!
# The actual directed ends of the target suffix and prefix

For Lemma 8 of VI (5.7), page 133, cut the old target rotation
immediately after the incoming end. The remaining suffix and
prefix contain exactly the other ends. The contraction bijection
maps these ends to the new source without changing their permanent
words or half-spoke parameters. Their old angular coordinates
increase between zero and one full turn. Excluding the finitely
many midpoints makes their rays strict short half-spokes.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- The suffix and prefix about a selected position list every
old word except that position's word, with no repetitions. -/
theorem retained_rotation_block_mem_iff
    {ys : List ℕ} (hnd : ys.Nodup) {q : ℕ} (hq : q < ys.length) (r : ℕ) :
    r ∈ ys.drop (q + 1) ++ ys.take q ↔ r ∈ ys ∧ r ≠ ys[q] := by
  have hperm : (ys.drop (q + 1) ++ ys.take q).Perm (ys.eraseIdx q) := by
    rw [List.eraseIdx_eq_take_drop_succ]
    exact List.perm_append_comm
  rw [hperm.mem_iff]
  constructor
  · intro hr
    obtain ⟨j, hj, hjq, hjr⟩ := List.mem_eraseIdx_iff_getElem.mp hr
    exact ⟨List.mem_of_mem_eraseIdx hr,
      fun heq => hjq (hnd.eq_of_getElem_eq hj hq (hjr.trans heq))⟩
  · rintro ⟨hr, hne⟩
    obtain ⟨j, hj, hjr⟩ := List.mem_iff_getElem.mp hr
    exact List.mem_eraseIdx_iff_getElem.mpr
      ⟨j, hj, (by intro hh; subst j; exact hne hjr.symm), hjr⟩

/-- A retained end with its actual image edge and unchanged end
bit has the same permanent word after contraction. -/
theorem permanent_label_of_image_halfedge
    {Γ Γ' : Drawing (OnePoint EuclideanPlane)}
    {γ γ' : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {s v : OnePoint EuclideanPlane} {e : Set (OnePoint EuclideanPlane)}
    (π : OnePoint EuclideanPlane → OnePoint EuclideanPlane)
    (hE : Γ'.E = (image π) '' (Γ.E \ {e}))
    (label : Γ.E ↪ ℕ) (label' : Γ'.E ↪ ℕ)
    (hlabel : ∀ f (hf : f ∈ Γ.E) (hne : f ≠ e),
      label' ⟨π '' f, hE ▸ mem_image_of_mem (image π) ⟨hf, hne⟩⟩ = label ⟨f, hf⟩)
    (a : halfEdges Γ γ v) (ha : a.val.1 ≠ e) (b : halfEdges Γ' γ' s)
    (hb : b.val = (π '' a.val.1, a.val.2)) :
    gm06PersistentHalfEdgeLabel label' b = gm06PersistentHalfEdgeLabel label a := by
  have he : (⟨b.val.1, b.property.1⟩ : Γ'.E) =
      ⟨π '' a.val.1, hE ▸ mem_image_of_mem (image π) ⟨a.property.1, ha⟩⟩ :=
    Subtype.ext (congrArg Prod.fst hb)
  have hbit := congrArg Prod.snd hb
  have hl := (congrArg label' he).trans (hlabel a.val.1 a.property.1 ha)
  simp only [gm06PersistentHalfEdgeLabel, hl, hbit]

/-- Even a row of length at most one can be realized by an actual
positive polar chart inside any prescribed vertex neighbourhood.
The general row relation omits that chart only to shorten inputs. -/
theorem GM06PersistentRotationRowRep.exists_small_chart_all
    {Γ : Drawing (OnePoint EuclideanPlane)} {label : Γ.E ↪ ℕ}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar Γ γ) {p : OnePoint EuclideanPlane} {xs : List ℕ}
    (hrow : GM06PersistentRotationRowRep label γ p xs) (hpV : p ∈ Γ.V)
    (hpfinite : p ∈ range ((↑) : EuclideanPlane → OnePoint EuclideanPlane))
    {O : Set (OnePoint EuclideanPlane)} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (z : ℕ → Circle),
      IsPolar Γ p Φ ∧ GM06PositivePolar Φ ∧ range Φ ⊆ O ∧
      InjOn z {r | r ∈ xs} ∧
      xs.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)) ∧
      (∀ a : halfEdges Γ γ p, ∀ t : I, 0 < t →
        Φ (polarDiscPoint t (z (gm06PersistentHalfEdgeLabel label a))) ∈ range (spoke γ a.val)) ∧
      ∀ (f : Γ.E) (w : Circle), polarRimMap Φ w ∈ f.val ↔ ∃ r ∈ xs,
        z r = w ∧ (r = 2 * label f ∨ r = 2 * label f + 1) := by
  by_cases hlarge : 1 < xs.length
  · exact hrow.exists_small_chart hlarge hO hpO
  have hlen : xs.length ≤ 1 := Nat.le_of_not_gt hlarge
  obtain ⟨Φ, d, hp, hpos, hd⟩ := exists_positive_polar_chart hγ hpV hpfinite
  obtain ⟨Φ', d', hp', hpos', hsub, _, hd'⟩ :=
    exists_small_labeled_positive_polar_chart hp hpos d hd hO hpO
  obtain ⟨z, _, hzi, hspoke, hlabel⟩ :=
    exists_permanent_directions_of_halfedge_equiv hγ label hrow.2.1 hp' d' hd'
  refine ⟨Φ', z, hp', hpos', hsub, hzi, ?_, hspoke, hlabel⟩
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  omega

/-- The suffix and prefix of an actual target row give injectively
labelled new source ends, their exact old spoke images, and their
increasing angular coordinates after the incoming end. -/
theorem exists_retained_target_block_data
    {Γ Γ' : Drawing (OnePoint EuclideanPlane)}
    {e : Set (OnePoint EuclideanPlane)} {s v : OnePoint EuclideanPlane}
    (hl : Γ.toGraph.IsLink e s v) (hvs : v ≠ s)
    (π : OnePoint EuclideanPlane → OnePoint EuclideanPlane)
    (hfibre : π ⁻¹' {s} = closure e) (hinj : InjOn π (closure e)ᶜ)
    (hE : Γ'.E = (image π) '' (Γ.E \ {e}))
    {γ γ' : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar Γ γ)
    (hpar : ∀ f ∈ Γ.E, f ≠ e → ∀ t, γ' (π '' f) t = π (γ f t))
    (label : Γ.E ↪ ℕ) (label' : Γ'.E ↪ ℕ)
    (hlabel : ∀ f (hf : f ∈ Γ.E) (hne : f ≠ e),
      label' ⟨π '' f, hE ▸ mem_image_of_mem (image π) ⟨hf, hne⟩⟩ = label ⟨f, hf⟩)
    (incoming : halfEdges Γ γ v) (hin : incoming.val.1 = e)
    {ys : List ℕ} (hy : GM06PersistentRotationRowRep label γ v ys)
    {q : ℕ} (hq : q < ys.length) (hget : ys[q] = gm06PersistentHalfEdgeLabel label incoming)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {z : ℕ → Circle}
    (hp : IsPolar Γ v Φ)
    (hs : ys.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)))
    (hspoke : ∀ a : halfEdges Γ γ v, ∀ t : I, 0 < t →
      Φ (polarDiscPoint t (z (gm06PersistentHalfEdgeLabel label a))) ∈ range (spoke γ a.val))
    (hmid : ∀ a : halfEdges Γ γ v, spoke γ a.val 1 ∉ range Φ) :
    let tail := ys.drop (q + 1) ++ ys.take q
    ∃ (b : {r : ℕ // r ∈ tail} → halfEdges Γ γ v)
      (a : {r : ℕ // r ∈ tail} → halfEdges Γ' γ' s) (θ : ℕ → ℝ),
      Function.Injective a ∧
      (∀ j, gm06PersistentHalfEdgeLabel label (b j) = j.val) ∧
      (∀ j, (b j).val.1 ≠ e) ∧
      (∀ j, gm06PersistentHalfEdgeLabel label' (a j) = j.val) ∧
      (∀ j, (a j).val = (π '' (b j).val.1, (b j).val.2)) ∧
      (∀ j t, spoke γ' (a j).val t = π (spoke γ (b j).val t)) ∧
      (∀ j : {r : ℕ // r ∈ tail}, 0 < θ j.val ∧ θ j.val < 2 * Real.pi ∧ z j.val = z ys[q] * Circle.exp (θ j.val)) ∧
      (∀ j, ∀ t : I, 0 < t → Φ (polarDiscPoint t (z ys[q] * Circle.exp (θ j.val))) ∈
        spoke γ (b j).val '' Ioo (0 : I) 1) ∧
      tail.Pairwise (fun i j => θ i < θ j) := by
  classical
  dsimp only
  let tail := ys.drop (q + 1) ++ ys.take q
  have hbex (j : {r : ℕ // r ∈ tail}) :
      ∃ b : halfEdges Γ γ v, gm06PersistentHalfEdgeLabel label b = j.val :=
    (hy.2.1 j.val).mp ((retained_rotation_block_mem_iff hy.1 hq j.val).mp j.property).1
  choose b hb using hbex
  have hbne (j : {r : ℕ // r ∈ tail}) : (b j).val.1 ≠ e := by
    intro heq
    have he := halfedge_eq_of_nonloop_edge hγ hl.symm (Ne.symm hvs) (b j) incoming heq hin
    have hcode := congrArg (gm06PersistentHalfEdgeLabel label) he
    rw [hb] at hcode
    exact ((retained_rotation_block_mem_iff hy.1 hq j.val).mp j.property).2
      (hcode.trans hget.symm)
  obtain ⟨η, _, hη, _, hspokes⟩ :=
    exists_contracted_source_halfedge_equiv hl hvs π hfibre hinj hE hγ hpar
  let a (j : {r : ℕ // r ∈ tail}) := η (.inr ⟨b j, hbne j⟩)
  have hdata (j : {r : ℕ // r ∈ tail}) :
      (a j).val = (π '' (b j).val.1, (b j).val.2) := hη ⟨b j, hbne j⟩
  have hcode (j : {r : ℕ // r ∈ tail}) : gm06PersistentHalfEdgeLabel label' (a j) = j.val :=
    (permanent_label_of_image_halfedge π hE label label' hlabel (b j) (hbne j) (a j) (hdata j)).trans (hb j)
  have hai : Function.Injective a := by
    intro j l h
    apply Subtype.ext
    exact (hcode j).symm.trans ((congrArg (gm06PersistentHalfEdgeLabel label') h).trans (hcode l))
  obtain ⟨θ, hθ, horder⟩ := exists_increasing_angles_after_row_entry ys z hs q hq
  refine ⟨b, a, θ, hai, hb, hbne, hcode, hdata, ?_, (fun j => hθ j.val j.property), ?_, horder⟩
  · intro j t
    exact hspokes ⟨b j, hbne j⟩ t
  · intro j t ht
    rw [← (hθ j.val j.property).2.2, ← hb j]
    exact polar_ray_mem_short_spoke_of_midpoint_exclusion hp (b j) _ (hspoke (b j)) (hmid (b j)) t ht


/-- At an interior vertex every current augmented end is ordinary.
Neither concrete cuff parametrization can end at such a point. -/
theorem GM06CurrentDrawingRep.interior_halfedge_ordinary
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) {v : ClosedCylinder}
    (hv : v ∉ bd ClosedCylinder)
    (a : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par (cylinderToSphere v)) :
    ∃ j : Fin rep.tagged.length, rep.tagged[j].2 = 1 ∧ a.val.1 = cylinderToSphere '' rep.edge j := by
  rcases rep.edge_cases hG ⟨a.val.1, a.property.1⟩ with h | ⟨j, hj⟩ | ⟨j, hj⟩
  · exact h
  · exfalso
    apply hv
    change a.val.1 = _ at hj
    have hpoint := a.property.2
    change rep.par a.val.1 (endOf a.val.2) = cylinderToSphere v at hpoint
    rw [hj, rep.inner_par] at hpoint
    have heq := injective_cylinderToSphere hpoint
    rw [bd_closedCylinder, ← heq]
    exact Or.inl ((initialCuffGapCurve_props hG j).2.2.1 (mem_range_self _))
  · exfalso
    apply hv
    change a.val.1 = _ at hj
    have hpoint := a.property.2
    change rep.par a.val.1 (endOf a.val.2) = cylinderToSphere v at hpoint
    rw [hj, rep.outer_par] at hpoint
    have hh := congrArg (fun p : ClosedCylinder => p.val.1) (injective_cylinderToSphere hpoint)
    rw [bd_closedCylinder]
    right
    change v.val.1 = 2
    change (3 : ℝ) - 1 = v.val.1 at hh
    norm_num at hh
    exact hh.symm


/-- An ordinary directed word is below twice the original ordinary
slot count, even when some slots have been retired. -/
theorem GM06CurrentDrawingRep.ordinary_halfedge_word_lt
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    {p : OnePoint EuclideanPlane}
    (a : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par p)
    (ha : ∃ j : Fin rep.tagged.length, rep.tagged[j].2 = 1 ∧ a.val.1 = cylinderToSphere '' rep.edge j) :
    gm06PersistentHalfEdgeLabel rep.label a < 2 * rep.tagged.length := by
  obtain ⟨j, hj, haj⟩ := ha
  obtain ⟨f, hf, hfl⟩ := rep.ordinary_labels j hj
  have he : (⟨a.val.1, a.property.1⟩ : (cylinderSphereDrawing rep.cuffed).E) = f :=
    Subtype.ext (haj.trans hf.symm)
  have hlabel : rep.label ⟨a.val.1, a.property.1⟩ = j.val := (congrArg rep.label he).trans hfl
  have hbit : a.val.2.toNat ≤ 1 := by cases a.val.2 <;> decide
  change 2 * rep.label ⟨a.val.1, a.property.1⟩ + a.val.2.toNat < _
  rw [hlabel]
  omega

end GraphMinor.GM06
