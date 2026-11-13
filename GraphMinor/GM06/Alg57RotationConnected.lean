module

public import GraphMinor.GM06.Alg57PrefixIncidence
import GraphMinor.GM06.Section5CappedPuncture
import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM16.DrawingPointConnectivity
import GraphMinor.GM11.EvenCircuit

/-!
# Lemma 4: the rotation of `G⁺` is connected

Lemma 3 needs two facts about the rotation of the cuffed drawing `G⁺`: the darts are connected by
rotation and reversal steps, and every vertex has a dart. Lemma 4 of our proof of VI (5.7) (outlined
in `Alg57Algorithm.lean`) says that both hold once Reduction 2 does not apply.

Both facts follow from one topological fact: the point set of the drawing is connected. Then
any two vertices are joined by a graph walk (`drawing_walk_of_isPreconnected_U`), and a walk
gives a chain of rotation and reversal steps between darts at its ends
(`DartRotation.connected_of_isPreconnected_U`). A vertex lies on a walk to an end of some
edge, so it has a dart (`exists_dart_of_isPreconnected_U`).

The point set of `G⁺` stays connected even with an initial vertex `sᵢ` removed, when Reduction 2
does not apply and `k ≥ 2` (`isConnected_punctured_cylinderSphereDrawing`). Adding `sᵢ`
back keeps it connected, because `sᵢ` is an end of the inner gap edge `cᵢ`.

The result is `region_incidence_of_no_reduction`: the incidence statement (10) of Lemma 11 with
these two hypotheses replaced by the failure of the reductions.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

section General

variable {S : Type*} [TopologicalSpace S] [T2Space S] {Γ : Drawing S} {γ : Set S → I → S}

/-- An edge linking `x` and `y` has a dart at `x` whose reverse is at `y`. -/
theorem exists_dart_of_isLink (hγ : EdgePar Γ γ) {e : Set S} {x y : S}
    (h : Γ.toGraph.IsLink e x y) :
    ∃ d : DrawingDart Γ, dartVertex γ d = x ∧ dartVertex γ (dartFlip Γ d) = y := by
  have he : e ∈ Γ.E := h.1
  have hc := closure_inter_V_eq hγ he
  have hxy : ({x, y} : Set S) = {γ e (endOf false), γ e (endOf true)} := h.2.2.2.symm.trans hc
  have hx : x ∈ ({γ e (endOf false), γ e (endOf true)} : Set S) := hxy ▸ mem_insert _ _
  have hy : y ∈ ({γ e (endOf false), γ e (endOf true)} : Set S) :=
    hxy ▸ mem_insert_of_mem _ (mem_singleton _)
  have hends : ∀ b : Bool, γ e (endOf b) ∈ ({x, y} : Set S) := fun b => by
    rw [hxy]; cases b
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ (mem_singleton _)
  simp only [mem_insert_iff, mem_singleton_iff] at hx hy
  have key : ∀ b : Bool, x = γ e (endOf b) → ∃ d : DrawingDart Γ,
      dartVertex γ d = x ∧ dartVertex γ (dartFlip Γ d) = y := by
    intro b hb
    refine ⟨⟨(e, b), he⟩, hb.symm, ?_⟩
    change γ e (endOf (!b)) = y
    by_cases hyb : y = γ e (endOf (!b))
    · exact hyb.symm
    · -- then `y` is the end `b`, so `y = x` and both ends are `x`
      have hyx : y = x := by
        cases b <;> simp_all
      have h1 := hends (!b)
      simp only [mem_insert_iff, mem_singleton_iff] at h1
      rcases h1 with h1 | h1
      · rw [h1, hyx]
      · rw [h1]
  rcases hx with hx | hx
  · exact key false hx
  · exact key true hx

/-- Two darts at the same vertex are joined by rotation steps. -/
theorem DartRotation.reflTransGen_of_sameCycle {D : Type*} [Finite D] (R : DartRotation D)
    {a b : D} (h : R.rot.SameCycle a b) :
    Relation.ReflTransGen (fun x y => y = R.rot x ∨ y = R.rev x) a b := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  subst hn
  clear h
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    refine ih.tail (Or.inl ?_)
    rw [pow_succ', Equiv.Perm.mul_apply]

/-- **Lemma 4, connectedness.** If the point set of the drawing is connected, the darts are
connected by rotation and reversal steps. -/
theorem DartRotation.connected_of_isPreconnected_U (hγ : EdgePar Γ γ)
    {R : DartRotation (DrawingDart Γ)} (hR : IsDrawingRotation Γ γ R)
    (hU : IsPreconnected Γ.U) : R.Connected := by
  have hwalk : ∀ (x y : S) (W : GraphWalk Γ.toGraph x y) (a b : DrawingDart Γ),
      dartVertex γ a = x → dartVertex γ b = y →
      Relation.ReflTransGen (fun x y => y = R.rot x ∨ y = R.rev x) a b := by
    intro x y W
    induction W with
    | nil hv =>
      intro a b ha hb
      exact R.reflTransGen_of_sameCycle (hR.reach a b (ha.trans hb.symm))
    | cons hlink rest ih =>
      intro a b ha hb
      obtain ⟨d, hd, hdf⟩ := exists_dart_of_isLink hγ hlink
      have h1 := R.reflTransGen_of_sameCycle (hR.reach a d (ha.trans hd.symm))
      have h2 : Relation.ReflTransGen (fun x y => y = R.rot x ∨ y = R.rev x) d (R.rev d) :=
        Relation.ReflTransGen.single (Or.inr rfl)
      rw [hR.rev_eq] at h2
      exact (h1.trans h2).trans (ih _ b hdf hb)
  intro a b
  obtain ⟨W⟩ := GM16.drawing_walk_of_isPreconnected_U hU (dartVertex_mem hγ a) (dartVertex_mem hγ b)
  exact hwalk _ _ W a b rfl rfl

/-- **Lemma 4, darts at vertices.** If the point set of the drawing is connected and there is an
edge, every vertex has a dart. -/
theorem exists_dart_of_isPreconnected_U (hγ : EdgePar Γ γ) (hU : IsPreconnected Γ.U)
    (hne : Γ.E.Nonempty) : ∀ v ∈ Γ.V, ∃ d : DrawingDart Γ, dartVertex γ d = v := by
  intro v hv
  obtain ⟨e, he⟩ := hne
  let d₀ : DrawingDart Γ := ⟨(e, false), he⟩
  obtain ⟨W⟩ := GM16.drawing_walk_of_isPreconnected_U hU hv (dartVertex_mem hγ d₀)
  cases W with
  | nil _ => exact ⟨d₀, rfl⟩
  | cons hlink _ =>
    obtain ⟨d, hd, -⟩ := exists_dart_of_isLink hγ hlink
    exact ⟨d, hd⟩

/-- Adding back an end `s` of an edge to a connected punctured point set keeps it connected. -/
theorem isPreconnected_U_of_punctured (hγ : EdgePar Γ γ) {e : Set S} (he : e ∈ Γ.E) (b : Bool)
    (h : IsPreconnected (Γ.U \ {γ e (endOf b)})) : IsPreconnected Γ.U := by
  have hsV : γ e (endOf b) ∈ Γ.V := by
    cases b
    · exact hγ.zero e he
    · exact hγ.one e he
  have heU : e ⊆ Γ.U \ {γ e (endOf b)} := by
    intro x hx
    refine ⟨?_, fun hxs => edge_notMem_V he hx (mem_singleton_iff.mp hxs ▸ hsV)⟩
    rw [Γ.U_eq]
    exact Or.inr (mem_iUnion₂.mpr ⟨e, he, subset_closure hx⟩)
  refine h.subset_closure sdiff_subset fun x hx => ?_
  by_cases hxs : x = γ e (endOf b)
  · rw [hxs]
    exact closure_mono heU (end_mem_closure hγ he b)
  · exact subset_closure ⟨hx, hxs⟩

end General

variable {k : ℕ} {G F : Drawing ClosedCylinder}
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
  {R : DartRotation (DrawingDart (cylinderSphereDrawing F))}

/-- When no reduction applies and `k ≥ 2`, the point set of the cuffed drawing in the sphere is
connected. -/
theorem isPreconnected_cylinderSphereDrawing_U_of_no_reduction (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hno : ¬ Section5AnyReductionApplies k G L)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hγ : EdgePar (cylinderSphereDrawing F) γ) (i : Fin k)
    (he : cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∈ (cylinderSphereDrawing F).E)
    (hγe : ∀ t, γ (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) t =
      cylinderToSphere (initialCuffGapCurve k i t)) :
    IsPreconnected (cylinderSphereDrawing F).U := by
  have hs : γ (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) (endOf false) =
      cylinderToSphere (cylinderM1Point k i) := by
    rw [hγe]
    exact congrArg cylinderToSphere (initialCuffGapCurve_props hG i).1
  refine isPreconnected_U_of_punctured hγ he false ?_
  rw [hs]
  exact (isConnected_punctured_cylinderSphereDrawing L hk hG hno hFU i).isPreconnected

/-- **Lemma 11, incidence (10), when no reduction applies.** For `k ≥ 2`, if no reduction
applies, then for the counterclockwise rotation of `G⁺`: a vertex `v` of `G` is in the closure of
`Rᵢ` exactly when some dart at `v` is in the face orbit of `c̄ᵢ`, and a dart's edge lies in the
closure of `Rᵢ` exactly when the dart or its reverse is in that orbit. -/
theorem region_incidence_of_no_reduction (L : CylinderLinkage k G) (hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G) (hno : ¬ Section5AnyReductionApplies k G L)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hγ : EdgePar (cylinderSphereDrawing F) γ)
    (hR : IsDrawingRotation (cylinderSphereDrawing F) γ R)
    (hccw : IsCcwRotation (cylinderSphereDrawing F) γ R) (i : Fin k)
    (he : cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∈ (cylinderSphereDrawing F).E)
    (hγe : ∀ t, γ (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) t =
      cylinderToSphere (initialCuffGapCurve k i t)) :
    (∀ v : ClosedCylinder, cylinderToSphere v ∈ (cylinderSphereDrawing F).V →
      (v ∈ closure (cylinderRegion k G i) ↔
        ∃ d : DrawingDart (cylinderSphereDrawing F), dartVertex γ d = cylinderToSphere v ∧
          R.faceOf d = R.faceOf (reverseInnerGapDart k i F he))) ∧
    (∀ d : DrawingDart (cylinderSphereDrawing F),
      d.1.1 ⊆ cylinderToSphere '' closure (cylinderRegion k G i) ↔
        R.faceOf d = R.faceOf (reverseInnerGapDart k i F he) ∨
          R.faceOf (R.rev d) = R.faceOf (reverseInnerGapDart k i F he)) := by
  have hU := isPreconnected_cylinderSphereDrawing_U_of_no_reduction L hk hG hno hFU hγ i he hγe
  exact region_incidence_of_ccw hG hFU hγ hR hccw (DartRotation.connected_of_isPreconnected_U hγ hR hU)
    (exists_dart_of_isPreconnected_U hγ hU ⟨_, he⟩) i he hγe

/-- **Reduction 4 incidence from the face orbit, when no reduction applies** (`k ≥ 2`). This is
`subset_closure_region_iff_of_ccw` with the hypotheses of Lemma 4 discharged. -/
theorem subset_closure_region_iff_of_no_reduction (L : CylinderLinkage k G) (hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G) (hno : ¬ Section5AnyReductionApplies k G L)
    (hGF : G.IsSubdrawing F)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hγ : EdgePar (cylinderSphereDrawing F) γ)
    (hR : IsDrawingRotation (cylinderSphereDrawing F) γ R)
    (hccw : IsCcwRotation (cylinderSphereDrawing F) γ R) (i : Fin k)
    (he : cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∈ (cylinderSphereDrawing F).E)
    (hγe : ∀ t, γ (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) t =
      cylinderToSphere (initialCuffGapCurve k i t))
    {P : Drawing ClosedCylinder} (hP : P.IsSubdrawing G) :
    P.U ⊆ closure (cylinderRegion k G i) ↔
      (∀ v ∈ P.V, ∃ d : DrawingDart (cylinderSphereDrawing F),
        dartVertex γ d = cylinderToSphere v ∧
          R.faceOf d = R.faceOf (reverseInnerGapDart k i F he)) ∧
      (∀ e ∈ P.E, ∃ (b : Bool) (he' : cylinderToSphere '' e ∈ (cylinderSphereDrawing F).E),
        R.faceOf ⟨(cylinderToSphere '' e, b), he'⟩ =
          R.faceOf (reverseInnerGapDart k i F he)) := by
  have hU := isPreconnected_cylinderSphereDrawing_U_of_no_reduction L hk hG hno hFU hγ i he hγe
  exact subset_closure_region_iff_of_ccw hG hGF hFU hγ hR hccw
    (DartRotation.connected_of_isPreconnected_U hγ hR hU)
    (exists_dart_of_isPreconnected_U hγ hU ⟨_, he⟩) i he hγe hP

end GraphMinor.GM06
