module

public import GraphMinor.GM06.Alg57CurrentDrawingRep
public import GraphMinor.GM06.Section5ContractedEdgeParam
import GraphMinor.GM06.Alg57CurrentEndClassification
import GraphMinor.GM06.Alg511CuffEnumeration
import GraphMinor.GM06.Section5InitialNeighbourUnique

/-!
# Permanent labels and fixed cuff curves after contraction

For Lemma 8 of VI (5.7), page 133, transport the old permanent
labels through the actual surviving-edge bijection and parametrize
each new edge by its old curve followed by the collapse. On either
cuff that composite is the original curve, since the collapse fixes
the boundary. Thus both cuff families keep their exact labels and
parametrizations. This supplies the cuff fields of the new current
drawing relation without choosing unrelated rotations or curves.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- The actual edge-image bijection transports all permanent labels
without renumbering any retained edge. -/
theorem exists_permanent_labels_of_closed_edge_collapse
    {S : Type*} [TopologicalSpace S] {Γ Γ' : Drawing S}
    {e : Set S} {s v : S} (hl : Γ.toGraph.IsLink e s v) (hvs : v ≠ s)
    (π : S → S) (hi : InjOn π (closure e)ᶜ)
    (hE : Γ'.E = (image π) '' (Γ.E \ {e})) (label : Γ.E ↪ ℕ) :
    ∃ label' : Γ'.E ↪ ℕ, ∀ f (hf : f ∈ Γ.E) (hne : f ≠ e),
      label' ⟨π '' f, hE ▸ mem_image_of_mem (image π) ⟨hf, hne⟩⟩ = label ⟨f, hf⟩ := by
  obtain ⟨η, hη⟩ := exists_edge_equiv_of_closed_edge_collapse hl hvs π hi hE
  let label' : Γ'.E ↪ ℕ := ⟨fun f => label ⟨(η.symm f).val, (η.symm f).property.1⟩, by
    intro a b hab
    have he : (η.symm a).val = (η.symm b).val := congrArg (fun f : Γ.E => f.val) (label.injective hab)
    exact η.symm.injective (Subtype.ext he)⟩
  refine ⟨label', ?_⟩
  intro f hf hne
  let a : {a : Set S // a ∈ Γ.E ∧ a ≠ e} := ⟨f, hf, hne⟩
  have he : (⟨π '' f, hE ▸ mem_image_of_mem (image π) ⟨hf, hne⟩⟩ : Γ'.E) = η a :=
    Subtype.ext (hη a).symm
  change label ⟨(η.symm _).val, _⟩ = _
  rw [he, η.symm_apply_apply]

private theorem retained_fixed_edge_data
    {S : Type*} [TopologicalSpace S] {Γ Γ' : Drawing S}
    {e f : Set S} (π : S → S) (hE : Γ'.E = (image π) '' (Γ.E \ {e}))
    (label : Γ.E ↪ ℕ) (label' : Γ'.E ↪ ℕ)
    (hlabel : ∀ f (hf : f ∈ Γ.E) (hne : f ≠ e),
      label' ⟨π '' f, hE ▸ mem_image_of_mem (image π) ⟨hf, hne⟩⟩ = label ⟨f, hf⟩)
    {γ γ' : Set S → I → S} (hγ : EdgePar Γ γ)
    (hpar : ∀ f ∈ Γ.E, f ≠ e → ∀ t, γ' (π '' f) t = π (γ f t))
    (hf : f ∈ Γ.E) (hne : f ≠ e) (hfix : ∀ t, π (γ f t) = γ f t) :
    (∃ f' : Γ'.E, f'.val = f ∧ label' f' = label ⟨f, hf⟩) ∧ ∀ t, γ' f t = γ f t := by
  have himage : π '' f = f := by
    rw [← hγ.image f hf, image_image]
    exact image_congr (fun t _ => hfix t)
  refine ⟨⟨⟨π '' f, hE ▸ mem_image_of_mem (image π) ⟨hf, hne⟩⟩, himage,
    hlabel f hf hne⟩, ?_⟩
  intro t
  exact (congrArg (fun g => γ' g t) himage.symm).trans ((hpar f hf hne t).trans (hfix t))

/-- Both cuff families retain their actual parametrizations and
permanent labels under the boundary-fixed contraction. The new
parametrization and labels are constructed from the actual edge
images and are shared by all the later rotation proofs. -/
theorem GM06CurrentDrawingRep.exists_contracted_cuff_data
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) {e : Set ClosedCylinder} {s v : ClosedCylinder}
    (hl : G.toGraph.IsLink e s v) (hvs : v ≠ s)
    {Γ' : Drawing (OnePoint EuclideanPlane)}
    (π : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (hi : InjOn π (closure (cylinderToSphere '' e))ᶜ)
    (hfixed : ∀ y ∈ cylinderToSphere '' bd ClosedCylinder, π y = y)
    (hV : Γ'.V = π '' (cylinderSphereDrawing rep.cuffed).V)
    (hE : Γ'.E = (image π) '' ((cylinderSphereDrawing rep.cuffed).E \ {cylinderToSphere '' e})) :
    ∃ (label' : Γ'.E ↪ ℕ) (γ' : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane),
      EdgePar Γ' γ' ∧
      (∀ f (hf : f ∈ (cylinderSphereDrawing rep.cuffed).E) (hne : f ≠ cylinderToSphere '' e),
        label' ⟨π '' f, hE ▸ mem_image_of_mem (image π) ⟨hf, hne⟩⟩ = rep.label ⟨f, hf⟩) ∧
      (∀ f ∈ (cylinderSphereDrawing rep.cuffed).E, f ≠ cylinderToSphere '' e →
        ∀ t, γ' (π '' f) t = π (rep.par f t)) ∧
      (∀ i : Fin k, ∃ f : Γ'.E,
        f.val = cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∧
        label' f = rep.tagged.length + i.val) ∧
      (∀ i : Fin k, ∃ f : Γ'.E,
        f.val = cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1) ∧
        label' f = rep.tagged.length + k + i.val) ∧
      (∀ i : Fin k, ∀ t : I,
        γ' (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) t =
          cylinderToSphere (initialCuffGapCurve k i t)) ∧
      ∀ i : Fin k, ∀ t : I,
        γ' (cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1)) t =
          cylinderToSphere (alg511OuterCuffGapCurve k i t) := by
  have hlF := (rep.subdrawing.isLink_iff hl.edge_mem).mp hl
  have hlS := cylinderSphereDrawing_isLink hlF
  have hvsS : cylinderToSphere v ≠ cylinderToSphere s := fun hh => hvs (injective_cylinderToSphere hh)
  obtain ⟨label', hlabel⟩ := exists_permanent_labels_of_closed_edge_collapse hlS hvsS π hi hE rep.label
  obtain ⟨γ', hγ', hpar⟩ := exists_edgePar_of_closed_edge_collapse hlS hvsS π hi hV hE rep.edgePar
  have hIbd (i : Fin k) (t : I) : initialCuffGapCurve k i t ∈ bd ClosedCylinder := by
    rw [bd_closedCylinder]
    exact Or.inl ((initialCuffGapCurve_props hG i).2.2.1 (mem_range_self t))
  have hObd (i : Fin k) (t : I) : alg511OuterCuffGapCurve k i t ∈ bd ClosedCylinder := by
    rw [bd_closedCylinder]
    right
    change (3 : ℝ) - 1 = 2
    norm_num
  have hIne (i : Fin k) : cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ≠
      cylinderToSphere '' e := by
    intro hh
    have heq := (Set.image_injective.mpr injective_cylinderToSphere) hh
    exact disjoint_left.mp (alg511_cuff_edge_families_disjoint hG).1 hl.edge_mem ⟨i, heq⟩
  have hOne (i : Fin k) : cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1) ≠
      cylinderToSphere '' e := by
    intro hh
    have heq := (Set.image_injective.mpr injective_cylinderToSphere) hh
    exact disjoint_left.mp (alg511_cuff_edge_families_disjoint hG).2.1 hl.edge_mem ⟨i, heq⟩
  have hI (i : Fin k) :
      (∃ f : Γ'.E, f.val = cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∧
        label' f = rep.tagged.length + i.val) ∧
      ∀ t, γ' (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) t =
        cylinderToSphere (initialCuffGapCurve k i t) := by
    obtain ⟨f, hf, hfl⟩ := rep.inner_labels i
    have hdata := retained_fixed_edge_data π hE rep.label label' hlabel rep.edgePar hpar
      f.property (fun hh => hIne i (hf.symm.trans hh)) (fun t => by
        rw [hf, rep.inner_par]
        exact hfixed _ (mem_image_of_mem cylinderToSphere (hIbd i t)))
    constructor
    · obtain ⟨f', hf', hfl'⟩ := hdata.1
      exact ⟨f', hf'.trans hf, hfl'.trans hfl⟩
    · intro t
      rw [← hf, hdata.2, hf, rep.inner_par]
  have hO (i : Fin k) :
      (∃ f : Γ'.E, f.val = cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1) ∧
        label' f = rep.tagged.length + k + i.val) ∧
      ∀ t, γ' (cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1)) t =
        cylinderToSphere (alg511OuterCuffGapCurve k i t) := by
    obtain ⟨f, hf, hfl⟩ := rep.outer_labels i
    have hdata := retained_fixed_edge_data π hE rep.label label' hlabel rep.edgePar hpar
      f.property (fun hh => hOne i (hf.symm.trans hh)) (fun t => by
        rw [hf, rep.outer_par]
        exact hfixed _ (mem_image_of_mem cylinderToSphere (hObd i t)))
    constructor
    · obtain ⟨f', hf', hfl'⟩ := hdata.1
      exact ⟨f', hf'.trans hf, hfl'.trans hfl⟩
    · intro t
      rw [← hf, hdata.2, hf, rep.outer_par]
  exact ⟨label', γ', hγ', hlabel, hpar, fun i => (hI i).1, fun i => (hO i).1,
    fun i => (hI i).2, fun i => (hO i).2⟩


/-- Every active ordinary directed word has its two actual sphere
ends, with exactly its word and mate word and the numeric tail and
head read from the current endpoint table. -/
theorem GM06CurrentDrawingRep.ordinary_dart_halfedges
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (d : Fin (2 * rep.tagged.length)) (hactive : (rep.tagged[d.val / 2]'(by omega)).2 = 1) :
    ∃ (a₀ : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
        (cylinderToSphere (rep.vertex (gm06DartTail rep.tagged d))))
      (a₁ : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
        (cylinderToSphere (rep.vertex (gm06DartHead rep.tagged d)))),
      a₀.val.1 = cylinderToSphere '' rep.edge ⟨d.val / 2, by omega⟩ ∧
      a₁.val.1 = cylinderToSphere '' rep.edge ⟨d.val / 2, by omega⟩ ∧
      gm06PersistentHalfEdgeLabel rep.label a₀ = d.val ∧
      gm06PersistentHalfEdgeLabel rep.label a₁ = gm06DartMate d.val := by
  let j : Fin rep.tagged.length := ⟨d.val / 2, by omega⟩
  obtain ⟨f, hf, hfl⟩ := rep.ordinary_labels j hactive
  have hends := rep.ordinary_ends j hactive
  have hf0 : rep.par f.val 0 = cylinderToSphere (rep.vertex rep.tagged[j].1.1) := by rw [hf]; exact hends.1
  have hf1 : rep.par f.val 1 = cylinderToSphere (rep.vertex rep.tagged[j].1.2) := by rw [hf]; exact hends.2
  by_cases heven : d.val % 2 = 0
  · let a₀ : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
        (cylinderToSphere (rep.vertex (gm06DartTail rep.tagged d))) :=
      ⟨(f.val, false), f.property, by
        simpa only [endOf, Bool.false_eq_true, ite_false, gm06DartTail, heven, ite_true, j, Fin.getElem_fin] using hf0⟩
    let a₁ : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
        (cylinderToSphere (rep.vertex (gm06DartHead rep.tagged d))) :=
      ⟨(f.val, true), f.property, by
        simpa only [endOf, ite_true, gm06DartHead, heven, j, Fin.getElem_fin] using hf1⟩
    refine ⟨a₀, a₁, hf, hf, ?_, ?_⟩
    · change 2 * rep.label f + 0 = d.val
      rw [hfl]
      dsimp only [j]
      omega
    · change 2 * rep.label f + 1 = gm06DartMate d.val
      rw [hfl]
      simp only [gm06DartMate, heven, ite_true]
      dsimp only [j]
      omega
  · let a₀ : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
        (cylinderToSphere (rep.vertex (gm06DartTail rep.tagged d))) :=
      ⟨(f.val, true), f.property, by
        simpa only [endOf, ite_true, gm06DartTail, heven, ite_false, j, Fin.getElem_fin] using hf1⟩
    let a₁ : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
        (cylinderToSphere (rep.vertex (gm06DartHead rep.tagged d))) :=
      ⟨(f.val, false), f.property, by
        simpa only [endOf, Bool.false_eq_true, ite_false, gm06DartHead, heven, j, Fin.getElem_fin] using hf0⟩
    refine ⟨a₀, a₁, hf, hf, ?_, ?_⟩
    · change 2 * rep.label f + 1 = d.val
      rw [hfl]
      dsimp only [j]
      omega
    · change 2 * rep.label f + 0 = gm06DartMate d.val
      rw [hfl]
      simp only [gm06DartMate, heven, ite_false]
      dsimp only [j]
      omega

/-- The first word of the actual linkage row gives the selected
source end and its mate at the actual neighbour. Thus no rotation
membership assertion is needed as an additional input to the
geometric contraction branch. -/
theorem GM06CurrentDrawingRep.initial_word_halfedges
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L) (i : Fin k)
    (first : ℕ) (rest : List ℕ)
    (hrow : x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt) = first :: rest)
    (hfirst : first < 2 * rep.tagged.length) {v : ClosedCylinder}
    (hl : G.toGraph.IsLink (rep.edge ⟨first / 2, by omega⟩) (cylinderM1Point k i) v)
    (hvs : v ≠ cylinderM1Point k i) :
    ∃ (a₀ : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
        (cylinderToSphere (cylinderM1Point k i)))
      (a₁ : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par (cylinderToSphere v)),
      a₀.val.1 = cylinderToSphere '' rep.edge ⟨first / 2, by omega⟩ ∧
      a₁.val.1 = cylinderToSphere '' rep.edge ⟨first / 2, by omega⟩ ∧
      gm06PersistentHalfEdgeLabel rep.label a₀ = first ∧
      gm06PersistentHalfEdgeLabel rep.label a₁ = gm06DartMate first := by
  obtain ⟨W, _, henc, _⟩ := rep.linkage.path i
  rw [hrow] at henc
  obtain ⟨_, hactive⟩ := henc.active_words first (by simp)
  obtain ⟨_, z, e, hlink, R, _, hedge, htail, hhead, _⟩ := henc.first_step
  have hother : G.toGraph.IsLink (rep.edge ⟨first / 2, by omega⟩) (cylinderM1Point k i) z :=
    hedge.symm ▸ hlink
  have hzv : z = v := by
    rcases hl.eq_and_eq_or_eq_and_eq hother with ⟨_, hvz⟩ | ⟨_, hvs'⟩
    · exact hvz.symm
    · exact False.elim (hvs hvs')
  have hhead' : rep.vertex (gm06DartHead rep.tagged ⟨first, hfirst⟩) = v := hhead.trans hzv
  have hends := rep.ordinary_dart_halfedges ⟨first, hfirst⟩ hactive
  rw [htail, hhead'] at hends
  exact hends

end GraphMinor.GM06
