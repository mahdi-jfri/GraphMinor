module

public import GraphMinor.Planar.Defs
public import GraphMinor.GM06.Defs
import GraphMinor.GM05.GraphComponents
import GraphMinor.GM05.DrawingSupportTransport
import GraphMinor.GM06.Section3Basic
import GraphMinor.GM07.Section11
import GraphMinor.GM11.Section4c
import GraphMinor.GM11.PerimeterPull
import GraphMinor.GM12.Section3FiniteDrawingUnion
import GraphMinor.GM19.Section6a
import GraphMinor.Surface.Jordan

/-!
# A nonplanar graph has a nonplanar component

GM V, (8.13), page 113, starts with "since $H$ is non-planar, it has a
non-planar component $H^*$". We prove the contrapositive. Draw each
component in its own sphere. Its support misses a point, so it lies in
a closed disc. Move the disc into a vertical band of the plane, with a
different band for each component, and then into one sphere. The
drawings are now disjoint, and their union is a drawing of the whole
graph.
-/

public section
namespace GraphMinor.GM05
open Set Topology Surface GM06 Graph
universe u v

/-- The points of `Q` that come from the band `|Re z - 3n| ≤ 1` of the
plane, under a fixed homeomorphism of `Q` with the sphere. -/
private def band {Q : Type} [TopologicalSpace Q] (e : Q ≃ₜ OnePoint EuclideanPlane)
    (n : ℕ) : Set Q :=
  {q | ∃ z : ℂ, |z.re - 3 * n| ≤ 1 ∧
    e.symm ((complexPlane z : EuclideanPlane) : OnePoint EuclideanPlane) = q}

/-- Bands with different indices are disjoint. -/
private theorem band_eq {Q : Type} [TopologicalSpace Q]
    (e : Q ≃ₜ OnePoint EuclideanPlane) {n k : ℕ} {q : Q}
    (hn : q ∈ band e n) (hk : q ∈ band e k) : n = k := by
  obtain ⟨z,hz,rfl⟩ := hn
  obtain ⟨w,hw,hwz⟩ := hk
  have hzw : w = z := complexPlane.injective
    (OnePoint.coe_injective (e.symm.injective hwz))
  subst hzw
  have h1 := abs_le.mp hz
  have h2 := abs_le.mp hw
  rcases lt_trichotomy n k with hlt|heq|hgt
  · have : (n : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt hlt
    linarith [h1.2,h2.1]
  · exact heq
  · have : (k : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hgt
    linarith [h1.1,h2.2]

/-- A planar graph has a drawing in `Q` inside any given band. -/
private theorem exists_drawing_in_band {α : Type u} {β : Type v} {C : Graph α β}
    (hC : IsPlanar C) {Q : Type} [TopologicalSpace Q] [T2Space Q] [Nonempty Q]
    (e : Q ≃ₜ OnePoint EuclideanPlane) (n : ℕ) :
    ∃ Δ : GraphDrawing C Q, Δ.drawing.U ⊆ band e n := by
  obtain ⟨-,-,S,_,hS,hSph,⟨Γ⟩⟩ := hC
  let : T2Space S := hS.2.1
  let : CompactSpace S := hS.1
  obtain ⟨φS⟩ := id hSph
  let : Nonempty S := ⟨φS.symm OnePoint.infty⟩
  -- The support misses a point, so it lies in a closed disc.
  obtain ⟨y,-,hy⟩ := GM11.exists_notMem_U (Γ := Γ.drawing)
    (GM11.IsSphere.isClosedSurface hSph).1 isOpen_univ univ_nonempty
  have hne : Γ.drawing.U ≠ univ := fun h ↦ hy (h ▸ mem_univ y)
  obtain ⟨D,⟨φ⟩,hUD⟩ := GM07.isPlanar_of_isSphere_ne_univ hS hSph Γ.drawing.isClosed_U hne
  -- Move the disc into the band and then into `Q`.
  let c : ℂ := ((3 * n : ℝ) : ℂ)
  let t : ℂ → Q := fun z ↦ e.symm ((complexPlane (z + c) : EuclideanPlane) : OnePoint EuclideanPlane)
  have ht : IsEmbedding t := e.symm.isEmbedding.comp
    (OnePoint.isOpenEmbedding_coe.isEmbedding.comp
      (complexPlane.toHomeomorph.isEmbedding.comp (Homeomorph.addRight c).isEmbedding))
  let j₀ : Γ.drawing.U → D := fun x ↦ ⟨x.val,hUD x.prop⟩
  have hj₀ : IsEmbedding j₀ := IsEmbedding.subtypeVal.codRestrict _ _
  let w : Γ.drawing.U → ℂ := fun x ↦ complexPlane.symm (φ.symm (j₀ x)).val
  have hw : IsEmbedding w := complexPlane.symm.toHomeomorph.isEmbedding.comp
    (IsEmbedding.subtypeVal.comp (φ.symm.isEmbedding.comp hj₀))
  obtain ⟨Δ,hΔ⟩ := exists_graphDrawing_of_support_embedding Γ (t ∘ w) (ht.comp hw)
  refine ⟨Δ,?_⟩
  rw [hΔ]
  rintro _ ⟨x,rfl⟩
  refine ⟨w x + c,?_,rfl⟩
  have hnorm : ‖w x‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact mem_closedBall_zero_iff.mp (φ.symm (j₀ x)).prop
  have hre : (w x + c).re - 3 * n = (w x).re := by simp [c]
  rw [hre]
  exact (Complex.abs_re_le_norm _).trans hnorm

/-- A finite graph whose components are all planar is planar. -/
theorem isPlanar_of_forall_component {α : Type u} {β : Type v} {H : Graph α β}
    (hV : V(H).Finite) (h : ∀ C, IsGraphComponent C H → IsPlanar C) : IsPlanar H := by
  classical
  obtain ⟨m,C,hinj,hCi,hcover⟩ := exists_component_enumeration hV
  let Q := SurfaceModel 0 0 0
  have hQ : IsSurface Q := (isSurface_model 0 0 0).1
  let : T2Space Q := hQ.2.1
  obtain ⟨e⟩ := (GM19.isSphere_model : IsSphere Q)
  let : Nonempty Q := ⟨e.symm OnePoint.infty⟩
  -- Draw the components in disjoint bands.
  choose Δ hΔU using fun i : Fin m ↦ exists_drawing_in_band (h _ (hCi i)) e i
  have hUeq : ∀ i j q, q ∈ (Δ i).drawing.U → q ∈ (Δ j).drawing.U → i = j :=
    fun i j _ hi hj ↦ Fin.ext (band_eq e (hΔU i hi) (hΔU j hj))
  have hdis : Pairwise (fun i j ↦ Disjoint (Δ i).drawing.U (Δ j).drawing.U) :=
    fun i j hij ↦ disjoint_left.mpr fun q hi hj ↦ hij (hUeq i j q hi hj)
  obtain ⟨K,-,hKV,hKE⟩ := GM12.exists_finite_disjoint_drawing_union (fun i ↦ (Δ i).drawing) hdis
  have hVi : ∀ i, (Δ i).drawing.V ⊆ K.V := fun i _ hx ↦ hKV ▸ mem_iUnion.mpr ⟨i,hx⟩
  have hEi : ∀ i, (Δ i).drawing.E ⊆ K.E := fun i _ hx ↦ hKE ▸ mem_iUnion.mpr ⟨i,hx⟩
  -- An edge of one drawing has the same ends in the union.
  have hlinkK : ∀ i, ∀ p ∈ (Δ i).drawing.E, ∀ a b,
      K.toGraph.IsLink p a b ↔ (Δ i).drawing.toGraph.IsLink p a b := by
    intro i p hp a b
    have hcl : closure p ⊆ (Δ i).drawing.U :=
      closure_minimal (hp.2.1.trans sdiff_subset) (Δ i).drawing.isClosed_U
    have hcV : closure p ∩ K.V = closure p ∩ (Δ i).drawing.V := by
      ext q
      constructor
      · rintro ⟨hq,hqK⟩
        rw [hKV] at hqK
        obtain ⟨j,hj⟩ := mem_iUnion.mp hqK
        obtain rfl := hUeq i j q (hcl hq) ((Δ j).drawing.V_subset_U hj)
        exact ⟨hq,hj⟩
      · rintro ⟨hq,hqi⟩
        exact ⟨hq,hVi i hqi⟩
    change (p ∈ K.E ∧ a ∈ K.V ∧ b ∈ K.V ∧ closure p ∩ K.V = {a,b}) ↔
      (p ∈ (Δ i).drawing.E ∧ a ∈ (Δ i).drawing.V ∧ b ∈ (Δ i).drawing.V ∧
        closure p ∩ (Δ i).drawing.V = {a,b})
    rw [hcV]
    constructor
    · rintro ⟨-,-,-,hab⟩
      have ha : a ∈ closure p ∩ (Δ i).drawing.V := hab ▸ mem_insert a _
      have hb : b ∈ closure p ∩ (Δ i).drawing.V := hab ▸ mem_insert_of_mem a rfl
      exact ⟨hp,ha.2,hb.2,hab⟩
    · rintro ⟨-,ha,hb,hab⟩
      exact ⟨hEi i hp,hVi i ha,hVi i hb,hab⟩
  -- The component of each vertex and edge.
  have hvi : ∀ v : V(H), ∃ i, v.1 ∈ V(C i) := by
    intro v
    obtain ⟨D,hD,hvD⟩ := exists_component_of_vertex v.2
    obtain ⟨i,rfl⟩ := hcover D hD
    exact ⟨i,hvD⟩
  have hei : ∀ f : E(H), ∃ i, f.1 ∈ E(C i) := by
    intro f
    obtain ⟨D,hD,hfD⟩ := exists_component_of_edge f.2
    obtain ⟨i,rfl⟩ := hcover D hD
    exact ⟨i,hfD⟩
  choose iv hiv using hvi
  choose ie hie using hei
  have hiv_eq : ∀ v i, v.1 ∈ V(C i) → iv v = i :=
    fun v i hi ↦ hinj ((hCi _).eq_of_mem_mem (hCi i) (hiv v) hi)
  have hie_eq : ∀ f i, f.1 ∈ E(C i) → ie f = i := by
    intro f i hi
    by_contra hne
    exact disjoint_left.mp ((hCi _).disjoint_edgeSet_of_ne (hCi i) fun h ↦ hne (hinj h))
      (hie f) hi
  -- The maps to the vertices and edges of the union.
  let fV : V(H) → K.V := fun v ↦
    ⟨((Δ (iv v)).iso.vertexEquiv ⟨v.1,hiv v⟩).1,hVi _ ((Δ (iv v)).iso.vertexEquiv ⟨v.1,hiv v⟩).2⟩
  let fE : E(H) → K.E := fun f ↦
    ⟨((Δ (ie f)).iso.edgeEquiv ⟨f.1,hie f⟩).1,hEi _ ((Δ (ie f)).iso.edgeEquiv ⟨f.1,hie f⟩).2⟩
  have hfV : ∀ v i (hi : v.1 ∈ V(C i)), (fV v).1 = ((Δ i).iso.vertexEquiv ⟨v.1,hi⟩).1 := by
    intro v i hi
    obtain rfl := hiv_eq v i hi
    rfl
  have hfE : ∀ f i (hi : f.1 ∈ E(C i)), (fE f).1 = ((Δ i).iso.edgeEquiv ⟨f.1,hi⟩).1 := by
    intro f i hi
    obtain rfl := hie_eq f i hi
    rfl
  have hfV_inj : Function.Injective fV := by
    intro v w hvw
    have h1 := congrArg Subtype.val hvw
    have hw : w.1 ∈ V(C (iv v)) := by
      have hpt : (fV v).1 ∈ (Δ (iv w)).drawing.U :=
        h1 ▸ (Δ (iv w)).drawing.V_subset_U ((Δ (iv w)).iso.vertexEquiv ⟨w.1,hiv w⟩).2
      have hpt' : (fV v).1 ∈ (Δ (iv v)).drawing.U :=
        (Δ (iv v)).drawing.V_subset_U ((Δ (iv v)).iso.vertexEquiv ⟨v.1,hiv v⟩).2
      have heq : iv w = iv v := hUeq _ _ _ hpt hpt'
      exact heq ▸ hiv w
    rw [hfV v (iv v) (hiv v),hfV w (iv v) hw] at h1
    have h2 := (Δ (iv v)).iso.vertexEquiv.injective (Subtype.ext h1)
    have h3 : v.1 = w.1 := Subtype.mk.inj h2
    exact Subtype.ext h3
  have hfV_surj : Function.Surjective fV := by
    rintro ⟨p,hp⟩
    have hp' := hp
    rw [hKV] at hp'
    obtain ⟨i,hpi⟩ := mem_iUnion.mp hp'
    let x := (Δ i).iso.vertexEquiv.symm ⟨p,hpi⟩
    have hxH : x.1 ∈ V(H) := (hCi i).1.vertexSet_mono x.2
    refine ⟨⟨x.1,hxH⟩,Subtype.ext ?_⟩
    rw [hfV ⟨x.1,hxH⟩ i x.2]
    simp [x]
  have hfE_inj : Function.Injective fE := by
    intro f g hfg
    have h1 := congrArg Subtype.val hfg
    have hg : g.1 ∈ E(C (ie f)) := by
      have hsub : ∀ k (p : (Δ k).drawing.toGraph.edgeSet), p.1 ⊆ (Δ k).drawing.U :=
        fun k p ↦ (show p.1 ∈ (Δ k).drawing.E from p.2).2.1.trans sdiff_subset
      obtain ⟨q,hq⟩ := (show ((Δ (ie f)).iso.edgeEquiv ⟨f.1,hie f⟩).1 ∈ (Δ (ie f)).drawing.E
        from ((Δ (ie f)).iso.edgeEquiv ⟨f.1,hie f⟩).2).1
      have hpt' : q ∈ (Δ (ie f)).drawing.U := hsub _ _ hq
      have hpt : q ∈ (Δ (ie g)).drawing.U := by
        have : ((Δ (ie f)).iso.edgeEquiv ⟨f.1,hie f⟩).1 =
            ((Δ (ie g)).iso.edgeEquiv ⟨g.1,hie g⟩).1 := h1
        exact hsub _ ((Δ (ie g)).iso.edgeEquiv ⟨g.1,hie g⟩) (this ▸ hq)
      have heq : ie g = ie f := hUeq _ _ _ hpt hpt'
      exact heq ▸ hie g
    rw [hfE f (ie f) (hie f),hfE g (ie f) hg] at h1
    have h2 := (Δ (ie f)).iso.edgeEquiv.injective (Subtype.ext h1)
    have h3 : f.1 = g.1 := Subtype.mk.inj h2
    exact Subtype.ext h3
  have hfE_surj : Function.Surjective fE := by
    rintro ⟨p,hp⟩
    have hp' := hp
    rw [hKE] at hp'
    obtain ⟨i,hpi⟩ := mem_iUnion.mp hp'
    let x := (Δ i).iso.edgeEquiv.symm ⟨p,hpi⟩
    have hxH : x.1 ∈ E(H) := (hCi i).1.edgeSet_mono x.2
    refine ⟨⟨x.1,hxH⟩,Subtype.ext ?_⟩
    rw [hfE ⟨x.1,hxH⟩ i x.2]
    simp [x]
  -- The isomorphism.
  let φ : Iso H K.toGraph :=
    { vertexEquiv := Equiv.ofBijective fV ⟨hfV_inj,hfV_surj⟩
      edgeEquiv := Equiv.ofBijective fE ⟨hfE_inj,hfE_surj⟩
      isLink_iff := by
        intro f x y
        let i := ie f
        have hCH : ∀ a b, (C i).IsLink f.1 a b ↔ H.IsLink f.1 a b :=
          fun a b ↦ (hCi i).1.isLink_iff (hie f)
        change H.IsLink f.1 x.1 y.1 ↔ K.toGraph.IsLink (fE f).1 (fV x).1 (fV y).1
        have hEdge := ((Δ i).iso.edgeEquiv ⟨f.1,hie f⟩).2
        rw [hlinkK i _ hEdge]
        constructor
        · intro hl
          have hlC := (hCH _ _).mpr hl
          have hx : x.1 ∈ V(C i) := hlC.left_mem
          have hy : y.1 ∈ V(C i) := hlC.right_mem
          rw [hfV x i hx,hfV y i hy]
          exact ((Δ i).iso.isLink_iff ⟨f.1,hie f⟩ ⟨x.1,hx⟩ ⟨y.1,hy⟩).mp hlC
        · intro hl
          have hmem : ∀ z : V(H), (fV z).1 ∈ (Δ i).drawing.V → z.1 ∈ V(C i) := by
            intro z hz
            have hpt := (Δ (iv z)).drawing.V_subset_U ((Δ (iv z)).iso.vertexEquiv ⟨z.1,hiv z⟩).2
            have heq : iv z = i := hUeq _ _ _ hpt ((Δ i).drawing.V_subset_U hz)
            exact heq ▸ hiv z
          have hx := hmem x hl.2.1
          have hy := hmem y hl.2.2.1
          rw [hfV x i hx,hfV y i hy] at hl
          exact (hCH _ _).mp (((Δ i).iso.isLink_iff ⟨f.1,hie f⟩ ⟨x.1,hx⟩ ⟨y.1,hy⟩).mpr hl) }
  exact IsPlanar.of_graphDrawing hQ GM19.isSphere_model ⟨K,φ⟩

/-- GM V, (8.13), page 113: "since $H$ is non-planar, it has a
non-planar component $H^*$". -/
theorem exists_nonplanar_component {α : Type u} {β : Type v} {H : Graph α β}
    (hV : V(H).Finite) (hnp : ¬ IsPlanar H) :
    ∃ C, IsGraphComponent C H ∧ ¬ IsPlanar C := by
  by_contra h
  push Not at h
  exact hnp (isPlanar_of_forall_component hV h)

end GraphMinor.GM05
