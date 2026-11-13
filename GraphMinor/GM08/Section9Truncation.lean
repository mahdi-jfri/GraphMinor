module

public import GraphMinor.GM08.Section9
import GraphMinor.GM08.Section9Paths
import GraphMinor.GM08.Section9Enclosed
import GraphMinor.GM08.Section8Sleeve

/-!
# Keeping the part of a truncation inside a ring

In the proof of Graph Minors VIII (9.1), page 270, early circuits of the nest lie
inside one foundation ring. This file shows that the part of the truncation
inside that ring belongs to its sleeve. Sleeves of other rings cannot enter it,
because the rings bound disjoint open discs.
-/

public section

namespace GraphMinor.GM08

open Set Surface Topology

universe u

variable {S : Type u} [TopologicalSpace S]

/-- If two rings bound disjoint open discs, no point of either ring is inside the other.
Work in a sphere chart so that a boundary point is a limit of interior points. -/
theorem not_insideOArc_of_boundDisjoint_of_mem {Δ F₁ F₂ : Set S}
    (hΔ : IsClosedDisc Δ) (hF₁ : F₁ ⊆ Δ) (hF₂ : F₂ ⊆ Δ)
    (ho₁ : IsOArc F₁) (ho₂ : IsOArc F₂) (hdis : BoundDisjointOpenDiscs Δ F₁ F₂)
    {x : S} (hx : x ∈ F₁) : ¬ InsideOArc Δ F₂ x := by
  intro hx₂
  obtain ⟨B₁, hB₁, -⟩ := disc_oArc Δ F₁ hΔ hF₁ ho₁
  obtain ⟨B₂, hB₂, -⟩ := disc_oArc Δ F₂ hΔ hF₂ ho₂
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hΔ
  have hS : IsClosedSurface SphereSurf :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have hman : ∀ p : SphereSurf, IsManifoldPoint p := fun p => (hS.2.2 p).isManifoldPoint
  have hB₁' := (sc.disc_f hB₁.1 hB₁.2.1).1
  have hB₂' := (sc.disc_f hB₂.1 hB₂.2.1).1
  have hxB₁ : f x ∈ f '' B₁ :=
    mem_image_of_mem f (discBd_subset B₁ (hB₁.2.2.1 ▸ hx))
  have hxB₂ : f x ∈ discInt (f '' B₂) := by
    rw [sc.discInt_f hB₂.1 hB₂.2.1]
    exact mem_image_of_mem f ((insideOArc_iff_mem_discInt hΔ hB₂).mp hx₂)
  obtain ⟨z, hz₂, hz₁⟩ := mem_closure_iff.mp (hB₁'.subset_closure_discInt hxB₁) _
    (hB₂'.isOpen_discInt hman) hxB₂
  rw [sc.discInt_f hB₁.1 hB₁.2.1] at hz₁
  rw [sc.discInt_f hB₂.1 hB₂.2.1] at hz₂
  obtain ⟨y₁, hy₁, rfl⟩ := hz₁
  obtain ⟨y₂, hy₂, heq⟩ := hz₂
  have heq' : y₂ = y₁ := sc.injOn_f (hB₂.1 hy₂.1) (hB₁.1 hy₁.1) heq
  exact Set.disjoint_left.mp hdis
    ((insideOArc_iff_mem_discInt hΔ hB₁).mpr hy₁)
    (heq' ▸ (insideOArc_iff_mem_discInt hΔ hB₂).mpr hy₂)

/-- Every point of a sleeve lies inside its ring or on its ring. -/
theorem IsSleeve.inside_or_mem {D Γ : Drawing S} {Δ F : Set S}
    (h : IsSleeve D Δ F Γ) {x : S} (hx : x ∈ Γ.U) :
    InsideOArc Δ F x ∨ x ∈ F := by
  obtain ⟨-, -, -, -, sd, hV, hE⟩ := h
  have hC : ∀ j, ∀ x ∈ (sd.circuitDraw j).U, InsideOArc Δ F x := fun j x hx =>
    sd.circuit_inside j x ((sd.isCircuit_draw j).2.2 ▸ hx)
  have hP : ∀ i, ∀ x ∈ (sd.spoke i).U, InsideOArc Δ F x ∨ x ∈ F := by
    intro i x hx
    by_cases hxF : x ∈ F
    · exact Or.inr hxF
    · obtain ⟨-, -, -, -, -, -, -, henc, -⟩ := sd.isPath_spoke i
      exact Or.inl (henc x ⟨hx, hxF⟩)
  by_cases hxV : x ∈ Γ.V
  · rw [hV] at hxV
    rcases hxV with hxC | hxP
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hxC
      exact Or.inl (hC j x ((sd.circuitDraw j).V_subset_U hj))
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hxP
      exact hP i x ((sd.spoke i).V_subset_U hi)
  · obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem hx hxV
    rw [hE] at he
    rcases he with heC | heP
    · obtain ⟨j, hj⟩ := mem_iUnion.mp heC
      exact Or.inl (hC j x (hj.2.1 hxe).1)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp heP
      exact hP i x (hi.2.1 hxe).1

/-- A sleeve cannot enter the open disc of a disjoint foundation ring. -/
theorem IsSleeve.not_inside_of_boundDisjoint {D Γ : Drawing S} {Δ F₁ F₂ : Set S}
    (hΔ : IsClosedDisc Δ) (h : IsSleeve D Δ F₁ Γ)
    (hF₂ : F₂ ⊆ Δ) (ho₂ : IsOArc F₂) (hdis : BoundDisjointOpenDiscs Δ F₁ F₂)
    {x : S} (hx : x ∈ Γ.U) : ¬ InsideOArc Δ F₂ x := by
  rcases h.inside_or_mem hx with hin | hon
  · exact fun hx₂ => Set.disjoint_left.mp hdis hin hx₂
  · exact not_insideOArc_of_boundDisjoint_of_mem hΔ h.1 hF₂ h.2.1 ho₂ hdis hon

/-- The spokes of a sleeve reach every drawing vertex on its ring.
Their ends are distinct and their number is the number of vertices on the ring. -/
theorem IsSleeve.boundary_vertices_subset {D Γ : Drawing S} {Δ F : Set S}
    (h : IsSleeve D Δ F Γ) : D.V ∩ F ⊆ Γ.V := by
  classical
  obtain ⟨-, -, -, -, sd, hV, -⟩ := h
  choose hs u v hsub hu hv hpath henc hVF using sd.isPath_spoke
  have hvV : ∀ i, v i ∈ (sd.spoke i).V := fun i =>
    ((hVF i).symm ▸ mem_singleton (v i) : v i ∈ (sd.spoke i).V ∩ F).1
  have hinj : Function.Injective v := by
    intro i j heq
    by_contra hne
    exact Set.disjoint_left.mp (sd.pairwise_disjoint_spokes hne) (hvV i) (heq ▸ hvV j)
  have hsubv : range v ⊆ D.V ∩ F := by
    rintro _ ⟨i, rfl⟩
    exact ⟨(hsub i).1 (hvV i), hv i⟩
  have hrange : range v = D.V ∩ F := Set.eq_of_subset_of_ncard_le hsubv
    (by rw [Set.ncard_range_of_injective hinj, Nat.card_fin])
    (D.finite_V.subset inter_subset_left)
  intro x hx
  obtain ⟨i, rfl⟩ : x ∈ range v := hrange.symm ▸ hx
  rw [hV]
  exact Or.inr (mem_iUnion.mpr ⟨i, hvV i⟩)

/-- For each foundation ring, the vertices and edges of the truncation inside it
belong to its sleeve. The other sleeves are excluded by disjointness of the open discs. -/
theorem IsTruncationInducedBy.exists_sleeve_containing_inside {D Dstar : Drawing S}
    {Δ : Set S} {t : ℕ} {F : Fin t → Set S}
    (hΔ : IsClosedDisc Δ) (h : IsTruncationInducedBy D Δ F Dstar) (i : Fin t) :
    ∃ Γ : Drawing S, IsSleeve D Δ (F i) Γ ∧
      (∀ x ∈ Dstar.V, InsideOArc Δ (F i) x → x ∈ Γ.V) ∧
      ∀ e ∈ Dstar.E, SetInsideOArc Δ (F i) e → e ∈ Γ.E := by
  obtain ⟨hfound, -, Γs, hsleeve, hV, hE⟩ := h
  obtain ⟨C, -, -, -, hmin, hdis, -⟩ := hfound
  refine ⟨Γs i, hsleeve i, ?_, ?_⟩
  · intro x hx hin
    rw [hV] at hx
    rcases hx with hout | hs
    · exact False.elim (hout.2 i hin)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hs
      by_cases hji : j = i
      · exact hji ▸ hj
      · exact False.elim ((hsleeve j).not_inside_of_boundDisjoint hΔ
          (hmin i).1.1 (hmin i).1.2.1 (hdis hji) ((Γs j).V_subset_U hj) hin)
  · intro e he hin
    have hne := he.1
    rw [hE] at he
    rcases he with hout | hs
    · exact False.elim (hout.2 i hin)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hs
      by_cases hji : j = i
      · exact hji ▸ hj
      · obtain ⟨x, hx⟩ := hne
        exact False.elim ((hsleeve j).not_inside_of_boundDisjoint hΔ
          (hmin i).1.1 (hmin i).1.2.1 (hdis hji) (hj.2.1 hx).1 (hin x hx))

/-- An edge cannot cross a normal ring. If it meets the inside, it is entirely inside. -/
theorem edge_inside_or_disjoint_normal_ring {D : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hFΔ : F ⊆ Δ) (hFo : IsOArc F)
    (hFn : D.IsNormal F) {e : Set S} (he : e ∈ D.E) :
    SetInsideOArc Δ F e ∨ Disjoint e {x | InsideOArc Δ F x} := by
  obtain ⟨B, hB, -⟩ := disc_oArc Δ F hΔ hFΔ hFo
  have hdis : Disjoint e (discBd B) := by
    rw [hB.2.2.1]
    exact Set.disjoint_left.mpr fun x hxe hxF =>
      (he.2.1 hxe).2 (hFn ⟨hxF, (he.2.1 hxe).1⟩)
  rcases side_of_closedDisc hΔ hB.1 (fun x hx => hDU (he.2.1 hx).1)
      hB.2.1 he.2.2.1.isConnected.isPreconnected hdis with hin | hout
  · exact Or.inl fun x hx => (insideOArc_iff_mem_discInt hΔ hB).mpr (hin hx)
  · exact Or.inr (Set.disjoint_left.mpr fun x hxe hxin =>
      Set.disjoint_left.mp hout hxe ((insideOArc_iff_mem_discInt hΔ hB).mp hxin).1)

/-- The whole point set of the truncation inside a foundation ring belongs to its sleeve.
For a nonvertex point, normality forces its edge to stay inside the ring. -/
theorem IsTruncationInducedBy.exists_sleeve_containing_points {D Dstar : Drawing S}
    {Δ : Set S} {t : ℕ} {F : Fin t → Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ)
    (h : IsTruncationInducedBy D Δ F Dstar) (i : Fin t) :
    ∃ Γ : Drawing S, IsSleeve D Δ (F i) Γ ∧
      ∀ x ∈ Dstar.U, InsideOArc Δ (F i) x → x ∈ Γ.U := by
  obtain ⟨Γ, hΓ, hV, hE⟩ := h.exists_sleeve_containing_inside hΔ i
  refine ⟨Γ, hΓ, fun x hx hin => ?_⟩
  by_cases hxV : x ∈ Dstar.V
  · exact Γ.V_subset_U (hV x hxV hin)
  · obtain ⟨e, he, hxe⟩ := Dstar.exists_edge_of_mem hx hxV
    have heD : e ∈ D.E := h.2.1.2 he
    rcases edge_inside_or_disjoint_normal_ring hΔ hDU hΓ.1 hΓ.2.1 hΓ.2.2.1 heD
        with hein | heout
    · exact ((hE e he hein).2.1 hxe).1
    · exact False.elim (Set.disjoint_left.mp heout hxe hin)

/-- Points of the truncation enclosed by a foundation ring belong to its sleeve.
The strict interior is handled by disjointness, and the ring vertices are the spoke ends. -/
theorem IsTruncationInducedBy.exists_sleeve_containing_enclosed_points {D Dstar : Drawing S}
    {Δ : Set S} {t : ℕ} {F : Fin t → Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ)
    (h : IsTruncationInducedBy D Δ F Dstar) (i : Fin t) :
    ∃ Γ : Drawing S, IsSleeve D Δ (F i) Γ ∧
      ∀ x ∈ Dstar.U, InsideOArc Δ (F i) x ∨ x ∈ F i → x ∈ Γ.U := by
  obtain ⟨Γ, hΓ, hpoints⟩ := h.exists_sleeve_containing_points hΔ hDU i
  refine ⟨Γ, hΓ, fun x hx hside => ?_⟩
  rcases hside with hin | hon
  · exact hpoints x hx hin
  · exact Γ.V_subset_U (hΓ.boundary_vertices_subset
      ⟨hΓ.2.2.1 ⟨hon, h.2.1.U_subset hx⟩, hon⟩)

/-- A circuit of the truncation inside a foundation ring can be regarded as a circuit
of that ring's sleeve. Its point set and inside disc are unchanged. -/
theorem IsTruncationInducedBy.exists_sleeve_containing_circuits {D Dstar : Drawing S}
    {Δ : Set S} {t : ℕ} {F : Fin t → Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ)
    (h : IsTruncationInducedBy D Δ F Dstar) (i : Fin t) :
    ∃ Γ : Drawing S, IsSleeve D Δ (F i) Γ ∧
      ∀ C : DiscCircuit Dstar Δ, SetInsideOArc Δ (F i) C.U →
        ∃ C' : DiscCircuit Γ Δ, C'.U = C.U ∧ C'.ins = C.ins := by
  obtain ⟨Γ, hΓ, hpoints⟩ := h.exists_sleeve_containing_points hΔ hDU i
  refine ⟨Γ, hΓ, fun C hin => ?_⟩
  exact ⟨{
    U := C.U
    ins := C.ins
    U_sub_drawing := fun x hx => hpoints x (C.U_sub_drawing hx) (hin x hx)
    U_sub_disc := C.U_sub_disc
    isOArc_U := C.isOArc_U
    isInside := C.isInside
  }, rfl, rfl⟩

/-- If the early circuits of a nest are enclosed by a foundation ring, their radial
paths can be cut there to give a nest in the sleeve. This is the restriction
step in Graph Minors VIII (9.1), page 270, when at least two circuits are kept. Enclosed circuits may meet the ring. -/
theorem IsTruncationInducedBy.exists_sleeve_nest_of_enclosed {S : Type u} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hman : ∀ x : S, IsManifoldPoint x)
    {D Dstar : Drawing S} {Δ : Set S} {t : ℕ} {F : Fin t → Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ)
    (h : IsTruncationInducedBy D Δ F Dstar) (i : Fin t)
    {r s q : ℕ} (N : DrawingNest Dstar Δ r s) (hq : 2 ≤ q) (hqs : q ≤ s)
    (hin : ∀ j : Fin q, OArcEncloses Δ (F i) (N.circuit (Fin.castLE hqs j)).U) :
    ∃ Γ : Drawing S, IsSleeve D Δ (F i) Γ ∧ Nonempty (DrawingNest Γ Δ r q) := by
  classical
  obtain ⟨Γ, hΓ, hpoints⟩ := h.exists_sleeve_containing_enclosed_points hΔ hDU i
  let jlast : Fin s := ⟨q - 1, by omega⟩
  obtain ⟨P, a, b, hP, hdis⟩ := N.exists_radial_paths_inside_circuit hman hΔ jlast (by
    dsimp [jlast]
    omega)
  have hlast : OArcEncloses Δ (F i) (N.circuit jlast).U := hin ⟨q - 1, by omega⟩
  obtain ⟨B, hB, -⟩ := disc_oArc Δ (F i) hΔ hΓ.1 hΓ.2.1
  have hmono := insideDisc_subset_of_oArcEncloses hΔ hB (N.circuit jlast).isInside hlast
  have hside : ∀ x ∈ B, InsideOArc Δ (F i) x ∨ x ∈ F i := by
    intro x hx
    by_cases hxF : x ∈ F i
    · exact Or.inr hxF
    · exact Or.inl ((insideOArc_iff_mem_discInt hΔ hB).mpr ⟨hx, hB.2.2.1 ▸ hxF⟩)
  have hcirc : ∀ j : Fin q, ∀ x ∈ (N.circuit (Fin.castLE hqs j)).U,
      InsideOArc Δ (F i) x ∨ x ∈ F i := by
    intro j x hx
    by_cases hxF : x ∈ F i
    · exact Or.inr hxF
    · exact Or.inl (hin j x ⟨hx, hxF⟩)
  have hPU : ∀ p, (P p).U ⊆ Γ.U := fun p x hx =>
    hpoints x ((hP p).1.U_subset hx)
      (hside x (hmono.1 ((hP p).2.2.2.2.2 hx)))
  have hends : ∀ p, a p ∈ (P p).U ∧ b p ∈ (P p).U := by
    intro p
    obtain ⟨W, -, -, -⟩ := (hP p).2.1
    exact ⟨(P p).V_subset_U (W.mem_vertexSet_of_mem_support W.start_mem_support),
      (P p).V_subset_U (W.mem_vertexSet_of_mem_support W.end_mem_support)⟩
  refine ⟨Γ, hΓ, ⟨{
    circuit := fun j => {
      U := (N.circuit (Fin.castLE hqs j)).U
      ins := (N.circuit (Fin.castLE hqs j)).ins
      U_sub_drawing := fun x hx =>
        hpoints x ((N.circuit _).U_sub_drawing hx) (hcirc j x hx)
      U_sub_disc := (N.circuit _).U_sub_disc
      isOArc_U := (N.circuit _).isOArc_U
      isInside := (N.circuit _).isInside
    }
    inside_of_lt hij := N.inside_of_lt (Fin.lt_def.mpr (Fin.lt_def.mp hij))
    radialPath p := (P p).U
    isPreconnected_radialPath p := isPreconnected_U_of_isPathBetween (hP p).2.1
    radialPath_sub_U := hPU
    radialPath_sub_disc p := (hP p).1.U_subset.trans (h.2.1.U_subset.trans hDU)
    pairwise_disjoint_paths := fun p p' hpp' => by
      apply Set.disjoint_left.mpr
      rintro x ⟨hxp, hxV⟩ ⟨hxp', -⟩
      have hxD : x ∈ D.V := hΓ.2.2.2.1.1 hxV
      have hpD := (hP p).1.trans h.2.1
      have hpD' := (hP p').1.trans h.2.1
      exact Set.disjoint_left.mp (hdis hpp')
        (mem_subdrawing_vertex_of_mem_U hpD hxp hxD)
        (mem_subdrawing_vertex_of_mem_U hpD' hxp' hxD)
    meets_inner p _hs := ⟨a p, (hends p).1, (hP p).2.2.1⟩
    meets_outer p _hs := ⟨b p, (hends p).2, (hP p).2.2.2.1⟩
  }⟩⟩

/-- The sleeve reduction in the proof of VIII (9.1), page 270, with one more
enclosed circuit retained when `k` is even. Once a foundation ring encloses
the first circuit, the sleeve contains an `(r, k / 2 + 1)`-nest.
This avoids the one-circuit loss in the printed argument when `k = 2`. -/
theorem IsTruncationInducedBy.exists_sleeve_nest_of_encloses_first
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hman : ∀ x : S, IsManifoldPoint x) {D Dstar : Drawing S} {Δ : Set S}
    {t : ℕ} {F : Fin t → Set S} (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ)
    (h : IsTruncationInducedBy D Δ F Dstar) (i : Fin t)
    {r s : ℕ} (N : DrawingNest Dstar Δ r s)
    (hk : 2 ≤ (D.V ∩ discBd Δ).ncard)
    (hr : (D.V ∩ discBd Δ).ncard ≤ r) (hs : (D.V ∩ discBd Δ).ncard ≤ s)
    (henc : OArcEncloses Δ (F i) (N.circuit ⟨0, by omega⟩).U) :
    ∃ Γ : Drawing S, IsSleeve D Δ (F i) Γ ∧
      Nonempty (DrawingNest Γ Δ r ((D.V ∩ discBd Δ).ncard / 2 + 1)) := by
  obtain ⟨C, hboss, -, -, hmin, -⟩ := h.1
  have hcard : (D.V ∩ F i).ncard < (D.V ∩ discBd Δ).ncard := by
    rw [(hmin i).1.2.2.2.2]
    exact (hboss i).rho_lt
  let N' := N.ofSubdrawing h.2.1
  have hqs : (D.V ∩ discBd Δ).ncard / 2 + 1 ≤ s := by omega
  apply h.exists_sleeve_nest_of_enclosed hman hΔ hDU i N (by omega) hqs
  intro j
  exact N'.initial_circuits_enclosed hΔ (by omega) hr hs
    (hmin i).1.1 (hmin i).1.2.1 (hmin i).1.2.2.1 henc hcard j

end GraphMinor.GM08
