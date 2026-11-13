module

public import GraphMinor.GM21.Section6ClaimThreeLine
public import GraphMinor.GM21.Section6Induction
import GraphMinor.GM21.Section6TwoEdges
import GraphMinor.GM19.CapExists
import GraphMinor.GM07.Section8
import GraphMinor.GM07.Reroute
import GraphMinor.GM17.Basic
import GraphMinor.GM11.Walks
import GraphMinor.GM06.Section3Dual

/-!
# Graph Minors XXI, (6.3), claim (3): finding the line between two cuffs

Claim (3) of the proof of (6.3) (page 29 of the preprint): "If $c(\Sigma) \ge 2$ then there
is a region of $\Gamma$ incident with vertices in two different cuffs, and so there is a proper line
$F$ with ends vertices of $\Gamma$ in different cuffs, and with no internal point in $U(\Gamma)$."

The first step needs that `Γ` is part of the linkage `L`, so that `Γ` is a union of disjoint paths
(see the correction to the proof of (6.3) in `corrections/GM21.md`). With a cycle of `Γ` around
the hole of an annulus, no region meets both cuffs. We work with the regions of the drawing `Γ⁺` in
the capped surface `Σ̂` (`exists_properLine_between_cuffs`). There are two cases.

* Some jump `J` of `Γ` has its ends in different cuffs (`exists_properLine_of_jump`). A region of
  `Γ⁺` along an edge of `J` holds both ends of `J` in its closure (`mem_closure_of_jump`).
* Every jump has both ends in one cuff. Fix a cuff `C₁`. Let `A₁ ⊆ Σ̂` be the pasted closed disc of
  `C₁` together with the jumps with an end in `C₁`, and `A₂` the other pasted closed discs together
  with the other jumps. These are disjoint closed sets, and `U(Γ⁺) ⊆ A₁ ∪ A₂`. A line `P` in `Σ̂` from
  `u ∈ A₁` to `v ∈ A₂` that meets `A₁ ∪ A₂` only in its ends (`GM07`, (8.?)
  `exists_connecting_line_between_disjoint_closed`) runs inside one region `p` of `Γ⁺`. From `u`,
  the closure of `p` reaches a vertex of `Γ` in `C₁`, along a space of `Γ`
  (`exists_vertex_of_mem_closure_bd`) or along a jump (`mem_closure_of_jump`). In the same way it
  reaches from `v` a vertex of `Γ` in `bd(Σ) \ C₁` (`exists_properLine_of_one_cuff`).

In both cases `exists_properLine_of_region` gives the line.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace ClaimThree

open Set Function Topology GraphMinor.Surface Hypergraph GraphMinor.GM19

universe u v

section basics

variable {S : Type} [TopologicalSpace S]

/-- A cuff through `w` is the component of `bd(Σ)` at `w`. -/
theorem cuff_eq_cc {C : Set S} (hC : C ∈ cuffs S) {w : S} (hw : w ∈ C) :
    C = connectedComponentIn (bd S) w := by
  obtain ⟨z, -, rfl⟩ := hC
  exact connectedComponentIn_eq hw

/-- A cuff lies in `bd(Σ)`. -/
theorem cuff_subset_bd {C : Set S} (hC : C ∈ cuffs S) : C ⊆ bd S := by
  obtain ⟨_, -, rfl⟩ := hC
  exact connectedComponentIn_subset _ _

/-- A point of `bd(Σ)` in the closure of an edge of a proper drawing is a vertex. -/
theorem mem_V_of_mem_closure_of_mem_bd {Γ : Surface.Drawing S} (hprop : Γ.IsProper) {e : Set S}
    (he : e ∈ Γ.E) {w : S} (hw : w ∈ closure e) (hwb : w ∈ bd S) : w ∈ Γ.V :=
  hprop ⟨hwb, closure_minimal (fun _ hz => (he.2.1 hz).1) Γ.isClosed_U hw⟩

/-- A point of the closure of an edge lies in the edge or is a vertex. -/
theorem mem_or_mem_V_of_mem_closure [T2Space S] {Γ : Surface.Drawing S} {e : Set S}
    (he : e ∈ Γ.E) {w : S} (hw : w ∈ closure e) : w ∈ e ∨ w ∈ Γ.V := by
  by_cases hwV : w ∈ Γ.V
  · exact Or.inr hwV
  · exact Or.inl (DiscLine.closure_inter_sdiff_subset Γ he
      ⟨hw, closure_minimal (fun _ hz => (he.2.1 hz).1) Γ.isClosed_U hw, hwV⟩)

variable {Shat : Type} [TopologicalSpace Shat]

/-- A point of `Σ` whose image lies in a closed pasted disc lies in its cuff. -/
theorem mem_of_emb_mem_closure_cuffDisc (hS : IsSurface S) (cap : IsCappedSurface S Shat)
    {C : Set S} (hC : C ∈ cuffs S) {w : S} (hw : cap.emb w ∈ closure (cap.cuffDisc C)) : w ∈ C := by
  have : T2Space S := hS.2.1
  rw [cap.closure_cuffDisc hS hC] at hw
  rcases hw with hw | ⟨w', hw'C, hw'⟩
  · exact (cap.notMem_range hC hw (mem_range_self w)).elim
  · exact cap.isEmbedding.injective hw' ▸ hw'C

/-- A region of `Γ⁺` whose closure holds the image of a point outside `bd(Σ)` meets the image of `Σ`:
otherwise it would be a pasted disc, whose closure meets the image of `Σ` only in a cuff. -/
theorem exists_emb_mem_region (hS : IsSurface S) (cap : IsCappedSurface S Shat)
    {Γ : Surface.Drawing S} (hprop : Γ.IsProper) (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard)
    {p : Set Shat} (hp : p ∈ (capDrawing hS cap (plusDrawing hS Γ hprop hge2)).R) {w : S}
    (hw : w ∉ bd S) (hwp : cap.emb w ∈ closure p) : ∃ z, cap.emb z ∈ p := by
  obtain ⟨t, ht⟩ := GM11.region_nonempty hp
  by_cases htr : t ∈ range cap.emb
  · obtain ⟨z, rfl⟩ := htr
    exact ⟨z, ht⟩
  have ht' : t ∈ (range cap.emb)ᶜ := htr
  rw [cap.compl_eq] at ht'
  obtain ⟨C, hC, htC⟩ := mem_iUnion₂.mp ht'
  have hpC : p = cap.cuffDisc C :=
    GM11.region_eq_of_mem hp (cuffDisc_mem_R_capDrawing_plusDrawing hS cap Γ hprop hge2 hC) ht htC
  rw [hpC] at hwp
  exact (hw (cuff_subset_bd hC (mem_of_emb_mem_closure_cuffDisc hS cap hC hwp))).elim

end basics

section main

variable {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
  {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ} {L : Hypergraph α β}

/-- A vertex in the closure of an edge of a jump is a vertex of the jump. -/
theorem mem_jump_of_mem_closure (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    {J : Hypergraph α β} (hJ : J ≤ Γ_sub) {e : Set S} (he : e ∈ Γ.E) (heJ : ιE e ∈ J.edgeSet)
    {w : S} (hwV : w ∈ Γ.V) (hw : w ∈ closure e) : ιV w ∈ J.vertexSet :=
  J.vertex_mem_of_inc ((GM10.inc_iff_of_le hJ heJ).2 ((hP.drawing_iso.inc_iff e he w hwV).2 hw))

/-- Every point of `U(Γ)` outside `bd(Σ)` lies in the closure of an edge: a vertex outside `bd(Σ)` has
two edges. -/
theorem exists_edge_of_mem_U (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (hL : IsExhaustiveLinkage G Γ_sub r H L) {w : S} (hw : w ∈ Γ.U) (hwb : w ∉ bd S) :
    ∃ e ∈ Γ.E, w ∈ closure e := by
  have hiso := hP.drawing_iso
  by_cases hwV : w ∈ Γ.V
  · have h2 := IsExhaustiveLinkage.ncard_incidentEdges_eq_two hP hL (ιV w)
      (hiso.ιV_image ▸ mem_image_of_mem ιV hwV)
      (by rintro ⟨y, hy, hyw⟩; exact hwb (hiso.ιV_injOn hy.1 hwV hyw ▸ hy.2))
    obtain ⟨f, hf⟩ := nonempty_of_ncard_ne_zero (s := incidentEdges Γ_sub (ιV w)) (by omega)
    obtain ⟨e, he, rfl⟩ : f ∈ ιE '' Γ.E := hiso.ιE_image ▸ hf.1
    exact ⟨e, he, (hiso.inc_iff e he w hwV).1 hf.2⟩
  · obtain ⟨e, he, hwe⟩ := Γ.exists_edge_of_mem hw hwV
    exact ⟨e, he, subset_closure hwe⟩

variable {Shat : Type} [TopologicalSpace Shat]

/-- **Claim (3), first case: a jump between two cuffs.** If a jump `J` has vertices `x ≠ y` in
`bd(Σ)`, then there is a proper line with ends `x, y` and no internal point in `U(Γ)`. A region of
`Γ⁺` along an edge of `J` has all of `J` in its closure (`mem_closure_of_jump`). -/
theorem exists_properLine_of_jump (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (hL : IsExhaustiveLinkage G Γ_sub r H L) (cap : IsCappedSurface S Shat) {J : Hypergraph α β}
    (hJ : J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))) {x y : S} (hx : x ∈ Γ.V ∩ bd S)
    (hy : y ∈ Γ.V ∩ bd S) (hxJ : ιV x ∈ J.vertexSet) (hyJ : ιV y ∈ J.vertexSet) (hxy : x ≠ y) :
    ∃ F : Set S, IsProperLineInSurface F x y ∧ F ∩ Γ.U ⊆ {x, y} := by
  have hS := hP.is_surface
  have : T2Space S := hS.2.1
  have hprop := hP.is_proper_drawing
  have hge2 := hP.cuff_vertices_ge_two
  obtain ⟨f, hf⟩ := edgeSet_nonempty_of_mem_jumpSet hJ
  obtain ⟨e, he, rfl⟩ : f ∈ ιE '' Γ.E := hP.drawing_iso.ιE_image ▸ hJ.1.edgeSet_subset hf
  obtain ⟨p, hp, hep⟩ := GM11.exists_region_incident cap.isClosedSurface
    (emb_mem_E_of_mem_E hS cap hprop hge2 he)
  obtain ⟨w, hw⟩ := he.1
  have hwp : cap.emb w ∈ closure p := hep ⟨w, hw, rfl⟩
  have hwb : w ∉ bd S := fun h => (he.2.1 hw).2 (hprop ⟨h, (he.2.1 hw).1⟩)
  have hall := mem_closure_of_jump hP hL cap hp hJ
    (Or.inl ⟨e, he, hf, ⟨cap.emb w, ⟨w, hw, rfl⟩, hwp⟩⟩)
  obtain ⟨z, hz⟩ := exists_emb_mem_region hS cap hprop hge2 hp hwb hwp
  exact exists_properLine_of_region hS cap hprop hge2 hp hz hx hy hxy (hall x hx.1 hxJ)
    (hall y hy.1 hyJ)

/-- **Claim (3), second case: every jump has both ends in one cuff.** Let `C₁ ≠ C₂` be cuffs. Then
there are vertices `x ∈ C₁` and `y ∈ bd(Σ) \ C₁` of `Γ` and a proper line with ends `x, y` and no
internal point in `U(Γ)`. -/
theorem exists_properLine_of_one_cuff (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (hL : IsExhaustiveLinkage G Γ_sub r H L) (cap : IsCappedSurface S Shat)
    (hH : ∀ J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S)), ∀ x ∈ Γ.V ∩ bd S, ∀ y ∈ Γ.V ∩ bd S,
      ιV x ∈ J.vertexSet → ιV y ∈ J.vertexSet →
        connectedComponentIn (bd S) x = connectedComponentIn (bd S) y)
    {C₁ C₂ : Set S} (hC₁ : C₁ ∈ cuffs S) (hC₂ : C₂ ∈ cuffs S) (h12 : C₁ ≠ C₂) :
    ∃ x ∈ Γ.V ∩ C₁, ∃ y ∈ Γ.V ∩ bd S, y ∉ C₁ ∧
      ∃ F : Set S, IsProperLineInSurface F x y ∧ F ∩ Γ.U ⊆ {x, y} := by
  classical
  have hS := hP.is_surface
  have : T2Space S := hS.2.1
  have hcs := cap.isClosedSurface
  have : T2Space Shat := hcs.2.1
  have : LocallyConnectedSpace Shat := GM11.IsClosedSurface.locallyConnectedSpace hcs
  have : PreconnectedSpace Shat := cap.connected.toPreconnectedSpace
  have hprop := hP.is_proper_drawing
  have hge2 := hP.cuff_vertices_ge_two
  have hiso := hP.drawing_iso
  have hK := IsExhaustiveLinkage.isLinkage hP hL
  have hdeg := IsExhaustiveLinkage.ncard_incidentEdges_eq_two hP hL
  have hinj := cap.isEmbedding.injective
  have hcf : (cuffs S).Finite := (cuff_statement S hS).2.1
  set B := ιV '' (Γ.V ∩ bd S)
  set D := capDrawing hS cap (plusDrawing hS Γ hprop hge2)
  -- The edges attached to `C₁`: their jump has a vertex in `C₁`.
  let att : Set S → Prop := fun e =>
    ∃ J ∈ jumpSet Γ_sub B, ιE e ∈ J.edgeSet ∧ ∃ x ∈ Γ.V ∩ C₁, ιV x ∈ J.vertexSet
  let K₁ : Set S := ⋃ e ∈ {e | e ∈ Γ.E ∧ att e}, closure e
  let K₂ : Set S := ⋃ e ∈ {e | e ∈ Γ.E ∧ ¬ att e}, closure e
  let A₁ : Set Shat := closure (cap.cuffDisc C₁) ∪ cap.emb '' K₁
  let A₂ : Set Shat := (⋃ C ∈ {C | C ∈ cuffs S ∧ C ≠ C₁}, closure (cap.cuffDisc C)) ∪
    cap.emb '' K₂
  have hjump : ∀ e ∈ Γ.E, ∃ J ∈ jumpSet Γ_sub B, ιE e ∈ J.edgeSet := fun e he =>
    exists_jump_of_edge hK hdeg (hiso.ιE_image ▸ mem_image_of_mem ιE he)
  -- Points of `K₁` and `K₂` in `bd(Σ)`.
  have hK₁bd : ∀ w ∈ K₁, w ∈ bd S → w ∈ C₁ ∧ w ∈ Γ.V := by
    intro w hw hwb
    obtain ⟨e, ⟨he, J, hJ, hf, x₀, hx₀, hx₀J⟩, hwe⟩ := mem_iUnion₂.mp hw
    have hwV := mem_V_of_mem_closure_of_mem_bd hprop he hwe hwb
    have hcc := hH J hJ w ⟨hwV, hwb⟩ x₀ ⟨hx₀.1, cuff_subset_bd hC₁ hx₀.2⟩
      (mem_jump_of_mem_closure hP hJ.1 he hf hwV hwe) hx₀J
    refine ⟨?_, hwV⟩
    rw [cuff_eq_cc hC₁ hx₀.2, ← hcc]
    exact mem_connectedComponentIn hwb
  have hK₂bd : ∀ w ∈ K₂, w ∈ bd S → w ∉ C₁ ∧ w ∈ Γ.V := by
    intro w hw hwb
    obtain ⟨e, ⟨he, hnatt⟩, hwe⟩ := mem_iUnion₂.mp hw
    have hwV := mem_V_of_mem_closure_of_mem_bd hprop he hwe hwb
    refine ⟨fun hwC => hnatt ?_, hwV⟩
    obtain ⟨J, hJ, hf⟩ := hjump e he
    exact ⟨J, hJ, hf, w, ⟨hwV, hwC⟩, mem_jump_of_mem_closure hP hJ.1 he hf hwV hwe⟩
  -- The two sets are closed, nonempty and disjoint, and they cover `U(Γ⁺)`.
  have hKc : ∀ (P : Set S → Prop), IsClosed (cap.emb '' ⋃ e ∈ {e | e ∈ Γ.E ∧ P e}, closure e) :=
    fun P => (cap.isClosedEmbedding hS).isClosedMap _
      ((Γ.finite_edges.subset fun e he => he.1).isClosed_biUnion fun _ _ => isClosed_closure)
  have hA₁c : IsClosed A₁ := isClosed_closure.union (hKc att)
  have hA₂c : IsClosed A₂ :=
    ((hcf.subset fun C hC => hC.1).isClosed_biUnion fun _ _ => isClosed_closure).union
      (hKc fun e => ¬ att e)
  have hcuffpt : ∀ C ∈ cuffs S, ∃ w, w ∈ C := by
    rintro C ⟨z, hz, rfl⟩
    exact ⟨z, mem_connectedComponentIn hz⟩
  have hembC : ∀ C ∈ cuffs S, ∀ w ∈ C, cap.emb w ∈ closure (cap.cuffDisc C) := by
    intro C hC w hw
    rw [cap.closure_cuffDisc hS hC]
    exact Or.inr ⟨w, hw, rfl⟩
  have : Nonempty Shat := by
    obtain ⟨w, -⟩ := hcuffpt C₁ hC₁
    exact ⟨cap.emb w⟩
  have hA₁ne : A₁.Nonempty := by
    obtain ⟨w, hw⟩ := hcuffpt C₁ hC₁
    exact ⟨_, Or.inl (hembC C₁ hC₁ w hw)⟩
  have hA₂ne : A₂.Nonempty := by
    obtain ⟨w, hw⟩ := hcuffpt C₂ hC₂
    exact ⟨_, Or.inl (mem_iUnion₂.mpr ⟨C₂, ⟨hC₂, h12.symm⟩, hembC C₂ hC₂ w hw⟩)⟩
  have hdisj : Disjoint A₁ A₂ := by
    rw [disjoint_left]
    rintro t (ht₁ | ⟨w, hwK, rfl⟩) ht₂
    · rcases ht₂ with ht₂ | ⟨w', hw'K, rfl⟩
      · obtain ⟨C, ⟨hC, hCne⟩, htC⟩ := mem_iUnion₂.mp ht₂
        exact disjoint_left.mp (cap.cuffDisc_disjoint C₁ hC₁ C hC hCne.symm) ht₁ htC
      · have hw'C := mem_of_emb_mem_closure_cuffDisc hS cap hC₁ ht₁
        exact (hK₂bd w' hw'K (cuff_subset_bd hC₁ hw'C)).1 hw'C
    · rcases ht₂ with ht₂ | ⟨w', hw'K, hww'⟩
      · obtain ⟨C, ⟨hC, hCne⟩, htC⟩ := mem_iUnion₂.mp ht₂
        have hwC := mem_of_emb_mem_closure_cuffDisc hS cap hC htC
        have hwC₁ := (hK₁bd w hwK (cuff_subset_bd hC hwC)).1
        exact hCne (Induction.eq_of_mem_cuffs_of_mem hC hC₁ hwC hwC₁)
      · obtain rfl := hinj hww'
        obtain ⟨e, ⟨he, J, hJ, hf, x₀, hx₀, hx₀J⟩, hwe⟩ := mem_iUnion₂.mp hwK
        obtain ⟨e', ⟨he', hnatt⟩, hwe'⟩ := mem_iUnion₂.mp hw'K
        by_cases hwb : w' ∈ bd S
        · exact (hK₂bd w' hw'K hwb).1 (hK₁bd w' hwK hwb).1
        rcases mem_or_mem_V_of_mem_closure he hwe with hw | hwV
        · rcases mem_or_mem_V_of_mem_closure he' hwe' with hw' | hwV
          · have hee : e = e' := by
              by_contra hne
              exact disjoint_left.mp (GM06.disjoint_edges_of_ne Γ he he' hne) hw hw'
            subst hee
            exact hnatt ⟨J, hJ, hf, x₀, hx₀, hx₀J⟩
          · exact (he.2.1 hw).2 hwV
        · obtain ⟨J', hJ', hf'⟩ := hjump e' he'
          have hnB : ιV w' ∉ B := by
            rintro ⟨y, hy, hyw⟩
            exact hwb (hiso.ιV_injOn hy.1 hwV hyw ▸ hy.2)
          have hJJ := jump_eq_of_vertex hdeg hJ hJ'
            (mem_jump_of_mem_closure hP hJ.1 he hf hwV hwe)
            (mem_jump_of_mem_closure hP hJ'.1 he' hf' hwV hwe') hnB
          subst hJJ
          exact hnatt ⟨J, hJ', hf', x₀, hx₀, hx₀J⟩
  have hcover : D.U ⊆ A₁ ∪ A₂ := by
    rw [capDrawing_U, plusDrawing_U]
    rintro _ ⟨w, hw, rfl⟩
    by_cases hwb : w ∈ bd S
    · have hC : connectedComponentIn (bd S) w ∈ cuffs S := ⟨w, hwb, rfl⟩
      have hwC := hembC _ hC w (mem_connectedComponentIn hwb)
      by_cases h1 : connectedComponentIn (bd S) w = C₁
      · exact Or.inl (Or.inl (h1 ▸ hwC))
      · exact Or.inr (Or.inl (mem_iUnion₂.mpr ⟨_, ⟨hC, h1⟩, hwC⟩))
    · have hwU : w ∈ Γ.U := hw.resolve_right hwb
      obtain ⟨e, he, hwe⟩ := exists_edge_of_mem_U hP hL hwU hwb
      by_cases hatt : att e
      · exact Or.inl (Or.inr ⟨w, mem_iUnion₂.mpr ⟨e, ⟨he, hatt⟩, hwe⟩, rfl⟩)
      · exact Or.inr (Or.inr ⟨w, mem_iUnion₂.mpr ⟨e, ⟨he, hatt⟩, hwe⟩, rfl⟩)
  -- A line from `A₁` to `A₂` that meets them only in its ends.
  have harc : GM11.IsArcConnected (univ : Set Shat) := by
    intro a _ b _ hab
    have hpc : IsPathConnected (univ : Set Shat) := GM11.isPathConnected_of_isOpen hcs isOpen_univ
      isPreconnected_univ univ_nonempty
    obtain ⟨P, -, hP'⟩ := ((GM07.joinedIn_iff_eq_or_exists_isLineWithEnds (mem_univ a)
      (mem_univ b)).mp (hpc.joinedIn a trivial b trivial)).resolve_left hab
    exact ⟨P, subset_univ P, hP'⟩
  obtain ⟨P, u, v, -, hu, hv, hPl, hPA₁, hPA₂⟩ :=
    GM07.exists_connecting_line_between_disjoint_closed harc (subset_univ _) (subset_univ _) hA₁c
      hA₂c hA₁ne hA₂ne hdisj
  obtain ⟨⟨t₀, ht₀⟩, hPpc⟩ := GM17.isPathConnected_diff_ends_of_isLineWithEnds hPl
  have hoff : ∀ t ∈ P \ {u, v}, t ∉ A₁ ∧ t ∉ A₂ := by
    intro t ht
    refine ⟨fun h => ht.2 (Or.inl ?_), fun h => ht.2 (Or.inr ?_)⟩
    · have : t ∈ P ∩ A₁ := ⟨ht.1, h⟩
      rwa [hPA₁] at this
    · have : t ∈ P ∩ A₂ := ⟨ht.1, h⟩
      rwa [hPA₂] at this
  have hPU : Disjoint (P \ {u, v}) D.U := disjoint_left.mpr fun t ht htU =>
    (hcover htU).elim (hoff t ht).1 (hoff t ht).2
  obtain ⟨p, hp, ht₀p⟩ := GM11.exists_region_of_notMem (Γ := D) (disjoint_left.mp hPU ht₀)
  have hPp : P \ {u, v} ⊆ p :=
    GM11.subset_region hp hPpc.isConnected.isPreconnected hPU ht₀ ht₀p
  have hPcl : P ⊆ closure p := by
    rw [← GM07.IsLineWithEnds.closure_sdiff hPl]
    exact closure_mono hPp
  have hucl : u ∈ closure p := hPcl hPl.left_mem
  have hvcl : v ∈ closure p := hPcl hPl.right_mem
  -- `p` is not a pasted disc, since it holds points off `A₁ ∪ A₂`.
  have hnotcap : ∀ C ∈ cuffs S, (cap.cuffDisc C ∩ closure p).Nonempty → False := by
    intro C hC hne
    have hR := cuffDisc_mem_R_capDrawing_plusDrawing hS cap Γ hprop hge2 hC
    obtain ⟨t, htC, htp⟩ := hne
    obtain ⟨t', ht'C, ht'p⟩ := mem_closure_iff.mp htp _ (GM11.region_isOpen hR) htC
    have hpC : p = cap.cuffDisc C := GM11.region_eq_of_mem hp hR ht'p ht'C
    have ht₀C : t₀ ∈ closure (cap.cuffDisc C) := subset_closure (hpC ▸ hPp ht₀)
    by_cases h1 : C = C₁
    · exact (hoff t₀ ht₀).1 (Or.inl (h1 ▸ ht₀C))
    · exact (hoff t₀ ht₀).2 (Or.inl (mem_iUnion₂.mpr ⟨C, ⟨hC, h1⟩, ht₀C⟩))
  have hcapcl : ∀ C ∈ cuffs S, ∀ t ∈ closure (cap.cuffDisc C), t ∈ closure p →
      ∃ w ∈ C, cap.emb w = t := by
    intro C hC t htC htp
    rw [cap.closure_cuffDisc hS hC] at htC
    rcases htC with htC | htC
    · exact (hnotcap C hC ⟨t, htC, htp⟩).elim
    · exact htC
  -- The point `t₀` lies in the image of `Σ`.
  obtain ⟨z, hz⟩ : ∃ z, cap.emb z ∈ p := by
    by_cases ht₀r : t₀ ∈ range cap.emb
    · obtain ⟨z, hz⟩ := ht₀r
      exact ⟨z, hz ▸ hPp ht₀⟩
    · have ht₀' : t₀ ∈ (range cap.emb)ᶜ := ht₀r
      rw [cap.compl_eq] at ht₀'
      obtain ⟨C, hC, htC⟩ := mem_iUnion₂.mp ht₀'
      exact (hnotcap C hC ⟨t₀, htC, subset_closure (hPp ht₀)⟩).elim
  -- From `u`, a vertex of `Γ` in `C₁`.
  obtain ⟨x, hxV, hxC, hxp⟩ : ∃ x ∈ Γ.V, x ∈ C₁ ∧ cap.emb x ∈ closure p := by
    rcases hu with hu | ⟨w, hwK, rfl⟩
    · obtain ⟨w, hwC, rfl⟩ := hcapcl C₁ hC₁ u hu hucl
      obtain ⟨x, hxV, hxcc, hxp⟩ :=
        exists_vertex_of_mem_closure_bd hS cap hprop hge2 hp (cuff_subset_bd hC₁ hwC) hucl
      exact ⟨x, hxV, (cuff_eq_cc hC₁ hwC) ▸ hxcc, hxp⟩
    · obtain ⟨e, ⟨he, J, hJ, hf, x₀, hx₀, hx₀J⟩, hwe⟩ := mem_iUnion₂.mp hwK
      by_cases hwb : w ∈ bd S
      · obtain ⟨hwC, hwV⟩ := hK₁bd w hwK hwb
        exact ⟨w, hwV, hwC, hucl⟩
      have hall := mem_closure_of_jump hP hL cap hp hJ (by
        rcases mem_or_mem_V_of_mem_closure he hwe with hw | hwV
        · exact Or.inl ⟨e, he, hf, ⟨cap.emb w, ⟨w, hw, rfl⟩, hucl⟩⟩
        · exact Or.inr ⟨w, hwV, hwb, mem_jump_of_mem_closure hP hJ.1 he hf hwV hwe, hucl⟩)
      exact ⟨x₀, hx₀.1, hx₀.2, hall x₀ hx₀.1 hx₀J⟩
  -- From `v`, a vertex of `Γ` in `bd(Σ) \ C₁`.
  obtain ⟨y, hyV, hyb, hyC, hyp⟩ : ∃ y ∈ Γ.V, y ∈ bd S ∧ y ∉ C₁ ∧ cap.emb y ∈ closure p := by
    rcases hv with hv | ⟨w, hwK, rfl⟩
    · obtain ⟨C, ⟨hC, hCne⟩, hvC⟩ := mem_iUnion₂.mp hv
      obtain ⟨w, hwC, rfl⟩ := hcapcl C hC v hvC hvcl
      obtain ⟨y, hyV, hycc, hyp⟩ :=
        exists_vertex_of_mem_closure_bd hS cap hprop hge2 hp (cuff_subset_bd hC hwC) hvcl
      rw [← cuff_eq_cc hC hwC] at hycc
      exact ⟨y, hyV, cuff_subset_bd hC hycc, fun hy => hCne (Induction.eq_of_mem_cuffs_of_mem hC hC₁ hycc hy),
        hyp⟩
    · obtain ⟨e', ⟨he', hnatt⟩, hwe'⟩ := mem_iUnion₂.mp hwK
      by_cases hwb : w ∈ bd S
      · obtain ⟨hwC, hwV⟩ := hK₂bd w hwK hwb
        exact ⟨w, hwV, hwb, hwC, hvcl⟩
      obtain ⟨J', hJ', hf'⟩ := hjump e' he'
      obtain ⟨_, ⟨y₀, hy₀, rfl⟩, b', -, -, hterm, -⟩ := hJ'.2.2
      have hy₀J : ιV y₀ ∈ J'.vertexSet := (show ιV y₀ ∈ terminals J' from hterm ▸ Or.inl rfl).1
      have hall := mem_closure_of_jump hP hL cap hp hJ' (by
        rcases mem_or_mem_V_of_mem_closure he' hwe' with hw | hwV
        · exact Or.inl ⟨e', he', hf', ⟨cap.emb w, ⟨w, hw, rfl⟩, hvcl⟩⟩
        · exact Or.inr ⟨w, hwV, hwb, mem_jump_of_mem_closure hP hJ'.1 he' hf' hwV hwe', hvcl⟩)
      exact ⟨y₀, hy₀.1, hy₀.2, fun hy => hnatt ⟨J', hJ', hf', y₀, ⟨hy₀.1, hy⟩, hy₀J⟩,
        hall y₀ hy₀.1 hy₀J⟩
  have hxy : x ≠ y := fun h => hyC (h ▸ hxC)
  exact ⟨x, ⟨hxV, hxC⟩, y, ⟨hyV, hyb⟩, hyC, exists_properLine_of_region hS cap hprop hge2 hp hz
    ⟨hxV, cuff_subset_bd hC₁ hxC⟩ ⟨hyV, hyb⟩ hxy hxp hyp⟩

end main

end ClaimThree
end GM21
end GraphMinor
