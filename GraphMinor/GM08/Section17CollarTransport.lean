module

public import GraphMinor.GM08.Section17CollarWheel
public import GraphMinor.GM07.Section9MoveOff
public import GraphMinor.GM12.Section3SubspaceDrawing
public import GraphMinor.GM07.Defs
public import GraphMinor.Hypergraph.Basic
import GraphMinor.GM08.Section17CollarOrder
import GraphMinor.GM08.Section17Paths
import GraphMinor.GM08.Section9NestLinkage
import GraphMinor.GM11.Defs
import GraphMinor.GM11.RadialChord
import GraphMinor.GM12.Section3SubspaceArcs
import GraphMinor.Thomas.Claims

/-!
# Carrying the linkage conditions into the larger cylinder

Let `X` be drawn in the cylinder `S` by `Γ`, and let `H` be the image of `Γ` in
the cap sphere with the spokes at the boundary vertices, read in the larger
cylinder `Q` (`CollarWheel.exists_collar_graftDrawing`). This file carries the
conditions of VII (9.3) from `S` to `Q`:

* a `Γ`-normal set of `S` has a normal image in `Q`, since spokes meet the image
  of `S` only at vertices;
* every normal arc of `Q` between the images of the two hoops contains the
  image of a normal arc of `S` between the hoops, with no more vertices;
* disjoint paths of `S` map to disjoint paths of `Q`;
* a path of `S` that ends on a cuff extends by the spoke at its end to a path
  that ends on the corresponding cuff of `Q`.
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM12

variable {S : Type} [TopologicalSpace S]

/-- The ends of the spokes are not in the image of `S`. -/
theorem CollarWheel.q_not_mem_range {cap : CylinderSphereCap S} {P : Set S}
    (W : CollarWheel cap P) {x : S} (hx : x ∈ P) : W.q (cap.j x) ∉ range cap.j := by
  have h : W.q (cap.j x) ∈ ({W.q (cap.j x)} : Set cap.Z) := rfl
  rw [← W.inter_E x hx] at h
  rintro ⟨y, hy⟩
  rcases h.2 with h' | h'
  · exact disjoint_left.mp cap.disjoint_range_discInt_D₁ ⟨y, hy⟩ (W.E₁_subset h')
  · exact disjoint_left.mp cap.disjoint_range_discInt_D₂ ⟨y, hy⟩ (W.E₂_subset h')

/-- The end of a spoke lies on the spoke. -/
theorem CollarWheel.q_mem_ℓ {cap : CylinderSphereCap S} {P : Set S}
    (W : CollarWheel cap P) {x : S} (hx : x ∈ P) : W.q (cap.j x) ∈ W.ℓ (cap.j x) := by
  have h : W.q (cap.j x) ∈ ({W.q (cap.j x)} : Set cap.Z) := rfl
  rw [← W.inter_E x hx] at h
  exact h.1

/-- A point of `S` whose image is a vertex of `H` is a vertex of `Γ`. -/
theorem CollarWheel.mem_V_of_j_mem {cap : CylinderSphereCap S} {P : Set S}
    (W : CollarWheel cap P) {Γ : Drawing S} {H : Drawing cap.Z}
    (hHV : H.V = cap.j '' Γ.V ∪ (fun x => W.q (cap.j x)) '' P)
    {x : S} (hx : cap.j x ∈ H.V) : x ∈ Γ.V := by
  rw [hHV] at hx
  rcases hx with ⟨y, hy, hyx⟩ | ⟨y, hy, hyx⟩
  · exact cap.inj hyx ▸ hy
  · exact absurd ⟨x, hyx.symm⟩ (W.q_not_mem_range hy)

/-- A `Γ`-normal set of `S` has a normal image in `Q`. -/
theorem CollarWheel.isNormal_liftEdge {cap : CylinderSphereCap S} {P : Set S}
    (W : CollarWheel cap P) {Γ : Drawing S} (hP : Γ.V ∩ bd S = P) {H : Drawing cap.Z}
    (hHQ : H.U ⊆ discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z))
    (hHU : H.U = cap.j '' Γ.U ∪ ⋃ x ∈ P, W.ℓ (cap.j x))
    (hHV : H.V = cap.j '' Γ.V ∪ (fun x => W.q (cap.j x)) '' P)
    {F : Set S} (hN : Γ.IsNormal F) :
    (drawingInSubspace H _ hHQ).IsNormal (liftEdge cap.j _ F) := by
  have hPV : P ⊆ Γ.V := hP ▸ inter_subset_left
  rintro x ⟨hxF, hxU⟩
  obtain ⟨y, hyF, hyx⟩ := hxF
  rw [drawingInSubspace_U, mem_preimage] at hxU
  rw [drawingInSubspace_V, mem_preimage, hHV]
  rw [hHU] at hxU
  rcases hxU with ⟨z, hz, hzx⟩ | hx
  · have hzy : z = y := cap.inj (hzx.trans hyx.symm)
    subst hzy
    exact Or.inl ⟨z, hN ⟨hyF, hz⟩, hzx⟩
  · obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
    have h : x.1 ∈ W.ℓ (cap.j p) ∩ range cap.j := ⟨hxp, y, hyx⟩
    rw [W.inter_range p hp] at h
    exact Or.inl ⟨p, hPV hp, h.symm⟩

/-- **Arcs in the larger cylinder.** A normal arc of `Q` between the images of
two hoops `B`, `A` (in the order `C₁, B, A, C₂`) has at least as many vertices
as some normal arc of `S` between `A` and `B`. -/
theorem CollarWheel.exists_line_le_ncard {cap : CylinderSphereCap S} {P : Set S}
    (W : CollarWheel cap P) (hS : IsCylinder S) {Γ : Drawing S} {H : Drawing cap.Z}
    (hHQ : H.U ⊆ discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z))
    (hHU : H.U = cap.j '' Γ.U ∪ ⋃ x ∈ P, W.ℓ (cap.j x))
    (hHV : H.V = cap.j '' Γ.V ∪ (fun x => W.q (cap.j x)) '' P)
    {A B : Set S} (hA : IsHoop A) (hB : IsHoop B) (hAB : Disjoint A B)
    (hle : cap.disc₁ hS.1 hB ⊆ cap.disc₁ hS.1 hA)
    {F : Set (discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z))}
    (hN : (drawingInSubspace H _ hHQ).IsNormal F) (hF : IsLine F)
    (hFA : (F ∩ liftEdge cap.j _ A).Nonempty) (hFB : (F ∩ liftEdge cap.j _ B).Nonempty) :
    ∃ L : Set S, IsLine L ∧ Γ.IsNormal L ∧ (L ∩ A).Nonempty ∧ (L ∩ B).Nonempty ∧
      (Γ.V ∩ L).ncard ≤ ((drawingInSubspace H _ hHQ).V ∩ F).ncard := by
  have hrange : range cap.j ⊆ discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z) := cap.range_subset_discComplement W.isClosedDisc_E₁
    W.isClosedDisc_E₂ W.E₁_subset W.E₂_subset
  obtain ⟨L, hL, hLA, hLB, hLF⟩ := cap.exists_line_of_collar_line hS hA hB hAB hle hF hFA hFB
  -- the point of `Q` over a point of `S`
  let φ : S → discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z) := fun x => ⟨cap.j x, hrange ⟨x, rfl⟩⟩
  have hφF : ∀ x ∈ L, φ x ∈ F := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hLF ⟨x, hx, rfl⟩
    have : y = φ x := Subtype.ext hyx
    exact this ▸ hy
  have hNL : Γ.IsNormal L := by
    rintro x ⟨hxL, hxU⟩
    have hU : φ x ∈ (drawingInSubspace H _ hHQ).U := by
      rw [drawingInSubspace_U, mem_preimage, hHU]
      exact Or.inl ⟨x, hxU, rfl⟩
    have hV := hN ⟨hφF x hxL, hU⟩
    rw [drawingInSubspace_V, mem_preimage] at hV
    exact W.mem_V_of_j_mem hHV hV
  refine ⟨L, hL, hNL, hLA, hLB, ?_⟩
  refine ncard_le_ncard_of_injOn φ ?_ ?_ ((drawingInSubspace H _ hHQ).finite_V.inter_of_left F)
  · rintro x ⟨hxV, hxL⟩
    refine ⟨?_, hφF x hxL⟩
    rw [drawingInSubspace_V, mem_preimage, hHV]
    exact Or.inl ⟨x, hxV, rfl⟩
  · intro x _ y _ hxy
    exact cap.inj (congrArg Subtype.val hxy)

/-- Path counts do not decrease when moving to a drawing with more vertices and edges. -/
theorem maxDisjointPaths_mono_of_isSubdrawing {T : Type} [TopologicalSpace T]
    {K H : Drawing T} (hsub : K.IsSubdrawing H) (X Y : Set T) :
    maxDisjointPaths K X Y ≤ maxDisjointPaths H X Y := by
  have h0 : HasDisjointPathsBetween K X Y 0 :=
    ⟨Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  have hmem : HasDisjointPathsBetween K X Y (maxDisjointPaths K X Y) :=
    Nat.sSup_mem ⟨0, h0⟩ ⟨K.V.ncard, fun _ hk => hasDisjointPathsBetween_le_ncard_V hk⟩
  exact le_maxDisjointPaths_of_paths (hasDisjointPathsBetween_of_isSubdrawing hsub hmem)

/-- Disjoint paths of `S` give as many disjoint paths in `Q` between the images. -/
theorem CollarWheel.maxDisjointPaths_le {cap : CylinderSphereCap S} {P : Set S}
    (W : CollarWheel cap P) [Nonempty S] {Γ : Drawing S} {H : Drawing cap.Z}
    (hHQ : H.U ⊆ discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z))
    (hHV : H.V = cap.j '' Γ.V ∪ (fun x => W.q (cap.j x)) '' P)
    (hHE : H.E = image cap.j '' Γ.E ∪
      (fun x => W.ℓ (cap.j x) \ {cap.j x, W.q (cap.j x)}) '' P) (X Y : Set S) :
    maxDisjointPaths Γ X Y ≤
      maxDisjointPaths (drawingInSubspace H _ hHQ) (liftEdge cap.j _ X) (liftEdge cap.j _ Y) := by
  have : T2Space cap.Z := cap.t2Space_Z
  have : T2Space S := cap.isClosedEmbedding.isEmbedding.t2Space
  have hj := cap.isClosedEmbedding
  have hrange : range cap.j ⊆ discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z) := cap.range_subset_discComplement W.isClosedDisc_E₁
    W.isClosedDisc_E₂ W.E₁_subset W.E₂_subset
  have hKQ : (embedDrawing hj Γ).U ⊆ discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z) := fun z ⟨x, _, hx⟩ => hrange ⟨x, hx⟩
  refine (maxDisjointPaths_le_liftEdge hj Γ _ hKQ X Y).trans
    (maxDisjointPaths_mono_of_isSubdrawing ⟨?_, ?_⟩ _ _)
  · rw [drawingInSubspace_embedDrawing_V, drawingInSubspace_V, hHV]
    exact preimage_mono subset_union_left
  · rw [drawingInSubspace_embedDrawing_E, drawingInSubspace_E, hHE]
    rintro _ ⟨e, he, rfl⟩
    exact ⟨_, Or.inl ⟨e, he, rfl⟩, rfl⟩

/-- **Paths to a cuff.** Disjoint paths of `S` from the vertices on a cuff `C`
to a set `F` extend, by the spokes at their starts, to as many disjoint paths of
`Q` from the image of `F` to the new cuff (the boundary of the small disc `E`).
So the number of vertices on the new cuff is at most the number of such paths. -/
theorem CollarWheel.ncard_cuff_le {cap : CylinderSphereCap S} {P : Set S}
    (W : CollarWheel cap P) {Γ : Drawing S} (hP : Γ.V ∩ bd S = P) {H : Drawing cap.Z}
    (hHQ : H.U ⊆ discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z))
    (hHU : H.U = cap.j '' Γ.U ∪ ⋃ x ∈ P, W.ℓ (cap.j x))
    (hHV : H.V = cap.j '' Γ.V ∪ (fun x => W.q (cap.j x)) '' P)
    (hHE : H.E = image cap.j '' Γ.E ∪
      (fun x => W.ℓ (cap.j x) \ {cap.j x, W.q (cap.j x)}) '' P)
    {C F : Set S} {E : Set cap.Z} (hCP : Γ.V ∩ C ⊆ P)
    (hqE : ∀ x ∈ Γ.V ∩ C, W.q (cap.j x) ∈ discBd E)
    (hVE : H.V ∩ discBd E ⊆ (fun x => W.q (cap.j x)) '' (Γ.V ∩ C))
    (hsk : HasDisjointPaths Γ.toHypergraph.skeleton (Γ.V ∩ C) (Γ.V ∩ F) (Γ.V ∩ C).ncard) :
    ((drawingInSubspace H _ hHQ).V ∩ (Subtype.val : discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z) → cap.Z) ⁻¹' discBd E).ncard ≤
      maxDisjointPaths (drawingInSubspace H _ hHQ) (liftEdge cap.j _ F)
        ((Subtype.val : discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z) → cap.Z) ⁻¹' discBd E) := by
  classical
  have : T2Space cap.Z := cap.t2Space_Z
  have hj := cap.isClosedEmbedding
  have hPV : P ⊆ Γ.V := hP ▸ inter_subset_left
  have hrange : range cap.j ⊆ discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z) := cap.range_subset_discComplement W.isClosedDisc_E₁
    W.isClosedDisc_E₂ W.E₁_subset W.E₂_subset
  let HQ := drawingInSubspace H _ hHQ
  have hEQ : ∀ e ∈ H.E, (Subtype.val : discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z) → cap.Z) ⁻¹' e ∈ HQ.E ∧
      closure ((Subtype.val : discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z) → cap.Z) ⁻¹' e) =
        (Subtype.val : discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z) → cap.Z) ⁻¹' closure e := by
    intro e he
    refine ⟨?_, closure_subtype_preimage fun x hx => hHQ (he.2.1 hx).1⟩
    change _ ∈ (drawingInSubspace H _ hHQ).E
    rw [drawingInSubspace_E]
    exact ⟨e, he, rfl⟩
  have hVQ : ∀ x : discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z), x ∈ HQ.V ↔ x.1 ∈ H.V := fun x => by
    change x ∈ (drawingInSubspace H _ hHQ).V ↔ _
    rw [drawingInSubspace_V]; rfl
  let φ : S → discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z) := fun x => ⟨cap.j x, hrange ⟨x, rfl⟩⟩
  have hφinj : Function.Injective φ := fun x y h => cap.inj (congrArg Subtype.val h)
  have hadj : ∀ x y, Γ.toHypergraph.skeleton.Adj x y →
      HQ.toHypergraph.skeleton.Adj (φ x) (φ y) := by
    rintro x y ⟨hxy, e, ⟨he, hxV, hxe⟩, ⟨-, hyV, hye⟩⟩
    have he₁ : cap.j '' e ∈ H.E := hHE ▸ Or.inl ⟨e, he, rfl⟩
    obtain ⟨heQ, hcl⟩ := hEQ _ he₁
    have hcl' : ∀ z ∈ closure e, φ z ∈ closure ((Subtype.val : discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z) → cap.Z) ⁻¹' (cap.j '' e)) := by
      intro z hz
      rw [hcl]
      exact image_closure_subset_closure_image hj.continuous ⟨z, hz, rfl⟩
    refine ⟨fun h => hxy (hφinj h), _, ⟨heQ, ?_, hcl' x hxe⟩, ⟨heQ, ?_, hcl' y hye⟩⟩
    · rw [hVQ, hHV]; exact Or.inl ⟨x, hxV, rfl⟩
    · rw [hVQ, hHV]; exact Or.inl ⟨y, hyV, rfl⟩
  let hom : Γ.toHypergraph.skeleton →g HQ.toHypergraph.skeleton :=
    ⟨φ, fun {x y} h => hadj x y h⟩
  have hqQ : ∀ c ∈ P, W.q (cap.j c) ∈ discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z) := fun c hc =>
    hHQ (hHU ▸ Or.inr (mem_iUnion₂.mpr ⟨c, hc, W.q_mem_ℓ hc⟩))
  let qc : ∀ c, c ∈ P → discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z) := fun c hc => ⟨W.q (cap.j c), hqQ c hc⟩
  have hsp : ∀ c (hc : c ∈ P), HQ.toHypergraph.skeleton.Adj (qc c hc) (φ c) := by
    intro c hc
    have he₁ : W.ℓ (cap.j c) \ {cap.j c, W.q (cap.j c)} ∈ H.E := hHE ▸ Or.inr ⟨c, hc, rfl⟩
    obtain ⟨heQ, hcl⟩ := hEQ _ he₁
    rw [GM11.closure_sdiff_pair (W.line c hc)] at hcl
    refine ⟨fun h => W.ne c hc (congrArg Subtype.val h).symm, _,
      ⟨heQ, ?_, ?_⟩, ⟨heQ, ?_, ?_⟩⟩
    · rw [hVQ, hHV]; exact Or.inr ⟨c, hc, rfl⟩
    · rw [hcl]; exact W.q_mem_ℓ hc
    · rw [hVQ, hHV]; exact Or.inl ⟨c, hPV hc, rfl⟩
    · rw [hcl]
      obtain ⟨ψ, h0, -⟩ := W.line c hc
      have h := (ψ 0).2
      rw [h0] at h
      exact h
  have hqr : ∀ c (hc : c ∈ P) (a : S), φ a ≠ qc c hc := by
    intro c hc a h
    exact W.q_not_mem_range hc ⟨a, congrArg Subtype.val h⟩
  obtain ⟨Pth, hdisj⟩ := hsk
  let newP : Fin (Γ.V ∩ C).ncard → PathFromTo HQ.toHypergraph.skeleton
      (HQ.V ∩ (Subtype.val : discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z) → cap.Z) ⁻¹' discBd E) (HQ.V ∩ liftEdge cap.j _ F) :=
    fun i =>
      { first := qc _ (hCP (Pth i).first_mem)
        last := φ (Pth i).last
        walk := SimpleGraph.Walk.cons (hsp _ (hCP (Pth i).first_mem)) ((Pth i).walk.map hom)
        isPath := by
          refine SimpleGraph.Walk.IsPath.cons
            ((SimpleGraph.Walk.isPath_map_iff_of_injective (f := hom) hφinj).mpr (Pth i).isPath) ?_
          rw [SimpleGraph.Walk.support_map, List.mem_map]
          rintro ⟨a, -, ha⟩
          exact hqr _ (hCP (Pth i).first_mem) a ha
        first_mem := by
          refine ⟨?_, hqE _ (Pth i).first_mem⟩
          rw [hVQ, hHV]; exact Or.inr ⟨_, hCP (Pth i).first_mem, rfl⟩
        last_mem := by
          refine ⟨?_, ⟨_, (Pth i).last_mem.2, rfl⟩⟩
          rw [hVQ, hHV]; exact Or.inl ⟨_, (Pth i).last_mem.1, rfl⟩ }
  have hdisj' : Pairwise fun i k => Disjoint {x | x ∈ (newP i).walk.support}
      {x | x ∈ (newP k).walk.support} := by
    intro i k hik
    refine disjoint_left.mpr ?_
    intro z hz₁ hz₂
    simp only [newP, mem_ofPred_eq, SimpleGraph.Walk.support_cons, List.mem_cons,
      SimpleGraph.Walk.support_map, List.mem_map] at hz₁ hz₂
    rcases hz₁ with rfl | ⟨a, ha, rfl⟩ <;> rcases hz₂ with h | ⟨b, hb, h⟩
    · -- two spoke ends
      have hci := hCP (Pth i).first_mem
      have hck := hCP (Pth k).first_mem
      have hq : W.q (cap.j (Pth i).first) = W.q (cap.j (Pth k).first) := congrArg Subtype.val h
      have hc : (Pth i).first = (Pth k).first := by
        by_contra hne
        have hk' : W.q (cap.j (Pth i).first) ∈ W.ℓ (cap.j (Pth k).first) := by
          rw [hq]; exact W.q_mem_ℓ hck
        exact disjoint_left.mp (W.disjoint _ hci _ hck hne) (W.q_mem_ℓ hci) hk'
      have hk'' : (Pth i).first ∈ (Pth k).walk.support := by
        rw [hc]; exact (Pth k).walk.start_mem_support
      exact disjoint_left.mp (hdisj hik) (Pth i).walk.start_mem_support hk''
    · exact hqr _ (hCP (Pth i).first_mem) b h
    · exact hqr _ (hCP (Pth k).first_mem) a h
    · have hab : a = b := hφinj (by first | exact h | exact h.symm)
      subst hab
      exact disjoint_left.mp (hdisj hik) ha hb
  have hpaths := le_maxDisjointPaths_of_skeleton_paths HQ
    (Thomas.hasDisjointPaths_symm ⟨newP, hdisj'⟩)
  refine le_trans ?_ hpaths
  have h1 : (HQ.V ∩ (Subtype.val : discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z) → cap.Z) ⁻¹' discBd E).ncard ≤
      (H.V ∩ discBd E).ncard :=
    ncard_le_ncard_of_injOn Subtype.val (fun x hx => ⟨(hVQ x).mp hx.1, hx.2⟩)
      Subtype.val_injective.injOn (H.finite_V.inter_of_left _)
  refine h1.trans ((ncard_le_ncard hVE ((Γ.finite_V.inter_of_left C).image _)).trans ?_)
  exact ncard_image_le (Γ.finite_V.inter_of_left C)

end GraphMinor.GM08
