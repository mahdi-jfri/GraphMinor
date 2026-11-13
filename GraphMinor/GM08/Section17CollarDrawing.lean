module

public import GraphMinor.GM08.Section17CollarWheel
public import GraphMinor.GM08.Section17CollarGraph
public import GraphMinor.GM07.Section9MoveOff
public import GraphMinor.GM12.Section3SubspaceDrawing
public import GraphMinor.GM08.Section12Subspace
import GraphMinor.GM07.CylinderWheel
import GraphMinor.GM07.Matched
import GraphMinor.GM07.Section9DiscSphere
import GraphMinor.GM08.Section15ImageIso
import GraphMinor.GM08.Section9Transport
import GraphMinor.GM08.Section11Iso
import GraphMinor.GM08.Section17CollarOrder
import GraphMinor.GM12.Section3Punctured
import GraphMinor.GM12.Section3PuncturedBoundary
import GraphMinor.GM12.Section3BoundaryEquality

/-!
# Drawing a graft with a new leaf at each root in the larger cylinder

Let `X` be drawn in a cylinder `S`, with its roots at a set `P` of boundary
points. Cap `S` to a sphere, and take spokes from the points of `P` into the
caps (`CollarWheel`). The image of the drawing together with the spokes is a
drawing in the sphere. It meets the small discs `E₁, E₂` only at the ends of
the spokes, so it is a drawing in the cylinder `Q` left after removing the
interiors of `E₁` and `E₂`. In `Q` it draws the graft `rootLeafGraft X`: its
new leaves are the ends of the spokes, which lie on the boundary of `Q`, and all
old vertices are inside `Q`.
-/

public section

namespace GraphMinor.GM08

open Set Topology Graph GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM12

universe u v

variable {S : Type} [TopologicalSpace S]

/-- Adding isolated vertices does not change the edges. -/
theorem addIsolated_E {T : Type*} [TopologicalSpace T] [T1Space T] (Γ : Drawing T)
    (B : Set T) (hf : B.Finite) (hB : Disjoint B Γ.U) :
    (addIsolated Γ B hf hB).E = Γ.E := by
  change arcComponentsIn ((Γ.U ∪ B) \ (Γ.V ∪ B)) = arcComponentsIn (Γ.U \ Γ.V)
  congr 1
  ext x
  simp only [mem_sdiff, mem_union, not_or]
  constructor
  · rintro ⟨h1 | h1, h2, h3⟩
    · exact ⟨h1, h2⟩
    · exact absurd h1 h3
  · rintro ⟨h1, h2⟩
    exact ⟨.inl h1, h2, fun h3 => disjoint_left.mp hB h3 h1⟩

/-- The image of a drawing of `S` together with the spokes of a collar wheel at
its boundary vertices is a drawing in the cap sphere. -/
theorem CollarWheel.exists_sphere_drawing [Nonempty S] {cap : CylinderSphereCap S} {P : Set S}
    (W : CollarWheel cap P) (Γ : Drawing S) (hP : P ⊆ Γ.V) :
    have : T2Space cap.Z := cap.t2Space_Z
    ∃ H : Drawing cap.Z,
      H.U = cap.j '' Γ.U ∪ ⋃ x ∈ P, W.ℓ (cap.j x) ∧
      H.V = cap.j '' Γ.V ∪ (fun x => W.q (cap.j x)) '' P ∧
      H.E = image cap.j '' Γ.E ∪ (fun x => W.ℓ (cap.j x) \ {cap.j x, W.q (cap.j x)}) '' P := by
  intro _
  classical
  have : T2Space S := cap.isClosedEmbedding.isEmbedding.t2Space
  have hj := cap.isClosedEmbedding
  have hPfin : P.Finite := Γ.finite_V.subset hP
  -- the ends of the spokes are off the image of `S`
  have hqE : ∀ x ∈ P, W.q (cap.j x) ∈ W.E₁ ∪ W.E₂ := fun x hx =>
    (W.inter_E x hx ▸ rfl : W.q (cap.j x) ∈ W.ℓ (cap.j x) ∩ (W.E₁ ∪ W.E₂)).2
  have hEr : Disjoint (W.E₁ ∪ W.E₂) (range cap.j) :=
    disjoint_union_left.mpr ⟨(cap.disjoint_range_discInt_D₁.mono_right W.E₁_subset).symm,
      (cap.disjoint_range_discInt_D₂.mono_right W.E₂_subset).symm⟩
  have hqr : ∀ x ∈ P, W.q (cap.j x) ∉ range cap.j := fun x hx h =>
    disjoint_left.mp hEr (hqE x hx) h
  have hend : ∀ x ∈ P, W.q (cap.j x) ∈ W.ℓ (cap.j x) := by
    intro x hx
    have h : W.q (cap.j x) ∈ ({W.q (cap.j x)} : Set cap.Z) := rfl
    rw [← W.inter_E x hx] at h
    exact h.1
  let K := embedDrawing hj Γ
  let B : Set cap.Z := (fun x => W.q (cap.j x)) '' P
  have hBf : B.Finite := hPfin.image _
  have hBK : Disjoint B K.U := by
    refine disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, -, hy⟩
    exact hqr x hx ⟨y, hy⟩
  let K₁ := addIsolated K B hBf hBK
  have hK₁U : K₁.U = cap.j '' Γ.U ∪ B := rfl
  have hK₁V : K₁.V = cap.j '' Γ.V ∪ B := rfl
  have hK₁E : K₁.E = image cap.j '' Γ.E := by
    rw [addIsolated_E]; exact embedDrawing_E hj Γ
  let s : Finset cap.Z := (hPfin.image cap.j).toFinset
  have hs : ∀ z, z ∈ s ↔ ∃ x ∈ P, cap.j x = z := fun z => by
    simp [s, Set.Finite.mem_toFinset]
  obtain ⟨H, hHU, hHV, hHE⟩ := exists_add_lines K₁ s W.ℓ id W.q
    (by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := (hs z).mp hz
      refine ⟨W.line x hx, W.ne x hx, Or.inl ⟨x, hP hx, rfl⟩, Or.inr ⟨x, hx, rfl⟩, ?_⟩
      rintro w ⟨hwℓ, hwU⟩
      rw [hK₁U] at hwU
      rcases hwU with ⟨y, -, rfl⟩ | ⟨y, hy, rfl⟩
      · have h : cap.j y ∈ W.ℓ (cap.j x) ∩ range cap.j := ⟨hwℓ, y, rfl⟩
        rw [W.inter_range x hx] at h
        exact Or.inl h
      · by_cases hxy : x = y
        · exact Or.inr (hxy ▸ rfl)
        · exact absurd hwℓ (disjoint_right.mp (W.disjoint x hx y hy hxy) (hend y hy)))
    (by
      intro z hz z' hz' hzz'
      obtain ⟨x, hx, rfl⟩ := (hs z).mp hz
      obtain ⟨y, hy, rfl⟩ := (hs z').mp hz'
      exact W.disjoint x hx y hy (fun h => hzz' (h ▸ rfl)))
  have hU' : (⋃ z ∈ s, W.ℓ z) = ⋃ x ∈ P, W.ℓ (cap.j x) := by
    ext w
    simp only [mem_iUnion, hs, exists_prop]
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, hw⟩; exact ⟨x, hx, hw⟩
    · rintro ⟨x, hx, hw⟩; exact ⟨_, ⟨x, hx, rfl⟩, hw⟩
  refine ⟨H, ?_, hHV.trans hK₁V, ?_⟩
  · rw [hHU, hK₁U, hU']
    ext w
    simp only [mem_union, mem_iUnion, exists_prop]
    constructor
    · rintro ((h | ⟨x, hx, rfl⟩) | h)
      · exact .inl h
      · exact .inr ⟨x, hx, hend x hx⟩
      · exact .inr h
    · rintro (h | h)
      · exact .inl (.inl h)
      · exact .inr h
  · rw [hHE, hK₁E]
    congr 1
    ext e
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hs z).mp (Finset.mem_coe.mp hz)
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, Finset.mem_coe.mpr ((hs _).mpr ⟨x, hx, rfl⟩), rfl⟩

/-- **The graft with new leaves in the larger cylinder.** Let `X` be drawn in the
cylinder `S` with its roots at the points `P`. Then the image of this drawing
with the spokes at `P`, read in the cylinder `Q` left after removing the
interiors of the small discs, is a drawing of `rootLeafGraft X` in `Q`. -/
theorem CollarWheel.exists_collar_graftDrawing [Nonempty S] [CompactSpace S]
    {cap : CylinderSphereCap S} {P : Set S} (W : CollarWheel cap P)
    {α : Type u} {β : Type v} {X : Graft α β} (gd : GraftDrawing X.G X.T S)
    (hP : gd.drawing.V ∩ bd S = P) :
    have : T2Space cap.Z := cap.t2Space_Z
    let Q := discComplement (![W.E₁, W.E₂] : Fin 2 → Set cap.Z)
    ∃ (H : Drawing cap.Z) (hHQ : H.U ⊆ Q)
      (gd' : GraftDrawing (rootLeafGraft X).G (rootLeafGraft X).T Q),
      gd'.drawing = drawingInSubspace H Q hHQ ∧
      H.U = cap.j '' gd.drawing.U ∪ ⋃ x ∈ P, W.ℓ (cap.j x) ∧
      H.V = cap.j '' gd.drawing.V ∪ (fun x => W.q (cap.j x)) '' P ∧
      H.E = image cap.j '' gd.drawing.E ∪
        (fun x => W.ℓ (cap.j x) \ {cap.j x, W.q (cap.j x)}) '' P := by
  intro _ Q
  classical
  have : T2Space S := cap.isClosedEmbedding.isEmbedding.t2Space
  have hj := cap.isClosedEmbedding
  set Γ := gd.drawing with hΓ
  have hPV : P ⊆ Γ.V := hP ▸ inter_subset_left
  have hPbd : P ⊆ bd S := hP ▸ inter_subset_right
  obtain ⟨H, hHU, hHV, hHE⟩ := W.exists_sphere_drawing Γ hPV
  -- facts about the spokes
  have hE₁₂ : Disjoint W.E₁ W.E₂ :=
    cap.disjoint_D.mono (W.E₁_subset.trans (discInt_subset _))
      (W.E₂_subset.trans (discInt_subset _))
  have hE₁r : Disjoint W.E₁ (range cap.j) :=
    (cap.disjoint_range_discInt_D₁.mono_right W.E₁_subset).symm
  have hE₂r : Disjoint W.E₂ (range cap.j) :=
    (cap.disjoint_range_discInt_D₂.mono_right W.E₂_subset).symm
  have hqbd : ∀ x ∈ P, W.q (cap.j x) ∈ discBd W.E₁ ∪ discBd W.E₂ := by
    intro x hx
    rcases (cap.bd_eq ▸ hPbd hx : x ∈ cap.C₁ ∪ cap.C₂) with h | h
    · exact .inl (W.q_mem₁ x hx h)
    · exact .inr (W.q_mem₂ x hx h)
  have hend : ∀ x ∈ P, W.q (cap.j x) ∈ W.ℓ (cap.j x) := by
    intro x hx
    have h : W.q (cap.j x) ∈ ({W.q (cap.j x)} : Set cap.Z) := rfl
    rw [← W.inter_E x hx] at h
    exact h.1
  -- `H` meets each small disc exactly in the spoke ends on its boundary
  have havoid : ∀ E : Set cap.Z, (E = W.E₁ ∨ E = W.E₂) → H.U ∩ E = H.V ∩ discBd E := by
    intro E hE
    have hEr : Disjoint E (range cap.j) := by rcases hE with rfl | rfl <;> assumption
    have hq : ∀ x ∈ P, W.q (cap.j x) ∈ E → W.q (cap.j x) ∈ discBd E := by
      intro x hx hqE
      rcases hE with rfl | rfl <;> rcases hqbd x hx with h | h
      · exact h
      · exact absurd (discBd_subset _ h) (disjoint_left.mp hE₁₂ hqE)
      · exact absurd hqE (disjoint_left.mp hE₁₂ (discBd_subset _ h))
      · exact h
    apply subset_antisymm
    · rintro z ⟨hzU, hzE⟩
      rw [hHU] at hzU
      rcases hzU with ⟨y, -, rfl⟩ | hz
      · exact absurd ⟨y, rfl⟩ (disjoint_left.mp hEr hzE)
      · obtain ⟨x, hx, hzℓ⟩ := mem_iUnion₂.mp hz
        have hzE' : z ∈ W.E₁ ∪ W.E₂ := by rcases hE with rfl | rfl <;> simp [hzE]
        have h : z ∈ W.ℓ (cap.j x) ∩ (W.E₁ ∪ W.E₂) := ⟨hzℓ, hzE'⟩
        rw [W.inter_E x hx] at h
        rw [h]
        exact ⟨hHV ▸ Or.inr ⟨x, hx, rfl⟩, hq x hx (h ▸ hzE)⟩
    · rintro z ⟨hzV, hzb⟩
      rw [hHV] at hzV
      rcases hzV with ⟨y, -, rfl⟩ | ⟨x, hx, rfl⟩
      · exact absurd ⟨y, rfl⟩ (disjoint_left.mp hEr (discBd_subset _ hzb))
      · exact ⟨hHU ▸ Or.inr (mem_iUnion₂.mpr ⟨x, hx, hend x hx⟩), discBd_subset _ hzb⟩
  let D : Fin 2 → Set cap.Z := ![W.E₁, W.E₂]
  have hD : ∀ i, IsClosedDisc (D i) := by
    intro i; fin_cases i
    · exact W.isClosedDisc_E₁
    · exact W.isClosedDisc_E₂
  have hdis : Pairwise (fun i j => Disjoint (D i) (D j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hE₁₂
    · exact hE₁₂.symm
    · exact (hij rfl).elim
  have havoid' : ∀ i, H.U ∩ D i = H.V ∩ discBd (D i) := by
    intro i; fin_cases i
    · exact havoid _ (.inl rfl)
    · exact havoid _ (.inr rfl)
  have hHQ : H.U ⊆ Q := drawing_support_subset_discComplement cap.isClosedSurface H D hD hdis
    havoid'
  have hprop := drawingInDiscComplement_isProper cap.isClosedSurface H D hD hdis havoid'
  obtain ⟨-, -, -, hbdQ⟩ := cylinder_complement_two_discs cap.isClosedSurface cap.isSphere
    W.isClosedDisc_E₁ W.isClosedDisc_E₂ hE₁₂
  -- the graph bijection
  let K := embedDrawing hj Γ
  have a₀ : IsGraphBij X.G Γ.toGraph gd.iso.fv gd.iso.fe := gd.iso.isGraphBij
  have a₁ : IsGraphBij Γ.toGraph K.toGraph cap.j (image cap.j) :=
    isGraphBij_of_matched_embedding hj.isEmbedding (embedDrawing_isMatched hj Γ)
  have a₂ := a₀.trans a₁
  have hfvT : gd.iso.fv '' X.T = P := by
    rw [← hP]
    apply subset_antisymm
    · rintro _ ⟨t, ht, rfl⟩
      refine ⟨Iso.fv_mem (a := gd.iso) (X.T_subset ht), ?_⟩
      rw [Iso.fv_of_mem (X.T_subset ht)]
      exact (gd.mem_bd_iff t (X.T_subset ht)).mpr ht
    · rintro p ⟨hpV, hpb⟩
      obtain ⟨v, hv, rfl⟩ := Iso.exists_fv (a := gd.iso) hpV
      refine ⟨v, ?_, rfl⟩
      rw [Iso.fv_of_mem hv] at hpb
      exact (gd.mem_bd_iff v hv).mp hpb
  have hR : (cap.j ∘ gd.iso.fv) '' X.T = cap.j '' P := by rw [image_comp, hfvT]
  have hb := isGraphBij_rootLeafGraph_of_spokes a₂ W.q W.ℓ
    (by rw [hR]; rintro _ ⟨x, hx, rfl⟩; exact W.line x hx)
    (by rw [hR]; rintro _ ⟨x, hx, rfl⟩; exact W.ne x hx)
    (by
      rw [hR]; rintro _ ⟨x, hx, rfl⟩
      rintro z ⟨hzℓ, ⟨y, -, rfl⟩⟩
      have h : cap.j y ∈ W.ℓ (cap.j x) ∩ range cap.j := ⟨hzℓ, y, rfl⟩
      rwa [W.inter_range x hx] at h)
    (by
      rw [hR]; rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      exact W.disjoint x hx y hy (fun h => hxy (h ▸ rfl)))
    (by rw [hR, hHV, image_image]; rfl)
    (by rw [hR, hHE, embedDrawing_E hj Γ, image_image])
  let a := hb.toIso
  let H' := drawingInSubspace H Q hHQ
  let i := (isGraphBij_drawingInSubspace H isClosed_closure hHQ).toIso
  have hinv : ∀ (e : E(H.toGraph)) (x y : V(H.toGraph)),
      H.toGraph.IsLink e.1 x.1 y.1 ↔
        H'.toGraph.IsLink (i.edgeEquiv.symm e).1
          (i.vertexEquiv.symm x).1 (i.vertexEquiv.symm y).1 := by
    intro e x y
    have h := i.isLink_iff (i.edgeEquiv.symm e) (i.vertexEquiv.symm x) (i.vertexEquiv.symm y)
    simp only [Equiv.apply_symm_apply] at h
    exact h.symm
  let b : GraphMinor.Iso (rootLeafGraft X).G H'.toGraph := {
    vertexEquiv := a.vertexEquiv.trans i.vertexEquiv.symm
    edgeEquiv := a.edgeEquiv.trans i.edgeEquiv.symm
    isLink_iff := fun e x y => (a.isLink_iff e x y).trans (hinv _ _ _) }
  have hcoord : ∀ w : V((rootLeafGraft X).G), ((b.vertexEquiv w).1).1 =
      Sum.elim (cap.j ∘ gd.iso.fv) (W.q ∘ (cap.j ∘ gd.iso.fv)) w.1 := by
    intro w
    change ((i.vertexEquiv.symm (a.vertexEquiv w)).1).1 = _
    have h : (i.vertexEquiv (i.vertexEquiv.symm (a.vertexEquiv w))).1 = (a.vertexEquiv w).1 := by
      rw [Equiv.apply_symm_apply]
    exact h
  have hbd : ∀ (v : α ⊕ α) (hv : v ∈ V((rootLeafGraft X).G)),
      (b.vertexEquiv ⟨v, hv⟩).1 ∈ bd Q ↔ v ∈ (rootLeafGraft X).T := by
    intro v hv
    rw [hbdQ, mem_preimage, hcoord ⟨v, hv⟩]
    rcases v with v | t
    · simp only [Sum.elim_inl, Function.comp_apply, inl_not_mem_rootLeafGraft_roots, iff_false]
      rintro (h | h)
      · exact disjoint_left.mp hE₁r (discBd_subset _ h) ⟨_, rfl⟩
      · exact disjoint_left.mp hE₂r (discBd_subset _ h) ⟨_, rfl⟩
    · simp only [Sum.elim_inr, Function.comp_apply, inr_mem_rootLeafGraft_roots]
      have ht : t ∈ X.T := (inr_mem_rootLeafGraph_vertexSet X t).mp hv
      refine ⟨fun _ => ht, fun _ => hqbd _ ?_⟩
      exact hfvT ▸ mem_image_of_mem _ ht
  let gd' : GraftDrawing (rootLeafGraft X).G (rootLeafGraft X).T Q :=
    { drawing := H'
      iso := b
      isProper := hprop
      T_subset_V := (rootLeafGraft X).T_subset
      mem_bd_iff := hbd }
  exact ⟨H, hHQ, gd', rfl, hHU, hHV, hHE⟩

end GraphMinor.GM08
