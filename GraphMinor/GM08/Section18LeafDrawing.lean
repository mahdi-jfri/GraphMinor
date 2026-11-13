module

public import GraphMinor.GM08.Section18LeafCollar
public import GraphMinor.GM08.Section17RootLeaves
public import GraphMinor.GM07.Section9MoveOff
import GraphMinor.GM07.CylinderWheel
import GraphMinor.GM07.Matched
import GraphMinor.GM08.Section15ImageIso
import GraphMinor.GM08.Section9Transport
import GraphMinor.GM08.Section17CollarGraph
import GraphMinor.GM08.Section17CollarDrawing
import GraphMinor.GM08.Section18LeafSchism

/-!
# Drawing every root as a leaf

Let `X` be drawn in a surface `S`. Push the drawing into the part of `S` above
the spokes of a boundary collar, by the map `e`. At each root `x` add the spoke
from `e x` down to `x`. This draws the graft `rootLeafGraft X`: every old vertex
is now inside `S`, and the new leaves are the old root points. So the new
drawing has the same vertices on each cuff.

The collapse `g` of the collar onto the tops of the spokes satisfies the
conditions of `exists_normal_schism_of_retraction` for the new drawing. So
for the new drawing every alpha candidate gives a normal schism with no more
vertices. This is the step that replaces the false remark of VII, page 242,
in the corrected proof of VIII (18.1) (see the correction on page 242 in
`corrections/GM07.md`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology Function Graph GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM11

universe u v w

variable {S : Type u} [TopologicalSpace S]

/-- The push of a boundary collar is a closed embedding. -/
theorem BoundaryCollar.isClosedEmbedding_e [T2Space S] [CompactSpace S] {B : Set S}
    (K : BoundaryCollar S B) : IsClosedEmbedding K.e :=
  K.cont_e.isClosedEmbedding K.inj_e

/-- The push misses the boundary. -/
theorem BoundaryCollar.e_not_mem_bd (K : BoundaryCollar S (bd S)) (y : S) :
    K.e y ∉ bd S := by
  intro h
  have hy := K.e_bd y h
  have hyy : K.e y = y := (K.fix y hy).1
  exact hy (K.B_subset (hyy ▸ h))

/-- The collapse misses the boundary. -/
theorem BoundaryCollar.g_not_mem_bd (K : BoundaryCollar S (bd S)) (y : S) :
    K.g y ∉ bd S := by
  rcases K.cover y with ⟨z, rfl⟩ | ⟨x, -, -, hg⟩
  · rw [K.g_e]; exact K.e_not_mem_bd z
  · rw [hg]; exact K.e_not_mem_bd x

/-- The collapse sends a boundary point to the top of its spoke. -/
theorem BoundaryCollar.g_of_mem_bd (K : BoundaryCollar S (bd S)) {x : S} (hx : x ∈ bd S) :
    K.g x = K.e x := by
  rcases K.cover x with ⟨z, rfl⟩ | ⟨x₀, hx₀, hxs, hg⟩
  · exact absurd hx (K.e_not_mem_bd z)
  · have h : x ∈ K.sp x₀ ∩ bd S := ⟨hxs, hx⟩
    rw [K.sp_bd x₀ hx₀] at h
    rw [hg, show x = x₀ from h]

theorem BoundaryCollar.start_mem_sp (K : BoundaryCollar S (bd S)) {x : S} (hx : x ∈ bd S) :
    K.e x ∈ K.sp x := by
  obtain ⟨φ, h0, -⟩ := K.line x hx
  have h := (φ 0).2
  rwa [h0] at h

theorem BoundaryCollar.end_mem_sp (K : BoundaryCollar S (bd S)) {x : S} (hx : x ∈ bd S) :
    x ∈ K.sp x := by
  obtain ⟨φ, -, h1⟩ := K.line x hx
  have h := (φ 1).2
  rwa [h1] at h

/-- The image of a drawing under the push, with the spokes at the points of `P`. -/
theorem BoundaryCollar.exists_leaf_drawing [T2Space S] [CompactSpace S] [Nonempty S]
    (K : BoundaryCollar S (bd S)) (Γ : Drawing S) {P : Set S} (hPV : P ⊆ Γ.V)
    (hPbd : P ⊆ bd S) :
    ∃ H : Drawing S,
      H.U = K.e '' Γ.U ∪ ⋃ x ∈ P, K.sp x ∧
      H.V = K.e '' Γ.V ∪ P ∧
      H.E = image K.e '' Γ.E ∪ (fun x => K.sp x \ {K.e x, x}) '' P := by
  classical
  have hj := K.isClosedEmbedding_e
  have hPfin : P.Finite := Γ.finite_V.subset hPV
  let ℓ : S → Set S := fun z => K.sp (invFun K.e z)
  let q : S → S := fun z => invFun K.e z
  have hℓ : ∀ x, ℓ (K.e x) = K.sp x := fun x => by simp [ℓ, leftInverse_invFun K.inj_e x]
  have hq : ∀ x, q (K.e x) = x := fun x => leftInverse_invFun K.inj_e x
  let Kd := embedDrawing hj Γ
  have hBK : Disjoint P Kd.U := by
    refine disjoint_left.mpr ?_
    rintro x hx ⟨y, -, rfl⟩
    exact K.e_not_mem_bd y (hPbd hx)
  let K₁ := addIsolated Kd P hPfin hBK
  have hK₁U : K₁.U = K.e '' Γ.U ∪ P := rfl
  have hK₁V : K₁.V = K.e '' Γ.V ∪ P := rfl
  have hK₁E : K₁.E = image K.e '' Γ.E := by
    rw [addIsolated_E]; exact embedDrawing_E hj Γ
  let s : Finset S := (hPfin.image K.e).toFinset
  have hs : ∀ z, z ∈ s ↔ ∃ x ∈ P, K.e x = z := fun z => by
    simp [s, Set.Finite.mem_toFinset]
  obtain ⟨H, hHU, hHV, hHE⟩ := exists_add_lines K₁ s ℓ id q
    (by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := (hs z).mp hz
      rw [hℓ, hq]
      refine ⟨K.line x (hPbd hx), K.ne x (hPbd hx), Or.inl ⟨x, hPV hx, rfl⟩, Or.inr hx, ?_⟩
      rintro y ⟨hyℓ, hyU⟩
      rw [hK₁U] at hyU
      rcases hyU with ⟨y', -, rfl⟩ | hy
      · have h : K.e y' ∈ K.sp x ∩ range K.e := ⟨hyℓ, y', rfl⟩
        rw [K.sp_range x (hPbd hx)] at h
        exact Or.inl h
      · have h : y ∈ K.sp x ∩ bd S := ⟨hyℓ, hPbd hy⟩
        rw [K.sp_bd x (hPbd hx)] at h
        exact Or.inr h)
    (by
      intro z hz z' hz' hzz'
      obtain ⟨x, hx, rfl⟩ := (hs z).mp hz
      obtain ⟨y, hy, rfl⟩ := (hs z').mp hz'
      rw [hℓ, hℓ]
      exact K.disjoint x (hPbd hx) y (hPbd hy) (fun h => hzz' (h ▸ rfl)))
  have hU' : (⋃ z ∈ s, ℓ z) = ⋃ x ∈ P, K.sp x := by
    ext y
    simp only [mem_iUnion, hs, exists_prop]
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, hy⟩; exact ⟨x, hx, hℓ x ▸ hy⟩
    · rintro ⟨x, hx, hy⟩; exact ⟨_, ⟨x, hx, rfl⟩, (hℓ x).symm ▸ hy⟩
  refine ⟨H, ?_, hHV.trans hK₁V, ?_⟩
  · rw [hHU, hK₁U, hU']
    ext y
    simp only [mem_union, mem_iUnion, exists_prop]
    constructor
    · rintro ((h | h) | h)
      · exact .inl h
      · exact .inr ⟨y, h, K.end_mem_sp (hPbd h)⟩
      · exact .inr h
    · rintro (h | h)
      · exact .inl (.inl h)
      · exact .inr h
  · rw [hHE, hK₁E]
    congr 1
    ext f
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hs z).mp (Finset.mem_coe.mp hz)
      refine ⟨x, hx, ?_⟩
      simp only [hℓ, hq, id]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨_, Finset.mem_coe.mpr ((hs _).mpr ⟨x, hx, rfl⟩), ?_⟩
      simp only [hℓ, hq, id]

/-- **Drawing every root as a leaf.** The graft `rootLeafGraft X` is drawn in
`S` by the push of the drawing of `X` together with the spokes at its roots. -/
theorem BoundaryCollar.exists_leaf_graftDrawing [T2Space S] [CompactSpace S] [Nonempty S]
    (K : BoundaryCollar S (bd S)) {α : Type v} {β : Type w} {X : Graft α β}
    (gd : GraftDrawing X.G X.T S) :
    ∃ gd' : GraftDrawing (rootLeafGraft X).G (rootLeafGraft X).T S,
      gd'.drawing.U = K.e '' gd.drawing.U ∪ ⋃ x ∈ gd.drawing.V ∩ bd S, K.sp x ∧
      gd'.drawing.V = K.e '' gd.drawing.V ∪ (gd.drawing.V ∩ bd S) := by
  classical
  have hj := K.isClosedEmbedding_e
  set Γ := gd.drawing with hΓ
  set P := Γ.V ∩ bd S with hP
  have hPV : P ⊆ Γ.V := inter_subset_left
  have hPbd : P ⊆ bd S := inter_subset_right
  obtain ⟨H, hHU, hHV, hHE⟩ := K.exists_leaf_drawing Γ hPV hPbd
  let ℓ : S → Set S := fun z => K.sp (invFun K.e z)
  let q : S → S := fun z => invFun K.e z
  have hℓ : ∀ x, ℓ (K.e x) = K.sp x := fun x => by simp [ℓ, leftInverse_invFun K.inj_e x]
  have hq : ∀ x, q (K.e x) = x := fun x => leftInverse_invFun K.inj_e x
  let Kd := embedDrawing hj Γ
  have a₀ : IsGraphBij X.G Γ.toGraph gd.iso.fv gd.iso.fe := gd.iso.isGraphBij
  have a₁ : IsGraphBij Γ.toGraph Kd.toGraph K.e (image K.e) :=
    isGraphBij_of_matched_embedding hj.isEmbedding (embedDrawing_isMatched hj Γ)
  have a₂ := a₀.trans a₁
  have hfvT : gd.iso.fv '' X.T = P := by
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
  have hR : (K.e ∘ gd.iso.fv) '' X.T = K.e '' P := by rw [image_comp, hfvT]
  have hqR : q '' (K.e '' P) = P := by
    rw [image_image]; simp only [hq, image_id']
  have hb := isGraphBij_rootLeafGraph_of_spokes a₂ q ℓ
    (by rw [hR]; rintro _ ⟨x, hx, rfl⟩; rw [hℓ, hq]; exact K.line x (hPbd hx))
    (by rw [hR]; rintro _ ⟨x, hx, rfl⟩; rw [hq]; exact K.ne x (hPbd hx))
    (by
      rw [hR]; rintro _ ⟨x, hx, rfl⟩
      rintro z ⟨hzℓ, ⟨y, -, rfl⟩⟩
      rw [hℓ] at hzℓ
      have h : K.e y ∈ K.sp x ∩ range K.e := ⟨hzℓ, y, rfl⟩
      rwa [K.sp_range x (hPbd hx)] at h)
    (by
      rw [hR]; rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      rw [hℓ, hℓ]
      exact K.disjoint x (hPbd hx) y (hPbd hy) (fun h => hxy (h ▸ rfl)))
    (by rw [hR, hHV, hqR]; rfl)
    (by
      rw [hR, hHE, embedDrawing_E hj Γ]
      congr 1
      rw [image_image]
      simp only [hℓ, hq])
  let a : Iso (rootLeafGraft X).G H.toGraph := hb.toIso
  have hcoord : ∀ w : V((rootLeafGraft X).G), (a.vertexEquiv w).1 =
      Sum.elim (K.e ∘ gd.iso.fv) (q ∘ (K.e ∘ gd.iso.fv)) w.1 := fun w => rfl
  have hprop : H.IsProper := by
    rintro z ⟨hzb, hzU⟩
    rw [hHU] at hzU
    rw [hHV]
    rcases hzU with ⟨y, -, rfl⟩ | hz
    · exact absurd hzb (K.e_not_mem_bd y)
    · obtain ⟨x, hx, hzs⟩ := mem_iUnion₂.mp hz
      have h : z ∈ K.sp x ∩ bd S := ⟨hzs, hzb⟩
      rw [K.sp_bd x (hPbd hx)] at h
      have hzx : z = x := h
      exact .inr (hzx ▸ hx)
  have hbd : ∀ (v : α ⊕ α) (hv : v ∈ V((rootLeafGraft X).G)),
      (a.vertexEquiv ⟨v, hv⟩).1 ∈ bd S ↔ v ∈ (rootLeafGraft X).T := by
    intro v hv
    rw [hcoord ⟨v, hv⟩]
    rcases v with v | t
    · simp only [Sum.elim_inl, Function.comp_apply, inl_not_mem_rootLeafGraft_roots, iff_false]
      exact K.e_not_mem_bd _
    · simp only [Sum.elim_inr, Function.comp_apply, inr_mem_rootLeafGraft_roots, hq]
      have ht : t ∈ X.T := (inr_mem_rootLeafGraph_vertexSet X t).mp hv
      refine ⟨fun _ => ht, fun _ => hPbd ?_⟩
      exact hfvT ▸ mem_image_of_mem _ ht
  let gd' : GraftDrawing (rootLeafGraft X).G (rootLeafGraft X).T S :=
    { drawing := H
      iso := a
      isProper := hprop
      T_subset_V := (rootLeafGraft X).T_subset
      mem_bd_iff := hbd }
  exact ⟨gd', hHU, hHV⟩

end GraphMinor.GM08
