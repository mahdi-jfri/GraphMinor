module

public import GraphMinor.GM08.Defs6to18
public import GraphMinor.GM04.Painting
public import GraphMinor.GM08.Section6
import GraphMinor.GM08.Section7Defs
import GraphMinor.GM04.Decomposition.TreeWidth
import GraphMinor.Thomas.RootedTree
import GraphMinor.GM11.PaintingCells
import GraphMinor.GM11.DrawingOps
import GraphMinor.GM14.DiscSlope

/-!
# Paintings in a disc, carried into the sphere

Graph Minors VIII proves (10.1) by citing Graph Minors IV, (9.2), which is stated for paintings in
a closed surface. This file prepares that step. A disc `S` embeds in the sphere by the chart of
`exists_sphereDiscChart`. We carry a painting of VIII in `S`, with its orderings and labels, to a
labelled painting of IV in the sphere, and we bound the tree-width of the result.

* The cells of a painting of VIII are its arc-wise connected pieces (`cells_eq_arcComponentsIn`),
  because a closed disc minus some of its boundary points is arc-wise connected. The points that a
  cell misses from its closure are nodes (`closure_inter_N`), and so is every point of `U` on the
  boundary of `S` (`inter_bd_subset_N`).
* `QPortrait.toLabelled` is the labelled painting in the sphere.
* `treeWidthLE_toLabelled`: if the portrait has tree-width at most `w`, the labelled painting has
  tree-width at most `w + k` in the sense of IV, where `k` is the index. We add the `k` boundary
  nodes to every bag, since IV asks that the root bag hold all of them. This is the remark after
  (10.1) on page 271.
-/

public section

namespace GraphMinor
namespace GM08

open Set Topology Surface

universe u w

variable {S : Type u} [TopologicalSpace S]

namespace PaintingInDisc

variable (P : PaintingInDisc S)

/-- A point that a cell misses from its closure is a node. A cell is a connected component of
`U - N`, so it holds every point of its closure that lies in `U - N`, and its closure lies in the
closed set `U`. -/
theorem closure_sdiff_subset_N {e : Set S} (he : e ∈ P.cells) : closure e \ e ⊆ P.N := by
  obtain ⟨x, hx, rfl⟩ := he
  rintro y ⟨hy, hye⟩
  by_contra hyN
  have hyU : y ∈ P.U :=
    closure_minimal ((connectedComponentIn_subset _ _).trans sdiff_subset) P.isClosed_U hy
  have hpre : IsPreconnected (insert y (connectedComponentIn (P.U \ P.N) x)) :=
    isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
      (insert_subset hy subset_closure)
  have hsub := hpre.subset_connectedComponentIn
    (mem_insert_of_mem _ (mem_connectedComponentIn hx))
    (insert_subset (show y ∈ P.U \ P.N from ⟨hyU, hyN⟩) (connectedComponentIn_subset _ _))
  exact hye (hsub (mem_insert y _))

/-- For a cell `e`, the nodes in the closure of `e` are exactly the points of the closure that are
not in `e`. -/
theorem closure_inter_N {e : Set S} (he : e ∈ P.cells) : closure e ∩ P.N = closure e \ e := by
  apply Subset.antisymm
  · rintro x ⟨hx, hxN⟩
    refine ⟨hx, fun hxe => ?_⟩
    obtain ⟨y, hy, rfl⟩ := he
    exact (connectedComponentIn_subset _ _ hxe).2 hxN
  · exact fun x hx => ⟨hx.1, P.closure_sdiff_subset_N he hx⟩

/-- Each cell is arc-wise connected: it is a closed disc minus some points of the boundary of the
disc, by condition (ii) of a painting. -/
theorem isPathConnected_cell {e : Set S} (he : e ∈ P.cells) : IsPathConnected e := by
  have h := GM11.isPathConnected_disc_sdiff (P.cell_disc e he).1
    (A := closure e \ e) (inter_subset_left.trans (P.cell_disc e he).2)
  rwa [sdiff_sdiff_cancel_left subset_closure] at h

/-- The cells of a painting (components of `U - N`) are the arc-wise connected components of
`U - N`, because each cell is arc-wise connected. -/
theorem cells_eq_arcComponentsIn : P.cells = arcComponentsIn (P.U \ P.N) := by
  ext C
  constructor
  · intro hC
    have hpc := P.isPathConnected_cell hC
    obtain ⟨x, hx, rfl⟩ := hC
    refine ⟨⟨x, mem_connectedComponentIn hx⟩, connectedComponentIn_subset _ _, hpc, ?_⟩
    intro D hD hDpc hCD
    exact (hDpc.isConnected.isPreconnected.subset_connectedComponentIn
      (hCD (mem_connectedComponentIn hx)) hD).antisymm hCD
  · rintro ⟨⟨x, hxC⟩, hsub, hpc, hmax⟩
    have hcell : connectedComponentIn (P.U \ P.N) x ∈ P.cells := ⟨x, hsub hxC, rfl⟩
    have hCe : C ⊆ connectedComponentIn (P.U \ P.N) x :=
      hpc.isConnected.isPreconnected.subset_connectedComponentIn hxC hsub
    rw [← hmax _ (connectedComponentIn_subset _ _) (P.isPathConnected_cell hcell) hCe]
    exact hcell

/-- Every point of `U` on the boundary of the disc is a node, by condition (iii) of a painting. -/
theorem inter_bd_subset_N : P.U ∩ bd S ⊆ P.N := by
  rintro x ⟨hxU, hxb⟩
  by_contra hxN
  have hcell : connectedComponentIn (P.U \ P.N) x ∈ P.cells := ⟨x, ⟨hxU, hxN⟩, rfl⟩
  exact disjoint_left.mp (P.cell_disjoint_bd _ hcell) (mem_connectedComponentIn ⟨hxU, hxN⟩) hxb

end PaintingInDisc

/-! ## Carrying a painting into the sphere -/

section Push

variable {f : S → OnePoint EuclideanPlane} {f' : OnePoint EuclideanPlane → S}

theorem SphereDiscChart.injective_of_univ (sc : SphereDiscChart (univ : Set S) f f') :
    Function.Injective f :=
  injOn_univ.mp sc.injOn_f

theorem SphereDiscChart.continuous_of_univ (sc : SphereDiscChart (univ : Set S) f f') :
    Continuous f :=
  continuousOn_univ.mp sc.fc

/-- The chart of a disc `S` in the sphere is a closed embedding. -/
theorem SphereDiscChart.isClosedEmbedding_of_univ (hS : IsClosedDisc (univ : Set S))
    (sc : SphereDiscChart (univ : Set S) f f') : IsClosedEmbedding f := by
  have : CompactSpace S := isCompact_univ_iff.mp hS.isCompact
  exact sc.continuous_of_univ.isClosedEmbedding sc.injective_of_univ

theorem isClosedSurface_sphere' : IsClosedSurface (OnePoint EuclideanPlane) :=
  (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1

/-- Images of arc-wise connected components under a map with a continuous left inverse. -/
private theorem arcComponentsIn_image_gen {S₁ : Type*} {S₂ : Type*}
    [TopologicalSpace S₁] [TopologicalSpace S₂] {F : Set S₁} {φ : S₁ → S₂} {ψ : S₂ → S₁}
    (hφ : ContinuousOn φ F) (hψ : ContinuousOn ψ (φ '' F)) (hψφ : ∀ x ∈ F, ψ (φ x) = x) :
    arcComponentsIn (φ '' F) = image φ '' arcComponentsIn F := by
  have hφψ : ∀ y ∈ φ '' F, φ (ψ y) = y := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hψφ x hx]
  have hconn : ∀ {A : Set S₁}, A ⊆ F → IsPathConnected A → IsPathConnected (φ '' A) :=
    fun hA h => h.image' (hφ.mono hA)
  have hconn' : ∀ {B : Set S₂}, B ⊆ φ '' F → IsPathConnected B → IsPathConnected (ψ '' B) :=
    fun hB h => h.image' (hψ.mono hB)
  have hψsub : ∀ {B : Set S₂}, B ⊆ φ '' F → ψ '' B ⊆ F := by
    rintro B hB _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hB hy
    rwa [hψφ x hx]
  have hφψim : ∀ {B : Set S₂}, B ⊆ φ '' F → φ '' (ψ '' B) = B := fun {B} hB => by
    rw [image_image]
    exact (image_congr fun y hy => hφψ y (hB hy)).trans (image_id' B)
  have hψφim : ∀ {A : Set S₁}, A ⊆ F → ψ '' (φ '' A) = A := fun {A} hA => by
    rw [image_image]
    exact (image_congr fun x hx => hψφ x (hA hx)).trans (image_id' A)
  ext C'
  constructor
  · rintro ⟨hne, hsub, hpc, hmax⟩
    refine ⟨ψ '' C', ⟨hne.image ψ, hψsub hsub, hconn' hsub hpc, ?_⟩, hφψim hsub⟩
    intro A hA hAc hCA
    have h₁ : C' ⊆ φ '' A := by
      have := image_mono (f := φ) hCA
      rwa [hφψim hsub] at this
    have h₂ := hmax _ (image_mono hA) (hconn hA hAc) h₁
    rw [← h₂, hψφim hA]
  · rintro ⟨C, ⟨hne, hsub, hpc, hmax⟩, rfl⟩
    refine ⟨hne.image φ, image_mono hsub, hconn hsub hpc, ?_⟩
    intro B hB hBc hCB
    have h₁ : C ⊆ ψ '' B := by
      have := image_mono (f := ψ) hCB
      rwa [hψφim hsub] at this
    have h₂ := hmax _ (hψsub hB) (hconn' hB hBc) h₁
    rw [← h₂, hφψim hB]

/-- The images of the cells of `P` are the arc-wise connected components of the image of `U - N`. -/
theorem PaintingInDisc.arcComponentsIn_image (P : PaintingInDisc S)
    (sc : SphereDiscChart (univ : Set S) f f') :
    arcComponentsIn (f '' P.U \ f '' P.N) = image f '' P.cells := by
  rw [← image_sdiff sc.injective_of_univ, P.cells_eq_arcComponentsIn]
  exact arcComponentsIn_image_gen (sc.fc.mono (subset_univ _))
    (sc.f'c.mono (image_mono (subset_univ _))) fun x _ => sc.f'f (mem_univ x)

/-- The image of a painting of VIII in a disc `S` under the chart, as a painting of IV in the
sphere. -/
@[expose] noncomputable def PaintingInDisc.toDiscPainting (P : PaintingInDisc S)
    (sc : SphereDiscChart (univ : Set S) f f') (hf : IsClosedEmbedding f) :
    GM04.DiscPainting (OnePoint EuclideanPlane) where
  U := f '' P.U
  V := f '' P.N
  V_subset_U := image_mono P.N_subset_U
  finite_V := P.finite_N.image f
  finite_edges := by
    rw [P.arcComponentsIn_image sc]
    exact P.finite_cells.image _
  edge_cond e he := by
    rw [P.arcComponentsIn_image sc] at he
    obtain ⟨c, hc, rfl⟩ := he
    rw [hf.closure_image_eq]
    obtain ⟨hd, hbd⟩ := (P.cell_disc c hc).1.image (sc.fc.mono (subset_univ _))
      (sc.f'c.mono (image_mono (subset_univ _))) fun x _ => sc.f'f (mem_univ x)
    refine ⟨hd, ?_⟩
    rw [GM14.IsClosedDisc.subBd_eq_discBd isClosedSurface_sphere' hd, hbd,
      ← image_inter sc.injective_of_univ, P.closure_inter_N hc]
    exact image_mono (P.cell_disc c hc).2
  isClosed_U := hf.isClosedMap _ P.isClosed_U
  cell_complement e he := by
    change e ∈ arcComponentsIn (f '' P.U \ f '' P.N) at he
    rw [P.arcComponentsIn_image sc] at he
    obtain ⟨c, hc, rfl⟩ := he
    rw [hf.closure_image_eq, ← image_inter sc.injective_of_univ, P.closure_inter_N hc,
      image_sdiff sc.injective_of_univ]

theorem PaintingInDisc.toDiscPainting_E (P : PaintingInDisc S)
    (sc : SphereDiscChart (univ : Set S) f f') (hf : IsClosedEmbedding f) :
    (P.toDiscPainting sc hf).E = image f '' P.cells :=
  P.arcComponentsIn_image sc

theorem PaintingInDisc.toDiscPainting_V (P : PaintingInDisc S)
    (sc : SphereDiscChart (univ : Set S) f f') (hf : IsClosedEmbedding f) :
    (P.toDiscPainting sc hf).V = f '' P.N :=
  rfl

variable {Q : Type w}

/-- A `Q`-portrait in a disc `S`, carried into the sphere as a labelled painting of IV. The march
is the ordering `α` of the boundary nodes, and each cell keeps its ordering and its label. -/
@[expose] noncomputable def QPortrait.toLabelled (P : QPortrait Q S)
    (sc : SphereDiscChart (univ : Set S) f f') (hf : IsClosedEmbedding f) :
    GM04.LabelledPainting Q (OnePoint EuclideanPlane) where
  painting := P.painting.toDiscPainting sc hf
  roots := P.α.map f
  roots_nodup := P.α_nodup.map sc.injective_of_univ
  roots_subset v hv := by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
    have hx' : x ∈ {x : S | x ∈ P.α} := hx
    rw [P.α_set] at hx'
    exact mem_image_of_mem f (P.painting.inter_bd_subset_N hx')
  μ e := (P.μ (f ⁻¹' e)).map f
  μ_nodup e he := by
    rw [PaintingInDisc.toDiscPainting_E] at he
    obtain ⟨c, hc, rfl⟩ := he
    rw [preimage_image_eq c sc.injective_of_univ]
    exact (P.μ_nodup c hc).map sc.injective_of_univ
  μ_set e he := by
    rw [PaintingInDisc.toDiscPainting_E] at he
    obtain ⟨c, hc, rfl⟩ := he
    rw [preimage_image_eq c sc.injective_of_univ, hf.closure_image_eq,
      ← image_sdiff sc.injective_of_univ, ← P.μ_set c hc]
    ext y
    simp [List.mem_map]
  φ e := P.φ (f ⁻¹' e)

open Classical in
/-- The tree-width bound for the labelled painting of a portrait. If the portrait has tree-width
at most `w`, then the labelled painting in the sphere has tree-width at most `w + k` in the sense
of Graph Minors IV, where `k` is the index. We take the hypertree of the portrait, root it, and
add the `k` boundary nodes to every bag. IV asks that the root bag hold the march, which is why
the boundary nodes are added (the remark after (10.1), page 271). -/
theorem treeWidthLE_toLabelled (P : QPortrait Q S) (sc : SphereDiscChart (univ : Set S) f f')
    (hf : IsClosedEmbedding f) {w : ℕ} (h : PortraitTreeWidthLE P w) :
    GM04.TreeWidthLE (P.toLabelled sc hf).toRootedHypergraph (w + P.index) := by
  obtain ⟨ι, _, T, X, hT, hw, hcell⟩ := h
  have hinj := sc.injective_of_univ
  let e := Fintype.equivFin ι
  have hT' := hT.relabel e
  have hK : (T.map e.toEmbedding).IsTree := hT'.isTree
  let R := Thomas.rootedTreeOfIsTree hK
  let A : Set S := {x | x ∈ P.α}
  have hA : A = P.painting.U ∩ bd S := P.α_set
  have hAN : A ⊆ P.painting.N := hA ▸ P.painting.inter_bd_subset_N
  let X' : ℕ → Set S := fun n => if hn : n < Fintype.card ι then X (e.symm ⟨n, hn⟩) else ∅
  have hXN : ∀ n, X' n ⊆ P.painting.N := by
    intro n
    by_cases hn : n < Fintype.card ι
    · simp only [X', dite_eq_left hn]
      rw [← hT.iUnion_eq]
      exact subset_iUnion X _
    · simp only [X', dite_eq_right hn]
      exact empty_subset _
  let Vb : ℕ → Set (OnePoint EuclideanPlane) := fun n => f '' X' n ∪ f '' A
  have hmem : ∀ {t : ℕ}, t ∈ R.verts ↔ t < Fintype.card ι := fun {t} => Finset.mem_range
  let G := (P.toLabelled sc hf).toRootedHypergraph
  have hGV : G.vertexSet = f '' P.painting.N := rfl
  have hGE : G.edgeSet = image f '' P.painting.cells := P.painting.toDiscPainting_E sc hf
  have hGroot : G.rootSet = f '' A := by
    ext y
    change y ∈ P.α.map f ↔ _
    simp [List.mem_map, A]
  obtain ⟨τ, hτ, hτV⟩ := GM04.exists_isTreeDecomposition_of_ends_subset G R Vb
    (fun t _ => union_subset (image_mono (hXN t)) (image_mono hAN))
    (by
      apply Subset.antisymm
      · exact iUnion₂_subset fun t _ => union_subset (image_mono (hXN t)) (image_mono hAN)
      · rintro _ ⟨x, hx, rfl⟩
        rw [← hT.iUnion_eq] at hx
        obtain ⟨t, ht⟩ := mem_iUnion.1 hx
        refine mem_iUnion₂.2 ⟨(e t).val, hmem.2 (e t).isLt, Or.inl ⟨x, ?_, rfl⟩⟩
        simp only [X', dite_eq_left (e t).isLt, Fin.eta, Equiv.symm_apply_apply]
        exact ht)
    (by
      intro c hc
      rw [hGE] at hc
      obtain ⟨c, hc, rfl⟩ := hc
      obtain ⟨t, ht⟩ := hcell c hc
      refine ⟨(e t).val, hmem.2 (e t).isLt, ?_⟩
      have hends := GM04.LabelledPainting.ends_eq (P.toLabelled sc hf)
        (e := f '' c) (by rw [show (P.toLabelled sc hf).painting.E = _ from hGE]; exact ⟨c, hc, rfl⟩)
      change G.ends (f '' c) ⊆ _
      rw [hends, hf.closure_image_eq, ← image_sdiff hinj]
      refine subset_union_left.trans' (image_mono ?_)
      simp only [X', dite_eq_left (e t).isLt, Fin.eta, Equiv.symm_apply_apply]
      exact ht)
    (by
      intro t₁ h₁ t₂ h₂ t₃ h₃ hon
      have hon' := (Thomas.onPath_rootedTreeOfIsTree_iff hK ⟨t₁, h₁⟩ ⟨t₃, h₃⟩ ⟨t₂, h₂⟩).1 hon
      have hsub := hT'.inter_subset hon'
      have hX : ∀ t (ht : t ∈ R.verts), X' t = (X ∘ e.symm) (Thomas.equivFinOfIsTree hK ⟨t, ht⟩) :=
        fun t ht => by simp only [X', dite_eq_left (hmem.1 ht)]; rfl
      rintro y ⟨hy₁, hy₃⟩
      rcases hy₁ with ⟨x, hx₁, rfl⟩ | hyA
      · rcases hy₃ with ⟨x', hx₃, hxx⟩ | hyA
        · rw [hinj hxx] at hx₃
          rw [hX t₁ h₁] at hx₁
          rw [hX t₃ h₃] at hx₃
          refine Or.inl ⟨x, ?_, rfl⟩
          rw [hX t₂ h₂]
          exact hsub ⟨hx₁, hx₃⟩
        · exact Or.inr hyA
      · exact Or.inr hyA)
    (by
      rw [hGroot]
      exact subset_union_right)
  refine ⟨R, τ, hτ, fun t ht => ?_⟩
  rw [hτV t ht]
  have hXfin : (X' t).Finite := P.painting.finite_N.subset (hXN t)
  have hAfin : A.Finite := P.painting.finite_N.subset hAN
  have hXw : (X' t).ncard ≤ w + 1 := by
    simp only [X', dite_eq_left (hmem.1 ht)]
    exact hw _
  have hAk : A.ncard = P.index := by rw [hA]; rfl
  calc (Vb t).ncard ≤ (f '' X' t).ncard + (f '' A).ncard := ncard_union_le _ _
    _ ≤ (X' t).ncard + A.ncard := add_le_add (ncard_image_le hXfin) (ncard_image_le hAfin)
    _ ≤ w + P.index + 1 := by omega

end Push

end GM08
end GraphMinor
