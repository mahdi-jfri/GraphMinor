module

public import GraphMinor.GM08.Defs6to18
import GraphMinor.GM08.Section10Push
import GraphMinor.GM04.PaintingTheorem
import GraphMinor.GM11.Walks
import GraphMinor.GM12.Section3ForestTransport
import GraphMinor.GM22.Section3Disc

/-!
# Graph Minors VIII, (10.1)

Graph Minors VIII states (10.1) for portraits in a disc and says that it "is proved in
[8, Theorem (9.2)]", which is Graph Minors IV, (9.2) (`GM04.theorem_9_2`). IV states (9.2) for
paintings in a closed surface. So we put the disc in the sphere by the chart of
`exists_sphereDiscChart`. Each portrait becomes a labelled painting of IV in the sphere
(`QPortrait.toLabelled`), of tree-width at most `w + k` in the sense of IV
(`treeWidthLE_toLabelled`). IV (9.2) then gives `i < j`, a drawn forest `Ξ` in the sphere, and the
maps `σ`. The forest lies in the image of the disc, since its edges lie in cells. We read it back
in the disc (`GM22.drawingComap`), and we read each component and each cell back by preimage. The
conditions (i)–(viii) of a simulation then follow from those of IV (9.2), since the chart is
injective.
-/

public section

namespace GraphMinor
namespace GM08

open Set Topology Surface

universe u w

variable {S : Type u} [TopologicalSpace S]

/-- **Graph Minors VIII, (10.1)** (page 271): "(10.1) *Let* $\mathbf{Q}$ *be a well-quasi-order, and let* $k, w \ge 0$ *be integers. Let* $P_1, P_2, \dots$ *be a countable sequence of* $\mathbf{Q}$*-portraits all with index* $k$ *and tree-width* $\le w$. *Then there exist* $j > i \ge 1$ *such that* $P_i$ *is simulated in* $P_j$." Here `S` is the disc $\Sigma$ of Section 10, and the sequence is indexed
from `0`. The proof applies Graph Minors IV, (9.2), as the paper does. -/
theorem theorem_10_1_proof {Q : Type w} {le : Q → Q → Prop} (hQ : IsWellQuasiOrder le)
    (hS : IsClosedDisc (univ : Set S)) (k w : ℕ) (P : ℕ → QPortrait Q S)
    (hindex : ∀ i, (P i).index = k) (htw : ∀ i, PortraitTreeWidthLE (P i) w) :
    ∃ i j, i < j ∧ IsPortraitSimulatedIn le (P i) (P j) := by
  classical
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hS
  have hf : IsClosedEmbedding f := sc.isClosedEmbedding_of_univ hS
  have hinj : Function.Injective f := sc.injective_of_univ
  have : T2Space S := hf.isEmbedding.t2Space
  have : Nonempty S := by
    obtain ⟨φ⟩ := hS
    exact ⟨(φ GM11.discCentre).1⟩
  let : Preorder Q :=
    { le := le
      le_refl := hQ.1.1
      le_trans := hQ.1.2 }
  have hwqo : WellQuasiOrderedLE Q := ⟨fun q => hQ.2 q⟩
  let L : ℕ → GM04.LabelledPainting Q (OnePoint EuclideanPlane) :=
    fun i => (P i).toLabelled sc hf
  have hLtw : ∀ i, GM04.TreeWidthLE (L i).toRootedHypergraph (w + k) := fun i => by
    have h := treeWidthLE_toLabelled (P i) sc hf (htw i)
    rwa [hindex i] at h
  obtain ⟨i, j, hij, Ξ, σv, σe, hΞV, hforest, hΞE, hcomp, hmaps, hinjσ, hdisj, hedge, hcell,
    hroots, hle⟩ := GM04.theorem_9_2_proof hwqo isClosedSurface_sphere' (w + k) L hLtw
  refine ⟨i, j, hij, ?_⟩
  -- The cells of `L i` are the images of the cells of `P i`.
  have hLE : ∀ n, (L n).painting.E = image f '' (P n).painting.cells := fun n =>
    (P n).painting.toDiscPainting_E sc hf
  have hLV : ∀ n, (L n).painting.V = f '' (P n).painting.N := fun n => rfl
  -- The forest lies in the image of the disc.
  have hΞU : Ξ.U ⊆ range f := by
    intro y hy
    by_cases hyV : y ∈ Ξ.V
    · rw [hΞV, hLV] at hyV
      obtain ⟨x, -, rfl⟩ := hyV
      exact mem_range_self x
    · obtain ⟨g, hg, hyg⟩ := Ξ.exists_edge_of_mem hy hyV
      obtain ⟨c, hc, hgc⟩ := hΞE g hg
      rw [hLE] at hc
      obtain ⟨c, -, rfl⟩ := hc
      obtain ⟨x, -, rfl⟩ := hgc hyg
      exact mem_range_self x
  let Ξs := GM22.drawingComap Ξ hf hΞU
  let ιV : S ↪ OnePoint EuclideanPlane := ⟨f, hinj⟩
  let ιE : Set S ↪ Set (OnePoint EuclideanPlane) := ⟨image f, image_injective.mpr hinj⟩
  have hmap : Ξs.toGraph.mapEmbed ιV ιE = Ξ.toGraph := GM22.drawingComap_toGraph_mapEmbed Ξ hf hΞU
  -- Each component of `Ξ` is the image of its preimage.
  have hσv : ∀ v ∈ (P i).painting.N,
      ((σv (f v)).comapEmbed ιV ιE).mapEmbed ιV ιE = σv (f v) ∧
        GM06.IsGraphComponent ((σv (f v)).comapEmbed ιV ιE) Ξs.toGraph := by
    intro v hv
    have hC := hcomp (f v) (mem_image_of_mem f hv)
    rw [← hmap] at hC
    obtain ⟨heq, -⟩ := GM22.mapEmbed_comapEmbed_of_le ιV ιE hC.1
    refine ⟨heq, (GM22.isGraphComponent_mapEmbed_iff ιV ιE).mp ?_⟩
    rw [heq]
    exact hC
  -- Each cell `σe (f '' e)` is the image of a cell of `P j`.
  have hσe : ∀ e ∈ (P i).painting.cells,
      f '' (f ⁻¹' σe (f '' e)) = σe (f '' e) ∧ f ⁻¹' σe (f '' e) ∈ (P j).painting.cells := by
    intro e he
    have h := hmaps (show f '' e ∈ (L i).painting.E by rw [hLE]; exact mem_image_of_mem _ he)
    change σe (f '' e) ∈ (L j).painting.E at h
    rw [hLE] at h
    obtain ⟨c, hc, hce⟩ := h
    rw [← hce, preimage_image_eq c hinj]
    exact ⟨rfl, hc⟩
  have hsdiff : ∀ A : Set S, closure (f '' A) \ f '' A = f '' (closure A \ A) := fun A => by
    rw [hf.closure_image_eq, image_sdiff hinj]
  refine ⟨Ξs, fun v => (σv (f v)).comapEmbed ιV ιE, fun e => f ⁻¹' σe (f '' e), ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change f ⁻¹' Ξ.V = _
    rw [hΞV, hLV, preimage_image_eq _ hinj]
  · -- `Ξ` read in the disc is still a forest.
    refine GM12.isGraphForest_of_injective_link_map f (image f) hinj (image_injective.mpr hinj)
      (fun x hx => hx) (fun {g x y} hl => ?_) hforest
    rw [← hmap]
    exact (GM22.isLink_mapEmbed_iff ιV ιE Ξs.toGraph).mpr hl
  · exact fun v hv => (hσv v hv).2
  · exact fun e he => (hσe e he).2
  · -- (i): every edge of the forest lies in a cell.
    intro g hg
    have hg' : f '' g ∈ Ξ.E := by
      change f '' g ∈ Graph.edgeSet Ξ.toGraph
      rw [← hmap]
      exact mem_image_of_mem ιE hg
    obtain ⟨c, hc, hgc⟩ := hΞE _ hg'
    rw [hLE] at hc
    obtain ⟨c, hc, rfl⟩ := hc
    exact ⟨c, hc, (image_subset_image_iff hinj).mp hgc⟩
  · -- (ii): distinct nodes go to distinct components.
    intro v₁ hv₁ v₂ hv₂ hne heq
    change (σv (f v₁)).comapEmbed ιV ιE = (σv (f v₂)).comapEmbed ιV ιE at heq
    have h₁ := (hσv v₁ hv₁).1
    rw [heq, (hσv v₂ hv₂).1] at h₁
    have hd := hdisj (f v₁) (mem_image_of_mem f hv₁) (f v₂) (mem_image_of_mem f hv₂)
      (fun h => hne (hinj h))
    rw [← h₁] at hd
    obtain ⟨x, hx⟩ := (hcomp (f v₂) (mem_image_of_mem f hv₂)).2.1.1
    exact disjoint_left.mp hd (Or.inl hx) (Or.inl hx)
  · -- (iii): distinct cells go to distinct cells.
    intro e₁ he₁ e₂ he₂ heq
    have h : f '' (f ⁻¹' σe (f '' e₁)) = f '' (f ⁻¹' σe (f '' e₂)) := congrArg (image f) heq
    rw [(hσe e₁ he₁).1, (hσe e₂ he₂).1] at h
    exact (image_injective.mpr hinj) (hinjσ (by rw [hLE]; exact mem_image_of_mem _ he₁)
      (by rw [hLE]; exact mem_image_of_mem _ he₂) h)
  · -- (iv): no edge of a component meets the image of a cell.
    intro v hv e he g hg
    obtain ⟨x₀, y₀, hl⟩ := hg
    have hg' : f '' g ∈ Graph.edgeSet (σv (f v)) := hl.edge_mem
    have hd := hedge (f v) (mem_image_of_mem f hv) (f '' e)
      (by rw [hLE]; exact mem_image_of_mem _ he) _ hg'
    rw [← (hσe e he).1] at hd
    exact (disjoint_image_iff hinj).mp hd
  · -- (v): cells keep their number of attachments.
    intro e he
    have h := (hcell (f '' e) (by rw [hLE]; exact mem_image_of_mem _ he)).1
    rw [← (hσe e he).1, hsdiff, hsdiff, ncard_image_of_injective _ hinj,
      ncard_image_of_injective _ hinj] at h
    exact h
  · -- (vi): the orderings of the cells.
    intro e he n hn hn'
    have h := (hcell (f '' e) (by rw [hLE]; exact mem_image_of_mem _ he)).2.2 n
    have key : (L i).μ (f '' e) = ((P i).μ e).map f := by
      change List.map f ((P i).μ (f ⁻¹' (f '' e))) = _
      rw [preimage_image_eq e hinj]
    have keyj : (L j).μ (σe (f '' e)) = ((P j).μ (f ⁻¹' σe (f '' e))).map f := rfl
    have h' := h (by rw [key]; simpa using hn) (by rw [keyj]; simpa using hn')
    simp only [key, keyj, List.getElem_map] at h'
    exact h'
  · -- (vii): the index and the ordering of the boundary nodes.
    refine ⟨(hindex i).trans (hindex j).symm, fun n hn hn' => ?_⟩
    have h := hroots.2 n
    have keyi : (L i).roots = (P i).α.map f := rfl
    have keyj : (L j).roots = (P j).α.map f := rfl
    have h' := h (by rw [keyi]; simpa using hn) (by rw [keyj]; simpa using hn')
    simp only [keyi, keyj, List.getElem_map] at h'
    exact h'
  · -- (viii): the labels.
    intro e he
    have h := hle (f '' e) (by rw [hLE]; exact mem_image_of_mem _ he)
    change le ((P i).φ (f ⁻¹' (f '' e))) ((P j).φ (f ⁻¹' σe (f '' e))) at h
    rwa [preimage_image_eq e hinj] at h

end GM08
end GraphMinor
