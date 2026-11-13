module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.Collapse
import GraphMinor.GM07.CuffCollapse
import GraphMinor.GM11.Forest
import GraphMinor.GM11.Section5
import GraphMinor.GM19.Section6a

/-!
# Collapsing an edge while allowing loops in the remaining drawing

GM V, (8.14), uses that contractions of drawn expansions can still be
drawn. Collapse the closed arc of a nonloop edge by the proved surface
collapse. Delete that edge first. Every remaining open edge has only
singleton fibres, so the proved image-drawing construction applies.
Parallel edges may become loops. Their open edges and endpoint sets
are still followed by the collapse map.
-/

public section
namespace GraphMinor.GM05
open Set Topology Surface GM11

/-- The nonloop edge contraction used in the drawing step of GM V,
proof of (8.14), page 113. Other edges may be loops or parallel edges. -/
theorem exists_drawing_collapse_nonloop {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) (D : Drawing S) {f : Set S} (hf : f∈D.E)
    {u v : S} (hline : IsLineWithEnds (closure f) u v) :
    ∃ (D' : Drawing S) (π : S → S),Continuous π ∧
      D'.U=π '' (D.U\f) ∧ D'.V=π '' D.V ∧
      (∀ x∈D.V,∀ y∈D.V,π x=π y ↔ x=y ∨ (x∈tilde f ∧ y∈tilde f)) ∧
      BijOn (image π) (D.E\{f}) D'.E ∧
      ∀ e∈D.E,e≠f → tilde (π '' e)=π '' tilde e := by
  classical
  let : CompactSpace S := hS.1
  let : T2Space S := hS.2.1
  let : Nonempty S := ⟨u⟩
  obtain ⟨a,ha,har,-,-⟩ := hline.exists_arc
  obtain ⟨c,w,hc,hc0,hcw,hcn,hci,-⟩ := exists_collapse hS ha
  rw [har] at hcw hcn hci
  let π : S → S := fun x ↦ c (1,x)
  have hπc : Continuous π := hc.comp (continuous_const.prodMk continuous_id)
  have hstable : ∀ x∉closure f,∀ y,π y=π x → y=x := by
    intro x hx y he
    by_cases hy : y∈closure f
    · exact (hcn x hx (he.symm.trans (hcw y hy))).elim
    · exact hci hy hx he
  have heoff : ∀ e∈D.E,e≠f → e⊆(closure f)ᶜ := by
    intro e he hef x hx hxf
    have hxV : x∉D.V := (he.2.1 hx).2
    have hxf' : x∈f := (D.closure_diff_V hf).subset ⟨hxf,hxV⟩
    exact hef (D.edge_eq_of_mem he hf hx hxf')
  have hdel : (D.deleteEdge f).U\(D.deleteEdge f).V⊆(closure f)ᶜ := by
    rw [deleteEdge_U D hf,deleteEdge_V]
    rintro x ⟨⟨hx,hxf⟩,hxV⟩ hxcl
    exact hxf ((D.closure_diff_V hf).subset ⟨hxcl,hxV⟩)
  obtain ⟨D',hU,hV,hE⟩ := GM07.exists_collapse_drawing hπc hstable (D.deleteEdge f) hdel
  rw [deleteEdge_U D hf] at hU
  rw [deleteEdge_V] at hV
  rw [deleteEdge_E] at hE
  have hvinj : ∀ x∈D.V,∀ y∈D.V,π x=π y ↔ x=y ∨ (x∈tilde f ∧ y∈tilde f) := by
    intro x hx y hy
    constructor
    · intro he
      by_cases hxy : x=y
      · exact .inl hxy
      · right
        have hxcl : x∈closure f := by
          by_contra hn
          exact hxy (hstable x hn y he.symm).symm
        have hycl : y∈closure f := by
          by_contra hn
          exact hxy (hstable y hn x he)
        rw [GM19.tilde_eq_inter_V D hf]
        exact ⟨⟨hxcl,hx⟩,hycl,hy⟩
    · rintro (rfl|⟨hx,hy⟩)
      · rfl
      · exact (hcw x hx.1).trans (hcw y hy.1).symm
  have heinj : InjOn (image π) (D.E\{f}) := by
    intro e he e' he' heq
    have hi : InjOn π ((closure f)ᶜ) := fun x hx y hy he ↦ (hstable x hx y he.symm).symm
    exact (hi.image_eq_image_iff (heoff e he.1 he.2) (heoff e' he'.1 he'.2)).mp heq
  have hebij : BijOn (image π) (D.E\{f}) D'.E := by
    refine ⟨?_,heinj,?_⟩
    · intro e he
      rw [hE]
      exact mem_image_of_mem _ he
    · intro e he
      rw [hE] at he
      exact he
  refine ⟨D',π,hπc,hU,hV,hvinj,hebij,?_⟩
  intro e he hef
  unfold tilde
  rw [hπc.isClosedMap.closure_image_eq_of_continuous hπc]
  ext z
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,hnot⟩
    exact ⟨x,⟨hx,fun hxe ↦ hnot (mem_image_of_mem π hxe)⟩,rfl⟩
  · rintro ⟨x,⟨hx,hxe⟩,rfl⟩
    refine ⟨mem_image_of_mem π hx,?_⟩
    rintro ⟨y,hy,hyx⟩
    have hxy : x=y := hstable y (heoff e he hef hy) x hyx.symm
    exact hxe (hxy ▸ hy)

end GraphMinor.GM05
