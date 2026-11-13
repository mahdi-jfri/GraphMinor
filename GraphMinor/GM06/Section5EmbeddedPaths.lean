module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM07.Matched
import GraphMinor.GM06.Section5WalkSubpaths
import GraphMinor.GM06.Section4PathTools
public import GraphMinor.GM07.Section9MoveOff
import GraphMinor.GM11.Walks
import GraphMinor.GM07.NetExists

/-!
# Carrying a frontier path back through a closed embedding

The boundary walk for VI (5.1), page 129, can be read after embedding
the drawing in a sphere. Carry its walk back through the inverse
matching and remove repeated vertices. The resulting path uses only
points of the original frontier path and preserves exclusion of an
edge. This applies to both the cylinder and the one-path cut disc.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11
universe u v

/-- A path between distinct image vertices pulls back through a closed
embedding, using only points of the image path. -/
theorem exists_subpath_of_embedded_subpath
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] [CompactSpace X] [T2Space X] [T2Space Y] {f : X → Y} (hf : IsClosedEmbedding f)
    {G : Drawing X} {P : Drawing Y} {a b : X} (hab : a ≠ b)
    (hP : IsSubpathOf (GM07.embedDrawing hf G) P (f a) (f b)) :
    ∃ Q : Drawing X, IsSubpathOf G Q a b ∧ f '' Q.U ⊆ P.U := by
  classical
  let H := GM07.embedDrawing hf G
  have hHV : H.V = f '' G.V := GM07.embedDrawing_V hf G
  obtain ⟨ψ, hleft, hright, hcarry⟩ := (GM07.embedDrawing_isMatched hf G).exists_inverse
  have haH : f a ∈ H.V := hP.1.1 (isPathDrawing_end_vertices hP.2.2).1
  have hbH : f b ∈ H.V := hP.1.1 (isPathDrawing_end_vertices hP.2.2).2
  have haG : a ∈ G.V := by
    obtain ⟨x, hx, hxa⟩ := hHV ▸ haH
    exact hf.injective hxa ▸ hx
  have hbG : b ∈ G.V := by
    obtain ⟨x, hx, hxb⟩ := hHV ▸ hbH
    exact hf.injective hxb ▸ hx
  obtain ⟨W, _, hV, hE⟩ := hP.2.2.1
  have hle : P.toGraph ≤ H.toGraph :=
    { vertexSet_mono := hP.1.1
      isLink_mono := fun _ _ _ hl => (hP.1.isLink_iff hl.1).mp hl }
  let W₀ := W.mono hle
  obtain ⟨R, hRV, hRE, _, _⟩ := hcarry.walk W₀ haH a b
    (hleft a (G.V_subset_U haG)) (hleft b (G.V_subset_U hbG))
  obtain ⟨Q, hQ, hQV, hQE⟩ :=
    exists_subpath_of_walk_support G R R.start_mem_support R.end_mem_support hab
  have hvertices : ∀ x ∈ Q.V, f x ∈ P.U := by
    intro x hx
    have hxR := hQV hx
    rw [hRV, show W₀.support = W.support from GraphWalk.support_mono hle W] at hxR
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hxR
    have hyV : y ∈ P.V := by rw [hV]; exact hy
    rw [hright y (hP.2.1 (P.V_subset_U hyV))]
    exact P.V_subset_U hyV
  refine ⟨Q, hQ, ?_⟩
  rintro z ⟨x, hx, rfl⟩
  rw [Q.U_eq] at hx
  rcases hx with hxV | hxE
  · exact hvertices x hxV
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxE
    have heR := hQE he
    rw [hRE, show W₀.edges = W.edges from GraphWalk.edges_mono hle W] at heR
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp heR
    have heP : e' ∈ P.E := by rw [hE]; exact he'
    have him : f '' (ψ '' e') = e' := by
      rw [image_image]
      calc
        (f ∘ ψ) '' e' = id '' e' := image_congr fun y hy =>
          hright y (hP.2.1 (P.closure_subset_U heP (subset_closure hy)))
        _ = e' := image_id' e'
    have hxIm : f x ∈ f '' closure (ψ '' e') := ⟨x, hxe, rfl⟩
    rw [← hf.closure_image_eq, him] at hxIm
    exact P.closure_subset_U heP hxIm

/-- Pullback of an embedded subpath also preserves exclusion of an edge. -/
theorem exists_subpath_of_embedded_subpath_avoiding_edge
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] [CompactSpace X] [T2Space X] [T2Space Y] {f : X → Y} (hf : IsClosedEmbedding f)
    {G : Drawing X} {P : Drawing Y} {a b : X} (hab : a ≠ b)
    (hP : IsSubpathOf (GM07.embedDrawing hf G) P (f a) (f b))
    {e : Set X} (he : f '' e ∉ P.E) :
    ∃ Q : Drawing X, IsSubpathOf G Q a b ∧ f '' Q.U ⊆ P.U ∧ e ∉ Q.E := by
  classical
  obtain ⟨Q, hQ, hU⟩ := exists_subpath_of_embedded_subpath hf hab hP
  refine ⟨Q, hQ, hU, ?_⟩
  intro heQ
  obtain ⟨x, hx⟩ := heQ.1
  have hxP : f x ∈ P.U := hU ⟨x, (heQ.2.1 hx).1, rfl⟩
  have hxPV : f x ∉ P.V := by
    intro hxV
    have hxH := hP.1.1 hxV
    rw [GM07.embedDrawing_V] at hxH
    obtain ⟨y, hy, hyx⟩ := hxH
    exact ((hQ.1.2 heQ).2.1 hx).2 (hf.injective hyx ▸ hy)
  obtain ⟨e', he', hxe'⟩ := P.exists_edge_of_mem hxP hxPV
  have heH : f '' e ∈ (GM07.embedDrawing hf G).E := by
    rw [GM07.embedDrawing_E]
    exact ⟨e, hQ.1.2 heQ, rfl⟩
  have heq := GM07.arcComponentsIn_eq_of_mem heH (hP.1.2 he')
    (mem_image_of_mem f hx) hxe'
  exact he (heq.symm ▸ he')

end GraphMinor.GM06
