module

public import GraphMinor.GM01.RootedModelOfMinor
public import GraphMinor.GM01.RootedPathAttachment
import GraphMinor.GM01.GraphSeparators
import GraphMinor.GM09.Section2c

/-!
# Rooting an ordinary model in a connected target

The bypass in Graph Minors I, (4.1), page 55, reaches an arbitrary vertex
of the final block. An ordinary comb model there can be rooted at some
source vertex while retaining this target root. Follow a path from the
target root to the first model branch it meets, then add that initial
path to that branch. It meets no other branch, so the model remains
valid. Choosing a long side of the comb is a further step.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09

/-- In a connected rooted target, an ordinary simple-source model can
be rooted at some source vertex without changing the target root.
The new root branch includes a path to the first branch encountered. -/
theorem exists_rooted_model_of_ordinary {ν α β : Type*} [Nonempty ν]
    {S : SimpleGraph ν} (G : RootedGraph α β) (hconn : GraphConnected G.graph)
    {ηv : ν → Set α} {ηe : Sym2 ν → β}
    (h : IsMinorModel (Graph.ofSimpleGraph S) G.graph ηv ηe) :
    ∃ r : ν, HasRootedMinor
      (⟨Graph.ofSimpleGraph S, ⟨r, mem_univ _⟩⟩ : RootedGraph ν (Sym2 ν)) G := by
  classical
  let Z : Set α := ⋃ v, ηv v
  let v : ν := Classical.arbitrary ν
  obtain ⟨x, hx⟩ := h.vertex_nonempty v (mem_univ _)
  have hxG : x ∈ V(G.graph) := h.vertex_subset v (mem_univ _) hx
  obtain ⟨P, hP⟩ := exists_path_of_adj_reachable G.root.property
    (hconn.2 G.root.val G.root.property x hxG)
  have hxZ : x ∈ Z := mem_iUnion.mpr ⟨v, hx⟩
  obtain ⟨p, ⟨_, hpZ⟩, R, _, hR₀, hRZ, _⟩ := hP.exists_first_hit ⟨x, hP.right_mem, hxZ⟩
  have hR := hR₀.mono hP.le
  obtain ⟨r, hpr⟩ := mem_iUnion.mp hpZ
  have hpG : p ∈ V(G.graph) := h.vertex_subset r (mem_univ _) hpr
  let M := rootedModelOfMinorModel h r ⟨p, hpG⟩ hpr
  have hDisj : ∀ w : V(Graph.ofSimpleGraph S), w ≠ ⟨r, mem_univ _⟩ →
      Disjoint (M.branch w) V(R) := by
    intro w hwr
    apply Set.disjoint_left.mpr
    intro y hy hyR
    rw [rootedModelOfMinorModel_branch] at hy
    have hyZ : y ∈ Z := mem_iUnion.mpr ⟨w.val, hy⟩
    have hyp : y = p := mem_singleton_iff.mp (hRZ ▸ ⟨hyR, hyZ⟩)
    have hneq : w.val ≠ r := fun heq ↦ hwr (Subtype.ext heq)
    exact Set.disjoint_left.mp (h.vertex_disjoint w.val (mem_univ _) r (mem_univ _) hneq)
      hy (hyp.symm ▸ hpr)
  let L := M.attachRootPathOfDisjointBranches le_rfl G.root.val hR hDisj
  exact ⟨r, ⟨L.mono (subgraphUnion_le le_rfl hR.le) rfl⟩⟩

end GraphMinor.GM01
