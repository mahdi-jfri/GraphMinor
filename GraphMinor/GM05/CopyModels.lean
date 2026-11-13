module

public import GraphMinor.GM05.GraphCopies
public import GraphMinor.Minor.Model
import GraphMinor.Minor.Basic

/-!
# Restricting a model of disjoint copies

The branch sets belonging to a fixed copy form a vertex set disjoint
from those of the other copies. Restrict the host to that vertex set.
The original branch sets and representing edges then model `H` there.
This is the model step behind the packing reduction in Graph Minors V,
proof of (8.8), page 111.
-/

public section

namespace GraphMinor.GM05

open Graph Set

/-- A modelled source edge has a representing link with one end in each
of the appropriate branch sets, also for loops. -/
theorem minor_model_link {α β α' β' : Type*} {H : Graph α' β'} {G : Graph α β}
    {ηv : α' → Set α} {ηe : β' → β} (hm : IsMinorModel H G ηv ηe)
    {e : β'} {u v : α'} (hl : H.IsLink e u v) :
    ∃ x∈ηv u, ∃ y∈ηv v, G.IsLink (ηe e) x y := by
  have he := hl.edge_mem
  obtain ⟨x,hx,y,hxy⟩ := (hm.inc_iff u hl.left_mem e he).mp hl.inc_left
  by_cases hloop : H.IsLoopAt e u
  · have hvu : v=u := (hl.right_eq_or_eq hloop).elim id id
    subst v
    exact ⟨x,hx,y,(hm.isLoopAt_iff u hl.left_mem e he).mp hloop y hxy.inc_right,hxy⟩
  · have huv : u≠v := fun h ↦ hloop (h ▸ hl)
    obtain ⟨z,hz,hzinc⟩ := (hm.inc_iff v hl.right_mem e he).mp hl.inc_right
    have hxz : x≠z := (hm.vertex_disjoint u hl.left_mem v hl.right_mem huv).ne_of_mem hx hz
    have hzy : z=y := hzinc.eq_of_isLink_of_ne_left hxy hxz.symm
    exact ⟨x,hx,y,hzy ▸ hz,hxy⟩

/-- Restrict a copy model to the union of the branches belonging to one
copy. The resulting model is a model of `H`. -/
theorem copy_model_restrict {α β α' β' : Type*} {k : ℕ}
    {H : Graph α' β'} {G : Graph α β}
    {ηv : Fin k × α' → Set α} {ηe : Fin k × β' → β}
    (hm : IsMinorModel (graphCopies k H) G ηv ηe) (i : Fin k) :
    IsMinorModel H (G.induce (⋃ v∈V(H),ηv (i,v)))
      (fun v ↦ ηv (i,v)) (fun e ↦ ηe (i,e)) := by
  let B := ⋃ v∈V(H),ηv (i,v)
  have hBi : B⊆V(G) := by
    intro x hx
    obtain ⟨v,hv,hxv⟩ := mem_iUnion₂.mp hx
    exact hm.vertex_subset (i,v) ⟨mem_univ i,hv⟩ hxv
  have ends (e : β') (he : e∈E(H)) : ∀ x, G.Inc (ηe (i,e)) x → x∈B := by
    obtain ⟨u,v,huv⟩ := exists_isLink_of_mem_edgeSet he
    have hcopy : (graphCopies k H).IsLink (i,e) (i,u) (i,v) := ⟨rfl,rfl,huv⟩
    obtain ⟨x,hx,y,hy,hxy⟩ := minor_model_link hm hcopy
    have hxB : x∈B := mem_biUnion huv.left_mem hx
    have hyB : y∈B := mem_biUnion huv.right_mem hy
    intro z hz
    rcases hz.eq_or_eq_of_isLink hxy with rfl|rfl
    · exact hxB
    · exact hyB
  have hinc (e : β') (he : e∈E(H)) (x : α) :
      (G.induce B).Inc (ηe (i,e)) x ↔ G.Inc (ηe (i,e)) x := by
    constructor
    · rintro ⟨y,hxy⟩; exact ⟨y,hxy.1⟩
    · rintro ⟨y,hxy⟩
      exact ⟨y,hxy,ends e he x hxy.inc_left,ends e he y hxy.inc_right⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro v hv
    exact hm.vertex_nonempty (i,v) ⟨mem_univ i,hv⟩
  · intro v hv x hx
    exact mem_biUnion hv hx
  · intro e he
    have heG := hm.edge_mem (i,e) ⟨mem_univ i,he⟩
    obtain ⟨x,y,hxy⟩ := exists_isLink_of_mem_edgeSet heG
    exact ⟨x,y,hxy,ends e he x hxy.inc_left,ends e he y hxy.inc_right⟩
  · intro u hu v hv huv
    exact hm.vertex_disjoint (i,u) ⟨mem_univ i,hu⟩ (i,v) ⟨mem_univ i,hv⟩
      (fun h ↦ huv (congrArg Prod.snd h))
  · intro e he f hf hef
    exact congrArg Prod.snd (hm.edge_injOn ⟨mem_univ i,he⟩ ⟨mem_univ i,hf⟩ hef)
  · intro v hv e he
    have h := hm.inc_iff (i,v) ⟨mem_univ i,hv⟩ (i,e) ⟨mem_univ i,he⟩
    simp only [graphCopies_inc,true_and] at h
    change H.Inc e v ↔ ∃ x∈ηv (i,v), (G.induce B).Inc (ηe (i,e)) x
    simpa only [hinc e he] using h
  · intro v hv e he
    have h := hm.isLoopAt_iff (i,v) ⟨mem_univ i,hv⟩ (i,e) ⟨mem_univ i,he⟩
    simp only [graphCopies_isLoopAt,true_and] at h
    change H.IsLoopAt e v ↔ ∀ x, (G.induce B).Inc (ηe (i,e)) x → x∈ηv (i,v)
    simpa only [hinc e he] using h
  · intro v hv
    obtain ⟨K,hK,hKV,hconn⟩ := hm.connected (i,v) ⟨mem_univ i,hv⟩
    have hKB : V(K)⊆B := fun x hx ↦ mem_biUnion hv (hKV ▸ hx)
    have hKG : K≤G := hK.trans Graph.deleteEdges_le
    refine ⟨K,⟨hKB,?_⟩,hKV,hconn⟩
    intro f x y hf
    refine ⟨⟨hKG.isLink_mono hf,hKB hf.left_mem,hKB hf.right_mem⟩,?_⟩
    rintro ⟨e,he,hef⟩
    exact (hK.isLink_mono hf).2 ⟨(i,e),⟨mem_univ i,he⟩,hef⟩

/-- The unions of branches belonging to different copies are disjoint. -/
theorem copy_model_branches_disjoint {α β α' β' : Type*} {k : ℕ}
    {H : Graph α' β'} {G : Graph α β}
    {ηv : Fin k × α' → Set α} {ηe : Fin k × β' → β}
    (hm : IsMinorModel (graphCopies k H) G ηv ηe) :
    Pairwise (fun i j ↦ Disjoint (⋃ v∈V(H),ηv (i,v)) (⋃ v∈V(H),ηv (j,v))) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hx hy
  obtain ⟨u,hu,hxu⟩ := mem_iUnion₂.mp hx
  obtain ⟨v,hv,hxv⟩ := mem_iUnion₂.mp hy
  exact Set.disjoint_left.mp
    (hm.vertex_disjoint (i,u) ⟨mem_univ i,hu⟩ (j,v) ⟨mem_univ j,hv⟩
      (fun h ↦ hij (congrArg Prod.fst h))) hxu hxv

end GraphMinor.GM05
