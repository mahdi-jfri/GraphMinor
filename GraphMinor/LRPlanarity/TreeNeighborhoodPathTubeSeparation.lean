module

public import GraphMinor.LRPlanarity.TreeNeighborhoodPathTube
public import GraphMinor.HP25.Embedding
import GraphMinor.LRPlanarity.TreeNeighborhoodPathTubeInterior

/-!
# Separation of tubes on different original tree edges

Part IV, Section 7b of the planarity note keeps distinct original edges
separate after subdivision. Their internal vertices are not on the other
edge, and they share no straight piece. The individual strip and polygon
separation conditions then imply that their tubes are disjoint, even when
the original edges have a common endpoint polygon.
-/

public section
namespace GraphMinor.LRPlanarity

open Set SimpleGraph

/-- Tubes on two subdivision paths are disjoint when their internal
vertices avoid the other path and their unordered straight pieces differ. -/
theorem walkTubes_disjoint {V : Type*} {G : SimpleGraph V}
    (P : V → Set ℂ) (R : V → V → Set ℂ)
    (hPsep : Pairwise (fun u v => Disjoint (P u) (P v)))
    (hRsep : ∀ u v, G.Adj u v → ∀ z t, G.Adj z t →
      s(u,v) ≠ s(z,t) → Disjoint (R u v) (R z t))
    (haway : ∀ u v, G.Adj u v → ∀ z, z ≠ u → z ≠ v → Disjoint (R u v) (P z))
    {u v z t : V} (w : G.Walk u v) (q : G.Walk z t)
    (hwq : ∀ y ∈ w.support.tail.dropLast, y ∉ q.support)
    (hqw : ∀ y ∈ q.support.tail.dropLast, y ∉ w.support)
    (hedges : ∀ e ∈ w.darts, ∀ f ∈ q.darts, s(e.fst,e.snd) ≠ s(f.fst,f.snd)) :
    Disjoint (walkTube P R w) (walkTube P R q) := by
  rw [Set.disjoint_left]
  intro x hxw hxq
  rcases (mem_walkTube_iff P R w x).mp hxw with ⟨e, he, hxe⟩ | ⟨y, hy, hxy⟩
  · rcases (mem_walkTube_iff P R q x).mp hxq with ⟨f, hf, hxf⟩ | ⟨y, hy, hxy⟩
    · exact Set.disjoint_left.mp (hRsep e.fst e.snd e.adj f.fst f.snd f.adj
        (hedges e he f hf)) hxe hxf
    · obtain ⟨hfst, hsnd⟩ := walk_dart_ends_mem_support w he
      have hye : y ≠ e.fst := fun h => hqw y hy (h.symm ▸ hfst)
      have hye' : y ≠ e.snd := fun h => hqw y hy (h.symm ▸ hsnd)
      exact Set.disjoint_left.mp (haway e.fst e.snd e.adj y hye hye') hxe hxy
  · rcases (mem_walkTube_iff P R q x).mp hxq with ⟨f, hf, hxf⟩ | ⟨y', hy', hxy'⟩
    · obtain ⟨hfst, hsnd⟩ := walk_dart_ends_mem_support q hf
      have hyf : y ≠ f.fst := fun h => hwq y hy (h.symm ▸ hfst)
      have hyf' : y ≠ f.snd := fun h => hwq y hy (h.symm ▸ hsnd)
      exact Set.disjoint_left.mp (haway f.fst f.snd f.adj y hyf hyf') hxf hxy
    · have hyy' : y ≠ y' := fun h => hwq y hy (h.symm ▸ walk_internal_mem_support q hy')
      exact Set.disjoint_left.mp (hPsep hyy') hxy hxy'

/-- A tree tube misses another drawn path when their straight pieces differ
and its internal vertices are absent from the other path. This applies to
an original cotree edge and an original tree-edge tube. -/
theorem walkTube_disjoint_pathImage {V : Type*} {G : SimpleGraph V}
    (drawing : HP25.PlaneEmbedding G univ) (P : V → Set ℂ) (R : V → V → Set ℂ)
    (hother : ∀ u v, G.Adj u v → ∀ z t, G.Adj z t → s(u,v) ≠ s(z,t) →
      Disjoint (R u v) (drawing.line z t))
    (haway : ∀ z u v, G.Adj u v → u ≠ z → v ≠ z → Disjoint (P z) (drawing.line u v))
    {u v z t : V} (w : G.Walk u v) (q : G.Walk z t)
    (hinternal : ∀ y ∈ w.support.tail.dropLast, y ∉ q.support)
    (hedges : ∀ e ∈ w.darts, ∀ f ∈ q.darts, s(e.fst,e.snd) ≠ s(f.fst,f.snd)) :
    Disjoint (walkTube P R w) (drawing.pathImage q.support) := by
  rw [Set.disjoint_left]
  intro x hxw hxq
  rw [walk_pathImage_eq_dart_union] at hxq
  obtain ⟨f, hf'⟩ := mem_iUnion.mp hxq
  obtain ⟨hf, hxf⟩ := mem_iUnion.mp hf'
  rcases (mem_walkTube_iff P R w x).mp hxw with ⟨e, he, hxe⟩ | ⟨y, hy, hxy⟩
  · exact Set.disjoint_left.mp (hother e.fst e.snd e.adj f.fst f.snd f.adj
      (hedges e he f hf)) hxe hxf
  · obtain ⟨hfst, hsnd⟩ := walk_dart_ends_mem_support q hf
    have hfy : f.fst ≠ y := fun h => hinternal y hy (h ▸ hfst)
    have hsy : f.snd ≠ y := fun h => hinternal y hy (h ▸ hsnd)
    exact Set.disjoint_left.mp (haway y f.fst f.snd f.adj hfy hsy) hxy hxf

end GraphMinor.LRPlanarity
