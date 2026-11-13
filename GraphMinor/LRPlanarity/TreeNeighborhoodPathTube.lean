module

public import GraphMinor.Surface.Defs
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Tubes along subdivided tree edges

Part IV, Section 7b of the planarity note subdivides the tree at its bends.
For an original tree edge, its tube consists of the strips on its straight
pieces and the polygons at its internal subdivision vertices. The original
endpoint polygons are excluded. This file records that union and its
recursion along the subdivision path.
-/

public section
namespace GraphMinor.LRPlanarity

open Set SimpleGraph

/-- Part IV, Section 7b: the tube on a subdivision path, excluding its two
endpoint polygons. -/
@[expose] def walkTube {V : Type*} {G : SimpleGraph V} (P : V → Set ℂ)
    (R : V → V → Set ℂ) {u v : V} (w : G.Walk u v) : Set ℂ :=
  (⋃ e ∈ w.darts, R e.fst e.snd) ∪ ⋃ z ∈ w.support.tail.dropLast, P z

/-- Tube membership comes either from a path strip or an internal polygon. -/
theorem mem_walkTube_iff {V : Type*} {G : SimpleGraph V} (P : V → Set ℂ)
    (R : V → V → Set ℂ) {u v : V} (w : G.Walk u v) (x : ℂ) :
    x ∈ walkTube P R w ↔
      (∃ e ∈ w.darts, x ∈ R e.fst e.snd) ∨
      ∃ z ∈ w.support.tail.dropLast, x ∈ P z := by
  simp only [walkTube, mem_union, mem_iUnion, exists_prop]

/-- A path of length zero has no tube. -/
theorem walkTube_nil {V : Type*} {G : SimpleGraph V} (P : V → Set ℂ)
    (R : V → V → Set ℂ) (u : V) : walkTube P R (Walk.nil : G.Walk u u) = ∅ := by
  ext x
  simp [walkTube]

/-- The tube on one straight piece is its strip. -/
theorem walkTube_single {V : Type*} {G : SimpleGraph V} (P : V → Set ℂ)
    (R : V → V → Set ℂ) {u v : V} (h : G.Adj u v) :
    walkTube P R (Walk.cons h Walk.nil) = R u v := by
  ext x
  simp [walkTube]

/-- Adding a straight piece before a nonempty subdivision path adds its
strip and the new bend polygon. -/
theorem walkTube_cons_cons {V : Type*} {G : SimpleGraph V} (P : V → Set ℂ)
    (R : V → V → Set ℂ) {u v z t : V} (huv : G.Adj u v) (hvz : G.Adj v z)
    (w : G.Walk z t) :
    walkTube P R (Walk.cons huv (Walk.cons hvz w)) =
      R u v ∪ P v ∪ walkTube P R (Walk.cons hvz w) := by
  ext x
  simp [walkTube, List.dropLast_cons_of_ne_nil w.support_ne_nil]
  aesop

/-- Both ends of every path dart occur among its vertices. -/
theorem walk_dart_ends_mem_support {V : Type*} {G : SimpleGraph V} {u v : V}
    (w : G.Walk u v) {e : G.Dart} (he : e ∈ w.darts) :
    e.fst ∈ w.support ∧ e.snd ∈ w.support := by
  refine ⟨w.dart_fst_mem_support_of_mem_darts he, ?_⟩
  have hm : e.snd ∈ w.darts.map (·.snd) := List.mem_map.mpr ⟨e, he, rfl⟩
  rw [w.map_snd_darts] at hm
  exact List.mem_of_mem_tail hm

/-- Internal subdivision vertices occur in the path support. -/
theorem walk_internal_mem_support {V : Type*} {G : SimpleGraph V} {u v z : V}
    (w : G.Walk u v) (hz : z ∈ w.support.tail.dropLast) : z ∈ w.support :=
  List.mem_of_mem_tail (List.mem_of_mem_dropLast hz)

/-- A simple path's start is not an internal subdivision vertex. -/
theorem path_start_not_mem_internal {V : Type*} {G : SimpleGraph V} {u v : V}
    {w : G.Walk u v} (hw : w.IsPath) : u ∉ w.support.tail.dropLast := by
  have hnd : (u :: w.support.tail).Nodup := w.cons_tail_support.symm ▸ hw.support_nodup
  exact fun h => hnd.notMem (List.mem_of_mem_dropLast h)

private theorem path_end_not_mem_dropLast {V : Type*} {G : SimpleGraph V} {u v : V}
    {w : G.Walk u v} (hw : w.IsPath) : v ∉ w.support.dropLast := by
  have he : w.support.dropLast ++ [v] = w.support := by
    simpa only [w.getLast_support] using List.dropLast_append_getLast w.support_ne_nil
  have hnd : (w.support.dropLast ++ [v]).Nodup := he.symm ▸ hw.support_nodup
  intro hv
  exact List.disjoint_left.mp hnd.disjoint hv (List.mem_singleton_self v)

/-- A simple path's end is not an internal subdivision vertex. -/
theorem path_end_not_mem_internal {V : Type*} {G : SimpleGraph V} {u v : V}
    {w : G.Walk u v} (hw : w.IsPath) : v ∉ w.support.tail.dropLast := by
  cases w with
  | nil => simp
  | cons h q => exact path_end_not_mem_dropLast hw.of_cons

/-- A tube misses every vertex polygon not visited by its path, when
strips avoid nonincident polygons and vertex polygons are disjoint. -/
theorem walkTube_disjoint_polygon {V : Type*} {G : SimpleGraph V}
    (P : V → Set ℂ) (R : V → V → Set ℂ)
    (hPsep : Pairwise (fun u v => Disjoint (P u) (P v)))
    (haway : ∀ u v, G.Adj u v → ∀ z, z ≠ u → z ≠ v → Disjoint (R u v) (P z))
    {u v z : V} (w : G.Walk u v) (hz : z ∉ w.support) :
    Disjoint (walkTube P R w) (P z) := by
  rw [Set.disjoint_left]
  intro x hx hxz
  rcases (mem_walkTube_iff P R w x).mp hx with ⟨e, he, hxe⟩ | ⟨y, hy, hxy⟩
  · obtain ⟨hfst, hsnd⟩ := walk_dart_ends_mem_support w he
    exact Set.disjoint_left.mp (haway e.fst e.snd e.adj z
      (fun h => hz (h ▸ hfst)) (fun h => hz (h ▸ hsnd))) hxe hxz
  · have hyz : y ≠ z := fun h => hz (h ▸ walk_internal_mem_support w hy)
    exact Set.disjoint_left.mp (hPsep hyz) hxy hxz

/-- A strip from a new vertex to the start of a simple path misses the
path tube. Its edge differs from every path edge, and its endpoints are
not internal vertices of that path. -/
theorem walkTube_disjoint_preceding_strip {V : Type*} {G : SimpleGraph V}
    (P : V → Set ℂ) (R : V → V → Set ℂ)
    (hRsep : ∀ u v, G.Adj u v → ∀ z t, G.Adj z t →
      s(u,v) ≠ s(z,t) → Disjoint (R u v) (R z t))
    (haway : ∀ u v, G.Adj u v → ∀ z, z ≠ u → z ≠ v → Disjoint (R u v) (P z))
    {u v t : V} (huv : G.Adj u v) (w : G.Walk v t) (hw : w.IsPath)
    (hu : u ∉ w.support) : Disjoint (walkTube P R w) (R u v) := by
  rw [Set.disjoint_left]
  intro x hx hxR
  rcases (mem_walkTube_iff P R w x).mp hx with ⟨e, he, hxe⟩ | ⟨z, hz, hxz⟩
  · obtain ⟨hfst, hsnd⟩ := walk_dart_ends_mem_support w he
    have hne : s(e.fst,e.snd) ≠ s(u,v) := by
      intro heq
      rcases Sym2.eq_iff.mp heq with ⟨hs, _⟩ | ⟨_, ht⟩
      · exact hu (hs ▸ hfst)
      · exact hu (ht ▸ hsnd)
    exact Set.disjoint_left.mp (hRsep e.fst e.snd e.adj u v huv hne) hxe hxR
  · have hzu : z ≠ u := fun he => hu (he ▸ walk_internal_mem_support w hz)
    have hzv : z ≠ v := fun he => path_start_not_mem_internal hw (he ▸ hz)
    exact Set.disjoint_left.mp (haway u v huv z hzu hzv) hxR hxz

end GraphMinor.LRPlanarity
