module

public import GraphMinor.Surface.ArcTools
public import Mathlib.Analysis.Convex.Segment
import GraphMinor.LRPlanarity.PolygonalizationSegmentGraph
import GraphMinor.LRPlanarity.PolygonalizationArrangementPaths
public import GraphMinor.HP25.Embedding
import GraphMinor.Surface.Lunes

/-!
# Removing self-intersections from a polygonal walk

Part IV, Section 7a of the planarity note forms the finite segment
arrangement and takes a simple graph path between the original endpoints.
The path image is a line and is still a finite union of straight segments.
It stays inside the original polygonal walk.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7a: the geometric image of a simple graph path with
distinct ends is a line between its endpoint points. -/
theorem isLine_walk_pathImage {V : Type*} {G : SimpleGraph V}
    (φ : HP25.PlaneEmbedding G univ) {u v : V} (huv : u ≠ v)
    (w : G.Walk u v) (hw : w.IsPath) :
    IsLineWithEnds (φ.pathImage w.support) (φ.pt u) (φ.pt v) := by
  have hlast : w.support.getLast? = some v := by
    rw [List.getLast?_eq_some_getLast w.support_ne_nil, w.getLast_support]
  have htail : w.support.tail ≠ [] := by
    intro ht
    rw [← w.cons_tail_support, ht] at hlast
    exact huv (by simpa using hlast)
  have hpath : HP25.IsPathList G univ (u :: w.support.tail) := by
    rw [w.cons_tail_support]
    exact ⟨hw.support_nodup, w.isChain_adj_support, fun _ _ => mem_univ _⟩
  have hend : w.support.tail.getLast htail = v := by
    rw [← w.cons_tail_support, List.getLast?_cons,
      List.getLast?_eq_some_getLast htail] at hlast
    exact Option.some.inj hlast
  simpa only [w.cons_tail_support, hend] using φ.isLine_pathImage htail hpath

/-- Part IV, Section 7a: a polygonal walk with different endpoints contains
a simple polygonal arc between the same endpoints. The proof uses the
finite segment arrangement and a simple path in its graph. -/
theorem polygonal_walk_contains_polygonal_arc {n : ℕ} (hn : 0 < n)
    (p : Fin (n + 1) → ℂ) (hne : p 0 ≠ p (Fin.last n)) :
    ∃ L : Set ℂ, IsLineWithEnds L (p 0) (p (Fin.last n)) ∧
      L ⊆ ⋃ i : Fin n, segment ℝ (p i.castSucc) (p i.succ) ∧
      ∃ pieces : Finset (ℂ × ℂ), L = ⋃ q ∈ pieces, segment ℝ q.1 q.2 := by
  classical
  let pieces := Finset.univ.image (fun i : Fin n => (p i.castSucc, p i.succ))
  have hmem : ∀ i : Fin n, (p i.castSucc, p i.succ) ∈ pieces :=
    fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨V, E, hG, hgr, hends, hstraight⟩ := exists_straight_segment_arrangement pieces
  have hpV : ∀ i, p i ∈ V := by
    intro i
    by_cases hi : i.val < n
    · let j : Fin n := ⟨i.val, hi⟩
      have he : j.castSucc = i := Fin.ext rfl
      rw [← he]
      exact (hends _ (hmem j)).1
    · have hin : i.val = n :=
        le_antisymm (Nat.le_of_lt_succ i.isLt) (Nat.le_of_not_gt hi)
      let j : Fin n := ⟨n - 1, Nat.sub_lt hn (by decide)⟩
      have he : j.succ = i := by
        apply Fin.ext
        exact (Nat.sub_add_cancel hn).trans hin.symm
      rw [← he]
      exact (hends _ (hmem j)).2
  let v : Fin (n + 1) → V := fun i => ⟨p i, hpV i⟩
  let G := segmentArrangementGraph V E
  have hsegsub : ∀ i : Fin n, segment ℝ (p i.castSucc) (p i.succ) ⊆ gr V E := by
    intro i x hx
    rw [hgr]
    exact mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨hmem i, hx⟩⟩
  have hstep : ∀ i : Fin n, G.Reachable (v i.castSucc) (v i.succ) := by
    intro i
    by_cases he : p i.castSucc = p i.succ
    · have hv : v i.castSucc = v i.succ := Subtype.ext he
      rw [hv]
    · exact segment_arrangement_reachable hG hstraight (isLineWithEnds_segment he)
        (hpV _) (hpV _) (hsegsub i)
  have hreach : ∀ i, G.Reachable (v 0) (v i) := by
    intro i
    induction i using Fin.induction with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ i ih => exact ih.trans (hstep i)
  obtain ⟨w, hw⟩ := (hreach (Fin.last n)).exists_isPath
  let φ := segmentArrangementEmbedding hG
  let L := φ.pathImage w.support
  have huv : v 0 ≠ v (Fin.last n) := fun he => hne (congrArg Subtype.val he)
  have hL : IsLineWithEnds L (p 0) (p (Fin.last n)) := isLine_walk_pathImage φ huv w hw
  have hLE : L ⊆ gr V E := by
    intro x hx
    obtain ⟨e, he⟩ := mem_iUnion.mp hx
    obtain ⟨he, hxe⟩ := mem_iUnion.mp he
    have hadj := HP25.isChain_iff_zip.mp w.isChain_adj_support e he
    exact Or.inr ⟨segment ℝ e.1.val e.2.val, hadj.2, hxe⟩
  have hsub : L ⊆ ⋃ i : Fin n, segment ℝ (p i.castSucc) (p i.succ) := by
    intro x hx
    have hm := hLE hx
    rw [hgr] at hm
    obtain ⟨q, hq⟩ := mem_iUnion.mp hm
    obtain ⟨hq, hxq⟩ := mem_iUnion.mp hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact mem_iUnion.mpr ⟨i, hxq⟩
  let output := ((w.support.zip w.support.tail).map
    (fun e => (e.1.val, e.2.val))).toFinset
  refine ⟨L, hL, hsub, output, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨e, he⟩ := mem_iUnion.mp hx
    obtain ⟨he, hxe⟩ := mem_iUnion.mp he
    exact mem_iUnion.mpr ⟨(e.1.val, e.2.val), mem_iUnion.mpr
      ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, he, rfl⟩), hxe⟩⟩
  · intro hx
    obtain ⟨q, hq⟩ := mem_iUnion.mp hx
    obtain ⟨hq, hxq⟩ := mem_iUnion.mp hq
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨he, hxq⟩⟩

end GraphMinor.LRPlanarity
