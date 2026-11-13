module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5GapEdge
import GraphMinor.GM11.Walks
import Mathlib.Data.Set.Finite.Lemmas

/-!
# The first drawing edge along an injective arc

The preimage of the finite vertex set under an injective curve is
finite. Choose its least positive parameter, which exists when the
curve ends at a vertex. The preceding open arc misses every vertex,
so it stays in one drawing edge. Density puts the arc's initial
point and that first new vertex in the edge closure. This supplies
the initial boundary edge used to exclude a left-seam return in
the one-path proof of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface
universe u

/-- An injective arc inside a finite drawing and ending at a vertex
has an initial drawing edge whose closure reaches its first positive
vertex parameter. That edge meets the arc itself. -/
theorem exists_first_edge_of_injective_curve
    {S : Type u} [TopologicalSpace S] [T2Space S] (F : Drawing S)
    (f : Curve S) (hf : Function.Injective f) (hFU : range f ⊆ F.U) (h1 : f 1 ∈ F.V) :
    ∃ τ : unitInterval, 0 < τ ∧ f τ ∈ F.V ∧
      ∃ e ∈ F.E, f 0 ∈ closure e ∧ f τ ∈ closure e ∧ (e ∩ range f).Nonempty := by
  classical
  let T := {t : unitInterval | 0 < t ∧ f t ∈ F.V}
  have hfin : T.Finite :=
    (Set.Finite.preimage hf.injOn F.finite_V).subset (fun _ ht => ht.2)
  have hne : T.Nonempty := ⟨1, zero_lt_one, h1⟩
  obtain ⟨τ, hτ, hmin⟩ := Set.exists_min_image T id hfin hne
  let g : Curve S := ⟨fun t => f (t * τ), f.continuous.comp (by fun_prop)⟩
  have hg0 : g 0 = f 0 := by change f (0 * τ) = f 0; rw [zero_mul]
  have hg1 : g 1 = f τ := by change f (1 * τ) = f τ; rw [one_mul]
  have hnotV {t : unitInterval} (ht : t ∈ Ioo 0 1) : g t ∉ F.V := by
    intro hV
    have hpos : 0 < t * τ := by
      change (0 : ℝ) < (t : ℝ) * (τ : ℝ)
      exact mul_pos (show (0 : ℝ) < (t : ℝ) from ht.1)
        (show (0 : ℝ) < (τ : ℝ) from hτ.1)
    have hlt : t * τ < τ := by
      change (t : ℝ) * (τ : ℝ) < (τ : ℝ)
      simpa only [one_mul] using mul_lt_mul_of_pos_right
        (show (t : ℝ) < 1 from ht.2) (show (0 : ℝ) < (τ : ℝ) from hτ.1)
    exact not_le_of_gt hlt (hmin (t * τ) ⟨hpos, hV⟩)
  have hgU : range g ⊆ F.U := by
    rintro x ⟨t, rfl⟩
    exact hFU (mem_range_self (t * τ))
  have hgap : g '' Ioo 0 1 ⊆ F.U \ F.V := by
    rintro x ⟨t, ht, rfl⟩
    exact ⟨hgU (mem_range_self t), hnotV ht⟩
  let t : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have ht : t ∈ Ioo (0 : unitInterval) 1 := by
    constructor
    · change (0 : ℝ) < 1 / 2
      norm_num
    · change (1 / 2 : ℝ) < 1
      norm_num
  obtain ⟨e, he, hge⟩ := F.exists_edge_of_mem (hgU (mem_range_self t)) (hnotV ht)
  obtain ⟨_, hcl⟩ := arc_interior_subset_edge he hgap ⟨g t, hge, t, ht, rfl⟩
  refine ⟨τ, hτ.1, hτ.2, e, he, ?_, ?_, ?_⟩
  · rw [← hg0]
    exact hcl (mem_range_self 0)
  · rw [← hg1]
    exact hcl (mem_range_self 1)
  · exact ⟨g t, hge, t * τ, rfl⟩

end GraphMinor.GM06
