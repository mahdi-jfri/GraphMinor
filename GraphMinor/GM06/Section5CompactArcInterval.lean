module

public import GraphMinor.Surface.CrossCut
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-!
# A smaller arc around a compact part of a corner

In the seed-disc construction for VI (5.5), page 130, the drawing
on the rim is compact and lies away from the ends of a corner arc.
Pull it back to the unit interval. Its least and greatest parameters
lie strictly between the ends. Slightly enlarge that parameter
interval to obtain a closed subarc still inside the corner.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A nonempty compact subset of an arc, missing both ends, lies
strictly inside a smaller closed parameter interval. -/
theorem exists_closed_subinterval_enclosing_compact_arc_part
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {a : unitInterval → X} (ha : IsArcMap a)
    {K : Set X} (hK : IsCompact K) (hne : K.Nonempty)
    (hKa : K ⊆ range a) (h0 : a 0 ∉ K) (h1 : a 1 ∉ K) :
    ∃ l r : unitInterval, 0 < l ∧ l < r ∧ r < 1 ∧
      K ⊆ a '' Ioo l r ∧ a '' Icc l r ⊆ range a \ {a 0, a 1} := by
  let T := a ⁻¹' K
  have hTc : IsCompact T := (hK.isClosed.preimage ha.1).isCompact
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨t, rfl⟩ := hKa hx
    exact ⟨t, hx⟩
  obtain ⟨u, hu, hmin⟩ := hTc.exists_isLeast hTne
  obtain ⟨v, hv, hmax⟩ := hTc.exists_isGreatest hTne
  have hu0 : (0 : ℝ) < u := by
    have he : u ≠ 0 := fun he => h0 (he ▸ hu)
    exact unitInterval.pos_iff_ne_zero.mpr he
  have hv1 : (v : ℝ) < 1 := by
    have he : v ≠ 1 := fun he => h1 (he ▸ hv)
    exact lt_of_le_of_ne v.2.2 (fun he' => he (Subtype.ext he'))
  have huv : (u : ℝ) ≤ v := hmin hv
  let l : unitInterval := ⟨(u : ℝ) / 2, by constructor <;> linarith [u.2.2]⟩
  let r : unitInterval := ⟨((v : ℝ) + 1) / 2, by constructor <;> linarith [v.2.1]⟩
  have hl0 : 0 < l := by change (0 : ℝ) < (u : ℝ) / 2; linarith
  have hlu : l < u := by change (u : ℝ) / 2 < u; linarith
  have hvr : v < r := by change (v : ℝ) < ((v : ℝ) + 1) / 2; linarith
  have hr1 : r < 1 := by change ((v : ℝ) + 1) / 2 < 1; linarith
  refine ⟨l, r, hl0, hlu.trans_le ((hmin hv).trans hvr.le), hr1, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, rfl⟩ := hKa hx
    exact ⟨t, ⟨hlu.trans_le (hmin hx), (hmax hx).trans_lt hvr⟩, rfl⟩
  · rintro x ⟨t, ht, rfl⟩
    refine ⟨⟨t, rfl⟩, ?_⟩
    rintro (he | he)
    · have ht0 : t = 0 := ha.2 he
      exact (hl0.trans_le ht.1).ne' ht0
    · have ht1 : t = 1 := ha.2 he
      exact (ht.2.trans_lt hr1).ne ht1

end GraphMinor.GM06
