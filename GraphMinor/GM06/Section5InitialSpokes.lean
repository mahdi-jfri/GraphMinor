module

public import GraphMinor.GM11.Corners
import GraphMinor.GM11.Walks

/-!
# A neighbourhood covered by the initial edge spokes

For the sector comparison in VI (5.1), page 129, a sufficiently
small neighbourhood of a vertex meets the drawing only at that
vertex and on its incident initial spokes. Remove the other vertices
and the compact middle portions of every edge. Each remaining edge
point has parameter before the middle from one of the ends at the
chosen vertex.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- Near a drawing vertex, every other drawing point lies on one of
the initial half-edge spokes at that vertex. -/
theorem exists_nhds_drawing_initial_spokes
    {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}
    {γ : Set S → I → S} (hγ : EdgePar Γ γ) {c : S} (hc : c ∈ Γ.V) :
    ∃ N : Set S, IsOpen N ∧ c ∈ N ∧
      ∀ x ∈ N ∩ Γ.U, x = c ∨
        ∃ j : halfEdges Γ γ c, ∃ t : I, 0 < t ∧ spoke γ j.1 t = x := by
  classical
  let mid : I := ⟨1 / 2, by constructor <;> norm_num⟩
  let T : Set S → Set I := fun e =>
    {t | (γ e 0 = c → mid ≤ t) ∧ (γ e 1 = c → t ≤ mid)}
  have hT (e : Set S) : IsClosed (T e) := by
    apply IsClosed.inter
    · by_cases h : γ e 0 = c
      · simp only [h, true_implies]
        exact isClosed_le continuous_const continuous_id
      · simp only [h, false_implies]
        change IsClosed (univ : Set I)
        exact isClosed_univ
    · by_cases h : γ e 1 = c
      · simp only [h, true_implies]
        exact isClosed_le continuous_id continuous_const
      · simp only [h, false_implies]
        change IsClosed (univ : Set I)
        exact isClosed_univ
  let K := (Γ.V \ {c}) ∪ ⋃ e ∈ Γ.E, γ e '' T e
  have hK : IsClosed K := (Γ.finite_V.subset sdiff_subset).isClosed.union
    (Γ.finite_edges.isClosed_biUnion fun e he => ((hT e).isCompact.image (hγ.cont e he)).isClosed)
  have hcK : c ∉ K := by
    rintro (hcV | hcE)
    · exact hcV.2 rfl
    · obtain ⟨e, he, t, ht, htc⟩ := mem_iUnion₂.mp hcE
      by_cases ht0 : t = 0
      · have hh := ht.1 (ht0 ▸ htc)
        rw [ht0] at hh
        change (1 / 2 : ℝ) ≤ 0 at hh
        norm_num at hh
      · by_cases ht1 : t = 1
        · have hh := ht.2 (ht1 ▸ htc)
          rw [ht1] at hh
          change (1 : ℝ) ≤ 1 / 2 at hh
          norm_num at hh
        · have htI : t ∈ Ioo (0 : I) 1 :=
            ⟨unitInterval.pos_iff_ne_zero.mpr ht0, unitInterval.lt_one_iff_ne_one.mpr ht1⟩
          have hce : c ∈ e := by rw [← hγ.image e he]; exact ⟨t, htI, htc⟩
          exact (he.2.1 hce).2 hc
  refine ⟨Kᶜ, hK.isOpen_compl, hcK, ?_⟩
  rintro x ⟨hxK, hxU⟩
  by_cases hxc : x = c
  · exact Or.inl hxc
  · have hxV : x ∉ Γ.V := fun hxV => hxK (Or.inl ⟨hxV, hxc⟩)
    obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem hxU hxV
    obtain ⟨t, ht, htx⟩ := hγ.image e he ▸ hxe
    have htNot : t ∉ T e := fun htT => hxK (Or.inr (mem_iUnion₂.mpr
      ⟨e, he, ⟨t, htT, htx⟩⟩))
    apply Or.inr
    by_cases hlow : t < mid
    · have he0 : γ e 0 = c := by
        by_contra hn
        exact htNot ⟨fun h => (hn h).elim, fun _ => hlow.le⟩
      let q : I := ⟨2 * (t : ℝ), by
        constructor
        · exact mul_nonneg (by norm_num) t.2.1
        · change (t : ℝ) < 1 / 2 at hlow
          linarith only [hlow]⟩
      refine ⟨⟨(e, false), he, he0⟩, q, ?_, ?_⟩
      · change (0 : ℝ) < 2 * (t : ℝ)
        exact mul_pos (by norm_num) ht.1
      · change γ e (halfPar false q) = x
        have hq : halfPar false q = t := by
          apply Subtype.ext
          change (2 * (t : ℝ)) / 2 = t
          ring
        rw [hq]
        exact htx
    · have hle : mid ≤ t := le_of_not_gt hlow
      have he1 : γ e 1 = c := by
        by_contra hn
        exact htNot ⟨fun _ => hle, fun h => (hn h).elim⟩
      have hhigh : mid < t := by
        by_contra hn
        exact htNot ⟨fun _ => hle, fun _ => le_of_not_gt hn⟩
      let q : I := ⟨2 - 2 * (t : ℝ), by
        constructor
        · linarith only [t.2.2]
        · change (1 / 2 : ℝ) < t at hhigh
          linarith only [hhigh]⟩
      refine ⟨⟨(e, true), he, he1⟩, q, ?_, ?_⟩
      · change (0 : ℝ) < 2 - 2 * (t : ℝ)
        have ht1 : (t : ℝ) < 1 := ht.2
        linarith only [ht1]
      · change γ e (halfPar true q) = x
        have hq : halfPar true q = t := by
          apply Subtype.ext
          change 1 - (2 - 2 * (t : ℝ)) / 2 = t
          ring
        rw [hq]
        exact htx

end GraphMinor.GM06
