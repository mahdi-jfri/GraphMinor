module

public import GraphMinor.GM12.Section3ArcPieces
public import GraphMinor.Surface.SurfaceGraph

/-!
# Adding a retained original subarc to a finite graph

For the homotopic finite-graph reduction used by XII (3.1), page 245,
the graph carrier is a fixed set together with finitely many segments
of one injective original arc. A new segment has finite contact with
the fixed set. The interval calculation proves finite connectedness
off the graph. Add the two ends as vertices and apply the proved
finite-graph path extension. A degenerate segment is just one point.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A retained subarc with finite contact with the fixed carrier can
be added to a finite graph already consisting of that carrier and
finitely many segments of the same original injective arc. -/
theorem exists_graph_add_subarc_of_finite_contacts
    {S ι : Type*} [TopologicalSpace S] [T2Space S]
    {p : unitInterval → S} (hp : IsArcMap p) {F V : Set S} {E : Set (Set S)}
    (hG : IsGraph V E) (J : Finset ι) (a b : ι → unitInterval)
    (hgr : gr V E = F ∪ ⋃ i ∈ J, p '' Icc (a i) (b i))
    (r s : unitInterval) (hF : ((p '' Icc r s) ∩ F).Finite) :
    ∃ V' E', V ⊆ V' ∧ IsGraph V' E' ∧ gr V' E' = gr V E ∪ p '' Icc r s := by
  classical
  by_cases hsr : s < r
  · refine ⟨V, E, subset_rfl, hG, ?_⟩
    rw [Icc_eq_empty_of_lt hsr, image_empty, union_empty]
  by_cases hrs : r = s
  · subst s
    obtain ⟨E', hG', hgr', _⟩ := hG.add_point (p r)
    refine ⟨insert (p r) V, E', subset_insert _ _, hG', ?_⟩
    rw [Icc_self, image_singleton, union_singleton]
    exact hgr'
  have hrs' : r < s := lt_of_le_of_ne (le_of_not_gt hsr) hrs
  let c := subArc p r s
  have hc : IsArcMap c := hp.sub hrs
  have hcr : range c = p '' Icc r s := range_subArc p hrs'.le
  have hpr : p r ∈ range c := by
    rw [hcr]
    exact ⟨r, ⟨le_rfl, hrs'.le⟩, rfl⟩
  have hps : p s ∈ range c := by
    rw [hcr]
    exact ⟨s, ⟨hrs'.le, le_rfl⟩, rfl⟩
  obtain ⟨E₁, hG₁, hgr₁, _⟩ := hG.add_point (p r)
  obtain ⟨E₂, hG₂, hgr₂, _⟩ := hG₁.add_point (p s)
  let V₂ := insert (p s) (insert (p r) V)
  let F' := insert (p s) (insert (p r) F)
  have hgr₂' : gr V₂ E₂ = F' ∪ ⋃ i ∈ J, p '' Icc (a i) (b i) := by
    rw [hgr₂, hgr₁, hgr]
    simp only [F', insert_union]
  have hF' : ((p '' Icc r s) ∩ F').Finite := by
    have hrL : p r ∈ p '' Icc r s := hcr ▸ hpr
    have hsL : p s ∈ p '' Icc r s := hcr ▸ hps
    change ((p '' Icc r s) ∩ insert (p s) (insert (p r) F)).Finite
    rw [inter_insert_of_mem hsL, inter_insert_of_mem hrL]
    exact (hF.insert (p r)).insert (p s)
  have hfin : FinConn (range c \ gr V₂ E₂) := by
    rw [hcr, hgr₂']
    exact finConn_subarc_diff_set_and_segments hp r s hF' J a b
  have hc0 : c 0 ∈ gr V₂ E₂ := by
    change subArc p r s 0 ∈ gr V₂ E₂
    rw [subArc_zero, hgr₂, hgr₁]
    exact Or.inr (Or.inl rfl)
  have hc1 : c 1 ∈ gr V₂ E₂ := by
    change subArc p r s 1 ∈ gr V₂ E₂
    rw [subArc_one, hgr₂]
    exact Or.inl rfl
  obtain ⟨K, hK, hpre, hKeq⟩ := hfin
  obtain ⟨V₃, E₃, hV₂₃, hG₃, hgr₃, _⟩ :=
    IsGraph.add_path hc K.ncard V₂ E₂ K hG₂ hc0 hc1 hK rfl hpre hKeq
  refine ⟨V₃, E₃, (subset_insert (p r) V).trans ((subset_insert (p s) _).trans hV₂₃), hG₃, ?_⟩
  have hprG : p r ∈ gr V E ∪ range c := Or.inr hpr
  have hpsG : p s ∈ gr V E ∪ range c := Or.inr hps
  rw [hgr₃, hgr₂, hgr₁, insert_union, insert_union,
    insert_eq_of_mem hprG, insert_eq_of_mem hpsG, hcr]

end GraphMinor.GM12
