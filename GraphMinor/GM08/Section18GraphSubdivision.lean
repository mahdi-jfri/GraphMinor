module

public import GraphMinor.Surface.SurfaceGraph
import Mathlib.Data.Set.Card
import Lean.Elab.Tactic.Omega

/-!
# Subdivision preserves the Euler sum of a cutting graph

Inserting a point in an edge replaces that edge by its two subarcs.
Both the vertex count and the edge count increase by one. This is the
subdivision step for counting the refined schism graph in VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u

/-- Subdivide a finite geometric graph at a nonvertex point of its
carrier. Exactly one vertex and one edge are added, as needed for the
refinement count in VIII (18.2), page 286. -/
theorem exists_graph_subdivision_at_point {S : Type u} [TopologicalSpace S] [T2Space S]
    {V : Set S} {E : Set (Set S)} (h : IsGraph V E) {x : S}
    (hxgr : x ∈ gr V E) (hV : x ∉ V) :
    ∃ E', IsGraph (insert x V) E' ∧ gr (insert x V) E' = gr V E ∧
      ⋃₀ E ⊆ ⋃₀ E' ∧ E'.ncard = E.ncard + 1 := by
  classical
  obtain ⟨e, he, hx⟩ : ∃ e ∈ E, x ∈ e := hxgr.resolve_left hV
  obtain ⟨u, v, huv, hl, hi⟩ := h.edge e he
  have hu : u ∈ V := (hi.symm ▸ mem_insert u {v} : u ∈ e ∩ V).2
  have hv : v ∈ V := (hi.symm ▸ mem_insert_of_mem u rfl : v ∈ e ∩ V).2
  have hxu : x ≠ u := fun he' => hV (he' ▸ hu)
  have hxv : x ≠ v := fun he' => hV (he' ▸ hv)
  obtain ⟨L₁, L₂, h₁, h₂, hun, hin⟩ := hl.split hx hxu hxv
  have hs1 : L₁ ⊆ e := hun ▸ subset_union_left
  have hs2 : L₂ ⊆ e := hun ▸ subset_union_right
  have hof : ∀ f ∈ E, f ≠ e → x ∉ f := fun f hf hne hxf => hV (h.disj e he f hf hne.symm ⟨hx, hxf⟩)
  have hvL : v ∉ L₁ := fun hc => hxv (mem_singleton_iff.mp (hin ▸ (⟨hc, h₂.right_mem⟩ : v ∈ L₁ ∩ L₂))).symm
  have huL : u ∉ L₂ := fun hc => hxu (mem_singleton_iff.mp (hin ▸ (⟨h₁.left_mem, hc⟩ : u ∈ L₁ ∩ L₂))).symm
  refine ⟨insert L₁ (insert L₂ (E \ {e})), ⟨h.fin.insert x, ((h.fine.sdiff).insert _).insert _, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rintro f (rfl | rfl | ⟨hf, hne⟩)
    · refine ⟨u, x, hxu.symm, h₁, ?_⟩
      ext y
      constructor
      · rintro ⟨hy, rfl | hy'⟩
        · simp
        · have : y ∈ e ∩ V := ⟨hs1 hy, hy'⟩
          rw [hi] at this
          rcases this with rfl | rfl
          · simp
          · exact absurd hy hvL
      · rintro (rfl | rfl)
        · exact ⟨h₁.left_mem, .inr hu⟩
        · exact ⟨h₁.right_mem, .inl rfl⟩
    · refine ⟨x, v, hxv, h₂, ?_⟩
      ext y
      constructor
      · rintro ⟨hy, rfl | hy'⟩
        · simp
        · have : y ∈ e ∩ V := ⟨hs2 hy, hy'⟩
          rw [hi] at this
          rcases this with rfl | rfl
          · exact absurd hy huL
          · simp
      · rintro (rfl | rfl)
        · exact ⟨h₂.left_mem, .inl rfl⟩
        · exact ⟨h₂.right_mem, .inr hv⟩
    · obtain ⟨a, b, hab, hl', hi'⟩ := h.edge f hf
      refine ⟨a, b, hab, hl', ?_⟩
      rw [inter_insert_of_notMem (hof f hf hne), hi']
  · have hL1 : ∀ g ∈ E \ {e}, L₁ ∩ g ⊆ insert x V := fun g hg y hy =>
      .inr (h.disj e he g hg.1 (Ne.symm hg.2) ⟨hs1 hy.1, hy.2⟩)
    have hL2 : ∀ g ∈ E \ {e}, L₂ ∩ g ⊆ insert x V := fun g hg y hy =>
      .inr (h.disj e he g hg.1 (Ne.symm hg.2) ⟨hs2 hy.1, hy.2⟩)
    have h12 : L₁ ∩ L₂ ⊆ insert x V := by
      rw [hin]
      exact singleton_subset_iff.mpr (mem_insert _ _)
    rintro f (rfl | rfl | hf) g (rfl | rfl | hg) hne
    · exact absurd rfl hne
    · exact h12
    · exact hL1 g hg
    · exact (inter_comm _ _).subset.trans h12
    · exact absurd rfl hne
    · exact hL2 g hg
    · exact (inter_comm _ _).subset.trans (hL1 f hf)
    · exact (inter_comm _ _).subset.trans (hL2 f hf)
    · exact (h.disj f hf.1 g hg.1 hne).trans (subset_insert _ _)
  · refine Eq.trans ?_ (insert_eq_of_mem hxgr)
    ext y
    simp only [gr, mem_union, mem_insert_iff, mem_sUnion, mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ((rfl | hy) | ⟨f, (rfl | rfl | ⟨hf, -⟩), hy⟩)
      · exact .inl rfl
      · exact .inr (.inl hy)
      · exact .inr (.inr ⟨e, he, hs1 hy⟩)
      · exact .inr (.inr ⟨e, he, hs2 hy⟩)
      · exact .inr (.inr ⟨f, hf, hy⟩)
    · rintro (rfl | hy | ⟨f, hf, hy⟩)
      · exact .inl (.inl rfl)
      · exact .inl (.inr hy)
      · by_cases hfe : f = e
        · subst hfe
          rw [← hun] at hy
          rcases hy with hy | hy
          · exact .inr ⟨L₁, .inl rfl, hy⟩
          · exact .inr ⟨L₂, .inr (.inl rfl), hy⟩
        · exact .inr ⟨f, .inr (.inr ⟨hf, hfe⟩), hy⟩
  · rintro y ⟨f, hf, hy⟩
    by_cases hfe : f = e
    · subst hfe
      rw [← hun] at hy
      rcases hy with hy | hy
      · exact ⟨L₁, .inl rfl, hy⟩
      · exact ⟨L₂, .inr (.inl rfl), hy⟩
    · exact ⟨f, .inr (.inr ⟨hf, hfe⟩), hy⟩
  · have h12 : L₁ ≠ L₂ := fun heq => huL (heq ▸ h₁.left_mem)
    have hn1 : L₁ ∉ E \ {e} := fun hh => hof L₁ hh.1 hh.2 h₁.right_mem
    have hn2 : L₂ ∉ E \ {e} := fun hh => hof L₂ hh.1 hh.2 h₂.left_mem
    have hn1' : L₁ ∉ insert L₂ (E \ {e}) := by
      rintro (hh | hh)
      · exact h12 hh
      · exact hn1 hh
    rw [ncard_insert_of_notMem hn1' ((h.fine.sdiff).insert L₂),
      ncard_insert_of_notMem hn2 (h.fine.sdiff)]
    exact congrArg (fun n => n + 1) (ncard_sdiff_singleton_add_one he h.fine)

/-- Mark finitely many points of a cutting graph without changing its
Euler sum. This supplies the common-refinement step in VIII (18.2). -/
theorem exists_graph_subdivision_at_finite_set {S : Type u} [TopologicalSpace S]
    [T2Space S] {V : Set S} {E : Set (Set S)} (h : IsGraph V E)
    {M : Set S} (hM : M.Finite) (hsub : M ⊆ gr V E) :
    ∃ E', IsGraph (V ∪ M) E' ∧ gr (V ∪ M) E' = gr V E ∧
      ⋃₀ E ⊆ ⋃₀ E' ∧ (V ∪ M).ncard + E.ncard = V.ncard + E'.ncard := by
  classical
  induction M, hM using Set.Finite.induction_on with
  | empty => exact ⟨E, by simpa, by simp, subset_rfl, by simp⟩
  | @insert x M hxM hM ih =>
    obtain ⟨E₁, hg₁, hgr₁, hE₁, hcount₁⟩ := ih ((subset_insert x M).trans hsub)
    have hvertex : V ∪ insert x M = insert x (V ∪ M) := by
      ext y
      simp only [mem_union, mem_insert_iff]
      exact or_left_comm
    by_cases hxV : x ∈ V ∪ M
    · have hvertex' : V ∪ insert x M = V ∪ M := hvertex.trans (insert_eq_of_mem hxV)
      rw [hvertex']
      exact ⟨E₁, hg₁, hgr₁, hE₁, hcount₁⟩
    · have hxgr : x ∈ gr (V ∪ M) E₁ := hgr₁.symm ▸ hsub (mem_insert x M)
      obtain ⟨E₂, hg₂, hgr₂, hE₂, hcount₂⟩ := exists_graph_subdivision_at_point hg₁ hxgr hxV
      rw [hvertex]
      refine ⟨E₂, hg₂, hgr₂.trans hgr₁, hE₁.trans hE₂, ?_⟩
      rw [ncard_insert_of_notMem hxV (h.fin.union hM), hcount₂]
      omega

end GraphMinor.GM08
