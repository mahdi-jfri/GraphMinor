module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM11.Defs
import GraphMinor.GM11.PerimeterCount
import GraphMinor.GM11.Walks

/-!
# Reading vertices and edges from a region walk

The region walk used in VI (5.1), page 129, follows the frontier
one edge at a time. A vertex on the tracing curve is therefore a
vertex of the walk. If the tracing curve lies in a set, all support
vertices and all traversed edges lie in that set as well. These facts
let us extract the boundary path used by the paper.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

universe u

/-- A drawing vertex encountered by a tracing curve belongs to the
support of the walk it traces. -/
theorem vertex_mem_support_of_runsAlongOn
    {S : Type u} [TopologicalSpace S] {G : Drawing S} {φ : ℝ → S}
    {a b : S} (W : GraphWalk G.toGraph a b) :
    ∀ {l r : ℝ}, RunsAlongOn G φ l r W → ∀ t ∈ Icc l r,
      φ t ∈ G.V → φ t ∈ W.support := by
  induction W with
  | nil ha =>
    rintro l r ⟨hlr, hφ⟩ t ht _
    have htl : t = l := le_antisymm (hlr.symm ▸ ht.2) ht.1
    rw [htl, hφ]
    exact List.mem_singleton_self _
  | @cons a c b e hl R ih =>
    rintro l r ⟨c, hlc, hφ, _, him, hR⟩ t ht htV
    rcases lt_or_ge t c with htc | hct
    · rcases eq_or_lt_of_le ht.1 with heq | hlt
      · rw [← heq, hφ]
        exact List.mem_cons_self
      · have hte : φ t ∈ e := him ▸ mem_image_of_mem φ ⟨hlt, htc⟩
        exact False.elim ((hl.1.2.1 hte).2 htV)
    · exact List.mem_cons_of_mem _ (ih hR t ⟨hct, ht.2⟩ htV)

/-- A tracing curve confined to a set has all the walk's vertices and
edges in that set. -/
theorem support_edges_subset_of_runsAlongOn
    {S : Type u} [TopologicalSpace S] {G : Drawing S} {φ : ℝ → S} {T : Set S}
    {a b : S} (W : GraphWalk G.toGraph a b) :
    ∀ {l r : ℝ}, RunsAlongOn G φ l r W → (∀ t ∈ Icc l r, φ t ∈ T) →
      (∀ x ∈ W.support, x ∈ T) ∧ (∀ e ∈ W.edges, e ⊆ T) := by
  induction W with
  | nil ha =>
    rintro l r ⟨hlr, hφ⟩ hT
    constructor
    · intro x hx
      have hxa := List.mem_singleton.mp hx
      subst x
      rw [← hφ]
      exact hT l ⟨le_rfl, hlr.le⟩
    · simp [GraphWalk.edges]
  | @cons a c b e hl R ih =>
    rintro l r ⟨m, hlm, hφ, _, him, hR⟩ hT
    have hmr : m ≤ r := GM11.runs_le R hR
    have hrest := ih hR (fun t ht => hT t ⟨hlm.le.trans ht.1, ht.2⟩)
    constructor
    · intro x hx
      rcases List.mem_cons.mp hx with hxa | hxR
      · rw [hxa, ← hφ]
        exact hT l ⟨le_rfl, hlm.le.trans hmr⟩
      · exact hrest.1 x hxR
    · intro f hf x hx
      rcases List.mem_cons.mp hf with hfe | hfR
      · subst f
        rw [← him] at hx
        obtain ⟨t, ht, rfl⟩ := hx
        exact hT t ⟨ht.1.le, ht.2.le.trans hmr⟩
      · exact hrest.2 f hfR hx

end GraphMinor.GM06
