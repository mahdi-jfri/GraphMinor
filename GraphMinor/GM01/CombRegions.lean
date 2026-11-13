module

public import GraphMinor.GM01.CombSubdivisionCuts
import Lean.Elab.Tactic.Omega

/-!
# The spine region sequence

Graph Minors I, page 55, sets `R₀ = V(H)` and `R_N = ∅`. Between these
endpoints, `R_j` consists of vertices reachable from the last spine
centre while avoiding the `j`th spine centre. We implement this indexing
and prove that the regions decrease, using the proved spine cuts and
the fact that the separate root path does not change these regions.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09

/-- The sequence `R_j` on page 55 of Graph Minors I. Spine indices here
start at zero, so the cut for the paper's `R_j` has index `j−1`. The
sequence is extended by empty sets after its endpoint. -/
def combSpineRegion {α β : Type*} {γ δ : ℕ} (hδ : 0 < δ)
    (H : Graph α β) (c : (pathComb γ δ).verts → α) (j : ℕ) : Set α :=
  if j = 0 then V(H) else if hj : j < δ then
    vertexAvoidanceRegion H
      (c ⟨Sum.inl ⟨δ - 1, by omega⟩, pathComb_spine_mem γ δ _⟩)
      (c ⟨Sum.inl ⟨j - 1, by omega⟩, pathComb_spine_mem γ δ _⟩)
    else ∅

/-- The initial region contains the whole graph. -/
theorem combSpineRegion_zero {α β : Type*} {γ δ : ℕ} (hδ : 0 < δ)
    (H : Graph α β) (c : (pathComb γ δ).verts → α) :
    combSpineRegion hδ H c 0 = V(H) := by simp only [combSpineRegion, ↓reduceIte]

/-- The region at the endpoint, and all later regions, are empty. -/
theorem combSpineRegion_empty {α β : Type*} {γ δ j : ℕ} (hδ : 0 < δ)
    (H : Graph α β) (c : (pathComb γ δ).verts → α) (hj : δ ≤ j) :
    combSpineRegion hδ H c j = ∅ := by
  have hjne : j ≠ 0 := by omega
  have hjlt : ¬ j < δ := by omega
  simp only [combSpineRegion, hjne, ↓reduceIte, hjlt, ↓reduceDIte]

/-- Every spine region consists of vertices of the graph. -/
theorem combSpineRegion_subset {α β : Type*} {γ δ : ℕ} (hδ : 0 < δ)
    (H : Graph α β) (c : (pathComb γ δ).verts → α) (j : ℕ) :
    combSpineRegion hδ H c j ⊆ V(H) := by
  unfold combSpineRegion
  split
  · exact Subset.rfl
  · split
    · exact (vertexAvoidanceRegion_subset H _ _).trans sdiff_subset
    · exact empty_subset _

/-- The actual region sequence in the subdivided comb together with its
root path is decreasing. All source cuts and attachment conditions are
proved in the preceding geometric lemmas. -/
theorem combSpineRegion_antitone {α β : Type*} {γ δ : ℕ} (hδ : 0 < δ)
    {G N R : Graph α β} (hN : N ≤ G) (hR : R ≤ G)
    {c : (pathComb γ δ).verts → α} (hc : Function.Injective c)
    (hcentres : ∀ v, c v ∈ V(N))
    {P : (pathComb γ δ).coe.edgeSet → Graph α β} (hPN : ∀ e, P e ≤ N)
    (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ δ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ δ).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c)
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ δ hδ).root}) :
    Antitone (combSpineRegion hδ (subgraphUnion G N R) c) := by
  intro a b hab
  by_cases ha : a = 0
  · subst a
    rw [combSpineRegion_zero]
    exact combSpineRegion_subset hδ _ c b
  by_cases hb : δ ≤ b
  · rw [combSpineRegion_empty hδ _ c hb]
    exact empty_subset _
  have haLt : a < δ := by omega
  have hbLt : b < δ := by omega
  have hbne : b ≠ 0 := by omega
  by_cases heq : a = b
  · subst b
    exact Subset.rfl
  have hcuts : a - 1 < b - 1 := by omega
  have hlast : b - 1 < δ - 1 := by omega
  let i : Fin δ := ⟨a - 1, by omega⟩
  let j : Fin δ := ⟨b - 1, by omega⟩
  let t : Fin δ := ⟨δ - 1, by omega⟩
  have hti : i.val < t.val := by dsimp [i, t]; omega
  have htj : j.val < t.val := hlast
  simp only [combSpineRegion, ha, hbne, ↓reduceIte, haLt, hbLt, ↓reduceDIte]
  rw [comb_root_path_region_eq hN hR hc hPN hE hPaths hInter j t htj
    (hcentres _) hmeet,
    comb_root_path_region_eq hN hR hc hPN hE hPaths hInter i t hti
      (hcentres _) hmeet]
  exact comb_subdivision_regions_nested hc hPN hE hPaths hInter i j t hcuts htj (hcentres _)

/-- Every region before the empty endpoint is connected and contains the
last spine centre. The initial region uses connectivity of the whole
graph, and each later one uses paths to that centre after deletion. -/
theorem combSpineRegion_connected {α β : Type*} {γ δ : ℕ} (hδ : 0 < δ)
    {H : Graph α β} (hconn : GraphConnected H) {c : (pathComb γ δ).verts → α}
    (hc : Function.Injective c) (hcentres : ∀ v, c v ∈ V(H)) (m : ℕ) (hm : m < δ) :
    GraphConnected (H.induce (combSpineRegion hδ H c m)) ∧
      c ⟨Sum.inl ⟨δ - 1, by omega⟩, pathComb_spine_mem γ δ _⟩ ∈
        combSpineRegion hδ H c m := by
  by_cases hm0 : m = 0
  · subst m
    rw [combSpineRegion_zero]
    exact ⟨by simpa only [Graph.induce_vertexSet] using hconn, hcentres _⟩
  · simp only [combSpineRegion, hm0, ↓reduceIte, hm, ↓reduceDIte]
    have hne : c ⟨Sum.inl ⟨δ - 1, by omega⟩, pathComb_spine_mem γ δ _⟩ ≠
        c ⟨Sum.inl ⟨m - 1, by omega⟩, pathComb_spine_mem γ δ _⟩ := by
      intro heq
      have hval := congrArg (fun v : (pathComb γ δ).verts ↦
        (pathCombSpineIndex v.val).val) (hc heq)
      change δ - 1 = m - 1 at hval
      omega
    exact ⟨vertexAvoidanceRegion_connected (hcentres _) hne,
      last_mem_vertexAvoidanceRegion (hcentres _) hne⟩

end GraphMinor.GM01
