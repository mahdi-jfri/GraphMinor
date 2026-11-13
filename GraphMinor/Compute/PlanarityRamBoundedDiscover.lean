module

public import GraphMinor.Compute.PlanarityRamBounds
public import GraphMinor.Compute.PlanarityRamDiscover

/-!
# Bounds preserved by edge creation and discovery

Creating an edge copies endpoint labels and existing depths. Discovery
writes bounded parent labels and a valid incoming-edge index. Its only
new depth is the source depth plus one, whose bound is supplied by the
frame-depth invariant.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

private theorem optionArray_set_bound {N : ℕ} (values : Array (Option ℕ))
    (hsize : values.size = N) (P : ℕ → Prop)
    (hbound : ∀ v : Fin N, ∀ d, values[v.val]?.join = some d → P d)
    (u : Fin N) (value : ℕ) (hvalue : P value) :
    ∀ v : Fin N, ∀ d, ((values.set! u.val (some value))[v.val]?.join) = some d → P d := by
  intro v d hv
  by_cases he : u.val = v.val
  · have hu : u.val < values.size := hsize.symm ▸ u.isLt
    rw [← he] at hv
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hu,
      Option.join_some, Option.some.injEq] at hv
    exact hv ▸ hvalue
  · have heval : (values.set! u.val (some value))[v.val]? = values[v.val]? := by
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne he]
    exact hbound v d (by simpa only [heval] using hv)

/-- Defaulted depths at valid vertices are below N. -/
theorem SearchBounded.depth_lt {N : ℕ} {search : Search} (h : SearchBounded N search)
    (v : Fin N) : (search.depth[v.val]?.join).getD 0 < N := by
  cases hd : search.depth[v.val]?.join with
  | none => simpa using Nat.lt_of_le_of_lt (Nat.zero_le v.val) v.isLt
  | some d => exact h.2.2.2.1 v d hd

/-- An in-range depth update preserves bounds when its new depth is below N. -/
theorem SearchBounded.set_depth {N : ℕ} {search : Search} (h : SearchBounded N search)
    (u : Fin N) (d : ℕ) (hd : d < N) :
    SearchBounded N { search with depth := search.depth.set! u.val (some d) } := by
  refine ⟨by simpa using h.1, h.2.1, h.2.2.1, ?_, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  exact optionArray_set_bound search.depth h.1 (fun d => d < N) h.2.2.2.1 u d hd

/-- A new record inherits the endpoint and depth bounds. -/
theorem SearchBounded.addEdge {N : ℕ} {search : Search} (h : SearchBounded N search)
    (v u : ℕ) (hv : v < N) (hu : u < N) (tree : Bool) :
    SearchBounded N (addEdge search v u tree).1 := by
  let e : EdgeRecord := ⟨v, u, tree,
    ⟨if tree then (search.depth[v]?.join).getD 0 else (search.depth[u]?.join).getD 0,
      (search.depth[v]?.join).getD 0⟩, 0⟩
  have hsource := h.depth_lt ⟨v, hv⟩
  have htarget := h.depth_lt ⟨u, hu⟩
  have heb : EdgeBounded N e := by
    refine ⟨hv, hu, ?_, hsource, Nat.zero_le _⟩
    cases tree <;> assumption
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_, ?_⟩
  · intro z i hi
    have hh := h.2.2.2.2.2.1 z i hi
    simpa [LRPlanarity.addEdge] using Nat.lt_trans hh (Nat.lt_succ_self _)
  · intro i hi
    change EdgeBounded N (search.edges.push e)[i]!
    have hi' : i < (search.edges.push e).size := hi
    rw [getElem!_pos (search.edges.push e) i hi']
    by_cases hold : i < search.edges.size
    · rw [Array.getElem_push_lt hold]
      simpa only [getElem!_pos search.edges i hold] using h.2.2.2.2.2.2 i hold
    · have heq : i = search.edges.size := by
        have hi2 : i < search.edges.size + 1 := by simpa only [Array.size_push] using hi'
        omega
      subst i
      simpa using heb

/-- Child discovery preserves all bounds when its incremented depth is
below N and its incoming edge is already live. -/
theorem SearchBounded.discoverChild {N : ℕ} {search : Search} (h : SearchBounded N search)
    (v u i : ℕ) (hv : v < N) (hu : u < N) (hi : i < search.edges.size)
    (hd : (search.depth[v]?.join).getD 0 + 1 < N) :
    SearchBounded N (discoverChild search v u i) := by
  refine ⟨by simpa [PlanarityRam.discoverChild] using h.1, by simpa [PlanarityRam.discoverChild] using h.2.1,
    by simpa [PlanarityRam.discoverChild] using h.2.2.1, ?_, ?_, ?_, h.2.2.2.2.2.2⟩
  · exact optionArray_set_bound search.depth h.1 (fun d => d < N) h.2.2.2.1 ⟨u, hu⟩ _ hd
  · exact optionArray_set_bound search.parent h.2.1 (fun p => p < N) h.2.2.2.2.1 ⟨u, hu⟩ v hv
  · exact optionArray_set_bound search.parentEdge h.2.2.1 (fun i => i < search.edges.size)
      h.2.2.2.2.2.1 ⟨u, hu⟩ i hi

end GraphMinor.Compute.PlanarityRam
