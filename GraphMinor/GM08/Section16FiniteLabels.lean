module

public import GraphMinor.GM08.Defs
import GraphMinor.GM08.Section4

/-!
# Grafts with labels in a finite type

If the vertex labels come from a finite type, a graft has a bounded number of
vertices. Then every class of grafts is well-rooted, by Dickson's lemma.

For a sequence of such grafts, we compare three things: the vertex set, the
root set, and, for each unordered pair of vertices, the number of edges with
exactly these ends. There are finitely many vertex and root sets, and the edge
counts form a vector indexed by the finite type `Sym2 α`. Dickson's lemma
(`Pi.wellQuasiOrderedLE`) gives two grafts, an earlier one and a later one,
with the same vertex and root sets and with every edge count of the earlier one
at most that of the later one. Then the earlier graft is a subgraph of the
later one, up to renaming edges, so it is simulated in it.

This lets (16.1) hold for every label type: for an infinite one it is proved by
the paper's argument, and for a finite one the conclusion holds outright.
-/

public section

namespace GraphMinor.GM08

open Set Graph

universe u v

variable {α : Type u} {β : Type v}

/-- The edges of `G` whose ends form the unordered pair `p`. -/
def edgesWithEnds (G : Graph α β) (p : Sym2 α) : Set β :=
  {e | ∃ x y, G.IsLink e x y ∧ s(x, y) = p}

private theorem eq_of_mem_edgesWithEnds {G : Graph α β} {e : β} {p q : Sym2 α}
    (hp : e ∈ edgesWithEnds G p) (hq : e ∈ edgesWithEnds G q) : p = q := by
  obtain ⟨x, y, hxy, rfl⟩ := hp
  obtain ⟨x', y', hxy', rfl⟩ := hq
  exact (hxy.isLink_iff_sym2_eq.mp hxy')

private theorem edgesWithEnds_subset (G : Graph α β) (p : Sym2 α) :
    edgesWithEnds G p ⊆ E(G) := by
  rintro e ⟨x, y, h, -⟩
  exact h.edge_mem

private theorem isLink_of_mem_edgesWithEnds {G : Graph α β} {e : β} {x y : α}
    (h : e ∈ edgesWithEnds G s(x, y)) : G.IsLink e x y := by
  obtain ⟨u, w, huw, hs⟩ := h
  rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact huw
  · exact huw.symm

/-- A map of edges that keeps the ends of every edge of `H`, and is injective on
`E(H)`, gives a simulation of `H` in `G` with single-vertex branch sets. -/
theorem isGraphSimulation_of_edge_map {H G : Graph α β} (f : β → β)
    (hV : V(H) ⊆ V(G)) (hinj : InjOn f E(H))
    (hlink : ∀ e x y, H.IsLink e x y → G.IsLink (f e) x y) :
    IsGraphSimulation H G (fun v => {v}) f where
  vertex_nonempty v _ := ⟨v, rfl⟩
  vertex_subset v hv := by rintro _ rfl; exact hV hv
  edge_mem e he := by
    obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
    exact (hlink e x y h).edge_mem
  vertex_disjoint v₁ _ v₂ _ hne := Set.disjoint_singleton.mpr hne
  edge_injOn := hinj
  inc_iff v _ e he := by
    obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
    simp only [mem_singleton_iff, exists_eq_left]
    constructor
    · intro hv
      rcases hv.eq_or_eq_of_isLink h with rfl | rfl
      · exact (hlink e _ y h).inc_left
      · exact (hlink e x _ h).inc_right
    · intro hv
      rcases hv.eq_or_eq_of_isLink (hlink e x y h) with rfl | rfl
      · exact h.inc_left
      · exact h.inc_right
  isLoopAt_iff v _ e he := by
    obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
    simp only [mem_singleton_iff]
    constructor
    · intro hloop w hw
      have hG : G.IsLink (f e) v v := hlink e v v hloop
      rcases hw.eq_or_eq_of_isLink hG with h' | h' <;> exact h'
    · intro hall
      have hG := hlink e x y h
      have hx : x = v := hall x hG.inc_left
      have hy : y = v := hall y hG.inc_right
      subst hx hy
      exact h
  connected v hv := by
    let D := G.deleteEdges (f '' E(H))
    have hvD : {v} ⊆ V(D) := singleton_subset_iff.mpr (hV hv)
    refine ⟨(D.induce {v}).restrict ∅, restrict_le.trans (D.induce_le hvD), rfl,
      ⟨⟨v, rfl⟩, ?_⟩⟩
    rintro _ rfl _ rfl
    exact .refl

/-- If two grafts have the same vertex and root sets, and for every unordered pair
of vertices the first has at most as many edges with these ends as the second,
then the first is simulated in the second. -/
theorem isGraftSimulatedIn_of_edgeCounts_le {X Y : Graft α β}
    (hV : V(X.G) = V(Y.G)) (hT : X.T = Y.T)
    (hle : ∀ p, (edgesWithEnds X.G p).encard ≤ (edgesWithEnds Y.G p).encard) :
    IsGraftSimulatedIn X Y := by
  classical
  have hfinX : ∀ p, (edgesWithEnds X.G p).Finite := fun p =>
    X.finite_G.2.subset (edgesWithEnds_subset X.G p)
  have hg : ∀ p, ∃ g : β → β, edgesWithEnds X.G p ⊆ g ⁻¹' edgesWithEnds Y.G p ∧
      InjOn g (edgesWithEnds X.G p) := by
    intro p
    rcases (edgesWithEnds X.G p).eq_empty_or_nonempty with h | ⟨e, he⟩
    · exact ⟨id, by simp [h], by simp [h]⟩
    · have : Nonempty β := ⟨e⟩
      exact (hfinX p).exists_injOn_of_encard_le (hle p)
  choose g hgmaps hginj using hg
  let key : β → Option (Sym2 α) := fun e =>
    if h : ∃ p, e ∈ edgesWithEnds X.G p then some h.choose else none
  have hkey : ∀ e p, e ∈ edgesWithEnds X.G p → key e = some p := by
    intro e p hp
    have h : ∃ p, e ∈ edgesWithEnds X.G p := ⟨p, hp⟩
    simp only [key, h, ↓reduceDIte]
    exact congrArg some (eq_of_mem_edgesWithEnds h.choose_spec hp)
  let f : β → β := fun e => match key e with
    | some p => g p e
    | none => e
  have hf : ∀ e p, e ∈ edgesWithEnds X.G p → f e = g p e := by
    intro e p hp
    simp only [f, hkey e p hp]
  have hmemX : ∀ e ∈ E(X.G), ∃ p, e ∈ edgesWithEnds X.G p := by
    intro e he
    obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
    exact ⟨s(x, y), x, y, h, rfl⟩
  have hlink : ∀ e x y, X.G.IsLink e x y → Y.G.IsLink (f e) x y := by
    intro e x y h
    have hp : e ∈ edgesWithEnds X.G s(x, y) := ⟨x, y, h, rfl⟩
    rw [hf e _ hp]
    exact isLink_of_mem_edgesWithEnds (hgmaps _ hp)
  have hinj : InjOn f E(X.G) := by
    intro e he e' he' heq
    obtain ⟨p, hp⟩ := hmemX e he
    obtain ⟨p', hp'⟩ := hmemX e' he'
    rw [hf e p hp, hf e' p' hp'] at heq
    have hpp : p = p' := by
      have h1 : g p e ∈ edgesWithEnds Y.G p := hgmaps p hp
      have h2 : g p' e' ∈ edgesWithEnds Y.G p' := hgmaps p' hp'
      rw [heq] at h1
      exact eq_of_mem_edgesWithEnds h1 h2
    subst hpp
    exact hginj p hp hp' heq
  refine ⟨fun v => {v}, f, isGraphSimulation_of_edge_map f hV.subset hinj hlink, ?_, ?_⟩
  · rw [hT]
  · intro u hu
    exact ⟨u, rfl, hT ▸ hu⟩

/-- If the vertex labels come from a finite type, every class of grafts is
well-rooted. -/
theorem isWellRootedGraftClass_of_finite [Finite α] (𝒜 : Set (Graft α β)) :
    IsWellRootedGraftClass 𝒜 := by
  intro X _
  let key : ℕ → (Set α × Set α) × (Sym2 α → ℕ∞) := fun n =>
    ((V((X n).G), (X n).T), fun p => (edgesWithEnds (X n).G p).encard)
  have hwqo : WellQuasiOrdered fun a b : (Set α × Set α) × (Sym2 α → ℕ∞) =>
      a.1 = b.1 ∧ a.2 ≤ b.2 :=
    (Finite.wellQuasiOrdered (· = ·)).prod wellQuasiOrdered_le
  obtain ⟨i, j, hij, heq, hle⟩ := hwqo key
  simp only [key, Prod.mk.injEq] at heq hle
  exact ⟨i, j, hij, isGraftSimulatedIn_of_edgeCounts_le heq.1 heq.2 hle⟩

end GraphMinor.GM08
