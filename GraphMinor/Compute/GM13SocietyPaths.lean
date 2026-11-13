module

public import GraphMinor.GM13.Defs
public import GraphMinor.GM05.ShadowMinor
public import GraphMinor.GM01.Basic
import GraphMinor.GM09.Basic

/-!
# Paths and cores after removing loops and parallel edges

Graph Minors XIII works with graphs that may have multiple edges (Section 1,
page 67) and loops (Section 2, page 68):
"Thus each edge has a head and a tail (the same, for a loop)."
"The underlying graph of a digraph is obtained by forgetting the directions of its edges."
A path has distinct vertices, so it
uses no loops. Replacing each of its edges by any edge with the same ends
preserves its vertex set. This gives the path transfer needed for cores in
Section 8, pages 93--95.
-/

public section
namespace GraphMinor.Compute
open Graph Surface GM09 GM13

private theorem gm13_walk_transfer {α β γ : Type*} {G : Graph α β} {H : Graph α γ}
    (hV : V(G) ⊆ V(H))
    (hA : ∀ u v, u ≠ v → G.Adj u v → H.Adj u v)
    {a b : α} (W : GraphWalk G a b) (hs : W.IsSimple) :
    ∃ W' : GraphWalk H a b, W'.support = W.support := by
  induction W with
  | nil hv => exact ⟨.nil (hV hv), rfl⟩
  | @cons u v b e hl rest ih =>
    have hs' := List.nodup_cons.mp hs
    have hne : u ≠ v := fun h => hs'.1 (h ▸ rest.start_mem_support)
    obtain ⟨f, hf⟩ := hA u v hne ⟨e, hl⟩
    obtain ⟨W', hW'⟩ := ih hs'.2
    exact ⟨.cons hf W', congrArg (List.cons u) hW'⟩

/-- Replacing edges between distinct ends preserves every path's vertex set.
This is the path reduction used for XIII, Section 8, pages 93--95. -/
theorem gm13_path_transfer {α β γ : Type*} {G : Graph α β} {H : Graph α γ}
    (hV : V(G) ⊆ V(H))
    (hA : ∀ u v, u ≠ v → G.Adj u v → H.Adj u v)
    {P : Graph α β} {a b : α} (hp : IsGraphPathWithEnds G P a b) :
    ∃ Q : Graph α γ, IsGraphPathWithEnds H Q a b ∧ V(Q) = V(P) := by
  obtain ⟨hPG, W, hs, hv, _⟩ := hp
  obtain ⟨W', hW'⟩ := gm13_walk_transfer (hPG.vertexSet_mono.trans hV)
    (fun u v hne ha => hA u v hne (ha.mono hPG)) W hs
  have hs' : W'.IsSimple := by
    change W'.support.Nodup
    rw [hW']
    exact hs
  refine ⟨walkSubgraph W', isGraphPathWithEnds_walkSubgraph hs', ?_⟩
  rw [vertexSet_walkSubgraph, hW', hv]

/-- Crosses lift by replacing each edge of the two paths. Their vertex sets
and their boundary endpoints stay the same (XIII, Section 8, page 93). -/
theorem gm13_cross_transfer {α β γ : Type*}
    {S : Society α β} {T : Society α γ}
    (hV : V(S.G) ⊆ V(T.G)) (hΩ : S.Ω = T.Ω)
    (hA : ∀ u v, u ≠ v → S.G.Adj u v → T.G.Adj u v)
    {P Q : Graph α β} (hc : S.IsCross P Q) :
    ∃ P' Q' : Graph α γ, T.IsCross P' Q' ∧ V(P') = V(P) ∧ V(Q') = V(Q) := by
  obtain ⟨hd, a, b, c, d, hp, hq, ho⟩ := hc
  obtain ⟨P', hp', hvp⟩ := gm13_path_transfer hV hA hp.1
  obtain ⟨Q', hq', hvq⟩ := gm13_path_transfer hV hA hq.1
  refine ⟨P', Q', ?_, hvp, hvq⟩
  refine ⟨?_, a, b, c, d, ?_, ?_, hΩ ▸ ho⟩
  · rwa [hvp, hvq]
  · exact ⟨hp', hp.2.1, hΩ ▸ hp.2.2⟩
  · exact ⟨hq', hq.2.1, hΩ ▸ hq.2.2⟩

/-- Removing loops and parallel copies preserves the existence of a cross. -/
theorem gm13_hasCross_iff {α β γ : Type*}
    {S : Society α β} {T : Society α γ}
    (hV : V(S.G) = V(T.G)) (hΩ : S.Ω = T.Ω)
    (hA : ∀ u v, u ≠ v → (S.G.Adj u v ↔ T.G.Adj u v)) :
    GM13.HasCross S ↔ GM13.HasCross T := by
  constructor
  · rintro ⟨P, Q, hc⟩
    obtain ⟨P', Q', hc', _, _⟩ := gm13_cross_transfer hV.subset hΩ
      (fun u v hn ha => (hA u v hn).mp ha) hc
    exact ⟨P', Q', hc'⟩
  · rintro ⟨P, Q, hc⟩
    obtain ⟨P', Q', hc', _, _⟩ := gm13_cross_transfer hV.symm.subset hΩ.symm
      (fun u v hn ha => (hA u v hn).mpr ha) hc
    exact ⟨P', Q', hc'⟩

/-- Trisecting sets depend only on vertices, the boundary, and adjacency
between distinct vertices. Loops and parallel copies do not affect them. -/
theorem gm13_isTrisecting_transfer {α β γ : Type*}
    {S : Society α β} {T : Society α γ}
    (hV : V(S.G) = V(T.G)) (hΩ : S.Ω = T.Ω)
    (hA : ∀ u v, u ≠ v → (S.G.Adj u v ↔ T.G.Adj u v))
    {Z : Set α} (hz : IsTrisecting S Z) : IsTrisecting T Z := by
  refine ⟨hV ▸ hz.subset_V, hΩ ▸ hz.bar_subset, ?_⟩
  intro v hv
  have hsets : {z ∈ Z | ∃ P : Graph α γ,
      IsGraphPathWithEnds T.G P v z ∧ V(P) ∩ Z = {z}} =
      {z ∈ Z | ∃ P : Graph α β,
      IsGraphPathWithEnds S.G P v z ∧ V(P) ∩ Z = {z}} := by
    ext z
    constructor
    · rintro ⟨hz, P, hp, hi⟩
      obtain ⟨Q, hq, hqV⟩ := gm13_path_transfer hV.symm.subset
        (fun u v hn ha => (hA u v hn).mpr ha) hp
      exact ⟨hz, Q, hq, hqV ▸ hi⟩
    · rintro ⟨hz, P, hp, hi⟩
      obtain ⟨Q, hq, hqV⟩ := gm13_path_transfer hV.subset
        (fun u v hn ha => (hA u v hn).mp ha) hp
      exact ⟨hz, Q, hq, hqV ▸ hi⟩
  rw [hsets]
  exact hz.attach_ncard_le_three v (hV.symm ▸ hv)

/-- The same simple graph is a core before and after removing loops and
parallel copies (XIII, Section 8, pages 93--94). -/
theorem gm13_isCoreOf_transfer {α β γ δ : Type*}
    {S : Society α β} {T : Society α γ} {C : Graph α δ}
    (hV : V(S.G) = V(T.G)) (hΩ : S.Ω = T.Ω)
    (hA : ∀ u v, u ≠ v → (S.G.Adj u v ↔ T.G.Adj u v))
    (hc : GM13.IsCoreOf S C) : GM13.IsCoreOf T C := by
  refine ⟨hc.isSimple, hc.finite_E,
    gm13_isTrisecting_transfer hV hΩ hA hc.isTrisecting, ?_⟩
  intro u hu v hv hn
  rw [hc.adj_iff u hu v hv hn]
  constructor
  · rintro ⟨P, hp, hi⟩
    obtain ⟨Q, hq, hqV⟩ := gm13_path_transfer hV.subset
      (fun u v hn ha => (hA u v hn).mp ha) hp
    exact ⟨Q, hq, hqV ▸ hi⟩
  · rintro ⟨P, hp, hi⟩
    obtain ⟨Q, hq, hqV⟩ := gm13_path_transfer hV.symm.subset
      (fun u v hn ha => (hA u v hn).mpr ha) hp
    exact ⟨Q, hq, hqV ▸ hi⟩

/-- Four-linkedness is unchanged because the core graph and boundary are
unchanged. Together with path transfer, this preserves a 4-linked core. -/
theorem gm13_isFourLinkedCore_transfer {α β γ δ : Type*}
    {S : Society α β} {T : Society α γ} {C : Graph α δ}
    (hV : V(S.G) = V(T.G)) (hΩ : S.Ω = T.Ω)
    (hA : ∀ u v, u ≠ v → (S.G.Adj u v ↔ T.G.Adj u v))
    (hc : GM13.IsFourLinkedCore S C) : GM13.IsFourLinkedCore T C := by
  refine ⟨gm13_isCoreOf_transfer hV hΩ hA hc.isCore, ?_⟩
  intro v hv
  have h := hc.fourLinked v hv
  change v ∈ V(C) ∧ _ at h ⊢
  simpa only [← hΩ] using h

/-- The underlying simple society has the original vertices and boundary.
Section 1 of XIII, page 67, calls its graph the underlying simple graph. -/
@[expose] noncomputable def gm13_simpleSociety {α β : Type*} (S : Society α β) :
    Society α (Sym2 α) where
  G := GM01.toGraph (GM05.simpleShadow S.G)
  Ω := S.Ω
  finite_V := S.finite_V
  finite_E := GM01.finite_edgeSet_of_finite_verts S.finite_V
  bar_subset := S.bar_subset

private theorem gm13_simpleSociety_adj {α β : Type*} (S : Society α β)
    (u v : α) (hn : u ≠ v) :
    S.G.Adj u v ↔ (gm13_simpleSociety S).G.Adj u v := by
  rw [gm13_simpleSociety, GM01.adj_toGraph]
  exact ⟨fun h => ⟨hn, h⟩, And.right⟩

/-- A society has a cross exactly when its underlying simple society has a
cross. This statement includes societies with loops and parallel edges. -/
theorem gm13_hasCross_simpleSociety_iff {α β : Type*} (S : Society α β) :
    GM13.HasCross S ↔ GM13.HasCross (gm13_simpleSociety S) :=
  gm13_hasCross_iff rfl rfl (gm13_simpleSociety_adj S)

/-- Exactly the same simple graphs are cores of a society and its underlying
simple society, including when the original graph has loops or parallel edges. -/
theorem gm13_isCoreOf_simpleSociety_iff {α β δ : Type*}
    (S : Society α β) (C : Graph α δ) :
    GM13.IsCoreOf S C ↔ GM13.IsCoreOf (gm13_simpleSociety S) C := by
  constructor
  · exact gm13_isCoreOf_transfer rfl rfl (gm13_simpleSociety_adj S)
  · exact gm13_isCoreOf_transfer rfl rfl
      (fun u v hn => (gm13_simpleSociety_adj S u v hn).symm)

/-- Four-linked cores agree for a society and its underlying simple society.
This is the mathematical reduction for XIII (8.3), page 95. -/
theorem gm13_isFourLinkedCore_simpleSociety_iff {α β δ : Type*}
    (S : Society α β) (C : Graph α δ) :
    GM13.IsFourLinkedCore S C ↔ GM13.IsFourLinkedCore (gm13_simpleSociety S) C := by
  constructor
  · exact gm13_isFourLinkedCore_transfer rfl rfl (gm13_simpleSociety_adj S)
  · exact gm13_isFourLinkedCore_transfer rfl rfl
      (fun u v hn => (gm13_simpleSociety_adj S u v hn).symm)

end GraphMinor.Compute
