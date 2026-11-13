module

public import GraphMinor.GM09.Section2e
public import GraphMinor.HP25.Gap43Rural
public import GraphMinor.Wagner.GraphTools

/-!
# Societies built from a simple graph

To prove Wagner's theorem we apply Graph Minors IX (2.4) to societies `(G, Ω)` where `G` is a simple
graph `K` restricted to a vertex set `R`, and `Ω` runs through the entries of a list `L` of
distinct vertices. This file builds that society (`society`) and proves what (2.4) needs about it:

* it is `3`-connected when no set of at most two vertices cuts a part of `R` off from `L`
  (`society_isKConnected_three`);
* it has no cross when `L` has three entries, since a cross needs four vertices of `Ω`
  (`society_not_cross`);
* when it is rural, the graph `K` restricted to `R` has a plane embedding
  (`planeEmbedding_of_rural`), by `HP25.exists_planeEmbedding`.
-/

@[expose] public section

namespace GraphMinor.Wagner

open Set Function Graph GraphMinor GraphMinor.GM09

variable {γ : Type*}

/-- The simple graph `K` restricted to `R`, as a `Graph` with edges labelled by `Sym2 γ`. -/
def sGraph (K : SimpleGraph γ) (R : Set γ) : Graph γ (Sym2 γ) :=
  (Graph.ofSimpleGraph K).induce R

theorem sGraph_isLink {K : SimpleGraph γ} {R : Set γ} {e : Sym2 γ} {x y : γ} :
    (sGraph K R).IsLink e x y ↔ (e = s(x, y) ∧ K.Adj x y) ∧ x ∈ R ∧ y ∈ R := by
  simp only [sGraph, Graph.induce_isLink, Graph.ofSimpleGraph_isLink]
  constructor
  · rintro ⟨⟨rfl, h⟩, hx, hy⟩
    exact ⟨⟨rfl, h⟩, hx, hy⟩
  · rintro ⟨⟨rfl, h⟩, hx, hy⟩
    exact ⟨⟨rfl, h⟩, hx, hy⟩

theorem sGraph_vertexSet {K : SimpleGraph γ} {R : Set γ} : V(sGraph K R) = R := rfl

theorem sGraph_isLink_of_adj {K : SimpleGraph γ} {R : Set γ} {x y : γ} (h : K.Adj x y)
    (hx : x ∈ R) (hy : y ∈ R) : (sGraph K R).IsLink s(x, y) x y :=
  sGraph_isLink.mpr ⟨⟨rfl, h⟩, hx, hy⟩

theorem sGraph_isSimpleGraph (K : SimpleGraph γ) (R : Set γ) : IsSimpleGraph (sGraph K R) := by
  refine ⟨fun e _ v h => ?_, fun e₁ _ e₂ _ u v h₁ h₂ => ?_⟩
  · exact K.loopless.irrefl v (sGraph_isLink.mp h).1.2
  · rw [(sGraph_isLink.mp h₁).1.1, (sGraph_isLink.mp h₂).1.1]

variable [Finite γ]

/-- The society on `K` restricted to `R`, whose cyclic permutation runs through the list `L`. -/
noncomputable def society (K : SimpleGraph γ) (R : Set γ) (L : List γ) (hnd : L.Nodup)
    (hne : L ≠ []) (hLR : ∀ x ∈ L, x ∈ R) : Society γ (Sym2 γ) where
  G := sGraph K R
  Ω := CyclicPerm.ofNodupList L hnd hne
  finite_V := Set.toFinite _
  finite_E := Set.toFinite _
  bar_subset := fun x hx => hLR x hx

variable {K : SimpleGraph γ} {R : Set γ} {L : List γ} {hnd : L.Nodup} {hne : L ≠ []}
  {hLR : ∀ x ∈ L, x ∈ R}

theorem society_G : (society K R L hnd hne hLR).G = sGraph K R := rfl

theorem society_bar : (society K R L hnd hne hLR).Ω.bar = {x | x ∈ L} := rfl

/-- The society is `3`-connected if no set `T` of at most two vertices cuts a nonempty part `D` of
`R` away from `L`. Here "cuts away" means that every edge of `K` from `D` to `R` ends in `D` or
in `T`. -/
theorem society_isKConnected_three
    (hcut : ∀ T : Set γ, T.ncard ≤ 2 → ∀ D : Set γ, D ⊆ R → D.Nonempty → Disjoint D T →
      (∀ x ∈ L, x ∉ D) → (∀ a ∈ D, ∀ b ∈ R, K.Adj a b → b ∈ D ∨ b ∈ T) → False) :
    (society K R L hnd hne hLR).IsKConnected 3 := by
  intro k hk G₁ G₂ hsep
  obtain ⟨⟨⟨hG₁, hG₂, hV, hE, -⟩, hbar⟩, hcard, hne₂⟩ := hsep
  have hV₂R : V(G₂) ⊆ R := hG₂.vertexSet_mono
  have hV₁R : V(G₁) ⊆ R := hG₁.vertexSet_mono
  refine hcut (V(G₁) ∩ V(G₂)) (by omega) (R \ V(G₂)) sdiff_subset ?_ ?_ ?_ ?_
  · by_contra h
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at h
    exact hne₂ (Subset.antisymm hV₂R h)
  · exact disjoint_left.mpr fun x hx hx' => hx.2 hx'.2
  · intro x hx hxD
    exact hxD.2 (hbar hx)
  · intro a ha b hb hab
    have hlink : (sGraph K R).IsLink s(a, b) a b := sGraph_isLink_of_adj hab ha.1 hb
    have hmem : s(a, b) ∈ E(G₁) ∪ E(G₂) := by
      rw [hE]
      exact hlink.edge_mem
    rcases hmem with h₁ | h₂
    · have hl₁ : G₁.IsLink s(a, b) a b := (hG₁.isLink_iff h₁).mpr hlink
      by_cases hb₂ : b ∈ V(G₂)
      · exact Or.inr ⟨hl₁.right_mem, hb₂⟩
      · exact Or.inl ⟨hb, hb₂⟩
    · have hl₂ : G₂.IsLink s(a, b) a b := (hG₂.isLink_iff h₂).mpr hlink
      exact (ha.2 hl₂.left_mem).elim

/-- The no-cut hypothesis of `society_isKConnected_three` holds when `L` has three distinct entries
in `R` and deleting any two vertices from `R` leaves a preconnected induced subgraph. -/
theorem noCut_of_preconnected (h3 : 3 ≤ L.length) (hLnd : L.Nodup) (hLR' : ∀ x ∈ L, x ∈ R)
    (hpc : ∀ T : Set γ, T.ncard ≤ 2 → (K.induce {x | x ∈ R ∧ x ∉ T}).Preconnected) :
    ∀ T : Set γ, T.ncard ≤ 2 → ∀ D : Set γ, D ⊆ R → D.Nonempty → Disjoint D T →
      (∀ x ∈ L, x ∉ D) → (∀ a ∈ D, ∀ b ∈ R, K.Adj a b → b ∈ D ∨ b ∈ T) → False := by
  classical
  intro T hT D hDR hDne hDT hLD hcl
  -- Some entry of `L` lies outside `T`, since `L` has three distinct entries.
  have hy : ∃ y ∈ L, y ∉ T := by
    by_contra hall
    push Not at hall
    have hsub : {x | x ∈ L} ⊆ T := fun x hx => hall x hx
    have hfin : T.Finite := Set.toFinite T
    have h1 : ({x | x ∈ L} : Set γ).ncard = L.length := by
      have : ({x | x ∈ L} : Set γ) = (L.toFinset : Set γ) := by ext; simp
      rw [this, ncard_coe_finset, List.toFinset_card_of_nodup hLnd]
    have h2 := ncard_le_ncard hsub hfin
    omega
  obtain ⟨y, hyL, hyT⟩ := hy
  obtain ⟨x, hx⟩ := hDne
  refine false_of_closed (hpc T hT) (D := D) (fun z hz => ⟨hDR hz, disjoint_left.mp hDT hz⟩) hx
    ⟨hLR' y hyL, hyT⟩ (hLD y hyL) ?_
  intro a ha b hb hab
  exact (hcl a ha b hb.1 hab).resolve_right hb.2

/-- A society whose list `L` has three entries has no cross. -/
theorem society_not_cross (hlen : L.length = 3) :
    ¬ ∃ Q₁ Q₂ : Graph γ (Sym2 γ), (society K R L hnd hne hLR).IsCross Q₁ Q₂ := by
  rintro ⟨Q₁, Q₂, -, s₁, t₁, s₂, t₂, -, -, hcr⟩
  have key : ∀ M : List γ, M.length = 4 → (society K R L hnd hne hLR).Ω.IsClockwiseSeq M →
      False := by
    intro M hM hcw
    have hsub : M ⊆ L := fun x hx => hcw.2.1 x hx
    have := (List.subperm_of_subset hcw.1 hsub).length_le
    omega
  rcases hcr with h | h
  · exact key _ rfl h
  · exact key _ rfl h

/-- Copy a plane embedding to a graph with fewer edges on `R`. -/
def planeEmbeddingMono {G G' : SimpleGraph γ} {R : Set γ} (φ : HP25.PlaneEmbedding G R)
    (h : ∀ u ∈ R, ∀ v ∈ R, G'.Adj u v → G.Adj u v) : HP25.PlaneEmbedding G' R where
  pt := φ.pt
  line := φ.line
  finite := φ.finite
  injOn := φ.injOn
  line_comm := φ.line_comm
  isLine u hu v hv huv := φ.isLine u hu v hv (h u hu v hv huv)
  inter u hu v hv u' hu' v' hv' huv huv' hne :=
    φ.inter u hu v hv u' hu' v' hv' (h u hu v hv huv) (h u' hu' v' hv' huv') hne
  avoid u hu v hv huv w hw := φ.avoid u hu v hv (h u hu v hv huv) w hw

/-- A rural society with at least three entries in `L` gives a plane embedding of `K` restricted to
`R`. -/
theorem planeEmbedding_of_rural (h3 : 3 ≤ L.length)
    (hr : (society K R L hnd hne hLR).IsRuralSociety) :
    Nonempty (HP25.PlaneEmbedding (HP25.restrict K R) R) := by
  classical
  obtain ⟨Ω₀, h₀, -, hrur⟩ := hr
  have hbar : 3 ≤ (society K R L hnd hne hLR).Ω.bar.ncard := by
    have : (society K R L hnd hne hLR).Ω.bar = (L.toFinset : Set γ) := by
      rw [society_bar]; ext; simp
    rw [this, ncard_coe_finset, List.toFinset_card_of_nodup hnd]
    exact h3
  obtain ⟨φ, -⟩ := HP25.exists_planeEmbedding hrur (sGraph_isSimpleGraph K R) hbar
    (HP25.restrict K R) (fun u w h => ⟨s(u, w), sGraph_isLink_of_adj h.1 h.2.1 h.2.2⟩)
  exact ⟨φ⟩

end GraphMinor.Wagner
