module

public import GraphMinor.GM08.Section11AB

/-!
# The simulation of `Γ_1` in `Γ_2` in (11.2)

In the proof of Graph Minors VIII, (11.2) the simulation of the portraits gives a simulation of
the graph of `Γ_1` in the graph of `Γ_2`. Here we put the pieces together.

* A vertex `v` of `Γ_1` is sent to `mv v`. This is the set `partA v ∪ partB v` from
  `Section11AB.lean` (empty unless `v` is a node), together with the branch sets of `v` in the
  simulations of the rings `Σ_i` of `Γ_1` that contain `v`.
* An edge `e` of `Γ_1` is sent to `me e`. If `e` is inside a ring `F_i` of `Γ_1`, this is its
  image in the simulation of that ring. Otherwise `e` is an edge of `Γ_0`, and its image is the
  edge of `Γ_2` in the image of the cell of `e`.

The hypotheses are collected in `ModelSetting`. They are proved from the portraits in
`Section11Data.lean`. The result is `ModelSetting.isMinorModel`.
-/

public section

namespace GraphMinor
namespace GM08

open Set Topology Surface Graph

universe u

/-- An edge of the graph of a drawing is incident with exactly the vertices in its closure. -/
theorem toGraph_inc_iff {S : Type u} [TopologicalSpace S] {Γ : Drawing S} {e : Set S} {x : S} :
    Γ.toGraph.Inc e x ↔ e ∈ Γ.E ∧ x ∈ closure e ∩ Γ.V := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨hy.1, ?_⟩
    rw [hy.2.2.2]
    exact mem_insert x {y}
  · rintro ⟨he, hx⟩
    obtain ⟨a, b, hl⟩ := Γ.toGraph.exists_isLink_of_mem_edgeSet he
    have hx' : x ∈ ({a, b} : Set S) := hl.2.2.2 ▸ hx
    rcases hx' with h | h
    · rw [h]
      exact ⟨b, hl⟩
    · rw [mem_singleton_iff] at h
      rw [h]
      exact ⟨a, hl.symm⟩

/-- A loop at `v` is an edge whose only end is `v`. -/
theorem isLoopAt_iff_inc {α β : Type*} {G : Graph α β} {e : β} {v : α} :
    G.IsLoopAt e v ↔ G.Inc e v ∧ ∀ w, G.Inc e w → w = v := by
  constructor
  · intro h
    refine ⟨⟨v, h⟩, fun w hw => ?_⟩
    rcases hw.eq_or_eq_of_isLink h with h' | h' <;> exact h'
  · rintro ⟨⟨y, hy⟩, hall⟩
    have := hall y hy.inc_right
    subst this
    exact hy

variable {S : Type u} [TopologicalSpace S] [T1Space S]

/-- A point of the disc of `F_{j'}` that is inside `F_j` forces `j = j'`. -/
theorem disc_eq_of_inside (hS : IsClosedDisc (univ : Set S)) {Γ : Drawing S} {t : ℕ}
    {F : Fin t → Set S} (hF : IsFoundation Γ univ F) {j j' : Fin t} {x : S}
    (hx : x ∈ F j' ∪ insideSet (F j')) (hin : x ∈ insideSet (F j)) : j = j' := by
  rcases hx with hx | hx
  · exact absurd hin (hF.not_inside_of_mem hS hx j)
  · by_contra hne
    exact Set.disjoint_left.mp (hF.disjoint_inside hne) hin hx

theorem linkRel_reflTransGen_symm {Γ : Drawing S} {Z : Set S} {Eb : Set (Set S)} {p q : S}
    (h : Relation.ReflTransGen (linkRel Γ Z Eb) p q) :
    Relation.ReflTransGen (linkRel Γ Z Eb) q p := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (linkRel_symm hbc) ih

/-- The hypotheses for the simulation of `Γ_1` in `Γ_2`. Here `π` sends the rings of `Γ_1` to
the rings of `Γ_2` (through `σ_e`), `R_1 i` and `R_2 j` are the parts of `Γ_1` and `Γ_2` in the
discs of their rings, `(ηR i, εR i)` simulates `R_1 i` in `R_2 (π i)`, and `partner e` is the edge
of `Γ_2` in the image of the cell of an edge `e` of `Γ_0`. -/
structure ModelSetting (Γ₁ Γ₂ : Drawing S) {t₁ t₂ : ℕ} (F₁ : Fin t₁ → Set S)
    (F₂ : Fin t₂ → Set S) (Ξ : Drawing S) (σv : S → Graph S (Set S)) (Ξ' : Fin t₂ → Drawing S)
    (π : Fin t₁ → Fin t₂) (R₁ : Fin t₁ → Graph S (Set S)) (R₂ : Fin t₂ → Graph S (Set S))
    (ηR : Fin t₁ → S → Set S) (εR : Fin t₁ → Set S → Set S) (partner : Set S → Set S) :
    Prop where
  xi : XiSetting Ξ σv (ringNodes Γ₁ F₁) Γ₂ F₂ Ξ' (range π)ᶜ
  foundation : IsFoundation Γ₁ univ F₁
  π_inj : Function.Injective π
  Ξ'_E : ∀ j ∈ (range π)ᶜ, ∀ e ∈ (Ξ' j).E, e ⊆ insideSet (F₂ j)
  R₁_le : ∀ i, R₁ i ≤ Γ₁.toGraph
  R₁_V : ∀ i, V(R₁ i) = Γ₁.V ∩ (F₁ i ∪ insideSet (F₁ i))
  R₁_E : ∀ i, E(R₁ i) = edgesInsideOArc Γ₁ univ (F₁ i)
  R₂_le : ∀ j, R₂ j ≤ Γ₂.toGraph
  R₂_V : ∀ j, V(R₂ j) = Γ₂.V ∩ (F₂ j ∪ insideSet (F₂ j))
  R₂_E : ∀ j, E(R₂ j) = edgesInsideOArc Γ₂ univ (F₂ j)
  ring : ∀ i, IsMinorModel (R₁ i) (R₂ (π i)) (ηR i) (εR i)
  ring_roots : ∀ i, ∀ z ∈ Γ₂.V ∩ F₂ (π i), ∃ v ∈ Γ₁.V ∩ F₁ i,
    z ∈ ηR i v ∧ z ∈ partA σv (ringNodes Γ₁ F₁) v
  ring_join : ∀ i, ∀ v ∈ Γ₁.V ∩ F₁ i, ∃ z ∈ ηR i v, z ∈ partA σv (ringNodes Γ₁ F₁) v
  partner_mem : ∀ e ∈ ringEdges Γ₁ F₁, partner e ∈ ringEdges Γ₂ F₂
  partner_inj : InjOn partner (ringEdges Γ₁ F₁)
  partner_ends : ∀ e ∈ ringEdges Γ₁ F₁, ∃ l₁ l₂ : List S,
    {x | x ∈ l₁} = closure e ∩ Γ₁.V ∧ {x | x ∈ l₂} = closure (partner e) ∩ Γ₂.V ∧
    l₁.length = l₂.length ∧ ∀ (n : ℕ) (h₁ : n < l₁.length) (h₂ : n < l₂.length),
      l₂[n] ∈ partA σv (ringNodes Γ₁ F₁) l₁[n]
  step : ∀ s ∈ ringNodes Γ₁ F₁, ∀ f p q, (σv s).IsLink f p q → p = q ∨
    (∃ e' ∈ ringEdges Γ₂ F₂, e' ∉ partner '' ringEdges Γ₁ F₁ ∧ Γ₂.toGraph.IsLink e' p q) ∨
    ∃ j ∈ (range π)ᶜ, f ⊆ (F₂ j ∪ insideSet (F₂ j)) \ ringNodes Γ₂ F₂ ∧ p ∈ F₂ j ∧ q ∈ F₂ j

/-- The branch set of a vertex `v` of `Γ_1`. -/
@[expose] def mv (σv : S → Graph S (Set S)) (Γ₁ : Drawing S) {t₁ t₂ : ℕ} (F₁ : Fin t₁ → Set S)
    (F₂ : Fin t₂ → Set S) (Ξ' : Fin t₂ → Drawing S) (π : Fin t₁ → Fin t₂)
    (R₁ : Fin t₁ → Graph S (Set S)) (ηR : Fin t₁ → S → Set S) (v : S) : Set S :=
  partA σv (ringNodes Γ₁ F₁) v ∪ partB σv (ringNodes Γ₁ F₁) F₂ Ξ' (range π)ᶜ v ∪
    ⋃ i, ⋃ (_ : v ∈ V(R₁ i)), ηR i v

open Classical in
/-- The image of an edge `e` of `Γ_1`. -/
@[expose] noncomputable def me {t₁ : ℕ} (F₁ : Fin t₁ → Set S) (εR : Fin t₁ → Set S → Set S)
    (partner : Set S → Set S) (e : Set S) : Set S :=
  if h : ∃ i, e ⊆ insideSet (F₁ i) then εR h.choose e else partner e

variable {Γ₁ Γ₂ : Drawing S} {t₁ t₂ : ℕ} {F₁ : Fin t₁ → Set S} {F₂ : Fin t₂ → Set S}
  {Ξ : Drawing S} {σv : S → Graph S (Set S)} {Ξ' : Fin t₂ → Drawing S} {π : Fin t₁ → Fin t₂}
  {R₁ : Fin t₁ → Graph S (Set S)} {R₂ : Fin t₂ → Graph S (Set S)} {ηR : Fin t₁ → S → Set S}
  {εR : Fin t₁ → Set S → Set S} {partner : Set S → Set S}

namespace ModelSetting

variable (h : ModelSetting Γ₁ Γ₂ F₁ F₂ Ξ σv Ξ' π R₁ R₂ ηR εR partner)
include h

theorem mv_subset (v : S) : mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR v ⊆ Γ₂.V := by
  rintro x ((ha | hb) | hr)
  · exact (partA_subset h.xi v ha).1
  · obtain ⟨j, hj, -, -, -, hz, -⟩ := hb
    exact (h.xi.sub j hj).1 hz
  · obtain ⟨i, hv, hx⟩ := mem_iUnion₂.mp hr
    have := (h.ring i).vertex_subset v hv hx
    rw [h.R₂_V] at this
    exact this.1

theorem partA_subset_mv (v : S) :
    partA σv (ringNodes Γ₁ F₁) v ⊆ mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR v :=
  fun _ hx => Or.inl (Or.inl hx)

/-- A point of `V(Γ_2) ∩ F_{π i}` lies in `partA` of the vertex of `F_i` whose branch set in the
ring simulation contains it. -/
theorem ring_vertex {i : Fin t₁} {x : S} (hxF : x ∈ Γ₂.V ∩ F₂ (π i)) {v : S}
    (hv : v ∈ V(R₁ i)) (hxr : x ∈ ηR i v) : x ∈ partA σv (ringNodes Γ₁ F₁) v := by
  obtain ⟨w, hw, hxw, hxa⟩ := h.ring_roots i x hxF
  have hwR : w ∈ V(R₁ i) := by
    rw [h.R₁_V]
    exact ⟨hw.1, Or.inl hw.2⟩
  have : w = v := by
    by_contra hne
    exact Set.disjoint_left.mp ((h.ring i).vertex_disjoint w hwR v hv hne) hxw hxr
  subst this
  exact hxa

/-- A node of `Γ_2` in a branch set lies in its `partA` part. -/
theorem partA_of_mv_node {v x : S} (hx : x ∈ mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR v)
    (hxN : x ∈ ringNodes Γ₂ F₂) : x ∈ partA σv (ringNodes Γ₁ F₁) v := by
  rcases hx with (ha | hb) | hr
  · exact ha
  · exact partA_of_partB h.xi hb hxN
  · obtain ⟨i, hv, hxr⟩ := mem_iUnion₂.mp hr
    have hxV := (h.ring i).vertex_subset v hv hxr
    rw [h.R₂_V] at hxV
    have hxF : x ∈ Γ₂.V ∩ F₂ (π i) := by
      rw [← h.xi.foundation.ring_inter_nodes h.xi.hS]
      exact ⟨hxV.2, hxN⟩
    exact h.ring_vertex hxF hv hxr

/-- A point of a branch set in the disc of an image ring `F_{π i}` lies in the branch set of the
ring simulation. -/
theorem ring_of_mv {v x : S} {i : Fin t₁} (hx : x ∈ mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR v)
    (hxR : x ∈ V(R₂ (π i))) : v ∈ V(R₁ i) ∧ x ∈ ηR i v := by
  rw [h.R₂_V] at hxR
  rcases mem_ringNodes_or_inside (F := F₂) hxR.1 with hxN | ⟨j, hj⟩
  · have hxa := h.partA_of_mv_node hx hxN
    have hxF : x ∈ Γ₂.V ∩ F₂ (π i) := by
      rw [← h.xi.foundation.ring_inter_nodes h.xi.hS]
      exact ⟨hxR.2, hxN⟩
    obtain ⟨w, hw, hxw, hxa'⟩ := h.ring_roots i x hxF
    have := eq_of_partA h.xi hxa' hxa
    subst this
    refine ⟨?_, hxw⟩
    rw [h.R₁_V]
    exact ⟨hw.1, Or.inl hw.2⟩
  · have hji : j = π i := disc_eq_of_inside h.xi.hS h.xi.foundation hxR.2 hj
    subst hji
    rcases hx with (ha | hb) | hr
    · exact absurd hj ((partA_subset h.xi v ha).2 (π i))
    · obtain ⟨j', hj', -, -, -, hz, -⟩ := hb
      have hin := inside_of_mem_Ξ' h.xi hj' hz (fun hN => hN.2 (π i) hj)
      have : π i = j' := by
        by_contra hne
        exact Set.disjoint_left.mp (h.xi.foundation.disjoint_inside hne) hj hin
      exact absurd ⟨i, this⟩ hj'
    · obtain ⟨i', hv, hxr⟩ := mem_iUnion₂.mp hr
      have hxR' := (h.ring i').vertex_subset v hv hxr
      rw [h.R₂_V] at hxR'
      have := h.π_inj (disc_eq_of_inside h.xi.hS h.xi.foundation hxR'.2 hj)
      subst this
      exact ⟨hv, hxr⟩

/-- A point of a branch set inside a ring `F_j` that is not an image ring lies in `partB`. -/
theorem partB_of_mv {v x : S} {j : Fin t₂} (hx : x ∈ mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR v)
    (hj : j ∈ (range π)ᶜ) (hin : x ∈ insideSet (F₂ j)) :
    x ∈ partB σv (ringNodes Γ₁ F₁) F₂ Ξ' (range π)ᶜ v := by
  rcases hx with (ha | hb) | hr
  · exact absurd hin ((partA_subset h.xi v ha).2 j)
  · exact hb
  · obtain ⟨i, hv, hxr⟩ := mem_iUnion₂.mp hr
    have hxR := (h.ring i).vertex_subset v hv hxr
    rw [h.R₂_V] at hxR
    exact absurd ⟨i, (disc_eq_of_inside h.xi.hS h.xi.foundation hxR.2 hin).symm⟩ hj

/-- Branch sets of distinct vertices are disjoint. -/
theorem mv_disjoint {v w : S} (hne : v ≠ w) :
    Disjoint (mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR v) (mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR w) := by
  refine Set.disjoint_left.mpr fun x hv hw => ?_
  rcases mem_ringNodes_or_inside (F := F₂) (h.mv_subset v hv) with hxN | ⟨j, hj⟩
  · exact hne (eq_of_partA h.xi (h.partA_of_mv_node hv hxN) (h.partA_of_mv_node hw hxN))
  · by_cases hjr : j ∈ range π
    · obtain ⟨i, rfl⟩ := hjr
      have hxR : x ∈ V(R₂ (π i)) := by
        rw [h.R₂_V]
        exact ⟨h.mv_subset v hv, Or.inr hj⟩
      have h1 := h.ring_of_mv hv hxR
      have h2 := h.ring_of_mv hw hxR
      exact Set.disjoint_left.mp ((h.ring i).vertex_disjoint v h1.1 w h2.1 hne) h1.2 h2.2
    · exact hne (eq_of_partAB h.xi (Or.inr (h.partB_of_mv hv hjr hj))
        (Or.inr (h.partB_of_mv hw hjr hj)))

theorem edge_R₁ {e : Set S} {i : Fin t₁} (he : e ∈ Γ₁.E) (hi : e ⊆ insideSet (F₁ i)) :
    e ∈ E(R₁ i) := by
  rw [h.R₁_E]
  exact ⟨he, hi⟩

theorem εR_mem {e : Set S} {i : Fin t₁} (he : e ∈ E(R₁ i)) :
    εR i e ∈ Γ₂.E ∧ εR i e ⊆ insideSet (F₂ (π i)) := by
  have := (h.ring i).edge_mem e he
  rw [h.R₂_E] at this
  exact ⟨this.1, this.2⟩

theorem me_of_inside {e : Set S} {i : Fin t₁} (he : e ∈ Γ₁.E) (hi : e ⊆ insideSet (F₁ i)) :
    me F₁ εR partner e = εR i e := by
  classical
  have hex : ∃ i, e ⊆ insideSet (F₁ i) := ⟨i, hi⟩
  simp only [me, dite_eq_left hex]
  rw [h.foundation.eq_of_inside he hex.choose_spec hi]

theorem me_of_ringEdges {e : Set S} (he : e ∈ ringEdges Γ₁ F₁) :
    me F₁ εR partner e = partner e := by
  classical
  have hex : ¬ ∃ i, e ⊆ insideSet (F₁ i) := fun ⟨i, hi⟩ => he.2 i hi
  simp [me, hex]

theorem me_mem {e : Set S} (he : e ∈ Γ₁.E) : me F₁ εR partner e ∈ Γ₂.E := by
  rcases mem_ringEdges_or_inside (F := F₁) he with hr | ⟨i, hi⟩
  · rw [h.me_of_ringEdges hr]
    exact (h.partner_mem e hr).1
  · rw [h.me_of_inside he hi]
    exact (h.εR_mem (h.edge_R₁ he hi)).1

/-- An image edge inside a ring `F_j` of `Γ_2` comes from a ring `F_i` with `π i = j`. -/
theorem eq_of_me_inside {e : Set S} {j : Fin t₂} (he : e ∈ Γ₁.E)
    (hj : me F₁ εR partner e ⊆ insideSet (F₂ j)) :
    ∃ i, π i = j ∧ e ∈ E(R₁ i) ∧ me F₁ εR partner e = εR i e := by
  rcases mem_ringEdges_or_inside (F := F₁) he with hr | ⟨i, hi⟩
  · rw [h.me_of_ringEdges hr] at hj
    exact absurd hj ((h.partner_mem e hr).2 j)
  · have hR := h.edge_R₁ he hi
    rw [h.me_of_inside he hi] at hj ⊢
    exact ⟨i, h.xi.foundation.eq_of_inside (h.εR_mem hR).1 (h.εR_mem hR).2 hj, hR, rfl⟩

theorem me_injOn : InjOn (me F₁ εR partner) Γ₁.E := by
  intro e₁ he₁ e₂ he₂ heq
  rcases mem_ringEdges_or_inside (F := F₁) he₁ with hr₁ | ⟨i₁, hi₁⟩
  · rcases mem_ringEdges_or_inside (F := F₁) he₂ with hr₂ | ⟨i₂, hi₂⟩
    · rw [h.me_of_ringEdges hr₁, h.me_of_ringEdges hr₂] at heq
      exact h.partner_inj hr₁ hr₂ heq
    · rw [h.me_of_ringEdges hr₁, h.me_of_inside he₂ hi₂] at heq
      exact absurd (heq ▸ (h.εR_mem (h.edge_R₁ he₂ hi₂)).2) ((h.partner_mem e₁ hr₁).2 (π i₂))
  · rcases mem_ringEdges_or_inside (F := F₁) he₂ with hr₂ | ⟨i₂, hi₂⟩
    · rw [h.me_of_inside he₁ hi₁, h.me_of_ringEdges hr₂] at heq
      exact absurd (heq.symm ▸ (h.εR_mem (h.edge_R₁ he₁ hi₁)).2)
        ((h.partner_mem e₂ hr₂).2 (π i₁))
    · have hR₁ := h.edge_R₁ he₁ hi₁
      have hR₂ := h.edge_R₁ he₂ hi₂
      rw [h.me_of_inside he₁ hi₁, h.me_of_inside he₂ hi₂] at heq
      have hπ : π i₁ = π i₂ := h.xi.foundation.eq_of_inside (h.εR_mem hR₁).1
        (h.εR_mem hR₁).2 (heq ▸ (h.εR_mem hR₂).2)
      have := h.π_inj hπ
      subst this
      exact (h.ring i₁).edge_injOn hR₁ hR₂ heq

theorem inc_iff {v : S} (hv : v ∈ Γ₁.V) {e : Set S} (he : e ∈ Γ₁.E) :
    Γ₁.toGraph.Inc e v ↔
      ∃ x ∈ mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR v, Γ₂.toGraph.Inc (me F₁ εR partner e) x := by
  rcases mem_ringEdges_or_inside (F := F₁) he with hr | ⟨i, hi⟩
  · rw [h.me_of_ringEdges hr]
    obtain ⟨l₁, l₂, hl₁, hl₂, hlen, hl⟩ := h.partner_ends e hr
    constructor
    · intro hinc
      have hv1 : v ∈ {x | x ∈ l₁} := by
        rw [hl₁]
        exact (toGraph_inc_iff.mp hinc).2
      obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hv1
      have hn2 : n < l₂.length := by omega
      refine ⟨l₂[n], h.partA_subset_mv _ (hl n hn hn2),
        toGraph_inc_iff.mpr ⟨(h.partner_mem e hr).1, ?_⟩⟩
      rw [← hl₂]
      exact List.getElem_mem _
    · rintro ⟨x, hx, hxi⟩
      have hx2 : x ∈ {x | x ∈ l₂} := by
        rw [hl₂]
        exact (toGraph_inc_iff.mp hxi).2
      obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hx2
      have hn1 : n < l₁.length := by omega
      have ha := hl n hn1 hn
      have hv' := eq_of_partA h.xi ha (h.partA_of_mv_node hx (partA_subset h.xi _ ha))
      refine toGraph_inc_iff.mpr ⟨he, ?_⟩
      rw [← hv', ← hl₁]
      exact List.getElem_mem _
  · have hR := h.edge_R₁ he hi
    have hεR : εR i e ∈ E(R₂ (π i)) := (h.ring i).edge_mem e hR
    rw [h.me_of_inside he hi, ← IsSubgraph.inc_congr (h.R₁_le i) hR]
    constructor
    · intro hinc
      have hvR : v ∈ V(R₁ i) := hinc.vertex_mem
      obtain ⟨x, hx, hxi⟩ := ((h.ring i).inc_iff v hvR e hR).mp hinc
      exact ⟨x, Or.inr (mem_iUnion₂.mpr ⟨i, hvR, hx⟩), hxi.mono (h.R₂_le _)⟩
    · rintro ⟨x, hx, hxi⟩
      have hxi' : (R₂ (π i)).Inc (εR i e) x := (IsSubgraph.inc_congr (h.R₂_le _) hεR).mpr hxi
      obtain ⟨hvR, hxr⟩ := h.ring_of_mv hx hxi'.vertex_mem
      exact ((h.ring i).inc_iff v hvR e hR).mpr ⟨x, hxr, hxi'⟩

theorem isLoopAt_iff {v : S} (hv : v ∈ Γ₁.V) {e : Set S} (he : e ∈ Γ₁.E) :
    Γ₁.toGraph.IsLoopAt e v ↔
      ∀ x, Γ₂.toGraph.Inc (me F₁ εR partner e) x → x ∈ mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR v := by
  rcases mem_ringEdges_or_inside (F := F₁) he with hr | ⟨i, hi⟩
  · rw [h.me_of_ringEdges hr, isLoopAt_iff_inc]
    obtain ⟨l₁, l₂, hl₁, hl₂, hlen, hl⟩ := h.partner_ends e hr
    have hend₁ : ∀ n (h₁ : n < l₁.length), Γ₁.toGraph.Inc e l₁[n] := fun n h₁ =>
      toGraph_inc_iff.mpr ⟨he, by rw [← hl₁]; exact List.getElem_mem _⟩
    have hend₂ : ∀ n (h₂ : n < l₂.length), Γ₂.toGraph.Inc (partner e) l₂[n] := fun n h₂ =>
      toGraph_inc_iff.mpr ⟨(h.partner_mem e hr).1, by rw [← hl₂]; exact List.getElem_mem _⟩
    constructor
    · rintro ⟨-, hall⟩ x hxi
      have hx2 : x ∈ {x | x ∈ l₂} := by
        rw [hl₂]
        exact (toGraph_inc_iff.mp hxi).2
      obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hx2
      have hn1 : n < l₁.length := by omega
      have hv' := hall _ (hend₁ n hn1)
      have ha := hl n hn1 hn
      rw [hv'] at ha
      exact h.partA_subset_mv _ ha
    · intro hall
      have key : ∀ n (h₁ : n < l₁.length) (h₂ : n < l₂.length), l₁[n] = v := fun n h₁ h₂ =>
        eq_of_partA h.xi (hl n h₁ h₂)
          (h.partA_of_mv_node (hall _ (hend₂ n h₂)) (partA_subset h.xi _ (hl n h₁ h₂)))
      obtain ⟨p, q, hpq⟩ := Γ₂.toGraph.exists_isLink_of_mem_edgeSet (h.partner_mem e hr).1
      refine ⟨?_, fun w hw => ?_⟩
      · have hp : p ∈ {x | x ∈ l₂} := by
          rw [hl₂]
          exact (toGraph_inc_iff.mp hpq.inc_left).2
        obtain ⟨n, hn, -⟩ := List.getElem_of_mem hp
        have hn1 : n < l₁.length := by omega
        rw [← key n hn1 hn]
        exact hend₁ n hn1
      · have hw1 : w ∈ {x | x ∈ l₁} := by
          rw [hl₁]
          exact (toGraph_inc_iff.mp hw).2
        obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hw1
        exact key n hn (by omega)
  · have hR := h.edge_R₁ he hi
    have hεR : εR i e ∈ E(R₂ (π i)) := (h.ring i).edge_mem e hR
    rw [h.me_of_inside he hi, ← IsSubgraph.isLoopAt_congr (h.R₁_le i) hR]
    constructor
    · intro hl x hxi
      have hvR : v ∈ V(R₁ i) := hl.left_mem
      have hxi' : (R₂ (π i)).Inc (εR i e) x := (IsSubgraph.inc_congr (h.R₂_le _) hεR).mpr hxi
      exact Or.inr (mem_iUnion₂.mpr ⟨i, hvR, ((h.ring i).isLoopAt_iff v hvR e hR).mp hl x hxi'⟩)
    · intro hall
      obtain ⟨p, q, hpq⟩ := (R₂ (π i)).exists_isLink_of_mem_edgeSet hεR
      have hvR : v ∈ V(R₁ i) :=
        (h.ring_of_mv (hall p (hpq.inc_left.mono (h.R₂_le _))) hpq.left_mem).1
      refine ((h.ring i).isLoopAt_iff v hvR e hR).mpr fun x hxi => ?_
      exact (h.ring_of_mv (hall x (hxi.mono (h.R₂_le _))) hxi.vertex_mem).2

theorem notMem_image_of_inside {e : Set S} {j : Fin t₂} (hj : j ∈ (range π)ᶜ)
    (he : e ⊆ insideSet (F₂ j)) : e ∉ me F₁ εR partner '' Γ₁.E := by
  rintro ⟨f, hf, rfl⟩
  obtain ⟨i, hij, -⟩ := h.eq_of_me_inside hf he
  exact hj ⟨i, hij⟩

theorem notMem_image_of_ringEdges {e : Set S} (he : e ∈ ringEdges Γ₂ F₂)
    (hp : e ∉ partner '' ringEdges Γ₁ F₁) : e ∉ me F₁ εR partner '' Γ₁.E := by
  rintro ⟨f, hf, rfl⟩
  rcases mem_ringEdges_or_inside (F := F₁) hf with hr | ⟨i, hi⟩
  · rw [h.me_of_ringEdges hr] at hp
    exact hp ⟨f, hr, rfl⟩
  · rw [h.me_of_inside hf hi] at he
    exact he.2 (π i) (h.εR_mem (h.edge_R₁ hf hi)).2

/-- The branch set of `v` in a ring simulation is joined by links of `Γ_2` that avoid the image
edges. -/
theorem ring_linked {v : S} {i : Fin t₁} (hv : v ∈ V(R₁ i)) :
    ∀ x ∈ ηR i v, ∀ y ∈ ηR i v, Relation.ReflTransGen
      (linkRel Γ₂ (mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR v) (me F₁ εR partner '' Γ₁.E)) x y := by
  obtain ⟨K, hK, hKV, hKc⟩ := (h.ring i).connected v hv
  intro x hx y hy
  refine Relation.ReflTransGen.mono ?_ x y (hKc.2 x (hKV ▸ hx) y (hKV ▸ hy))
  rintro a b ⟨e, hl⟩
  have hl' := hl.mono hK
  rw [deleteEdges_isLink] at hl'
  obtain ⟨hl2, hne⟩ := hl'
  refine ⟨Or.inr (mem_iUnion₂.mpr ⟨i, hv, hKV ▸ hl.left_mem⟩),
    Or.inr (mem_iUnion₂.mpr ⟨i, hv, hKV ▸ hl.right_mem⟩), e, ?_, hl2.mono (h.R₂_le _)⟩
  rintro ⟨f, hf, hfe⟩
  have heR : e ∈ E(R₂ (π i)) := hl2.edge_mem
  have hein : e ⊆ insideSet (F₂ (π i)) := by
    rw [h.R₂_E] at heR
    exact heR.2
  rw [← hfe] at hein
  obtain ⟨i', hi', hfR, hme⟩ := h.eq_of_me_inside hf hein
  have := h.π_inj hi'
  subst this
  exact hne ⟨f, hfR, by rw [← hme, hfe]⟩

/-- For a node `v`, the set `partA v ∪ partB v` is joined by links of `Γ_2` that avoid the image
edges. -/
theorem ab_linked {v : S} (hs : v ∈ ringNodes Γ₁ F₁) :
    ∀ p ∈ partA σv (ringNodes Γ₁ F₁) v ∪ partB σv (ringNodes Γ₁ F₁) F₂ Ξ' (range π)ᶜ v,
    ∀ q ∈ partA σv (ringNodes Γ₁ F₁) v ∪ partB σv (ringNodes Γ₁ F₁) F₂ Ξ' (range π)ᶜ v,
      Relation.ReflTransGen
        (linkRel Γ₂ (mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR v) (me F₁ εR partner '' Γ₁.E)) p q := by
  intro p hp q hq
  refine Relation.ReflTransGen.mono ?_ p q (reflTransGen_partAB h.xi hs
    (Eb := me F₁ εR partner '' Γ₁.E) ?_ ?_ p hp q hq)
  · rintro a b ⟨ha, hb, hab⟩
    exact ⟨Or.inl ha, Or.inl hb, hab⟩
  · intro j hj e he
    exact h.notMem_image_of_inside hj (h.Ξ'_E j hj e he)
  · intro f p q hl
    rcases h.step v hs f p q hl with hpq | ⟨e', he', hp', hl'⟩ | hring
    · exact Or.inl hpq
    · exact Or.inr (Or.inl ⟨e', h.notMem_image_of_ringEdges he' hp', hl'⟩)
    · exact Or.inr (Or.inr hring)

/-- A branch set is joined by links of `Γ_2` that avoid the image edges. -/
theorem mv_linked {v : S} (hv : v ∈ Γ₁.V) :
    ∀ x ∈ mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR v, ∀ y ∈ mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR v,
      Relation.ReflTransGen
        (linkRel Γ₂ (mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR v) (me F₁ εR partner '' Γ₁.E)) x y := by
  intro x hx y hy
  rcases mem_ringNodes_or_inside (F := F₁) hv with hvN | ⟨i, hi⟩
  · obtain ⟨a, ha⟩ := (h.xi.comp v hvN).2.1.1
    have haA : a ∈ partA σv (ringNodes Γ₁ F₁) v := ⟨hvN, ha⟩
    have hub : ∀ z ∈ mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR v, Relation.ReflTransGen
        (linkRel Γ₂ (mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR v) (me F₁ εR partner '' Γ₁.E)) a z := by
      rintro z (hz | hz)
      · exact h.ab_linked hvN a (Or.inl haA) z hz
      · obtain ⟨i, hvR, hzr⟩ := mem_iUnion₂.mp hz
        have hvF : v ∈ Γ₁.V ∩ F₁ i := by
          rw [← h.foundation.ring_inter_nodes h.xi.hS]
          rw [h.R₁_V] at hvR
          exact ⟨hvR.2, hvN⟩
        obtain ⟨z₀, hz₀, hz₀a⟩ := h.ring_join i v hvF
        exact (h.ab_linked hvN a (Or.inl haA) z₀ (Or.inl hz₀a)).trans
          (h.ring_linked hvR z₀ hz₀ z hzr)
    exact (linkRel_reflTransGen_symm (hub x hx)).trans (hub y hy)
  · have hvR : v ∈ V(R₁ i) := by
      rw [h.R₁_V]
      exact ⟨hv, Or.inr hi⟩
    have hsub : ∀ z ∈ mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR v, z ∈ ηR i v := by
      rintro z ((hz | hz) | hz)
      · exact absurd hi (hz.1.2 i)
      · obtain ⟨j, -, u, hu, -⟩ := hz
        exact absurd hi (hu.1.2 i)
      · obtain ⟨i', hvR', hzr⟩ := mem_iUnion₂.mp hz
        rw [h.R₁_V] at hvR'
        have := disc_eq_of_inside h.xi.hS h.foundation hvR'.2 hi
        subst this
        exact hzr
    exact h.ring_linked hvR x (hsub x hx) y (hsub y hy)

theorem mv_nonempty {v : S} (hv : v ∈ Γ₁.V) : (mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR v).Nonempty := by
  rcases mem_ringNodes_or_inside (F := F₁) hv with hvN | ⟨i, hi⟩
  · obtain ⟨a, ha⟩ := (h.xi.comp v hvN).2.1.1
    exact ⟨a, h.partA_subset_mv v ⟨hvN, ha⟩⟩
  · have hvR : v ∈ V(R₁ i) := by
      rw [h.R₁_V]
      exact ⟨hv, Or.inr hi⟩
    obtain ⟨x, hx⟩ := (h.ring i).vertex_nonempty v hvR
    exact ⟨x, Or.inr (mem_iUnion₂.mpr ⟨i, hvR, hx⟩)⟩

/-- **The simulation of `Γ_1` in `Γ_2`.** -/
theorem isMinorModel :
    IsMinorModel Γ₁.toGraph Γ₂.toGraph (mv σv Γ₁ F₁ F₂ Ξ' π R₁ ηR) (me F₁ εR partner) where
  vertex_nonempty v hv := h.mv_nonempty hv
  vertex_subset v _ := h.mv_subset v
  edge_mem e he := h.me_mem he
  vertex_disjoint _ _ _ _ hne := h.mv_disjoint hne
  edge_injOn := h.me_injOn
  inc_iff v hv e he := h.inc_iff hv he
  isLoopAt_iff v hv e he := h.isLoopAt_iff hv he
  connected v hv := by
    refine exists_graphConnected_of_reflTransGen (G' := Γ₂.toGraph.deleteEdges
      (me F₁ εR partner '' E(Γ₁.toGraph))) (h.mv_subset v) (h.mv_nonempty hv) ?_
    intro x hx y hy
    refine Relation.ReflTransGen.mono ?_ x y (h.mv_linked hv x hx y hy)
    rintro a b ⟨ha, hb, e, he, hl⟩
    exact ⟨ha, hb, e, by rw [deleteEdges_isLink]; exact ⟨hl, he⟩⟩

end ModelSetting

end GM08
end GraphMinor
