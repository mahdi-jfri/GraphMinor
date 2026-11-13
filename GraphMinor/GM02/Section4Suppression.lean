module

public import GraphMinor.GM02.TopologicalContainment

/-!
# Suppression sequences up to renaming of edges

Graph Minors II, Section 4, page 318, says that `G` topologically contains `H`
when `H` can be obtained from a subgraph of `G` by repeated suppression. The
proofs of (4.2), (4.3) and (4.5) change such a sequence of suppressions: they
rename edges, delete or add a loop, or pass to a subgraph. This file proves
that each change gives a sequence of the same kind.

The isomorphisms here fix every vertex, so we describe them by a map on edge
names (`IsoFixVia`). A suppression may give its new edge the name of the first
removed edge (`IsKeepSuppression`). Every sequence of suppressions can be
replaced by one of this kind, and then no new edge names appear.
-/

@[expose] public section

namespace GraphMinor.GM02

open Graph Set Relation

universe u v

variable {α : Type u} {β : Type v}

/-- An isomorphism from `H` to `L` that fixes every vertex. It is given by the
map `σ` on edge names. -/
def IsoFixVia (σ : β → β) (H L : Graph α β) : Prop :=
  V(H) = V(L) ∧ BijOn σ E(H) E(L) ∧ ∀ e ∈ E(H), ∀ a b, H.IsLink e a b ↔ L.IsLink (σ e) a b

/-- `H` and `L` are isomorphic by an isomorphism that fixes every vertex. -/
def IsoFix (H L : Graph α β) : Prop := ∃ σ : β → β, IsoFixVia σ H L

/-- A suppression whose new edge keeps the name of the first removed edge. -/
def IsKeepSuppression (G H : Graph α β) : Prop :=
  ∃ d : SuppressionData G, d.fresh = d.first ∧ H = d.result

theorem IsKeepSuppression.isSuppression {G H : Graph α β} (h : IsKeepSuppression G H) :
    IsSuppression G H := by
  obtain ⟨d, _, rfl⟩ := h
  exact ⟨d, rfl⟩

theorem reflTransGen_isSuppression_of_keep {K L : Graph α β}
    (h : ReflTransGen IsKeepSuppression K L) : ReflTransGen IsSuppression K L :=
  by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail hstep.isSuppression

/-- Suppressions never add vertices. -/
theorem vertexSet_subset_of_reflTransGen {K L : Graph α β}
    (h : ReflTransGen IsSuppression K L) : V(L) ⊆ V(K) := by
  induction h with
  | refl => exact Subset.refl _
  | tail _ hstep ih => exact hstep.vertexSet_subset.trans ih

/-- Suppressions that keep names use only edge names of the first graph. -/
theorem edgeSet_subset_of_keep {K L : Graph α β}
    (h : ReflTransGen IsKeepSuppression K L) : E(L) ⊆ E(K) := by
  induction h with
  | refl => exact Subset.refl _
  | tail _ hstep ih =>
    obtain ⟨d, hd, rfl⟩ := hstep
    refine Subset.trans ?_ ih
    intro e he
    rcases he with he | he
    · exact he.1
    · rw [Set.mem_singleton_iff.1 he, hd]
      exact d.first_link.edge_mem

theorem IsoFixVia.refl (H : Graph α β) : IsoFixVia id H H :=
  ⟨rfl, bijOn_id _, fun _ _ _ _ => Iff.rfl⟩

theorem IsoFix.refl (H : Graph α β) : IsoFix H H := ⟨id, IsoFixVia.refl H⟩

theorem IsoFixVia.trans {σ τ : β → β} {H K L : Graph α β} (h₁ : IsoFixVia σ H K)
    (h₂ : IsoFixVia τ K L) : IsoFixVia (τ ∘ σ) H L :=
  ⟨h₁.1.trans h₂.1, h₂.2.1.comp h₁.2.1,
    fun e he a b => (h₁.2.2 e he a b).trans (h₂.2.2 _ (h₁.2.1.mapsTo he) a b)⟩

theorem IsoFix.trans {H K L : Graph α β} (h₁ : IsoFix H K) (h₂ : IsoFix K L) : IsoFix H L := by
  obtain ⟨σ, hσ⟩ := h₁
  obtain ⟨τ, hτ⟩ := h₂
  exact ⟨τ ∘ σ, hσ.trans hτ⟩

/-- An isomorphism fixing every vertex gives an edge map as above. -/
theorem isoFix_of_iso {H L : Graph α β} (φ : Iso H L)
    (hφ : ∀ v : V(H), (φ.vertexEquiv v).val = v.val) : IsoFix H L := by
  classical
  have hV : V(H) = V(L) := by
    ext v
    constructor
    · intro hv
      have h := (φ.vertexEquiv ⟨v, hv⟩).property
      rwa [hφ] at h
    · intro hv
      have h := hφ (φ.vertexEquiv.symm ⟨v, hv⟩)
      rw [Equiv.apply_symm_apply] at h
      rw [show v = (φ.vertexEquiv.symm ⟨v, hv⟩).val from h]
      exact (φ.vertexEquiv.symm ⟨v, hv⟩).property
  refine ⟨fun e => if he : e ∈ E(H) then (φ.edgeEquiv ⟨e, he⟩).val else e, hV, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro e he
    simp only [he, ↓reduceDIte]
    exact (φ.edgeEquiv ⟨e, he⟩).property
  · intro e₁ he₁ e₂ he₂ h
    simp only [he₁, he₂, ↓reduceDIte] at h
    have := φ.edgeEquiv.injective (Subtype.ext h)
    exact congrArg Subtype.val this
  · intro f hf
    refine ⟨(φ.edgeEquiv.symm ⟨f, hf⟩).val, (φ.edgeEquiv.symm ⟨f, hf⟩).property, ?_⟩
    simp only [(φ.edgeEquiv.symm ⟨f, hf⟩).property, ↓reduceDIte, Subtype.coe_eta,
      Equiv.apply_symm_apply]
  · intro e he a b
    simp only [he, ↓reduceDIte]
    constructor
    · intro h
      have h' := (φ.isLink_iff ⟨e, he⟩ ⟨a, h.left_mem⟩ ⟨b, h.right_mem⟩).1 h
      rwa [hφ, hφ] at h'
    · intro h
      have ha : a ∈ V(H) := hV ▸ h.left_mem
      have hb : b ∈ V(H) := hV ▸ h.right_mem
      apply (φ.isLink_iff ⟨e, he⟩ ⟨a, ha⟩ ⟨b, hb⟩).2
      rwa [hφ, hφ]

/-- An edge map as above gives an isomorphism fixing every vertex. -/
theorem iso_of_isoFix {H L : Graph α β} (h : IsoFix H L) :
    ∃ φ : Iso H L, ∀ v : V(H), (φ.vertexEquiv v).val = v.val := by
  obtain ⟨σ, hV, hbij, hlink⟩ := h
  refine ⟨⟨⟨fun v => ⟨v.1, hV ▸ v.2⟩, fun v => ⟨v.1, hV.symm ▸ v.2⟩,
    fun _ => rfl, fun _ => rfl⟩, hbij.equiv σ, ?_⟩, fun _ => rfl⟩
  intro e x y
  exact hlink e.1 e.2 x.1 y.1

/-- Topological containment, with the isomorphism given by an edge map. -/
theorem topologicallyContains_iff_isoFix {G H : Graph α β} :
    TopologicallyContains G H ↔
      ∃ K ≤ G, ∃ L, ReflTransGen IsSuppression K L ∧ IsoFix H L := by
  constructor
  · rintro ⟨K, hK, L, hs, φ, hφ⟩
    exact ⟨K, hK, L, hs, isoFix_of_iso φ hφ⟩
  · rintro ⟨K, hK, L, hs, hiso⟩
    obtain ⟨φ, hφ⟩ := iso_of_isoFix hiso
    exact ⟨K, hK, L, hs, φ, hφ⟩

/-- Moving a suppression along an isomorphism that fixes every vertex. The new
edge gets the name of the first removed edge. -/
theorem SuppressionData.transport {M N : Graph α β} {σ : β → β} (hMN : IsoFixVia σ M N)
    (d : SuppressionData M) :
    ∃ d' : SuppressionData N, d'.fresh = d'.first ∧ IsoFix d.result d'.result := by
  classical
  obtain ⟨hV, hbij, hlink⟩ := hMN
  have h1 : d.first ∈ E(M) := d.first_link.edge_mem
  have h2 : d.second ∈ E(M) := d.second_link.edge_mem
  have hne : σ d.first ≠ σ d.second := fun h => d.first_ne_second (hbij.injOn h1 h2 h)
  let d' : SuppressionData N :=
    { vertex := d.vertex
      left := d.left
      right := d.right
      first := σ d.first
      second := σ d.second
      fresh := σ d.first
      first_ne_second := hne
      first_link := (hlink _ h1 _ _).1 d.first_link
      second_link := (hlink _ h2 _ _).1 d.second_link
      vertex_ne_left := d.vertex_ne_left
      vertex_ne_right := d.vertex_ne_right
      incident := by
        rintro e ⟨y, hy⟩
        obtain ⟨e₀, he₀, rfl⟩ := hbij.surjOn hy.edge_mem
        rcases d.incident e₀ ⟨y, (hlink e₀ he₀ _ _).2 hy⟩ with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      fresh_notMem := fun h => h.2 (Or.inl rfl) }
  refine ⟨d', rfl, fun e => if e = d.fresh then σ d.first else σ e, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · change V(M) \ {d.vertex} = V(N) \ {d.vertex}
    rw [hV]
  · rintro e (⟨he, hne'⟩ | he)
    · have hef : e ≠ d.fresh := d.retained_not_fresh he (fun h => hne' (Or.inl h))
        (fun h => hne' (Or.inr h))
      simp only [hef, ite_false]
      refine Or.inl ⟨hbij.mapsTo he, ?_⟩
      rintro (h | h)
      · exact hne' (Or.inl (hbij.injOn he h1 h))
      · exact hne' (Or.inr (hbij.injOn he h2 h))
    · rw [Set.mem_singleton_iff.1 he]
      simp only [ite_true]
      exact Or.inr rfl
  · have hret : ∀ e ∈ E(d.result), e ≠ d.fresh → e ∈ E(M) ∧ e ≠ d.first ∧ e ≠ d.second := by
      rintro e (⟨he, hne'⟩ | he) hef
      · exact ⟨he, fun h => hne' (Or.inl h), fun h => hne' (Or.inr h)⟩
      · exact (hef (Set.mem_singleton_iff.1 he)).elim
    intro e₁ he₁ e₂ he₂ h
    by_cases hf₁ : e₁ = d.fresh <;> by_cases hf₂ : e₂ = d.fresh
    · rw [hf₁, hf₂]
    · obtain ⟨he, hn1, _⟩ := hret e₂ he₂ hf₂
      simp only [hf₁, hf₂, ite_true, ite_false] at h
      exact (hn1 (hbij.injOn h1 he h).symm).elim
    · obtain ⟨he, hn1, _⟩ := hret e₁ he₁ hf₁
      simp only [hf₁, hf₂, ite_true, ite_false] at h
      exact (hn1 (hbij.injOn he h1 h)).elim
    · obtain ⟨he1, _, _⟩ := hret e₁ he₁ hf₁
      obtain ⟨he2, _, _⟩ := hret e₂ he₂ hf₂
      simp only [hf₁, hf₂, ite_false] at h
      exact hbij.injOn he1 he2 h
  · rintro g (⟨hg, hne'⟩ | hg)
    · obtain ⟨e, he, rfl⟩ := hbij.surjOn hg
      have hn1 : e ≠ d.first := fun h => hne' (Or.inl (h ▸ rfl))
      have hn2 : e ≠ d.second := fun h => hne' (Or.inr (h ▸ rfl))
      have hef : e ≠ d.fresh := d.retained_not_fresh he hn1 hn2
      refine ⟨e, Or.inl ⟨he, ?_⟩, by simp only [hef, ite_false]⟩
      rintro (h | h)
      · exact hn1 h
      · exact hn2 h
    · refine ⟨d.fresh, Or.inr rfl, ?_⟩
      simp only [ite_true]
      exact (Set.mem_singleton_iff.1 hg).symm
  · intro e he a b
    by_cases hef : e = d.fresh
    · subst hef
      simp only [ite_true]
      rw [d.fresh_isLink_iff]
      exact (d'.fresh_isLink_iff a b).symm
    · simp only [hef, ite_false]
      have hmem : e ∈ E(M) ∧ e ≠ d.first ∧ e ≠ d.second := by
        rcases he with ⟨he, hne'⟩ | he
        · exact ⟨he, fun h => hne' (Or.inl h), fun h => hne' (Or.inr h)⟩
        · exact (hef (Set.mem_singleton_iff.1 he)).elim
      obtain ⟨heM, hn1, hn2⟩ := hmem
      have hσ1 : σ e ≠ σ d.first := fun h => hn1 (hbij.injOn heM h1 h)
      have hσ2 : σ e ≠ σ d.second := fun h => hn2 (hbij.injOn heM h2 h)
      rw [d.retained_isLink_iff hef, d'.retained_isLink_iff hσ1]
      constructor
      · rintro ⟨h, _, _⟩
        exact ⟨(hlink e heM a b).1 h, hσ1, hσ2⟩
      · rintro ⟨h, _, _⟩
        exact ⟨(hlink e heM a b).2 h, hn1, hn2⟩

/-- A sequence of suppressions moves along an isomorphism that fixes every
vertex. The new sequence keeps edge names. -/
theorem IsoFix.exists_keep {K N L : Graph α β} (hKN : IsoFix K N)
    (h : ReflTransGen IsSuppression K L) :
    ∃ L', ReflTransGen IsKeepSuppression N L' ∧ IsoFix L L' := by
  induction h with
  | refl => exact ⟨N, ReflTransGen.refl, hKN⟩
  | tail _ hstep ih =>
    obtain ⟨L', hs, σ, hσ⟩ := ih
    obtain ⟨d, rfl⟩ := hstep
    obtain ⟨d', hd', hiso⟩ := d.transport hσ
    exact ⟨d'.result, hs.tail ⟨d', hd', rfl⟩, hiso⟩

/-- Topological containment through suppressions that keep edge names. -/
theorem topologicallyContains_iff_keep {G H : Graph α β} :
    TopologicallyContains G H ↔
      ∃ K ≤ G, ∃ L, ReflTransGen IsKeepSuppression K L ∧ IsoFix H L := by
  rw [topologicallyContains_iff_isoFix]
  constructor
  · rintro ⟨K, hK, L, hs, hiso⟩
    obtain ⟨L', hs', hiso'⟩ := (IsoFix.refl K).exists_keep hs
    exact ⟨K, hK, L', hs', hiso.trans hiso'⟩
  · rintro ⟨K, hK, L, hs, hiso⟩
    exact ⟨K, hK, L, reflTransGen_isSuppression_of_keep hs, hiso⟩

/-! ### Loops -/

/-- A loop is never one of the two edges removed by a suppression. -/
theorem SuppressionData.ne_first_of_isLoopAt {M : Graph α β} (d : SuppressionData M)
    {e : β} {w : α} (he : M.IsLoopAt e w) : e ≠ d.first := by
  intro h
  rw [h] at he
  rcases (he : M.IsLink d.first w w).eq_and_eq_or_eq_and_eq d.first_link with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact d.vertex_ne_left (h1.symm.trans h2)
  · exact d.vertex_ne_left (h2.symm.trans h1)

theorem SuppressionData.ne_second_of_isLoopAt {M : Graph α β} (d : SuppressionData M)
    {e : β} {w : α} (he : M.IsLoopAt e w) : e ≠ d.second := by
  intro h
  rw [h] at he
  rcases (he : M.IsLink d.second w w).eq_and_eq_or_eq_and_eq d.second_link with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact d.vertex_ne_right (h1.symm.trans h2)
  · exact d.vertex_ne_right (h2.symm.trans h1)

/-- A loop survives a suppression with its name and its vertex. -/
theorem SuppressionData.isLoopAt_result {M : Graph α β} (d : SuppressionData M)
    {e : β} {w : α} (he : M.IsLoopAt e w) : d.result.IsLoopAt e w :=
  Or.inl ⟨he, d.ne_first_of_isLoopAt he, d.ne_second_of_isLoopAt he⟩

/-- A loop survives every sequence of suppressions. -/
theorem isLoopAt_of_reflTransGen {K L : Graph α β} (h : ReflTransGen IsSuppression K L)
    {e : β} {w : α} (he : K.IsLoopAt e w) : L.IsLoopAt e w := by
  induction h with
  | refl => exact he
  | tail _ hstep ih =>
    obtain ⟨d, rfl⟩ := hstep
    exact d.isLoopAt_result ih

/-- The same suppression after deleting a loop. -/
def SuppressionData.deleteLoop {M : Graph α β} (d : SuppressionData M) {e : β} {w : α}
    (he : M.IsLoopAt e w) : SuppressionData (M.deleteEdges {e}) where
  vertex := d.vertex
  left := d.left
  right := d.right
  first := d.first
  second := d.second
  fresh := d.fresh
  first_ne_second := d.first_ne_second
  first_link := ⟨d.first_link, fun h => d.ne_first_of_isLoopAt he (Set.mem_singleton_iff.1 h).symm⟩
  second_link :=
    ⟨d.second_link, fun h => d.ne_second_of_isLoopAt he (Set.mem_singleton_iff.1 h).symm⟩
  vertex_ne_left := d.vertex_ne_left
  vertex_ne_right := d.vertex_ne_right
  incident g hg := d.incident g (Graph.deleteEdges_inc.1 hg).1
  fresh_notMem h := d.fresh_notMem ⟨h.1.1, h.2⟩

/-- The new edge of a suppression is not an old loop. -/
theorem SuppressionData.fresh_ne_of_isLoopAt {M : Graph α β} (d : SuppressionData M)
    {e : β} {w : α} (he : M.IsLoopAt e w) : d.fresh ≠ e := by
  intro h
  apply d.fresh_notMem
  rw [h]
  refine ⟨he.edge_mem, ?_⟩
  rintro (h' | h')
  · exact d.ne_first_of_isLoopAt he h'
  · exact d.ne_second_of_isLoopAt he h'

theorem SuppressionData.result_deleteLoop {M : Graph α β} (d : SuppressionData M) {e : β}
    {w : α} (he : M.IsLoopAt e w) :
    (d.deleteLoop he).result = d.result.deleteEdges {e} := by
  have hfe := d.fresh_ne_of_isLoopAt he
  refine Graph.ext rfl fun g a b => ?_
  change ((M.IsLink g a b ∧ g ∉ ({e} : Set β)) ∧ g ≠ d.first ∧ g ≠ d.second ∨
      (g = d.fresh ∧ ((a = d.left ∧ b = d.right) ∨ (a = d.right ∧ b = d.left)))) ↔
    ((M.IsLink g a b ∧ g ≠ d.first ∧ g ≠ d.second) ∨
      (g = d.fresh ∧ ((a = d.left ∧ b = d.right) ∨ (a = d.right ∧ b = d.left)))) ∧
      g ∉ ({e} : Set β)
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro (⟨⟨h, hg⟩, h1, h2⟩ | ⟨rfl, hab⟩)
    · exact ⟨Or.inl ⟨h, h1, h2⟩, hg⟩
    · exact ⟨Or.inr ⟨rfl, hab⟩, hfe⟩
  · rintro ⟨⟨h, h1, h2⟩ | ⟨rfl, hab⟩, hg⟩
    · exact Or.inl ⟨⟨h, hg⟩, h1, h2⟩
    · exact Or.inr ⟨rfl, hab⟩

/-- Deleting a loop commutes with a sequence of suppressions. -/
theorem reflTransGen_deleteEdges_of_isLoopAt {K L : Graph α β}
    (h : ReflTransGen IsSuppression K L) {e : β} {w : α} (he : K.IsLoopAt e w) :
    ReflTransGen IsSuppression (K.deleteEdges {e}) (L.deleteEdges {e}) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail M _ hKM hstep ih =>
    obtain ⟨d, rfl⟩ := hstep
    have hM : M.IsLoopAt e w := isLoopAt_of_reflTransGen hKM he
    exact ih.tail ⟨d.deleteLoop hM, (d.result_deleteLoop hM).symm⟩

/-- A suppression that keeps names lifts to the graph with one more loop, when
the loop is not at the suppressed vertex. -/
theorem SuppressionData.exists_lift_loop {N : Graph α β} {e : β} {w : α}
    (hN : N.IsLoopAt e w) (d : SuppressionData (N.deleteEdges {e})) (hd : d.fresh = d.first)
    (hw : w ≠ d.vertex) :
    ∃ d' : SuppressionData N, d'.result.deleteEdges {e} = d.result ∧
      d'.result.IsLoopAt e w := by
  have hfirst : d.first ≠ e := fun h => d.first_link.2 (Set.mem_singleton_iff.2 h)
  have hsecond : d.second ≠ e := fun h => d.second_link.2 (Set.mem_singleton_iff.2 h)
  let d' : SuppressionData N :=
    { vertex := d.vertex
      left := d.left
      right := d.right
      first := d.first
      second := d.second
      fresh := d.first
      first_ne_second := d.first_ne_second
      first_link := d.first_link.1
      second_link := d.second_link.1
      vertex_ne_left := d.vertex_ne_left
      vertex_ne_right := d.vertex_ne_right
      incident := by
        intro g hg
        by_cases hge : g = e
        · subst hge
          exact (hw (hN.eq_of_inc hg)).elim
        · exact d.incident g (Graph.deleteEdges_inc.2 ⟨hg, hge⟩)
      fresh_notMem := fun h => h.2 (Or.inl rfl) }
  refine ⟨d', ?_, ?_⟩
  · refine Graph.ext rfl fun g a b => ?_
    change ((N.IsLink g a b ∧ g ≠ d.first ∧ g ≠ d.second) ∨
        (g = d.first ∧ ((a = d.left ∧ b = d.right) ∨ (a = d.right ∧ b = d.left)))) ∧
        g ∉ ({e} : Set β) ↔
      ((N.IsLink g a b ∧ g ∉ ({e} : Set β)) ∧ g ≠ d.first ∧ g ≠ d.second) ∨
        (g = d.fresh ∧ ((a = d.left ∧ b = d.right) ∨ (a = d.right ∧ b = d.left)))
    rw [hd]
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨h, h1, h2⟩ | ⟨rfl, hab⟩, hg⟩
      · exact Or.inl ⟨⟨h, hg⟩, h1, h2⟩
      · exact Or.inr ⟨rfl, hab⟩
    · rintro (⟨⟨h, hg⟩, h1, h2⟩ | ⟨rfl, hab⟩)
      · exact ⟨Or.inl ⟨h, h1, h2⟩, hg⟩
      · exact ⟨Or.inr ⟨rfl, hab⟩, hfirst⟩
  · exact d'.isLoopAt_result hN

/-- A sequence of suppressions that keeps names lifts to the graph with one
more loop at a vertex that is never suppressed. -/
theorem exists_lift_loop_of_keep {K L : Graph α β} (h : ReflTransGen IsKeepSuppression K L)
    {N : Graph α β} {e : β} {w : α} (hN : N.IsLoopAt e w) (hNK : N.deleteEdges {e} = K)
    (hw : w ∈ V(L)) :
    ∃ L', ReflTransGen IsSuppression N L' ∧ L'.deleteEdges {e} = L ∧ L'.IsLoopAt e w := by
  induction h with
  | refl => exact ⟨N, ReflTransGen.refl, hNK, hN⟩
  | @tail M _ _ hstep ih =>
    obtain ⟨d, hd, rfl⟩ := hstep
    have hwM : w ∈ V(M) := hw.1
    obtain ⟨M', hs, rfl, hM'⟩ := ih hwM
    have hwx : w ≠ d.vertex := fun h => hw.2 (Set.mem_singleton_iff.2 h)
    obtain ⟨d', hd', hloop⟩ := d.exists_lift_loop hM' hd hwx
    exact ⟨d'.result, hs.tail ⟨d', rfl⟩, hd', hloop⟩

/-! ### Subgraphs -/

/-- A subgraph of the result of one suppression comes from a subgraph of the
graph before it, by at most one suppression. -/
theorem SuppressionData.exists_le_of_le_result {M : Graph α β} (d : SuppressionData M)
    {M₁ : Graph α β} (hM₁ : M₁ ≤ d.result) :
    ∃ M' ≤ M, ReflTransGen IsSuppression M' M₁ := by
  classical
  have hVM : V(M₁) ⊆ V(M) := fun x hx => (hM₁.vertexSet_mono hx).1
  have hx : d.vertex ∉ V(M₁) := fun h => (hM₁.vertexSet_mono h).2 rfl
  by_cases hf : d.fresh ∈ E(M₁)
  · obtain ⟨a₀, b₀, hab₀⟩ := M₁.exists_isLink_of_mem_edgeSet hf
    have hends := (d.fresh_isLink_iff a₀ b₀).1 (hab₀.mono hM₁)
    have hleft : d.left ∈ V(M₁) := by
      rcases hends with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact hab₀.left_mem
      · exact hab₀.right_mem
    have hright : d.right ∈ V(M₁) := by
      rcases hends with ⟨-, rfl⟩ | ⟨rfl, -⟩
      · exact hab₀.right_mem
      · exact hab₀.left_mem
    let X : Set α := insert d.vertex V(M₁)
    let F : Set β := insert d.first (insert d.second (E(M₁) \ {d.fresh}))
    have hXM : X ⊆ V(M) := by
      rintro x (rfl | hx')
      · exact d.first_link.left_mem
      · exact hVM hx'
    let M' : Graph α β := (M.induce X).restrict F
    have hM'le : M' ≤ M := Graph.restrict_le.trans (Graph.induce_le hXM)
    have hM'link : ∀ g a b, M'.IsLink g a b ↔ g ∈ F ∧ M.IsLink g a b ∧ a ∈ X ∧ b ∈ X :=
      fun _ _ _ => Iff.rfl
    let d' : SuppressionData M' :=
      { vertex := d.vertex
        left := d.left
        right := d.right
        first := d.first
        second := d.second
        fresh := d.fresh
        first_ne_second := d.first_ne_second
        first_link := (hM'link _ _ _).2 ⟨Or.inl rfl, d.first_link, Or.inl rfl, Or.inr hleft⟩
        second_link := (hM'link _ _ _).2
          ⟨Or.inr (Or.inl rfl), d.second_link, Or.inl rfl, Or.inr hright⟩
        vertex_ne_left := d.vertex_ne_left
        vertex_ne_right := d.vertex_ne_right
        incident := fun g hg => d.incident g (hg.mono hM'le)
        fresh_notMem := by
          rintro ⟨hfM', hne⟩
          obtain ⟨a, b, hab⟩ := M'.exists_isLink_of_mem_edgeSet hfM'
          rcases ((hM'link _ _ _).1 hab).1 with h | h | h
          · exact hne (Or.inl h)
          · exact hne (Or.inr h)
          · exact h.2 rfl }
    refine ⟨M', hM'le, ReflTransGen.single ⟨d', ?_⟩⟩
    refine Graph.ext ?_ fun g a b => ?_
    · change V(M₁) = X \ {d.vertex}
      ext y
      constructor
      · intro hy
        exact ⟨Or.inr hy, fun h => hx ((Set.mem_singleton_iff.1 h) ▸ hy)⟩
      · rintro ⟨rfl | hy, hne⟩
        · exact (hne rfl).elim
        · exact hy
    · change M₁.IsLink g a b ↔ (M'.IsLink g a b ∧ g ≠ d.first ∧ g ≠ d.second) ∨
        (g = d.fresh ∧ ((a = d.left ∧ b = d.right) ∨ (a = d.right ∧ b = d.left)))
      rw [hM'link]
      constructor
      · intro h
        have hr := h.mono hM₁
        by_cases hgf : g = d.fresh
        · subst hgf
          exact Or.inr ⟨rfl, (d.fresh_isLink_iff a b).1 hr⟩
        · obtain ⟨hl, h1, h2⟩ := (d.retained_isLink_iff hgf a b).1 hr
          exact Or.inl ⟨⟨Or.inr (Or.inr ⟨h.edge_mem, hgf⟩), hl, Or.inr h.left_mem,
            Or.inr h.right_mem⟩, h1, h2⟩
      · rintro (⟨⟨hF, hl, -, -⟩, h1, h2⟩ | ⟨rfl, hab⟩)
        · rcases hF with h | h | ⟨hg, hgf⟩
          · exact (h1 h).elim
          · exact (h2 h).elim
          · have hgf' : g ≠ d.fresh := fun h => hgf (Set.mem_singleton_iff.2 h)
            exact (Graph.IsSubgraph.isLink_iff hM₁ hg).2
              ((d.retained_isLink_iff hgf' a b).2 ⟨hl, h1, h2⟩)
        · exact (Graph.IsSubgraph.isLink_iff hM₁ hf).2 ((d.fresh_isLink_iff a b).2 hab)
  · refine ⟨M₁, ⟨hVM, fun g a b h => ?_⟩, ReflTransGen.refl⟩
    have hgf : g ≠ d.fresh := fun h' => hf (h' ▸ h.edge_mem)
    exact ((d.retained_isLink_iff hgf a b).1 (h.mono hM₁)).1

/-- A subgraph of the end of a sequence of suppressions is the end of a
sequence of suppressions that starts from a subgraph. -/
theorem exists_le_reflTransGen {K L : Graph α β} (h : ReflTransGen IsSuppression K L)
    {L' : Graph α β} (hL : L' ≤ L) : ∃ K' ≤ K, ReflTransGen IsSuppression K' L' := by
  induction h generalizing L' with
  | refl => exact ⟨L', hL, ReflTransGen.refl⟩
  | tail _ hstep ih =>
    obtain ⟨d, rfl⟩ := hstep
    obtain ⟨M', hM', hs⟩ := d.exists_le_of_le_result hL
    obtain ⟨K', hK', hs'⟩ := ih hM'
    exact ⟨K', hK', hs'.trans hs⟩

/-! ### Isomorphisms and deleted edges -/

/-- Deleting an edge and its image. -/
theorem IsoFixVia.deleteEdges {σ : β → β} {H L : Graph α β} (h : IsoFixVia σ H L) {f : β}
    (hf : f ∈ E(H)) : IsoFixVia σ (H.deleteEdges {f}) (L.deleteEdges {σ f}) := by
  obtain ⟨hV, hbij, hlink⟩ := h
  refine ⟨hV, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro e ⟨he, hef⟩
    refine ⟨hbij.mapsTo he, fun h => hef ?_⟩
    exact Set.mem_singleton_iff.2 (hbij.injOn he hf (Set.mem_singleton_iff.1 h))
  · exact hbij.injOn.mono Set.sdiff_subset
  · rintro g ⟨hg, hgf⟩
    obtain ⟨e, he, rfl⟩ := hbij.surjOn hg
    refine ⟨e, ⟨he, fun h => hgf ?_⟩, rfl⟩
    rw [Set.mem_singleton_iff.1 h]
    exact Set.mem_singleton_iff.2 rfl
  · rintro e ⟨he, hef⟩ a b
    change H.IsLink e a b ∧ e ∉ ({f} : Set β) ↔ L.IsLink (σ e) a b ∧ σ e ∉ ({σ f} : Set β)
    have hσ : σ e ∉ ({σ f} : Set β) := fun h =>
      hef (Set.mem_singleton_iff.2 (hbij.injOn he hf (Set.mem_singleton_iff.1 h)))
    rw [hlink e he a b]
    exact ⟨fun h => ⟨h.1, hσ⟩, fun h => ⟨h.1, hef⟩⟩

/-- Deleting either of two loops at one vertex gives the same graph up to the
name of the remaining loop. -/
theorem isoFix_deleteEdges_loops {L : Graph α β} {e f : β} {w : α} (he : L.IsLoopAt e w)
    (hf : L.IsLoopAt f w) : IsoFix (L.deleteEdges {f}) (L.deleteEdges {e}) := by
  classical
  by_cases hef : e = f
  · rw [hef]
    exact IsoFix.refl _
  refine ⟨Equiv.swap e f, rfl, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro g ⟨hg, hgf⟩
    have hgf' : g ≠ f := fun h => hgf (Set.mem_singleton_iff.2 h)
    by_cases hge : g = e
    · subst hge
      rw [Equiv.swap_apply_left]
      exact ⟨hf.edge_mem, fun h => hef (Set.mem_singleton_iff.1 h).symm⟩
    · rw [Equiv.swap_apply_of_ne_of_ne hge hgf']
      exact ⟨hg, fun h => hge (Set.mem_singleton_iff.1 h)⟩
  · exact (Equiv.injective _).injOn
  · rintro g ⟨hg, hge⟩
    have hge' : g ≠ e := fun h => hge (Set.mem_singleton_iff.2 h)
    refine ⟨Equiv.swap e f g, ?_, Equiv.swap_apply_self _ _ _⟩
    by_cases hgf : g = f
    · subst hgf
      rw [Equiv.swap_apply_right]
      exact ⟨he.edge_mem, fun h => hef (Set.mem_singleton_iff.1 h)⟩
    · rw [Equiv.swap_apply_of_ne_of_ne hge' hgf]
      exact ⟨hg, fun h => hgf (Set.mem_singleton_iff.1 h)⟩
  · rintro g ⟨hg, hgf⟩ a b
    have hgf' : g ≠ f := fun h => hgf (Set.mem_singleton_iff.2 h)
    change L.IsLink g a b ∧ g ∉ ({f} : Set β) ↔
      L.IsLink (Equiv.swap e f g) a b ∧ Equiv.swap e f g ∉ ({e} : Set β)
    by_cases hge : g = e
    · subst hge
      rw [Equiv.swap_apply_left]
      have h1 := (he : L.IsLink g w w).isLink_iff (x' := a) (y' := b)
      have h2 := (hf : L.IsLink f w w).isLink_iff (x' := a) (y' := b)
      rw [h1, h2]
      exact ⟨fun h => ⟨h.1, fun h' => hef (Set.mem_singleton_iff.1 h').symm⟩,
        fun h => ⟨h.1, hgf⟩⟩
    · rw [Equiv.swap_apply_of_ne_of_ne hge hgf']
      exact ⟨fun h => ⟨h.1, fun h' => hge (Set.mem_singleton_iff.1 h')⟩, fun h => ⟨h.1, hgf⟩⟩

/-- Adding a loop to both graphs, at the same vertex, extends an isomorphism. -/
theorem IsoFixVia.extend_loop {σ : β → β} {H L : Graph α β} {f e : β} {w : α}
    (hf : H.IsLoopAt f w) (he : L.IsLoopAt e w)
    (h : IsoFixVia σ (H.deleteEdges {f}) (L.deleteEdges {e})) : IsoFix H L := by
  classical
  obtain ⟨hV, hbij, hlink⟩ := h
  refine ⟨fun g => if g = f then e else σ g, hV, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro g hg
    by_cases hgf : g = f
    · simp only [hgf, ite_true]
      exact he.edge_mem
    · simp only [hgf, ite_false]
      exact (hbij.mapsTo ⟨hg, fun h => hgf (Set.mem_singleton_iff.1 h)⟩).1
  · intro g₁ hg₁ g₂ hg₂ hg
    have hmem : ∀ g ∈ E(H), g ≠ f → σ g ∈ E(L) ∧ σ g ≠ e := fun g hg hgf =>
      let h := hbij.mapsTo ⟨hg, fun h => hgf (Set.mem_singleton_iff.1 h)⟩
      ⟨h.1, fun h' => h.2 (Set.mem_singleton_iff.2 h')⟩
    by_cases h₁ : g₁ = f <;> by_cases h₂ : g₂ = f
    · rw [h₁, h₂]
    · simp only [h₁, h₂, ite_true, ite_false] at hg
      exact ((hmem g₂ hg₂ h₂).2 hg.symm).elim
    · simp only [h₁, h₂, ite_true, ite_false] at hg
      exact ((hmem g₁ hg₁ h₁).2 hg).elim
    · simp only [h₁, h₂, ite_false] at hg
      exact hbij.injOn ⟨hg₁, fun h => h₁ (Set.mem_singleton_iff.1 h)⟩
        ⟨hg₂, fun h => h₂ (Set.mem_singleton_iff.1 h)⟩ hg
  · intro g hg
    by_cases hge : g = e
    · exact ⟨f, hf.edge_mem, by simp only [ite_true, hge]⟩
    · obtain ⟨g', hg', rfl⟩ := hbij.surjOn ⟨hg, fun h => hge (Set.mem_singleton_iff.1 h)⟩
      have hg'f : g' ≠ f := fun h => hg'.2 (Set.mem_singleton_iff.2 h)
      exact ⟨g', hg'.1, by simp only [hg'f, ite_false]⟩
  · intro g hg a b
    by_cases hgf : g = f
    · subst hgf
      simp only [ite_true]
      rw [(hf : H.IsLink g w w).isLink_iff, (he : L.IsLink e w w).isLink_iff]
    · simp only [hgf, ite_false]
      have hg' : g ∈ E(H.deleteEdges {f}) := ⟨hg, fun h => hgf (Set.mem_singleton_iff.1 h)⟩
      have h := hlink g hg' a b
      have hσ : σ g ∉ ({e} : Set β) := (hbij.mapsTo hg').2
      change H.IsLink g a b ∧ g ∉ ({f} : Set β) ↔ L.IsLink (σ g) a b ∧ σ g ∉ ({e} : Set β) at h
      exact ⟨fun h' => (h.1 ⟨h', hg'.2⟩).1, fun h' => (h.2 ⟨h', hσ⟩).1⟩

/-- A subgraph that avoids an edge is a subgraph of the graph without it. -/
theorem le_deleteEdges_of_notMem {K G : Graph α β} (hK : K ≤ G) {e : β} (he : e ∉ E(K)) :
    K ≤ G.deleteEdges {e} :=
  ⟨hK.vertexSet_mono, fun _ _ _ h =>
    ⟨h.mono hK, fun h' => he ((Set.mem_singleton_iff.1 h') ▸ h.edge_mem)⟩⟩

end GraphMinor.GM02
