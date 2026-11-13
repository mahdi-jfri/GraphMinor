module

public import GraphMinor.GM21.Section6SplitLinkage
public import GraphMinor.GM21.HypergraphMap

/-!
# Graph Minors XXI, (6.3): splitting several vertices at once

Claim (2) of the proof of (6.3) (page 28 of the preprint) splits every vertex `v` of `μ(a)`
and of `μ(b)` into two, "according to $\delta_1(v), \delta_2(v)$", and uses (2.4) to get a vital
linkage of the new graph. The correction to claim (4) (see the correction to the proof of (6.3) in
`corrections/GM21.md`) does the same for the vertices of
`μ(a) ∩ μ(b)`. This file builds the graph obtained by splitting all vertices of a finite set `X` at
once, and proves what (2.4) gives for it.

The new graph `splitAlong G X E₂` has vertex type `α ⊕ α ⊕ α`. A vertex `v ∉ X` is kept, as
`inl v`. A vertex `v ∈ X` becomes two vertices: `inr (inl v)`, incident with the edges of `v` not
in `E₂`, and `inr (inr v)`, incident with the edges of `v` in `E₂`. The edges do not change.
`splitName X c v` is the name of the copy of `v` on side `c` (`false` for the edges outside `E₂`,
`true` for those in `E₂`).

* Splitting the vertices of `X` one at a time gives a sequence of vertex splits in the sense of
  Section 2 (`isVertexSplit_splitAlong_insert`). Before any split the graph is a copy of `G`
  (`splitAlong_empty`). So (2.4), applied once for each vertex of `X`, gives a vital
  `(p + 2|X|)`-linkage of `splitAlong G X E₂` with the edges of `L` and all vertices of the new
  graph (`isVitalPLinkage_splitAlong`).
* A subgraph `A ≤ G` whose edges are all in `E₂`, or all outside `E₂`, is copied into the new graph
  by `splitName X c` for the matching side `c` (`isoImage_splitName_le`).
* Disjoint paths are carried by an injective map (`HasDisjointPaths.image_of_injective`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Split

open Set Function Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-! ## The split graph -/

/-- The graph obtained from `G` by splitting every vertex `v ∈ X`: `inl v` is a vertex `v ∉ X`;
for `v ∈ X`, `inr (inl v)` takes the edges of `v` outside `E₂` and `inr (inr v)` those in `E₂`. -/
def splitAlong (G : Hypergraph α β) (X : Set α) (E₂ : Set β) : Hypergraph (α ⊕ α ⊕ α) β where
  vertexSet := Sum.inl '' (G.vertexSet \ X) ∪ (Sum.inr ∘ Sum.inl) '' (G.vertexSet ∩ X) ∪
    (Sum.inr ∘ Sum.inr) '' (G.vertexSet ∩ X)
  edgeSet := G.edgeSet
  Inc e x := match x with
    | .inl v => G.Inc e v ∧ v ∉ X
    | .inr (.inl v) => G.Inc e v ∧ v ∈ X ∧ e ∉ E₂
    | .inr (.inr v) => G.Inc e v ∧ v ∈ X ∧ e ∈ E₂
  vertex_mem_of_inc e x h := by
    rcases x with v | v | v
    · exact Or.inl (Or.inl ⟨v, ⟨G.vertex_mem_of_inc h.1, h.2⟩, rfl⟩)
    · exact Or.inl (Or.inr ⟨v, ⟨G.vertex_mem_of_inc h.1, h.2.1⟩, rfl⟩)
    · exact Or.inr ⟨v, ⟨G.vertex_mem_of_inc h.1, h.2.1⟩, rfl⟩
  edge_mem_of_inc e x h := by
    rcases x with v | v | v
    · exact G.edge_mem_of_inc h.1
    · exact G.edge_mem_of_inc h.1
    · exact G.edge_mem_of_inc h.1
  vertexSet_finite := ((G.vertexSet_finite.sdiff.image _).union
    ((G.vertexSet_finite.inter_of_left X).image _)).union
    ((G.vertexSet_finite.inter_of_left X).image _)
  edgeSet_finite := G.edgeSet_finite

section splitAlong

variable {G : Hypergraph α β} {X : Set α} {E₂ : Set β}

@[simp] theorem splitAlong_edgeSet : (splitAlong G X E₂).edgeSet = G.edgeSet := rfl

@[simp] theorem splitAlong_inc_inl {e : β} {v : α} :
    (splitAlong G X E₂).Inc e (.inl v) ↔ G.Inc e v ∧ v ∉ X := Iff.rfl

@[simp] theorem splitAlong_inc_inr_inl {e : β} {v : α} :
    (splitAlong G X E₂).Inc e (.inr (.inl v)) ↔ G.Inc e v ∧ v ∈ X ∧ e ∉ E₂ := Iff.rfl

@[simp] theorem splitAlong_inc_inr_inr {e : β} {v : α} :
    (splitAlong G X E₂).Inc e (.inr (.inr v)) ↔ G.Inc e v ∧ v ∈ X ∧ e ∈ E₂ := Iff.rfl

theorem mem_splitAlong_inl {v : α} :
    Sum.inl v ∈ (splitAlong G X E₂).vertexSet ↔ v ∈ G.vertexSet ∧ v ∉ X := by
  simp [splitAlong]

theorem mem_splitAlong_inr_inl {v : α} :
    Sum.inr (Sum.inl v) ∈ (splitAlong G X E₂).vertexSet ↔ v ∈ G.vertexSet ∧ v ∈ X := by
  simp [splitAlong]

theorem mem_splitAlong_inr_inr {v : α} :
    Sum.inr (Sum.inr v) ∈ (splitAlong G X E₂).vertexSet ↔ v ∈ G.vertexSet ∧ v ∈ X := by
  simp [splitAlong]

/-- Before any split, the graph is the copy `inl(G)` of `G`. -/
theorem splitAlong_empty (G : Hypergraph α β) (E₂ : Set β) :
    splitAlong G ∅ E₂ = isoImage Sum.inl id G := by
  refine Hypergraph.ext ?_ ?_ ?_
  · ext x
    rcases x with v | v | v <;> simp [splitAlong, isoImage]
  · simp [splitAlong, isoImage]
  · funext e x
    rcases x with v | v | v <;> simp [splitAlong, isoImage]

/-- Splitting one more vertex `v ∉ Y` is a vertex split in the sense of Section 2: `inl v` is split
into `inr (inl v)`, with the edges of `v` outside `E₂`, and `inr (inr v)`, with those in `E₂`. -/
theorem isVertexSplit_splitAlong_insert {Y : Set α} {v : α} (hv : v ∈ G.vertexSet) (hvY : v ∉ Y) :
    IsVertexSplit (splitAlong G Y E₂) (splitAlong G (insert v Y) E₂) (.inl v) (.inr (.inl v))
      (.inr (.inr v)) {e | e ∈ G.edgeSet ∧ G.Inc e v ∧ e ∉ E₂}
      {e | e ∈ G.edgeSet ∧ G.Inc e v ∧ e ∈ E₂} where
  v_mem := mem_splitAlong_inl.mpr ⟨hv, hvY⟩
  v₁_not_mem := fun h => hvY (mem_splitAlong_inr_inl.mp h).2
  v₂_not_mem := fun h => hvY (mem_splitAlong_inr_inr.mp h).2
  v₁_ne_v₂ := by simp
  δ_disjoint := by
    rw [Set.disjoint_left]
    exact fun e h₁ h₂ => h₁.2.2 h₂.2.2
  δ_union := by
    ext e
    simp only [incidentEdges, mem_union, mem_ofPred_eq, splitAlong_edgeSet, splitAlong_inc_inl]
    tauto
  vertexSet_eq := by
    ext x
    rcases x with w | w | w
    · simp only [mem_splitAlong_inl, mem_union, mem_sdiff, mem_singleton_iff, mem_insert_iff,
        Sum.inl.injEq, reduceCtorEq, or_false]
      tauto
    · simp only [mem_splitAlong_inr_inl, mem_union, mem_sdiff, mem_singleton_iff, mem_insert_iff,
        reduceCtorEq, Sum.inr.injEq, Sum.inl.injEq, or_false]
      constructor
      · rintro ⟨hw, rfl | hwY⟩
        · exact Or.inr rfl
        · exact Or.inl ⟨⟨hw, hwY⟩, by simp⟩
      · rintro (⟨⟨hw, hwY⟩, -⟩ | rfl)
        · exact ⟨hw, Or.inr hwY⟩
        · exact ⟨hv, Or.inl rfl⟩
    · simp only [mem_splitAlong_inr_inr, mem_union, mem_sdiff, mem_singleton_iff, mem_insert_iff,
        reduceCtorEq, Sum.inr.injEq, false_or]
      constructor
      · rintro ⟨hw, rfl | hwY⟩
        · exact Or.inr rfl
        · exact Or.inl ⟨⟨hw, hwY⟩, by simp⟩
      · rintro (⟨⟨hw, hwY⟩, -⟩ | rfl)
        · exact ⟨hw, Or.inr hwY⟩
        · exact ⟨hv, Or.inl rfl⟩
  edgeSet_eq := rfl
  inc_iff := by
    intro e he x hx
    rcases x with w | w | w
    · simp only [splitAlong_inc_inl, mem_insert_iff, ne_eq, reduceCtorEq, not_false_eq_true,
        true_and, false_and, or_false, mem_ofPred_eq]
      have hwv : w ≠ v := by
        rintro rfl
        exact (mem_splitAlong_inl.mp hx).2 (mem_insert _ _)
      tauto
    · simp only [splitAlong_inc_inr_inl, mem_insert_iff, ne_eq, Sum.inr.injEq, Sum.inl.injEq,
        reduceCtorEq, not_false_eq_true, true_and, mem_ofPred_eq, false_and, or_false]
      by_cases hwv : w = v
      · subst hwv
        simp only [not_true_eq_false, false_and, false_or, true_or, true_and]
        exact ⟨fun h => ⟨he, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩
      · simp only [hwv, false_or, not_false_eq_true, true_and, false_and, or_false]
    · simp only [splitAlong_inc_inr_inr, mem_insert_iff, ne_eq, Sum.inr.injEq, reduceCtorEq,
        not_false_eq_true, true_and, mem_ofPred_eq, false_and, false_or]
      by_cases hwv : w = v
      · subst hwv
        simp only [not_true_eq_false, false_and, false_or, true_or, true_and]
        exact ⟨fun h => ⟨he, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩
      · simp only [hwv, false_or, not_false_eq_true, true_and, false_and, or_false]

end splitAlong

/-! ## The vital linkage of the split graph -/

/-- The spanning subgraph of `G'` with the edges of `L`, for the copy `inl(L)` of a spanning
subgraph `L ≤ G` and `G' = inl(G)`, is `inl(L)`. -/
private theorem splitSpanningSubgraph_isoImage {G L : Hypergraph α β} (hL : L ≤ G)
    (hV : L.vertexSet = G.vertexSet) :
    splitSpanningSubgraph (isoImage Sum.inl id G) (isoImage (Sum.inl : α → α ⊕ α ⊕ α) id L) =
      isoImage Sum.inl id L := by
  ext x
  · simp only [splitSpanningSubgraph, isoImage, hV]
  · simp only [splitSpanningSubgraph, isoImage, image_id, mem_inter_iff]
    exact ⟨fun h => h.2, fun h => ⟨hL.edgeSet_subset h, h⟩⟩
  · rename_i e
    simp only [splitSpanningSubgraph, isoImage, image_id', mem_inter_iff, id_eq]
    constructor
    · rintro ⟨⟨-, heL⟩, e₀, v₀, hinc, rfl, rfl⟩
      exact ⟨e₀, v₀, (GM10.inc_iff_of_le hL heL).mpr hinc, rfl, rfl⟩
    · rintro ⟨e₀, v₀, hinc, rfl, rfl⟩
      exact ⟨⟨hL.edgeSet_subset (L.edge_mem_of_inc hinc), L.edge_mem_of_inc hinc⟩, e₀, v₀,
        GM10.inc_of_le hL hinc, rfl, rfl⟩

/-- Taking the spanning subgraph twice: only the edge set of the inner graph matters. -/
private theorem splitSpanningSubgraph_splitSpanningSubgraph {G'' G' L : Hypergraph α β}
    (hE : G''.edgeSet = G'.edgeSet) :
    splitSpanningSubgraph G'' (splitSpanningSubgraph G' L) = splitSpanningSubgraph G'' L := by
  ext x
  · rfl
  · simp only [splitSpanningSubgraph, hE, mem_inter_iff]
    tauto
  · rename_i e
    simp only [splitSpanningSubgraph, hE, mem_inter_iff]
    tauto

/-- **(2.4) for several splits at once** (Graph Minors XXI, (2.4), page 3 of the preprint, applied
once for each vertex of `X`, as in claim (2) of the proof of (6.3), page 28 of the preprint). Let
`L` be a vital `p`-linkage in `G`, and let `X ⊆ V(G)` be finite. Then the spanning subgraph of
`splitAlong G X E₂` with the edges of `L` is a vital `(p + 2|X|)`-linkage, and each of its
terminals is a copy `inl t` of a terminal `t` of `L`, or a copy of a vertex of `X`. -/
theorem isVitalPLinkage_splitAlong {G L : Hypergraph α β} {p : ℕ} (hL : IsVitalPLinkage G L p)
    (X : Finset α) (hX : (X : Set α) ⊆ G.vertexSet) (E₂ : Set β) :
    IsVitalPLinkage (splitAlong G X E₂)
        (splitSpanningSubgraph (splitAlong G X E₂) (isoImage Sum.inl id L)) (p + 2 * X.card) ∧
      terminals (splitSpanningSubgraph (splitAlong G X E₂) (isoImage Sum.inl id L)) ⊆
        Sum.inl '' terminals L ∪ (Sum.inr ∘ Sum.inl) '' X ∪ (Sum.inr ∘ Sum.inr) '' X := by
  classical
  induction X using Finset.induction_on with
  | empty =>
    simp only [Finset.coe_empty, Finset.card_empty, mul_zero, add_zero, image_empty, union_empty]
    rw [splitAlong_empty, splitSpanningSubgraph_isoImage hL.1.1.1 hL.1.2.1]
    have hinj : InjOn (Sum.inl : α → α ⊕ α ⊕ α) G.vertexSet := Sum.inl_injective.injOn
    refine ⟨(isVitalPLinkage_isoImage hL.1.1.1 hinj (injOn_id _)).mpr hL, ?_⟩
    rw [terminals_isoImage hL.1.1.1 hinj (injOn_id _)]
  | @insert v Y hvY ih =>
    have hXY : (Y : Set α) ⊆ G.vertexSet := fun x hx => hX (Finset.mem_insert_of_mem hx)
    have hv : v ∈ G.vertexSet := hX (Finset.mem_insert_self v Y)
    obtain ⟨ihL, ihT⟩ := ih hXY
    have hs := isVertexSplit_splitAlong_insert (E₂ := E₂) hv (show v ∉ (Y : Set α) from hvY)
    rw [Finset.coe_insert]
    obtain ⟨hL', -, hT'⟩ := isVitalPLinkage_split_and hs ihL
    rw [splitSpanningSubgraph_splitSpanningSubgraph (G'' := splitAlong G (insert v ↑Y) E₂)
      (G' := splitAlong G ↑Y E₂) rfl] at hL' hT'
    refine ⟨?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hvY, show p + 2 * (Y.card + 1) = p + 2 * Y.card + 2 by ring]
      exact hL'
    · intro x hx
      rcases hT' hx with rfl | rfl | hx
      · exact Or.inl (Or.inr ⟨v, mem_insert _ _, rfl⟩)
      · exact Or.inr ⟨v, mem_insert _ _, rfl⟩
      · rcases ihT hx with (h | ⟨w, hw, rfl⟩) | ⟨w, hw, rfl⟩
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr ⟨w, mem_insert_of_mem _ hw, rfl⟩)
        · exact Or.inr ⟨w, mem_insert_of_mem _ hw, rfl⟩

/-! ## Copies of subgraphs on one side -/

open Classical in
/-- The name of the copy of `v` on side `c`: `inl v` if `v ∉ X`; otherwise `inr (inl v)` for
`c = false` and `inr (inr v)` for `c = true`. -/
noncomputable def splitName (X : Set α) (c : Bool) (v : α) : α ⊕ α ⊕ α :=
  if v ∈ X then (if c then .inr (.inr v) else .inr (.inl v)) else .inl v

section splitName

variable {X : Set α}

theorem splitName_of_notMem {c : Bool} {v : α} (hv : v ∉ X) : splitName X c v = .inl v := by
  simp [splitName, hv]

theorem splitName_false_of_mem {v : α} (hv : v ∈ X) : splitName X false v = .inr (.inl v) := by
  simp [splitName, hv]

theorem splitName_true_of_mem {v : α} (hv : v ∈ X) : splitName X true v = .inr (.inr v) := by
  simp [splitName, hv]

/-- Two copies are equal only for the same vertex. -/
theorem eq_of_splitName_eq {c c' : Bool} {v w : α} (h : splitName X c v = splitName X c' w) :
    v = w := by
  unfold splitName at h
  split_ifs at h <;> simp_all

theorem splitName_injective (c : Bool) : Injective (splitName X c) :=
  fun _ _ h => eq_of_splitName_eq h

/-- Copies on different sides are equal only for a vertex outside `X`. -/
theorem notMem_of_splitName_eq {c c' : Bool} (hcc' : c ≠ c') {v w : α}
    (h : splitName X c v = splitName X c' w) : v ∉ X := by
  intro hv
  have hvw := eq_of_splitName_eq h
  subst hvw
  unfold splitName at h
  cases c <;> cases c' <;> simp_all

/-- A copy is a vertex `inl w` only when it is the copy of `w ∉ X`. -/
theorem splitName_eq_inl {c : Bool} {v w : α} (h : splitName X c v = .inl w) : v = w ∧ v ∉ X := by
  unfold splitName at h
  split_ifs at h with hv
  exact ⟨Sum.inl.inj h, hv⟩

/-- The copy of a vertex of `G` is a vertex of the split graph. -/
theorem splitName_mem {G : Hypergraph α β} {E₂ : Set β} (c : Bool) {v : α}
    (hv : v ∈ G.vertexSet) : splitName X c v ∈ (splitAlong G X E₂).vertexSet := by
  by_cases hvX : v ∈ X
  · cases c
    · rw [splitName_false_of_mem hvX]; exact mem_splitAlong_inr_inl.mpr ⟨hv, hvX⟩
    · rw [splitName_true_of_mem hvX]; exact mem_splitAlong_inr_inr.mpr ⟨hv, hvX⟩
  · rw [splitName_of_notMem hvX]; exact mem_splitAlong_inl.mpr ⟨hv, hvX⟩

/-- An edge on side `c` is incident in the split graph with the copy on side `c` of each of its
ends. -/
theorem splitAlong_inc_splitName_iff {G : Hypergraph α β} {E₂ : Set β} {c : Bool} {e : β}
    (hc : e ∈ E₂ ↔ c = true) {v : α} :
    (splitAlong G X E₂).Inc e (splitName X c v) ↔ G.Inc e v := by
  by_cases hvX : v ∈ X
  · cases c
    · rw [splitName_false_of_mem hvX, splitAlong_inc_inr_inl]
      have : e ∉ E₂ := fun h => by simpa using hc.mp h
      tauto
    · rw [splitName_true_of_mem hvX, splitAlong_inc_inr_inr]
      have : e ∈ E₂ := hc.mpr rfl
      tauto
  · rw [splitName_of_notMem hvX, splitAlong_inc_inl]
    tauto

/-- An edge on side `c` is incident in the split graph only with copies on side `c`. -/
theorem eq_splitName_of_splitAlong_inc {G : Hypergraph α β} {E₂ : Set β} {c : Bool} {e : β}
    (hc : e ∈ E₂ ↔ c = true) {x : α ⊕ α ⊕ α} (hx : (splitAlong G X E₂).Inc e x) :
    ∃ v, G.Inc e v ∧ splitName X c v = x := by
  rcases x with w | w | w
  · exact ⟨w, hx.1, splitName_of_notMem hx.2⟩
  · refine ⟨w, hx.1, ?_⟩
    cases c
    · exact splitName_false_of_mem hx.2.1
    · exact absurd (hc.mpr rfl) hx.2.2
  · refine ⟨w, hx.1, ?_⟩
    cases c
    · exact absurd (hc.mp hx.2.2) (by simp)
    · exact splitName_true_of_mem hx.2.1

/-- **A subgraph on one side is copied into the split graph.** If `A ≤ G` and every edge of `A` is
in `E₂` exactly when `c = true`, then the copy of `A` by `splitName X c` is a subgraph of
`splitAlong G X E₂`. -/
theorem isoImage_splitName_le {G A : Hypergraph α β} {E₂ : Set β} {c : Bool} (hA : A ≤ G)
    (hc : ∀ e ∈ A.edgeSet, (e ∈ E₂ ↔ c = true)) :
    isoImage (splitName X c) id A ≤ splitAlong G X E₂ where
  vertexSet_subset := by
    rintro _ ⟨v, hv, rfl⟩
    exact splitName_mem c (hA.vertexSet_subset hv)
  edgeSet_subset := by
    rintro _ ⟨e, he, rfl⟩
    exact hA.edgeSet_subset he
  ends_eq := by
    rintro _ ⟨e, he, rfl⟩
    ext x
    simp only [Hypergraph.ends, mem_ofPred_eq, isoImage, id_eq]
    constructor
    · intro hx
      obtain ⟨v, hv, rfl⟩ := eq_splitName_of_splitAlong_inc (hc e he) hx
      exact ⟨e, v, (GM10.inc_iff_of_le hA he).mpr hv, rfl, rfl⟩
    · rintro ⟨e₀, v, hv, rfl, rfl⟩
      exact (splitAlong_inc_splitName_iff (hc e₀ he)).mpr (GM10.inc_of_le hA hv)

end splitName

/-! ## Disjoint paths under an injective map -/

/-- An injective map that sends edges of `K` to edges of `K'` carries `n` disjoint paths of `K`
from `X` to `Y` to `n` disjoint paths of `K'` from `f(X)` to `f(Y)`. -/
theorem HasDisjointPaths.image_of_injective {γ δ : Type*} {K : SimpleGraph γ} {K' : SimpleGraph δ}
    {f : γ → δ} (hf : Injective f) (hadj : ∀ {x y}, K.Adj x y → K'.Adj (f x) (f y)) {X Y : Set γ}
    {n : ℕ} (h : HasDisjointPaths K X Y n) : HasDisjointPaths K' (f '' X) (f '' Y) n := by
  obtain ⟨P, hP⟩ := h
  let φ : K →g K' := ⟨f, hadj⟩
  refine ⟨fun i => ⟨f (P i).first, f (P i).last, (P i).walk.map φ,
    (P i).isPath.map hf, mem_image_of_mem f (P i).first_mem,
    mem_image_of_mem f (P i).last_mem⟩, ?_⟩
  intro i j hij
  rw [Set.disjoint_left]
  simp only [mem_ofPred_eq, SimpleGraph.Walk.support_map, List.mem_map]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  rw [hf hxy] at hy
  exact Set.disjoint_left.mp (hP hij) hx hy

/-- The skeleton of the copy `isoImage f id A` of `A` by an injective map `f` contains the image of
the skeleton of `A`. -/
theorem skeleton_adj_isoImage_of_injective {γ δ : Type*} {A : Hypergraph γ β} {f : γ → δ}
    (hf : Injective f) {x y : γ} (h : A.skeleton.Adj x y) :
    (isoImage f id A).skeleton.Adj (f x) (f y) := by
  obtain ⟨hne, e, hx, hy⟩ := h
  exact ⟨hf.ne hne, e, ⟨e, x, hx, rfl, rfl⟩, ⟨e, y, hy, rfl, rfl⟩⟩

end Split
end GM21
end GraphMinor
