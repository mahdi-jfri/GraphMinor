module

public import GraphMinor.GM08.Defs

/-!
# Graph Minors VIII, printed (15.1): gluing path-decompositions

Our proof of the printed (15.1) (`Section15PrintedFinal.lean`, and see the correction to the proof
of (15.1) in `corrections/GM08.md`) builds its trains from several pieces: an edgeless piece, one
piece for each bridge of a pocket, and the chain of a strong tube. This file gives the bookkeeping
for that.

A path-decomposition is indexed by `Fin`. We first read it through natural-number indices
(`GraftPathDecomposition.Gn`, `GraftPathDecomposition.Yn`) and build one from natural-number data
(`GraftPathDecomposition.ofNat`). Then we glue two decompositions whose graphs meet exactly in the
last junction of the first and the first junction of the second
(`GraftPathDecomposition.append`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Graph

universe u v

variable {α : Type u} {β : Type v}

/-- The graph with vertex set `V₀` and those edges of `E₀` that `G` draws between vertices of
`V₀`. -/
def subOf (G : Graph α β) (V₀ : Set α) (E₀ : Set β) : Graph α β :=
  (G.induce V₀).restrict E₀

@[simp] theorem subOf_vertexSet (G : Graph α β) (V₀ : Set α) (E₀ : Set β) :
    V(subOf G V₀ E₀) = V₀ := rfl

@[simp] theorem subOf_isLink (G : Graph α β) (V₀ : Set α) (E₀ : Set β) {e : β} {x y : α} :
    (subOf G V₀ E₀).IsLink e x y ↔ e ∈ E₀ ∧ G.IsLink e x y ∧ x ∈ V₀ ∧ y ∈ V₀ := by
  simp [subOf]

theorem subOf_edgeSet (G : Graph α β) (V₀ : Set α) (E₀ : Set β) :
    E(subOf G V₀ E₀) = {e | e ∈ E₀ ∧ ∃ x y, G.IsLink e x y ∧ x ∈ V₀ ∧ y ∈ V₀} := by
  ext e
  rw [edgeSet_eq_setOfPred_exists_isLink]
  simp only [subOf_isLink, mem_ofPred_eq]
  constructor
  · rintro ⟨x, y, h1, h2⟩
    exact ⟨h1, x, y, h2⟩
  · rintro ⟨h1, x, y, h2⟩
    exact ⟨x, y, h1, h2⟩

theorem subOf_le (G : Graph α β) {V₀ : Set α} (hV : V₀ ⊆ V(G)) (E₀ : Set β) :
    subOf G V₀ E₀ ≤ G :=
  (restrict_le).trans (induce_le hV)

namespace GraftPathDecomposition

variable {𝒜 : Set (Graft α β)} {X : Graft α β}

/-- The graphs of a path-decomposition, read through natural-number indices. -/
def Gn (D : GraftPathDecomposition 𝒜 X) (i : ℕ) : Graph α β :=
  if h : i < D.r then D.G ⟨i, h⟩ else Graph.noEdge ∅ β

/-- The junctions of a path-decomposition, read through natural-number indices. -/
def Yn (D : GraftPathDecomposition 𝒜 X) (i : ℕ) : Set α :=
  if h : i < D.r + 1 then D.Y ⟨i, h⟩ else ∅

theorem Gn_eq (D : GraftPathDecomposition 𝒜 X) (i : Fin D.r) : D.Gn i = D.G i := by
  simp [Gn, i.2]

theorem Yn_eq (D : GraftPathDecomposition 𝒜 X) (i : Fin (D.r + 1)) : D.Yn i = D.Y i := by
  simp [Yn, i.2]

theorem Yn_subset (D : GraftPathDecomposition 𝒜 X) {i : ℕ} (hi : i < D.r) :
    D.Yn i ∪ D.Yn (i + 1) ⊆ V(D.Gn i) := by
  have := D.Y_subset ⟨i, hi⟩
  simpa [Yn, Gn, hi, Nat.lt_succ_of_lt hi, Nat.succ_lt_succ hi] using this

theorem Gn_le (D : GraftPathDecomposition 𝒜 X) {i : ℕ} (hi : i < D.r) : D.Gn i ≤ X.G := by
  simpa [Gn, hi] using D.le_G ⟨i, hi⟩

theorem mem_𝒜' (D : GraftPathDecomposition 𝒜 X) {i : ℕ} (hi : i < D.r)
    (h : D.Yn i ∪ D.Yn (i + 1) ⊆ V(D.Gn i)) (hf : IsFiniteGraph (D.Gn i)) :
    Graft.mk (D.Gn i) (D.Yn i ∪ D.Yn (i + 1)) h hf ∈ 𝒜 := by
  have := D.mem_𝒜 ⟨i, hi⟩
  simp only [Gn, Yn, hi, Nat.lt_succ_of_lt hi, Nat.succ_lt_succ hi, ↓reduceDIte] at h hf ⊢
  exact this

theorem vertexSet_iUnion' (D : GraftPathDecomposition 𝒜 X) :
    (⋃ (i : ℕ) (_ : i < D.r), V(D.Gn i)) = V(X.G) := by
  rw [← D.vertexSet_iUnion]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact ⟨⟨i, hi⟩, by simpa [Gn, hi] using hx⟩
  · rintro ⟨i, hx⟩
    exact ⟨i, i.2, by simpa [Gn, i.2] using hx⟩

theorem edgeSet_iUnion' (D : GraftPathDecomposition 𝒜 X) :
    (⋃ (i : ℕ) (_ : i < D.r), E(D.Gn i)) = E(X.G) := by
  rw [← D.edgeSet_iUnion]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact ⟨⟨i, hi⟩, by simpa [Gn, hi] using hx⟩
  · rintro ⟨i, hx⟩
    exact ⟨i, i.2, by simpa [Gn, i.2] using hx⟩

theorem edge_disjoint' (D : GraftPathDecomposition 𝒜 X) {i j : ℕ} (hi : i < D.r) (hj : j < D.r)
    (hij : i ≠ j) : Disjoint E(D.Gn i) E(D.Gn j) := by
  simpa [Gn, hi, hj] using D.edge_disjoint ⟨i, hi⟩ ⟨j, hj⟩ (fun h => hij (congrArg Fin.val h))

theorem vertex_inter_subset' (D : GraftPathDecomposition 𝒜 X) {h i j : ℕ} (hhi : h ≤ i)
    (hij : i ≤ j) (hj : j < D.r) : V(D.Gn h) ∩ V(D.Gn j) ⊆ V(D.Gn i) := by
  have hi : i < D.r := lt_of_le_of_lt hij hj
  have hh : h < D.r := lt_of_le_of_lt hhi hi
  simpa [Gn, hh, hi, hj] using
    D.vertex_inter_subset ⟨h, hh⟩ ⟨i, hi⟩ ⟨j, hj⟩ (Fin.mk_le_mk.mpr hhi) (Fin.mk_le_mk.mpr hij)

theorem adj_vertex_inter' (D : GraftPathDecomposition 𝒜 X) {i : ℕ} (hi : i + 1 < D.r) :
    V(D.Gn i) ∩ V(D.Gn (i + 1)) = D.Yn (i + 1) := by
  have h1 : i < D.r := by omega
  have h2 : i + 1 < D.r + 1 := by omega
  simpa [Gn, Yn, h1, hi, h2] using D.adj_vertex_inter ⟨i, h1⟩ hi

theorem T_eq' (D : GraftPathDecomposition 𝒜 X) : X.T = D.Yn 0 ∪ D.Yn D.r := by
  have h0 := D.Yn_eq ⟨0, Nat.zero_lt_succ _⟩
  have h1 := D.Yn_eq (Fin.last D.r)
  rw [D.T_eq]
  exact congrArg₂ (· ∪ ·) h0.symm h1.symm

/-- The junctions lie in the graph. -/
theorem Yn_subset_V (D : GraftPathDecomposition 𝒜 X) {i : ℕ} (hi : i ≤ D.r) :
    D.Yn i ⊆ V(X.G) := by
  rcases Nat.lt_or_ge i D.r with h | h
  · exact ((subset_union_left).trans (D.Yn_subset h)).trans (D.Gn_le h).vertexSet_mono
  · have hi' : i = (D.r - 1) + 1 := by have := D.hr; omega
    have hlt : D.r - 1 < D.r := by have := D.hr; omega
    rw [hi']
    exact ((subset_union_right).trans (D.Yn_subset hlt)).trans (D.Gn_le hlt).vertexSet_mono

/-- **Building a path-decomposition from natural-number data.** -/
def ofNat (r : ℕ) (hr : 1 ≤ r) (G : ℕ → Graph α β) (Y : ℕ → Set α)
    (Y_subset : ∀ i < r, Y i ∪ Y (i + 1) ⊆ V(G i)) (le_G : ∀ i < r, G i ≤ X.G)
    (mem : ∀ i < r, ∀ h hf, Graft.mk (G i) (Y i ∪ Y (i + 1)) h hf ∈ 𝒜)
    (vertexSet_iUnion : (⋃ (i : ℕ) (_ : i < r), V(G i)) = V(X.G))
    (edgeSet_iUnion : (⋃ (i : ℕ) (_ : i < r), E(G i)) = E(X.G))
    (edge_disjoint : ∀ i j, i < r → j < r → i ≠ j → Disjoint E(G i) E(G j))
    (vertex_inter_subset : ∀ h i j, h ≤ i → i ≤ j → j < r → V(G h) ∩ V(G j) ⊆ V(G i))
    (adj : ∀ i, i + 1 < r → V(G i) ∩ V(G (i + 1)) = Y (i + 1))
    (T_eq : X.T = Y 0 ∪ Y r) : GraftPathDecomposition 𝒜 X where
  r := r
  hr := hr
  G := fun i => G i
  Y := fun j => Y j
  Y_subset := fun i => Y_subset i i.2
  le_G := fun i => le_G i i.2
  mem_𝒜 := fun i => mem i i.2 _ _
  vertexSet_iUnion := by
    rw [← vertexSet_iUnion]
    ext x
    simp only [mem_iUnion]
    exact ⟨fun ⟨i, hx⟩ => ⟨i, i.2, hx⟩, fun ⟨i, hi, hx⟩ => ⟨⟨i, hi⟩, hx⟩⟩
  edgeSet_iUnion := by
    rw [← edgeSet_iUnion]
    ext x
    simp only [mem_iUnion]
    exact ⟨fun ⟨i, hx⟩ => ⟨i, i.2, hx⟩, fun ⟨i, hi, hx⟩ => ⟨⟨i, hi⟩, hx⟩⟩
  edge_disjoint := fun i j hij => edge_disjoint i j i.2 j.2 (fun h => hij (Fin.ext h))
  vertex_inter_subset := fun h i j hhi hij => vertex_inter_subset h i j hhi hij j.2
  adj_vertex_inter := fun i hi => adj i hi
  T_eq := T_eq

@[simp] theorem ofNat_r {r hr G Y Y_subset le_G mem vU eU ed vi adj T_eq} :
    (ofNat (𝒜 := 𝒜) (X := X) r hr G Y Y_subset le_G mem vU eU ed vi adj T_eq).r = r := rfl

theorem ofNat_Yn {r hr G Y Y_subset le_G mem vU eU ed vi adj T_eq} {j : ℕ} (hj : j ≤ r) :
    (ofNat (𝒜 := 𝒜) (X := X) r hr G Y Y_subset le_G mem vU eU ed vi adj T_eq).Yn j = Y j := by
  simp [Yn, ofNat, Nat.lt_succ_of_le hj]

theorem ofNat_Gn {r hr G Y Y_subset le_G mem vU eU ed vi adj T_eq} {i : ℕ} (hi : i < r) :
    (ofNat (𝒜 := 𝒜) (X := X) r hr G Y Y_subset le_G mem vU eU ed vi adj T_eq).Gn i = G i := by
  simp [Gn, ofNat, hi]

theorem graft_mem_of_eq {G G' : Graph α β} {T T' : Set α} (hG : G = G') (hT : T = T')
    {h : T ⊆ V(G)} {hf : IsFiniteGraph G} {h' : T' ⊆ V(G')} {hf' : IsFiniteGraph G'}
    (hm : Graft.mk G' T' h' hf' ∈ 𝒜) : Graft.mk G T h hf ∈ 𝒜 := by
  subst hG
  subst hT
  exact hm

theorem isFiniteGraph_Gn (D : GraftPathDecomposition 𝒜 X) {i : ℕ} (hi : i < D.r) :
    IsFiniteGraph (D.Gn i) :=
  ⟨X.finite_G.1.subset (D.Gn_le hi).vertexSet_mono, X.finite_G.2.subset (D.Gn_le hi).edgeSet_mono⟩

/-- **A one-piece path-decomposition.** A graft in `𝒜` whose roots are `A ∪ B` has the
decomposition with the single part `(G, A, B)`. -/
def single {A B : Set α} (hAB : A ∪ B ⊆ V(X.G)) (hm : Graft.mk X.G (A ∪ B) hAB X.finite_G ∈ 𝒜)
    (hT : X.T = A ∪ B) : GraftPathDecomposition 𝒜 X :=
  ofNat 1 le_rfl (fun _ => X.G) (fun j => if j = 0 then A else B)
    (fun i hi => by
      obtain rfl : i = 0 := by omega
      simpa using hAB)
    (fun _ _ => le_rfl)
    (fun i hi h hf => by
      obtain rfl : i = 0 := by omega
      exact graft_mem_of_eq rfl (by simp) hm)
    (by ext x; simp)
    (by ext x; simp)
    (fun i j hi hj hij => by omega)
    (fun h i j _ _ _ => by simp)
    (fun i hi => by omega)
    (by simpa using hT)

theorem single_r {A B : Set α} {hAB : A ∪ B ⊆ V(X.G)} {hm} {hT : X.T = A ∪ B} :
    (single (𝒜 := 𝒜) hAB hm hT).r = 1 := rfl

theorem single_Yn_zero {A B : Set α} {hAB : A ∪ B ⊆ V(X.G)} {hm} {hT : X.T = A ∪ B} :
    (single (𝒜 := 𝒜) hAB hm hT).Yn 0 = A := by
  rw [single, ofNat_Yn (Nat.zero_le _)]
  simp

theorem single_Yn_one {A B : Set α} {hAB : A ∪ B ⊆ V(X.G)} {hm} {hT : X.T = A ∪ B} :
    (single (𝒜 := 𝒜) hAB hm hT).Yn 1 = B := by
  rw [single, ofNat_Yn le_rfl]
  simp

/-- **Gluing two path-decompositions.** Let `X` be the union of `X₁` and `X₂`, with no common
edge, and suppose the graphs of `X₁` and `X₂` meet exactly in the last junction of `D₁`, which is
also the first junction of `D₂`. Then the parts of `D₁` followed by the parts of `D₂` form a
path-decomposition of `X`, if the roots of `X` are the first junction of `D₁` and the last
junction of `D₂`.

The interval property for a part `h` of `D₁` and a part `j` of `D₂` holds because their common
vertices lie in the junction, and the junction lies in the last part of `D₁` and the first part
of `D₂`. -/
def append {X₁ X₂ : Graft α β} (D₁ : GraftPathDecomposition 𝒜 X₁)
    (D₂ : GraftPathDecomposition 𝒜 X₂) (h₁ : X₁.G ≤ X.G) (h₂ : X₂.G ≤ X.G)
    (hV : V(X.G) = V(X₁.G) ∪ V(X₂.G)) (hE : E(X.G) = E(X₁.G) ∪ E(X₂.G))
    (hdisj : Disjoint E(X₁.G) E(X₂.G)) (hJ₁ : V(X₁.G) ∩ V(X₂.G) = D₁.Yn D₁.r)
    (hJ₂ : D₂.Yn 0 = D₁.Yn D₁.r) (hT : X.T = D₁.Yn 0 ∪ D₂.Yn D₂.r) :
    GraftPathDecomposition 𝒜 X :=
  have hn := D₁.hr
  have hm := D₂.hr
  have hY₁ : ∀ j, j ≤ D₁.r →
      (if j ≤ D₁.r then D₁.Yn j else D₂.Yn (j - D₁.r)) = D₁.Yn j :=
    fun j hj => by simp [hj]
  have hY₂ : ∀ j, D₁.r ≤ j →
      (if j ≤ D₁.r then D₁.Yn j else D₂.Yn (j - D₁.r)) = D₂.Yn (j - D₁.r) := by
    intro j hj
    rcases eq_or_lt_of_le hj with rfl | hlt
    · simp [hJ₂]
    · simp [show ¬ j ≤ D₁.r by omega]
  have hG₁ : ∀ i, i < D₁.r →
      (if i < D₁.r then D₁.Gn i else D₂.Gn (i - D₁.r)) = D₁.Gn i :=
    fun i hi => by simp [hi]
  have hG₂ : ∀ i, D₁.r ≤ i →
      (if i < D₁.r then D₁.Gn i else D₂.Gn (i - D₁.r)) = D₂.Gn (i - D₁.r) :=
    fun i hi => by simp [show ¬ i < D₁.r by omega]
  -- the junction lies in the last part of `D₁` and in the first part of `D₂`
  have hJa : D₁.Yn D₁.r ⊆ V(D₁.Gn (D₁.r - 1)) := by
    have := D₁.Yn_subset (i := D₁.r - 1) (by omega)
    rw [show D₁.r - 1 + 1 = D₁.r by omega] at this
    exact subset_union_right.trans this
  have hJb : D₁.Yn D₁.r ⊆ V(D₂.Gn 0) := hJ₂ ▸ subset_union_left.trans (D₂.Yn_subset (by omega))
  have hV₁ : ∀ i, i < D₁.r → V(D₁.Gn i) ⊆ V(X₁.G) := fun i hi => (D₁.Gn_le hi).vertexSet_mono
  have hV₂ : ∀ i, i < D₂.r → V(D₂.Gn i) ⊆ V(X₂.G) := fun i hi => (D₂.Gn_le hi).vertexSet_mono
  ofNat (D₁.r + D₂.r) (by omega)
    (fun i => if i < D₁.r then D₁.Gn i else D₂.Gn (i - D₁.r))
    (fun j => if j ≤ D₁.r then D₁.Yn j else D₂.Yn (j - D₁.r))
    (fun i hi => by
      rcases Nat.lt_or_ge i D₁.r with h | h
      · rw [hY₁ i h.le, hY₁ (i + 1) h, hG₁ i h]
        exact D₁.Yn_subset h
      · rw [hY₂ i h, hY₂ (i + 1) (by omega), hG₂ i h, show i + 1 - D₁.r = i - D₁.r + 1 by omega]
        exact D₂.Yn_subset (by omega))
    (fun i hi => by
      rcases Nat.lt_or_ge i D₁.r with h | h
      · rw [hG₁ i h]
        exact (D₁.Gn_le h).trans h₁
      · rw [hG₂ i h]
        exact (D₂.Gn_le (by omega)).trans h₂)
    (fun i hi h hf => by
      rcases Nat.lt_or_ge i D₁.r with h' | h'
      · exact graft_mem_of_eq (hG₁ i h') (by rw [hY₁ i h'.le, hY₁ (i + 1) h'])
          (D₁.mem_𝒜' h' (D₁.Yn_subset h') (D₁.isFiniteGraph_Gn h'))
      · have hlt : i - D₁.r < D₂.r := by omega
        exact graft_mem_of_eq (hG₂ i h')
          (by rw [hY₂ i h', hY₂ (i + 1) (by omega), show i + 1 - D₁.r = i - D₁.r + 1 by omega])
          (D₂.mem_𝒜' hlt (D₂.Yn_subset hlt) (D₂.isFiniteGraph_Gn hlt)))
    (by
      refine Subset.antisymm (iUnion₂_subset fun i hi => ?_) ?_
      · rcases Nat.lt_or_ge i D₁.r with h | h
        · rw [hG₁ i h]
          exact (hV₁ i h).trans (hV ▸ subset_union_left)
        · rw [hG₂ i h]
          exact (hV₂ _ (by omega)).trans (hV ▸ subset_union_right)
      · rw [hV, ← D₁.vertexSet_iUnion', ← D₂.vertexSet_iUnion']
        refine union_subset (iUnion₂_subset fun i hi => ?_) (iUnion₂_subset fun i hi => ?_)
        · exact fun x hx => mem_iUnion₂.mpr ⟨i, by omega, by rw [hG₁ i hi]; exact hx⟩
        · refine fun x hx => mem_iUnion₂.mpr ⟨D₁.r + i, by omega, ?_⟩
          rw [hG₂ (D₁.r + i) (by omega), show D₁.r + i - D₁.r = i by omega]
          exact hx)
    (by
      refine Subset.antisymm (iUnion₂_subset fun i hi => ?_) ?_
      · rcases Nat.lt_or_ge i D₁.r with h | h
        · rw [hG₁ i h, hE]
          exact (D₁.Gn_le h).edgeSet_mono.trans subset_union_left
        · rw [hG₂ i h, hE]
          exact (D₂.Gn_le (by omega)).edgeSet_mono.trans subset_union_right
      · rw [hE, ← D₁.edgeSet_iUnion', ← D₂.edgeSet_iUnion']
        refine union_subset (iUnion₂_subset fun i hi => ?_) (iUnion₂_subset fun i hi => ?_)
        · exact fun x hx => mem_iUnion₂.mpr ⟨i, by omega, by rw [hG₁ i hi]; exact hx⟩
        · refine fun x hx => mem_iUnion₂.mpr ⟨D₁.r + i, by omega, ?_⟩
          rw [hG₂ (D₁.r + i) (by omega), show D₁.r + i - D₁.r = i by omega]
          exact hx)
    (fun i j hi hj hij => by
      rcases Nat.lt_or_ge i D₁.r with h | h <;> rcases Nat.lt_or_ge j D₁.r with h' | h'
      · rw [hG₁ i h, hG₁ j h']
        exact D₁.edge_disjoint' h h' hij
      · rw [hG₁ i h, hG₂ j h']
        exact hdisj.mono (D₁.Gn_le h).edgeSet_mono (D₂.Gn_le (by omega)).edgeSet_mono
      · rw [hG₂ i h, hG₁ j h']
        exact hdisj.symm.mono (D₂.Gn_le (by omega)).edgeSet_mono (D₁.Gn_le h').edgeSet_mono
      · rw [hG₂ i h, hG₂ j h']
        exact D₂.edge_disjoint' (by omega) (by omega) (by omega))
    (fun h i j hhi hij hj => by
      rcases Nat.lt_or_ge j D₁.r with hj' | hj'
      · rw [hG₁ h (by omega), hG₁ i (by omega), hG₁ j hj']
        exact D₁.vertex_inter_subset' hhi hij hj'
      rcases Nat.lt_or_ge h D₁.r with hh' | hh'
      · rw [hG₁ h hh', hG₂ j hj']
        have hsub : V(D₁.Gn h) ∩ V(D₂.Gn (j - D₁.r)) ⊆ D₁.Yn D₁.r :=
          hJ₁ ▸ inter_subset_inter (hV₁ h hh') (hV₂ _ (by omega))
        rcases Nat.lt_or_ge i D₁.r with hi' | hi'
        · rw [hG₁ i hi']
          intro x hx
          exact D₁.vertex_inter_subset' hhi (by omega : i ≤ D₁.r - 1) (by omega)
            ⟨hx.1, hJa (hsub hx)⟩
        · rw [hG₂ i hi']
          intro x hx
          exact D₂.vertex_inter_subset' (Nat.zero_le _) (by omega : i - D₁.r ≤ j - D₁.r)
            (by omega) ⟨hJb (hsub hx), hx.2⟩
      · rw [hG₂ h hh', hG₂ i (by omega), hG₂ j hj']
        exact D₂.vertex_inter_subset' (by omega) (by omega) (by omega))
    (fun i hi => by
      rcases Nat.lt_or_ge (i + 1) D₁.r with h | h
      · rw [hG₁ i (by omega), hG₁ (i + 1) h, hY₁ (i + 1) h.le]
        exact D₁.adj_vertex_inter' h
      rcases eq_or_lt_of_le h with h' | h'
      · rw [hG₁ i (by omega), hG₂ (i + 1) h, hY₁ (i + 1) h'.ge,
          show i + 1 - D₁.r = 0 by omega, ← h']
        have hi' : D₁.r - 1 = i := by omega
        refine Subset.antisymm ?_ fun x hx => ⟨?_, hJb hx⟩
        · rw [← hJ₁]
          exact inter_subset_inter (hV₁ i (by omega)) (hV₂ 0 (by omega))
        · rw [← hi']
          exact hJa hx
      · rw [hG₂ i (by omega), hG₂ (i + 1) h, hY₂ (i + 1) h,
          show i + 1 - D₁.r = i - D₁.r + 1 by omega]
        exact D₂.adj_vertex_inter' (by omega))
    (by
      rw [hY₁ 0 (Nat.zero_le _), hY₂ _ (by omega), show D₁.r + D₂.r - D₁.r = D₂.r by omega]
      exact hT)

theorem append_r {X₁ X₂ : Graft α β} {D₁ : GraftPathDecomposition 𝒜 X₁}
    {D₂ : GraftPathDecomposition 𝒜 X₂} {h₁ h₂ hV hE hdisj hJ₁ hJ₂ hT} :
    (append (X := X) D₁ D₂ h₁ h₂ hV hE hdisj hJ₁ hJ₂ hT).r = D₁.r + D₂.r := rfl

theorem append_Yn_left {X₁ X₂ : Graft α β} {D₁ : GraftPathDecomposition 𝒜 X₁}
    {D₂ : GraftPathDecomposition 𝒜 X₂} {h₁ h₂ hV hE hdisj hJ₁ hJ₂ hT} {j : ℕ} (hj : j ≤ D₁.r) :
    (append (X := X) D₁ D₂ h₁ h₂ hV hE hdisj hJ₁ hJ₂ hT).Yn j = D₁.Yn j := by
  rw [append, ofNat_Yn (by omega)]
  simp [hj]

theorem append_Yn_right {X₁ X₂ : Graft α β} {D₁ : GraftPathDecomposition 𝒜 X₁}
    {D₂ : GraftPathDecomposition 𝒜 X₂} {h₁ h₂ hV hE hdisj hJ₁ hJ₂ hT} {j : ℕ} (hj : D₁.r ≤ j)
    (hj' : j ≤ D₁.r + D₂.r) :
    (append (X := X) D₁ D₂ h₁ h₂ hV hE hdisj hJ₁ hJ₂ hT).Yn j = D₂.Yn (j - D₁.r) := by
  rw [append, ofNat_Yn hj']
  rcases eq_or_lt_of_le hj with rfl | hlt
  · simp [hJ₂]
  · simp [show ¬ j ≤ D₁.r by omega]

/-- **Changing the class of pieces.** A path-decomposition over `𝒜` whose pieces all lie in `ℬ`
is a path-decomposition over `ℬ` with the same graphs and junctions. -/
def recast {ℬ : Set (Graft α β)} (D : GraftPathDecomposition 𝒜 X)
    (h : ∀ i < D.r, ∀ h hf, Graft.mk (D.Gn i) (D.Yn i ∪ D.Yn (i + 1)) h hf ∈ ℬ) :
    GraftPathDecomposition ℬ X :=
  ofNat D.r D.hr D.Gn D.Yn (fun i hi => D.Yn_subset hi) (fun i hi => D.Gn_le hi) h
    D.vertexSet_iUnion' D.edgeSet_iUnion' (fun i j hi hj hij => D.edge_disjoint' hi hj hij)
    (fun h i j hhi hij hj => D.vertex_inter_subset' hhi hij hj)
    (fun i hi => D.adj_vertex_inter' hi) D.T_eq'

theorem recast_r {ℬ : Set (Graft α β)} {D : GraftPathDecomposition 𝒜 X} {h} :
    (recast (ℬ := ℬ) D h).r = D.r := rfl

theorem recast_Yn {ℬ : Set (Graft α β)} {D : GraftPathDecomposition 𝒜 X} {h} {j : ℕ}
    (hj : j ≤ D.r) : (recast (ℬ := ℬ) D h).Yn j = D.Yn j := by
  rw [recast, ofNat_Yn hj]

/-- **Reversing a path-decomposition.** The parts in the opposite order form a path-decomposition
with the junctions in the opposite order. -/
def reverse (D : GraftPathDecomposition 𝒜 X) : GraftPathDecomposition 𝒜 X :=
  have hr := D.hr
  ofNat D.r D.hr (fun i => D.Gn (D.r - 1 - i)) (fun j => D.Yn (D.r - j))
    (fun i hi => by
      have := D.Yn_subset (i := D.r - 1 - i) (by omega)
      rw [show D.r - 1 - i + 1 = D.r - i by omega] at this
      rw [show D.r - (i + 1) = D.r - 1 - i by omega, union_comm]
      exact this)
    (fun i hi => D.Gn_le (by omega))
    (fun i hi h hf => graft_mem_of_eq rfl
      (by rw [show D.r - (i + 1) = D.r - 1 - i by omega, union_comm,
        show D.r - i = D.r - 1 - i + 1 by omega])
      (D.mem_𝒜' (i := D.r - 1 - i) (by omega) (D.Yn_subset (by omega)) (D.isFiniteGraph_Gn (by omega))))
    (by
      rw [← D.vertexSet_iUnion']
      ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨i, hi, hx⟩
        exact ⟨D.r - 1 - i, by omega, hx⟩
      · rintro ⟨i, hi, hx⟩
        exact ⟨D.r - 1 - i, by omega, by rwa [show D.r - 1 - (D.r - 1 - i) = i by omega]⟩)
    (by
      rw [← D.edgeSet_iUnion']
      ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨i, hi, hx⟩
        exact ⟨D.r - 1 - i, by omega, hx⟩
      · rintro ⟨i, hi, hx⟩
        exact ⟨D.r - 1 - i, by omega, by rwa [show D.r - 1 - (D.r - 1 - i) = i by omega]⟩)
    (fun i j hi hj hij => D.edge_disjoint' (by omega) (by omega) (by omega))
    (fun h i j hhi hij hj => by
      rw [inter_comm]
      exact D.vertex_inter_subset' (by omega) (by omega) (by omega))
    (fun i hi => by
      have := D.adj_vertex_inter' (i := D.r - 1 - (i + 1)) (by omega)
      rw [show D.r - 1 - (i + 1) + 1 = D.r - 1 - i by omega] at this
      rw [inter_comm, this, show D.r - (i + 1) = D.r - 1 - i by omega])
    (by rw [D.T_eq', Nat.sub_zero, Nat.sub_self, union_comm])

theorem reverse_r {D : GraftPathDecomposition 𝒜 X} : D.reverse.r = D.r := rfl

theorem reverse_Yn {D : GraftPathDecomposition 𝒜 X} {j : ℕ} (hj : j ≤ D.r) :
    D.reverse.Yn j = D.Yn (D.r - j) := by
  rw [reverse, ofNat_Yn hj]

end GraftPathDecomposition

/-- A path-decomposition whose inner junctions have `k` vertices, and with `k` disjoint paths
between its first and last inner junctions when it has at least three parts, makes its graft a
`k`-train. This is the definition of `IsKTrain`, read through natural-number indices. -/
theorem isKTrain_of_decomposition {𝒜 : Set (Graft α β)} {X : Graft α β} {k : ℕ}
    (D : GraftPathDecomposition 𝒜 X) (hcard : ∀ i, 1 ≤ i → i < D.r → (D.Yn i).ncard = k)
    (hlink : 3 ≤ D.r → HasDisjointGraphPathsFromTo X.G (D.Yn 1) (D.Yn (D.r - 1)) k) :
    IsKTrain 𝒜 k X := by
  refine ⟨D, fun i hi h1 h2 => ?_, fun hr3 => ?_⟩
  · have := hcard i h1 h2
    simpa [GraftPathDecomposition.Yn, hi] using this
  · have := hlink hr3
    simpa [GraftPathDecomposition.Yn, show 1 < D.r + 1 by omega,
      show D.r - 1 < D.r + 1 by omega] using this

/-- **A fan of pieces.** Let the graph of `X` be the union of finitely many subgraphs `Q i`, with
no common edges, each containing `J`, and any two meeting only in `J`. If the roots of `X` are
`J` and each `(Q i, J)` lies in `𝒜`, then `X` has a path-decomposition whose junctions are all
`J`, with one part for each `Q i`. The proof adds the pieces one at a time
(`GraftPathDecomposition.append`). -/
theorem exists_fan_decomposition {𝒜 : Set (Graft α β)} {ι : Type*} [DecidableEq ι]
    (Q : ι → Graph α β) (J : Set α) (s : Finset ι) (hs : s.Nonempty) :
    ∀ X : Graft α β,
      (∀ i ∈ s, Q i ≤ X.G) → (∀ i ∈ s, J ⊆ V(Q i)) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → V(Q i) ∩ V(Q j) ⊆ J) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint E(Q i) E(Q j)) →
      V(X.G) = (⋃ i ∈ s, V(Q i)) → E(X.G) = (⋃ i ∈ s, E(Q i)) → X.T = J →
      (∀ i ∈ s, ∀ h hf, Graft.mk (Q i) J h hf ∈ 𝒜) →
      ∃ D : GraftPathDecomposition 𝒜 X, D.r = s.card ∧ ∀ j ≤ D.r, D.Yn j = J := by
  induction s using Finset.induction_on with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | insert a s has ih =>
    intro X hle hJ hV hE hVU hEU hT hmem
    have ha : a ∈ insert a s := Finset.mem_insert_self a s
    have hJa : J ⊆ V(Q a) := hJ a ha
    have hfa : IsFiniteGraph (Q a) :=
      ⟨X.finite_G.1.subset (hle a ha).vertexSet_mono, X.finite_G.2.subset (hle a ha).edgeSet_mono⟩
    have hJJ : J ∪ J ⊆ V(Q a) := (union_self J).symm ▸ hJa
    let Xa : Graft α β := ⟨Q a, J ∪ J, hJJ, hfa⟩
    have hma : Graft.mk Xa.G (J ∪ J) hJJ Xa.finite_G ∈ 𝒜 :=
      GraftPathDecomposition.graft_mem_of_eq rfl (union_self J) (hmem a ha hJa hfa)
    let Da : GraftPathDecomposition 𝒜 Xa := GraftPathDecomposition.single hJJ hma rfl
    rcases s.eq_empty_or_nonempty with rfl | hsne
    · -- one piece: the graph of `X` is `Q a`
      have hXG : X.G = Q a := by
        refine ((Compatible.of_le (hle a ha)).ext ?_ ?_).symm
        · simpa using hVU.symm
        · simpa using hEU.symm
      have hJX : J ∪ J ⊆ V(X.G) := hXG ▸ hJJ
      have hm : Graft.mk X.G (J ∪ J) hJX X.finite_G ∈ 𝒜 :=
        GraftPathDecomposition.graft_mem_of_eq hXG (union_self J) (hmem a ha hJa hfa)
      refine ⟨GraftPathDecomposition.single hJX hm (by rw [hT, union_self]), rfl, ?_⟩
      intro j hj
      rw [GraftPathDecomposition.single_r] at hj
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
      · exact GraftPathDecomposition.single_Yn_zero
      · exact GraftPathDecomposition.single_Yn_one
    -- several pieces: the union of the others, then `Q a`
    have hs' : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    set V' : Set α := ⋃ i ∈ s, V(Q i) with hV'
    set E' : Set β := ⋃ i ∈ s, E(Q i) with hE'
    have hV'X : V' ⊆ V(X.G) :=
      iUnion₂_subset fun i hi => (hle i (hs' i hi)).vertexSet_mono
    have hE'eq : E(subOf X.G V' E') = E' := by
      rw [subOf_edgeSet]
      refine Subset.antisymm (fun e he => he.1) fun e he => ⟨he, ?_⟩
      obtain ⟨i, hi, he'⟩ := mem_iUnion₂.mp he
      obtain ⟨x, y, hxy⟩ : ∃ x y, (Q i).IsLink e x y := exists_isLink_of_mem_edgeSet he'
      exact ⟨x, y, hxy.mono (hle i (hs' i hi)), mem_iUnion₂.mpr ⟨i, hi, hxy.left_mem⟩,
        mem_iUnion₂.mpr ⟨i, hi, hxy.right_mem⟩⟩
    obtain ⟨i₀, hi₀⟩ := hsne
    have hJV' : J ⊆ V' := (hJ i₀ (hs' i₀ hi₀)).trans (subset_biUnion_of_mem (u := fun i => V(Q i)) hi₀)
    let X' : Graft α β := ⟨subOf X.G V' E', J, hJV',
      ⟨X.finite_G.1.subset hV'X, X.finite_G.2.subset (subOf_le X.G hV'X E').edgeSet_mono⟩⟩
    have hleX' : ∀ i ∈ s, Q i ≤ X'.G := by
      intro i hi
      refine ⟨subset_biUnion_of_mem (u := fun i => V(Q i)) hi, fun e x y (h : (Q i).IsLink e x y) => ?_⟩
      change (subOf X.G V' E').IsLink e x y
      rw [subOf_isLink]
      exact ⟨mem_iUnion₂.mpr ⟨i, hi, h.edge_mem⟩, h.mono (hle i (hs' i hi)),
        mem_iUnion₂.mpr ⟨i, hi, h.left_mem⟩, mem_iUnion₂.mpr ⟨i, hi, h.right_mem⟩⟩
    obtain ⟨D', hD'r, hD'Y⟩ := ih ⟨i₀, hi₀⟩ X' hleX' (fun i hi => hJ i (hs' i hi))
      (fun i hi j hj => hV i (hs' i hi) j (hs' j hj)) (fun i hi j hj => hE i (hs' i hi) j (hs' j hj))
      rfl hE'eq rfl (fun i hi => hmem i (hs' i hi))
    have hVa : V(X.G) = V(X'.G) ∪ V(Xa.G) := by
      rw [hVU, Finset.set_biUnion_insert, union_comm]
      rfl
    have hEa : E(X.G) = E(X'.G) ∪ E(Xa.G) := by
      rw [hEU, Finset.set_biUnion_insert, union_comm]
      change _ = E(subOf X.G V' E') ∪ _
      rw [hE'eq]
    have hdisj : Disjoint E(X'.G) E(Xa.G) := by
      change Disjoint E(subOf X.G V' E') E(Q a)
      rw [hE'eq, hE', disjoint_iUnion₂_left]
      intro i hi
      exact hE i (hs' i hi) a ha (fun h => has (h ▸ hi))
    have hJ₁ : V(X'.G) ∩ V(Xa.G) = D'.Yn D'.r := by
      rw [hD'Y _ le_rfl]
      refine Subset.antisymm ?_ (subset_inter hJV' hJa)
      change V' ∩ V(Q a) ⊆ J
      rw [hV', iUnion₂_inter]
      exact iUnion₂_subset fun i hi => hV i (hs' i hi) a ha (fun h => has (h ▸ hi))
    have hJ₂ : Da.Yn 0 = D'.Yn D'.r := by
      rw [hD'Y _ le_rfl]
      exact GraftPathDecomposition.single_Yn_zero
    have hTa : X.T = D'.Yn 0 ∪ Da.Yn Da.r := by
      rw [hD'Y 0 (Nat.zero_le _), hT, GraftPathDecomposition.single_r,
        GraftPathDecomposition.single_Yn_one, union_self]
    refine ⟨GraftPathDecomposition.append D' Da (subOf_le X.G hV'X E') (hle a ha) hVa hEa hdisj hJ₁ hJ₂ hTa,
      ?_, ?_⟩
    · rw [GraftPathDecomposition.append_r, hD'r, GraftPathDecomposition.single_r,
        Finset.card_insert_of_notMem has]
    · intro j hj
      rw [GraftPathDecomposition.append_r, GraftPathDecomposition.single_r] at hj
      rcases Nat.lt_or_ge j (D'.r + 1) with h | h
      · rw [GraftPathDecomposition.append_Yn_left (by omega)]
        exact hD'Y j (by omega)
      · rw [GraftPathDecomposition.append_Yn_right (by omega) (by
          rw [GraftPathDecomposition.single_r]; omega)]
        rw [show j - D'.r = 1 by omega]
        exact GraftPathDecomposition.single_Yn_one

end GraphMinor.GM08
