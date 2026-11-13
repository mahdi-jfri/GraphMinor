module

public import GraphMinor.GM21.Section12One

/-!
# Graph Minors XXI, Section 12: tools for chains

The proof of (12.4) cuts a graph into pieces that each carry a unique set of disjoint paths, and
glues the pieces back. This file has the steps on sets of disjoint paths that this needs.

* `UniqSystem.deleteFirst`: deleting the first vertex `v ∈ Y \ Z` of its path; the second vertex
  of that path takes its place in `Y`.
* `UniqSystem.deleteTrivial`: deleting a vertex of `Y ∩ Z`, whose path has one vertex.
* `UniqSystem.isChain_deleteVertices`: deleting both ends sets `Y` and `Z` leaves a chain.

Paths are handled as families of sequences (`IsPathFam`), as in the proof of (12.1).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set Hypergraph

universe u v w

variable {α : Type u} {β : Type v}

/-! ## Families -/

section Fam

variable {ι : Type w} {K : Hypergraph α β} {I : Set ι} {c : ι → ℕ → α} {n : ι → ℕ}
  {f : ι → ℕ → β}

theorem IsPathFam.restrict (hF : IsPathFam K I c n f) {J : Set ι} (hJ : J ⊆ I) :
    IsPathFam K J c n f :=
  ⟨fun i hi ↦ hF.inj i (hJ hi), fun i hi j hj ↦ hF.disj i (hJ hi) j (hJ hj),
    fun i hi ↦ hF.mem i (hJ hi), fun i hi ↦ hF.edge_mem i (hJ hi), fun i hi ↦ hF.ends i (hJ hi)⟩

theorem famVerts_mono {J : Set ι} (hJ : J ⊆ I) : famVerts J c n ⊆ famVerts I c n := fun x hx ↦ by
  obtain ⟨i, hi, a, ha, rfl⟩ := mem_famVerts.1 hx
  exact mem_famVerts.2 ⟨i, hJ hi, a, ha, rfl⟩

theorem famEdges_mono {J : Set ι} (hJ : J ⊆ I) : famEdges J n f ⊆ famEdges I n f := fun x hx ↦ by
  obtain ⟨i, hi, a, ha, rfl⟩ := mem_famEdges.1 hx
  exact mem_famEdges.2 ⟨i, hJ hi, a, ha, rfl⟩

theorem famVerts_union {J : Set ι} : famVerts (I ∪ J) c n = famVerts I c n ∪ famVerts J c n := by
  ext x
  simp only [mem_famVerts, mem_union]
  constructor
  · rintro ⟨i, hi | hi, h⟩
    exacts [Or.inl ⟨i, hi, h⟩, Or.inr ⟨i, hi, h⟩]
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
    exacts [⟨i, Or.inl hi, h⟩, ⟨i, Or.inr hi, h⟩]

theorem famEdges_union {J : Set ι} : famEdges (I ∪ J) n f = famEdges I n f ∪ famEdges J n f := by
  ext x
  simp only [mem_famEdges, mem_union]
  constructor
  · rintro ⟨i, hi | hi, h⟩
    exacts [Or.inl ⟨i, hi, h⟩, Or.inr ⟨i, hi, h⟩]
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
    exacts [⟨i, Or.inl hi, h⟩, ⟨i, Or.inr hi, h⟩]

/-- Add the path with the one vertex `v`, with index `i₀`. -/
noncomputable def trivC (i₀ : ι) (v : α) (c : ι → ℕ → α) : ι → ℕ → α := by
  classical exact fun i a ↦ if i = i₀ then v else c i a

/-- The lengths after `trivC`. -/
noncomputable def trivN (i₀ : ι) (n : ι → ℕ) : ι → ℕ := by
  classical exact fun i ↦ if i = i₀ then 0 else n i

@[simp] theorem trivC_self {i₀ : ι} {v : α} {a : ℕ} : trivC i₀ v c i₀ a = v := by simp [trivC]
@[simp] theorem trivC_of_ne {i i₀ : ι} {v : α} {a : ℕ} (h : i ≠ i₀) : trivC i₀ v c i a = c i a := by
  simp [trivC, h]
@[simp] theorem trivN_self {i₀ : ι} : trivN i₀ n i₀ = 0 := by simp [trivN]
@[simp] theorem trivN_of_ne {i i₀ : ι} (h : i ≠ i₀) : trivN i₀ n i = n i := by simp [trivN, h]

/-- **Adding a path with one vertex.** -/
theorem IsPathFam.insertTrivial (hF : IsPathFam K I c n f) {i₀ : ι} (hi₀ : i₀ ∉ I) {v : α}
    (hv : v ∈ K.vertexSet) (hvF : v ∉ famVerts I c n) :
    IsPathFam K (insert i₀ I) (trivC i₀ v c) (trivN i₀ n) f ∧
      famVerts (insert i₀ I) (trivC i₀ v c) (trivN i₀ n) = insert v (famVerts I c n) ∧
      famEdges (insert i₀ I) (trivN i₀ n) f = famEdges I n f := by
  have hne : ∀ i ∈ I, i ≠ i₀ := fun i hi h ↦ hi₀ (h ▸ hi)
  have himg : ∀ i ∈ I, trivC i₀ v c i '' Iic (trivN i₀ n i) = c i '' Iic (n i) := fun i hi ↦ by
    rw [trivN_of_ne (hne i hi)]
    exact image_congr fun a _ ↦ trivC_of_ne (hne i hi)
  have himg₀ : trivC i₀ v c i₀ '' Iic (trivN i₀ n i₀) = {v} := by
    rw [trivN_self]
    ext x
    simp
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i hi
    rcases mem_insert_iff.1 hi with rfl | hi
    · intro a ha b hb _
      rw [trivN_self, mem_Iic, Nat.le_zero] at ha hb
      rw [ha, hb]
    · intro a ha b hb h
      rw [trivN_of_ne (hne i hi)] at ha hb
      rw [trivC_of_ne (hne i hi), trivC_of_ne (hne i hi)] at h
      exact hF.inj i hi ha hb h
  · intro i hi j hj hij
    have hv' : ∀ j ∈ I, v ∉ c j '' Iic (n j) := fun j hj h ↦ by
      obtain ⟨a, ha, he⟩ := h
      exact hvF (mem_famVerts.2 ⟨j, hj, a, ha, he⟩)
    rcases mem_insert_iff.1 hi with hi' | hi' <;> rcases mem_insert_iff.1 hj with hj' | hj'
    · exact absurd (hi'.trans hj'.symm) hij
    · rw [hi', himg₀, himg j hj', disjoint_singleton_left]
      exact hv' j hj'
    · rw [hj', himg₀, himg i hi', disjoint_singleton_right]
      exact hv' i hi'
    · rw [himg i hi', himg j hj']
      exact hF.disj i hi' j hj' hij
  · intro i hi a ha
    rcases mem_insert_iff.1 hi with rfl | hi
    · rw [trivC_self]; exact hv
    · rw [trivN_of_ne (hne i hi)] at ha
      rw [trivC_of_ne (hne i hi)]
      exact hF.mem i hi a ha
  · intro i hi a ha
    rcases mem_insert_iff.1 hi with rfl | hi
    · rw [trivN_self] at ha; exact absurd ha (Nat.not_lt_zero _)
    · rw [trivN_of_ne (hne i hi)] at ha
      exact hF.edge_mem i hi a ha
  · intro i hi a ha
    rcases mem_insert_iff.1 hi with rfl | hi
    · rw [trivN_self] at ha; exact absurd ha (Nat.not_lt_zero _)
    · rw [trivN_of_ne (hne i hi)] at ha
      rw [trivC_of_ne (hne i hi), trivC_of_ne (hne i hi)]
      exact hF.ends i hi a ha
  · ext x
    simp only [mem_famVerts, mem_insert_iff]
    constructor
    · rintro ⟨i, rfl | hi, a, ha, rfl⟩
      · exact Or.inl trivC_self
      · rw [trivN_of_ne (hne i hi)] at ha
        exact Or.inr ⟨i, hi, a, ha, (trivC_of_ne (hne i hi)).symm⟩
    · rintro (rfl | ⟨i, hi, a, ha, rfl⟩)
      · exact ⟨i₀, Or.inl rfl, 0, by rw [trivN_self], trivC_self⟩
      · exact ⟨i, Or.inr hi, a, by rw [trivN_of_ne (hne i hi)]; exact ha, trivC_of_ne (hne i hi)⟩
  · ext g
    simp only [mem_famEdges, mem_insert_iff]
    constructor
    · rintro ⟨i, rfl | hi, a, ha, rfl⟩
      · rw [trivN_self] at ha; exact absurd ha (Nat.not_lt_zero _)
      · rw [trivN_of_ne (hne i hi)] at ha
        exact ⟨i, hi, a, ha, rfl⟩
    · rintro ⟨i, hi, a, ha, rfl⟩
      exact ⟨i, Or.inr hi, a, by rw [trivN_of_ne (hne i hi)]; exact ha, rfl⟩

end Fam

/-! ## Good families indexed by their first vertices -/

section Good

variable {K : Hypergraph α β} {Y Z : Set α} {c : α → ℕ → α} {n : α → ℕ} {f : α → ℕ → β}

/-- A vertex of the path of `y` that lies in `Y` is its first vertex. -/
theorem IsGoodFam.eq_zero_of_mem (hF : IsGoodFam K Y Z Y c n f) (hc0 : ∀ y ∈ Y, c y 0 = y)
    {y : α} (hy : y ∈ Y) {a : ℕ} (ha : a ≤ n y) (h : c y a ∈ Y) : a = 0 :=
  (hF.1.eq_of_eq hy h ha (Nat.zero_le _) (by rw [hc0 _ h])).2

/-- If `|Z| = |Y|`, every vertex of `Z` is the last vertex of a path. -/
theorem IsGoodFam.exists_end (hF : IsGoodFam K Y Z Y c n f) (hZf : Z.Finite)
    (hYZ : Z.ncard = Y.ncard) {z : α} (hz : z ∈ Z) : ∃ y ∈ Y, c y (n y) = z := by
  have hinj : InjOn (fun y ↦ c y (n y)) Y := fun y hy y' hy' h ↦
    (hF.1.eq_of_eq hy hy' le_rfl le_rfl h).1
  have himg : (fun y ↦ c y (n y)) '' Y = Z :=
    eq_of_subset_of_ncard_le (by rintro _ ⟨y, hy, rfl⟩; exact (hF.2.2.2 y hy).2)
      (by rw [hinj.ncard_image, hYZ]) hZf
  rw [← himg] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨y, hy, rfl⟩

/-- If `|Z| = |Y|`, a vertex of the path of `y` that lies in `Z` is its last vertex. -/
theorem IsGoodFam.eq_last_of_mem (hF : IsGoodFam K Y Z Y c n f) (hZf : Z.Finite)
    (hYZ : Z.ncard = Y.ncard) {y : α} (hy : y ∈ Y) {a : ℕ} (ha : a ≤ n y) (h : c y a ∈ Z) :
    a = n y := by
  obtain ⟨y', hy', he⟩ := hF.exists_end hZf hYZ h
  obtain ⟨rfl, h'⟩ := hF.1.eq_of_eq hy hy' ha le_rfl he.symm
  exact h'

end Good

/-! ## Unique sets of disjoint paths -/

section Uniq

variable {K : Hypergraph α β} {Y Z : Set α} {k : ℕ}

theorem IsPathSystem.symm {M : Hypergraph α β} (h : IsPathSystem K Y Z k M) :
    IsPathSystem K Z Y k M :=
  ⟨h.1, h.2.1, fun P hP ↦ by
    obtain ⟨y, hy, z, hz, rfl⟩ := h.2.2 P hP
    exact ⟨z, hz, y, hy, pair_comm _ _⟩⟩

theorem UniqSystem.symm (h : UniqSystem K Y Z k) : UniqSystem K Z Y k := by
  obtain ⟨M, hM, hMu, hMV⟩ := h
  exact ⟨M, hM.symm, fun M' hM' ↦ hMu M' hM'.symm, hMV⟩

/-- The first vertices of the paths are vertices of `K`. -/
theorem UniqSystem.subset_left [Nonempty β] (h : UniqSystem K Y Z k) (hYf : Y.Finite)
    (hY : Y.ncard = k) : Y ⊆ K.vertexSet := by
  intro y hy
  have : Nonempty α := ⟨y⟩
  obtain ⟨M, hM, -, -⟩ := h
  obtain ⟨c, n, f, hF, hc0, -⟩ := exists_goodFam_of_isPathSystem hYf (hY ▸ hM)
  have := hF.1.mem y hy 0 (Nat.zero_le _)
  rwa [hc0 y hy] at this

theorem UniqSystem.subset_right [Nonempty β] (h : UniqSystem K Y Z k) (hZf : Z.Finite)
    (hZ : Z.ncard = k) : Z ⊆ K.vertexSet :=
  h.symm.subset_left hZf hZ

/-- Deleting the vertices of `∅`. -/
theorem deleteVertices_empty' (K : Hypergraph α β) : K.deleteVertices ∅ = K := by
  ext x <;> simp [Hypergraph.deleteVertices]

/-- Deleting `X` and then `X'` deletes `X ∪ X'`. -/
theorem deleteVertices_deleteVertices' (K : Hypergraph α β) (X X' : Set α) :
    (K.deleteVertices X).deleteVertices X' = K.deleteVertices (X ∪ X') := by
  ext x y
  · simp only [Hypergraph.deleteVertices, mem_sdiff, mem_union]
    tauto
  · simp only [Hypergraph.deleteVertices, mem_ofPred_eq, mem_union]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun w hw hinc ↦ ?_⟩
      rcases hw with hw | hw
      · exact h2 w hw hinc
      · exact h3 w hw ⟨hinc, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun w hw ↦ h2 w (Or.inl hw)⟩, fun w hw hinc ↦ h2 w (Or.inr hw) hinc.1⟩
  · simp only [Hypergraph.deleteVertices, mem_union]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun w hw hinc ↦ ?_⟩
      rcases hw with hw | hw
      · exact h2 w hw hinc
      · exact h3 w hw ⟨hinc, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun w hw ↦ h2 w (Or.inl hw)⟩, fun w hw hinc ↦ h2 w (Or.inr hw) hinc.1⟩

/-- **Deleting the first vertex `v ∈ Y \ Z` of its path.** The second vertex `v₁` of the path
takes the place of `v` in `Y`. -/
theorem UniqSystem.deleteFirst [Nonempty β] (hU : UniqSystem K Y Z k) (hYf : Y.Finite)
    (hY : Y.ncard = k) {v : α} (hvY : v ∈ Y) (hvZ : v ∉ Z) :
    ∃ v₁ ∉ Y, UniqSystem (K.deleteVertices {v}) (insert v₁ (Y \ {v})) Z k := by
  classical
  have : Nonempty α := ⟨v⟩
  obtain ⟨M, hM, hMu, hMV⟩ := hU
  obtain ⟨c, n, f, hF, hc0, hfam⟩ := exists_goodFam_of_isPathSystem hYf (hY ▸ hM)
  have hFp := hF.1
  have hnv : 1 ≤ n v := by
    by_contra h0
    have h0' : n v = 0 := by omega
    have := (hF.2.2.2 v hvY).2
    rw [h0', hc0 v hvY] at this
    exact hvZ this
  have hv₁Y : c v 1 ∉ Y := fun h ↦ by
    have := hF.eq_zero_of_mem hc0 hvY hnv h
    omega
  have hvK : v ∈ K.vertexSet := by
    have := hFp.mem v hvY 0 (Nat.zero_le _)
    rwa [hc0 v hvY] at this
  have hgK : f v 0 ∈ K.edgeSet := hFp.edge_mem v hvY 0 hnv
  have hge : K.ends (f v 0) = {v, c v 1} := by rw [hFp.ends v hvY 0 hnv, hc0 v hvY]
  obtain ⟨hF₁, hV₁, hvF₁, hE₁', hgF₁⟩ := hFp.shift hvY hnv
  rw [hc0 v hvY] at hV₁ hvF₁
  have hK₁K : K.deleteVertices {v} ≤ K := GM10.deleteVertices_le K {v}
  have hFV : famVerts Y c n = M.vertexSet := by rw [← hfam, famGraph_vertexSet hFp]
  have hFE : famEdges Y n f = M.edgeSet := by rw [← hfam, famGraph_edgeSet hFp]
  have hF₁K₁ : IsPathFam (K.deleteVertices {v}) Y (shiftC v c) (shiftN v n) (shiftF v f) := by
    refine hF₁.of_le hK₁K (fun x hx ↦ ⟨famVerts_subset hF₁ hx, fun h ↦
      hvF₁ (mem_singleton_iff.1 h ▸ hx)⟩) ?_
    intro e he
    obtain ⟨i, hi, a, ha, rfl⟩ := mem_famEdges.1 he
    refine ⟨hF₁.edge_mem i hi a ha, fun x hx hinc ↦ hvF₁ ?_⟩
    have hxv : x = v := hx
    have : x ∈ famVerts Y (shiftC v c) (shiftN v n) := by
      rcases (hF₁.inc_iff hi ha).1 hinc with h | h
      · rw [h]; exact mem_famVerts.2 ⟨i, hi, a, ha.le, rfl⟩
      · rw [h]; exact mem_famVerts.2 ⟨i, hi, a + 1, ha, rfl⟩
    exact hxv ▸ this
  have hkpos : 1 ≤ k := by
    rw [← hY]; exact Nat.one_le_iff_ne_zero.2 (ncard_ne_zero_of_mem hvY hYf)
  have hY₁k : (insert (c v 1) (Y \ {v})).ncard = k := by
    rw [ncard_insert_of_notMem (fun h ↦ hv₁Y h.1) (hYf.subset sdiff_subset),
      ncard_sdiff_singleton_of_mem hvY, hY]
    omega
  have hY₁f : (insert (c v 1) (Y \ {v})).Finite := (hYf.subset sdiff_subset).insert _
  have hgood₁ : IsGoodFam (K.deleteVertices {v}) (insert (c v 1) (Y \ {v})) Z Y (shiftC v c)
      (shiftN v n) (shiftF v f) := by
    refine ⟨hF₁K₁, hYf, by rw [hY₁k, hY], fun y hy ↦ ?_⟩
    by_cases hyv : y = v
    · rw [hyv, shiftC_self, shiftC_self, shiftN_self, Nat.sub_add_cancel hnv]
      exact ⟨mem_insert _ _, (hF.2.2.2 v hvY).2⟩
    · rw [shiftC_of_ne hyv, shiftC_of_ne hyv, shiftN_of_ne hyv, hc0 y hy]
      exact ⟨mem_insert_of_mem _ ⟨hy, hyv⟩, hc0 y hy ▸ (hF.2.2.2 y hy).2⟩
  have hM₁ := isPathSystem_famGraph hgood₁
  rw [hY₁k] at hM₁
  refine ⟨c v 1, hv₁Y, _, hM₁, fun M' hM' ↦ ?_, ?_⟩
  · obtain ⟨c', n', f', hF', hc0', hfam'⟩ := exists_goodFam_of_isPathSystem hY₁f (hY₁k ▸ hM')
    have hv₁Y₁ : c v 1 ∈ insert (c v 1) (Y \ {v}) := mem_insert _ _
    have hF'K := hF'.1.mono hK₁K
    have hvF' : v ∉ famVerts (insert (c v 1) (Y \ {v})) c' n' := fun h ↦ by
      have := famVerts_subset hF'.1 h
      exact this.2 rfl
    obtain ⟨hF'', hV'', hE''⟩ := hF'K.extend hv₁Y₁ hvK hvF' hgK
      (by rw [hge, hc0' _ hv₁Y₁])
    have hgood'' : IsGoodFam K Y Z (insert (c v 1) (Y \ {v})) (extC (c v 1) v c')
        (extN (c v 1) n') (extF (c v 1) (f v 0) f') := by
      refine ⟨hF'', hY₁f, by rw [hY₁k, hY], fun y hy ↦ ?_⟩
      by_cases hyv : y = c v 1
      · rw [hyv, extC_self_zero, extN_self, extC_self_succ]
        exact ⟨hvY, (hF'.2.2.2 _ hv₁Y₁).2⟩
      · rw [extC_of_ne hyv, extC_of_ne hyv, extN_of_ne hyv]
        refine ⟨?_, (hF'.2.2.2 y hy).2⟩
        rw [hc0' y hy]
        rcases hy with h | hy
        · exact absurd h hyv
        · exact hy.1
    have hM'' := hMu _ (hY ▸ isPathSystem_famGraph hgood'')
    have hV' : famVerts (insert (c v 1) (Y \ {v})) c' n' =
        famVerts Y (shiftC v c) (shiftN v n) := by
      have h1 : insert v (famVerts (insert (c v 1) (Y \ {v})) c' n') =
          insert v (famVerts Y (shiftC v c) (shiftN v n)) := by
        rw [← hV'', ← hV₁, hFV, ← famGraph_vertexSet hF'', hM'']
      rw [← insert_sdiff_self_of_notMem hvF', h1, insert_sdiff_self_of_notMem hvF₁]
    have hgF' : f v 0 ∉ famEdges (insert (c v 1) (Y \ {v})) n' f' := fun h ↦ by
      have := (famGraph_edgeSet hF'.1 ▸ (famGraph_le hF'.1).edgeSet_subset) h
      exact this.2 v rfl (by rw [← mem_ends_iff, hge]; exact mem_insert _ _)
    have hE' : famEdges (insert (c v 1) (Y \ {v})) n' f' =
        famEdges Y (shiftN v n) (shiftF v f) := by
      have h1 : insert (f v 0) (famEdges (insert (c v 1) (Y \ {v})) n' f') =
          insert (f v 0) (famEdges Y (shiftN v n) (shiftF v f)) := by
        rw [← hE'', ← hE₁', hFE, ← famGraph_edgeSet hF'', hM'']
      rw [← insert_sdiff_self_of_notMem hgF', h1, insert_sdiff_self_of_notMem hgF₁]
    rw [← hfam']
    change subOn _ (famVerts _ c' n') (famEdges _ n' f') =
      subOn _ (famVerts Y (shiftC v c) (shiftN v n)) (famEdges Y (shiftN v n) (shiftF v f))
    rw [hV', hE']
  · rw [famGraph_vertexSet hF₁K₁]
    change _ = K.vertexSet \ {v}
    rw [← hMV, ← hFV, hV₁, insert_sdiff_self_of_notMem hvF₁]

/-- The vertices of a family, with the path of `v` having the one vertex `v`. -/
theorem famVerts_eq_insert {ι : Type w} {I : Set ι} {c : ι → ℕ → α} {n : ι → ℕ} {i₀ : ι}
    (hi₀ : i₀ ∈ I) (hn : n i₀ = 0) :
    famVerts I c n = insert (c i₀ 0) (famVerts (I \ {i₀}) c n) := by
  ext x
  simp only [mem_famVerts, mem_insert_iff, mem_sdiff, mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, a, ha, rfl⟩
    by_cases h : i = i₀
    · subst h
      left
      rw [hn, Nat.le_zero] at ha
      rw [ha]
    · exact Or.inr ⟨i, ⟨hi, h⟩, a, ha, rfl⟩
  · rintro (rfl | ⟨i, ⟨hi, -⟩, a, ha, rfl⟩)
    · exact ⟨i₀, hi₀, 0, Nat.zero_le _, rfl⟩
    · exact ⟨i, hi, a, ha, rfl⟩

/-- The edges of a family, when the path of `i₀` has one vertex. -/
theorem famEdges_eq_sdiff {ι : Type w} {I : Set ι} {n : ι → ℕ} {f : ι → ℕ → β} {i₀ : ι}
    (hn : n i₀ = 0) : famEdges I n f = famEdges (I \ {i₀}) n f := by
  ext g
  simp only [mem_famEdges, mem_sdiff, mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, a, ha, rfl⟩
    refine ⟨i, ⟨hi, fun h ↦ ?_⟩, a, ha, rfl⟩
    subst h
    omega
  · rintro ⟨i, ⟨hi, -⟩, a, ha, rfl⟩
    exact ⟨i, hi, a, ha, rfl⟩

/-- **Deleting a vertex `v ∈ Y ∩ Z`.** When `|Y| = |Z| = k`, the path of `v` has the one vertex
`v`, and the other paths stay. -/
theorem UniqSystem.deleteTrivial [Nonempty β] (hU : UniqSystem K Y Z k) (hYf : Y.Finite)
    (hZf : Z.Finite) (hY : Y.ncard = k) (hZ : Z.ncard = k) {v : α} (hvY : v ∈ Y) (hvZ : v ∈ Z) :
    UniqSystem (K.deleteVertices {v}) (Y \ {v}) (Z \ {v}) (k - 1) := by
  classical
  have : Nonempty α := ⟨v⟩
  obtain ⟨M, hM, hMu, hMV⟩ := hU
  obtain ⟨c, n, f, hF, hc0, hfam⟩ := exists_goodFam_of_isPathSystem hYf (hY ▸ hM)
  have hFp := hF.1
  have hZY : Z.ncard = Y.ncard := by rw [hZ, hY]
  have hnv : n v = 0 := by
    obtain ⟨y, hy, he⟩ := hF.exists_end hZf hZY hvZ
    obtain ⟨rfl, h⟩ := hFp.eq_of_eq hy hvY le_rfl (Nat.zero_le _) (he.trans (hc0 v hvY).symm)
    exact h
  have hvK : v ∈ K.vertexSet := by
    have := hFp.mem v hvY 0 (Nat.zero_le _)
    rwa [hc0 v hvY] at this
  have hvR : v ∉ famVerts (Y \ {v}) c n := fun h ↦ by
    obtain ⟨y, hy, a, ha, he⟩ := mem_famVerts.1 h
    exact hy.2 (mem_singleton_iff.2
      (hFp.eq_of_eq hy.1 hvY ha (Nat.zero_le _) (he.trans (hc0 v hvY).symm)).1)
  have hK₁K : K.deleteVertices {v} ≤ K := GM10.deleteVertices_le K {v}
  have hFR := hFp.restrict (sdiff_subset : Y \ {v} ⊆ Y)
  have hFRK₁ : IsPathFam (K.deleteVertices {v}) (Y \ {v}) c n f := by
    refine hFR.of_le hK₁K (fun x hx ↦ ⟨famVerts_subset hFR hx, fun h ↦
      hvR (mem_singleton_iff.1 h ▸ hx)⟩) ?_
    intro e he
    obtain ⟨i, hi, a, ha, rfl⟩ := mem_famEdges.1 he
    refine ⟨hFR.edge_mem i hi a ha, fun x hx hinc ↦ hvR ?_⟩
    have hxv : x = v := hx
    have : x ∈ famVerts (Y \ {v}) c n := by
      rcases (hFR.inc_iff hi ha).1 hinc with h | h
      · rw [h]; exact mem_famVerts.2 ⟨i, hi, a, ha.le, rfl⟩
      · rw [h]; exact mem_famVerts.2 ⟨i, hi, a + 1, ha, rfl⟩
    exact hxv ▸ this
  have hYk : (Y \ {v}).ncard = k - 1 := by rw [ncard_sdiff_singleton_of_mem hvY, hY]
  have hYvf : (Y \ {v}).Finite := hYf.subset sdiff_subset
  have hgood : IsGoodFam (K.deleteVertices {v}) (Y \ {v}) (Z \ {v}) (Y \ {v}) c n f := by
    refine ⟨hFRK₁, hYvf, rfl, fun y hy ↦ ⟨by rw [hc0 y hy.1]; exact hy,
      (hF.2.2.2 y hy.1).2, fun h ↦ ?_⟩⟩
    exact hy.2 (mem_singleton_iff.2 (hFp.eq_of_eq hy.1 hvY le_rfl (Nat.zero_le _)
      ((mem_singleton_iff.1 h).trans (hc0 v hvY).symm)).1)
  have hM₁ := isPathSystem_famGraph hgood
  rw [hYk] at hM₁
  have hFV : famVerts Y c n = M.vertexSet := by rw [← hfam, famGraph_vertexSet hFp]
  have hFE : famEdges Y n f = M.edgeSet := by rw [← hfam, famGraph_edgeSet hFp]
  have hV₀ : famVerts Y c n = insert v (famVerts (Y \ {v}) c n) := by
    rw [famVerts_eq_insert hvY hnv, hc0 v hvY]
  have hE₀ : famEdges Y n f = famEdges (Y \ {v}) n f := famEdges_eq_sdiff hnv
  refine ⟨_, hM₁, fun M' hM' ↦ ?_, ?_⟩
  · obtain ⟨c', n', f', hF', hc0', hfam'⟩ := exists_goodFam_of_isPathSystem hYvf (hYk ▸ hM')
    have hvF' : v ∉ famVerts (Y \ {v}) c' n' := fun h ↦ (famVerts_subset hF'.1 h).2 rfl
    obtain ⟨hF'', hV'', hE''⟩ := (hF'.1.mono hK₁K).insertTrivial (fun h ↦ h.2 rfl) hvK hvF'
    have hidx : insert v (Y \ {v}) = Y := insert_sdiff_singleton_eq hvY
    have hgood'' : IsGoodFam K Y Z (insert v (Y \ {v})) (trivC v v c') (trivN v n') f' := by
      refine ⟨hF'', by rw [hidx]; exact hYf, by rw [hidx], fun y hy ↦ ?_⟩
      by_cases hyv : y = v
      · rw [hyv, trivC_self, trivC_self]
        exact ⟨hvY, hvZ⟩
      · have hy' : y ∈ Y \ {v} := ⟨hidx ▸ hy, hyv⟩
        rw [trivC_of_ne hyv, trivC_of_ne hyv, trivN_of_ne hyv, hc0' y hy']
        exact ⟨hy'.1, (hF'.2.2.2 y hy').2.1⟩
    have hM'' := hMu _ (hY ▸ isPathSystem_famGraph hgood'')
    have hV' : famVerts (Y \ {v}) c' n' = famVerts (Y \ {v}) c n := by
      have h1 : insert v (famVerts (Y \ {v}) c' n') = insert v (famVerts (Y \ {v}) c n) := by
        rw [← hV'', ← hV₀, hFV, ← famGraph_vertexSet hF'', hM'']
      rw [← insert_sdiff_self_of_notMem hvF', h1, insert_sdiff_self_of_notMem hvR]
    have hE' : famEdges (Y \ {v}) n' f' = famEdges (Y \ {v}) n f := by
      rw [← hE'', ← hE₀, hFE, ← famGraph_edgeSet hF'', hM'']
    rw [← hfam']
    change subOn _ (famVerts _ c' n') (famEdges _ n' f') =
      subOn _ (famVerts (Y \ {v}) c n) (famEdges (Y \ {v}) n f)
    rw [hV', hE']
  · rw [famGraph_vertexSet hFRK₁]
    change _ = K.vertexSet \ {v}
    rw [← hMV, ← hFV, hV₀, insert_sdiff_self_of_notMem hvR]

/-- **Deleting a set `R ⊆ Y` of first vertices.** -/
theorem UniqSystem.deleteSet [Nonempty β] : ∀ (R : Finset α) {K : Hypergraph α β} {Y Z : Set α}
    {k : ℕ}, (R : Set α) ⊆ Y → UniqSystem K Y Z k → Y.Finite → Z.Finite → Y.ncard = k →
    Z.ncard = k → ∃ (Y' : Set α) (k' : ℕ), UniqSystem (K.deleteVertices R) Y' (Z \ R) k' ∧
      Y'.Finite ∧ Y'.ncard = k' ∧ (Z \ R).ncard = k' ∧ k' ≤ k ∧ Y \ R ⊆ Y' := by
  classical
  intro R
  induction R using Finset.induction_on with
  | empty =>
    intro K Y Z k _ hU hYf _ hY hZ
    refine ⟨Y, k, ?_, hYf, hY, by simpa using hZ, le_rfl, by simp⟩
    simpa [deleteVertices_empty'] using hU
  | @insert v R hvR ih =>
    intro K Y Z k hRY hU hYf hZf hY hZ
    rw [Finset.coe_insert] at hRY ⊢
    obtain ⟨Y', k', hU', hY'f, hY', hZ', hk', hYY'⟩ :=
      ih (subset_trans (subset_insert _ _) hRY) hU hYf hZf hY hZ
    have hvY' : v ∈ Y' := hYY' ⟨hRY (mem_insert _ _), hvR⟩
    have hdel : (K.deleteVertices ↑R).deleteVertices {v} = K.deleteVertices (insert v ↑R) := by
      rw [deleteVertices_deleteVertices', Set.union_comm, ← insert_eq]
    by_cases hvZ : v ∈ Z
    · have hvZ' : v ∈ Z \ ↑R := ⟨hvZ, hvR⟩
      have h2 := hU'.deleteTrivial hY'f (hZf.subset sdiff_subset) hY' hZ' hvY' hvZ'
      rw [hdel] at h2
      have hZe : (Z \ ↑R) \ {v} = Z \ insert v ↑R := by
        rw [sdiff_sdiff, Set.union_comm, ← insert_eq]
      rw [hZe] at h2
      refine ⟨Y' \ {v}, k' - 1, h2, hY'f.subset sdiff_subset, by
        rw [ncard_sdiff_singleton_of_mem hvY', hY'], by
        rw [← hZe, ncard_sdiff_singleton_of_mem hvZ', hZ'], by omega, ?_⟩
      intro y hy
      exact ⟨hYY' ⟨hy.1, fun h ↦ hy.2 (mem_insert_of_mem _ h)⟩,
        fun h ↦ hy.2 (mem_singleton_iff.1 h ▸ mem_insert _ _)⟩
    · obtain ⟨v₁, hv₁, h1⟩ := hU'.deleteFirst hY'f hY' hvY' (fun h ↦ hvZ h.1)
      rw [hdel] at h1
      have hZe : Z \ insert v ↑R = Z \ ↑R := by
        ext x
        simp only [mem_sdiff, mem_insert_iff, not_or]
        constructor
        · rintro ⟨h, -, h'⟩; exact ⟨h, h'⟩
        · rintro ⟨h, h'⟩; exact ⟨h, fun e ↦ hvZ (e ▸ h), h'⟩
      rw [← hZe] at h1
      have hcard : (insert v₁ (Y' \ {v})).ncard = k' := by
        rw [ncard_insert_of_notMem (fun h ↦ hv₁ h.1) (hY'f.subset sdiff_subset),
          ncard_sdiff_singleton_of_mem hvY', hY']
        have : 1 ≤ k' := by
          rw [← hY']; exact Nat.one_le_iff_ne_zero.2 (ncard_ne_zero_of_mem hvY' hY'f)
        omega
      refine ⟨insert v₁ (Y' \ {v}), k', h1, (hY'f.subset sdiff_subset).insert _, hcard,
        by rw [hZe, hZ'], hk', ?_⟩
      intro y hy
      exact mem_insert_of_mem _ ⟨hYY' ⟨hy.1, fun h ↦ hy.2 (mem_insert_of_mem _ h)⟩,
        fun h ↦ hy.2 (mem_singleton_iff.1 h ▸ mem_insert _ _)⟩

/-- A unique set of `k` disjoint paths between `Y` and `Z`, with `|Y| = |Z| = k ≤ p`, makes `K` a
`p`-chain. -/
theorem isChain_of_uniqSystem [Nonempty β] (hU : UniqSystem K Y Z k) (hYf : Y.Finite)
    (hZf : Z.Finite) (hY : Y.ncard = k) (hZ : Z.ncard = k) {p : ℕ} (hk : k ≤ p) :
    IsChain K p := by
  have h1 := hU.subset_left hYf hY
  have h2 := hU.subset_right hZf hZ
  obtain ⟨M, hM, hMu, hMV⟩ := hU
  subst hY
  exact ⟨Y, Z, h1, h2, hZ.symm, hk, M, hM, hMu, hMV⟩

/-- **Deleting both end sets.** If `K` has a unique set of `k` disjoint paths between `S` and `S'`,
with `|S| = |S'| = k`, and every vertex of `K` is on one of them, then `K \ (S ∪ S')` is a
`k`-chain. -/
theorem UniqSystem.isChain_deleteVertices [Nonempty β] {S S' : Set α} (hU : UniqSystem K S S' k)
    (hSf : S.Finite) (hS'f : S'.Finite) (hS : S.ncard = k) (hS' : S'.ncard = k) :
    IsChain (K.deleteVertices (S ∪ S')) k := by
  obtain ⟨Y', k', hU', hY'f, hY', hZ', hk', -⟩ :=
    UniqSystem.deleteSet hSf.toFinset (by simp) hU hSf hS'f hS hS'
  rw [Finite.coe_toFinset] at hU' hZ'
  have hdf : (S' \ S).Finite := hS'f.subset sdiff_subset
  obtain ⟨Y'', k'', hU'', hY''f, hY'', hZ'', hk'', -⟩ :=
    UniqSystem.deleteSet hdf.toFinset (by simp) hU'.symm hdf hY'f hZ' hY'
  rw [Finite.coe_toFinset, deleteVertices_deleteVertices', union_sdiff_self] at hU''
  rw [Finite.coe_toFinset] at hZ''
  exact isChain_of_uniqSystem hU'' hY''f (hY'f.subset sdiff_subset) hY'' hZ'' (hk''.trans hk')

end Uniq

/-! ## Building chains -/

section Build

variable {K : Hypergraph α β} {Y Z : Set α} {k : ℕ}

theorem IsLinkage.mono' {K' M : Hypergraph α β} (h : IsLinkage K M) (hK : K ≤ K') :
    IsLinkage K' M :=
  ⟨h.1.trans hK, h.2⟩

theorem IsPathSystem.mono {K' M : Hypergraph α β} (h : IsPathSystem K Y Z k M) (hK : K ≤ K') :
    IsPathSystem K' Y Z k M :=
  ⟨h.1.mono' hK, h.2⟩

theorem IsChain.mono {p q : ℕ} (h : IsChain K p) (hpq : p ≤ q) : IsChain K q := by
  obtain ⟨Y, Z, hY, hZ, hYZ, hp, M, hM⟩ := h
  exact ⟨Y, Z, hY, hZ, hYZ, hp.trans hpq, M, hM⟩

/-- A hypergraph with no vertices is a `p`-chain, with no paths. -/
theorem isChain_of_vertexSet_eq_empty (hV : K.vertexSet = ∅) (p : ℕ) : IsChain K p := by
  have hbot : IsLinkage K (⊥ : Hypergraph α β) := by
    refine ⟨bot_le, fun e he ↦ absurd he (notMem_empty e), fun C hC ↦ ?_⟩
    obtain ⟨x, hx⟩ := hC.2.1
    exact absurd (hC.1.vertexSet_subset hx) (notMem_empty x)
  have hpat : linkagePattern (⊥ : Hypergraph α β) = ∅ := by
    refine eq_empty_of_forall_notMem fun B hB ↦ ?_
    obtain ⟨C, hC, -⟩ := hB
    obtain ⟨x, hx⟩ := hC.2.1
    exact absurd (hC.1.vertexSet_subset hx) (notMem_empty x)
  refine ⟨∅, ∅, empty_subset _, empty_subset _, rfl, (by simp), ⊥, ⟨hbot, (by simp [hpat]),
    (by simp [hpat])⟩, fun M' hM' ↦ ?_, (by rw [hV]; rfl)⟩
  have hMV : M'.vertexSet = ∅ := subset_empty_iff.1 (hV ▸ hM'.1.1.vertexSet_subset)
  have hME : M'.edgeSet = ∅ := by
    refine eq_empty_of_forall_notMem fun e he ↦ ?_
    obtain ⟨x, hx⟩ := (hM'.1.2.1 e he).1
    have := M'.vertex_mem_of_inc hx
    rw [hMV] at this
    exact this
  exact GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hM'.1.1 bot_le hMV hME

/-- **Adding a vertex as a path of its own.** -/
theorem UniqSystem.addVertex [Nonempty β] {x : α} (hU : UniqSystem (K.deleteVertices {x}) Y Z k)
    (hYf : Y.Finite) (hZf : Z.Finite) (hY : Y.ncard = k) (hZ : Z.ncard = k)
    (hx : x ∈ K.vertexSet) : UniqSystem K (insert x Y) (insert x Z) (k + 1) := by
  classical
  have : Nonempty α := ⟨x⟩
  have hYK := hU.subset_left hYf hY
  have hZK := hU.subset_right hZf hZ
  have hxY : x ∉ Y := fun h ↦ (hYK h).2 rfl
  have hxZ : x ∉ Z := fun h ↦ (hZK h).2 rfl
  have hK₁K : K.deleteVertices {x} ≤ K := GM10.deleteVertices_le K {x}
  obtain ⟨M, hM, hMu, hMV⟩ := hU
  obtain ⟨c, n, f, hF, hc0, hfam⟩ := exists_goodFam_of_isPathSystem hYf (hY ▸ hM)
  have hxF : x ∉ famVerts Y c n := fun h ↦ (famVerts_subset hF.1 h).2 rfl
  obtain ⟨hF₁, hV₁, hE₁⟩ := (hF.1.mono hK₁K).insertTrivial hxY hx hxF
  have hY₁ : (insert x Y).ncard = k + 1 := by rw [ncard_insert_of_notMem hxY hYf, hY]
  have hZ₁ : (insert x Z).ncard = k + 1 := by rw [ncard_insert_of_notMem hxZ hZf, hZ]
  have hgood : IsGoodFam K (insert x Y) (insert x Z) (insert x Y) (trivC x x c) (trivN x n) f := by
    refine ⟨hF₁, hYf.insert x, rfl, fun y hy ↦ ?_⟩
    by_cases hyx : y = x
    · rw [hyx, trivC_self, trivC_self]; exact ⟨mem_insert _ _, mem_insert _ _⟩
    · have hy' : y ∈ Y := (mem_insert_iff.1 hy).resolve_left hyx
      rw [trivC_of_ne hyx, trivC_of_ne hyx, trivN_of_ne hyx, hc0 y hy']
      exact ⟨mem_insert_of_mem _ hy', mem_insert_of_mem _ (hc0 y hy' ▸ (hF.2.2.2 y hy').2)⟩
  have hM₁ := isPathSystem_famGraph hgood
  rw [hY₁] at hM₁
  have hFV : famVerts Y c n = M.vertexSet := by rw [← hfam, famGraph_vertexSet hF.1]
  have hFE : famEdges Y n f = M.edgeSet := by rw [← hfam, famGraph_edgeSet hF.1]
  refine ⟨_, hM₁, fun M' hM' ↦ ?_, ?_⟩
  · obtain ⟨c', n', f', hF', hc0', hfam'⟩ :=
      exists_goodFam_of_isPathSystem (hYf.insert x) (hY₁ ▸ hM')
    have hZY : (insert x Z).ncard = (insert x Y).ncard := by rw [hZ₁, hY₁]
    have hnx : n' x = 0 := by
      obtain ⟨y, hy, he⟩ := hF'.exists_end (hZf.insert x) hZY (mem_insert x Z)
      obtain ⟨rfl, h⟩ := hF'.1.eq_of_eq hy (mem_insert x Y) le_rfl (Nat.zero_le _)
        (he.trans (hc0' x (mem_insert x Y)).symm)
      exact h
    have hxR : x ∉ famVerts Y c' n' := fun h ↦ by
      obtain ⟨y, hy, a, ha, he⟩ := mem_famVerts.1 h
      have := hF'.1.eq_of_eq (mem_insert_of_mem x hy) (mem_insert x Y) ha (Nat.zero_le _)
        (he.trans (hc0' x (mem_insert x Y)).symm)
      exact hxY (this.1 ▸ hy)
    have hFR := hF'.1.restrict (subset_insert x Y)
    have hFRK : IsPathFam (K.deleteVertices {x}) Y c' n' f' := by
      refine hFR.of_le hK₁K (fun z hz ↦ ⟨famVerts_subset hFR hz, fun h ↦
        hxR (mem_singleton_iff.1 h ▸ hz)⟩) ?_
      intro e he
      obtain ⟨i, hi, a, ha, rfl⟩ := mem_famEdges.1 he
      refine ⟨hFR.edge_mem i hi a ha, fun z hz hinc ↦ hxR ?_⟩
      have hzx : z = x := hz
      have : z ∈ famVerts Y c' n' := by
        rcases (hFR.inc_iff hi ha).1 hinc with h | h
        · rw [h]; exact mem_famVerts.2 ⟨i, hi, a, ha.le, rfl⟩
        · rw [h]; exact mem_famVerts.2 ⟨i, hi, a + 1, ha, rfl⟩
      exact hzx ▸ this
    have hgoodR : IsGoodFam (K.deleteVertices {x}) Y Z Y c' n' f' := by
      refine ⟨hFRK, hYf, rfl, fun y hy ↦ ⟨by rw [hc0' y (mem_insert_of_mem x hy)]; exact hy, ?_⟩⟩
      rcases mem_insert_iff.1 (hF'.2.2.2 y (mem_insert_of_mem x hy)).2 with h | h
      · exact absurd (mem_famVerts.2 ⟨y, hy, n' y, le_rfl, h⟩) hxR
      · exact h
    have hMR := hMu _ (hY ▸ isPathSystem_famGraph hgoodR)
    have hVR : famVerts Y c' n' = famVerts Y c n := by
      rw [← famGraph_vertexSet hFRK, hMR, hFV]
    have hER : famEdges Y n' f' = famEdges Y n f := by
      rw [← famGraph_edgeSet hFRK, hMR, hFE]
    have hIx : insert x Y \ {x} = Y := insert_sdiff_self_of_notMem hxY
    have hV' : famVerts (insert x Y) c' n' = insert x (famVerts Y c' n') := by
      rw [famVerts_eq_insert (mem_insert x Y) hnx, hc0' x (mem_insert x Y), hIx]
    have hE' : famEdges (insert x Y) n' f' = famEdges Y n' f' := by
      rw [famEdges_eq_sdiff hnx, hIx]
    rw [← hfam']
    change subOn _ (famVerts _ c' n') (famEdges _ n' f') =
      subOn _ (famVerts _ (trivC x x c) (trivN x n)) (famEdges _ (trivN x n) f)
    rw [hV', hE', hV₁, hE₁, hVR, hER]
  · rw [famGraph_vertexSet hF₁, hV₁, hFV, hMV]
    change insert x (K.vertexSet \ {x}) = K.vertexSet
    rw [insert_sdiff_singleton, insert_eq_of_mem hx]

/-- Deleting a vertex that is not there. -/
theorem deleteVertices_eq_self {x : α} (hx : x ∉ K.vertexSet) : K.deleteVertices {x} = K := by
  ext e y
  · simp only [Hypergraph.deleteVertices, mem_sdiff, mem_singleton_iff]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun h' ↦ hx (h' ▸ h)⟩⟩
  · simp only [Hypergraph.deleteVertices, mem_ofPred_eq, mem_singleton_iff, forall_eq]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun h' ↦ hx (K.vertex_mem_of_inc h')⟩⟩
  · simp only [Hypergraph.deleteVertices, mem_singleton_iff, forall_eq]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun h' ↦ hx (K.vertex_mem_of_inc h')⟩⟩

/-- If `K \ x` is a `p`-chain then `K` is a `(p + 1)`-chain. -/
theorem IsChain.of_deleteVertex [Nonempty β] {x : α} {p : ℕ}
    (h : IsChain (K.deleteVertices {x}) p) : IsChain K (p + 1) := by
  by_cases hx : x ∈ K.vertexSet
  · obtain ⟨Y, Z, hY, hZ, hYZ, hp, hU⟩ := h
    have hYf : Y.Finite := (K.deleteVertices {x}).vertexSet_finite.subset hY
    have hZf : Z.Finite := (K.deleteVertices {x}).vertexSet_finite.subset hZ
    have hxY : x ∉ Y := fun h ↦ (hY h).2 rfl
    have hxZ : x ∉ Z := fun h ↦ (hZ h).2 rfl
    exact isChain_of_uniqSystem (UniqSystem.addVertex hU hYf hZf rfl hYZ.symm hx) (hYf.insert x)
      (hZf.insert x) (ncard_insert_of_notMem hxY hYf)
      (by rw [ncard_insert_of_notMem hxZ hZf, hYZ]) (by omega)
  · rw [deleteVertices_eq_self hx] at h
    exact h.mono (Nat.le_succ p)

/-- **If `K \ X` is a `p`-chain then `K` is a `(p + |X|)`-chain.** -/
theorem IsChain.of_deleteVertices [Nonempty β] :
    ∀ (X : Finset α) {K : Hypergraph α β} {p : ℕ}, IsChain (K.deleteVertices X) p →
      IsChain K (p + X.card) := by
  classical
  intro X
  induction X using Finset.induction_on with
  | empty => intro K p h; simpa [deleteVertices_empty'] using h
  | @insert x X hxX ih =>
    intro K p h
    rw [Finset.coe_insert, insert_eq, ← deleteVertices_deleteVertices'] at h
    rw [Finset.card_insert_of_notMem hxX, ← Nat.add_assoc]
    exact (ih h).of_deleteVertex

end Build

/-! ## Unions of chains -/

section Union

variable {ι : Type w}

/-- `x i` for `i ∈ I₁`, and `y i` otherwise. -/
noncomputable def pick {γ : Type*} (I₁ : Set ι) (x y : ι → γ) : ι → γ := by
  classical exact fun i ↦ if i ∈ I₁ then x i else y i

@[simp] theorem pick_of_mem {γ : Type*} {I₁ : Set ι} {x y : ι → γ} {i : ι} (h : i ∈ I₁) :
    pick I₁ x y i = x i := by simp [pick, h]

@[simp] theorem pick_of_notMem {γ : Type*} {I₁ : Set ι} {x y : ι → γ} {i : ι} (h : i ∉ I₁) :
    pick I₁ x y i = y i := by simp [pick, h]

theorem famVerts_congr {I : Set ι} {c c' : ι → ℕ → α} {n n' : ι → ℕ}
    (h : ∀ i ∈ I, c i = c' i ∧ n i = n' i) : famVerts I c n = famVerts I c' n' := by
  ext x
  simp only [mem_famVerts]
  constructor
  · rintro ⟨i, hi, a, ha, rfl⟩
    exact ⟨i, hi, a, (h i hi).2 ▸ ha, by rw [(h i hi).1]⟩
  · rintro ⟨i, hi, a, ha, rfl⟩
    exact ⟨i, hi, a, (h i hi).2 ▸ ha, by rw [(h i hi).1]⟩

theorem famEdges_congr {I : Set ι} {n n' : ι → ℕ} {f f' : ι → ℕ → β}
    (h : ∀ i ∈ I, n i = n' i ∧ f i = f' i) : famEdges I n f = famEdges I n' f' := by
  ext x
  simp only [mem_famEdges]
  constructor
  · rintro ⟨i, hi, a, ha, rfl⟩
    exact ⟨i, hi, a, (h i hi).1 ▸ ha, by rw [(h i hi).2]⟩
  · rintro ⟨i, hi, a, ha, rfl⟩
    exact ⟨i, hi, a, (h i hi).1 ▸ ha, by rw [(h i hi).2]⟩

variable {K : Hypergraph α β} {I₁ I₂ : Set ι} {c₁ c₂ : ι → ℕ → α} {n₁ n₂ : ι → ℕ}
  {f₁ f₂ : ι → ℕ → β}

/-- **Two families with disjoint vertices form one family.** -/
theorem IsPathFam.union (hF₁ : IsPathFam K I₁ c₁ n₁ f₁) (hF₂ : IsPathFam K I₂ c₂ n₂ f₂)
    (hI : Disjoint I₁ I₂) (hd : Disjoint (famVerts I₁ c₁ n₁) (famVerts I₂ c₂ n₂)) :
    IsPathFam K (I₁ ∪ I₂) (pick I₁ c₁ c₂) (pick I₁ n₁ n₂) (pick I₁ f₁ f₂) ∧
      famVerts (I₁ ∪ I₂) (pick I₁ c₁ c₂) (pick I₁ n₁ n₂) =
        famVerts I₁ c₁ n₁ ∪ famVerts I₂ c₂ n₂ ∧
      famEdges (I₁ ∪ I₂) (pick I₁ n₁ n₂) (pick I₁ f₁ f₂) =
        famEdges I₁ n₁ f₁ ∪ famEdges I₂ n₂ f₂ := by
  have e₁ : ∀ i ∈ I₁, pick I₁ c₁ c₂ i = c₁ i ∧ pick I₁ n₁ n₂ i = n₁ i ∧
      pick I₁ f₁ f₂ i = f₁ i := fun i hi ↦ ⟨pick_of_mem hi, pick_of_mem hi, pick_of_mem hi⟩
  have e₂ : ∀ i ∈ I₂, pick I₁ c₁ c₂ i = c₂ i ∧ pick I₁ n₁ n₂ i = n₂ i ∧
      pick I₁ f₁ f₂ i = f₂ i := fun i hi ↦
    have h : i ∉ I₁ := fun h ↦ disjoint_left.1 hI h hi
    ⟨pick_of_notMem h, pick_of_notMem h, pick_of_notMem h⟩
  have himg₁ : ∀ i ∈ I₁, c₁ i '' Iic (n₁ i) ⊆ famVerts I₁ c₁ n₁ := fun i hi x ⟨a, ha, he⟩ ↦
    mem_famVerts.2 ⟨i, hi, a, ha, he⟩
  have himg₂ : ∀ i ∈ I₂, c₂ i '' Iic (n₂ i) ⊆ famVerts I₂ c₂ n₂ := fun i hi x ⟨a, ha, he⟩ ↦
    mem_famVerts.2 ⟨i, hi, a, ha, he⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro i (hi | hi)
    · obtain ⟨h1, h2, -⟩ := e₁ i hi; rw [h1, h2]; exact hF₁.inj i hi
    · obtain ⟨h1, h2, -⟩ := e₂ i hi; rw [h1, h2]; exact hF₂.inj i hi
  · rintro i (hi | hi) j (hj | hj) hij
    · obtain ⟨h1, h2, -⟩ := e₁ i hi; obtain ⟨h3, h4, -⟩ := e₁ j hj
      rw [h1, h2, h3, h4]; exact hF₁.disj i hi j hj hij
    · obtain ⟨h1, h2, -⟩ := e₁ i hi; obtain ⟨h3, h4, -⟩ := e₂ j hj
      rw [h1, h2, h3, h4]; exact hd.mono (himg₁ i hi) (himg₂ j hj)
    · obtain ⟨h1, h2, -⟩ := e₂ i hi; obtain ⟨h3, h4, -⟩ := e₁ j hj
      rw [h1, h2, h3, h4]; exact hd.symm.mono (himg₂ i hi) (himg₁ j hj)
    · obtain ⟨h1, h2, -⟩ := e₂ i hi; obtain ⟨h3, h4, -⟩ := e₂ j hj
      rw [h1, h2, h3, h4]; exact hF₂.disj i hi j hj hij
  · rintro i (hi | hi) a ha
    · obtain ⟨h1, h2, -⟩ := e₁ i hi; rw [h2] at ha; rw [h1]; exact hF₁.mem i hi a ha
    · obtain ⟨h1, h2, -⟩ := e₂ i hi; rw [h2] at ha; rw [h1]; exact hF₂.mem i hi a ha
  · rintro i (hi | hi) a ha
    · obtain ⟨-, h2, h3⟩ := e₁ i hi; rw [h2] at ha; rw [h3]; exact hF₁.edge_mem i hi a ha
    · obtain ⟨-, h2, h3⟩ := e₂ i hi; rw [h2] at ha; rw [h3]; exact hF₂.edge_mem i hi a ha
  · rintro i (hi | hi) a ha
    · obtain ⟨h1, h2, h3⟩ := e₁ i hi; rw [h2] at ha; rw [h1, h3]; exact hF₁.ends i hi a ha
    · obtain ⟨h1, h2, h3⟩ := e₂ i hi; rw [h2] at ha; rw [h1, h3]; exact hF₂.ends i hi a ha
  · rw [famVerts_union, famVerts_congr (fun i hi ↦ ⟨(e₁ i hi).1, (e₁ i hi).2.1⟩),
      famVerts_congr (fun i hi ↦ ⟨(e₂ i hi).1, (e₂ i hi).2.1⟩)]
  · rw [famEdges_union, famEdges_congr (fun i hi ↦ ⟨(e₁ i hi).2.1, (e₁ i hi).2.2⟩),
      famEdges_congr (fun i hi ↦ ⟨(e₂ i hi).2.1, (e₂ i hi).2.2⟩)]

/-- A path of a family in `K = K₁ ∪ K₂`, with `V(K₁)` and `V(K₂)` disjoint, that starts in `K₁`
stays in `K₁`. -/
theorem IsPathFam.mem_of_start {K₁ K₂ : Hypergraph α β} {I : Set ι} {c : ι → ℕ → α} {n : ι → ℕ}
    {f : ι → ℕ → β} (hF : IsPathFam K I c n f) (h₂ : K₂ ≤ K)
    (hE : K.edgeSet = K₁.edgeSet ∪ K₂.edgeSet) (h₁ : K₁ ≤ K)
    (hd : Disjoint K₁.vertexSet K₂.vertexSet) {i : ι} (hi : i ∈ I)
    (h0 : c i 0 ∈ K₁.vertexSet) : ∀ a ≤ n i, c i a ∈ K₁.vertexSet ∧ (a < n i → f i a ∈ K₁.edgeSet) := by
  intro a
  induction a with
  | zero =>
    intro _
    refine ⟨h0, fun ha ↦ ?_⟩
    have he := hF.edge_mem i hi 0 ha
    rw [hE] at he
    rcases he with he | he
    · exact he
    · have : c i 0 ∈ K₂.ends (f i 0) := by
        rw [← h₂.ends_eq _ he, hF.ends i hi 0 ha]; exact mem_insert _ _
      exact absurd (K₂.vertex_mem_of_inc this) (disjoint_left.1 hd h0)
  | succ a ih =>
    intro ha
    obtain ⟨-, hE₁⟩ := ih (by omega)
    have he₁ := hE₁ (by omega)
    have hv : c i (a + 1) ∈ K₁.vertexSet := by
      have : c i (a + 1) ∈ K₁.ends (f i a) := by
        rw [← h₁.ends_eq _ he₁, hF.ends i hi a (by omega)]; exact mem_insert_of_mem _ rfl
      exact K₁.vertex_mem_of_inc this
    refine ⟨hv, fun ha' ↦ ?_⟩
    have he := hF.edge_mem i hi (a + 1) ha'
    rw [hE] at he
    rcases he with he | he
    · exact he
    · have : c i (a + 1) ∈ K₂.ends (f i (a + 1)) := by
        rw [← h₂.ends_eq _ he, hF.ends i hi (a + 1) ha']; exact mem_insert _ _
      exact absurd (K₂.vertex_mem_of_inc this) (disjoint_left.1 hd hv)

/-- **The union of two chains with disjoint vertex sets is a chain.** -/
theorem isChain_union [Nonempty β] {K K₁ K₂ : Hypergraph α β} (h₁ : K₁ ≤ K) (h₂ : K₂ ≤ K)
    (hV : K.vertexSet = K₁.vertexSet ∪ K₂.vertexSet) (hE : K.edgeSet = K₁.edgeSet ∪ K₂.edgeSet)
    (hd : Disjoint K₁.vertexSet K₂.vertexSet) {p₁ p₂ : ℕ} (hc₁ : IsChain K₁ p₁)
    (hc₂ : IsChain K₂ p₂) : IsChain K (p₁ + p₂) := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · exact isChain_of_vertexSet_eq_empty (eq_empty_of_isEmpty _) _
  obtain ⟨Y₁, Z₁, hY₁, hZ₁, hYZ₁, hp₁, M₁, hM₁, hMu₁, hMV₁⟩ := hc₁
  obtain ⟨Y₂, Z₂, hY₂, hZ₂, hYZ₂, hp₂, M₂, hM₂, hMu₂, hMV₂⟩ := hc₂
  have hY₁f : Y₁.Finite := K₁.vertexSet_finite.subset hY₁
  have hY₂f : Y₂.Finite := K₂.vertexSet_finite.subset hY₂
  have hZ₁f : Z₁.Finite := K₁.vertexSet_finite.subset hZ₁
  have hZ₂f : Z₂.Finite := K₂.vertexSet_finite.subset hZ₂
  have hdY : Disjoint Y₁ Y₂ := hd.mono hY₁ hY₂
  have hdZ : Disjoint Z₁ Z₂ := hd.mono hZ₁ hZ₂
  obtain ⟨c₁, n₁, f₁, hF₁, hc₁0, hfam₁⟩ := exists_goodFam_of_isPathSystem hY₁f hM₁
  obtain ⟨c₂, n₂, f₂, hF₂, hc₂0, hfam₂⟩ := exists_goodFam_of_isPathSystem hY₂f hM₂
  have hV₁ : famVerts Y₁ c₁ n₁ = M₁.vertexSet := by rw [← hfam₁, famGraph_vertexSet hF₁.1]
  have hV₂ : famVerts Y₂ c₂ n₂ = M₂.vertexSet := by rw [← hfam₂, famGraph_vertexSet hF₂.1]
  have hE₁ : famEdges Y₁ n₁ f₁ = M₁.edgeSet := by rw [← hfam₁, famGraph_edgeSet hF₁.1]
  have hE₂ : famEdges Y₂ n₂ f₂ = M₂.edgeSet := by rw [← hfam₂, famGraph_edgeSet hF₂.1]
  obtain ⟨hF, hFV, hFE⟩ := (hF₁.1.mono h₁).union (hF₂.1.mono h₂) hdY
    (hd.mono (famVerts_subset hF₁.1) (famVerts_subset hF₂.1))
  have hYc : (Y₁ ∪ Y₂).ncard = Y₁.ncard + Y₂.ncard := ncard_union_eq hdY hY₁f hY₂f
  have hZc : (Z₁ ∪ Z₂).ncard = Z₁.ncard + Z₂.ncard := ncard_union_eq hdZ hZ₁f hZ₂f
  have hgood : IsGoodFam K (Y₁ ∪ Y₂) (Z₁ ∪ Z₂) (Y₁ ∪ Y₂) (pick Y₁ c₁ c₂) (pick Y₁ n₁ n₂)
      (pick Y₁ f₁ f₂) := by
    refine ⟨hF, hY₁f.union hY₂f, rfl, ?_⟩
    rintro y (hy | hy)
    · rw [pick_of_mem hy, pick_of_mem hy]
      exact ⟨Or.inl (hF₁.2.2.2 y hy).1, Or.inl (hF₁.2.2.2 y hy).2⟩
    · have hy' : y ∉ Y₁ := fun h ↦ disjoint_left.1 hdY h hy
      rw [pick_of_notMem hy', pick_of_notMem hy']
      exact ⟨Or.inr (hF₂.2.2.2 y hy).1, Or.inr (hF₂.2.2.2 y hy).2⟩
  refine ⟨Y₁ ∪ Y₂, Z₁ ∪ Z₂, union_subset (hY₁.trans (hV ▸ subset_union_left))
    (hY₂.trans (hV ▸ subset_union_right)), union_subset (hZ₁.trans (hV ▸ subset_union_left))
    (hZ₂.trans (hV ▸ subset_union_right)), by rw [hYc, hZc, hYZ₁, hYZ₂], by omega, _,
    isPathSystem_famGraph hgood, fun M' hM' ↦ ?_, ?_⟩
  · obtain ⟨c', n', f', hF', hc0', hfam'⟩ := exists_goodFam_of_isPathSystem (hY₁f.union hY₂f) hM'
    have hst₁ : ∀ y ∈ Y₁, ∀ a ≤ n' y, c' y a ∈ K₁.vertexSet ∧ (a < n' y → f' y a ∈ K₁.edgeSet) :=
      fun y hy ↦ hF'.1.mem_of_start h₂ hE h₁ hd (Or.inl hy) (by rw [hc0' y (Or.inl hy)]; exact hY₁ hy)
    have hst₂ : ∀ y ∈ Y₂, ∀ a ≤ n' y, c' y a ∈ K₂.vertexSet ∧ (a < n' y → f' y a ∈ K₂.edgeSet) :=
      fun y hy ↦ hF'.1.mem_of_start h₁ (by rw [hE, Set.union_comm]) h₂ hd.symm (Or.inr hy)
        (by rw [hc0' y (Or.inr hy)]; exact hY₂ hy)
    have hR₁ : IsPathFam K₁ Y₁ c' n' f' := (hF'.1.restrict subset_union_left).of_le h₁
      (fun x hx ↦ by obtain ⟨y, hy, a, ha, rfl⟩ := mem_famVerts.1 hx; exact (hst₁ y hy a ha).1)
      (fun e he ↦ by obtain ⟨y, hy, a, ha, rfl⟩ := mem_famEdges.1 he; exact (hst₁ y hy a ha.le).2 ha)
    have hR₂ : IsPathFam K₂ Y₂ c' n' f' := (hF'.1.restrict subset_union_right).of_le h₂
      (fun x hx ↦ by obtain ⟨y, hy, a, ha, rfl⟩ := mem_famVerts.1 hx; exact (hst₂ y hy a ha).1)
      (fun e he ↦ by obtain ⟨y, hy, a, ha, rfl⟩ := mem_famEdges.1 he; exact (hst₂ y hy a ha.le).2 ha)
    have hg₁ : IsGoodFam K₁ Y₁ Z₁ Y₁ c' n' f' := by
      refine ⟨hR₁, hY₁f, rfl, fun y hy ↦ ⟨by rw [hc0' y (Or.inl hy)]; exact hy, ?_⟩⟩
      rcases (hF'.2.2.2 y (Or.inl hy)).2 with h | h
      · exact h
      · exact absurd (hZ₂ h) (disjoint_left.1 hd (hst₁ y hy _ le_rfl).1)
    have hg₂ : IsGoodFam K₂ Y₂ Z₂ Y₂ c' n' f' := by
      refine ⟨hR₂, hY₂f, rfl, fun y hy ↦ ⟨by rw [hc0' y (Or.inr hy)]; exact hy, ?_⟩⟩
      rcases (hF'.2.2.2 y (Or.inr hy)).2 with h | h
      · exact absurd (hZ₁ h) (disjoint_right.1 hd (hst₂ y hy _ le_rfl).1)
      · exact h
    have hm₁ := hMu₁ _ (isPathSystem_famGraph hg₁)
    have hm₂ := hMu₂ _ (isPathSystem_famGraph hg₂)
    rw [← hfam']
    change subOn _ (famVerts _ c' n') (famEdges _ n' f') = subOn _ _ _
    rw [hFV, hFE, famVerts_union, famEdges_union, ← famGraph_vertexSet hR₁, ← famGraph_vertexSet hR₂,
      ← famGraph_edgeSet hR₁, ← famGraph_edgeSet hR₂, hm₁, hm₂, hV₁, hV₂, hE₁, hE₂]
  · rw [famGraph_vertexSet hF, hFV, hV₁, hV₂, hMV₁, hMV₂, hV]

/-- **A union of chains with disjoint vertex sets.** -/
theorem isChain_biUnion [Nonempty β] (S : Finset ι) :
    ∀ {K : Hypergraph α β} (P : ι → Hypergraph α β) {q : ℕ}, (∀ i ∈ S, P i ≤ K) →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (P i).vertexSet (P j).vertexSet) →
      K.vertexSet = ⋃ i ∈ S, (P i).vertexSet → K.edgeSet = ⋃ i ∈ S, (P i).edgeSet →
      (∀ i ∈ S, IsChain (P i) q) → IsChain K (S.card * q) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro K P q _ _ hV _ _
    exact isChain_of_vertexSet_eq_empty (by simpa using hV) _
  | @insert i S hiS ih =>
    intro K P q hle hd hV hE hc
    set K' := subOn K (⋃ j ∈ S, (P j).vertexSet) (⋃ j ∈ S, (P j).edgeSet) with hK'
    have hK'K : K' ≤ K := by
      refine subOn_le fun e he _ x hx ↦ ?_
      obtain ⟨j, hj, hej⟩ := mem_iUnion₂.1 he
      have hjK := hle j (Finset.mem_insert_of_mem hj)
      have : x ∈ (P j).ends e := by rw [← hjK.ends_eq e hej]; exact hx
      exact mem_iUnion₂.2 ⟨j, hj, (P j).vertex_mem_of_inc this⟩
    have hV' : K'.vertexSet = ⋃ j ∈ S, (P j).vertexSet := by
      refine inter_eq_left.2 fun x hx ↦ ?_
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hx
      exact (hle j (Finset.mem_insert_of_mem hj)).vertexSet_subset hxj
    have hE' : K'.edgeSet = ⋃ j ∈ S, (P j).edgeSet := by
      refine inter_eq_left.2 fun x hx ↦ ?_
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hx
      exact (hle j (Finset.mem_insert_of_mem hj)).edgeSet_subset hxj
    have hPK' : ∀ j ∈ S, P j ≤ K' := fun j hj ↦
      le_subOn (hle j (Finset.mem_insert_of_mem hj)) (subset_biUnion_of_mem (u := fun j ↦ (P j).vertexSet) hj)
        (subset_biUnion_of_mem (u := fun j ↦ (P j).edgeSet) hj)
    have hc' := ih P hPK' (fun j hj l hl ↦ hd j (Finset.mem_insert_of_mem hj) l
      (Finset.mem_insert_of_mem hl)) hV' hE' (fun j hj ↦ hc j (Finset.mem_insert_of_mem hj))
    have hdi : Disjoint (P i).vertexSet K'.vertexSet := by
      rw [hV', disjoint_iUnion₂_right]
      exact fun j hj ↦ hd i (Finset.mem_insert_self i S) j (Finset.mem_insert_of_mem hj)
        (fun h ↦ hiS (h ▸ hj))
    have := isChain_union (hle i (Finset.mem_insert_self i S)) hK'K
      (by rw [hV, hV', Finset.set_biUnion_insert]) (by rw [hE, hE', Finset.set_biUnion_insert])
      hdi (hc i (Finset.mem_insert_self i S)) hc'
    refine this.mono (le_of_eq ?_)
    rw [Finset.card_insert_of_notMem hiS]
    ring

end Union

/-! ## The converse of (12.1) -/

section Converse

variable {K : Hypergraph α β} {Y Z : Set α} {k : ℕ}

/-- **No edges.** A hypergraph with no edges has a unique set of `|V(K)|` disjoint paths between
`V(K)` and `V(K)`: its one-vertex paths. -/
theorem uniqSystem_of_edgeSet_eq_empty [Nonempty β] (hE : K.edgeSet = ∅) :
    UniqSystem K K.vertexSet K.vertexSet K.vertexSet.ncard := by
  classical
  have hF : IsPathFam K K.vertexSet (fun x _ ↦ x) (fun _ ↦ 0) (fun _ _ ↦ Classical.arbitrary β) :=
    ⟨fun _ _ a ha b hb _ ↦ by simp only [mem_Iic] at ha hb; rw [Nat.le_zero.1 ha, Nat.le_zero.1 hb],
      fun x _ y _ hxy ↦ by
        rw [disjoint_left]
        rintro z ⟨a, -, rfl⟩ ⟨b, -, h⟩
        exact hxy h.symm,
      fun x hx _ _ ↦ hx, fun _ _ a ha ↦ absurd ha (Nat.not_lt_zero a),
      fun _ _ a ha ↦ absurd ha (Nat.not_lt_zero a)⟩
  have hgood : IsGoodFam K K.vertexSet K.vertexSet K.vertexSet (fun x _ ↦ x) (fun _ ↦ 0)
      (fun _ _ ↦ Classical.arbitrary β) := ⟨hF, K.vertexSet_finite, rfl, fun x hx ↦ ⟨hx, hx⟩⟩
  have hFV : famVerts K.vertexSet (fun x _ ↦ x) (fun _ ↦ 0) = K.vertexSet := by
    ext x
    simp only [mem_famVerts]
    exact ⟨fun ⟨y, hy, _, _, h⟩ ↦ h ▸ hy, fun hx ↦ ⟨x, hx, 0, le_rfl, rfl⟩⟩
  refine ⟨_, isPathSystem_famGraph hgood, fun M' hM' ↦ ?_, by rw [famGraph_vertexSet hF, hFV]⟩
  have hM'E : M'.edgeSet = ∅ := subset_empty_iff.1 (hE ▸ hM'.1.1.edgeSet_subset)
  have hM'V : M'.vertexSet = K.vertexSet := by
    refine (hM'.1.1.vertexSet_subset).antisymm fun x hx ↦ ?_
    have : Nonempty α := ⟨x⟩
    obtain ⟨c', n', f', hF', hc0', hfam'⟩ :=
      exists_goodFam_of_isPathSystem K.vertexSet_finite hM'
    rw [← hfam', famGraph_vertexSet hF'.1]
    exact mem_famVerts.2 ⟨x, hx, 0, Nat.zero_le _, hc0' x hx⟩
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hM'.1.1 (famGraph_le hF) ?_ ?_
  · rw [hM'V, famGraph_vertexSet hF, hFV]
  · rw [hM'E, famGraph_edgeSet hF]
    ext g
    simp [mem_famEdges]

/-- **Adding edges with both ends in `Y`.** They are on none of the paths. -/
theorem UniqSystem.addEdges [Nonempty β] {K₁ : Hypergraph α β} (hK : K₁ ≤ K)
    (hU : UniqSystem K₁ Y Z k) (hYf : Y.Finite) (hY : Y.ncard = k)
    (hV : K.vertexSet = K₁.vertexSet) (hE : ∀ e ∈ K.edgeSet, e ∉ K₁.edgeSet → K.ends e ⊆ Y) :
    UniqSystem K Y Z k := by
  obtain ⟨M, hM, hMu, hMV⟩ := hU
  refine ⟨M, hM.mono hK, fun M' hM' ↦ ?_, by rw [hMV, hV]⟩
  rcases isEmpty_or_nonempty α with hα | hα
  · refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hM'.1.1 (hM.1.1.trans hK)
      (eq_empty_of_isEmpty _ |>.trans (eq_empty_of_isEmpty _).symm) ?_
    have h1 : M'.edgeSet = ∅ := eq_empty_of_forall_notMem fun e he ↦ by
      obtain ⟨x, -⟩ := (hM'.1.2.1 e he).1
      exact isEmptyElim x
    have h2 : M.edgeSet = ∅ := eq_empty_of_forall_notMem fun e he ↦ by
      obtain ⟨x, -⟩ := (hM.1.2.1 e he).1
      exact isEmptyElim x
    rw [h1, h2]
  obtain ⟨c, n, f, hF, hc0, hfam⟩ := exists_goodFam_of_isPathSystem hYf (hY ▸ hM')
  have hR : IsPathFam K₁ Y c n f := by
    refine hF.1.of_le hK (fun x hx ↦ hV ▸ famVerts_subset hF.1 hx) fun e he ↦ ?_
    obtain ⟨y, hy, a, ha, rfl⟩ := mem_famEdges.1 he
    by_contra hno
    have hsub := hE _ (hF.1.edge_mem y hy a ha) hno
    rw [hF.1.ends y hy a ha] at hsub
    have h0 := hF.eq_zero_of_mem hc0 hy ha.le (hsub (mem_insert _ _))
    have h1 := hF.eq_zero_of_mem hc0 hy ha (hsub (mem_insert_of_mem _ rfl))
    omega
  have hg : IsGoodFam K₁ Y Z Y c n f := ⟨hR, hF.2⟩
  rw [← hfam, ← famGraph_eq_of_le hR hK]
  exact hMu _ (hY ▸ isPathSystem_famGraph hg)

/-- **Adding a first vertex.** Let `v` be a vertex of `K` whose only edge is `g = vv'`, where
`v' ∈ Y₁`. A unique set of paths of `K \ v` between `Y₁` and `Z` gives one of `K` between
`Y₁ - v' + v` and `Z`: the path of `v'` gets `v` in front. -/
theorem UniqSystem.addFirst [Nonempty β] {Y₁ : Set α} {v v' : α} {g : β}
    (hU : UniqSystem (K.deleteVertices {v}) Y₁ Z k) (hY₁f : Y₁.Finite) (hY₁ : Y₁.ncard = k)
    (hv'Y₁ : v' ∈ Y₁) (hvK : v ∈ K.vertexSet) (hvY₁ : v ∉ Y₁) (hvZ : v ∉ Z)
    (hg : g ∈ K.edgeSet) (hge : K.ends g = {v, v'}) (hvg : ∀ e ∈ K.edgeSet, K.Inc e v → e = g) :
    UniqSystem K (insert v (Y₁ \ {v'})) Z k := by
  classical
  have : Nonempty α := ⟨v⟩
  have hK₁K : K.deleteVertices {v} ≤ K := GM10.deleteVertices_le K {v}
  obtain ⟨M, hM, hMu, hMV⟩ := hU
  obtain ⟨c, n, f, hF, hc0, hfam⟩ := exists_goodFam_of_isPathSystem hY₁f (hY₁ ▸ hM)
  have hvF : v ∉ famVerts Y₁ c n := fun h ↦ (famVerts_subset hF.1 h).2 rfl
  obtain ⟨hF₂, hV₂, hE₂⟩ := (hF.1.mono hK₁K).extend hv'Y₁ hvK hvF hg
    (by rw [hge, hc0 v' hv'Y₁])
  have hYc : (insert v (Y₁ \ {v'})).ncard = k := by
    rw [ncard_insert_of_notMem (fun h ↦ hvY₁ h.1) (hY₁f.subset sdiff_subset),
      ncard_sdiff_singleton_of_mem hv'Y₁, hY₁]
    have : 1 ≤ k := by rw [← hY₁]; exact Nat.one_le_iff_ne_zero.2 (ncard_ne_zero_of_mem hv'Y₁ hY₁f)
    omega
  have hYf : (insert v (Y₁ \ {v'})).Finite := (hY₁f.subset sdiff_subset).insert v
  have hgood : IsGoodFam K (insert v (Y₁ \ {v'})) Z Y₁ (extC v' v c) (extN v' n) (extF v' g f) := by
    refine ⟨hF₂, hY₁f, by rw [hYc, hY₁], fun y hy ↦ ?_⟩
    by_cases hyv : y = v'
    · rw [hyv, extC_self_zero, extN_self, extC_self_succ]
      exact ⟨mem_insert _ _, (hF.2.2.2 v' hv'Y₁).2⟩
    · rw [extC_of_ne hyv, extC_of_ne hyv, extN_of_ne hyv, hc0 y hy]
      exact ⟨mem_insert_of_mem _ ⟨hy, hyv⟩, hc0 y hy ▸ (hF.2.2.2 y hy).2⟩
  have hM₂ := isPathSystem_famGraph hgood
  rw [hYc] at hM₂
  have hFV : famVerts Y₁ c n = M.vertexSet := by rw [← hfam, famGraph_vertexSet hF.1]
  have hFE : famEdges Y₁ n f = M.edgeSet := by rw [← hfam, famGraph_edgeSet hF.1]
  refine ⟨_, hM₂, fun M' hM' ↦ ?_, ?_⟩
  · obtain ⟨c', n', f', hF', hc0', hfam'⟩ := exists_goodFam_of_isPathSystem hYf (hYc ▸ hM')
    have hvY : v ∈ insert v (Y₁ \ {v'}) := mem_insert _ _
    have hnv : 1 ≤ n' v := by
      by_contra h0
      have := (hF'.2.2.2 v hvY).2
      rw [show n' v = 0 by omega, hc0' v hvY] at this
      exact hvZ this
    have hf0 : f' v 0 = g := hvg _ (hF'.1.edge_mem v hvY 0 hnv)
      ((hF'.1.inc_iff hvY hnv).2 (Or.inl (hc0' v hvY).symm))
    have hc1 : c' v 1 = v' := by
      have h1 : c' v 1 ∈ K.ends g := by
        rw [← hf0, hF'.1.ends v hvY 0 hnv]; exact mem_insert_of_mem _ rfl
      rw [hge] at h1
      rcases h1 with h1 | h1
      · exact absurd (h1.trans (hc0' v hvY).symm) (hF'.1.c_ne_succ hvY hnv).symm
      · exact h1
    obtain ⟨hF₁, hV₁, hvF₁, hE₁', hgF₁⟩ := hF'.1.shift hvY hnv
    rw [hc0' v hvY] at hV₁ hvF₁
    rw [hf0] at hE₁' hgF₁
    have hF₁K₁ : IsPathFam (K.deleteVertices {v}) (insert v (Y₁ \ {v'})) (shiftC v c')
        (shiftN v n') (shiftF v f') := by
      refine hF₁.of_le hK₁K (fun x hx ↦ ⟨famVerts_subset hF₁ hx, fun h ↦
        hvF₁ (mem_singleton_iff.1 h ▸ hx)⟩) ?_
      intro e he
      refine ⟨(famGraph_edgeSet hF₁ ▸ (famGraph_le hF₁).edgeSet_subset) he, fun x hx hinc ↦ ?_⟩
      have hxv : x = v := hx
      rw [hxv] at hinc
      exact hgF₁ (hvg e ((famGraph_edgeSet hF₁ ▸ (famGraph_le hF₁).edgeSet_subset) he) hinc ▸ he)
    have hgood₁ : IsGoodFam (K.deleteVertices {v}) Y₁ Z (insert v (Y₁ \ {v'})) (shiftC v c')
        (shiftN v n') (shiftF v f') := by
      refine ⟨hF₁K₁, hYf, by rw [hYc, hY₁], fun y hy ↦ ?_⟩
      by_cases hyv : y = v
      · rw [hyv, shiftC_self, shiftC_self, shiftN_self, Nat.sub_add_cancel hnv]
        exact ⟨hc1 ▸ hv'Y₁, (hF'.2.2.2 v hvY).2⟩
      · rw [shiftC_of_ne hyv, shiftC_of_ne hyv, shiftN_of_ne hyv, hc0' y hy]
        have hy' : y ∈ Y₁ \ {v'} := (mem_insert_iff.1 hy).resolve_left hyv
        exact ⟨hy'.1, hc0' y hy ▸ (hF'.2.2.2 y hy).2⟩
    have hM₁ := hMu _ (hY₁ ▸ isPathSystem_famGraph hgood₁)
    have hVs : famVerts (insert v (Y₁ \ {v'})) (shiftC v c') (shiftN v n') = famVerts Y₁ c n := by
      rw [← famGraph_vertexSet hF₁K₁, hM₁, hFV]
    have hEs : famEdges (insert v (Y₁ \ {v'})) (shiftN v n') (shiftF v f') = famEdges Y₁ n f := by
      rw [← famGraph_edgeSet hF₁K₁, hM₁, hFE]
    rw [← hfam']
    change subOn _ (famVerts _ c' n') (famEdges _ n' f') =
      subOn _ (famVerts _ (extC v' v c) (extN v' n)) (famEdges _ (extN v' n) (extF v' g f))
    rw [hV₁, hE₁', hVs, hEs, hV₂, hE₂]
  · rw [famGraph_vertexSet hF₂, hV₂, hFV, hMV]
    change insert v (K.vertexSet \ {v}) = K.vertexSet
    rw [insert_sdiff_singleton, insert_eq_of_mem hvK]

variable {G : Hypergraph α β}

/-- A step as in the chain of (12.1), except that in case (a) any number of edges may move, all
with both ends in the separating set. -/
def IsChainStep' (k : ℕ) (A B A₁ B₁ : Hypergraph α β) : Prop :=
  ((A ∩ B).vertexSet = (B ∩ A₁).vertexSet ∧ (A₁ ∩ B₁).vertexSet = (B ∩ A₁).vertexSet) ∨
    IsChainStep k A B A₁ B₁

/-- **One step of the converse of (12.1).** If `(A, B)` and `(A₁, B₁)` are as in a step of the
chain of (12.1), and every vertex of `B ∩ A₁` is in `A ∩ B` or `A₁ ∩ B₁`, then a unique set of
paths in `B₁ ∩ A'` gives one in `B ∩ A'`. -/
theorem uniqSystem_step_back [Nonempty β] {A B A₁ B₁ A' B' : Hypergraph α β}
    (hs : G.IsSeparation A B) (hs₁ : G.IsSeparation A₁ B₁) (hs' : G.IsSeparation A' B')
    (hAA₁ : A ≤ A₁) (hB₁B : B₁ ≤ B) (hA₁A' : A₁ ≤ A') (hB'B₁ : B' ≤ B₁)
    (hk : (A ∩ B).vertexSet.ncard = k) (hk₁ : (A₁ ∩ B₁).vertexSet.ncard = k)
    (hst : IsChainStep' k A B A₁ B₁)
    (hcov : (B ∩ A₁).vertexSet ⊆ (A ∩ B).vertexSet ∪ (A₁ ∩ B₁).vertexSet)
    (hU : UniqSystem (B₁ ∩ A') (A₁ ∩ B₁).vertexSet (A' ∩ B').vertexSet k) :
    UniqSystem (B ∩ A') (A ∩ B).vertexSet (A' ∩ B').vertexSet k := by
  classical
  have hA := hs.left_le
  have hB := hs.right_le
  have hA₁ := hs₁.left_le
  have hB₁ := hs₁.right_le
  have hA' := hs'.left_le
  have hKG : B ∩ A' ≤ G := GM10.inter_le hB hA'
  have hK₁G : B₁ ∩ A' ≤ G := GM10.inter_le hB₁ hA'
  have hBA₁G : B ∩ A₁ ≤ G := GM10.inter_le hB hA₁
  have hK₁K : B₁ ∩ A' ≤ B ∩ A' := (GM10.le_iff_of_le hK₁G hKG).2
    ⟨fun x hx ↦ ⟨hB₁B.vertexSet_subset hx.1, hx.2⟩, fun e he ↦ ⟨hB₁B.edgeSet_subset he.1, he.2⟩⟩
  -- An edge of `B ∩ A'` that is not in `B₁ ∩ A'` is in `B ∩ A₁`.
  have hEK' : ∀ e ∈ (B ∩ A').edgeSet, e ∉ (B₁ ∩ A').edgeSet → e ∈ (B ∩ A₁).edgeSet := by
    intro e he hne
    have heG : e ∈ G.edgeSet := hB.edgeSet_subset he.1
    rw [← hs₁.edgeSet_union] at heG
    rcases heG with h | h
    · exact ⟨he.1, h⟩
    · exact absurd ⟨h, he.2⟩ hne
  have hY₁K₁ : (A₁ ∩ B₁).vertexSet ⊆ (B₁ ∩ A').vertexSet := fun x hx ↦
    ⟨hx.2, hA₁A'.vertexSet_subset hx.1⟩
  have hVK : (B ∩ A').vertexSet ⊆ (B ∩ A₁).vertexSet ∪ (B₁ ∩ A').vertexSet := by
    intro x hx
    have hxG : x ∈ G.vertexSet := hB.vertexSet_subset hx.1
    rw [← hs₁.vertexSet_union] at hxG
    rcases hxG with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h, hx.2⟩
  have hY₁f : (A₁ ∩ B₁).vertexSet.Finite := (A₁ ∩ B₁).vertexSet_finite
  by_cases hYY : (A ∩ B).vertexSet = (A₁ ∩ B₁).vertexSet
  · -- The vertex sets agree: the new edges have both ends in them.
    have hsub : (B ∩ A₁).vertexSet ⊆ (A₁ ∩ B₁).vertexSet := fun x hx ↦ by
      rcases hcov hx with h | h
      · exact hYY ▸ h
      · exact h
    rw [hYY]
    refine hU.addEdges hK₁K hY₁f hk₁ ?_ ?_
    · refine (hVK.trans (union_subset (hsub.trans hY₁K₁) subset_rfl)).antisymm
        hK₁K.vertexSet_subset
    · intro e he hne
      have he₁ := hEK' e he hne
      rw [← hKG.ends_eq e he, hBA₁G.ends_eq e he₁]
      exact fun x hx ↦ hsub ((B ∩ A₁).vertex_mem_of_inc hx)
  have hst : IsChainStep k A B A₁ B₁ := by
    rcases hst with ⟨h1, h2⟩ | h
    · exact absurd (h1.trans h2.symm) hYY
    · exact h
  obtain ⟨g, hgE, hcase⟩ := hst
  have hgBA₁ : g ∈ (B ∩ A₁).edgeSet := hgE ▸ mem_singleton g
  have hgK : g ∈ (B ∩ A').edgeSet := ⟨hgBA₁.1, hA₁A'.edgeSet_subset hgBA₁.2⟩
  have hEK : ∀ e ∈ (B ∩ A').edgeSet, e ∉ (B₁ ∩ A').edgeSet → e = g := by
    intro e he hne
    have := hEK' e he hne
    rw [hgE] at this
    exact this
  have hends : (B ∩ A').ends g = (B ∩ A₁).ends g := by
    rw [← hKG.ends_eq g hgK, hBA₁G.ends_eq g hgBA₁]
  · -- Otherwise the step is (b), with `v ≠ v'`.
    obtain ⟨X, v, v', -, hX, hge, hY, hY₁⟩ : ∃ X : Set α, ∃ v v' : α,
        (A ∩ B).vertexSet ∩ (A₁ ∩ B₁).vertexSet = X ∧ X.ncard = k - 1 ∧
        (B ∩ A₁).ends g = {v, v'} ∧ (A ∩ B).vertexSet = insert v X ∧
        (A₁ ∩ B₁).vertexSet = insert v' X := by
      rcases hcase with ⟨h1, h2⟩ | h
      · exact absurd (h1.trans h2.symm) hYY
      · exact h
    have hXf : X.Finite := by
      have : X ⊆ (A ∩ B).vertexSet := hY ▸ subset_insert v X
      exact (A ∩ B).vertexSet_finite.subset this
    have hvX : v ∉ X := by
      intro h
      have h1 : (A ∩ B).vertexSet = X := by rw [hY, insert_eq_of_mem h]
      have h2 : 1 ≤ k := by
        rw [← hk, hY]; exact Nat.one_le_iff_ne_zero.2 (ncard_ne_zero_of_mem (mem_insert _ _)
          (hXf.insert v))
      rw [h1, hX] at hk
      omega
    have hv'X : v' ∉ X := by
      intro h
      have h1 : (A₁ ∩ B₁).vertexSet = X := by rw [hY₁, insert_eq_of_mem h]
      have h2 : 1 ≤ k := by
        rw [← hk₁, hY₁]; exact Nat.one_le_iff_ne_zero.2 (ncard_ne_zero_of_mem (mem_insert _ _)
          (hXf.insert v'))
      rw [h1, hX] at hk₁
      omega
    have hvv' : v ≠ v' := fun h ↦ hYY (by rw [hY, hY₁, h])
    have hvY : v ∈ (A ∩ B).vertexSet := hY ▸ mem_insert _ _
    have hvK₁ : v ∉ (B₁ ∩ A').vertexSet := by
      rintro ⟨h1, -⟩
      have : v ∈ (A₁ ∩ B₁).vertexSet := ⟨hAA₁.vertexSet_subset hvY.1, h1⟩
      rw [hY₁] at this
      rcases this with h | h
      · exact hvv' h
      · exact hvX h
    have hvK : v ∈ (B ∩ A').vertexSet := ⟨hvY.2, hA₁A'.vertexSet_subset (hAA₁.vertexSet_subset hvY.1)⟩
    have hvZ : v ∉ (A' ∩ B').vertexSet := fun h ↦ hvK₁ ⟨hB'B₁.vertexSet_subset h.2, h.1⟩
    have hvg : ∀ e ∈ (B ∩ A').edgeSet, (B ∩ A').Inc e v → e = g := by
      intro e he hinc
      by_contra hne
      have he₁ : e ∈ (B₁ ∩ A').edgeSet := by
        by_contra h
        exact hne (hEK e he h)
      have : v ∈ (B₁ ∩ A').ends e := by
        rw [← hK₁K.ends_eq e he₁]; exact hinc
      exact hvK₁ ((B₁ ∩ A').vertex_mem_of_inc this)
    have hdel : (B ∩ A').deleteVertices {v} = B₁ ∩ A' := by
      refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
        ((GM10.deleteVertices_le _ _).trans hKG) hK₁G ?_ ?_
      · apply Subset.antisymm
        · rintro x ⟨hx, hxv⟩
          rcases hVK hx with h | h
          · rcases hcov h with h' | h'
            · rw [hY] at h'
              rcases h' with rfl | h'
              · exact absurd rfl hxv
              · exact hY₁K₁ (hY₁ ▸ mem_insert_of_mem _ h')
            · exact hY₁K₁ h'
          · exact h
        · intro x hx
          exact ⟨hK₁K.vertexSet_subset hx, fun h ↦ hvK₁ (mem_singleton_iff.1 h ▸ hx)⟩
      · apply Subset.antisymm
        · rintro e ⟨he, hn⟩
          by_contra h
          have := hEK e he h
          subst this
          refine hn v rfl ?_
          change v ∈ (B ∩ A').ends e
          rw [hends, hge]
          exact mem_insert _ _
        · intro e he
          refine ⟨hK₁K.edgeSet_subset he, fun x hx hinc ↦ hvK₁ ?_⟩
          have hxv : x = v := hx
          have : x ∈ (B₁ ∩ A').ends e := by rw [← hK₁K.ends_eq e he]; exact hinc
          exact hxv ▸ (B₁ ∩ A').vertex_mem_of_inc this
    rw [← hdel] at hU
    have hv'Y₁ : v' ∈ (A₁ ∩ B₁).vertexSet := hY₁ ▸ mem_insert _ _
    have hvY₁ : v ∉ (A₁ ∩ B₁).vertexSet := fun h ↦ hvK₁ (hY₁K₁ h)
    have := hU.addFirst hY₁f hk₁ hv'Y₁ hvK hvY₁ hvZ hgK (by rw [hends, hge]) hvg
    rwa [hY₁, insert_sdiff_self_of_notMem hv'X, ← hY] at this

/-- `a i ≤ a j` along a chain whose steps grow. -/
theorem le_of_steps {γ : Type*} [Preorder γ] {a : ℕ → γ} {m : ℕ} (h : ∀ j < m, a j ≤ a (j + 1))
    {i j : ℕ} (hij : i ≤ j) (hjm : j ≤ m) : a i ≤ a j := by
  induction j with
  | zero => rw [Nat.le_zero.1 hij]
  | succ j ih =>
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · exact (ih (by omega) (by omega)).trans (h j (by omega))

/-- **The converse of (12.1).** Let `(a j, b j)` (`j ≤ m`) be separations of `G` of order `k`,
where each step is as in the chain of (12.1) and every vertex of `b j ∩ a (j + 1)` is in
`a j ∩ b j` or `a (j + 1) ∩ b (j + 1)`. Then `b 0 ∩ a m` has a unique set of `k` disjoint paths
between `V(a 0 ∩ b 0)` and `V(a m ∩ b m)`, and every vertex of `b 0 ∩ a m` is on one of them. -/
theorem uniqSystem_of_steps [Nonempty β] : ∀ (m : ℕ) (a b : ℕ → Hypergraph α β),
    (∀ j ≤ m, G.IsSeparation (a j) (b j)) → (∀ j ≤ m, (a j ∩ b j).vertexSet.ncard = k) →
    (∀ j < m, a j ≤ a (j + 1) ∧ b (j + 1) ≤ b j) →
    (∀ j < m, IsChainStep' k (a j) (b j) (a (j + 1)) (b (j + 1)) ∧
      (b j ∩ a (j + 1)).vertexSet ⊆ (a j ∩ b j).vertexSet ∪ (a (j + 1) ∩ b (j + 1)).vertexSet) →
    UniqSystem (b 0 ∩ a m) (a 0 ∩ b 0).vertexSet (a m ∩ b m).vertexSet k := by
  intro m
  induction m with
  | zero =>
    intro a b hs hk _ _
    have hE : (b 0 ∩ a 0).edgeSet = ∅ := by
      rw [GM10.inter_comm]; exact (hs 0 le_rfl).edgeSet_inter_eq
    have hV : (b 0 ∩ a 0).vertexSet = (a 0 ∩ b 0).vertexSet := by
      rw [GM10.inter_comm]
    have := uniqSystem_of_edgeSet_eq_empty hE
    rwa [hV, hk 0 le_rfl] at this
  | succ m ih =>
    intro a b hs hk hmono hst
    have hU := ih (fun j ↦ a (j + 1)) (fun j ↦ b (j + 1)) (fun j hj ↦ hs (j + 1) (by omega))
      (fun j hj ↦ hk (j + 1) (by omega)) (fun j hj ↦ hmono (j + 1) (by omega))
      (fun j hj ↦ hst (j + 1) (by omega))
    have ha : a 1 ≤ a (m + 1) := le_of_steps (a := a) (m := m + 1)
      (fun j hj ↦ (hmono j hj).1) (by omega) le_rfl
    have hb : b (m + 1) ≤ b 1 := le_of_steps (γ := (Hypergraph α β)ᵒᵈ) (a := fun j ↦ OrderDual.toDual (b j))
      (m := m + 1) (fun j hj ↦ (hmono j hj).2) (by omega) le_rfl
    exact uniqSystem_step_back (hs 0 (by omega)) (hs 1 (by omega)) (hs (m + 1) le_rfl)
      (hmono 0 (by omega)).1 (hmono 0 (by omega)).2 ha hb (hk 0 (by omega)) (hk 1 (by omega))
      (hst 0 (by omega)).1 (hst 0 (by omega)).2 hU

end Converse

end GM21
end GraphMinor
