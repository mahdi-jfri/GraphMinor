module

public import GraphMinor.GM21.Section11One
public import GraphMinor.GM21.Section11Defs
public import GraphMinor.GM21.Section11Core
public import GraphMinor.GM21.Section1Two
public import GraphMinor.GM21.LinkagePaths
public import GraphMinor.GM21.SeparationGluing

/-!
# Graph Minors XXI, Section 12: families of disjoint paths

The proof of (12.1) changes a set of disjoint paths by hand. Here a set of disjoint paths is given
by sequences: path `i` has vertices `c i 0, …, c i (n i)` and edges `f i 0, …, f i (n i - 1)`, where
`f i a` joins `c i a` and `c i (a + 1)` (`IsPathFam`). Its union `famGraph` is a linkage whose
blocks are the pairs of ends (`isLinkage_famGraph`, `linkagePattern_famGraph`), and every set of
`k` disjoint paths between two sets of size `k` is of this form (`exists_pathFam_of_isPathSystem`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set Hypergraph

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w}

/-- Path `i` has vertices `c i 0, …, c i (n i)` in order and edges `f i 0, …, f i (n i - 1)`. The
paths are disjoint. -/
structure IsPathFam (H : Hypergraph α β) (I : Set ι) (c : ι → ℕ → α) (n : ι → ℕ)
    (f : ι → ℕ → β) : Prop where
  inj : ∀ i ∈ I, InjOn (c i) (Iic (n i))
  disj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (c i '' Iic (n i)) (c j '' Iic (n j))
  mem : ∀ i ∈ I, ∀ a ≤ n i, c i a ∈ H.vertexSet
  edge_mem : ∀ i ∈ I, ∀ a < n i, f i a ∈ H.edgeSet
  ends : ∀ i ∈ I, ∀ a < n i, H.ends (f i a) = {c i a, c i (a + 1)}

/-- The vertices of the family. -/
def famVerts (I : Set ι) (c : ι → ℕ → α) (n : ι → ℕ) : Set α := ⋃ i ∈ I, c i '' Iic (n i)

/-- The edges of the family. -/
def famEdges (I : Set ι) (n : ι → ℕ) (f : ι → ℕ → β) : Set β := ⋃ i ∈ I, f i '' Iio (n i)

/-- The union of the paths of the family. -/
def famGraph (H : Hypergraph α β) (I : Set ι) (c : ι → ℕ → α) (n : ι → ℕ) (f : ι → ℕ → β) :
    Hypergraph α β :=
  subOn H (famVerts I c n) (famEdges I n f)

section Fam

variable {H : Hypergraph α β} {I : Set ι} {c : ι → ℕ → α} {n : ι → ℕ} {f : ι → ℕ → β}

theorem mem_famVerts {v : α} : v ∈ famVerts I c n ↔ ∃ i ∈ I, ∃ a ≤ n i, c i a = v := by
  simp [famVerts]

theorem mem_famEdges {g : β} : g ∈ famEdges I n f ↔ ∃ i ∈ I, ∃ a < n i, f i a = g := by
  simp [famEdges]

variable (hF : IsPathFam H I c n f)
include hF

/-- A vertex of the family has one place in it. -/
theorem IsPathFam.eq_of_eq {i j : ι} (hi : i ∈ I) (hj : j ∈ I) {a b : ℕ} (ha : a ≤ n i)
    (hb : b ≤ n j) (h : c i a = c j b) : i = j ∧ a = b := by
  by_cases hij : i = j
  · subst hij
    exact ⟨rfl, hF.inj i hi ha hb h⟩
  · exact absurd (disjoint_left.1 (hF.disj i hi j hj hij) ⟨a, ha, rfl⟩ ⟨b, hb, h.symm⟩) id

theorem IsPathFam.inc_iff {i : ι} (hi : i ∈ I) {a : ℕ} (ha : a < n i) {v : α} :
    H.Inc (f i a) v ↔ v = c i a ∨ v = c i (a + 1) := by
  have := hF.ends i hi a ha
  change v ∈ H.ends (f i a) ↔ _
  rw [this]
  rfl

theorem IsPathFam.c_ne_succ {i : ι} (hi : i ∈ I) {a : ℕ} (ha : a < n i) :
    c i a ≠ c i (a + 1) := fun h ↦ by
  have := hF.inj i hi (show a ∈ Iic (n i) from ha.le) (show a + 1 ∈ Iic (n i) from ha) h
  omega

theorem famVerts_subset : famVerts I c n ⊆ H.vertexSet := fun v hv ↦ by
  obtain ⟨i, hi, a, ha, rfl⟩ := mem_famVerts.1 hv
  exact hF.mem i hi a ha

theorem famGraph_le : famGraph H I c n f ≤ H := by
  refine subOn_le fun g hg _ v hv ↦ ?_
  obtain ⟨i, hi, a, ha, rfl⟩ := mem_famEdges.1 hg
  rcases (hF.inc_iff hi ha).1 hv with rfl | rfl
  · exact mem_famVerts.2 ⟨i, hi, a, ha.le, rfl⟩
  · exact mem_famVerts.2 ⟨i, hi, a + 1, ha, rfl⟩

theorem famGraph_vertexSet : (famGraph H I c n f).vertexSet = famVerts I c n :=
  inter_eq_left.2 (famVerts_subset hF)

theorem famGraph_edgeSet : (famGraph H I c n f).edgeSet = famEdges I n f := by
  refine inter_eq_left.2 fun g hg ↦ ?_
  obtain ⟨i, hi, a, ha, rfl⟩ := mem_famEdges.1 hg
  exact hF.edge_mem i hi a ha

/-- The edges of the family at the vertex `c i a`. -/
theorem IsPathFam.mem_incidentEdges_iff {i : ι} (hi : i ∈ I) {a : ℕ} (ha : a ≤ n i) {g : β} :
    g ∈ incidentEdges (famGraph H I c n f) (c i a) ↔
      (a < n i ∧ g = f i a) ∨ (0 < a ∧ g = f i (a - 1)) := by
  constructor
  · rintro ⟨-, hinc, hg, -⟩
    obtain ⟨j, hj, b, hb, rfl⟩ := mem_famEdges.1 hg
    rcases (hF.inc_iff hj hb).1 hinc with h | h
    · obtain ⟨rfl, rfl⟩ := hF.eq_of_eq hi hj ha hb.le h
      exact Or.inl ⟨hb, rfl⟩
    · obtain ⟨rfl, rfl⟩ := hF.eq_of_eq hi hj ha hb h
      exact Or.inr ⟨by omega, rfl⟩
  · have hv : c i a ∈ famVerts I c n := mem_famVerts.2 ⟨i, hi, a, ha, rfl⟩
    rintro (⟨hlt, rfl⟩ | ⟨hpos, rfl⟩)
    · have hg : f i a ∈ famEdges I n f := mem_famEdges.2 ⟨i, hi, a, hlt, rfl⟩
      exact ⟨⟨hg, hF.edge_mem i hi a hlt⟩, (hF.inc_iff hi hlt).2 (Or.inl rfl), hg, hv⟩
    · have hlt : a - 1 < n i := by omega
      have hg : f i (a - 1) ∈ famEdges I n f := mem_famEdges.2 ⟨i, hi, a - 1, hlt, rfl⟩
      refine ⟨⟨hg, hF.edge_mem i hi _ hlt⟩, (hF.inc_iff hi hlt).2 (Or.inr ?_), hg, hv⟩
      rw [Nat.sub_add_cancel hpos]

theorem IsPathFam.f_ne {i : ι} (hi : i ∈ I) {a b : ℕ} (ha : a < n i) (hb : b < n i)
    (hab : a ≠ b) : f i a ≠ f i b := fun h ↦ by
  have h1 : c i a ∈ H.ends (f i a) := (hF.inc_iff hi ha).2 (Or.inl rfl)
  rw [h] at h1
  rcases (hF.inc_iff hi hb).1 h1 with h' | h'
  · exact hab (hF.inj i hi ha.le hb.le h')
  · have h2 : c i (a + 1) ∈ H.ends (f i a) := (hF.inc_iff hi ha).2 (Or.inr rfl)
    rw [h] at h2
    have := hF.inj i hi ha.le (show b + 1 ∈ Iic (n i) from hb) h'
    rcases (hF.inc_iff hi hb).1 h2 with h'' | h''
    · have := hF.inj i hi (show a + 1 ∈ Iic (n i) from ha) hb.le h''
      omega
    · have := hF.inj i hi (show a + 1 ∈ Iic (n i) from ha) (show b + 1 ∈ Iic (n i) from hb) h''
      omega

theorem IsPathFam.ncard_incidentEdges {i : ι} (hi : i ∈ I) {a : ℕ} (ha : a ≤ n i) :
    (incidentEdges (famGraph H I c n f) (c i a)).ncard =
      (if a < n i then 1 else 0) + (if 0 < a then 1 else 0) := by
  classical
  have hset : incidentEdges (famGraph H I c n f) (c i a) =
      (if a < n i then {f i a} else ∅) ∪ (if 0 < a then {f i (a - 1)} else ∅) := by
    ext g
    rw [hF.mem_incidentEdges_iff hi ha]
    split_ifs <;> simp_all [or_comm]
  rw [hset]
  have hd : Disjoint (if a < n i then ({f i a} : Set β) else ∅)
      (if 0 < a then {f i (a - 1)} else ∅) := by
    split_ifs with h1 h2
    · exact disjoint_singleton.2 (hF.f_ne hi h1 (by omega) (by omega))
    all_goals simp
  rw [ncard_union_eq hd (by split_ifs <;> simp) (by split_ifs <;> simp)]
  split_ifs <;> simp

theorem famGraph_ends {g : β} (hg : g ∈ (famGraph H I c n f).edgeSet) :
    ((famGraph H I c n f).ends g).ncard = 2 := by
  rw [← (famGraph_le hF).ends_eq g hg]
  rw [famGraph_edgeSet hF] at hg
  obtain ⟨i, hi, a, ha, rfl⟩ := mem_famEdges.1 hg
  rw [hF.ends i hi a ha, ncard_pair (hF.c_ne_succ hi ha)]

theorem IsPathFam.reachable_zero {i : ι} (hi : i ∈ I) {a : ℕ} (ha : a ≤ n i) :
    (famGraph H I c n f).skeleton.Reachable (c i 0) (c i a) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    refine (ih (by omega)).trans (SimpleGraph.Adj.reachable ⟨hF.c_ne_succ hi ha, f i a, ?_, ?_⟩)
    · have := (hF.mem_incidentEdges_iff hi (a := a) (by omega) (g := f i a)).2 (Or.inl ⟨ha, rfl⟩)
      exact this.2
    · have := (hF.mem_incidentEdges_iff hi (a := a + 1) ha (g := f i a)).2
        (Or.inr ⟨by omega, rfl⟩)
      exact this.2

/-- A walk of the family stays in one path. -/
theorem IsPathFam.mem_of_reachable {i : ι} (hi : i ∈ I) {a : ℕ} (ha : a ≤ n i) {w : α}
    (hr : (famGraph H I c n f).skeleton.Reachable (c i a) w) : ∃ b ≤ n i, c i b = w := by
  obtain ⟨p⟩ := hr
  suffices h : ∀ u w (p : (famGraph H I c n f).skeleton.Walk u w), (∃ a ≤ n i, c i a = u) →
      ∃ b ≤ n i, c i b = w from h _ _ p ⟨a, ha, rfl⟩
  intro u w p
  induction p with
  | nil => exact id
  | cons hadj _ ih =>
    rintro ⟨a, ha, rfl⟩
    apply ih
    obtain ⟨-, g, hg1, hg2⟩ := hadj
    have hg : g ∈ incidentEdges (famGraph H I c n f) (c i a) := ⟨(famGraph H I c n f).edge_mem_of_inc hg1, hg1⟩
    rcases (hF.mem_incidentEdges_iff hi ha).1 hg with ⟨hlt, rfl⟩ | ⟨hpos, rfl⟩
    · rcases (hF.inc_iff hi hlt).1 hg2.1 with h | h
      exacts [⟨a, ha, h.symm⟩, ⟨a + 1, hlt, h.symm⟩]
    · rcases (hF.inc_iff hi (by omega)).1 hg2.1 with h | h
      · exact ⟨a - 1, by omega, h.symm⟩
      · exact ⟨a - 1 + 1, by omega, h.symm⟩

/-- **The union of the family is a linkage.** -/
theorem isLinkage_famGraph : IsLinkage H (famGraph H I c n f) := by
  refine isLinkage_of_deg_le_two_of_reachable_deg_le_one (famGraph_le hF)
    (fun g hg ↦ famGraph_ends hF hg) ?_ ?_
  · intro v hv
    rw [famGraph_vertexSet hF] at hv
    obtain ⟨i, hi, a, ha, rfl⟩ := mem_famVerts.1 hv
    rw [hF.ncard_incidentEdges hi ha]
    split_ifs <;> omega
  · intro v hv
    rw [famGraph_vertexSet hF] at hv
    obtain ⟨i, hi, a, ha, rfl⟩ := mem_famVerts.1 hv
    refine ⟨c i (n i), by rw [famGraph_vertexSet hF]; exact mem_famVerts.2 ⟨i, hi, _, le_rfl, rfl⟩,
      (hF.reachable_zero hi ha).symm.trans (hF.reachable_zero hi le_rfl), ?_⟩
    rw [hF.ncard_incidentEdges hi le_rfl]
    split_ifs <;> omega

theorem IsPathFam.mem_terminals_iff {i : ι} (hi : i ∈ I) {a : ℕ} (ha : a ≤ n i) :
    c i a ∈ terminals (famGraph H I c n f) ↔ a = 0 ∨ a = n i := by
  change (c i a ∈ (famGraph H I c n f).vertexSet ∧ vertexDegree _ _ ≤ 1) ↔ _
  rw [vertexDegree_eq_ncard_incidentEdges (fun g hg ↦ famGraph_ends hF hg),
    hF.ncard_incidentEdges hi ha, famGraph_vertexSet hF]
  have hv : c i a ∈ famVerts I c n := mem_famVerts.2 ⟨i, hi, a, ha, rfl⟩
  constructor
  · rintro ⟨-, h⟩
    split_ifs at h <;> omega
  · intro h
    refine ⟨hv, ?_⟩
    split_ifs <;> omega

theorem terminals_famGraph :
    terminals (famGraph H I c n f) = ⋃ i ∈ I, {c i 0, c i (n i)} := by
  ext v
  simp only [mem_iUnion, mem_insert_iff, mem_singleton_iff]
  constructor
  · intro hv
    have hvV := hv.1
    rw [famGraph_vertexSet hF] at hvV
    obtain ⟨i, hi, a, ha, rfl⟩ := mem_famVerts.1 hvV
    rcases (hF.mem_terminals_iff hi ha).1 hv with rfl | rfl
    exacts [⟨i, hi, Or.inl rfl⟩, ⟨i, hi, Or.inr rfl⟩]
  · rintro ⟨i, hi, rfl | rfl⟩
    · exact (hF.mem_terminals_iff hi (Nat.zero_le _)).2 (Or.inl rfl)
    · exact (hF.mem_terminals_iff hi le_rfl).2 (Or.inr rfl)

/-- **The blocks of the family are the pairs of ends.** -/
theorem linkagePattern_famGraph :
    linkagePattern (famGraph H I c n f) = (fun i ↦ {c i 0, c i (n i)}) '' I := by
  have hL := isLinkage_famGraph hF
  have hblock : ∀ i ∈ I, ∀ a ≤ n i, a = 0 ∨ a = n i →
      {t' ∈ terminals (famGraph H I c n f) |
        (famGraph H I c n f).skeleton.Reachable (c i a) t'} = {c i 0, c i (n i)} := by
    intro i hi a ha _
    ext t'
    constructor
    · rintro ⟨ht', hr⟩
      obtain ⟨b, hb, rfl⟩ := hF.mem_of_reachable hi ha hr
      rcases (hF.mem_terminals_iff hi hb).1 ht' with rfl | rfl
      exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl)
      · exact ⟨(hF.mem_terminals_iff hi (Nat.zero_le _)).2 (Or.inl rfl),
          (hF.reachable_zero hi ha).symm⟩
      · exact ⟨(hF.mem_terminals_iff hi le_rfl).2 (Or.inr rfl),
          (hF.reachable_zero hi ha).symm.trans (hF.reachable_zero hi le_rfl)⟩
  rw [linkagePattern_eq_image hL]
  ext B
  constructor
  · rintro ⟨t, ht, rfl⟩
    have htV := ht.1
    rw [famGraph_vertexSet hF] at htV
    obtain ⟨i, hi, a, ha, rfl⟩ := mem_famVerts.1 htV
    exact ⟨i, hi, (hblock i hi a ha ((hF.mem_terminals_iff hi ha).1 ht)).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨c i 0, (hF.mem_terminals_iff hi (Nat.zero_le _)).2 (Or.inl rfl),
      hblock i hi 0 (Nat.zero_le _) (Or.inl rfl)⟩

end Fam

/-! ## Families and sets of disjoint paths -/

section Systems

/-- A subgraph of `K` is the part of `K` on its own vertices and edges. -/
theorem eq_subOn_of_le {M K : Hypergraph α β} (h : M ≤ K) :
    subOn K M.vertexSet M.edgeSet = M := by
  refine Hypergraph.ext (inter_eq_left.2 h.vertexSet_subset) (inter_eq_left.2 h.edgeSet_subset) ?_
  funext e x
  apply propext
  constructor
  · rintro ⟨hinc, he, -⟩
    have hx : x ∈ K.ends e := hinc
    rw [h.ends_eq e he] at hx
    exact hx
  · intro hinc
    have he := M.edge_mem_of_inc hinc
    refine ⟨?_, he, M.vertex_mem_of_inc hinc⟩
    have hx : x ∈ M.ends e := hinc
    rw [← h.ends_eq e he] at hx
    exact hx

variable {K K' : Hypergraph α β} {I : Set ι} {c : ι → ℕ → α} {n : ι → ℕ} {f : ι → ℕ → β}

theorem IsPathFam.mono (hF : IsPathFam K I c n f) (h : K ≤ K') : IsPathFam K' I c n f :=
  ⟨hF.inj, hF.disj, fun i hi a ha ↦ h.vertexSet_subset (hF.mem i hi a ha),
    fun i hi a ha ↦ h.edgeSet_subset (hF.edge_mem i hi a ha),
    fun i hi a ha ↦ by rw [h.ends_eq _ (hF.edge_mem i hi a ha)]; exact hF.ends i hi a ha⟩

theorem IsPathFam.of_le (hF : IsPathFam K' I c n f) (h : K ≤ K')
    (hV : famVerts I c n ⊆ K.vertexSet) (hE : famEdges I n f ⊆ K.edgeSet) :
    IsPathFam K I c n f := by
  refine ⟨hF.inj, hF.disj, fun i hi a ha ↦ hV (mem_famVerts.2 ⟨i, hi, a, ha, rfl⟩),
    fun i hi a ha ↦ hE (mem_famEdges.2 ⟨i, hi, a, ha, rfl⟩), fun i hi a ha ↦ ?_⟩
  rw [← h.ends_eq _ (hE (mem_famEdges.2 ⟨i, hi, a, ha, rfl⟩))]
  exact hF.ends i hi a ha

theorem famGraph_eq_of_le (hF : IsPathFam K I c n f) (h : K ≤ K') :
    famGraph K I c n f = famGraph K' I c n f :=
  GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq ((famGraph_le hF).trans h) (famGraph_le (hF.mono h))
    (by rw [famGraph_vertexSet hF, famGraph_vertexSet (hF.mono h)])
    (by rw [famGraph_edgeSet hF, famGraph_edgeSet (hF.mono h)])

/-- A family of `|Y|` disjoint paths of `K`, each from `Y` to `Z`. -/
def IsGoodFam (K : Hypergraph α β) (Y Z : Set α) (I : Set ι) (c : ι → ℕ → α) (n : ι → ℕ)
    (f : ι → ℕ → β) : Prop :=
  IsPathFam K I c n f ∧ I.Finite ∧ I.ncard = Y.ncard ∧ ∀ i ∈ I, c i 0 ∈ Y ∧ c i (n i) ∈ Z

/-- The union of a good family is a set of `|Y|` disjoint paths between `Y` and `Z`. -/
theorem isPathSystem_famGraph {Y Z : Set α} (hF : IsGoodFam K Y Z I c n f) :
    IsPathSystem K Y Z Y.ncard (famGraph K I c n f) := by
  obtain ⟨hF, hIf, hI, hYZ⟩ := hF
  refine ⟨isLinkage_famGraph hF, ?_, ?_⟩
  · have hinj : InjOn (fun i ↦ ({c i 0, c i (n i)} : Set α)) I := by
      intro i hi j hj h
      have h' : ({c i 0, c i (n i)} : Set α) = {c j 0, c j (n j)} := h
      have h0 : c i 0 ∈ ({c j 0, c j (n j)} : Set α) := h' ▸ mem_insert _ _
      rcases h0 with h0 | h0
      · exact (hF.eq_of_eq hi hj (Nat.zero_le _) (Nat.zero_le _) h0).1
      · exact (hF.eq_of_eq hi hj (Nat.zero_le _) le_rfl h0).1
    rw [linkagePattern_famGraph hF, hinj.ncard_image, hI]
  · rw [linkagePattern_famGraph hF]
    rintro P ⟨i, hi, rfl⟩
    exact ⟨c i 0, (hYZ i hi).1, c i (n i), (hYZ i hi).2, rfl⟩

end Systems

section Extract

variable {K M : Hypergraph α β}

/-- Every vertex of a linkage is joined in it to a terminal. -/
theorem exists_terminal_reachable (hL : IsLinkage K M) {x : α} (hx : x ∈ M.vertexSet) :
    ∃ t ∈ terminals M, M.skeleton.Reachable x t := by
  set Q := reachableComponent M x
  have hQ : IsComponentOf M Q := isComponentOf_reachableComponent hL.2.1 hx
  have hQP : IsPathGraph Q := hL.2.2 _ hQ
  have hxQ : x ∈ Q.vertexSet := self_mem_reachableComponent hx
  by_cases hE : Q.edgeSet.Nonempty
  · obtain ⟨x₁, hx₁, x₂, hx₂, hne, hpath, hdeg⟩ := exists_isIndexedPath_of_isPathGraph hQP hE
    refine ⟨x₁, ⟨hx₁.1, ?_⟩, hx₁.2⟩
    rw [vertexDegree_eq_ncard_incidentEdges_of_isComponentOf hL.2.1 hQ hQP hx₁]
    exact (hdeg x₁ hx₁).2 (Or.inl rfl)
  · refine ⟨x, ⟨hx, ?_⟩, SimpleGraph.Reachable.refl _⟩
    rw [vertexDegree_eq_ncard_incidentEdges_of_isComponentOf hL.2.1 hQ hQP hxQ]
    have : incidentEdges Q x = ∅ := eq_empty_of_forall_notMem fun e he ↦ hE ⟨e, he.1⟩
    rw [this, ncard_empty]
    exact Nat.zero_le _

/-- The component of a terminal `y` of a linkage, as a sequence of vertices and edges starting at
`y`. -/
theorem exists_seq_of_terminal [Nonempty β] (hL : IsLinkage K M) {y : α} (hy : y ∈ terminals M) :
    ∃ (m : ℕ) (w : ℕ → α) (g : ℕ → β), InjOn w (Iic m) ∧ w 0 = y ∧ w m ∈ terminals M ∧
      (∀ a ≤ m, M.skeleton.Reachable y (w a)) ∧
      (∀ x ∈ M.vertexSet, M.skeleton.Reachable y x → ∃ a ≤ m, w a = x) ∧
      (∀ a < m, g a ∈ M.edgeSet ∧ M.ends (g a) = {w a, w (a + 1)}) ∧
      (∀ e ∈ M.edgeSet, ∀ a ≤ m, M.Inc e (w a) → ∃ b < m, g b = e) := by
  classical
  have hyV : y ∈ M.vertexSet := hy.1
  set Q := reachableComponent M y with hQdef
  have hQ : IsComponentOf M Q := isComponentOf_reachableComponent hL.2.1 hyV
  have hQP : IsPathGraph Q := hL.2.2 _ hQ
  have hyQ : y ∈ Q.vertexSet := self_mem_reachableComponent hyV
  have hQM : Q ≤ M := reachableComponent_le M y
  -- An edge of `M` at a vertex reachable from `y` is an edge of `Q`.
  have hEQ : ∀ e ∈ M.edgeSet, ∀ u, M.Inc e u → M.skeleton.Reachable y u → e ∈ Q.edgeSet :=
    fun e he u hu hr ↦ ⟨he, u, hu, hr⟩
  by_cases hE : Q.edgeSet.Nonempty
  · obtain ⟨x₁, hx₁, x₂, hx₂, hne, hpath, hdeg⟩ := exists_isIndexedPath_of_isPathGraph hQP hE
    have hyd : (incidentEdges Q y).ncard ≤ 1 := by
      rw [← vertexDegree_eq_ncard_incidentEdges_of_isComponentOf hL.2.1 hQ hQP hyQ]
      exact hy.2
    have hpath' : ∃ y', IsIndexedPath Q y y' ∧ y' ∈ Q.vertexSet ∧ (incidentEdges Q y').ncard ≤ 1 := by
      rcases (hdeg y hyQ).1 hyd with rfl | rfl
      · exact ⟨x₂, hpath, hx₂, (hdeg x₂ hx₂).2 (Or.inr rfl)⟩
      · exact ⟨x₁, hpath.symm, hx₁, (hdeg x₁ hx₁).2 (Or.inl rfl)⟩
    obtain ⟨y', hp, hy'Q, hy'd⟩ := hpath'
    obtain ⟨m, w, hm, hinj, hw0, hwm, hV, hadj⟩ := exists_nat_seq_of_isIndexedPath hp
    have hwQ : ∀ a ≤ m, w a ∈ Q.vertexSet := fun a ha ↦ hV ▸ ⟨a, ha, rfl⟩
    have hends : ∀ e ∈ M.edgeSet, ∀ u v : α, u ≠ v → M.Inc e u → M.Inc e v →
        M.ends e = {u, v} := fun e he u v huv hu hv ↦
      (eq_of_subset_of_ncard_le (s := ({u, v} : Set α)) (t := M.ends e)
        (by rintro x (rfl | rfl); exacts [hu, hv])
        (by rw [hL.ends_ncard_eq_two he, ncard_pair huv])
        (M.vertexSet_finite.subset fun x hx ↦ M.vertex_mem_of_inc hx)).symm
    have hex : ∀ a, a < m → ∃ e, Q.Inc e (w a) ∧ Q.Inc e (w (a + 1)) := fun a ha ↦ by
      have := (hadj a ha.le (a + 1) ha).2 (Or.inl rfl)
      exact this.2
    choose! g hg using hex
    have hgM : ∀ a < m, g a ∈ M.edgeSet ∧ M.ends (g a) = {w a, w (a + 1)} := fun a ha ↦ by
      have h1 := hQM.edgeSet_subset (Q.edge_mem_of_inc (hg a ha).1)
      refine ⟨h1, hends _ h1 _ _ ?_ (hg a ha).1.1 (hg a ha).2.1⟩
      intro h
      have := hinj (show a ∈ Iic m from ha.le) (show a + 1 ∈ Iic m from ha) h
      omega
    refine ⟨m, w, g, hinj, hw0, ?_, fun a ha ↦ (hwQ a ha).2, ?_, hgM, ?_⟩
    · rw [hwm]
      refine ⟨hQM.vertexSet_subset hy'Q, ?_⟩
      rw [vertexDegree_eq_ncard_incidentEdges_of_isComponentOf hL.2.1 hQ hQP hy'Q]
      exact hy'd
    · intro x hx hr
      obtain ⟨a, ha, rfl⟩ := hV ▸ (show x ∈ Q.vertexSet from ⟨hx, hr⟩)
      exact ⟨a, ha, rfl⟩
    · intro e he a ha hinc
      have heQ := hEQ e he _ hinc (hwQ a ha).2
      obtain ⟨u, hu, hua⟩ : ∃ u ∈ M.ends e, u ≠ w a := by
        by_contra hno
        push Not at hno
        have : (M.ends e).ncard ≤ ({w a} : Set α).ncard :=
          ncard_le_ncard (fun x hx ↦ hno x hx) (toFinite _)
        rw [hL.ends_ncard_eq_two he, ncard_singleton] at this
        omega
      have huQ : u ∈ Q.vertexSet := ⟨M.vertex_mem_of_inc hu, ((hwQ a ha).2.trans
        (SimpleGraph.Adj.reachable ⟨hua.symm, e, hinc, hu⟩))⟩
      obtain ⟨b, hb, rfl⟩ := hV ▸ huQ
      have hb' : b ≤ m := hb
      have hQinc : ∀ v, M.Inc e v → Q.Inc e v := fun v hv ↦ ⟨hv, w a, hinc, (hwQ a ha).2⟩
      have hab := (hadj a ha b hb).1 ⟨fun h ↦ hua h.symm, e, hQinc _ hinc, hQinc _ hu⟩
      have hdeg1 := no_parallel_edges_of_exists_deg_one
        (fun H hH hHne ↦ hL.exists_deg_one_of_le hH hHne)
      rcases hab with rfl | rfl
      · refine ⟨a, by omega, hdeg1 _ (hgM a (by omega)).1 e he ?_⟩
        rw [(hgM a (by omega)).2, hends e he _ _ (Ne.symm hua) hinc hu]
      · refine ⟨b, by omega, hdeg1 _ (hgM b (by omega)).1 e he ?_⟩
        rw [(hgM b (by omega)).2, hends e he _ _ hua hu hinc, pair_comm]
  · have hnoE : ∀ e ∈ M.edgeSet, ¬ M.Inc e y := fun e he hinc ↦
      hE ⟨e, hEQ e he y hinc (SimpleGraph.Reachable.refl _)⟩
    refine ⟨0, fun _ ↦ y, fun _ ↦ Classical.arbitrary β, ?_, rfl, hy, fun _ _ ↦
      SimpleGraph.Reachable.refl _, ?_, fun a ha ↦ absurd ha (Nat.not_lt_zero _), ?_⟩
    · intro a ha b hb _
      simp only [mem_Iic, Nat.le_zero] at ha hb
      rw [ha, hb]
    · intro x _ hr
      refine ⟨0, le_rfl, ?_⟩
      by_contra hxy
      obtain ⟨p⟩ := hr
      cases p with
      | nil => exact hxy rfl
      | cons hadj _ =>
        obtain ⟨-, e, he, -⟩ := hadj
        exact hnoE e (M.edge_mem_of_inc he) he
    · intro e he a _ hinc
      exact absurd hinc (hnoE e he)

/-- **Every set of `|Y|` disjoint paths between `Y` and `Z` is the union of a good family indexed
by `Y`, where the path of `y` starts at `y`.** -/
theorem exists_goodFam_of_isPathSystem [Nonempty α] [Nonempty β] {Y Z : Set α} (hYf : Y.Finite)
    (hM : IsPathSystem K Y Z Y.ncard M) :
    ∃ (c : α → ℕ → α) (n : α → ℕ) (f : α → ℕ → β), IsGoodFam K Y Z Y c n f ∧
      (∀ y ∈ Y, c y 0 = y) ∧ famGraph K Y c n f = M := by
  classical
  obtain ⟨hL, hk, hblk⟩ := hM
  have hex : ∀ P ∈ linkagePattern M, ∃ y ∈ Y, y ∈ P := fun P hP ↦ by
    obtain ⟨y, hy, z, -, rfl⟩ := hblk P hP
    exact ⟨y, hy, mem_insert _ _⟩
  choose! yP hyY hyP using hex
  have hinj : InjOn yP (linkagePattern M) := fun P hP Q hQ h ↦ by
    by_contra hne
    exact disjoint_left.1 (hL.disjoint_of_mem_linkagePattern hP hQ hne) (hyP P hP)
      (h ▸ hyP Q hQ)
  have himg : yP '' linkagePattern M = Y :=
    eq_of_subset_of_ncard_le (by rintro _ ⟨P, hP, rfl⟩; exact hyY P hP)
      (by rw [hinj.ncard_image, hk]) hYf
  have huniq : ∀ P ∈ linkagePattern M, ∀ y ∈ Y, y ∈ P → y = yP P := fun P hP y hy hyP' ↦ by
    rw [← himg] at hy
    obtain ⟨Q, hQ, rfl⟩ := hy
    by_cases hPQ : P = Q
    · rw [hPQ]
    · exact absurd (hyP Q hQ) (disjoint_left.1 (hL.disjoint_of_mem_linkagePattern hP hQ hPQ) hyP')
  have hpatR := linkagePattern_eq_image hL
  -- The block of `y` is `{y, z}` with `z ∈ Z`, and it holds every terminal reachable from `y`.
  have hblock : ∀ y ∈ Y, y ∈ terminals M ∧ ∃ z ∈ Z, z ∈ terminals M ∧
      M.skeleton.Reachable y z ∧ (∀ t ∈ terminals M, M.skeleton.Reachable y t → t = y ∨ t = z) ∧
      ∀ y' ∈ Y, y' ∈ terminals M → M.skeleton.Reachable y y' → y' = y := by
    intro y hy
    have hy' := hy
    rw [← himg] at hy'
    obtain ⟨P, hP, rfl⟩ := hy'
    have hP' := hP
    rw [hpatR] at hP'
    obtain ⟨t, ht, hPt⟩ := hP'
    beta_reduce at hPt
    have hyPt : yP P ∈ {t' ∈ terminals M | M.skeleton.Reachable t t'} := hPt ▸ hyP P hP
    obtain ⟨y₀, hy₀, z, hz, hPyz⟩ := hblk P hP
    have hy₀e : y₀ = yP P := huniq P hP y₀ hy₀ (hPyz ▸ mem_insert _ _)
    have hzP : z ∈ P := hPyz ▸ mem_insert_of_mem _ rfl
    have hzt : z ∈ {t' ∈ terminals M | M.skeleton.Reachable t t'} := hPt ▸ hzP
    refine ⟨hyPt.1, z, hz, hzt.1, hyPt.2.symm.trans hzt.2, fun t' ht' hr ↦ ?_,
      fun y' hy' ht' hr ↦ huniq P hP y' hy' (hPt ▸ ⟨ht', hyPt.2.trans hr⟩)⟩
    have : t' ∈ P := hPt ▸ ⟨ht', hyPt.2.trans hr⟩
    rw [hPyz, hy₀e] at this
    exact this
  have hseq : ∀ y ∈ Y, ∃ (m : ℕ) (w : ℕ → α) (g : ℕ → β), InjOn w (Iic m) ∧ w 0 = y ∧
      w m ∈ Z ∧ (∀ a ≤ m, M.skeleton.Reachable y (w a)) ∧
      (∀ x ∈ M.vertexSet, M.skeleton.Reachable y x → ∃ a ≤ m, w a = x) ∧
      (∀ a < m, g a ∈ M.edgeSet ∧ M.ends (g a) = {w a, w (a + 1)}) ∧
      (∀ e ∈ M.edgeSet, ∀ a ≤ m, M.Inc e (w a) → ∃ b < m, g b = e) := by
    intro y hy
    obtain ⟨hyT, z, hz, hzT, hyz, hT, -⟩ := hblock y hy
    obtain ⟨m, w, g, hinj, hw0, hwm, hr, hcov, hg, hgc⟩ := exists_seq_of_terminal hL hyT
    refine ⟨m, w, g, hinj, hw0, ?_, hr, hcov, hg, hgc⟩
    rcases hT _ hwm (hr m le_rfl) with h | h
    · obtain ⟨a, ha, rfl⟩ := hcov z hzT.1 hyz
      obtain rfl : m = 0 := by
        have := hinj (mem_Iic.2 le_rfl) (mem_Iic.2 (Nat.zero_le _))
          (h.trans hw0.symm)
        exact this
      obtain rfl : a = 0 := by omega
      rw [hw0] at hz ⊢
      exact hz
    · rw [h]; exact hz
  choose! n c f hinj hc0 hcn hr hcov hf hfc using hseq
  have hyV : ∀ y ∈ Y, y ∈ M.vertexSet := fun y hy ↦ (hblock y hy).1.1
  have hF : IsPathFam K Y c n f := by
    refine ⟨hinj, ?_, fun y hy a ha ↦ hL.1.vertexSet_subset
      (mem_vertexSet_of_reachable (hyV y hy) (hr y hy a ha)), fun y hy a ha ↦
      hL.1.edgeSet_subset (hf y hy a ha).1, fun y hy a ha ↦ ?_⟩
    · intro y hy y' hy' hne
      rw [disjoint_left]
      rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hx⟩
      have hr' : M.skeleton.Reachable y y' := (hr y hy a ha).trans
        (hx ▸ (hr y' hy' b hb).symm)
      obtain ⟨-, -, -, -, -, -, hY⟩ := hblock y hy
      exact hne (hY y' hy' (hblock y' hy').1 hr').symm
    · rw [hL.1.ends_eq _ (hf y hy a ha).1]
      exact (hf y hy a ha).2
  have hVcov : ∀ x ∈ M.vertexSet, ∃ y ∈ Y, ∃ a ≤ n y, c y a = x := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := exists_terminal_reachable hL hx
    have ht' := ht
    rw [hL.terminals_eq_sUnion_linkagePattern] at ht'
    obtain ⟨P, hP, htP⟩ := ht'
    have hP' := hP
    rw [hpatR] at hP'
    obtain ⟨t₀, -, hPt⟩ := hP'
    beta_reduce at hPt
    have h1 : yP P ∈ {t' ∈ terminals M | M.skeleton.Reachable t₀ t'} := hPt ▸ hyP P hP
    have h2 : t ∈ {t' ∈ terminals M | M.skeleton.Reachable t₀ t'} := hPt ▸ htP
    obtain ⟨a, ha, hax⟩ := hcov (yP P) (hyY P hP) x hx (h1.2.symm.trans (h2.2.trans hxt.symm))
    exact ⟨yP P, hyY P hP, a, ha, hax⟩
  refine ⟨c, n, f, ⟨hF, hYf, rfl, fun y hy ↦ ⟨(hc0 y hy).symm ▸ hy, hcn y hy⟩⟩, hc0, ?_⟩
  rw [← eq_subOn_of_le hL.1]
  have hV : famVerts Y c n = M.vertexSet := by
    ext x
    rw [mem_famVerts]
    constructor
    · rintro ⟨y, hy, a, ha, rfl⟩
      exact mem_vertexSet_of_reachable (hyV y hy) (hr y hy a ha)
    · exact hVcov x
  have hE : famEdges Y n f = M.edgeSet := by
    ext e
    rw [mem_famEdges]
    constructor
    · rintro ⟨y, hy, a, ha, rfl⟩
      exact (hf y hy a ha).1
    · intro he
      obtain ⟨u, hu⟩ : (M.ends e).Nonempty :=
        nonempty_of_ncard_ne_zero (by rw [hL.ends_ncard_eq_two he]; omega)
      obtain ⟨y, hy, a, ha, rfl⟩ := hVcov u (M.vertex_mem_of_inc hu)
      obtain ⟨b, hb, rfl⟩ := hfc y hy e he a ha hu
      exact ⟨y, hy, b, hb, rfl⟩
  unfold famGraph
  rw [hV, hE]

end Extract

/-! ## Changing one path of a family -/

section Ops

variable {K : Hypergraph α β} {I : Set ι} {c : ι → ℕ → α} {n : ι → ℕ} {f : ι → ℕ → β}

/-- Drop the first vertex and the first edge of the path of `i₀`. -/
noncomputable def shiftC (i₀ : ι) (c : ι → ℕ → α) : ι → ℕ → α := by
  classical exact fun i a ↦ if i = i₀ then c i (a + 1) else c i a

/-- The lengths after `shiftC`. -/
noncomputable def shiftN (i₀ : ι) (n : ι → ℕ) : ι → ℕ := by
  classical exact fun i ↦ if i = i₀ then n i - 1 else n i

/-- The edges after `shiftC`. -/
noncomputable def shiftF (i₀ : ι) (f : ι → ℕ → β) : ι → ℕ → β := by
  classical exact fun i a ↦ if i = i₀ then f i (a + 1) else f i a

/-- Put the vertex `v` and the edge `g` in front of the path of `i₀`. -/
noncomputable def extC (i₀ : ι) (v : α) (c : ι → ℕ → α) : ι → ℕ → α := by
  classical exact fun i a ↦ if i = i₀ then (if a = 0 then v else c i (a - 1)) else c i a

/-- The lengths after `extC`. -/
noncomputable def extN (i₀ : ι) (n : ι → ℕ) : ι → ℕ := by
  classical exact fun i ↦ if i = i₀ then n i + 1 else n i

/-- The edges after `extC`. -/
noncomputable def extF (i₀ : ι) (g : β) (f : ι → ℕ → β) : ι → ℕ → β := by
  classical exact fun i a ↦ if i = i₀ then (if a = 0 then g else f i (a - 1)) else f i a

section Simp

variable {i i₀ : ι} {a : ℕ} {v : α} {g : β}

@[simp] theorem shiftC_self : shiftC i₀ c i₀ a = c i₀ (a + 1) := by simp [shiftC]
@[simp] theorem shiftC_of_ne (h : i ≠ i₀) : shiftC i₀ c i a = c i a := by simp [shiftC, h]
@[simp] theorem shiftN_self : shiftN i₀ n i₀ = n i₀ - 1 := by simp [shiftN]
@[simp] theorem shiftN_of_ne (h : i ≠ i₀) : shiftN i₀ n i = n i := by simp [shiftN, h]
@[simp] theorem shiftF_self : shiftF i₀ f i₀ a = f i₀ (a + 1) := by simp [shiftF]
@[simp] theorem shiftF_of_ne (h : i ≠ i₀) : shiftF i₀ f i a = f i a := by simp [shiftF, h]
@[simp] theorem extC_self_zero : extC i₀ v c i₀ 0 = v := by simp [extC]
@[simp] theorem extC_self_succ : extC i₀ v c i₀ (a + 1) = c i₀ a := by simp [extC]
@[simp] theorem extC_of_ne (h : i ≠ i₀) : extC i₀ v c i a = c i a := by simp [extC, h]
@[simp] theorem extN_self : extN i₀ n i₀ = n i₀ + 1 := by simp [extN]
@[simp] theorem extN_of_ne (h : i ≠ i₀) : extN i₀ n i = n i := by simp [extN, h]
@[simp] theorem extF_self_zero : extF i₀ g f i₀ 0 = g := by simp [extF]
@[simp] theorem extF_self_succ : extF i₀ g f i₀ (a + 1) = f i₀ a := by simp [extF]
@[simp] theorem extF_of_ne (h : i ≠ i₀) : extF i₀ g f i a = f i a := by simp [extF, h]

end Simp

variable (hF : IsPathFam K I c n f)
include hF

/-- Edges of different paths, or at different places of one path, are different. -/
theorem IsPathFam.f_eq {i j : ι} (hi : i ∈ I) (hj : j ∈ I) {a b : ℕ} (ha : a < n i)
    (hb : b < n j) (h : f i a = f j b) : i = j ∧ a = b := by
  have h1 : c i a ∈ K.ends (f i a) := (hF.inc_iff hi ha).2 (Or.inl rfl)
  rw [h] at h1
  rcases (hF.inc_iff hj hb).1 h1 with h' | h'
  · obtain ⟨rfl, rfl⟩ := hF.eq_of_eq hi hj ha.le hb.le h'
    exact ⟨rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := hF.eq_of_eq hi hj ha.le hb h'
    exact absurd h (hF.f_ne hi ha hb (by omega))

/-- **Dropping the first vertex of a path.** -/
theorem IsPathFam.shift {i₀ : ι} (hi₀ : i₀ ∈ I) (hn : 1 ≤ n i₀) :
    IsPathFam K I (shiftC i₀ c) (shiftN i₀ n) (shiftF i₀ f) ∧
      famVerts I c n = insert (c i₀ 0) (famVerts I (shiftC i₀ c) (shiftN i₀ n)) ∧
      c i₀ 0 ∉ famVerts I (shiftC i₀ c) (shiftN i₀ n) ∧
      famEdges I n f = insert (f i₀ 0) (famEdges I (shiftN i₀ n) (shiftF i₀ f)) ∧
      f i₀ 0 ∉ famEdges I (shiftN i₀ n) (shiftF i₀ f) := by
  -- The vertices of the new path of `i` are old vertices of the path of `i`.
  have hV : ∀ i ∈ I, ∀ a ≤ shiftN i₀ n i, ∃ b ≤ n i, shiftC i₀ c i a = c i b ∧
      (i = i₀ → b = a + 1) ∧ (i ≠ i₀ → b = a) := fun i hi a ha ↦ by
    by_cases h : i = i₀
    · subst h; rw [shiftN_self] at ha
      exact ⟨a + 1, by omega, by rw [shiftC_self], fun _ ↦ rfl, fun h ↦ absurd rfl h⟩
    · rw [shiftN_of_ne h] at ha
      exact ⟨a, ha, by rw [shiftC_of_ne h], fun h' ↦ absurd h' h, fun _ ↦ rfl⟩
  have hNE : ∀ i ∈ I, ∀ a < shiftN i₀ n i, ∃ b < n i, shiftF i₀ f i a = f i b ∧
      shiftC i₀ c i a = c i b ∧ shiftC i₀ c i (a + 1) = c i (b + 1) ∧ (i = i₀ → b = a + 1) :=
    fun i hi a ha ↦ by
    by_cases h : i = i₀
    · subst h; rw [shiftN_self] at ha
      exact ⟨a + 1, by omega, by rw [shiftF_self], by rw [shiftC_self], by rw [shiftC_self],
        fun _ ↦ rfl⟩
    · rw [shiftN_of_ne h] at ha
      exact ⟨a, ha, by rw [shiftF_of_ne h], by rw [shiftC_of_ne h], by rw [shiftC_of_ne h],
        fun h' ↦ absurd h' h⟩
  refine ⟨⟨fun i hi a ha b hb hab ↦ ?_, fun i hi j hj hij ↦ ?_, fun i hi a ha ↦ ?_,
    fun i hi a ha ↦ ?_, fun i hi a ha ↦ ?_⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a', ha', hca, hai, hai'⟩ := hV i hi a ha
    obtain ⟨b', hb', hcb, hbi, hbi'⟩ := hV i hi b hb
    have := hF.inj i hi ha' hb' (hca.symm.trans (hab.trans hcb))
    by_cases h : i = i₀
    · have := hai h; have := hbi h; omega
    · have := hai' h; have := hbi' h; omega
  · rw [disjoint_left]
    rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hx⟩
    obtain ⟨a', ha', hca, -⟩ := hV i hi a ha
    obtain ⟨b', hb', hcb, -⟩ := hV j hj b hb
    exact hij (hF.eq_of_eq hi hj ha' hb' (hca.symm.trans (hx.symm.trans hcb))).1
  · obtain ⟨a', ha', hca, -⟩ := hV i hi a ha
    rw [hca]; exact hF.mem i hi a' ha'
  · obtain ⟨b, hb, hfb, -⟩ := hNE i hi a ha
    rw [hfb]; exact hF.edge_mem i hi b hb
  · obtain ⟨b, hb, hfb, hc1, hc2, -⟩ := hNE i hi a ha
    rw [hfb, hc1, hc2]; exact hF.ends i hi b hb
  · ext x
    simp only [mem_insert_iff, mem_famVerts]
    constructor
    · rintro ⟨i, hi, a, ha, rfl⟩
      by_cases h : i = i₀
      · subst h
        rcases Nat.eq_zero_or_pos a with rfl | hpos
        · exact Or.inl rfl
        · right
          refine ⟨i, hi, a - 1, by rw [shiftN_self]; omega, ?_⟩
          rw [shiftC_self, Nat.sub_add_cancel hpos]
      · exact Or.inr ⟨i, hi, a, by rw [shiftN_of_ne h]; exact ha, by rw [shiftC_of_ne h]⟩
    · rintro (rfl | ⟨i, hi, a, ha, rfl⟩)
      · exact ⟨i₀, hi₀, 0, Nat.zero_le _, rfl⟩
      · obtain ⟨b, hb, hcb, -⟩ := hV i hi a ha
        exact ⟨i, hi, b, hb, hcb.symm⟩
  · rw [mem_famVerts]
    rintro ⟨i, hi, a, ha, hx⟩
    obtain ⟨b, hb, hcb, hbi, hbi'⟩ := hV i hi a ha
    obtain ⟨rfl, rfl⟩ := hF.eq_of_eq hi hi₀ hb (Nat.zero_le _) (hcb.symm.trans hx)
    have := hbi rfl
    omega
  · ext x
    simp only [mem_insert_iff, mem_famEdges]
    constructor
    · rintro ⟨i, hi, a, ha, rfl⟩
      by_cases h : i = i₀
      · subst h
        rcases Nat.eq_zero_or_pos a with rfl | hpos
        · exact Or.inl rfl
        · right
          refine ⟨i, hi, a - 1, by rw [shiftN_self]; omega, ?_⟩
          rw [shiftF_self, Nat.sub_add_cancel hpos]
      · exact Or.inr ⟨i, hi, a, by rw [shiftN_of_ne h]; exact ha, by rw [shiftF_of_ne h]⟩
    · rintro (rfl | ⟨i, hi, a, ha, rfl⟩)
      · exact ⟨i₀, hi₀, 0, hn, rfl⟩
      · obtain ⟨b, hb, hfb, -⟩ := hNE i hi a ha
        exact ⟨i, hi, b, hb, hfb.symm⟩
  · rw [mem_famEdges]
    rintro ⟨i, hi, a, ha, hx⟩
    obtain ⟨b, hb, hfb, -, -, hbi⟩ := hNE i hi a ha
    obtain ⟨rfl, rfl⟩ := hF.f_eq hi hi₀ hb hn (hfb.symm.trans hx)
    have := hbi rfl
    omega

/-- **Putting a new vertex and edge in front of a path.** -/
theorem IsPathFam.extend {i₀ : ι} (hi₀ : i₀ ∈ I) {v : α} {g : β} (hv : v ∈ K.vertexSet)
    (hvF : v ∉ famVerts I c n) (hg : g ∈ K.edgeSet) (hge : K.ends g = {v, c i₀ 0}) :
    IsPathFam K I (extC i₀ v c) (extN i₀ n) (extF i₀ g f) ∧
      famVerts I (extC i₀ v c) (extN i₀ n) = insert v (famVerts I c n) ∧
      famEdges I (extN i₀ n) (extF i₀ g f) = insert g (famEdges I n f) := by
  have hvne : ∀ i ∈ I, ∀ a ≤ n i, c i a ≠ v := fun i hi a ha h ↦
    hvF (mem_famVerts.2 ⟨i, hi, a, ha, h⟩)
  -- The new path of `i` is the old one, with `v` in front when `i = i₀`.
  have hV : ∀ i ∈ I, ∀ a ≤ extN i₀ n i, (i = i₀ ∧ a = 0 ∧ extC i₀ v c i a = v) ∨
      ∃ b ≤ n i, extC i₀ v c i a = c i b ∧ (i = i₀ → a = b + 1) ∧ (i ≠ i₀ → a = b) :=
    fun i hi a ha ↦ by
    by_cases h : i = i₀
    · subst h; rw [extN_self] at ha
      rcases a with _ | a
      · exact Or.inl ⟨rfl, rfl, extC_self_zero⟩
      · exact Or.inr ⟨a, by omega, extC_self_succ, fun _ ↦ rfl, fun h ↦ absurd rfl h⟩
    · rw [extN_of_ne h] at ha
      exact Or.inr ⟨a, ha, extC_of_ne h, fun h' ↦ absurd h' h, fun _ ↦ rfl⟩
  have hNE : ∀ i ∈ I, ∀ a < extN i₀ n i, (i = i₀ ∧ a = 0) ∨ ∃ b < n i,
      extF i₀ g f i a = f i b ∧ extC i₀ v c i a = c i b ∧ extC i₀ v c i (a + 1) = c i (b + 1) :=
    fun i hi a ha ↦ by
    by_cases h : i = i₀
    · subst h; rw [extN_self] at ha
      rcases a with _ | a
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨a, by omega, extF_self_succ, extC_self_succ, extC_self_succ⟩
    · rw [extN_of_ne h] at ha
      exact Or.inr ⟨a, ha, extF_of_ne h, extC_of_ne h, extC_of_ne h⟩
  refine ⟨⟨fun i hi a ha b hb hab ↦ ?_, fun i hi j hj hij ↦ ?_, fun i hi a ha ↦ ?_,
    fun i hi a ha ↦ ?_, fun i hi a ha ↦ ?_⟩, ?_, ?_⟩
  · rcases hV i hi a ha with ⟨rfl, rfl, hva⟩ | ⟨a', ha', hca, hai, hai'⟩ <;>
      rcases hV i hi b hb with ⟨-, rfl, hvb⟩ | ⟨b', hb', hcb, hbi, hbi'⟩
    · rfl
    · exact absurd (hcb.symm.trans (hab.symm.trans hva)) (hvne _ hi _ hb')
    · exact absurd (hca.symm.trans (hab.trans hvb)) (hvne _ hi _ ha')
    · have := hF.inj i hi ha' hb' (hca.symm.trans (hab.trans hcb))
      by_cases h : i = i₀
      · have := hai h; have := hbi h; omega
      · have := hai' h; have := hbi' h; omega
  · rw [disjoint_left]
    rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hx⟩
    rcases hV i hi a ha with ⟨rfl, -, hva⟩ | ⟨a', ha', hca, -⟩ <;>
      rcases hV j hj b hb with ⟨rfl, -, hvb⟩ | ⟨b', hb', hcb, -⟩
    · exact hij rfl
    · exact hvne _ hj _ hb' (hcb.symm.trans (hx.trans hva))
    · exact hvne _ hi _ ha' (hca.symm.trans (hx.symm.trans hvb))
    · exact hij (hF.eq_of_eq hi hj ha' hb' (hca.symm.trans (hx.symm.trans hcb))).1
  · rcases hV i hi a ha with ⟨-, -, hva⟩ | ⟨a', ha', hca, -⟩
    · rw [hva]; exact hv
    · rw [hca]; exact hF.mem i hi a' ha'
  · rcases hNE i hi a ha with ⟨rfl, rfl⟩ | ⟨b, hb, hfb, -⟩
    · rw [extF_self_zero]; exact hg
    · rw [hfb]; exact hF.edge_mem i hi b hb
  · rcases hNE i hi a ha with ⟨rfl, rfl⟩ | ⟨b, hb, hfb, hc1, hc2⟩
    · rw [extF_self_zero, extC_self_zero, zero_add, extC_self_succ]; exact hge
    · rw [hfb, hc1, hc2]; exact hF.ends i hi b hb
  · ext x
    simp only [mem_insert_iff, mem_famVerts]
    constructor
    · rintro ⟨i, hi, a, ha, rfl⟩
      rcases hV i hi a ha with ⟨-, -, hva⟩ | ⟨b, hb, hcb, -⟩
      · exact Or.inl hva
      · exact Or.inr ⟨i, hi, b, hb, hcb.symm⟩
    · rintro (rfl | ⟨i, hi, a, ha, rfl⟩)
      · exact ⟨i₀, hi₀, 0, Nat.zero_le _, extC_self_zero⟩
      · by_cases h : i = i₀
        · subst h
          exact ⟨i, hi, a + 1, by rw [extN_self]; omega, extC_self_succ⟩
        · exact ⟨i, hi, a, by rw [extN_of_ne h]; exact ha, extC_of_ne h⟩
  · ext x
    simp only [mem_insert_iff, mem_famEdges]
    constructor
    · rintro ⟨i, hi, a, ha, rfl⟩
      rcases hNE i hi a ha with ⟨rfl, rfl⟩ | ⟨b, hb, hfb, -⟩
      · exact Or.inl extF_self_zero
      · exact Or.inr ⟨i, hi, b, hb, hfb.symm⟩
    · rintro (rfl | ⟨i, hi, a, ha, rfl⟩)
      · exact ⟨i₀, hi₀, 0, by rw [extN_self]; omega, extF_self_zero⟩
      · by_cases h : i = i₀
        · subst h
          exact ⟨i, hi, a + 1, by rw [extN_self]; omega, extF_self_succ⟩
        · exact ⟨i, hi, a, by rw [extN_of_ne h]; exact ha, extF_of_ne h⟩

end Ops

/-! ## Rerouting along a cycle of jumps -/

section Reroute

variable {K : Hypergraph α β} {I : Set ι} {c : ι → ℕ → α} {n : ι → ℕ} {f : ι → ℕ → β}

/-- For `i ∈ C`, the new path of `i` starts at `c i 0`, uses the edge `e i` to the vertex at place
`p i` of the path of `nxt i`, and then follows that path to its end. -/
noncomputable def rrC (C : Set ι) (nxt : ι → ι) (p : ι → ℕ) (c : ι → ℕ → α) : ι → ℕ → α := by
  classical exact fun i a ↦
    if i ∈ C then (if a = 0 then c i 0 else c (nxt i) (p i + a - 1)) else c i a

/-- The lengths after `rrC`. -/
noncomputable def rrN (C : Set ι) (nxt : ι → ι) (p : ι → ℕ) (n : ι → ℕ) : ι → ℕ := by
  classical exact fun i ↦ if i ∈ C then n (nxt i) - p i + 1 else n i

/-- The edges after `rrC`. -/
noncomputable def rrF (C : Set ι) (nxt : ι → ι) (p : ι → ℕ) (e : ι → β) (f : ι → ℕ → β) :
    ι → ℕ → β := by
  classical exact fun i a ↦
    if i ∈ C then (if a = 0 then e i else f (nxt i) (p i + a - 1)) else f i a

/-- **Rerouting.** If `nxt` is one-to-one on `C` and maps `C` into `C`, and for `i ∈ C` the edge
`e i` joins `c i 0` to the vertex at place `p i ≥ 1` of the path of `nxt i`, then the rerouted
paths are again disjoint. -/
theorem IsPathFam.reroute (hF : IsPathFam K I c n f) {C : Set ι} (hCI : C ⊆ I) {nxt : ι → ι}
    (hnC : ∀ i ∈ C, nxt i ∈ C) (hinj : InjOn nxt C) {p : ι → ℕ}
    (hp : ∀ i ∈ C, 1 ≤ p i ∧ p i ≤ n (nxt i)) {e : ι → β}
    (he : ∀ i ∈ C, e i ∈ K.edgeSet ∧ K.ends (e i) = {c i 0, c (nxt i) (p i)}) :
    IsPathFam K I (rrC C nxt p c) (rrN C nxt p n) (rrF C nxt p e f) := by
  classical
  -- The vertices of the new path of `i`.
  have hV : ∀ i ∈ I, ∀ a ≤ rrN C nxt p n i,
      (i ∈ C ∧ a = 0 ∧ rrC C nxt p c i a = c i 0) ∨
      (i ∈ C ∧ 1 ≤ a ∧ p i + a - 1 ≤ n (nxt i) ∧ rrC C nxt p c i a = c (nxt i) (p i + a - 1)) ∨
      (i ∉ C ∧ a ≤ n i ∧ rrC C nxt p c i a = c i a) := fun i hi a ha ↦ by
    by_cases h : i ∈ C
    · simp only [rrN, h, ite_true] at ha
      have := hp i h
      rcases Nat.eq_zero_or_pos a with rfl | hpos
      · exact Or.inl ⟨h, rfl, by simp [rrC, h]⟩
      · exact Or.inr (Or.inl ⟨h, hpos, by omega, by simp [rrC, h, hpos.ne']⟩)
    · simp only [rrN, h, ite_false] at ha
      exact Or.inr (Or.inr ⟨h, ha, by simp [rrC, h]⟩)
  refine ⟨fun i hi a ha b hb hab ↦ ?_, fun i hi j hj hij ↦ ?_, fun i hi a ha ↦ ?_,
    fun i hi a ha ↦ ?_, fun i hi a ha ↦ ?_⟩
  · by_cases hC : i ∈ C
    · have hni := hCI (hnC i hC)
      have hpi := (hp i hC).1
      rcases hV i hi a ha with ⟨-, rfl, h1⟩ | ⟨-, h0, hle, h1⟩ | ⟨hC', -⟩
      · rcases hV i hi b hb with ⟨-, rfl, h2⟩ | ⟨-, h0', hle', h2⟩ | ⟨hC', -⟩
        · rfl
        · have := (hF.eq_of_eq hi hni (Nat.zero_le _) hle' (h1.symm.trans (hab.trans h2))).2
          omega
        · exact absurd hC hC'
      · rcases hV i hi b hb with ⟨-, rfl, h2⟩ | ⟨-, h0', hle', h2⟩ | ⟨hC', -⟩
        · have := (hF.eq_of_eq hi hni (Nat.zero_le _) hle
            (h2.symm.trans (hab.symm.trans h1))).2
          omega
        · have := hF.inj _ hni hle hle' (h1.symm.trans (hab.trans h2))
          omega
        · exact absurd hC hC'
      · exact absurd hC hC'
    · rcases hV i hi a ha with ⟨hC', -⟩ | ⟨hC', -⟩ | ⟨-, hle, h1⟩
      · exact absurd hC' hC
      · exact absurd hC' hC
      · rcases hV i hi b hb with ⟨hC', -⟩ | ⟨hC', -⟩ | ⟨-, hle', h2⟩
        · exact absurd hC' hC
        · exact absurd hC' hC
        · exact hF.inj i hi hle hle' (h1.symm.trans (hab.trans h2))
  · rw [disjoint_left]
    rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hx⟩
    have hni : ∀ i ∈ C, nxt i ∈ I := fun i h ↦ hCI (hnC i h)
    rcases hV i hi a ha with ⟨hC, -, h1⟩ | ⟨hC, h0, hle, h1⟩ | ⟨hC, hle, h1⟩ <;>
      rcases hV j hj b hb with ⟨hC', -, h2⟩ | ⟨hC', h0', hle', h2⟩ | ⟨hC', hle', h2⟩
    · exact hij (hF.eq_of_eq hi hj (Nat.zero_le _) (Nat.zero_le _) (h1.symm.trans (hx.symm.trans h2))).1
    · have := (hF.eq_of_eq hi (hni j hC') (Nat.zero_le _) hle'
        (h1.symm.trans (hx.symm.trans h2))).2
      have := (hp j hC').1
      omega
    · exact hij (hF.eq_of_eq hi hj (Nat.zero_le _) hle' (h1.symm.trans (hx.symm.trans h2))).1
    · have := (hF.eq_of_eq hj (hni i hC) (Nat.zero_le _) hle
        (h2.symm.trans (hx.trans h1))).2
      have := (hp i hC).1
      omega
    · exact hij (hinj hC hC' (hF.eq_of_eq (hni i hC) (hni j hC') hle hle'
        (h1.symm.trans (hx.symm.trans h2))).1)
    · exact hC' ((hF.eq_of_eq (hni i hC) hj hle hle' (h1.symm.trans (hx.symm.trans h2))).1 ▸
        hnC i hC)
    · exact hij (hF.eq_of_eq hi hj hle (Nat.zero_le _) (h1.symm.trans (hx.symm.trans h2))).1
    · exact hC ((hF.eq_of_eq hi (hni j hC') hle hle' (h1.symm.trans (hx.symm.trans h2))).1.symm ▸
        hnC j hC')
    · exact disjoint_left.1 (hF.disj i hi j hj hij) ⟨a, hle, h1.symm⟩ ⟨b, hle', h2.symm.trans hx⟩
  · rcases hV i hi a ha with ⟨-, -, h1⟩ | ⟨hC, -, hle, h1⟩ | ⟨-, hle, h1⟩
    · rw [h1]; exact hF.mem i hi 0 (Nat.zero_le _)
    · rw [h1]; exact hF.mem _ (hCI (hnC i hC)) _ hle
    · rw [h1]; exact hF.mem i hi a hle
  · by_cases h : i ∈ C
    · simp only [rrF, h, ite_true]
      split_ifs with ha0
      · exact (he i h).1
      · simp only [rrN, h, ite_true] at ha
        exact hF.edge_mem _ (hCI (hnC i h)) _ (by have := hp i h; omega)
    · simp only [rrF, h, ite_false]
      simp only [rrN, h, ite_false] at ha
      exact hF.edge_mem i hi a ha
  · by_cases h : i ∈ C
    · simp only [rrN, h, ite_true] at ha
      have hpi := hp i h
      simp only [rrF, rrC, h, ite_true, Nat.add_one_ne_zero, ite_false]
      split_ifs with ha0
      · subst ha0
        rw [(he i h).2]
        simp
      · rw [hF.ends (nxt i) (hCI (hnC i h)) (p i + a - 1) (by omega),
          show p i + (a + 1) - 1 = p i + a - 1 + 1 by omega]
    · simp only [rrN, h, ite_false] at ha
      simp only [rrF, rrC, h, ite_false]
      exact hF.ends i hi a ha

end Reroute

end GM21
end GraphMinor
