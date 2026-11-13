module

public import GraphMinor.LRPlanarity.SolverInvariants

/-!
# Subtree, Branch, and Prefix Formulas for the Postorder Solver (Part II)

This module defines the back-edge sets (`subtreeBackEdges`, `branchBackEdges`,
`allReturnsAt`, `minDepthSet`) and logical formulas (`VertexConstraint`,
`SubtreeFormula`, `BranchFormula`, `PrefFormula`, `CrossConstraint`) used in
`GraphMinor/LRPlanarity/Solver.lean` to prove `SolverStatement`.
-/

@[expose] public section
namespace GraphMinor.LRPlanarity

open Classical

/-! ## Lowpoint and `ForkPair` Helper Lemmas -/

theorem Forest.low_le_depth {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N)) (e : Arc N) :
    T.low G e ≤ T.depth e.1 := by
  unfold Forest.low
  exact Finset.min'_le _ (T.depth e.1) (by simp)

theorem Forest.low_le_of_mem_returns {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    {e b : Arc N} (hb : b ∈ T.returns G e) :
    T.low G e ≤ T.depth b.2 := by
  unfold Forest.low
  apply Finset.min'_le
  rw [Finset.mem_insert, Finset.mem_image]
  exact Or.inr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩, rfl⟩

theorem ForkPair.symm {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    {color : Coloring N} {e f : Arc N} (h : ForkPair T G color e f) :
    ForkPair T G color f e :=
  ⟨h.2.1, h.1, fun b hb c hc => (h.2.2 c hc b hb).symm⟩

/-! ## `subtreeBackEdges`, `branchBackEdges`, `allReturnsAt`, and `minDepthSet` -/

/-- All back edges originating in the subtree of `v`. -/
def Forest.subtreeBackEdges {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (v : Fin N) : Set (Arc N) :=
  {b | T.BackEdge G b ∧ T.Ancestor v b.1}

/-- All back edges in the branch of an outgoing edge `e`. -/
def Forest.branchBackEdges {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (e : Arc N) : Set (Arc N) :=
  {b | T.BackEdge G b ∧
    ((T.BackEdge G e ∧ b = e) ∨ (T.TreeEdge e ∧ T.Ancestor e.2 b.1))}

/-- All return edges strictly above `v` originating in the subtree of `v`. -/
def Forest.allReturnsAt {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (v : Fin N) : Set (Arc N) :=
  {b | T.BackEdge G b ∧ T.Ancestor v b.1 ∧ T.depth b.2 < T.depth v}

/-- The subset of `S` attaining the minimum target depth in `S`. -/
def Forest.minDepthSet {N : ℕ} (T : Forest N) (S : Set (Arc N)) : Set (Arc N) :=
  {b | b ∈ S ∧ ∀ b' ∈ S, T.depth b.2 ≤ T.depth b'.2}

theorem Forest.ancestor_cases_head {N : ℕ} {T : Forest N} {u v : Fin N} :
    T.Ancestor u v ↔ u = v ∨ ∃ w : Fin N, T.TreeEdge (u, w) ∧ T.Ancestor w v := by
  constructor
  · intro hanc
    induction hanc with
    | refl => exact Or.inl rfl
    | @tail p x _ hp ih =>
      rcases ih with rfl | ⟨w, hte, hanc_w⟩
      · exact Or.inr ⟨x, hp, Relation.ReflTransGen.refl⟩
      · exact Or.inr ⟨w, hte, Relation.ReflTransGen.tail hanc_w hp⟩
  · rintro (rfl | ⟨w, hte, hanc_w⟩)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head hte hanc_w

theorem Forest.returns_sub_branchBackEdges {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (e : Arc N) :
    T.returns G e ⊆ T.branchBackEdges G e := by
  intro b hb
  rcases hb with ⟨hbe, h1 | ⟨hte, hanc, _⟩⟩
  · exact ⟨hbe, Or.inl h1⟩
  · exact ⟨hbe, Or.inr ⟨hte, hanc⟩⟩

theorem Forest.branchBackEdges_sub_subtreeBackEdges {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    {v : Fin N} {e : Arc N} (he : T.Outgoing G v e) :
    T.branchBackEdges G e ⊆ T.subtreeBackEdges G v := by
  intro b hb
  rcases hb with ⟨hbe, ⟨_, rfl⟩ | ⟨hte, hanc⟩⟩
  · exact ⟨hbe, he.1 ▸ Relation.ReflTransGen.refl⟩
  · have hvw : T.Ancestor v e.2 :=
      Relation.ReflTransGen.head (he.1 ▸ hte) Relation.ReflTransGen.refl
    exact ⟨hbe, hvw.trans hanc⟩

theorem Forest.branchBackEdges_eq_subtreeBackEdges_of_treeEdge {N : ℕ}
    {G : SimpleGraph (Fin N)} {T : Forest N} (hDFS : T.IsDFS G)
    {u v : Fin N} (hte : T.TreeEdge (u, v)) :
    T.branchBackEdges G (u, v) = T.subtreeBackEdges G v := by
  ext b
  simp only [Forest.branchBackEdges, Forest.subtreeBackEdges, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hbe, ⟨hback, _⟩ | ⟨_, hanc⟩⟩
    · have hstep := T.depth_step_of_isDFS hDFS u v hte
      have hlt : T.depth v < T.depth u := hback.2.2.1
      omega
    · exact ⟨hbe, hanc⟩
  · rintro ⟨hbe, hanc⟩
    exact ⟨hbe, Or.inr ⟨hte, hanc⟩⟩

theorem Forest.branchBackEdges_disjoint {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) {v : Fin N} {e f : Arc N}
    (he : T.Outgoing G v e) (hf : T.Outgoing G v f) (hne : e ≠ f) :
    Disjoint (T.branchBackEdges G e) (T.branchBackEdges G f) := by
  rw [Set.disjoint_left]
  intro b hbe hbf
  rcases hbe with ⟨_, ⟨_, rfl⟩ | ⟨hte_e, hanc_e⟩⟩ <;>
    rcases hbf with ⟨_, ⟨_, hbf_eq⟩ | ⟨hte_f, hanc_f⟩⟩
  · exact hne hbf_eq
  · have hstep : T.depth f.2 = T.depth v + 1 :=
      hf.1 ▸ T.depth_step_of_isDFS hDFS f.1 f.2 hte_f
    have hle : T.depth f.2 ≤ T.depth v :=
      he.1 ▸ T.depth_le_of_ancestor_of_isDFS hDFS hanc_f
    omega
  · subst hbf_eq
    have hstep : T.depth e.2 = T.depth v + 1 :=
      he.1 ▸ T.depth_step_of_isDFS hDFS e.1 e.2 hte_e
    have hle : T.depth e.2 ≤ T.depth v :=
      hf.1 ▸ T.depth_le_of_ancestor_of_isDFS hDFS hanc_e
    omega
  · have hde : T.depth e.2 = T.depth v + 1 :=
      he.1 ▸ T.depth_step_of_isDFS hDFS e.1 e.2 hte_e
    have hdf : T.depth f.2 = T.depth v + 1 :=
      hf.1 ▸ T.depth_step_of_isDFS hDFS f.1 f.2 hte_f
    have he2_eq_f2 : e.2 = f.2 :=
      T.eq_of_ancestor_of_depth_eq hDFS hanc_e hanc_f (hde.trans hdf.symm)
    apply hne
    ext
    · rw [he.1, hf.1]
    · exact congrArg Fin.val he2_eq_f2

theorem Forest.returns_disjoint {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) {v : Fin N} {e f : Arc N}
    (he : T.Outgoing G v e) (hf : T.Outgoing G v f) (hne : e ≠ f) :
    Disjoint (T.returns G e) (T.returns G f) :=
  (T.branchBackEdges_disjoint hDFS he hf hne).mono
    (T.returns_sub_branchBackEdges G e) (T.returns_sub_branchBackEdges G f)

theorem Forest.allReturnsAt_eq_biUnion {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (v : Fin N) :
    T.allReturnsAt G v = {b | ∃ e, T.Outgoing G v e ∧ b ∈ T.returns G e} := by
  ext b
  simp only [Forest.allReturnsAt, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hbe, hanc, hd_lt⟩
    rcases T.ancestor_cases_head.mp hanc with hvb | ⟨w, hte, hanc_w⟩
    · subst hvb
      exact ⟨b, ⟨rfl, Or.inr hbe⟩, hbe, Or.inl ⟨hbe, rfl⟩⟩
    · exact ⟨(v, w), ⟨rfl, Or.inl hte⟩, hbe, Or.inr ⟨hte, hanc_w, hd_lt⟩⟩
  · rintro ⟨e, he, hb⟩
    have hsub := T.branchBackEdges_sub_subtreeBackEdges G he (T.returns_sub_branchBackEdges G e hb)
    have hd_lt : T.depth b.2 < T.depth v := he.1 ▸ T.returns_depth_lt G e b hb
    exact ⟨hsub.1, hsub.2, hd_lt⟩

theorem Forest.allReturnsAt_eq_empty_of_root {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) {v : Fin N} (hroot : T.parent v = none) :
    T.allReturnsAt G v = ∅ := by
  have hd0 : T.depth v = 0 := hDFS.1 v hroot
  ext b
  simp [Forest.allReturnsAt, hd0]

theorem Forest.allReturnsAt_eq_weakReturns_of_treeEdge {N : ℕ} {G : SimpleGraph (Fin N)}
    {T : Forest N} (hDFS : T.IsDFS G) {u v : Fin N} (hte : T.TreeEdge (u, v)) :
    T.allReturnsAt G v = T.weakReturns G (u, v) := by
  have hstep : T.depth v = T.depth u + 1 := T.depth_step_of_isDFS hDFS u v hte
  ext b
  simp only [Forest.allReturnsAt, Forest.weakReturns, Set.mem_ofPred_eq, hstep]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by omega⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by omega⟩⟩

theorem Forest.returns_treeEdge_eq_filter_allReturnsAt {N : ℕ} {G : SimpleGraph (Fin N)}
    {T : Forest N} (hDFS : T.IsDFS G) {u v : Fin N} (hte : T.TreeEdge (u, v)) :
    T.returns G (u, v) = {b | b ∈ T.allReturnsAt G v ∧ T.depth b.2 < T.depth u} := by
  have hstep : T.depth v = T.depth u + 1 := T.depth_step_of_isDFS hDFS u v hte
  ext b
  simp only [Forest.returns, Forest.allReturnsAt, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hbe, ⟨hback, _⟩ | ⟨_, hanc, hd_lt⟩⟩
    · have hlt : T.depth v < T.depth u := hback.2.2.1
      omega
    · exact ⟨⟨hbe, hanc, by omega⟩, hd_lt⟩
  · rintro ⟨⟨hbe, hanc, _⟩, hd_lt⟩
    exact ⟨hbe, Or.inr ⟨hte, hanc, hd_lt⟩⟩

/-! ## `VertexConstraint`, `SubtreeFormula`, and Gluing Root Colorings -/

/-- Local constraint at a single vertex `v`: all pairs of distinct outgoing
edges satisfy `ForkPair`, and the minimum-depth return edges in `allReturnsAt G v`
are monochromatic. -/
def Forest.VertexConstraint {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (v : Fin N) (color : Coloring N) : Prop :=
  (∀ e f, T.Outgoing G v e → T.Outgoing G v f → e ≠ f → ForkPair T G color e f) ∧
  Monochromatic color (T.minDepthSet (T.allReturnsAt G v))

/-- Complete constraint formula for the subtree rooted at `v`. -/
def Forest.SubtreeFormula {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (v : Fin N) (color : Coloring N) : Prop :=
  ∀ x : Fin N, T.Ancestor v x → T.VertexConstraint G x color

theorem Forest.fork_and_align_iff_forall_vertexConstraint {N : ℕ}
    {G : SimpleGraph (Fin N)} {T : Forest N} (hDFS : T.IsDFS G) (color : Coloring N) :
    (T.ForkConstraints G color ∧ T.WeakAlignment G color) ↔
      ∀ v : Fin N, T.VertexConstraint G v color := by
  constructor
  · rintro ⟨hfork, halign⟩ v
    refine ⟨fun e f he hf hne => hfork v e f he hf hne, ?_⟩
    rcases hp : T.parent v with _ | u
    · rw [T.allReturnsAt_eq_empty_of_root hDFS hp]
      intro b hb
      simp [Forest.minDepthSet] at hb
    · rw [T.allReturnsAt_eq_weakReturns_of_treeEdge hDFS hp]
      exact halign (u, v) hp
  · intro hall
    refine ⟨fun v e f he hf hne => (hall v).1 e f he hf hne, ?_⟩
    intro ⟨u, v⟩ hte
    rw [← T.allReturnsAt_eq_weakReturns_of_treeEdge hDFS hte]
    exact (hall v).2

theorem Forest.subtreeFormula_iff {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (v : Fin N) (color : Coloring N) :
    T.SubtreeFormula G v color ↔
      T.VertexConstraint G v color ∧
      ∀ w : Fin N, T.TreeEdge (v, w) → T.SubtreeFormula G w color := by
  constructor
  · intro hsub
    refine ⟨hsub v Relation.ReflTransGen.refl, ?_⟩
    intro w hte x hanc_wx
    exact hsub x (Relation.ReflTransGen.head hte hanc_wx)
  · rintro ⟨hvc, hchildren⟩ x hanc_vx
    rcases T.ancestor_cases_head.mp hanc_vx with rfl | ⟨w, hte, hanc_wx⟩
    · exact hvc
    · exact hchildren w hte x hanc_wx

theorem Forest.vertexConstraint_congr {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    {v : Fin N} {c₁ c₂ : Coloring N}
    (heq : ∀ b ∈ T.subtreeBackEdges G v, c₁ b = c₂ b) :
    T.VertexConstraint G v c₁ → T.VertexConstraint G v c₂ := by
  rintro ⟨hfork, halign⟩
  have hfork_sub : ∀ {e f}, T.Outgoing G v e → T.forkSet G e f ⊆ T.subtreeBackEdges G v := by
    intro e f he b hb
    exact T.branchBackEdges_sub_subtreeBackEdges G he (T.returns_sub_branchBackEdges G e hb.1)
  refine ⟨fun e f he hf hne => ?_, ?_⟩
  · have hpair := hfork e f he hf hne
    refine ⟨hpair.1.congr_on (fun b hb => heq b (hfork_sub he hb)),
      hpair.2.1.congr_on (fun b hb => heq b (hfork_sub hf hb)), ?_⟩
    intro b hb c hc
    rw [← heq b (hfork_sub he hb), ← heq c (hfork_sub hf hc)]
    exact hpair.2.2 b hb c hc
  · refine halign.congr_on (fun b hb => heq b ?_)
    exact ⟨hb.1.1, hb.1.2.1⟩

theorem Forest.subtreeFormula_congr {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    {v : Fin N} {c₁ c₂ : Coloring N}
    (heq : ∀ b ∈ T.subtreeBackEdges G v, c₁ b = c₂ b) :
    T.SubtreeFormula G v c₁ → T.SubtreeFormula G v c₂ := by
  intro hsub x hanc_vx
  refine T.vertexConstraint_congr (fun b hb => heq b ?_) (hsub x hanc_vx)
  exact ⟨hb.1, hanc_vx.trans hb.2⟩

theorem Forest.exists_global_of_roots {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G)
    (hroots : ∀ r : Fin N, T.parent r = none → ∃ color, T.SubtreeFormula G r color) :
    ∃ color, T.ForkConstraints G color ∧ T.WeakAlignment G color := by
  let rootOf (v : Fin N) : Fin N := Classical.choose (T.exists_root_ancestor hDFS v)
  have hrootOf (v : Fin N) : T.parent (rootOf v) = none ∧ T.Ancestor (rootOf v) v :=
    Classical.choose_spec (T.exists_root_ancestor hDFS v)
  let colOf (r : Fin N) : Coloring N :=
    if hr : T.parent r = none then Classical.choose (hroots r hr) else fun _ => .left
  have hcolOf (r : Fin N) (hr : T.parent r = none) : T.SubtreeFormula G r (colOf r) := by
    simp only [colOf, hr, ↓reduceDIte]
    exact Classical.choose_spec (hroots r hr)
  let color : Coloring N := fun b => colOf (rootOf b.1) b
  refine ⟨color, (T.fork_and_align_iff_forall_vertexConstraint hDFS color).mpr ?_⟩
  intro x
  have hsub_r : T.SubtreeFormula G (rootOf x) (colOf (rootOf x)) :=
    hcolOf (rootOf x) (hrootOf x).1
  have hvc_r : T.VertexConstraint G x (colOf (rootOf x)) :=
    hsub_r x (hrootOf x).2
  refine T.vertexConstraint_congr (fun b hb => ?_) hvc_r
  dsimp [color]
  have hanc_rb : T.Ancestor (rootOf x) b.1 := (hrootOf x).2.trans hb.2
  have heq_root : rootOf b.1 = rootOf x :=
    T.root_ancestor_unique hDFS (hrootOf b.1).1 (hrootOf x).1 (hrootOf b.1).2 hanc_rb
  rw [heq_root]

/-! ## `BranchFormula`, `PrefBranches`, `PrefReturns`, `PrefFormula`, and `CrossConstraint` -/

/-- Formula for a single outgoing edge record `i`: if `i` is a tree edge, the
subtree formula of its target; if `i` is a back edge, `True`. -/
def BranchFormula (N : ℕ) [NeZero N] (G : SimpleGraph (Fin N)) (s : Search)
    (i : ℕ) (c : ℕ → Color) : Prop :=
  if (s.edges[i]!).tree then
    (s.forest N).SubtreeFormula G (arcOfIdx N s i).2 (toColoring N s c)
  else True

/-- Union of `branchBackEdges` over a prefix `pref` of outgoing edge indices. -/
def PrefBranches (N : ℕ) [NeZero N] (G : SimpleGraph (Fin N)) (s : Search)
    (pref : List ℕ) : Set (Arc N) :=
  {b | ∃ i ∈ pref, b ∈ (s.forest N).branchBackEdges G (arcOfIdx N s i)}

/-- Union of `returns` over a prefix `pref` of outgoing edge indices. -/
def PrefReturns (N : ℕ) [NeZero N] (G : SimpleGraph (Fin N)) (s : Search)
    (pref : List ℕ) : Set (Arc N) :=
  {b | ∃ i ∈ pref, b ∈ (s.forest N).returns G (arcOfIdx N s i)}

/-- Formula accumulated over a prefix `pref` of outgoing edge indices. -/
def PrefFormula (N : ℕ) [NeZero N] (G : SimpleGraph (Fin N)) (s : Search)
    (pref : List ℕ) (c : ℕ → Color) : Prop :=
  (∀ i ∈ pref, BranchFormula N G s i c) ∧
  (∀ i ∈ pref, ∀ j ∈ pref, i ≠ j →
    ForkPair (s.forest N) G (toColoring N s c) (arcOfIdx N s i) (arcOfIdx N s j)) ∧
  Monochromatic (toColoring N s c) ((s.forest N).minDepthSet (PrefReturns N G s pref))

/-- Cross-constraints introduced when appending edge index `i` to `pref`. -/
def CrossConstraint (N : ℕ) [NeZero N] (G : SimpleGraph (Fin N)) (s : Search)
    (pref : List ℕ) (i : ℕ) (c : ℕ → Color) : Prop :=
  (∀ k ∈ pref, ForkPair (s.forest N) G (toColoring N s c) (arcOfIdx N s k) (arcOfIdx N s i)) ∧
  Monochromatic (toColoring N s c) ((s.forest N).minDepthSet (PrefReturns N G s (pref ++ [i])))

theorem prefReturns_sub_prefBranches (N : ℕ) [NeZero N] (G : SimpleGraph (Fin N))
    (s : Search) (pref : List ℕ) :
    PrefReturns N G s pref ⊆ PrefBranches N G s pref := by
  rintro b ⟨i, hi, hb⟩
  exact ⟨i, hi, (s.forest N).returns_sub_branchBackEdges G (arcOfIdx N s i) hb⟩

theorem prefReturns_sub_backEdges (N : ℕ) [NeZero N] (G : SimpleGraph (Fin N))
    (s : Search) (pref : List ℕ) :
    PrefReturns N G s pref ⊆ {b | (s.forest N).BackEdge G b} := by
  rintro b ⟨_, _, hb⟩
  exact hb.1

theorem prefBranches_sub_backEdges (N : ℕ) [NeZero N] (G : SimpleGraph (Fin N))
    (s : Search) (pref : List ℕ) :
    PrefBranches N G s pref ⊆ {b | (s.forest N).BackEdge G b} := by
  rintro b ⟨_, _, hb⟩
  exact hb.1

theorem prefReturns_snoc (N : ℕ) [NeZero N] (G : SimpleGraph (Fin N))
    (s : Search) (pref : List ℕ) (i : ℕ) :
    PrefReturns N G s (pref ++ [i]) =
      PrefReturns N G s pref ∪ (s.forest N).returns G (arcOfIdx N s i) := by
  ext b
  simp only [PrefReturns, List.mem_append, List.mem_singleton, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨k, hk | rfl, hbk⟩
    · exact Or.inl ⟨k, hk, hbk⟩
    · exact Or.inr hbk
  · rintro (⟨k, hk, hbk⟩ | hbi)
    · exact ⟨k, Or.inl hk, hbk⟩
    · exact ⟨i, Or.inr rfl, hbi⟩

theorem prefBranches_snoc (N : ℕ) [NeZero N] (G : SimpleGraph (Fin N))
    (s : Search) (pref : List ℕ) (i : ℕ) :
    PrefBranches N G s (pref ++ [i]) =
      PrefBranches N G s pref ∪ (s.forest N).branchBackEdges G (arcOfIdx N s i) := by
  ext b
  simp only [PrefBranches, List.mem_append, List.mem_singleton, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨k, hk | rfl, hbk⟩
    · exact Or.inl ⟨k, hk, hbk⟩
    · exact Or.inr hbk
  · rintro (⟨k, hk, hbk⟩ | hbi)
    · exact ⟨k, Or.inl hk, hbk⟩
    · exact ⟨i, Or.inr rfl, hbi⟩

theorem branchFormula_dependsOnlyOn {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : Search}
    (hAdj : Compute.IsAdjListFamily G lists)
    (hinv : DFSInv N G lists s []) (hall : ∀ v < N, s.Visited v)
    {i : ℕ} (hi : i < s.edges.size) :
    DependsOnlyOn (BranchFormula N G s i)
      (edgeSet N s ((s.forest N).branchBackEdges G (arcOfIdx N s i))) := by
  intro c₁ c₂ heq hform
  unfold BranchFormula at hform ⊢
  rcases arcOfIdx_tree_or_back hAdj hinv hall hi with ⟨htr, hte⟩ | ⟨htr, _⟩
  · simp only [htr, ↓reduceIte] at hform ⊢
    have hDFS : (s.forest N).IsDFS G := hinv.isDFS_of_nil hall
    have hbr_eq : (s.forest N).branchBackEdges G (arcOfIdx N s i) =
        (s.forest N).subtreeBackEdges G (arcOfIdx N s i).2 :=
      (s.forest N).branchBackEdges_eq_subtreeBackEdges_of_treeEdge hDFS hte
    refine (s.forest N).subtreeFormula_congr (fun b hb => ?_) hform
    have hb_in : b ∈ (s.forest N).branchBackEdges G (arcOfIdx N s i) := hbr_eq.symm ▸ hb
    have hidx : idxOfArc N s b ∈ edgeSet N s ((s.forest N).branchBackEdges G (arcOfIdx N s i)) :=
      idxOfArc_mem_edgeSet hAdj hinv hall (fun _ h => h.1) hb_in
    exact heq (idxOfArc N s b) hidx
  · simp [htr]

theorem prefFormula_dependsOnlyOn {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : Search}
    (hAdj : Compute.IsAdjListFamily G lists)
    (hinv : DFSInv N G lists s []) (hall : ∀ v < N, s.Visited v)
    {pref : List ℕ} (hpref : ∀ i ∈ pref, i < s.edges.size) :
    DependsOnlyOn (PrefFormula N G s pref)
      (edgeSet N s (PrefBranches N G s pref)) := by
  intro c₁ c₂ heq ⟨hbr, hfork, hmono⟩
  have hcol_eq : ∀ b ∈ PrefBranches N G s pref, toColoring N s c₁ b = toColoring N s c₂ b := by
    intro b hb
    exact heq (idxOfArc N s b)
      (idxOfArc_mem_edgeSet hAdj hinv hall (prefBranches_sub_backEdges N G s pref) hb)
  have hret_eq : ∀ b ∈ PrefReturns N G s pref, toColoring N s c₁ b = toColoring N s c₂ b :=
    fun b hb => hcol_eq b (prefReturns_sub_prefBranches N G s pref hb)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact branchFormula_dependsOnlyOn hAdj hinv hall (hpref i hi) c₁ c₂
      (fun k hk => heq k ⟨hk.1, hk.2.1, i, hi, hk.2.2⟩) (hbr i hi)
  · intro i hi j hj hne
    have hpair := hfork i hi j hj hne
    have hsub_i : (s.forest N).forkSet G (arcOfIdx N s i) (arcOfIdx N s j) ⊆ PrefReturns N G s pref :=
      fun b hb => ⟨i, hi, hb.1⟩
    have hsub_j : (s.forest N).forkSet G (arcOfIdx N s j) (arcOfIdx N s i) ⊆ PrefReturns N G s pref :=
      fun b hb => ⟨j, hj, hb.1⟩
    refine ⟨hpair.1.congr_on (fun b hb => hret_eq b (hsub_i hb)),
      hpair.2.1.congr_on (fun b hb => hret_eq b (hsub_j hb)), ?_⟩
    intro b hb c hc
    rw [← hret_eq b (hsub_i hb), ← hret_eq c (hsub_j hc)]
    exact hpair.2.2 b hb c hc
  · exact hmono.congr_on (fun b hb => hret_eq b hb.1)

theorem crossConstraint_dependsOnlyOn {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : Search}
    (hAdj : Compute.IsAdjListFamily G lists)
    (hinv : DFSInv N G lists s []) (hall : ∀ v < N, s.Visited v)
    (pref : List ℕ) (i : ℕ) :
    DependsOnlyOn (CrossConstraint N G s pref i)
      (edgeSet N s (PrefReturns N G s pref) ∪
        edgeSet N s ((s.forest N).returns G (arcOfIdx N s i))) := by
  intro c₁ c₂ heq ⟨hfork, hmono⟩
  rw [← edgeSet_union, ← prefReturns_snoc] at heq
  have hret_eq : ∀ b ∈ PrefReturns N G s (pref ++ [i]), toColoring N s c₁ b = toColoring N s c₂ b := by
    intro b hb
    exact heq (idxOfArc N s b)
      (idxOfArc_mem_edgeSet hAdj hinv hall (prefReturns_sub_backEdges N G s (pref ++ [i])) hb)
  refine ⟨?_, hmono.congr_on (fun b hb => hret_eq b hb.1)⟩
  intro k hk
  have hpair := hfork k hk
  have hsub_k : (s.forest N).forkSet G (arcOfIdx N s k) (arcOfIdx N s i) ⊆
      PrefReturns N G s (pref ++ [i]) :=
    fun b hb => ⟨k, List.mem_append_left _ hk, hb.1⟩
  have hsub_i : (s.forest N).forkSet G (arcOfIdx N s i) (arcOfIdx N s k) ⊆
      PrefReturns N G s (pref ++ [i]) :=
    fun b hb => ⟨i, List.mem_append_right _ (List.mem_singleton_self i), hb.1⟩
  refine ⟨hpair.1.congr_on (fun b hb => hret_eq b (hsub_k hb)),
    hpair.2.1.congr_on (fun b hb => hret_eq b (hsub_i hb)), ?_⟩
  intro b hb c hc
  rw [← hret_eq b (hsub_k hb), ← hret_eq c (hsub_i hc)]
  exact hpair.2.2 b hb c hc

theorem prefFormula_snoc_iff {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {s : Search} {pref : List ℕ} {i : ℕ}
    (hi_not_mem : i ∉ pref)
    (hmin_le : ∀ b₁ ∈ (s.forest N).minDepthSet (PrefReturns N G s pref),
      ∀ b₂ ∈ (s.forest N).returns G (arcOfIdx N s i),
        (s.forest N).depth b₁.2 ≤ (s.forest N).depth b₂.2)
    (c : ℕ → Color) :
    PrefFormula N G s (pref ++ [i]) c ↔
      PrefFormula N G s pref c ∧ BranchFormula N G s i c ∧ CrossConstraint N G s pref i c := by
  have hmin_sub :
      (s.forest N).minDepthSet (PrefReturns N G s pref) ⊆
        (s.forest N).minDepthSet (PrefReturns N G s (pref ++ [i])) := by
    intro b ⟨hb_in, hb_min⟩
    rw [prefReturns_snoc]
    refine ⟨Or.inl hb_in, ?_⟩
    rintro b' (hb'_pref | hb'_i)
    · exact hb_min b' hb'_pref
    · exact hmin_le b ⟨hb_in, hb_min⟩ b' hb'_i
  constructor
  · rintro ⟨hbr, hfork, hmono⟩
    refine ⟨⟨?_, ?_, hmono.subset hmin_sub⟩,
      hbr i (List.mem_append_right _ (List.mem_singleton_self i)),
      ⟨?_, hmono⟩⟩
    · intro k hk
      exact hbr k (List.mem_append_left _ hk)
    · intro k₁ hk₁ k₂ hk₂ hne
      exact hfork k₁ (List.mem_append_left _ hk₁) k₂ (List.mem_append_left _ hk₂) hne
    · intro k hk
      exact hfork k (List.mem_append_left _ hk) i
        (List.mem_append_right _ (List.mem_singleton_self i))
        (fun hki => hi_not_mem (hki ▸ hk))
  · rintro ⟨⟨hbr_pref, hfork_pref, _⟩, hbr_i, ⟨hfork_cross, hmono_all⟩⟩
    refine ⟨?_, ?_, hmono_all⟩
    · intro k hk
      rcases List.mem_append.mp hk with hk_pref | hk_i
      · exact hbr_pref k hk_pref
      · rw [List.mem_singleton.mp hk_i]
        exact hbr_i
    · intro k₁ hk₁ k₂ hk₂ hne
      rcases List.mem_append.mp hk₁ with hk₁_pref | hk₁_i <;>
        rcases List.mem_append.mp hk₂ with hk₂_pref | hk₂_i
      · exact hfork_pref k₁ hk₁_pref k₂ hk₂_pref hne
      · rw [List.mem_singleton.mp hk₂_i]
        exact hfork_cross k₁ hk₁_pref
      · rw [List.mem_singleton.mp hk₁_i]
        exact (hfork_cross k₂ hk₂_pref).symm
      · rw [List.mem_singleton.mp hk₁_i, List.mem_singleton.mp hk₂_i] at hne
        exact absurd rfl hne

theorem prefFormula_outgoing_iff_subtreeFormula {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : Search}
    (hAdj : Compute.IsAdjListFamily G lists)
    (hinv : DFSInv N G lists s []) (hall : ∀ v < N, s.Visited v)
    (v : Fin N) (out : List ℕ)
    (hout : ∀ i, i ∈ out ↔ i < s.edges.size ∧ (s.edges[i]!).source = v.val) :
    PrefReturns N G s out = (s.forest N).allReturnsAt G v ∧
    ∀ c : ℕ → Color,
      PrefFormula N G s out c ↔ (s.forest N).SubtreeFormula G v (toColoring N s c) := by
  have hout_arc : ∀ i ∈ out, (s.forest N).Outgoing G v (arcOfIdx N s i) := by
    intro i hi
    obtain ⟨hi_lt, hsrc⟩ := (hout i).mp hi
    have hf : (arcOfIdx N s i).1 = v := Fin.ext ((arcOfIdx_fst_val hinv hi_lt).trans hsrc)
    rcases arcOfIdx_tree_or_back hAdj hinv hall hi_lt with ⟨_, hte⟩ | ⟨_, hbe⟩
    · exact ⟨hf, Or.inl hte⟩
    · exact ⟨hf, Or.inr hbe⟩
  have hex_out : ∀ e : Arc N, (s.forest N).Outgoing G v e →
      idxOfArc N s e ∈ out ∧ arcOfIdx N s (idxOfArc N s e) = e := by
    intro e ⟨he1, hkind⟩
    obtain ⟨hi_lt, harc⟩ := idxOfArc_spec hAdj hinv hall hkind
    refine ⟨(hout (idxOfArc N s e)).mpr ⟨hi_lt, ?_⟩, harc⟩
    rw [← arcOfIdx_fst_val hinv hi_lt, harc, he1]
  have hret_eq : PrefReturns N G s out = (s.forest N).allReturnsAt G v := by
    rw [(s.forest N).allReturnsAt_eq_biUnion G v]
    ext b
    simp only [PrefReturns, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi, hb⟩
      exact ⟨arcOfIdx N s i, hout_arc i hi, hb⟩
    · rintro ⟨e, he, hb⟩
      obtain ⟨hidx_in, harc⟩ := hex_out e he
      exact ⟨idxOfArc N s e, hidx_in, harc.symm ▸ hb⟩
  refine ⟨hret_eq, fun c => ?_⟩
  rw [(s.forest N).subtreeFormula_iff G v (toColoring N s c)]
  unfold PrefFormula Forest.VertexConstraint
  rw [hret_eq]
  constructor
  · rintro ⟨hbr, hfork, hmono⟩
    refine ⟨⟨?_, hmono⟩, ?_⟩
    · intro e f he hf hne
      obtain ⟨ie_in, he_arc⟩ := hex_out e he
      obtain ⟨if_in, hf_arc⟩ := hex_out f hf
      have hne_idx : idxOfArc N s e ≠ idxOfArc N s f := by
        intro heq
        apply hne
        rw [← he_arc, ← hf_arc, heq]
      have hpair := hfork (idxOfArc N s e) ie_in (idxOfArc N s f) if_in hne_idx
      rwa [he_arc, hf_arc] at hpair
    · intro w hte
      obtain ⟨iw_in, hw_arc⟩ := hex_out (v, w) ⟨rfl, Or.inl hte⟩
      have hiw_lt : idxOfArc N s (v, w) < s.edges.size := ((hout _).mp iw_in).1
      have hbr_w := hbr (idxOfArc N s (v, w)) iw_in
      unfold BranchFormula at hbr_w
      rcases arcOfIdx_tree_or_back hAdj hinv hall hiw_lt with ⟨htr, _⟩ | ⟨_, hbe⟩
      · simp only [htr, ↓reduceIte, hw_arc] at hbr_w
        exact hbr_w
      · rw [hw_arc] at hbe
        have hstep := hinv.depth_step v w hte
        have hlt : (s.forest N).depth w < (s.forest N).depth v := hbe.2.2.1
        omega
  · rintro ⟨⟨hfork, hmono⟩, hchildren⟩
    refine ⟨?_, ?_, hmono⟩
    · intro i hi
      obtain ⟨hi_lt, hsrc⟩ := (hout i).mp hi
      unfold BranchFormula
      rcases arcOfIdx_tree_or_back hAdj hinv hall hi_lt with ⟨htr, hte⟩ | ⟨htr, _⟩
      · simp only [htr, ↓reduceIte]
        have hf : (arcOfIdx N s i).1 = v := Fin.ext ((arcOfIdx_fst_val hinv hi_lt).trans hsrc)
        have hte' : (s.forest N).TreeEdge (v, (arcOfIdx N s i).2) := hf ▸ hte
        exact hchildren (arcOfIdx N s i).2 hte'
      · simp [htr]
    · intro i hi j hj hne
      have hi_lt : i < s.edges.size := ((hout i).mp hi).1
      have hj_lt : j < s.edges.size := ((hout j).mp hj).1
      have hne_arc : arcOfIdx N s i ≠ arcOfIdx N s j :=
        fun heq => hne (arcOfIdx_inj hinv hi_lt hj_lt heq)
      exact hfork (arcOfIdx N s i) (arcOfIdx N s j) (hout_arc i hi) (hout_arc j hj) hne_arc

/-! ## Step Specification for Merging One Outgoing Branch (`merge_step_spec`) -/

theorem SummaryRep.least_eq_low {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {s : Search} {t : Summary} {e : Arc N}
    (hrep : SummaryRep N G s (some t) ((s.forest N).returns G e)) :
    t.least = (s.forest N).low G e := by
  obtain ⟨_, hle, ⟨b₁, hb₁, hd₁⟩, _⟩ := hrep.some_spec t rfl
  obtain ⟨b₂, hb₂, hd₂⟩ := (s.forest N).exists_mem_returns_depth_eq_low G e ⟨b₁, hb₁⟩
  have h1 : t.least ≤ (s.forest N).low G e := hd₂ ▸ hle b₂ hb₂
  have h2 : (s.forest N).low G e ≤ t.least :=
    hd₁ ▸ (s.forest N).low_le_depth_of_mem_returns G e b₁ hb₁
  omega

theorem SummaryRep.mono_minDepthSet {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : Search}
    (hAdj : Compute.IsAdjListFamily G lists)
    (hinv : DFSInv N G lists s []) (hall : ∀ v < N, s.Visited v)
    {sum : Option Summary} {S : Set (Arc N)}
    (hrep : SummaryRep N G s sum S) {c : ℕ → Color}
    (hform : SummaryFormula sum c) :
    Monochromatic (toColoring N s c) ((s.forest N).minDepthSet S) := by
  have hsub_min : (s.forest N).minDepthSet S ⊆ {b | (s.forest N).BackEdge G b} :=
    fun b hb => hrep.sub_back hb.1
  rcases sum with _ | t
  · have hemp : S = ∅ := hrep.none_iff.mp rfl
    intro b hb
    simp [Forest.minDepthSet, hemp] at hb
  · obtain ⟨_, _, _, hanc_eq⟩ := hrep.some_spec t rfl
    have hmono_anc : Monochromatic c (edgeSet N s ((s.forest N).minDepthSet S)) :=
      hanc_eq ▸ hform.1
    exact (monochromatic_edgeSet_iff hAdj hinv hall hsub_min c).mp hmono_anc

theorem merge_step_spec {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : Search}
    (hAdj : Compute.IsAdjListFamily G lists)
    (hinv : DFSInv N G lists s []) (hall : ∀ v < N, s.Visited v)
    (v : Fin N) (pref : List ℕ) (i : ℕ)
    (hnodup : (pref ++ [i]).Nodup)
    (hout : ∀ k ∈ pref ++ [i], k < s.edges.size ∧ (s.edges[k]!).source = v.val)
    (hkey_pair : (pref ++ [i]).Pairwise
      (fun k j => (s.forest N).key G (arcOfIdx N s k) ≤ (s.forest N).key G (arcOfIdx N s j)))
    (summary child : Option Summary)
    (hrep₁ : SummaryRep N G s summary (PrefReturns N G s pref))
    (hproj₁ : ProjectsTo (PrefFormula N G s pref)
      (edgeSet N s (PrefReturns N G s pref)) (SummaryFormula summary))
    (hrep₂ : SummaryRep N G s child ((s.forest N).returns G (arcOfIdx N s i)))
    (hproj₂ : ProjectsTo (BranchFormula N G s i)
      (edgeSet N s ((s.forest N).returns G (arcOfIdx N s i))) (SummaryFormula child)) :
    match merge summary child with
    | none => ¬ ∃ c, PrefFormula N G s (pref ++ [i]) c
    | some summary' =>
      SummaryRep N G s summary' (PrefReturns N G s (pref ++ [i])) ∧
      ProjectsTo (PrefFormula N G s (pref ++ [i]))
        (edgeSet N s (PrefReturns N G s (pref ++ [i])))
        (SummaryFormula summary') := by
  let T := s.forest N
  let e_new := arcOfIdx N s i
  have hDFS : T.IsDFS G := hinv.isDFS_of_nil hall
  have hnodup_split := List.nodup_append.mp hnodup
  have hpref_nodup : pref.Nodup := hnodup_split.1
  have hi_not_mem : i ∉ pref := fun hi => hnodup_split.2.2 i hi i (List.mem_singleton_self i) rfl
  have hi_in : i ∈ pref ++ [i] := List.mem_append_right _ (List.mem_singleton_self i)
  have hi_lt : i < s.edges.size := (hout i hi_in).1
  have hout_arc : ∀ k ∈ pref ++ [i], T.Outgoing G v (arcOfIdx N s k) := by
    intro k hk
    obtain ⟨hk_lt, hsrc⟩ := hout k hk
    have hf : (arcOfIdx N s k).1 = v := Fin.ext ((arcOfIdx_fst_val hinv hk_lt).trans hsrc)
    rcases arcOfIdx_tree_or_back hAdj hinv hall hk_lt with ⟨_, hte⟩ | ⟨_, hbe⟩
    · exact ⟨hf, Or.inl hte⟩
    · exact ⟨hf, Or.inr hbe⟩
  have hpair_split := List.pairwise_append.mp hkey_pair
  have hpref_pair : pref.Pairwise (fun k j => T.key G (arcOfIdx N s k) ≤ T.key G (arcOfIdx N s j)) :=
    hpair_split.1
  have hkey_le_i : ∀ k ∈ pref, T.key G (arcOfIdx N s k) ≤ T.key G e_new :=
    fun k hk => hpair_split.2.2 k hk i (List.mem_singleton_self i)
  have hdisj_br : Disjoint (PrefBranches N G s pref) (T.branchBackEdges G e_new) := by
    rw [Set.disjoint_left]
    rintro b ⟨k, hk, hbk⟩ hbi
    have hk_in : k ∈ pref ++ [i] := List.mem_append_left _ hk
    have hne_ki : k ≠ i := fun h => hi_not_mem (h ▸ hk)
    have hne_arc : arcOfIdx N s k ≠ e_new :=
      fun heq => hne_ki (arcOfIdx_inj hinv (hout k hk_in).1 hi_lt heq)
    exact Set.disjoint_left.mp
      (T.branchBackEdges_disjoint hDFS (hout_arc k hk_in) (hout_arc i hi_in) hne_arc)
      hbk hbi
  have hdisj_ret : Disjoint (PrefReturns N G s pref) (T.returns G e_new) :=
    hdisj_br.mono (prefReturns_sub_prefBranches N G s pref) (T.returns_sub_branchBackEdges G e_new)
  have hmin_le : ∀ b₁ ∈ T.minDepthSet (PrefReturns N G s pref),
      ∀ b₂ ∈ T.returns G e_new, T.depth b₁.2 ≤ T.depth b₂.2 := by
    rintro b₁ ⟨⟨k, hk, hbk⟩, hb₁_min⟩ b₂ hb₂
    obtain ⟨b₀, hb₀_ret, hb₀_eq⟩ :=
      T.exists_mem_returns_depth_eq_low G (arcOfIdx N s k) ⟨b₁, hbk⟩
    have hb₁_le_b₀ : T.depth b₁.2 ≤ T.low G (arcOfIdx N s k) :=
      hb₀_eq ▸ hb₁_min b₀ ⟨k, hk, hb₀_ret⟩
    have hlow_k_le_i : T.low G (arcOfIdx N s k) ≤ T.low G e_new :=
      T.low_le_of_key_le G (arcOfIdx N s k) e_new (hkey_le_i k hk)
    have hlow_i_le_b₂ : T.low G e_new ≤ T.depth b₂.2 :=
      T.low_le_depth_of_mem_returns G e_new b₂ hb₂
    exact le_trans hb₁_le_b₀ (le_trans hlow_k_le_i hlow_i_le_b₂)
  -- Existential projection composition onto `PrefReturns N G s (pref ++ [i])`
  have hproj_conj :
      ProjectsTo (PrefFormula N G s (pref ++ [i]))
        (edgeSet N s (PrefReturns N G s (pref ++ [i])))
        (fun c => SummaryFormula summary c ∧ SummaryFormula child c ∧
          CrossConstraint N G s pref i c) := by
    have hconj := ProjectsTo.conj_disjoint
      hproj₁ hproj₂
      (prefFormula_dependsOnlyOn hAdj hinv hall (fun k hk => (hout k (List.mem_append_left _ hk)).1))
      (branchFormula_dependsOnlyOn hAdj hinv hall hi_lt)
      (crossConstraint_dependsOnlyOn hAdj hinv hall pref i)
      (fun j hj => ⟨hj.1, hj.2.1, prefReturns_sub_prefBranches N G s pref hj.2.2⟩)
      (fun j hj => ⟨hj.1, hj.2.1, T.returns_sub_branchBackEdges G e_new hj.2.2⟩)
      (edgeSet_disjoint hdisj_br)
    rw [← edgeSet_union, ← prefReturns_snoc] at hconj
    exact ProjectsTo.congr_left hconj (fun ext => (prefFormula_snoc_iff hi_not_mem hmin_le ext).symm)
  -- Now split on `child` and `summary`
  rcases child with _ | new
  · -- Case 1: `child = none`
    have hmerge : merge summary none = some summary := by cases summary <;> rfl
    rw [hmerge]
    have hemp_new : T.returns G e_new = ∅ := hrep₂.none_iff.mp rfl
    have hret_eq : PrefReturns N G s (pref ++ [i]) = PrefReturns N G s pref := by
      rw [prefReturns_snoc, hemp_new, Set.union_empty]
    refine ⟨hret_eq.symm ▸ hrep₁, ?_⟩
    intro c
    rw [← hproj_conj c]
    constructor
    · intro hsum
      refine ⟨hsum, trivial, ?_, ?_⟩
      · intro k hk
        exact (T.forkPair_of_returns_empty (toColoring N s c)
          (hout_arc i hi_in) (hout_arc k (List.mem_append_left _ hk)) hemp_new).2
      · rw [hret_eq]
        exact hrep₁.mono_minDepthSet hAdj hinv hall hsum
    · exact fun h => h.1
  · rcases summary with _ | old
    · -- Case 2: `summary = none`, `child = some new`
      have hmerge : merge none (some new) = some (some new) := rfl
      rw [hmerge]
      have hemp_pref : PrefReturns N G s pref = ∅ := hrep₁.none_iff.mp rfl
      have hret_eq : PrefReturns N G s (pref ++ [i]) = T.returns G e_new := by
        rw [prefReturns_snoc, hemp_pref, Set.empty_union]
      refine ⟨hret_eq.symm ▸ hrep₂, ?_⟩
      intro c
      rw [← hproj_conj c]
      constructor
      · intro hnew
        refine ⟨trivial, hnew, ?_, ?_⟩
        · intro k hk
          have hemp_k : T.returns G (arcOfIdx N s k) = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            intro b hb
            have : b ∈ PrefReturns N G s pref := ⟨k, hk, hb⟩
            rw [hemp_pref] at this
            exact this
          exact (T.forkPair_of_returns_empty (toColoring N s c)
            (hout_arc k (List.mem_append_left _ hk)) (hout_arc i hi_in) hemp_k).1
        · rw [hret_eq]
          exact hrep₂.mono_minDepthSet hAdj hinv hall hnew
      · exact fun h => h.2.1
    · -- Case 3: `summary = some old`, `child = some new`
      have hnew_least : new.least = T.low G e_new := hrep₂.least_eq_low
      obtain ⟨hold_valid, hold_least_le, ⟨b_old, hb_old_in, hb_old_depth⟩, hold_anc_eq⟩ :=
        hrep₁.some_spec old rfl
      obtain ⟨hnew_valid, hnew_least_le, ⟨b_new, hb_new_in, hb_new_depth⟩, hnew_anc_eq⟩ :=
        hrep₂.some_spec new rfl
      -- Nonempty branches in `pref`
      let nePref : List (Arc N) :=
        (pref.map (arcOfIdx N s)).filter (fun e => decide (T.returns G e).Nonempty)
      have hmem_nePref : ∀ k ∈ pref, (T.returns G (arcOfIdx N s k)).Nonempty →
          arcOfIdx N s k ∈ nePref := by
        intro k hk hne
        exact List.mem_filter.mpr ⟨List.mem_map_of_mem hk, decide_eq_true hne⟩
      have ⟨k₀, hk₀, hbk₀⟩ := hb_old_in
      have hnePref_ne : nePref ≠ [] := by
        intro hnil
        have := hmem_nePref k₀ hk₀ ⟨b_old, hbk₀⟩
        rw [hnil] at this
        nomatch this
      rcases hnePref_eq : nePref with _ | ⟨first, rest⟩
      · exact absurd hnePref_eq hnePref_ne
      have hnePref_sub : (first :: rest).Sublist (pref.map (arcOfIdx N s)) :=
        hnePref_eq ▸ List.filter_sublist
      have hnePref_prop : ∀ e ∈ first :: rest,
          (∃ k ∈ pref, arcOfIdx N s k = e) ∧ (T.returns G e).Nonempty := by
        intro e he
        have he' : e ∈ nePref := hnePref_eq ▸ he
        rw [List.mem_filter, List.mem_map, decide_eq_true_eq] at he'
        exact he'
      have hmap_pair : (pref.map (arcOfIdx N s)).Pairwise (fun e f => T.key G e ≤ T.key G f) :=
        List.pairwise_map.mpr hpref_pair
      have hnePref_pair : (first :: rest).Pairwise (fun e f => T.key G e ≤ T.key G f) :=
        hmap_pair.sublist hnePref_sub
      -- Prove `old.least = T.low G first`
      have hold_least : old.least = T.low G first := by
        obtain ⟨⟨k_f, hk_f, hkf_eq⟩, hfirst_ne⟩ := hnePref_prop first List.mem_cons_self
        obtain ⟨b_f, hb_f_in, hb_f_depth⟩ :=
          T.exists_mem_returns_depth_eq_low G first hfirst_ne
        have h1 : old.least ≤ T.low G first :=
          hb_f_depth ▸ hold_least_le b_f ⟨k_f, hk_f, hkf_eq.symm ▸ hb_f_in⟩
        have hbk₀_ge : T.low G (arcOfIdx N s k₀) ≤ old.least :=
          hb_old_depth ▸ T.low_le_depth_of_mem_returns G (arcOfIdx N s k₀) b_old hbk₀
        have hk₀_in_fr : arcOfIdx N s k₀ ∈ first :: rest :=
          hnePref_eq ▸ hmem_nePref k₀ hk₀ ⟨b_old, hbk₀⟩
        have hkey_fk₀ : T.key G first ≤ T.key G (arcOfIdx N s k₀) := by
          rcases List.mem_cons.mp hk₀_in_fr with heq | hmem_rest
          · rw [heq]
          · exact (List.pairwise_cons.mp hnePref_pair).1 _ hmem_rest
        have hlow_fk₀ : T.low G first ≤ T.low G (arcOfIdx N s k₀) :=
          T.low_le_of_key_le G _ _ hkey_fk₀
        omega
      have hleast_le : old.least ≤ new.least := by
        obtain ⟨⟨k_f, hk_f, hkf_eq⟩, _⟩ := hnePref_prop first List.mem_cons_self
        rw [hold_least, hnew_least, ← hkf_eq]
        exact T.low_le_of_key_le G _ _ (hkey_le_i k_f hk_f)
      -- Set up `forkAggregationStatement` for `branches := first :: rest ++ [e_new]`
      have hbranches_nodup : (first :: rest ++ [e_new]).Nodup := by
        have hmap_all_nodup : ((pref ++ [i]).map (arcOfIdx N s)).Nodup := by
          rw [List.nodup_map_iff_inj_on hnodup]
          intro x hx y hy heq
          exact arcOfIdx_inj hinv (hout x hx).1 (hout y hy).1 heq
        rw [List.map_append, List.map_singleton] at hmap_all_nodup
        exact hmap_all_nodup.sublist (hnePref_sub.append (List.Sublist.refl [e_new]))
      have hbranches_out : ∀ e ∈ first :: rest ++ [e_new],
          T.Outgoing G v e ∧ (T.returns G e).Nonempty := by
        intro e he
        rcases List.mem_append.mp he with he_fr | he_new
        · obtain ⟨⟨k, hk, rfl⟩, hne_k⟩ := hnePref_prop e he_fr
          exact ⟨hout_arc k (List.mem_append_left _ hk), hne_k⟩
        · rw [List.mem_singleton.mp he_new]
          exact ⟨hout_arc i hi_in, ⟨b_new, hb_new_in⟩⟩
      have hbranches_pair : (first :: rest ++ [e_new]).Pairwise
          (fun e f => T.key G e ≤ T.key G f) := by
        rw [List.pairwise_append]
        refine ⟨hnePref_pair, List.pairwise_singleton _ _, ?_⟩
        intro e he f hf
        rw [List.mem_singleton.mp hf]
        obtain ⟨⟨k, hk, rfl⟩, _⟩ := hnePref_prop e he
        exact hkey_le_i k hk
      let B_arc : Set (Arc N) := T.forkSet G e_new first
      let U_arc : Set (Arc N) :=
        {b | ∃ e ∈ first :: rest, b ∈ T.returns G e ∧ T.low G e_new < T.depth b.2}
      have hB_arc_eq : B_arc = {b | b ∈ T.returns G e_new ∧ old.least < T.depth b.2} := by
        ext b; simp [B_arc, Forest.forkSet, hold_least]
      have hU_arc_eq : U_arc = {b | b ∈ PrefReturns N G s pref ∧ new.least < T.depth b.2} := by
        ext b
        simp only [U_arc, PrefReturns, Set.mem_ofPred_eq, hnew_least]
        constructor
        · rintro ⟨e, he_fr, hbe, hlt⟩
          obtain ⟨⟨k, hk, rfl⟩, _⟩ := hnePref_prop e he_fr
          exact ⟨⟨k, hk, hbe⟩, hlt⟩
        · rintro ⟨⟨k, hk, hbk⟩, hlt⟩
          exact ⟨arcOfIdx N s k, hnePref_eq ▸ hmem_nePref k hk ⟨b, hbk⟩, hbk, hlt⟩
      have hUB : (∃ b ∈ PrefReturns N G s pref, new.least < T.depth b.2) →
          (∃ b ∈ T.returns G e_new, old.least < T.depth b.2) := by
        intro ⟨b, hb_in, hlt⟩
        have hU_ne : U_arc.Nonempty := ⟨b, hU_arc_eq.symm ▸ ⟨hb_in, hlt⟩⟩
        have hB_ne : B_arc.Nonempty :=
          (forkAggregationStatement N G T hDFS (fun _ => .left) v first rest e_new
            hbranches_nodup hbranches_out hbranches_pair).2 hU_ne
        rcases hB_ne with ⟨b', hb'⟩
        rw [hB_arc_eq] at hb'
        exact ⟨b', hb'.1, hb'.2⟩
      -- Equivalence between `SummaryFormula (some old) c ∧ SummaryFormula (some new) c ∧ CrossConstraint ... c`
      -- and `MergeFormula old new c`
      have hmid_iff_merge : ∀ c : ℕ → Color,
          (SummaryFormula (some old) c ∧ SummaryFormula (some new) c ∧
            CrossConstraint N G s pref i c) ↔ MergeFormula old new c := by
        intro c
        have hagg := (forkAggregationStatement N G T hDFS (toColoring N s c) v first rest e_new
          hbranches_nodup hbranches_out hbranches_pair).1
        have hfork_pref_iff :
            (∀ k ∈ pref, ForkPair T G (toColoring N s c) (arcOfIdx N s k) e_new) ↔
              (∀ e ∈ first :: rest, ForkPair T G (toColoring N s c) e e_new) := by
          constructor
          · intro hall_k e he
            obtain ⟨⟨k, hk, rfl⟩, _⟩ := hnePref_prop e he
            exact hall_k k hk
          · intro hall_fr k hk
            by_cases hne_k : (T.returns G (arcOfIdx N s k)).Nonempty
            · exact hall_fr (arcOfIdx N s k) (hnePref_eq ▸ hmem_nePref k hk hne_k)
            · have hemp_k : T.returns G (arcOfIdx N s k) = ∅ :=
                Set.not_nonempty_iff_eq_empty.mp hne_k
              exact (T.forkPair_of_returns_empty (toColoring N s c)
                (hout_arc k (List.mem_append_left _ hk)) (hout_arc i hi_in) hemp_k).1
        have hB_node :
            nodeSet (new.nodes.filter (fun b => decide (old.least < b.depth))) =
              edgeSet N s B_arc := by
          rw [hrep₂.filter_gt_eq old.least, hB_arc_eq]
        have hU_node :
            nodeSet (old.nodes.filter (fun b => decide (new.least < b.depth))) =
              edgeSet N s U_arc := by
          rw [hrep₁.filter_gt_eq new.least, hU_arc_eq]
        have hB_sub_back : B_arc ⊆ {b | T.BackEdge G b} := fun b hb => hb.1.1
        have hU_sub_back : U_arc ⊆ {b | T.BackEdge G b} := by
          rw [hU_arc_eq]
          exact fun b hb => prefReturns_sub_backEdges N G s pref hb.1
        have hB_mono_iff :
            Monochromatic c (nodeSet (new.nodes.filter (fun b => decide (old.least < b.depth)))) ↔
              Monochromatic (toColoring N s c) B_arc := by
          rw [hB_node]
          exact monochromatic_edgeSet_iff hAdj hinv hall hB_sub_back c
        have hU_mono_iff :
            Monochromatic c (nodeSet (old.nodes.filter (fun b => decide (new.least < b.depth)))) ↔
              Monochromatic (toColoring N s c) U_arc := by
          rw [hU_node]
          exact monochromatic_edgeSet_iff hAdj hinv hall hU_sub_back c
        have hBU_opp_iff :
            (∀ x ∈ nodeSet (new.nodes.filter (fun b => decide (old.least < b.depth))),
              ∀ y ∈ nodeSet (old.nodes.filter (fun b => decide (new.least < b.depth))),
                c x ≠ c y) ↔
              (∀ b ∈ B_arc, ∀ d ∈ U_arc, toColoring N s c b ≠ toColoring N s c d) := by
          rw [hB_node, hU_node]
          exact opp_edgeSet_iff hAdj hinv hall hB_sub_back hU_sub_back c
        have hcross_fork_iff :
            (∀ k ∈ pref, ForkPair T G (toColoring N s c) (arcOfIdx N s k) e_new) ↔
              Monochromatic c (nodeSet (new.nodes.filter (fun b => decide (old.least < b.depth)))) ∧
              Monochromatic c (nodeSet (old.nodes.filter (fun b => decide (new.least < b.depth)))) ∧
              (∀ x ∈ nodeSet (new.nodes.filter (fun b => decide (old.least < b.depth))),
                ∀ y ∈ nodeSet (old.nodes.filter (fun b => decide (new.least < b.depth))),
                  c x ≠ c y) := by
          rw [hfork_pref_iff, hagg, hB_mono_iff, hU_mono_iff, hBU_opp_iff]
        -- Anchor condition equivalence
        have hmin_sub_back :
            T.minDepthSet (PrefReturns N G s (pref ++ [i])) ⊆ {b | T.BackEdge G b} :=
          fun b hb => prefReturns_sub_backEdges N G s (pref ++ [i]) hb.1
        have hanc_iff :
            old.Holds c → new.Holds c →
              (Monochromatic (toColoring N s c) (T.minDepthSet (PrefReturns N G s (pref ++ [i]))) ↔
                (old.least = new.least → Monochromatic c (nodeSet (old.anchor ++ new.anchor)))) := by
          intro hold_c hnew_c
          by_cases heq : old.least = new.least
          · simp only [heq, forall_true_left]
            have hmin_union :
                T.minDepthSet (PrefReturns N G s (pref ++ [i])) =
                  T.minDepthSet (PrefReturns N G s pref) ∪ T.minDepthSet (T.returns G e_new) := by
              rw [prefReturns_snoc]
              ext b
              simp only [Forest.minDepthSet, Set.mem_ofPred_eq, Set.mem_union]
              constructor
              · rintro ⟨hb_pref | hb_new', hb_min⟩
                · exact Or.inl ⟨hb_pref, fun b' hb' => hb_min b' (Or.inl hb')⟩
                · exact Or.inr ⟨hb_new', fun b' hb' => hb_min b' (Or.inr hb')⟩
              · rintro (⟨hb_pref, hb_min⟩ | ⟨hb_new', hb_min⟩)
                · refine ⟨Or.inl hb_pref, ?_⟩
                  rintro b' (hb'_pref | hb'_new)
                  · exact hb_min b' hb'_pref
                  · exact hmin_le b ⟨hb_pref, hb_min⟩ b' hb'_new
                · refine ⟨Or.inr hb_new', ?_⟩
                  rintro b' (hb'_pref | hb'_new)
                  · have h1 : T.depth b.2 ≤ new.least :=
                      hb_new_depth ▸ hb_min b_new hb_new_in
                    have h2 : new.least ≤ T.depth b'.2 :=
                      heq ▸ hold_least_le b' hb'_pref
                    exact le_trans h1 h2
                  · exact hb_min b' hb'_new
            have hnode_anc :
                nodeSet (old.anchor ++ new.anchor) =
                  edgeSet N s (T.minDepthSet (PrefReturns N G s (pref ++ [i]))) := by
              rw [nodeSet_append, hold_anc_eq, hnew_anc_eq, ← edgeSet_union, hmin_union]
              rfl
            rw [hnode_anc]
            exact (monochromatic_edgeSet_iff hAdj hinv hall hmin_sub_back c).symm
          · simp only [heq, IsEmpty.forall_iff, iff_true]
            have hlt : old.least < new.least := lt_of_le_of_ne hleast_le heq
            have hmin_eq :
                T.minDepthSet (PrefReturns N G s (pref ++ [i])) =
                  T.minDepthSet (PrefReturns N G s pref) := by
              rw [prefReturns_snoc]
              ext b
              simp only [Forest.minDepthSet, Set.mem_ofPred_eq, Set.mem_union]
              constructor
              · rintro ⟨hb_pref | hb_new', hb_min⟩
                · exact ⟨hb_pref, fun b' hb' => hb_min b' (Or.inl hb')⟩
                · have h1 : T.depth b.2 ≤ old.least :=
                    hb_old_depth ▸ hb_min b_old (Or.inl hb_old_in)
                  have h2 : new.least ≤ T.depth b.2 := hnew_least_le b hb_new'
                  omega
              · rintro ⟨hb_pref, hb_min⟩
                refine ⟨Or.inl hb_pref, ?_⟩
                rintro b' (hb'_pref | hb'_new)
                · exact hb_min b' hb'_pref
                · exact hmin_le b ⟨hb_pref, hb_min⟩ b' hb'_new
            rw [hmin_eq]
            exact hrep₁.mono_minDepthSet hAdj hinv hall hold_c
        unfold SummaryFormula CrossConstraint MergeFormula
        dsimp only
        rw [hcross_fork_iff]
        constructor
        · rintro ⟨hold_c, hnew_c, ⟨hB, hU, hBU⟩, hmono⟩
          exact ⟨hold_c, hnew_c, hB, hU, hBU, (hanc_iff hold_c hnew_c).mp hmono⟩
        · rintro ⟨hold_c, hnew_c, hB, hU, hBU, hanc⟩
          exact ⟨hold_c, hnew_c, ⟨hB, hU, hBU⟩, (hanc_iff hold_c hnew_c).mpr hanc⟩
      -- Apply `SummaryRep.merge_some`
      have hmerge_spec :=
        SummaryRep.merge_some hAdj hinv hall hrep₁ hrep₂ hdisj_ret hleast_le hUB
      rcases hmerge : merge (some old) (some new) with _ | summary'
      · rw [hmerge] at hmerge_spec
        rintro ⟨c, hc⟩
        have hc_mid := (hproj_conj c).mpr ⟨c, hc, fun _ _ => rfl⟩
        exact hmerge_spec ⟨c, (hmid_iff_merge c).mp hc_mid⟩
      · rw [hmerge] at hmerge_spec
        rcases hmerge_spec with ⟨hform_iff, hrep_merged⟩
        rw [← prefReturns_snoc] at hrep_merged
        refine ⟨hrep_merged, ?_⟩
        intro c
        rw [hform_iff c, ← hmid_iff_merge c, ← hproj_conj c]

end GraphMinor.LRPlanarity
