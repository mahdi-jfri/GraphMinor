module

public import GraphMinor.LRPlanarity.Search
public import GraphMinor.LRPlanarity.Lowpoints
public import GraphMinor.LRPlanarity.Bucket
public import GraphMinor.LRPlanarity.Merge

/-!
# Solver Invariants, Existential Projection Composition, and Summary Representation (Part II)

This module develops the forest structural lemmas, existential projection
composition lemmas ("Why completed formulas compose", Part II), and the
`SummaryRep` representation invariant used in `GraphMinor/LRPlanarity/Solver.lean`
to prove `SolverStatement`.
-/

@[expose] public section
namespace GraphMinor.LRPlanarity

open Classical

/-! ## Recursive Unfolding of `solve` (`solveLoop`) -/

/-- Recursive formulation of the postorder loop in `solve`. -/
def solveLoop (search : Search) (outgoing : Array (List ℕ)) :
    List ℕ → Array (Option Summary) → Bool
  | [], _ => true
  | v :: rest, results =>
    match solveOutgoing search outgoing[v]! results none with
    | none => false
    | some (rs, summary) =>
      let summary := match search.parent[v]?.join with
        | none => summary
        | some u => trim summary ((search.depth[u]?.join).getD 0)
      solveLoop search outgoing rest (rs.set! v summary)

private theorem solve_forIn_eq_solveLoop (search : Search) (outgoing : Array (List ℕ))
    (l : List ℕ) (results : Array (Option Summary)) :
    Id.run (do
      let __s ←
        forIn l ((none : Option Bool), results) fun v __s ↦
          match solveOutgoing search outgoing[v]! __s.2 none with
          | none => pure (ForInStep.done (some false, __s.2))
          | some (rs, summary) =>
            pure (ForInStep.yield (none, rs.set! v
              (match search.parent[v]?.join with
              | none => summary
              | some u => trim summary (search.depth[u]?.join.getD 0))))
      match __s.1 with
      | some r => pure r
      | none => pure true) = solveLoop search outgoing l results := by
  induction l generalizing results with
  | nil =>
    simp [solveLoop]
  | cons v rest ih =>
    simp only [List.forIn_cons, bind, pure, Id.run, solveLoop]
    rcases solveOutgoing search outgoing[v]! results none with _ | ⟨rs, summary⟩
    · rfl
    · exact ih _

theorem solve_eq_solveLoop (n : ℕ) (search : Search) (outgoing : Array (List ℕ)) :
    solve n search outgoing =
      solveLoop search outgoing search.postorder (Array.replicate n none) := by
  unfold solve
  dsimp only
  convert solve_forIn_eq_solveLoop search outgoing search.postorder (Array.replicate n none)
  rename_i x
  cases x.1 <;> rfl

/-! ## Depth-First Forest Structural Lemmas -/

theorem Forest.depth_step_of_isDFS {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) (u v : Fin N) (hp : T.parent v = some u) :
    T.depth v = T.depth u + 1 :=
  (hDFS.2.1 u v hp).2

theorem Forest.depth_le_of_ancestor_of_isDFS {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) {u v : Fin N} (hanc : T.Ancestor u v) :
    T.depth u ≤ T.depth v :=
  Forest.depth_le_of_ancestor (Forest.depth_step_of_isDFS hDFS) hanc

theorem Forest.depth_lt_of_ancestor_ne_of_isDFS {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) {u v : Fin N} (hanc : T.Ancestor u v) (hne : u ≠ v) :
    T.depth u < T.depth v := by
  cases hanc with
  | refl => exact absurd rfl hne
  | tail hp_anc hp =>
    have hd_le := T.depth_le_of_ancestor_of_isDFS hDFS hp_anc
    have hd_step := T.depth_step_of_isDFS hDFS _ v hp
    omega

theorem Forest.eq_of_ancestor_of_depth_le_of_isDFS {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) {u v : Fin N} (hanc : T.Ancestor u v) (hle : T.depth v ≤ T.depth u) :
    u = v := by
  by_contra hne
  have hlt := T.depth_lt_of_ancestor_ne_of_isDFS hDFS hanc hne
  omega

theorem Forest.ancestor_of_ancestor_of_depth_le {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) {u w x : Fin N}
    (hu : T.Ancestor u x) (hw : T.Ancestor w x) (hd : T.depth u ≤ T.depth w) :
    T.Ancestor u w := by
  induction hw with
  | refl => exact hu
  | @tail y z hwy hyz ih =>
    have hdy : T.depth w ≤ T.depth y := T.depth_le_of_ancestor_of_isDFS hDFS hwy
    have hdz : T.depth z = T.depth y + 1 := T.depth_step_of_isDFS hDFS y z hyz
    cases hu with
    | refl => omega
    | @tail y' _ huy' hy'z =>
      have hy_eq : y' = y := Option.some.inj (hy'z.symm.trans hyz)
      subst hy_eq
      exact ih huy'

theorem Forest.eq_of_ancestor_of_depth_eq {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) {u₁ u₂ x : Fin N}
    (h1 : T.Ancestor u₁ x) (h2 : T.Ancestor u₂ x) (hd : T.depth u₁ = T.depth u₂) :
    u₁ = u₂ := by
  have h12 : T.Ancestor u₁ u₂ :=
    T.ancestor_of_ancestor_of_depth_le hDFS h1 h2 (le_of_eq hd)
  exact T.eq_of_ancestor_of_depth_le_of_isDFS hDFS h12 (ge_of_eq hd)

theorem Forest.parent_eq_none_iff_depth_eq_zero {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) (v : Fin N) :
    T.parent v = none ↔ T.depth v = 0 := by
  constructor
  · exact hDFS.1 v
  · intro hd
    rcases hp : T.parent v with _ | u
    · rfl
    · have hstep := T.depth_step_of_isDFS hDFS u v hp
      omega

private theorem Forest.exists_ancestor_sub {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) (k : ℕ) :
    ∀ v : Fin N, k ≤ T.depth v → ∃ u : Fin N, T.Ancestor u v ∧ T.depth u = T.depth v - k := by
  induction k with
  | zero =>
    intro v _
    exact ⟨v, Relation.ReflTransGen.refl, by omega⟩
  | succ k ih =>
    intro v hk
    rcases hp : T.parent v with _ | p
    · have hd0 := hDFS.1 v hp
      omega
    · have hstep := T.depth_step_of_isDFS hDFS p v hp
      obtain ⟨u, hup, hdu⟩ := ih p (by omega)
      exact ⟨u, Relation.ReflTransGen.tail hup hp, by omega⟩

theorem Forest.exists_ancestor_of_depth_le {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) (v : Fin N) {d : ℕ} (hd : d ≤ T.depth v) :
    ∃ u : Fin N, T.Ancestor u v ∧ T.depth u = d := by
  obtain ⟨u, huv, hdu⟩ := T.exists_ancestor_sub hDFS (T.depth v - d) v (by omega)
  exact ⟨u, huv, by omega⟩

theorem Forest.exists_root_ancestor {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) (v : Fin N) :
    ∃ r : Fin N, T.parent r = none ∧ T.Ancestor r v := by
  obtain ⟨r, hrv, hdr⟩ := T.exists_ancestor_of_depth_le hDFS v (Nat.zero_le (T.depth v))
  exact ⟨r, (T.parent_eq_none_iff_depth_eq_zero hDFS r).mpr hdr, hrv⟩

theorem Forest.root_ancestor_unique {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) {r₁ r₂ v : Fin N}
    (hr₁ : T.parent r₁ = none) (hr₂ : T.parent r₂ = none)
    (h1 : T.Ancestor r₁ v) (h2 : T.Ancestor r₂ v) :
    r₁ = r₂ :=
  T.eq_of_ancestor_of_depth_eq hDFS h1 h2 ((hDFS.1 r₁ hr₁).trans (hDFS.1 r₂ hr₂).symm)

theorem Forest.depth_lt_N {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) (v : Fin N) :
    T.depth v < N := by
  let f : Fin (T.depth v + 1) → Fin N := fun d =>
    Classical.choose (T.exists_ancestor_of_depth_le hDFS v (Nat.le_of_lt_succ d.isLt))
  have hf : ∀ d : Fin (T.depth v + 1), T.depth (f d) = d.val := fun d =>
    (Classical.choose_spec (T.exists_ancestor_of_depth_le hDFS v (Nat.le_of_lt_succ d.isLt))).2
  have hinj : Function.Injective f := by
    intro d₁ d₂ heq
    ext
    rw [← hf d₁, ← hf d₂, heq]
  have hcard := Fintype.card_le_of_injective f hinj
  simpa using hcard

theorem Forest.key_le_two_mul_N {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) (e : Arc N) :
    T.key G e ≤ 2 * N := by
  unfold Forest.key
  have hlow_le : T.low G e ≤ T.depth e.1 := by
    unfold Forest.low
    exact Finset.min'_le _ (T.depth e.1) (by simp)
  have hd_lt : T.depth e.1 < N := T.depth_lt_N hDFS e.1
  have hthick_le : (T.thick G e).toNat ≤ 1 := Bool.toNat_le (T.thick G e)
  omega

theorem Forest.ancestor_iff_eq_or_exists_child {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) (v u : Fin N) :
    T.Ancestor v u ↔ u = v ∨ ∃ w : Fin N, T.TreeEdge (v, w) ∧ T.Ancestor w u := by
  constructor
  · intro hanc
    by_cases heq : u = v
    · exact Or.inl heq
    · right
      have hlt : T.depth v < T.depth u := T.depth_lt_of_ancestor_ne_of_isDFS hDFS hanc (Ne.symm heq)
      obtain ⟨w, hwu, hdw⟩ := T.exists_ancestor_of_depth_le hDFS u (by omega : T.depth v + 1 ≤ T.depth u)
      have hvw : T.Ancestor v w := T.ancestor_of_ancestor_of_depth_le hDFS hanc hwu (by omega)
      cases hvw with
      | refl => omega
      | @tail p _ hvp hp =>
        have hp_step := T.depth_step_of_isDFS hDFS p w hp
        have hp_eq : v = p := T.eq_of_ancestor_of_depth_le_of_isDFS hDFS hvp (by omega)
        subst hp_eq
        exact ⟨w, hp, hwu⟩
  · rintro (rfl | ⟨w, hvw, hwu⟩)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head hvw hwu

theorem Forest.weakReturns_eq_biUnion_returns {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) {u v : Fin N} (hp : T.TreeEdge (u, v)) :
    T.weakReturns G (u, v) = {b | ∃ e, T.Outgoing G v e ∧ b ∈ T.returns G e} := by
  have hd_step : T.depth v = T.depth u + 1 := T.depth_step_of_isDFS hDFS u v hp
  ext b
  simp only [Forest.weakReturns, Forest.Outgoing, Forest.returns, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hb_back, hanc_vb1, hd_le⟩
    have hd_lt : T.depth b.2 < T.depth v := by omega
    rw [T.ancestor_iff_eq_or_exists_child hDFS v b.1] at hanc_vb1
    rcases hanc_vb1 with hb1_eq | ⟨w, hvw, hwb1⟩
    · refine ⟨b, ⟨hb1_eq, Or.inr hb_back⟩, hb_back, Or.inl ⟨hb_back, rfl⟩⟩
    · refine ⟨(v, w), ⟨rfl, Or.inl hvw⟩, hb_back, Or.inr ⟨hvw, hwb1, hd_lt⟩⟩
  · rintro ⟨e, ⟨rfl, hte | hbe⟩, hb_back, ⟨_, rfl⟩ | ⟨hte', hanc_eb1, hd_lt⟩⟩
    · have := hb_back.2.2.1
      exact ⟨hb_back, Relation.ReflTransGen.refl, by omega⟩
    · exact ⟨hb_back, Relation.ReflTransGen.head hte' hanc_eb1, by omega⟩
    · have := hb_back.2.2.1
      exact ⟨hb_back, Relation.ReflTransGen.refl, by omega⟩
    · exact ⟨hb_back, Relation.ReflTransGen.head hte' hanc_eb1, by omega⟩

theorem Forest.returns_eq_empty_of_root {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) {v : Fin N} (hroot : T.parent v = none)
    {e : Arc N} (he : T.Outgoing G v e) :
    T.returns G e = ∅ := by
  have hdv : T.depth v = 0 := hDFS.1 v hroot
  ext b
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hb
  have hlt := T.returns_depth_lt G e b hb
  rw [he.1, hdv] at hlt
  omega

theorem Forest.forkSet_eq_empty_of_returns_empty_left {N : ℕ} {G : SimpleGraph (Fin N)}
    {T : Forest N} {e f : Arc N} (he : T.returns G e = ∅) :
    T.forkSet G e f = ∅ := by
  ext b
  simp [Forest.forkSet, he]

theorem Forest.forkSet_eq_empty_of_returns_empty_right {N : ℕ} {G : SimpleGraph (Fin N)}
    {T : Forest N} {v : Fin N} {e f : Arc N}
    (he : T.Outgoing G v e) (hf : T.Outgoing G v f) (hf_emp : T.returns G f = ∅) :
    T.forkSet G e f = ∅ := by
  have hlow_f : T.low G f = T.depth v := by
    unfold Forest.low
    have hfilt : Finset.univ.filter (fun b => b ∈ T.returns G f) = ∅ := by
      ext b; simp [hf_emp]
    simp [hfilt, hf.1]
  ext b
  simp only [Forest.forkSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hb
  have hlt := T.returns_depth_lt G e b hb
  rw [he.1] at hlt
  rw [hlow_f]
  omega

theorem Forest.forkPair_of_returns_empty {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (color : Coloring N) {v : Fin N} {e f : Arc N}
    (he : T.Outgoing G v e) (hf : T.Outgoing G v f) (he_emp : T.returns G e = ∅) :
    ForkPair T G color e f ∧ ForkPair T G color f e := by
  have h1 := T.forkSet_eq_empty_of_returns_empty_left (f := f) he_emp
  have h2 := T.forkSet_eq_empty_of_returns_empty_right hf he he_emp
  simp [ForkPair, h1, h2]

/-! ## `DependsOnlyOn` and `ProjectsTo` Composition Lemmas -/

/-- A predicate on `ℕ → Color` depends only on a variable set `S : Set ℕ`. -/
def DependsOnlyOn (P : (ℕ → Color) → Prop) (S : Set ℕ) : Prop :=
  ∀ c₁ c₂ : ℕ → Color, (∀ i ∈ S, c₁ i = c₂ i) → P c₁ → P c₂

theorem DependsOnlyOn.iff {P : (ℕ → Color) → Prop} {S : Set ℕ}
    (h : DependsOnlyOn P S) {c₁ c₂ : ℕ → Color} (heq : ∀ i ∈ S, c₁ i = c₂ i) :
    P c₁ ↔ P c₂ :=
  ⟨h c₁ c₂ heq, h c₂ c₁ (fun i hi => (heq i hi).symm)⟩

theorem DependsOnlyOn.mono {P : (ℕ → Color) → Prop} {S₁ S₂ : Set ℕ}
    (h : DependsOnlyOn P S₁) (hsub : S₁ ⊆ S₂) :
    DependsOnlyOn P S₂ :=
  fun c₁ c₂ heq hp => h c₁ c₂ (fun i hi => heq i (hsub hi)) hp

theorem ProjectsTo.refl (P : (ℕ → Color) → Prop) (A : Set ℕ)
    (hdep : DependsOnlyOn P A) :
    ProjectsTo P A P := by
  intro c
  constructor
  · intro hpc
    exact ⟨c, hpc, fun _ _ => rfl⟩
  · rintro ⟨ext, hp_ext, heq⟩
    exact hdep ext c heq hp_ext

theorem ProjectsTo.congr_right {P Q₁ Q₂ : (ℕ → Color) → Prop} {A : Set ℕ}
    (h : ProjectsTo P A Q₁) (hq : ∀ c, Q₁ c ↔ Q₂ c) :
    ProjectsTo P A Q₂ := by
  intro c
  rw [← hq c]
  exact h c

theorem ProjectsTo.congr_left {P₁ P₂ Q : (ℕ → Color) → Prop} {A : Set ℕ}
    (h : ProjectsTo P₁ A Q) (hp : ∀ c, P₁ c ↔ P₂ c) :
    ProjectsTo P₂ A Q := by
  intro c
  rw [h c]
  constructor <;> rintro ⟨ext, hp_ext, heq⟩
  · exact ⟨ext, (hp ext).mp hp_ext, heq⟩
  · exact ⟨ext, (hp ext).mpr hp_ext, heq⟩

theorem ProjectsTo.trans {P Q R : (ℕ → Color) → Prop} {A₁ A₂ : Set ℕ}
    (h1 : ProjectsTo P A₁ Q) (h2 : ProjectsTo Q A₂ R) (hsub : A₂ ⊆ A₁) :
    ProjectsTo P A₂ R := by
  intro c
  rw [h2 c]
  constructor
  · rintro ⟨c₁, hq₁, heq₁⟩
    obtain ⟨c₂, hp₂, heq₂⟩ := (h1 c₁).mp hq₁
    exact ⟨c₂, hp₂, fun i hi => (heq₂ i (hsub hi)).trans (heq₁ i hi)⟩
  · rintro ⟨c₂, hp₂, heq₂⟩
    refine ⟨c₂, (h1 c₂).mpr ⟨c₂, hp₂, fun _ _ => rfl⟩, heq₂⟩

/-- Part II ("Why completed formulas compose"): existential projections over
disjoint variable sets compose with any formula `R` on the active variables. -/
theorem ProjectsTo.conj_disjoint {P₁ P₂ Q₁ Q₂ R : (ℕ → Color) → Prop}
    {V₁ V₂ A₁ A₂ : Set ℕ}
    (h1 : ProjectsTo P₁ A₁ Q₁) (h2 : ProjectsTo P₂ A₂ Q₂)
    (hdep1 : DependsOnlyOn P₁ V₁) (hdep2 : DependsOnlyOn P₂ V₂)
    (hdepR : DependsOnlyOn R (A₁ ∪ A₂))
    (hsub1 : A₁ ⊆ V₁) (hsub2 : A₂ ⊆ V₂) (hdisj : Disjoint V₁ V₂) :
    ProjectsTo (fun c => P₁ c ∧ P₂ c ∧ R c) (A₁ ∪ A₂) (fun c => Q₁ c ∧ Q₂ c ∧ R c) := by
  intro c
  dsimp only
  rw [h1 c, h2 c]
  constructor
  · rintro ⟨⟨c₁, hp₁, heq₁⟩, ⟨c₂, hp₂, heq₂⟩, hrc⟩
    let ext : ℕ → Color := fun i =>
      if i ∈ V₁ \ A₁ then c₁ i
      else if i ∈ V₂ \ A₂ then c₂ i
      else c i
    have hext_A : ∀ i ∈ A₁ ∪ A₂, ext i = c i := by
      intro i hi
      have hnot1 : i ∉ V₁ \ A₁ := by
        rintro ⟨hv1, ha1⟩
        rcases hi with hia1 | hia2
        · exact ha1 hia1
        · exact Set.disjoint_left.mp hdisj hv1 (hsub2 hia2)
      have hnot2 : i ∉ V₂ \ A₂ := by
        rintro ⟨hv2, ha2⟩
        rcases hi with hia1 | hia2
        · exact Set.disjoint_left.mp hdisj (hsub1 hia1) hv2
        · exact ha2 hia2
      simp only [ext, hnot1, hnot2, ↓reduceIte]
    have hext_V1 : ∀ i ∈ V₁, c₁ i = ext i := by
      intro i hi
      by_cases ha1 : i ∈ A₁
      · rw [hext_A i (Or.inl ha1), heq₁ i ha1]
      · have hmem : i ∈ V₁ \ A₁ := ⟨hi, ha1⟩
        simp only [ext, hmem, ↓reduceIte]
    have hext_V2 : ∀ i ∈ V₂, c₂ i = ext i := by
      intro i hi
      by_cases ha2 : i ∈ A₂
      · rw [hext_A i (Or.inr ha2), heq₂ i ha2]
      · have hnot1 : i ∉ V₁ \ A₁ :=
          fun h => Set.disjoint_left.mp hdisj h.1 hi
        have hmem : i ∈ V₂ \ A₂ := ⟨hi, ha2⟩
        simp only [ext, hnot1, hmem, ↓reduceIte]
    refine ⟨ext, ⟨hdep1 c₁ ext hext_V1 hp₁, hdep2 c₂ ext hext_V2 hp₂,
      hdepR c ext (fun i hi => (hext_A i hi).symm) hrc⟩, hext_A⟩
  · rintro ⟨ext, ⟨hp₁, hp₂, hrext⟩, heq⟩
    refine ⟨⟨ext, hp₁, fun i hi => heq i (Or.inl hi)⟩,
      ⟨ext, hp₂, fun i hi => heq i (Or.inr hi)⟩,
      hdepR ext c heq hrext⟩

theorem ProjectsTo.exists_of_empty {P : (ℕ → Color) → Prop}
    (h : ProjectsTo P ∅ (SummaryFormula none)) :
    ∃ c, P c := by
  obtain ⟨ext, hp, _⟩ := (h (fun _ => .left)).mp trivial
  exact ⟨ext, hp⟩

/-! ## Edge Record / Arc Bijection and `SummaryRep` -/

/-- Map an edge record index `i` to an `Arc N` when `N > 0`. -/
def arcOfIdx (N : ℕ) [NeZero N] (s : Search) (i : ℕ) : Arc N :=
  (Fin.ofNat N (s.edges[i]!).source, Fin.ofNat N (s.edges[i]!).target)

/-- Inverse map choosing the edge record index of an `Arc N`. -/
noncomputable def idxOfArc (N : ℕ) [NeZero N] (s : Search) (b : Arc N) : ℕ :=
  if h : ∃ i < s.edges.size, arcOfIdx N s i = b then Classical.choose h else 0

/-- The set of back-edge record indices corresponding to `S : Set (Arc N)`. -/
def edgeSet (N : ℕ) [NeZero N] (s : Search) (S : Set (Arc N)) : Set ℕ :=
  {i | i < s.edges.size ∧ (s.edges[i]!).tree = false ∧ arcOfIdx N s i ∈ S}

/-- Turn an index coloring `c : ℕ → Color` into an arc coloring `Coloring N`. -/
noncomputable def toColoring (N : ℕ) [NeZero N] (s : Search) (c : ℕ → Color) : Coloring N :=
  fun b => c (idxOfArc N s b)

/-- Turn an arc coloring `color : Coloring N` into an index coloring `ℕ → Color`. -/
def ofColoring (N : ℕ) [NeZero N] (s : Search) (color : Coloring N) : ℕ → Color :=
  fun i => color (arcOfIdx N s i)

theorem arcOfIdx_fst_val {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} (hinv : DFSInv N G lists s []) {i : ℕ} (hi : i < s.edges.size) :
    (arcOfIdx N s i).1.val = (s.edges[i]!).source := by
  obtain ⟨hs_lt, _, _⟩ := hinv.edges_valid i hi
  simp [arcOfIdx, Fin.ofNat, Nat.mod_eq_of_lt hs_lt]

theorem arcOfIdx_snd_val {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} (hinv : DFSInv N G lists s []) {i : ℕ} (hi : i < s.edges.size) :
    (arcOfIdx N s i).2.val = (s.edges[i]!).target := by
  obtain ⟨_, ht_lt, _⟩ := hinv.edges_valid i hi
  simp [arcOfIdx, Fin.ofNat, Nat.mod_eq_of_lt ht_lt]

theorem arcOfIdx_inj {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} (hinv : DFSInv N G lists s []) {i j : ℕ}
    (hi : i < s.edges.size) (hj : j < s.edges.size)
    (heq : arcOfIdx N s i = arcOfIdx N s j) : i = j := by
  have h1 : (s.edges[i]!).source = (s.edges[j]!).source := by
    rw [← arcOfIdx_fst_val hinv hi, ← arcOfIdx_fst_val hinv hj, heq]
  have h2 : (s.edges[i]!).target = (s.edges[j]!).target := by
    rw [← arcOfIdx_snd_val hinv hi, ← arcOfIdx_snd_val hinv hj, heq]
  exact hinv.edges_inj i hi j hj h1 h2

theorem idxOfArc_arcOfIdx {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} (hinv : DFSInv N G lists s []) {i : ℕ} (hi : i < s.edges.size) :
    idxOfArc N s (arcOfIdx N s i) = i := by
  unfold idxOfArc
  have hex : ∃ j < s.edges.size, arcOfIdx N s j = arcOfIdx N s i := ⟨i, hi, rfl⟩
  simp only [hex, ↓reduceDIte]
  obtain ⟨hj, hjeq⟩ := Classical.choose_spec hex
  exact arcOfIdx_inj hinv hj hi hjeq

theorem toColoring_arcOfIdx {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} (hinv : DFSInv N G lists s []) (c : ℕ → Color) {i : ℕ} (hi : i < s.edges.size) :
    toColoring N s c (arcOfIdx N s i) = c i := by
  simp [toColoring, idxOfArc_arcOfIdx hinv hi]

theorem arcOfIdx_tree_or_back {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} (hAdj : Compute.IsAdjListFamily G lists)
    (hinv : DFSInv N G lists s []) (hall : ∀ v < N, s.Visited v)
    {i : ℕ} (hi : i < s.edges.size) :
    ((s.edges[i]!).tree = true ∧ (s.forest N).TreeEdge (arcOfIdx N s i)) ∨
    ((s.edges[i]!).tree = false ∧ (s.forest N).BackEdge G (arcOfIdx N s i)) := by
  obtain ⟨hs_lt, ht_lt, _, _, ⟨k, hsc, hk⟩, htree⟩ := hinv.edges_valid i hi
  have hisDFS : (s.forest N).IsDFS G := hinv.isDFS_of_nil hall
  have he_eq : arcOfIdx N s i = (⟨(s.edges[i]!).source, hs_lt⟩, ⟨(s.edges[i]!).target, ht_lt⟩) := by
    ext <;> simp [arcOfIdx_fst_val hinv hi, arcOfIdx_snd_val hinv hi]
  rw [he_eq]
  have hadj : G.Adj ⟨(s.edges[i]!).source, hs_lt⟩ ⟨(s.edges[i]!).target, ht_lt⟩ := by
    rw [← adj_mem_iff hAdj hs_lt ht_lt, ← hk]
    rcases hsc with ⟨_, hk_len, _⟩
    rw [getElem!_pos _ k hk_len]
    exact List.getElem_mem hk_len
  cases htr_bool : (s.edges[i]!).tree
  · right
    simp only [htr_bool, Bool.false_eq_true, ↓reduceIte] at htree
    refine ⟨rfl, hadj, ?_, htree.2, ?_⟩
    · rcases hisDFS.2.2 _ _ hadj with h1 | h2
      · have hd_le := Forest.depth_le_of_ancestor hinv.depth_step h1
        exact absurd hd_le (by omega)
      · exact h2
    · intro hpar
      exact htree.1 ((hinv.forest_parent_some_iff _ _).mp hpar)
  · left
    simp only [htr_bool, ↓reduceIte] at htree
    exact ⟨rfl, (hinv.forest_parent_some_iff _ _).mpr htree.1⟩

theorem exists_idx_of_tree_or_back {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : Search} (hAdj : Compute.IsAdjListFamily G lists)
    (hinv : DFSInv N G lists s []) (hall : ∀ v < N, s.Visited v)
    {b : Arc N} (hb : (s.forest N).TreeEdge b ∨ (s.forest N).BackEdge G b) :
    ∃ i < s.edges.size, arcOfIdx N s i = b ∧
      ((b ∈ {e | (s.forest N).TreeEdge e} → (s.edges[i]!).tree = true) ∧
       (b ∈ {e | (s.forest N).BackEdge G e} → (s.edges[i]!).tree = false)) := by
  rcases hb with hte | hbe
  · have hp : s.parent[b.2.val]?.join = some b.1.val :=
      (hinv.forest_parent_some_iff b.1 b.2).mp hte
    obtain ⟨i, hi_lt, htr, hsrc, htg⟩ := (hinv.parent_iff_edge b.2.val b.2.2 b.1.val).mp hp
    have harc : arcOfIdx N s i = b := by
      ext
      · rw [arcOfIdx_fst_val hinv hi_lt, hsrc]
      · rw [arcOfIdx_snd_val hinv hi_lt, htg]
    refine ⟨i, hi_lt, harc, fun _ => htr, ?_⟩
    intro hbe'
    have hstep := hinv.depth_step b.1 b.2 hte
    have hlt := hbe'.2.2.1
    omega
  · rcases hbe with ⟨hadj, hanc, hd_lt, hnp⟩
    have hmem : b.2.val ∈ (List.ofFn lists).toArray[b.1.val]! :=
      (adj_mem_iff hAdj b.1.2 b.2.2).mpr hadj
    obtain ⟨k, hk_lt, hget⟩ := List.getElem_of_mem hmem
    have hb1_post : b.1.val ∈ s.postorder := by
      have := (hinv.visited_iff b.1.val).mp (hall b.1.val b.1.2)
      simpa using this
    have hsc : Scanned N lists s [] b.1.val k := ⟨b.1.2, hk_lt, Or.inl hb1_post⟩
    have hget! : ((List.ofFn lists).toArray[b.1.val]!)[k]! = b.2.val := by
      rw [getElem!_pos _ k hk_lt, hget]
    have hb2' : ((List.ofFn lists).toArray[b.1.val]!)[k]! < N := by
      rw [hget!]; exact b.2.2
    have hnp' : s.parent[b.1.val]?.join ≠ some b.2.val :=
      fun h => hnp ((hinv.forest_parent_some_iff b.2 b.1).mpr h)
    have hcond : s.parent[b.1.val]?.join ≠ some ((List.ofFn lists).toArray[b.1.val]!)[k]! ∧
        (s.forest N).depth ⟨((List.ofFn lists).toArray[b.1.val]!)[k]!, hb2'⟩ <
          (s.forest N).depth b.1 := by
      refine ⟨by rw [hget!]; exact hnp', ?_⟩
      convert hd_lt using 2
      exact Fin.ext hget!
    obtain ⟨i, hi_lt, hsrc, htg⟩ := hinv.scanned_edge_exists b.1.val k hsc b.1.2 hb2' (Or.inr hcond)
    rw [hget!] at htg
    have harc : arcOfIdx N s i = b := by
      ext
      · rw [arcOfIdx_fst_val hinv hi_lt, hsrc]
      · rw [arcOfIdx_snd_val hinv hi_lt, htg]
    rcases arcOfIdx_tree_or_back hAdj hinv hall hi_lt with ⟨htr, hte⟩ | ⟨htr, _⟩
    · rw [harc] at hte
      have hstep := hinv.depth_step b.1 b.2 hte
      omega
    · refine ⟨i, hi_lt, harc, ?_, fun _ => htr⟩
      intro hte
      have hstep := hinv.depth_step b.1 b.2 hte
      omega

theorem idxOfArc_spec {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} (hAdj : Compute.IsAdjListFamily G lists)
    (hinv : DFSInv N G lists s []) (hall : ∀ v < N, s.Visited v)
    {b : Arc N} (hb : (s.forest N).TreeEdge b ∨ (s.forest N).BackEdge G b) :
    idxOfArc N s b < s.edges.size ∧ arcOfIdx N s (idxOfArc N s b) = b := by
  obtain ⟨i, hi_lt, harc, _⟩ := exists_idx_of_tree_or_back hAdj hinv hall hb
  have hex : ∃ j < s.edges.size, arcOfIdx N s j = b := ⟨i, hi_lt, harc⟩
  unfold idxOfArc
  simp only [hex, ↓reduceDIte]
  exact Classical.choose_spec hex

theorem idxOfArc_mem_edgeSet {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} (hAdj : Compute.IsAdjListFamily G lists)
    (hinv : DFSInv N G lists s []) (hall : ∀ v < N, s.Visited v)
    {S : Set (Arc N)} (hsub : S ⊆ {b | (s.forest N).BackEdge G b}) {b : Arc N} (hb : b ∈ S) :
    idxOfArc N s b ∈ edgeSet N s S := by
  have hb_back : (s.forest N).BackEdge G b := hsub hb
  obtain ⟨hi_lt, harc⟩ := idxOfArc_spec hAdj hinv hall (Or.inr hb_back)
  rcases arcOfIdx_tree_or_back hAdj hinv hall hi_lt with ⟨htr, hte⟩ | ⟨htr, _⟩
  · rw [harc] at hte
    have hstep := hinv.depth_step b.1 b.2 hte
    have hlt := hb_back.2.2.1
    omega
  · exact ⟨hi_lt, htr, harc.symm ▸ hb⟩

theorem monochromatic_edgeSet_iff {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : Search} (hAdj : Compute.IsAdjListFamily G lists)
    (hinv : DFSInv N G lists s []) (hall : ∀ v < N, s.Visited v)
    {S : Set (Arc N)} (hsub : S ⊆ {b | (s.forest N).BackEdge G b}) (c : ℕ → Color) :
    Monochromatic c (edgeSet N s S) ↔ Monochromatic (toColoring N s c) S := by
  constructor
  · intro hmono b₁ hb₁ b₂ hb₂
    exact hmono (idxOfArc N s b₁) (idxOfArc_mem_edgeSet hAdj hinv hall hsub hb₁)
      (idxOfArc N s b₂) (idxOfArc_mem_edgeSet hAdj hinv hall hsub hb₂)
  · intro hmono i₁ ⟨hi₁_lt, _, hi₁_in⟩ i₂ ⟨hi₂_lt, _, hi₂_in⟩
    rw [← toColoring_arcOfIdx hinv c hi₁_lt, ← toColoring_arcOfIdx hinv c hi₂_lt]
    exact hmono (arcOfIdx N s i₁) hi₁_in (arcOfIdx N s i₂) hi₂_in

theorem opp_edgeSet_iff {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : Search} (hAdj : Compute.IsAdjListFamily G lists)
    (hinv : DFSInv N G lists s []) (hall : ∀ v < N, s.Visited v)
    {S₁ S₂ : Set (Arc N)} (hsub₁ : S₁ ⊆ {b | (s.forest N).BackEdge G b})
    (hsub₂ : S₂ ⊆ {b | (s.forest N).BackEdge G b}) (c : ℕ → Color) :
    (∀ i ∈ edgeSet N s S₁, ∀ j ∈ edgeSet N s S₂, c i ≠ c j) ↔
      (∀ b₁ ∈ S₁, ∀ b₂ ∈ S₂, toColoring N s c b₁ ≠ toColoring N s c b₂) := by
  constructor
  · intro hopp b₁ hb₁ b₂ hb₂
    exact hopp (idxOfArc N s b₁) (idxOfArc_mem_edgeSet hAdj hinv hall hsub₁ hb₁)
      (idxOfArc N s b₂) (idxOfArc_mem_edgeSet hAdj hinv hall hsub₂ hb₂)
  · intro hopp i₁ ⟨hi₁_lt, _, hi₁_in⟩ i₂ ⟨hi₂_lt, _, hi₂_in⟩
    rw [← toColoring_arcOfIdx hinv c hi₁_lt, ← toColoring_arcOfIdx hinv c hi₂_lt]
    exact hopp (arcOfIdx N s i₁) hi₁_in (arcOfIdx N s i₂) hi₂_in

/-- Part II (I1, I3, I4): exact structural invariant relating a physical
`Option Summary` to the active back-edge set `S : Set (Arc N)` it represents. -/
structure SummaryRep (N : ℕ) [NeZero N] (G : SimpleGraph (Fin N))
    (s : Search) (sum : Option Summary) (S : Set (Arc N)) : Prop where
  sub_back : S ⊆ {b | (s.forest N).BackEdge G b}
  nodes_wf : ∀ b ∈ summaryNodes sum,
    b.edge < s.edges.size ∧
    (s.edges[b.edge]!).tree = false ∧
    b.depth = (s.forest N).depth (arcOfIdx N s b.edge).2
  nodes_eq : nodeSet (summaryNodes sum) = edgeSet N s S
  none_iff : sum = none ↔ S = ∅
  some_spec : ∀ t, sum = some t →
    t.Valid ∧
    (∀ b ∈ S, t.least ≤ (s.forest N).depth b.2) ∧
    (∃ b ∈ S, (s.forest N).depth b.2 = t.least) ∧
    nodeSet t.anchor =
      edgeSet N s {b | b ∈ S ∧ ∀ b' ∈ S, (s.forest N).depth b.2 ≤ (s.forest N).depth b'.2}

theorem SummaryRep.dependsOnlyOn {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {s : Search} {sum : Option Summary} {S : Set (Arc N)}
    (hrep : SummaryRep N G s sum S) :
    DependsOnlyOn (SummaryFormula sum) (edgeSet N s S) := by
  intro c₁ c₂ heq hform
  rcases sum with _ | t
  · trivial
  · have hnodes : nodeSet t.nodes = edgeSet N s S := hrep.nodes_eq
    have heq' : ∀ i ∈ nodeSet t.nodes, c₁ i = c₂ i := hnodes.symm ▸ heq
    refine ⟨hform.1.congr_on (fun i hi => heq' i (by simp [Summary.nodes, hi])), ?_⟩
    intro q hq
    refine (hform.2 q hq).congr_on (fun i hi => heq' i ?_)
    rw [Summary.nodes, nodeSet_append]
    right
    rw [mem_nodeSet_iff, List.mem_map] at hi ⊢
    rcases hi with ⟨b, hb, rfl⟩
    exact ⟨b, List.mem_flatMap.mpr ⟨q, hq, hb⟩, rfl⟩

theorem SummaryRep.filter_gt_eq {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {s : Search} {t : Summary} {S : Set (Arc N)}
    (hrep : SummaryRep N G s (some t) S) (d : ℕ) :
    nodeSet (t.nodes.filter (fun b => decide (d < b.depth))) =
      edgeSet N s {b | b ∈ S ∧ d < (s.forest N).depth b.2} := by
  have hnodes : nodeSet t.nodes = edgeSet N s S := hrep.nodes_eq
  ext i
  simp only [mem_nodeSet_iff, List.mem_map, List.mem_filter, decide_eq_true_eq,
    edgeSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨b, ⟨hb_mem, hd_lt⟩, rfl⟩
    have hwf := hrep.nodes_wf b hb_mem
    have hin : b.edge ∈ nodeSet t.nodes := by
      rw [mem_nodeSet_iff]; exact List.mem_map_of_mem hb_mem
    rw [hnodes] at hin
    exact ⟨hwf.1, hwf.2.1, hin.2.2, hwf.2.2 ▸ hd_lt⟩
  · rintro ⟨hi_lt, htr, hb_S, hd_lt⟩
    have hin : i ∈ edgeSet N s S := ⟨hi_lt, htr, hb_S⟩
    rw [← hnodes, mem_nodeSet_iff, List.mem_map] at hin
    rcases hin with ⟨b, hb_mem, rfl⟩
    have hwf := hrep.nodes_wf b hb_mem
    exact ⟨b, ⟨hb_mem, hwf.2.2.symm ▸ hd_lt⟩, rfl⟩

theorem SummaryRep.filter_lt_eq {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {s : Search} {t : Summary} {S : Set (Arc N)}
    (hrep : SummaryRep N G s (some t) S) (d : ℕ) :
    nodeSet (t.nodes.filter (fun b => decide (b.depth < d))) =
      edgeSet N s {b | b ∈ S ∧ (s.forest N).depth b.2 < d} := by
  have hnodes : nodeSet t.nodes = edgeSet N s S := hrep.nodes_eq
  ext i
  simp only [mem_nodeSet_iff, List.mem_map, List.mem_filter, decide_eq_true_eq,
    edgeSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨b, ⟨hb_mem, hd_lt⟩, rfl⟩
    have hwf := hrep.nodes_wf b hb_mem
    have hin : b.edge ∈ nodeSet t.nodes := by
      rw [mem_nodeSet_iff]; exact List.mem_map_of_mem hb_mem
    rw [hnodes] at hin
    exact ⟨hwf.1, hwf.2.1, hin.2.2, hwf.2.2 ▸ hd_lt⟩
  · rintro ⟨hi_lt, htr, hb_S, hd_lt⟩
    have hin : i ∈ edgeSet N s S := ⟨hi_lt, htr, hb_S⟩
    rw [← hnodes, mem_nodeSet_iff, List.mem_map] at hin
    rcases hin with ⟨b, hb_mem, rfl⟩
    have hwf := hrep.nodes_wf b hb_mem
    exact ⟨b, ⟨hb_mem, hwf.2.2.symm ▸ hd_lt⟩, rfl⟩

/-! ## Preservation of `SummaryRep` under `none`, Back Edges, `trim`, and `merge` -/

theorem SummaryRep.none {N : ℕ} [NeZero N] (G : SimpleGraph (Fin N)) (s : Search) :
    SummaryRep N G s none ∅ where
  sub_back := Set.empty_subset _
  nodes_wf b hb := by simp [summaryNodes] at hb
  nodes_eq := by simp [summaryNodes, nodeSet, edgeSet]
  none_iff := by simp
  some_spec t ht := by cases ht

theorem Forest.returns_eq_singleton_of_backEdge {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hDFS : T.IsDFS G) {e : Arc N} (he : T.BackEdge G e) :
    T.returns G e = {e} := by
  ext b
  simp only [Forest.returns, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, ⟨_, rfl⟩ | ⟨hte, _, _⟩⟩
    · rfl
    · have hstep := T.depth_step_of_isDFS hDFS e.1 e.2 hte
      have hlt := he.2.2.1
      omega
  · rintro rfl
    exact ⟨he, Or.inl ⟨he, rfl⟩⟩

theorem edgeSet_singleton_of_back {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : Search} (hinv : DFSInv N G lists s [])
    {i : ℕ} (hi : i < s.edges.size) (htr : (s.edges[i]!).tree = false) :
    edgeSet N s {arcOfIdx N s i} = {i} := by
  ext j
  simp only [edgeSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hj, _, heq⟩
    exact arcOfIdx_inj hinv hj hi heq
  · rintro rfl
    exact ⟨hi, htr, rfl⟩

theorem edgeSet_disjoint {N : ℕ} [NeZero N] {s : Search} {S₁ S₂ : Set (Arc N)}
    (h : Disjoint S₁ S₂) : Disjoint (edgeSet N s S₁) (edgeSet N s S₂) := by
  rw [Set.disjoint_left] at h ⊢
  intro i hi₁ hi₂
  exact h hi₁.2.2 hi₂.2.2

theorem edgeSet_union {N : ℕ} [NeZero N] (s : Search) (S₁ S₂ : Set (Arc N)) :
    edgeSet N s (S₁ ∪ S₂) = edgeSet N s S₁ ∪ edgeSet N s S₂ := by
  ext i
  simp only [edgeSet, Set.mem_ofPred_eq, Set.mem_union]
  tauto

theorem summaryFormula_singleton (d i : ℕ) (c : ℕ → Color) :
    SummaryFormula (some ⟨d, [⟨i, d⟩], []⟩) c := by
  refine ⟨?_, by simp⟩
  intro x hx y hy
  simp only [mem_nodeSet_iff, List.map_cons, List.map_nil, List.mem_singleton] at hx hy
  rw [hx, hy]

theorem SummaryRep.singleton_back {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : Search} (hAdj : Compute.IsAdjListFamily G lists)
    (hinv : DFSInv N G lists s []) (hall : ∀ v < N, s.Visited v)
    {i : ℕ} (hi : i < s.edges.size) (htr : (s.edges[i]!).tree = false) :
    let d := (s.depth[(s.edges[i]!).target]?.join).getD 0
    SummaryRep N G s (some ⟨d, [⟨i, d⟩], []⟩) ((s.forest N).returns G (arcOfIdx N s i)) := by
  intro d
  have hDFS : (s.forest N).IsDFS G := hinv.isDFS_of_nil hall
  have hbe : (s.forest N).BackEdge G (arcOfIdx N s i) := by
    rcases arcOfIdx_tree_or_back hAdj hinv hall hi with ⟨h1, _⟩ | ⟨_, hbe⟩
    · rw [htr] at h1; cases h1
    · exact hbe
  have hret : (s.forest N).returns G (arcOfIdx N s i) = {arcOfIdx N s i} :=
    Forest.returns_eq_singleton_of_backEdge hDFS hbe
  have hd_eq : d = (s.forest N).depth (arcOfIdx N s i).2 := by
    dsimp [d, Search.forest]
    rw [arcOfIdx_snd_val hinv hi]
  have hedge_eq : edgeSet N s {arcOfIdx N s i} = {i} :=
    edgeSet_singleton_of_back hinv hi htr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hret]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    exact hb ▸ hbe
  · intro b hb
    simp only [summaryNodes, Summary.nodes, List.flatMap_nil, List.append_nil,
      List.mem_singleton] at hb
    subst hb
    exact ⟨hi, htr, hd_eq⟩
  · rw [hret, hedge_eq]
    ext j
    simp [summaryNodes, Summary.nodes]
  · simp [hret]
  · intro t ht
    injection ht with ht_eq
    subst ht_eq
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨by simp, ?_, by simp, by simp, by simp [Summary.nodes]⟩
      intro b hb
      simp only [List.mem_singleton] at hb
      subst hb
      rfl
    · intro b hb
      rw [hret, Set.mem_singleton_iff] at hb
      subst hb
      exact le_of_eq hd_eq
    · exact ⟨arcOfIdx N s i, by simp [hret], hd_eq.symm⟩
    · have hmin_eq :
          {b | b ∈ (s.forest N).returns G (arcOfIdx N s i) ∧
            ∀ b' ∈ (s.forest N).returns G (arcOfIdx N s i),
              (s.forest N).depth b.2 ≤ (s.forest N).depth b'.2} = {arcOfIdx N s i} := by
        ext b
        simp only [hret, Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq, and_iff_left_iff_imp]
        rintro rfl
        exact le_rfl
      rw [hmin_eq, hedge_eq]
      ext j
      simp

theorem mem_trimBlocks_flatMap {c : ℕ} {blocks : List Block} {b : ReturnNode}
    (hb : b ∈ (trimBlocks c blocks).flatMap Block.nodes) :
    b ∈ blocks.flatMap Block.nodes := by
  induction blocks with
  | nil => simp [trimBlocks] at hb
  | cons q rest ih =>
    unfold trimBlocks at hb
    split_ifs at hb with hmin
    · exact List.mem_append_right _ (ih hb)
    · simp only [List.flatMap_cons, List.mem_append] at hb ⊢
      rcases hb with hb_q | hb_rest
      · left
        simp only [Block.nodes, List.mem_append] at hb_q ⊢
        rcases hb_q with hbL | hbR
        · exact Or.inl ((List.dropWhile_sublist _).subset hbL)
        · exact Or.inr ((List.dropWhile_sublist _).subset hbR)
      · exact Or.inr hb_rest

theorem SummaryRep.trim {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {s : Search} {sum : Option Summary} {S : Set (Arc N)}
    (hrep : SummaryRep N G s sum S) (d : ℕ)
    (hd_le : ∀ b ∈ S, (s.forest N).depth b.2 ≤ d) :
    SummaryRep N G s (LRPlanarity.trim sum d) {b | b ∈ S ∧ (s.forest N).depth b.2 < d} ∧
    ProjectsTo (SummaryFormula sum)
      (edgeSet N s {b | b ∈ S ∧ (s.forest N).depth b.2 < d})
      (SummaryFormula (LRPlanarity.trim sum d)) := by
  rcases sum with _ | t
  · have hS_emp : S = ∅ := hrep.none_iff.mp rfl
    have hS'_emp : {b | b ∈ S ∧ (s.forest N).depth b.2 < d} = ∅ := by simp [hS_emp]
    rw [hS'_emp]
    refine ⟨SummaryRep.none G s, ?_⟩
    intro c
    exact ⟨fun _ => ⟨c, trivial, fun _ _ => rfl⟩, fun _ => trivial⟩
  · obtain ⟨ht_valid, hleast_le, ⟨b₀, hb₀_S, hb₀_depth⟩, hanc_eq⟩ := hrep.some_spec t rfl
    have ht_least_le : t.least ≤ d := hb₀_depth ▸ hd_le b₀ hb₀_S
    have ht_nodes_le : ∀ b ∈ t.nodes, b.depth ≤ d := by
      intro b hb
      have hwf := hrep.nodes_wf b hb
      have hin : b.edge ∈ nodeSet (summaryNodes (some t)) := by
        rw [mem_nodeSet_iff]; exact List.mem_map_of_mem hb
      rw [hrep.nodes_eq] at hin
      rw [hwf.2.2]
      exact hd_le (arcOfIdx N s b.edge) hin.2.2
    obtain ⟨hproj, hnodes_trim, hvalid_trim⟩ := trimStatement t d ht_valid ht_nodes_le
    rw [hrep.filter_lt_eq d] at hproj hnodes_trim
    refine ⟨⟨?_, ?_, hnodes_trim, ?_, ?_⟩, hproj⟩
    · intro b hb; exact hrep.sub_back hb.1
    · intro b hb
      dsimp [LRPlanarity.trim] at hb
      split_ifs at hb with hleast_eq
      · simp [summaryNodes] at hb
      · simp only [summaryNodes, Summary.nodes, List.mem_append] at hb
        apply hrep.nodes_wf b
        simp only [summaryNodes, Summary.nodes, List.mem_append]
        rcases hb with hb_anc | hb_blk
        · exact Or.inl hb_anc
        · exact Or.inr (mem_trimBlocks_flatMap hb_blk)
    · dsimp [LRPlanarity.trim]
      split_ifs with hleast_eq
      · simp only [true_iff, Set.eq_empty_iff_forall_notMem, Set.mem_ofPred_eq, not_and]
        intro b hb_S
        have := hleast_le b hb_S
        omega
      · simp only [false_iff, Set.eq_empty_iff_forall_notMem, Set.mem_ofPred_eq,
          not_forall, not_not]
        exact ⟨b₀, hb₀_S, by omega⟩
    · intro t' ht'
      have ht'_valid : t'.Valid := hvalid_trim t' ht'
      dsimp [LRPlanarity.trim] at ht'
      split_ifs at ht' with hleast_eq
      injection ht' with ht'_eq
      subst ht'_eq
      have hlt_d : t.least < d := lt_of_le_of_ne ht_least_le hleast_eq
      refine ⟨ht'_valid, ?_, ?_, ?_⟩
      · intro b hb
        exact hleast_le b hb.1
      · exact ⟨b₀, ⟨hb₀_S, hb₀_depth ▸ hlt_d⟩, hb₀_depth⟩
      · dsimp only
        rw [hanc_eq]
        congr 1
        ext b
        simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨hb_S, hb_min⟩
          have hb_le_b₀ : (s.forest N).depth b.2 ≤ t.least := hb₀_depth ▸ hb_min b₀ hb₀_S
          refine ⟨⟨hb_S, lt_of_le_of_lt hb_le_b₀ hlt_d⟩, ?_⟩
          intro b' hb'
          exact hb_min b' hb'.1
        · rintro ⟨⟨hb_S, _⟩, hb_min'⟩
          refine ⟨hb_S, ?_⟩
          intro b' hb'_S
          have hb₀_in : b₀ ∈ S ∧ (s.forest N).depth b₀.2 < d := ⟨hb₀_S, hb₀_depth ▸ hlt_d⟩
          have hb_le_b₀ := hb_min' b₀ hb₀_in
          have hb₀_le_b' := hb₀_depth.symm ▸ hleast_le b' hb'_S
          exact le_trans hb_le_b₀ hb₀_le_b'

theorem merge_some_some_spec {old new : Summary} {res : Option Summary}
    (h : merge (some old) (some new) = some res) :
    ∃ merged : Summary,
      res = some merged ∧
      merged.least = old.least ∧
      merged.anchor = (if new.least = old.least then old.anchor ++ new.anchor else old.anchor) ∧
      merged.nodes.Perm (old.nodes ++ new.nodes) := by
  rcases hchild : mergeChild new.blocks [] with _ | right₀
  · simp [merge, hchild] at h
  · obtain ⟨_, hright₀_eq⟩ := (mergeChild_eq_some_iff new.blocks [] right₀).mp hchild
    rw [List.nil_append] at hright₀_eq
    let anchor := if new.least = old.least then old.anchor ++ new.anchor else old.anchor
    let right₁ := if new.least = old.least then right₀ else right₀ ++ new.anchor
    rcases hold_base : mergeOld new.least old.blocks [] [] with _ | ⟨rem, L, R⟩
    · have hold_merge : mergeOld new.least old.blocks [] right₁ = none := by
        rw [mergeOld_acc, hold_base]; rfl
      simp [merge, hchild, right₁, hold_merge] at h
    · obtain ⟨popped, hold_blocks_eq, _, hL_eq, hR_eq, _⟩ := mergeOld_eq_some hold_base
      let blocks' := if L.isEmpty && (right₁ ++ R).isEmpty then rem else ⟨L, right₁ ++ R⟩ :: rem
      let merged : Summary := ⟨old.least, anchor, blocks'⟩
      have hold_merge : mergeOld new.least old.blocks [] right₁ = some (rem, L, right₁ ++ R) := by
        rw [mergeOld_acc, hold_base]; rfl
      have hmerge : merge (some old) (some new) = some (some merged) := by
        simp [merge, hchild, anchor, right₁, hold_merge, blocks', merged]
      rw [hmerge] at h
      injection h with hres
      subst hres
      refine ⟨merged, rfl, rfl, rfl, ?_⟩
      have hblocks'_flatMap :
          blocks'.flatMap Block.nodes = L ++ (right₁ ++ R) ++ rem.flatMap Block.nodes := by
        unfold blocks'
        split_ifs with hemp
        · simp only [Bool.and_eq_true, List.isEmpty_iff] at hemp
          simp [hemp.1, hemp.2]
        · simp [Block.nodes, List.append_assoc]
      have hLR_perm : (L ++ R).Perm (popped.flatMap Block.nodes) := by
        rw [hL_eq, hR_eq]
        exact flatMap_orientBlock_perm new.least popped
      have hanc_right₁_perm : (anchor ++ right₁).Perm (old.anchor ++ new.nodes) := by
        by_cases heq : new.least = old.least
        · simp only [anchor, right₁, heq, ↓reduceIte, hright₀_eq, Summary.nodes, List.append_assoc]
          exact List.Perm.refl _
        · simp only [anchor, right₁, heq, ↓reduceIte, hright₀_eq, Summary.nodes]
          exact List.Perm.append_left old.anchor List.perm_append_comm
      unfold Summary.nodes
      dsimp [merged]
      rw [hblocks'_flatMap]
      have hrearr :
          (anchor ++ (L ++ (right₁ ++ R) ++ rem.flatMap Block.nodes)).Perm
          ((anchor ++ right₁) ++ ((L ++ R) ++ rem.flatMap Block.nodes)) := by
        simp only [List.append_assoc]
        refine List.Perm.append_left anchor ?_
        have h1 : (L ++ (right₁ ++ (R ++ rem.flatMap Block.nodes))).Perm
            (right₁ ++ (L ++ (R ++ rem.flatMap Block.nodes))) :=
          List.perm_append_comm_assoc L right₁ (R ++ rem.flatMap Block.nodes)
        simpa [List.append_assoc] using h1
      have hold_blk_perm :
          ((L ++ R) ++ rem.flatMap Block.nodes).Perm (old.blocks.flatMap Block.nodes) := by
        rw [hold_blocks_eq, List.flatMap_append]
        exact hLR_perm.append_right (rem.flatMap Block.nodes)
      have hstep := hrearr.trans (hanc_right₁_perm.append hold_blk_perm)
      refine hstep.trans ?_
      simp only [List.append_assoc]
      exact List.Perm.append_left old.anchor List.perm_append_comm

theorem SummaryRep.merge_some {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : Search}
    (hAdj : Compute.IsAdjListFamily G lists)
    (hinv : DFSInv N G lists s []) (hall : ∀ v < N, s.Visited v)
    {old new : Summary} {S₁ S₂ : Set (Arc N)}
    (hrep₁ : SummaryRep N G s (some old) S₁)
    (hrep₂ : SummaryRep N G s (some new) S₂)
    (hdisj : Disjoint S₁ S₂)
    (hleast : old.least ≤ new.least)
    (hUB : (∃ b ∈ S₁, new.least < (s.forest N).depth b.2) →
           (∃ b ∈ S₂, old.least < (s.forest N).depth b.2)) :
    match merge (some old) (some new) with
    | Option.none => ¬ ∃ color, MergeFormula old new color
    | some res =>
      (∀ color, SummaryFormula res color ↔ MergeFormula old new color) ∧
      SummaryRep N G s res (S₁ ∪ S₂) := by
  obtain ⟨hold_valid, hold_least_le, ⟨b₁, hb₁_S₁, hb₁_depth⟩, hold_anc_eq⟩ := hrep₁.some_spec old rfl
  obtain ⟨hnew_valid, hnew_least_le, ⟨b₂, hb₂_S₂, hb₂_depth⟩, hnew_anc_eq⟩ := hrep₂.some_spec new rfl
  have hnodup : ((old.nodes ++ new.nodes).map ReturnNode.edge).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨hold_valid.2.2.2.2, hnew_valid.2.2.2.2, ?_⟩
    intro i hi j hj hij
    subst hij
    have hi_set : i ∈ edgeSet N s S₁ := by
      rw [← hrep₁.nodes_eq, mem_nodeSet_iff]; exact hi
    have hj_set : i ∈ edgeSet N s S₂ := by
      rw [← hrep₂.nodes_eq, mem_nodeSet_iff]; exact hj
    exact Set.disjoint_left.mp (edgeSet_disjoint hdisj) hi_set hj_set
  have hUB_nodes :
      (∃ b ∈ old.nodes, new.least < b.depth) → (∃ b ∈ new.nodes, old.least < b.depth) := by
    rintro ⟨x, hx_old, hx_gt⟩
    have hx_in : x.edge ∈ nodeSet (old.nodes.filter (fun b => decide (new.least < b.depth))) := by
      rw [mem_nodeSet_iff, List.mem_map]
      exact ⟨x, List.mem_filter.mpr ⟨hx_old, decide_eq_true hx_gt⟩, rfl⟩
    rw [hrep₁.filter_gt_eq new.least] at hx_in
    obtain ⟨b', hb'_S₂, hb'_gt⟩ := hUB ⟨arcOfIdx N s x.edge, hx_in.2.2.1, hx_in.2.2.2⟩
    have hb'_idx : idxOfArc N s b' ∈ edgeSet N s {b | b ∈ S₂ ∧ old.least < (s.forest N).depth b.2} := by
      have hmem := idxOfArc_mem_edgeSet hAdj hinv hall hrep₂.sub_back hb'_S₂
      have hspec := idxOfArc_spec hAdj hinv hall (Or.inr (hrep₂.sub_back hb'_S₂))
      exact ⟨hmem.1, hmem.2.1, hmem.2.2, hspec.2.symm ▸ hb'_gt⟩
    rw [← hrep₂.filter_gt_eq old.least, mem_nodeSet_iff, List.mem_map] at hb'_idx
    rcases hb'_idx with ⟨y, hy_filt, _⟩
    rw [List.mem_filter, decide_eq_true_eq] at hy_filt
    exact ⟨y, hy_filt.1, hy_filt.2⟩
  have hstmt := mergeStatement old new hold_valid hnew_valid hleast hnodup hUB_nodes
  rcases hmerge : merge (some old) (some new) with _ | res
  · rw [hmerge] at hstmt
    exact hstmt
  · rw [hmerge] at hstmt
    rcases hstmt with ⟨hform_iff, hvalid_res, hnodes_res⟩
    obtain ⟨merged, rfl, hmerged_least, hmerged_anc, hmerged_perm⟩ := merge_some_some_spec hmerge
    refine ⟨hform_iff, ?_⟩
    have hmerged_valid : merged.Valid := hvalid_res merged rfl
    refine ⟨Set.union_subset hrep₁.sub_back hrep₂.sub_back, ?_, ?_, ?_, ?_⟩
    · intro b hb
      have hb_app : b ∈ old.nodes ++ new.nodes := hmerged_perm.subset hb
      rcases List.mem_append.mp hb_app with hb_old | hb_new
      · exact hrep₁.nodes_wf b hb_old
      · exact hrep₂.nodes_wf b hb_new
    · rw [hnodes_res, nodeSet_append, show nodeSet old.nodes = edgeSet N s S₁ from hrep₁.nodes_eq,
        show nodeSet new.nodes = edgeSet N s S₂ from hrep₂.nodes_eq, ← edgeSet_union]
    · simp only [reduceCtorEq, false_iff]
      intro hemp
      have : b₁ ∈ (∅ : Set (Arc N)) := hemp ▸ Or.inl hb₁_S₁
      exact this
    · intro t ht
      injection ht with ht_eq
      subst ht_eq
      refine ⟨hmerged_valid, ?_, ?_, ?_⟩
      · intro b hb
        rw [hmerged_least]
        rcases hb with hb_S₁ | hb_S₂
        · exact hold_least_le b hb_S₁
        · exact le_trans hleast (hnew_least_le b hb_S₂)
      · exact ⟨b₁, Or.inl hb₁_S₁, hb₁_depth.trans hmerged_least.symm⟩
      · rw [hmerged_anc]
        by_cases heq : new.least = old.least
        · simp only [heq, ↓reduceIte, nodeSet_append, hold_anc_eq, hnew_anc_eq, ← edgeSet_union]
          congr 1
          ext b
          simp only [Set.mem_union, Set.mem_ofPred_eq]
          constructor
          · rintro (⟨hb_S₁, hb_min₁⟩ | ⟨hb_S₂, hb_min₂⟩)
            · refine ⟨Or.inl hb_S₁, ?_⟩
              rintro b' (hb'_S₁ | hb'_S₂)
              · exact hb_min₁ b' hb'_S₁
              · have h1 : (s.forest N).depth b.2 ≤ old.least := hb₁_depth ▸ hb_min₁ b₁ hb₁_S₁
                have h2 : old.least ≤ (s.forest N).depth b'.2 := heq ▸ hnew_least_le b' hb'_S₂
                exact le_trans h1 h2
            · refine ⟨Or.inr hb_S₂, ?_⟩
              rintro b' (hb'_S₁ | hb'_S₂)
              · have h1 : (s.forest N).depth b.2 ≤ old.least :=
                  heq ▸ hb₂_depth ▸ hb_min₂ b₂ hb₂_S₂
                have h2 : old.least ≤ (s.forest N).depth b'.2 := hold_least_le b' hb'_S₁
                exact le_trans h1 h2
              · exact hb_min₂ b' hb'_S₂
          · rintro ⟨hb_S₁ | hb_S₂, hb_min⟩
            · exact Or.inl ⟨hb_S₁, fun b' hb' => hb_min b' (Or.inl hb')⟩
            · exact Or.inr ⟨hb_S₂, fun b' hb' => hb_min b' (Or.inr hb')⟩
        · simp only [heq, ↓reduceIte, hold_anc_eq]
          have hlt : old.least < new.least := lt_of_le_of_ne hleast (Ne.symm heq)
          congr 1
          ext b
          simp only [Set.mem_ofPred_eq, Set.mem_union]
          constructor
          · rintro ⟨hb_S₁, hb_min₁⟩
            refine ⟨Or.inl hb_S₁, ?_⟩
            rintro b' (hb'_S₁ | hb'_S₂)
            · exact hb_min₁ b' hb'_S₁
            · have h1 : (s.forest N).depth b.2 ≤ old.least := hb₁_depth ▸ hb_min₁ b₁ hb₁_S₁
              have h2 : new.least ≤ (s.forest N).depth b'.2 := hnew_least_le b' hb'_S₂
              exact le_trans h1 (le_trans (le_of_lt hlt) h2)
          · rintro ⟨hb_S₁ | hb_S₂, hb_min⟩
            · exact ⟨hb_S₁, fun b' hb' => hb_min b' (Or.inl hb')⟩
            · have h1 : (s.forest N).depth b.2 ≤ old.least :=
                hb₁_depth ▸ hb_min b₁ (Or.inl hb₁_S₁)
              have h2 : new.least ≤ (s.forest N).depth b.2 := hnew_least_le b hb_S₂
              omega

end GraphMinor.LRPlanarity
