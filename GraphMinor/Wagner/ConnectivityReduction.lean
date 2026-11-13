module

public import GraphMinor.Wagner.MultigraphReduction
import GraphMinor.HP25.Lemma33

/-!
# Connectivity Reductions (`(≤ 3)`-Cut Decomposition) for Wagner's Theorem

This file reduces the `SimpleGraph (Fin N)` dichotomy (`N ≥ 5`) of
`GraphMinor.Wagner.hasTreeStructureOver_of_finSimple_step` to internally `4`-connected graphs on
`N ≥ 6` vertices (`IsInternally4ConnFin K`):

1. **`N = 5` split**: every `K_5`-minor-free simple graph on `Fin 5` misses at least one edge `uv`,
   and splits across the `3`-vertex set `Finset.univ \ {u, v}` into two `4`-vertex torsos.
2. **`(≤ 2)`-cut reduction to `Is3ConnectedFin K` (`N ≥ 6`)**:
   * `0`-cuts and `1`-cuts add no torso edges, so torso `K_5` models lift directly to `K`.
   * Minimal `2`-cuts `{a, b}` (`K - {a}` and `K - {b}` connected) have every component `D` of
     `K - {a, b}` adjacent to both `a` and `b`, lifting torso `K_5` models to `K`.
3. **`3`-cut reductions from `Is3ConnectedFin K` (`N ≥ 6`) to `IsInternally4ConnFin K`**:
   * If a `3`-cut `S` contains an edge of `K`, one component of `K - S` lifts torso `K_5` models.
   * If `K - S` is an independent set, splitting off one vertex leaves a `4`-vertex torso and a
     torso whose complement of `S` is independent (hence `K_5`-minor-free).
   * If `Aᶜ` contains two components of `K - S`, they form a rooted `K_3` on `S`.
   * If `Aᶜ` contains a component `D` of `K - S` with `2 ≤ D.card` (`S` independent), `3`-connectedness
     produces a rooted `K_3` on `S` inside `S ∪ D`.
-/

public section

namespace GraphMinor.Wagner

open Set Function SimpleGraph

/-- `K : SimpleGraph (Fin N)` is `3`-connected: `4 ≤ N` and deleting at most `2` vertices leaves a
connected induced subgraph. -/
@[expose] def Is3ConnectedFin {N : ℕ} (K : SimpleGraph (Fin N)) : Prop :=
  4 ≤ N ∧ ∀ S : Finset (Fin N), S.card ≤ 2 → (K.induce {x : Fin N | x ∉ S}).Connected

/-- `K : SimpleGraph (Fin N)` is internally `4`-connected (`6 ≤ N`): `K` is `3`-connected and every
`3`-vertex cut `S` of `K` is an independent set whose complement in `K` consists of a single vertex
`u` of degree `3` together with one connected component. -/
@[expose] def IsInternally4ConnFin {N : ℕ} (K : SimpleGraph (Fin N)) : Prop :=
  6 ≤ N ∧ Is3ConnectedFin K ∧
    ∀ S : Finset (Fin N), S.card = 3 → ¬ (K.induce {x : Fin N | x ∉ S}).Connected →
      (∀ x ∈ S, ∀ y ∈ S, ¬ K.Adj x y) ∧
      ∃ u : Fin N, u ∉ S ∧ (∀ y : Fin N, K.Adj u y ↔ y ∈ S) ∧
        (K.induce {x : Fin N | x ∉ S ∧ x ≠ u}).Connected

/-! ### Part 1: Induced Preconnectedness Helpers -/

private theorem induce_reachable_mono {γ : Type*} {K : SimpleGraph γ} {X Y : Set γ}
    (hXY : X ⊆ Y) {u v : X} (hr : (K.induce X).Reachable u v) :
    (K.induce Y).Reachable ⟨u.1, hXY u.2⟩ ⟨v.1, hXY v.2⟩ := by
  let f : K.induce X →g K.induce Y := ⟨fun z => ⟨z.1, hXY z.2⟩, fun h => h⟩
  exact hr.map f

private theorem preconnected_induce_singleton {γ : Type*} (K : SimpleGraph γ) (x : γ) :
    (K.induce ({x} : Set γ)).Preconnected := by
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  rw [mem_singleton_iff] at hu hv
  subst hu; subst hv
  exact Reachable.rfl

private theorem preconnected_induce_union_of_adj {γ : Type*} {K : SimpleGraph γ} {X Y : Set γ}
    (hX : (K.induce X).Preconnected) (hY : (K.induce Y).Preconnected)
    {x y : γ} (hx : x ∈ X) (hy : y ∈ Y) (hxy : K.Adj x y) :
    (K.induce (X ∪ Y)).Preconnected := by
  have hx' : x ∈ X ∪ Y := Or.inl hx
  have hy' : y ∈ X ∪ Y := Or.inr hy
  have hlink : (K.induce (X ∪ Y)).Reachable ⟨x, hx'⟩ ⟨y, hy'⟩ :=
    Adj.reachable (G := K.induce (X ∪ Y)) (u := ⟨x, hx'⟩) (v := ⟨y, hy'⟩) hxy
  have htoX : ∀ z : ↥(X ∪ Y), z.1 ∈ X → (K.induce (X ∪ Y)).Reachable z ⟨x, hx'⟩ := fun z hz =>
    induce_reachable_mono subset_union_left (hX ⟨z.1, hz⟩ ⟨x, hx⟩)
  have htoY : ∀ z : ↥(X ∪ Y), z.1 ∈ Y → (K.induce (X ∪ Y)).Reachable z ⟨x, hx'⟩ := fun z hz =>
    (induce_reachable_mono subset_union_right (hY ⟨z.1, hz⟩ ⟨y, hy⟩)).trans hlink.symm
  intro u v
  have hu : (K.induce (X ∪ Y)).Reachable u ⟨x, hx'⟩ := u.2.elim (htoX u) (htoY u)
  have hv : (K.induce (X ∪ Y)).Reachable v ⟨x, hx'⟩ := v.2.elim (htoX v) (htoY v)
  exact hu.trans hv.symm

private theorem preconnected_induce_insert_of_adj {γ : Type*} {K : SimpleGraph γ} {X : Set γ}
    (hX : (K.induce X).Preconnected) {x y : γ} (hy : y ∈ X) (hxy : K.Adj x y) :
    (K.induce (insert x X)).Preconnected := by
  rw [← singleton_union]
  exact preconnected_induce_union_of_adj (preconnected_induce_singleton K x) hX rfl hy hxy

private theorem reachable_induce_of_walk_support {γ : Type*} {K : SimpleGraph γ} {X : Set γ}
    {a b : γ} (w : K.Walk a b) (hw : ∀ z ∈ w.support, z ∈ X)
    {z : γ} (hz : z ∈ w.support) :
    (K.induce X).Reachable ⟨a, hw a w.start_mem_support⟩ ⟨z, hw z hz⟩ := by
  induction w with
  | nil =>
    rw [Walk.support_nil, List.mem_singleton] at hz
    subst hz
    exact Reachable.rfl
  | @cons u v c huv p ih =>
    have huX : u ∈ X := hw u (by simp)
    have hvX : v ∈ X := hw v (by simp)
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact Reachable.rfl
    · have hstep : (K.induce X).Reachable ⟨u, huX⟩ ⟨v, hvX⟩ :=
        Adj.reachable (G := K.induce X) (u := ⟨u, huX⟩) (v := ⟨v, hvX⟩) huv
      exact hstep.trans (ih (fun q hq => hw q (by simp [hq])) hz)

private theorem preconnected_induce_walk_support {γ : Type*} {K : SimpleGraph γ}
    {a b : γ} (w : K.Walk a b) :
    (K.induce {z : γ | z ∈ w.support}).Preconnected := by
  intro ⟨u, hu⟩ ⟨v, hv⟩
  have r1 := reachable_induce_of_walk_support w (fun _ h => h) hu
  have r2 := reachable_induce_of_walk_support w (fun _ h => h) hv
  exact r1.symm.trans r2

private theorem mem_support_reverse_iff {γ : Type*} {K : SimpleGraph γ} {a b u : γ}
    (w : K.Walk a b) : u ∈ w.reverse.support ↔ u ∈ w.support := by
  rw [Walk.support_reverse, List.mem_reverse]

/-! ### Part 2: Torso `K_5`-Minor Exclusion and Unified Rooted-Clique Lifting -/

/-- No simple graph on fewer than `5` vertices has a `K_5` minor. -/
private theorem not_hasK5MinorSimple_of_card_lt_five {γ : Type*} [Fintype γ]
    (hcard : Fintype.card γ < 5) (T : SimpleGraph γ) : ¬ HasK5MinorSimple T := by
  rintro ⟨B, hne, _, hdisj, _⟩
  let f : Fin 5 → γ := fun i => (hne i).some
  have hf_mem : ∀ i, f i ∈ B i := fun i => (hne i).some_mem
  have hf_inj : Injective f := fun i j hij => by
    by_contra hne_ij
    exact Set.disjoint_left.mp (hdisj hne_ij) (hf_mem i) (hij ▸ hf_mem j)
  have hle : 5 ≤ Fintype.card γ := by
    simpa using Fintype.card_le_of_injective f hf_inj
  omega

private theorem not_hasK5MinorSimple_torsoOn_of_card_le_four {N : ℕ} {K : SimpleGraph (Fin N)}
    {A S : Finset (Fin N)} (hA : A.card ≤ 4) : ¬ HasK5MinorSimple (torsoOn K A S) := by
  apply not_hasK5MinorSimple_of_card_lt_five
  rw [Fintype.card_coe]
  omega

/-- If `S.card ≤ 3` and `A \ S` is an independent set of `K`, then `torsoOn K A S` has no `K_5`
minor: at most `3` of the `5` disjoint branch sets can meet `S`, leaving two branch sets in the
edgeless set `A \ S`. -/
private theorem not_hasK5MinorSimple_torsoOn_of_indep_sdiff {N : ℕ} {K : SimpleGraph (Fin N)}
    {A S : Finset (Fin N)} (hS : S.card ≤ 3)
    (hindep : ∀ x ∈ A \ S, ∀ y ∈ A \ S, ¬ K.Adj x y) :
    ¬ HasK5MinorSimple (torsoOn K A S) := by
  classical
  rintro ⟨B, hne, _, hdisj, hadj⟩
  let hit : Finset (Fin 5) := Finset.univ.filter fun i => ∃ x ∈ B i, x.1 ∈ S
  have hhit_le : hit.card ≤ S.card := by
    let g : {i : Fin 5 // i ∈ hit} → {s : Fin N // s ∈ S} := fun ⟨i, hi⟩ =>
      let hx := (Finset.mem_filter.mp hi).2
      ⟨hx.choose.1, hx.choose_spec.2⟩
    have hg_inj : Injective g := by
      rintro ⟨i, hi⟩ ⟨j, hj⟩ heq
      apply Subtype.ext
      by_contra hij
      have hxi := (Finset.mem_filter.mp hi).2.choose_spec.1
      have hxj := (Finset.mem_filter.mp hj).2.choose_spec.1
      have h1 : (g ⟨i, hi⟩).1 = (g ⟨j, hj⟩).1 := congrArg Subtype.val heq
      have hval : (Finset.mem_filter.mp hi).2.choose = (Finset.mem_filter.mp hj).2.choose :=
        Subtype.ext h1
      exact Set.disjoint_left.mp (hdisj hij) hxi (hval ▸ hxj)
    have hcard := Fintype.card_le_of_injective g hg_inj
    simpa [Fintype.card_coe] using hcard
  have hmiss_gt : 1 < (Finset.univ \ hit).card := by
    have hsub : hit ⊆ Finset.univ := Finset.subset_univ _
    have hc := Finset.card_sdiff_add_card_eq_card hsub
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hmiss_gt
  have hi_not : ¬ ∃ x ∈ B i, x.1 ∈ S := by
    simpa [hit] using (Finset.mem_sdiff.mp hi).2
  have hj_not : ¬ ∃ x ∈ B j, x.1 ∈ S := by
    simpa [hit] using (Finset.mem_sdiff.mp hj).2
  obtain ⟨x, hx, y, hy, _, hKxy | ⟨hxS, _⟩⟩ := hadj hij
  · have hxS : x.1 ∉ S := fun h => hi_not ⟨x, hx, h⟩
    have hyS : y.1 ∉ S := fun h => hj_not ⟨y, hy, h⟩
    exact hindep x.1 (Finset.mem_sdiff.mpr ⟨x.2, hxS⟩) y.1 (Finset.mem_sdiff.mpr ⟨y.2, hyS⟩) hKxy
  · exact hi_not ⟨x, hx, hxS⟩

/-- **Unified Rooted-Clique Torso Lifting Lemma**: if `S ⊆ A` and each `s ∈ S` has a connected
witness `W s ⊆ V(K)` containing `s`, meeting `A` only at `s`, pairwise disjoint across `S`, and
with a `K`-edge between `W s₁` and `W s₂` for every `s₁ ≠ s₂` in `S`, then any `K_5` minor of
`torsoOn K A S` lifts to a `K_5` minor of `K`. -/
private theorem hasK5MinorSimple_of_torsoOn_rooted_clique {N : ℕ} {K : SimpleGraph (Fin N)}
    {A S : Finset (Fin N)} (hSA : S ⊆ A)
    (W : {s : Fin N // s ∈ S} → Set (Fin N))
    (hroot : ∀ s : {s : Fin N // s ∈ S}, s.1 ∈ W s)
    (hmeetA : ∀ (s : {s : Fin N // s ∈ S}) (z : Fin N), z ∈ W s → z ∈ A → z = s.1)
    (hW_disj : ∀ s₁ s₂ : {s : Fin N // s ∈ S}, s₁ ≠ s₂ → Disjoint (W s₁) (W s₂))
    (hW_conn : ∀ s : {s : Fin N // s ∈ S}, (K.induce (W s)).Preconnected)
    (hW_adj : ∀ s₁ s₂ : {s : Fin N // s ∈ S}, s₁ ≠ s₂ →
      ∃ u ∈ W s₁, ∃ v ∈ W s₂, K.Adj u v)
    (hm : HasK5MinorSimple (torsoOn K A S)) : HasK5MinorSimple K := by
  obtain ⟨B, hne, hpre, hdisj, hadj⟩ := hm
  let B' : Fin 5 → Set (Fin N) := fun i =>
    (Subtype.val '' B i) ∪ ⋃ (s : {s : Fin N // s ∈ S}) (_ : ⟨s.1, hSA s.2⟩ ∈ B i), W s
  have hsub_W : ∀ i (s : {s : Fin N // s ∈ S}), ⟨s.1, hSA s.2⟩ ∈ B i → W s ⊆ B' i := by
    intro i s hs z hz
    exact Or.inr (mem_iUnion₂.mpr ⟨s, hs, hz⟩)
  refine ⟨B', ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨x, hx⟩ := hne i
    exact ⟨x.1, Or.inl ⟨x, hx, rfl⟩⟩
  · intro i
    -- Step 1: every `x, y ∈ B i` are reachable in `K.induce (B' i)`.
    have hstep_torso : ∀ {x y : {z : Fin N // z ∈ A}}
        (hxB : x ∈ B i) (hyB : y ∈ B i), (torsoOn K A S).Adj x y →
        (K.induce (B' i)).Reachable ⟨x.1, Or.inl ⟨x, hxB, rfl⟩⟩
          ⟨y.1, Or.inl ⟨y, hyB, rfl⟩⟩ := by
      rintro x y hxB hyB ⟨hxy_ne, hKxy | ⟨hxS, hyS⟩⟩
      · exact Adj.reachable (G := K.induce (B' i))
          (u := ⟨x.1, Or.inl ⟨x, hxB, rfl⟩⟩) (v := ⟨y.1, Or.inl ⟨y, hyB, rfl⟩⟩) hKxy
      · let s₁ : {s : Fin N // s ∈ S} := ⟨x.1, hxS⟩
        let s₂ : {s : Fin N // s ∈ S} := ⟨y.1, hyS⟩
        have hs₁₂ : s₁ ≠ s₂ := fun h => hxy_ne (Subtype.ext (by have h' := congrArg Subtype.val h; exact h'))
        have hs₁B : ⟨s₁.1, hSA s₁.2⟩ ∈ B i := hxB
        have hs₂B : ⟨s₂.1, hSA s₂.2⟩ ∈ B i := hyB
        obtain ⟨u, huW, v, hvW, huv⟩ := hW_adj s₁ s₂ hs₁₂
        have r1 : (K.induce (B' i)).Reachable
            ⟨x.1, Or.inl ⟨x, hxB, rfl⟩⟩ ⟨u, hsub_W i s₁ hs₁B huW⟩ :=
          induce_reachable_mono (hsub_W i s₁ hs₁B) (hW_conn s₁ ⟨s₁.1, hroot s₁⟩ ⟨u, huW⟩)
        have r2 : (K.induce (B' i)).Reachable
            ⟨u, hsub_W i s₁ hs₁B huW⟩ ⟨v, hsub_W i s₂ hs₂B hvW⟩ :=
          Adj.reachable (G := K.induce (B' i))
            (u := ⟨u, hsub_W i s₁ hs₁B huW⟩) (v := ⟨v, hsub_W i s₂ hs₂B hvW⟩) huv
        have r3 : (K.induce (B' i)).Reachable
            ⟨v, hsub_W i s₂ hs₂B hvW⟩ ⟨y.1, Or.inl ⟨y, hyB, rfl⟩⟩ :=
          induce_reachable_mono (hsub_W i s₂ hs₂B) (hW_conn s₂ ⟨v, hvW⟩ ⟨s₂.1, hroot s₂⟩)
        exact (r1.trans r2).trans r3
    have hreach_B : ∀ (x y : B i),
        (K.induce (B' i)).Reachable ⟨x.1.1, Or.inl ⟨x.1, x.2, rfl⟩⟩
          ⟨y.1.1, Or.inl ⟨y.1, y.2, rfl⟩⟩ := by
      intro x y
      obtain ⟨w⟩ := hpre i x y
      induction w with
      | nil => exact Reachable.rfl
      | @cons a b c hab _ ih =>
        exact (hstep_torso a.2 b.2 hab).trans ih
    -- Step 2: every element of `B' i` reaches some element of `Subtype.val '' B i`.
    have hto_base : ∀ z : B' i, ∃ x : B i,
        (K.induce (B' i)).Reachable z ⟨x.1.1, Or.inl ⟨x.1, x.2, rfl⟩⟩ := by
      rintro ⟨z, ⟨x, hxB, rfl⟩ | hzU⟩
      · exact ⟨⟨x, hxB⟩, Reachable.rfl⟩
      · obtain ⟨s, hsB, hzW⟩ := mem_iUnion₂.mp hzU
        refine ⟨⟨⟨s.1, hSA s.2⟩, hsB⟩, ?_⟩
        exact induce_reachable_mono (hsub_W i s hsB) (hW_conn s ⟨z, hzW⟩ ⟨s.1, hroot s⟩)
    intro z₁ z₂
    obtain ⟨x₁, r₁⟩ := hto_base z₁
    obtain ⟨x₂, r₂⟩ := hto_base z₂
    exact (r₁.trans (hreach_B x₁ x₂)).trans r₂.symm
  · intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    by_cases hzA : z ∈ A
    · have hmemB : ∀ k, z ∈ B' k → ⟨z, hzA⟩ ∈ B k := by
        rintro k (⟨x, hxB, rfl⟩ | hzU)
        · exact hxB
        · obtain ⟨s, hsB, hzW⟩ := mem_iUnion₂.mp hzU
          have hzs : z = s.1 := hmeetA s z hzW hzA
          subst hzs
          exact hsB
      exact Set.disjoint_left.mp (hdisj hij) (hmemB i hzi) (hmemB j hzj)
    · have hnotBase : ∀ k, z ∉ Subtype.val '' B k := by
        rintro k ⟨x, _, rfl⟩
        exact hzA x.2
      obtain ⟨s₁, hs₁B, hzW₁⟩ := mem_iUnion₂.mp (hzi.resolve_left (hnotBase i))
      obtain ⟨s₂, hs₂B, hzW₂⟩ := mem_iUnion₂.mp (hzj.resolve_left (hnotBase j))
      have hs_eq : s₁ = s₂ := by
        by_contra hne_s
        exact Set.disjoint_left.mp (hW_disj s₁ s₂ hne_s) hzW₁ hzW₂
      subst hs_eq
      exact Set.disjoint_left.mp (hdisj hij) hs₁B hs₂B
  · intro i j hij
    obtain ⟨x, hxB, y, hyB, hxy_ne, hKxy | ⟨hxS, hyS⟩⟩ := hadj hij
    · exact ⟨x.1, Or.inl ⟨x, hxB, rfl⟩, y.1, Or.inl ⟨y, hyB, rfl⟩, hKxy⟩
    · let s₁ : {s : Fin N // s ∈ S} := ⟨x.1, hxS⟩
      let s₂ : {s : Fin N // s ∈ S} := ⟨y.1, hyS⟩
      have hs₁₂ : s₁ ≠ s₂ := fun h => hxy_ne (Subtype.ext (by have h' := congrArg Subtype.val h; exact h'))
      obtain ⟨u, huW, v, hvW, huv⟩ := hW_adj s₁ s₂ hs₁₂
      exact ⟨u, hsub_W i s₁ hxB huW, v, hsub_W j s₂ hyB hvW, huv⟩

/-- Special case `S.card ≤ 1`: `torsoOn K A S` adds no edges, so any `K_5` minor lifts to `K`. -/
private theorem hasK5MinorSimple_of_torsoOn_card_le_one {N : ℕ} {K : SimpleGraph (Fin N)}
    {A S : Finset (Fin N)} (hSA : S ⊆ A) (hS : S.card ≤ 1)
    (hm : HasK5MinorSimple (torsoOn K A S)) : HasK5MinorSimple K := by
  refine hasK5MinorSimple_of_torsoOn_rooted_clique hSA (fun s => {s.1})
    (fun _ => rfl) (fun _ _ hz _ => hz) ?_ (fun s => preconnected_induce_singleton K s.1) ?_ hm
  · intro s₁ s₂ hne
    exact disjoint_singleton.mpr fun h => hne (Subtype.ext h)
  · intro s₁ s₂ hne
    have hgt : 1 < S.card := Finset.one_lt_card.mpr ⟨s₁.1, s₁.2, s₂.1, s₂.2,
      fun h => hne (Subtype.ext h)⟩
    omega

/-! ### Part 3: Components of `K - S` and Attachment Lemmas -/

/-- The connected component of `p ∉ S` in `K - S`, as a `Finset (Fin N)`. -/
private noncomputable def compFinset {N : ℕ} (K : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (p : {x : Fin N // x ∉ S}) : Finset (Fin N) := by
  classical
  exact (Finset.univ \ S).filter fun x =>
    ∃ hx : x ∉ S, (K.induce {z : Fin N | z ∉ S}).Reachable p ⟨x, hx⟩

private theorem mem_compFinset_self {N : ℕ} {K : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    (p : {x : Fin N // x ∉ S}) : p.1 ∈ compFinset K S p := by
  classical
  simp only [compFinset, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact ⟨p.2, p.2, Reachable.rfl⟩

private theorem notMem_of_mem_compFinset {N : ℕ} {K : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {p : {x : Fin N // x ∉ S}} {x : Fin N} (hx : x ∈ compFinset K S p) : x ∉ S := by
  classical
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).2

private theorem compFinset_closed {N : ℕ} {K : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {p : {x : Fin N // x ∉ S}} {x y : Fin N}
    (hx : x ∈ compFinset K S p) (hyS : y ∉ S) (hxy : K.Adj x y) :
    y ∈ compFinset K S p := by
  classical
  obtain ⟨_, hxS, hr⟩ := Finset.mem_filter.mp hx
  rw [compFinset, Finset.mem_filter]
  refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyS⟩, hyS, ?_⟩
  exact hr.trans (Adj.reachable (G := K.induce {z : Fin N | z ∉ S})
    (u := ⟨x, hxS⟩) (v := ⟨y, hyS⟩) hxy)

private theorem compFinset_disjoint_of_notMem {N : ℕ} {K : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {p q : {x : Fin N // x ∉ S}} (hq : q.1 ∉ compFinset K S p) :
    Disjoint (compFinset K S p) (compFinset K S q) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzp hzq
  apply hq
  obtain ⟨_, hzS, hrp⟩ := Finset.mem_filter.mp hzp
  obtain ⟨_, _, hrq⟩ := Finset.mem_filter.mp hzq
  rw [compFinset, Finset.mem_filter]
  exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, q.2⟩, q.2, hrp.trans hrq.symm⟩

private theorem preconnected_compFinset {N : ℕ} {K : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    (p : {x : Fin N // x ∉ S}) :
    (K.induce (compFinset K S p : Set (Fin N))).Preconnected := by
  classical
  -- Show every `x ∈ compFinset K S p` reaches `p` inside `compFinset K S p`.
  have hto_p : ∀ x : (compFinset K S p : Set (Fin N)),
      (K.induce (compFinset K S p : Set (Fin N))).Reachable
        ⟨p.1, mem_compFinset_self p⟩ x := by
    rintro ⟨x, hx⟩
    obtain ⟨_, hxS, ⟨w⟩⟩ := Finset.mem_filter.mp hx
    have haux : ∀ {u v : {z : Fin N | z ∉ S}} (q : (K.induce {z : Fin N | z ∉ S}).Walk u v)
        (hu : u.1 ∈ compFinset K S p),
        (K.induce (compFinset K S p : Set (Fin N))).Reachable
          ⟨u.1, hu⟩ ⟨v.1, by
            induction q with
            | nil => exact hu
            | @cons a b c hab _ ihq => exact ihq (compFinset_closed hu b.2 hab)⟩ := by
      intro u v q
      induction q with
      | nil => intro _; exact Reachable.rfl
      | @cons a b c hab q' ih =>
        intro ha
        have hb : b.1 ∈ compFinset K S p := compFinset_closed ha b.2 hab
        have hstep : (K.induce (compFinset K S p : Set (Fin N))).Reachable ⟨a.1, ha⟩ ⟨b.1, hb⟩ :=
          Adj.reachable (G := K.induce (compFinset K S p : Set (Fin N)))
            (u := ⟨a.1, ha⟩) (v := ⟨b.1, hb⟩) hab
        exact hstep.trans (ih hb)
    exact haux w (mem_compFinset_self p)
  intro x y
  exact (hto_p x).symm.trans (hto_p y)

/-- If `K - S` is not connected, there exist `p, q ∉ S` with `q ∉ compFinset K S p`
(provided `Finset.univ \ S` is nonempty). -/
private theorem exists_two_outside_of_not_connected {N : ℕ} {K : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} (hne : (Finset.univ \ S).Nonempty)
    (hnot : ¬ (K.induce {x : Fin N | x ∉ S}).Connected) :
    ∃ (p q : {x : Fin N // x ∉ S}), q.1 ∉ compFinset K S p := by
  classical
  obtain ⟨p₀, hp₀⟩ := hne
  let p : {x : Fin N // x ∉ S} := ⟨p₀, (Finset.mem_sdiff.mp hp₀).2⟩
  by_contra hall
  push Not at hall
  apply hnot
  have : Nonempty {x : Fin N | x ∉ S} := ⟨⟨p.1, p.2⟩⟩
  refine ⟨fun u v => ?_⟩
  have hr : ∀ w : {x : Fin N | x ∉ S}, (K.induce {x : Fin N | x ∉ S}).Reachable ⟨p.1, p.2⟩ w := by
    intro w
    have h := hall p ⟨w.1, w.2⟩
    simp only [compFinset, Finset.mem_filter] at h
    obtain ⟨_, _, hrw⟩ := h
    exact hrw
  exact (hr u).symm.trans (hr v)

/-- **Boundary Attachment Lemma**: if `D ⊆ Finset.univ \ S` is closed under `K`-neighbors outside
`S`, `p ∈ D`, `q ∉ S ∪ D`, and `K - (S \ {s})` is connected (`s ∈ S`), then `s` has a `K`-neighbor
in `D`. -/
private theorem exists_adj_in_closed_set {N : ℕ} {K : SimpleGraph (Fin N)}
    {S D : Finset (Fin N)} {s : Fin N} (hs : s ∈ S)
    (hclosed : ∀ x ∈ D, ∀ y ∉ S, K.Adj x y → y ∈ D)
    {p q : Fin N} (hpD : p ∈ D) (hpS : p ∉ S) (hqD : q ∉ D) (hqS : q ∉ S)
    (hconn : (K.induce {x : Fin N | x ∉ S.erase s}).Connected) :
    ∃ x ∈ D, K.Adj s x := by
  have hp' : p ∉ S.erase s := fun h => hpS (Finset.mem_of_mem_erase h)
  have hq' : q ∉ S.erase s := fun h => hqS (Finset.mem_of_mem_erase h)
  obtain ⟨w⟩ := hconn.preconnected ⟨p, hp'⟩ ⟨q, hq'⟩
  have hwalk : ∀ {u v : {x : Fin N | x ∉ S.erase s}}
      (r : (K.induce {x : Fin N | x ∉ S.erase s}).Walk u v),
      u.1 ∈ D → v.1 ∉ D → ∃ x ∈ D, K.Adj s x := by
    intro u v r
    induction r with
    | nil => intro hu hv; exact (hv hu).elim
    | @cons a b c hab r' ih =>
      intro ha hc
      by_cases hbs : b.1 = s
      · have hba : K.Adj b.1 a.1 := hab.symm
        rw [hbs] at hba
        exact ⟨a.1, ha, hba⟩
      · have hbS : b.1 ∉ S := fun h => b.2 (Finset.mem_erase.mpr ⟨hbs, h⟩)
        exact ih (hclosed a.1 ha b.1 hbS hab) hc
  exact hwalk w hpD hqD

/-! ### Part 4: Torso Lifting for `2`-Cuts, `3`-Cuts with an Edge, and `3`-Cuts with Two Components -/

/-- **`2`-Cut Torso Lift**: if `S = {a, b}` (`a ≠ b`), `S ⊆ A`, and `D ⊆ Aᶜ` is a nonempty
preconnected set adjacent to both `a` and `b`, then `torsoOn K A S` lifts to `K`. -/
private theorem hasK5MinorSimple_of_two_cut_comp {N : ℕ} {K : SimpleGraph (Fin N)}
    {A S D : Finset (Fin N)} {a b : Fin N} (hab : a ≠ b) (hS : S = {a, b}) (hSA : S ⊆ A)
    (hDA : Disjoint D A) (hD_pre : (K.induce (D : Set (Fin N))).Preconnected)
    (haD : ∃ x ∈ D, K.Adj a x) (hbD : ∃ x ∈ D, K.Adj b x)
    (hm : HasK5MinorSimple (torsoOn K A S)) : HasK5MinorSimple K := by
  classical
  let W : {s : Fin N // s ∈ S} → Set (Fin N) := fun s =>
    if s.1 = a then {a} else insert b (D : Set (Fin N))
  have hs_cases : ∀ s : {s : Fin N // s ∈ S}, s.1 = a ∨ s.1 = b := by
    rintro ⟨s, hs⟩
    rw [hS] at hs
    simpa using hs
  have key : ∀ s : {s : Fin N // s ∈ S},
      (s.1 = a ∧ W s = {a}) ∨ (s.1 = b ∧ W s = insert b (D : Set (Fin N))) := by
    intro s
    rcases hs_cases s with h | h
    · exact Or.inl ⟨h, if_pos h⟩
    · have hna : s.1 ≠ a := by rw [h]; exact hab.symm
      exact Or.inr ⟨h, if_neg hna⟩
  have haA : a ∈ A := hSA (by simp [hS])
  have hdisj_ab : Disjoint ({a} : Set (Fin N)) (insert b (D : Set (Fin N))) := by
    rw [disjoint_singleton_left, mem_insert_iff, not_or]
    exact ⟨hab, fun haD' => Finset.disjoint_left.mp hDA haD' haA⟩
  refine hasK5MinorSimple_of_torsoOn_rooted_clique hSA W ?_ ?_ ?_ ?_ ?_ hm
  · intro s
    rcases key s with ⟨h, hW⟩ | ⟨h, hW⟩ <;> rw [hW, h]
    · exact mem_singleton a
    · exact mem_insert b _
  · intro s z hz hzA
    rcases key s with ⟨h, hW⟩ | ⟨h, hW⟩ <;> rw [hW] at hz <;> rw [h]
    · exact hz
    · rcases hz with rfl | hzD
      · rfl
      · exact (Finset.disjoint_left.mp hDA hzD hzA).elim
  · intro s₁ s₂ hne
    have hne_val : s₁.1 ≠ s₂.1 := fun h => hne (Subtype.ext h)
    rcases key s₁ with ⟨h1, hW1⟩ | ⟨h1, hW1⟩ <;> rcases key s₂ with ⟨h2, hW2⟩ | ⟨h2, hW2⟩ <;>
      rw [hW1, hW2]
    · exact (hne_val (h1.trans h2.symm)).elim
    · exact hdisj_ab
    · exact hdisj_ab.symm
    · exact (hne_val (h1.trans h2.symm)).elim
  · intro s
    rcases key s with ⟨h, hW⟩ | ⟨h, hW⟩ <;> rw [hW]
    · exact preconnected_induce_singleton K a
    · obtain ⟨x, hxD, hbx⟩ := hbD
      exact preconnected_induce_insert_of_adj hD_pre hxD hbx
  · intro s₁ s₂ hne
    have hne_val : s₁.1 ≠ s₂.1 := fun h => hne (Subtype.ext h)
    obtain ⟨x, hxD, hax⟩ := haD
    rcases key s₁ with ⟨h1, hW1⟩ | ⟨h1, hW1⟩ <;> rcases key s₂ with ⟨h2, hW2⟩ | ⟨h2, hW2⟩ <;>
      rw [hW1, hW2]
    · exact (hne_val (h1.trans h2.symm)).elim
    · exact ⟨a, mem_singleton a, x, Or.inr hxD, hax⟩
    · exact ⟨x, Or.inr hxD, a, mem_singleton a, hax.symm⟩
    · exact (hne_val (h1.trans h2.symm)).elim

/-- Helper assembling a `3`-element `Finset` witness `(W_a, W_b, W_c)` on `S = {a, b, c}` into the
indexed family expected by `hasK5MinorSimple_of_torsoOn_rooted_clique`. -/
private theorem hasK5MinorSimple_of_three_cut_witness {N : ℕ} {K : SimpleGraph (Fin N)}
    {A S : Finset (Fin N)} {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hS : S = {a, b, c}) (hSA : S ⊆ A)
    (Wa Wb Wc : Set (Fin N))
    (ha : a ∈ Wa) (hb : b ∈ Wb) (hc : c ∈ Wc)
    (hWaA : ∀ z ∈ Wa, z ∈ A → z = a)
    (hWbA : ∀ z ∈ Wb, z ∈ A → z = b)
    (hWcA : ∀ z ∈ Wc, z ∈ A → z = c)
    (hd_ab : Disjoint Wa Wb) (hd_ac : Disjoint Wa Wc) (hd_bc : Disjoint Wb Wc)
    (hc_a : (K.induce Wa).Preconnected)
    (hc_b : (K.induce Wb).Preconnected)
    (hc_c : (K.induce Wc).Preconnected)
    (hadj_ab : ∃ u ∈ Wa, ∃ v ∈ Wb, K.Adj u v)
    (hadj_ac : ∃ u ∈ Wa, ∃ v ∈ Wc, K.Adj u v)
    (hadj_bc : ∃ u ∈ Wb, ∃ v ∈ Wc, K.Adj u v)
    (hm : HasK5MinorSimple (torsoOn K A S)) : HasK5MinorSimple K := by
  classical
  let W : {s : Fin N // s ∈ S} → Set (Fin N) := fun s =>
    if s.1 = a then Wa else if s.1 = b then Wb else Wc
  have hs_cases : ∀ s : {s : Fin N // s ∈ S}, s.1 = a ∨ s.1 = b ∨ s.1 = c := by
    rintro ⟨s, hs⟩
    rw [hS] at hs
    simpa using hs
  have key : ∀ s : {s : Fin N // s ∈ S},
      (s.1 = a ∧ W s = Wa) ∨ (s.1 = b ∧ W s = Wb) ∨ (s.1 = c ∧ W s = Wc) := by
    intro s
    rcases hs_cases s with h | h | h
    · exact Or.inl ⟨h, if_pos h⟩
    · have hna : s.1 ≠ a := by rw [h]; exact hab.symm
      exact Or.inr (Or.inl ⟨h, (if_neg hna).trans (if_pos h)⟩)
    · have hna : s.1 ≠ a := by rw [h]; exact hac.symm
      have hnb : s.1 ≠ b := by rw [h]; exact hbc.symm
      exact Or.inr (Or.inr ⟨h, (if_neg hna).trans (if_neg hnb)⟩)
  have sym_adj : ∀ {X Y : Set (Fin N)},
      (∃ u ∈ X, ∃ v ∈ Y, K.Adj u v) → ∃ u ∈ Y, ∃ v ∈ X, K.Adj u v := by
    rintro _ _ ⟨u, hu, v, hv, huv⟩
    exact ⟨v, hv, u, hu, huv.symm⟩
  refine hasK5MinorSimple_of_torsoOn_rooted_clique hSA W ?_ ?_ ?_ ?_ ?_ hm
  · intro s
    rcases key s with ⟨h, hW⟩ | ⟨h, hW⟩ | ⟨h, hW⟩ <;> rw [hW, h]
    exacts [ha, hb, hc]
  · intro s z hz hzA
    rcases key s with ⟨h, hW⟩ | ⟨h, hW⟩ | ⟨h, hW⟩ <;> rw [hW] at hz <;> rw [h]
    exacts [hWaA z hz hzA, hWbA z hz hzA, hWcA z hz hzA]
  · intro s₁ s₂ hne
    have hne_val : s₁.1 ≠ s₂.1 := fun h => hne (Subtype.ext h)
    rcases key s₁ with ⟨h1, hW1⟩ | ⟨h1, hW1⟩ | ⟨h1, hW1⟩ <;>
      rcases key s₂ with ⟨h2, hW2⟩ | ⟨h2, hW2⟩ | ⟨h2, hW2⟩ <;> rw [hW1, hW2] <;>
      first
        | exact (hne_val (h1.trans h2.symm)).elim
        | exact hd_ab | exact hd_ac | exact hd_bc
        | exact hd_ab.symm | exact hd_ac.symm | exact hd_bc.symm
  · intro s
    rcases key s with ⟨h, hW⟩ | ⟨h, hW⟩ | ⟨h, hW⟩ <;> rw [hW]
    exacts [hc_a, hc_b, hc_c]
  · intro s₁ s₂ hne
    have hne_val : s₁.1 ≠ s₂.1 := fun h => hne (Subtype.ext h)
    rcases key s₁ with ⟨h1, hW1⟩ | ⟨h1, hW1⟩ | ⟨h1, hW1⟩ <;>
      rcases key s₂ with ⟨h2, hW2⟩ | ⟨h2, hW2⟩ | ⟨h2, hW2⟩ <;> rw [hW1, hW2] <;>
      first
        | exact (hne_val (h1.trans h2.symm)).elim
        | exact hadj_ab | exact hadj_ac | exact hadj_bc
        | exact sym_adj hadj_ab | exact sym_adj hadj_ac | exact sym_adj hadj_bc

/-- **`3`-Cut Reduction 1 (`S` has an edge `K.Adj a b`)**: a single component `D ⊆ Aᶜ` adjacent to
`a, b, c` gives the rooted `K_3` `({a}, {b}, {c} ∪ D)`. -/
private theorem hasK5MinorSimple_of_three_cut_edge {N : ℕ} {K : SimpleGraph (Fin N)}
    {A S D : Finset (Fin N)} {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hS : S = {a, b, c}) (hSA : S ⊆ A)
    (hK_ab : K.Adj a b) (hDA : Disjoint D A)
    (hD_pre : (K.induce (D : Set (Fin N))).Preconnected)
    (haD : ∃ x ∈ D, K.Adj a x) (hbD : ∃ x ∈ D, K.Adj b x) (hcD : ∃ x ∈ D, K.Adj c x)
    (hm : HasK5MinorSimple (torsoOn K A S)) : HasK5MinorSimple K := by
  obtain ⟨xa, hxa, hax⟩ := haD
  obtain ⟨xb, hxb, hbx⟩ := hbD
  obtain ⟨xc, hxc, hcx⟩ := hcD
  have haA : a ∈ A := hSA (by simp [hS])
  have hbA : b ∈ A := hSA (by simp [hS])
  refine hasK5MinorSimple_of_three_cut_witness hab hac hbc hS hSA
    {a} {b} (insert c (D : Set (Fin N)))
    rfl rfl (mem_insert _ _)
    (fun _ hz _ => hz) (fun _ hz _ => hz)
    (fun z hz hzA => hz.elim id fun hzD => (Finset.disjoint_left.mp hDA hzD hzA).elim)
    (disjoint_singleton.mpr hab)
    (disjoint_singleton_left.mpr fun h =>
      h.elim hac fun haD' => Finset.disjoint_left.mp hDA haD' haA)
    (disjoint_singleton_left.mpr fun h =>
      h.elim hbc fun hbD' => Finset.disjoint_left.mp hDA hbD' hbA)
    (preconnected_induce_singleton K a)
    (preconnected_induce_singleton K b)
    (preconnected_induce_insert_of_adj hD_pre hxc hcx)
    ⟨a, rfl, b, rfl, hK_ab⟩
    ⟨a, rfl, xa, Or.inr hxa, hax⟩
    ⟨b, rfl, xb, Or.inr hxb, hbx⟩ hm

/-- **`3`-Cut Reduction 2 (`Aᶜ` has two disjoint components `D₁, D₂`)**: `({a}, {b} ∪ D₁, {c} ∪ D₂)`
forms a rooted `K_3` on `S = {a, b, c}`. -/
private theorem hasK5MinorSimple_of_three_cut_two_comps {N : ℕ} {K : SimpleGraph (Fin N)}
    {A S D₁ D₂ : Finset (Fin N)} {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hS : S = {a, b, c}) (hSA : S ⊆ A)
    (hD₁A : Disjoint D₁ A) (hD₂A : Disjoint D₂ A) (hD₁₂ : Disjoint D₁ D₂)
    (hD₁_pre : (K.induce (D₁ : Set (Fin N))).Preconnected)
    (hD₂_pre : (K.induce (D₂ : Set (Fin N))).Preconnected)
    (ha₁ : ∃ x ∈ D₁, K.Adj a x) (hb₁ : ∃ x ∈ D₁, K.Adj b x)
    (ha₂ : ∃ x ∈ D₂, K.Adj a x) (hb₂ : ∃ x ∈ D₂, K.Adj b x) (hc₂ : ∃ x ∈ D₂, K.Adj c x)
    (hm : HasK5MinorSimple (torsoOn K A S)) : HasK5MinorSimple K := by
  obtain ⟨xa₁, hxa₁, hax₁⟩ := ha₁
  obtain ⟨xb₁, hxb₁, hbx₁⟩ := hb₁
  obtain ⟨xa₂, hxa₂, hax₂⟩ := ha₂
  obtain ⟨xb₂, hxb₂, hbx₂⟩ := hb₂
  obtain ⟨xc₂, hxc₂, hcx₂⟩ := hc₂
  have haA : a ∈ A := hSA (by simp [hS])
  have hbA : b ∈ A := hSA (by simp [hS])
  have hcA : c ∈ A := hSA (by simp [hS])
  refine hasK5MinorSimple_of_three_cut_witness hab hac hbc hS hSA
    {a} (insert b (D₁ : Set (Fin N))) (insert c (D₂ : Set (Fin N)))
    rfl (mem_insert _ _) (mem_insert _ _)
    (fun _ hz _ => hz)
    (fun z hz hzA => hz.elim id fun hzD => (Finset.disjoint_left.mp hD₁A hzD hzA).elim)
    (fun z hz hzA => hz.elim id fun hzD => (Finset.disjoint_left.mp hD₂A hzD hzA).elim)
    (disjoint_singleton_left.mpr fun h =>
      h.elim hab fun hD => Finset.disjoint_left.mp hD₁A hD haA)
    (disjoint_singleton_left.mpr fun h =>
      h.elim hac fun hD => Finset.disjoint_left.mp hD₂A hD haA)
    (by
      rw [Set.disjoint_left]
      rintro z (rfl | hz₁) (rfl | hz₂)
      · exact hbc rfl
      · exact Finset.disjoint_left.mp hD₂A hz₂ hbA
      · exact Finset.disjoint_left.mp hD₁A hz₁ hcA
      · exact Finset.disjoint_left.mp hD₁₂ hz₁ hz₂)
    (preconnected_induce_singleton K a)
    (preconnected_induce_insert_of_adj hD₁_pre hxb₁ hbx₁)
    (preconnected_induce_insert_of_adj hD₂_pre hxc₂ hcx₂)
    ⟨a, rfl, xa₁, Or.inr hxa₁, hax₁⟩
    ⟨a, rfl, xa₂, Or.inr hxa₂, hax₂⟩
    ⟨b, Or.inl rfl, xb₂, Or.inr hxb₂, hbx₂⟩ hm

/-! ### Part 5: `3`-Cut Reduction 3 (a Component `D` of Size `≥ 2` Yields a Rooted `K_3`) -/

/-- Extending a `K`-path `p : K.Walk z x` inside `D` (`s ∉ D`, `K.Adj x s`) by the final step from
`x` to `s` and dropping the initial vertex `z` yields a preconnected set `W₀ ⊆ insert s D`
containing `s`, avoiding `z`, and containing a neighbor of `z`. -/
private theorem spoke_tail_set {N : ℕ} {K : SimpleGraph (Fin N)} {D : Finset (Fin N)}
    {z x s : Fin N} (hzD : z ∈ D) (hsD : s ∉ D)
    (p : K.Walk z x) (hp : p.IsPath) (hpD : ∀ u ∈ p.support, u ∈ D) (hxs : K.Adj x s) :
    ∃ W₀ : Set (Fin N),
      s ∈ W₀ ∧
      W₀ ⊆ insert s ((p.support.toFinset.erase z : Finset (Fin N)) : Set (Fin N)) ∧
      (K.induce W₀).Preconnected ∧
      ∃ v ∈ W₀, K.Adj z v := by
  classical
  have hs_not_p : s ∉ p.support := fun hs => hsD (hpD s hs)
  let p_ext : K.Walk z s := p.append (Walk.cons hxs .nil)
  have hp_ext : p_ext.IsPath := by
    refine HP25.isPath_append_of hp (Walk.IsPath.of_adj hxs) ?_
    intro y hy hys
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hys
    rcases hys with rfl | hys
    · rfl
    · exact (hs_not_p (hys ▸ hy)).elim
  have hzs : z ≠ s := fun h => hsD (h ▸ hzD)
  cases hp_eq : p_ext with
  | nil => exact (hzs (Walk.Nil.eq (hp_eq ▸ Walk.Nil.nil))).elim
  | @cons _ v _ hzv q =>
    have hq_nd : (z :: q.support).Nodup := by
      rw [hp_eq] at hp_ext
      simpa [Walk.isPath_def, Walk.support_cons] using hp_ext
    have hz_not_q : z ∉ q.support := (List.nodup_cons.mp hq_nd).1
    refine ⟨{u | u ∈ q.support}, q.end_mem_support, ?_, preconnected_induce_walk_support q,
      v, q.start_mem_support, hzv⟩
    intro u hu
    have hu_ext : u ∈ p_ext.support := by
      rw [hp_eq]
      exact List.mem_cons_of_mem z hu
    dsimp only [p_ext] at hu_ext
    rw [Walk.support_append, List.mem_append] at hu_ext
    rcases hu_ext with hup | hus
    · right
      simp only [Finset.mem_coe, Finset.mem_erase, List.mem_toFinset]
      exact ⟨fun h => hz_not_q (h ▸ hu), hup⟩
    · simp only [Walk.support_cons, Walk.support_nil, List.tail_cons,
        List.mem_singleton] at hus
      exact Or.inl hus

/-- Asymmetric star rerouting: given `S = {s₁, s₂, s₃}` (`3`-cut of `3`-connected `K`), component
`D` of `K - S`, center `z ∈ D`, and three paths `p₁, p₂, p₃` in `D` from `z` to neighbors `x₁, x₂, x₃`
of `s₁, s₂, s₃` meeting pairwise only at `z`, **if `z ≠ x₁`**, then `S ∪ D` contains a rooted `K_3`
`(W₁, W₂, W₃)` on `(s₁, s₂, s₃)`. -/
private theorem rooted_K3_of_nontrivial_spoke {N : ℕ} {K : SimpleGraph (Fin N)}
    (h3 : Is3ConnectedFin K) {S D : Finset (Fin N)} {s₁ s₂ s₃ : Fin N}
    (h12 : s₁ ≠ s₂) (h13 : s₁ ≠ s₃) (h23 : s₂ ≠ s₃) (hS : S = {s₁, s₂, s₃})
    (hDS : Disjoint D S)
    (hclosed : ∀ x ∈ D, ∀ y ∉ S, K.Adj x y → y ∈ D)
    {z x₁ x₂ x₃ : Fin N} (hzD : z ∈ D)
    (p₁ : K.Walk z x₁) (hp₁ : p₁.IsPath) (hp₁D : ∀ u ∈ p₁.support, u ∈ D) (hx₁ : K.Adj x₁ s₁)
    (p₂ : K.Walk z x₂) (hp₂ : p₂.IsPath) (hp₂D : ∀ u ∈ p₂.support, u ∈ D) (hx₂ : K.Adj x₂ s₂)
    (p₃ : K.Walk z x₃) (hp₃ : p₃.IsPath) (hp₃D : ∀ u ∈ p₃.support, u ∈ D) (hx₃ : K.Adj x₃ s₃)
    (h12_int : ∀ u ∈ p₁.support, u ∈ p₂.support → u = z)
    (h13_int : ∀ u ∈ p₁.support, u ∈ p₃.support → u = z)
    (h23_int : ∀ u ∈ p₂.support, u ∈ p₃.support → u = z)
    (hzx₁ : z ≠ x₁) :
    ∃ W₁ W₂ W₃ : Set (Fin N),
      s₁ ∈ W₁ ∧ s₂ ∈ W₂ ∧ s₃ ∈ W₃ ∧
      W₁ ⊆ insert s₁ (D : Set (Fin N)) ∧
      W₂ ⊆ insert s₂ (D : Set (Fin N)) ∧
      W₃ ⊆ insert s₃ (D : Set (Fin N)) ∧
      Disjoint W₁ W₂ ∧ Disjoint W₁ W₃ ∧ Disjoint W₂ W₃ ∧
      (K.induce W₁).Preconnected ∧ (K.induce W₂).Preconnected ∧ (K.induce W₃).Preconnected ∧
      (∃ u ∈ W₁, ∃ v ∈ W₂, K.Adj u v) ∧
      (∃ u ∈ W₁, ∃ v ∈ W₃, K.Adj u v) ∧
      (∃ u ∈ W₂, ∃ v ∈ W₃, K.Adj u v) := by
  classical
  have hs₁D : s₁ ∉ D := fun h => Finset.disjoint_left.mp hDS h (by simp [hS])
  have hs₂D : s₂ ∉ D := fun h => Finset.disjoint_left.mp hDS h (by simp [hS])
  have hs₃D : s₃ ∉ D := fun h => Finset.disjoint_left.mp hDS h (by simp [hS])
  obtain ⟨W₂₀, hs₂W, hW₂_sub, hW₂_pre, v₂, hv₂W, hzv₂⟩ := spoke_tail_set hzD hs₂D p₂ hp₂ hp₂D hx₂
  obtain ⟨W₃₀, hs₃W, hW₃_sub, hW₃_pre, v₃, hv₃W, hzv₃⟩ := spoke_tail_set hzD hs₃D p₃ hp₃ hp₃D hx₃
  have hW₂D : W₂₀ ⊆ insert s₂ (D : Set (Fin N)) := fun u hu =>
    (hW₂_sub hu).imp_right fun h => hp₂D u (List.mem_toFinset.mp (Finset.mem_of_mem_erase h))
  have hW₃D : W₃₀ ⊆ insert s₃ (D : Set (Fin N)) := fun u hu =>
    (hW₃_sub hu).imp_right fun h => hp₃D u (List.mem_toFinset.mp (Finset.mem_of_mem_erase h))
  have hz_not_W₂ : z ∉ W₂₀ := fun hz => by
    rcases hW₂_sub hz with rfl | h
    · exact hs₂D hzD
    · exact (Finset.mem_erase.mp h).1 rfl
  have hz_not_W₃ : z ∉ W₃₀ := fun hz => by
    rcases hW₃_sub hz with rfl | h
    · exact hs₃D hzD
    · exact (Finset.mem_erase.mp h).1 rfl
  have hdisj_23 : Disjoint W₂₀ W₃₀ := by
    rw [Set.disjoint_left]
    intro u hu₂ hu₃
    rcases hW₂_sub hu₂ with rfl | h₂ <;> rcases hW₃_sub hu₃ with rfl | h₃
    · exact h23 rfl
    · exact hs₂D (hp₃D _ (List.mem_toFinset.mp (Finset.mem_of_mem_erase h₃)))
    · exact hs₃D (hp₂D _ (List.mem_toFinset.mp (Finset.mem_of_mem_erase h₂)))
    · obtain ⟨huz, hup₂⟩ := Finset.mem_erase.mp h₂
      have hup₃ := List.mem_toFinset.mp (Finset.mem_of_mem_erase h₃)
      exact huz (h23_int u (List.mem_toFinset.mp hup₂) hup₃)
  -- Nonempty internal part of `p₁` (`z ≠ x₁`): `p₁ = .cons hzv₁ q₁` with `q₁` inside `D \ {z}`.
  cases p₁ with
  | nil => exact (hzx₁ rfl).elim
  | @cons _ v₁ _ hzv₁ q₁ =>
    have hq₁_nd : (z :: q₁.support).Nodup := by
      simpa [Walk.isPath_def, Walk.support_cons] using hp₁
    have hz_not_q₁ : z ∉ q₁.support := (List.nodup_cons.mp hq₁_nd).1
    let U₁ : Set (Fin N) := {u | u ∈ q₁.support}
    have hU₁D : ∀ u ∈ U₁, u ∈ D ∧ u ≠ z := fun u hu =>
      ⟨hp₁D u (List.mem_cons_of_mem z hu), fun h => hz_not_q₁ (h ▸ hu)⟩
    have hU₁_disj₂ : Disjoint U₁ W₂₀ := by
      rw [Set.disjoint_left]
      intro u hu₁ hu₂
      rcases hW₂_sub hu₂ with rfl | h₂
      · exact hs₂D (hU₁D u hu₁).1
      · exact (hU₁D u hu₁).2 (h12_int u (List.mem_cons_of_mem z hu₁)
          (List.mem_toFinset.mp (Finset.mem_of_mem_erase h₂)))
    have hU₁_disj₃ : Disjoint U₁ W₃₀ := by
      rw [Set.disjoint_left]
      intro u hu₁ hu₃
      rcases hW₃_sub hu₃ with rfl | h₃
      · exact hs₃D (hU₁D u hu₁).1
      · exact (hU₁D u hu₁).2 (h13_int u (List.mem_cons_of_mem z hu₁)
          (List.mem_toFinset.mp (Finset.mem_of_mem_erase h₃)))
    -- Connect `x₁ ∈ U₁` to `W₂₀ ∪ W₃₀` in `K - {z, s₁}` using `3`-connectedness!
    let Z : Finset (Fin N) := {z, s₁}
    have hZ_card : Z.card ≤ 2 := Finset.card_le_two
    have hconnZ : (K.induce {u : Fin N | u ∉ Z}).Connected := h3.2 Z hZ_card
    have hx₁_notZ : x₁ ∉ Z := by
      simp only [Z, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hzx₁.symm, fun h => hs₁D (h ▸ (hU₁D x₁ q₁.end_mem_support).1)⟩
    have hs₂_notZ : s₂ ∉ Z := by
      simp only [Z, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hs₂D (h ▸ hzD), h12.symm⟩
    obtain ⟨w₀⟩ := hconnZ.preconnected ⟨x₁, hx₁_notZ⟩ ⟨s₂, hs₂_notZ⟩
    let Target : Set {u : Fin N | u ∉ Z} := {u | u.1 ∈ W₂₀ ∪ W₃₀}
    obtain ⟨t, htT, r₀, _, hr_avoid, _⟩ :=
      HP25.exists_first_hit Target w₀ (Or.inl hs₂W)
    -- Every vertex of `r` before `t` stays inside `D \ {z}` (since `{s₂, s₃} ⊆ W₂₀ ∪ W₃₀`)!
    let r := r₀.bypass
    have hr_path : r.IsPath := r₀.bypass_isPath
    have hr_avoid' : ∀ u ∈ r.support, u ≠ t → u ∉ Target :=
      fun u hu hne => hr_avoid u (r₀.support_bypass_subset_support hu) hne
    have htx₁ : t ≠ ⟨x₁, hx₁_notZ⟩ := by
      intro heq
      have hx₁T : x₁ ∈ W₂₀ ∪ W₃₀ := by subst heq; exact htT
      exact hx₁T.elim
        (Set.disjoint_left.mp hU₁_disj₂ q₁.end_mem_support)
        (Set.disjoint_left.mp hU₁_disj₃ q₁.end_mem_support)
    have hr_rev_path : r.reverse.IsPath := hr_path.reverse
    cases hr_rev : r.reverse with
    | nil => exact (htx₁ rfl).elim
    | @cons _ u_hit _ h_tu r' =>
      have hr'_nd : (t :: r'.support).Nodup := by
        rw [hr_rev] at hr_rev_path
        simpa [Walk.isPath_def, Walk.support_cons] using hr_rev_path
      have ht_not_r' : t ∉ r'.support := (List.nodup_cons.mp hr'_nd).1
      have hr'_notT : ∀ u ∈ r'.support, u ∉ Target := by
        intro u hu
        have hu_rev : u ∈ r.reverse.support := by rw [hr_rev]; exact List.mem_cons_of_mem t hu
        exact hr_avoid' u ((mem_support_reverse_iff r).mp hu_rev) (fun h => ht_not_r' (h ▸ hu))
      have hr'_notS : ∀ u ∈ r'.support, u.1 ∉ S ∧ u.1 ≠ z := by
        intro u hu
        have huZ : u.1 ∉ Z := u.2
        simp only [Z, Finset.mem_insert, Finset.mem_singleton, not_or] at huZ
        have huT : u.1 ∉ W₂₀ ∪ W₃₀ := hr'_notT u hu
        refine ⟨?_, huZ.1⟩
        rw [hS]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨huZ.2, fun h => huT (Or.inl (h ▸ hs₂W)), fun h => huT (Or.inr (h ▸ hs₃W))⟩
      -- Walk `r'.reverse` starts at `x₁ ∈ D` and avoids `S`, so all its vertices lie in `D`!
      have hr'_inD : ∀ u ∈ r'.support, u.1 ∈ D := by
        have hwalkD : ∀ {a b : {u : Fin N | u ∉ Z}}
            (w : (K.induce {u : Fin N | u ∉ Z}).Walk a b),
            a.1 ∈ D → (∀ u ∈ w.support, u.1 ∉ S) → ∀ u ∈ w.support, u.1 ∈ D := by
          intro a b w
          induction w with
          | nil =>
            intro haD _ u hu
            rw [Walk.support_nil, List.mem_singleton] at hu
            exact hu ▸ haD
          | @cons a₁ a₂ a₃ ha12 w_tl ih =>
            intro ha₁D hnotS u hu
            rw [Walk.support_cons, List.mem_cons] at hu
            rcases hu with rfl | hu
            · exact ha₁D
            · have ha₂S : a₂.1 ∉ S := hnotS a₂ (by simp)
              exact ih (hclosed a₁.1 ha₁D a₂.1 ha₂S ha12)
                (fun q hq => hnotS q (by simp [hq])) u hu
        intro u hu
        exact hwalkD r'.reverse (hU₁D x₁ q₁.end_mem_support).1
          (fun q hq => (hr'_notS q ((mem_support_reverse_iff r').mp hq)).1)
          u ((mem_support_reverse_iff r').mpr hu)
      let rK : K.Walk u_hit.1 x₁ := r'.map ⟨Subtype.val, fun h => h⟩
      let R_set : Set (Fin N) := {y | y ∈ rK.support}
      have hR_mem : ∀ {y : Fin N}, y ∈ R_set ↔ ∃ u ∈ r'.support, u.1 = y := by
        intro y
        change y ∈ (r'.map ⟨Subtype.val, fun h => h⟩).support ↔ _
        rw [Walk.support_map, List.mem_map]
        rfl
      have hU₁R_pre : (K.induce (U₁ ∪ R_set)).Preconnected := by
        have hx₁U : x₁ ∈ U₁ := q₁.end_mem_support
        have hx₁R : x₁ ∈ R_set := rK.end_mem_support
        have hU₁_pre : (K.induce U₁).Preconnected := preconnected_induce_walk_support q₁
        have hR_pre : (K.induce R_set).Preconnected := preconnected_induce_walk_support rK
        have hx₁UR : x₁ ∈ U₁ ∪ R_set := Or.inl hx₁U
        have hto : ∀ y : ↥(U₁ ∪ R_set), (K.induce (U₁ ∪ R_set)).Reachable y ⟨x₁, hx₁UR⟩ := by
          rintro ⟨y, hyU | hyR⟩
          · exact induce_reachable_mono subset_union_left (hU₁_pre ⟨y, hyU⟩ ⟨x₁, hx₁U⟩)
          · exact induce_reachable_mono subset_union_right (hR_pre ⟨y, hyR⟩ ⟨x₁, hx₁R⟩)
        exact fun y₁ y₂ => (hto y₁).trans (hto y₂).symm
      let W₁ : Set (Fin N) := insert s₁ (U₁ ∪ R_set)
      have hs₁W : s₁ ∈ W₁ := mem_insert _ _
      have hW₁_pre : (K.induce W₁).Preconnected :=
        preconnected_induce_insert_of_adj hU₁R_pre (Or.inl q₁.end_mem_support) hx₁.symm
      have hW₁_sub : W₁ ⊆ insert s₁ (D : Set (Fin N)) := by
        rintro y (rfl | hyU | hyR)
        · exact Or.inl rfl
        · exact Or.inr (hU₁D y hyU).1
        · obtain ⟨u, hu, rfl⟩ := hR_mem.mp hyR
          exact Or.inr (hr'_inD u hu)
      have hz_not_W₁ : z ∉ W₁ := by
        rintro (h | hzU | hzR)
        · exact hs₁D (h ▸ hzD)
        · exact (hU₁D z hzU).2 rfl
        · obtain ⟨u, hu, huz⟩ := hR_mem.mp hzR
          exact (hr'_notS u hu).2 huz
      have hW₁_disj₂ : Disjoint W₁ W₂₀ := by
        rw [Set.disjoint_left]
        rintro y (rfl | hyU | hyR) hy₂
        · rcases hW₂_sub hy₂ with h | h
          · exact h12 h
          · exact hs₁D (hp₂D _ (List.mem_toFinset.mp (Finset.mem_of_mem_erase h)))
        · exact Set.disjoint_left.mp hU₁_disj₂ hyU hy₂
        · obtain ⟨u, hu, rfl⟩ := hR_mem.mp hyR
          exact hr'_notT u hu (Or.inl hy₂)
      have hW₁_disj₃ : Disjoint W₁ W₃₀ := by
        rw [Set.disjoint_left]
        rintro y (rfl | hyU | hyR) hy₃
        · rcases hW₃_sub hy₃ with h | h
          · exact h13 h
          · exact hs₁D (hp₃D _ (List.mem_toFinset.mp (Finset.mem_of_mem_erase h)))
        · exact Set.disjoint_left.mp hU₁_disj₃ hyU hy₃
        · obtain ⟨u, hu, rfl⟩ := hR_mem.mp hyR
          exact hr'_notT u hu (Or.inr hy₃)
      have hv₁_W₁ : v₁ ∈ W₁ := Or.inr (Or.inl q₁.start_mem_support)
      have huhit_W₁ : u_hit.1 ∈ W₁ := Or.inr (Or.inr rK.start_mem_support)
      have hK_uhit_t : K.Adj u_hit.1 t.1 := h_tu.symm
      rcases htT with ht₂ | ht₃
      · refine ⟨W₁, W₂₀, insert z W₃₀,
          hs₁W, hs₂W, mem_insert_of_mem z hs₃W,
          hW₁_sub, hW₂D,
          fun y hy => hy.elim (fun h => Or.inr (h ▸ hzD)) (fun h => hW₃D h),
          hW₁_disj₂,
          disjoint_insert_right.mpr ⟨hz_not_W₁, hW₁_disj₃⟩,
          disjoint_insert_right.mpr ⟨hz_not_W₂, hdisj_23⟩,
          hW₁_pre, hW₂_pre,
          preconnected_induce_insert_of_adj hW₃_pre hv₃W hzv₃,
          ⟨u_hit.1, huhit_W₁, t.1, ht₂, hK_uhit_t⟩,
          ⟨v₁, hv₁_W₁, z, mem_insert _ _, hzv₁.symm⟩,
          ⟨v₂, hv₂W, z, mem_insert _ _, hzv₂.symm⟩⟩
      · refine ⟨W₁, insert z W₂₀, W₃₀,
          hs₁W, mem_insert_of_mem z hs₂W, hs₃W,
          hW₁_sub,
          fun y hy => hy.elim (fun h => Or.inr (h ▸ hzD)) (fun h => hW₂D h),
          hW₃D,
          disjoint_insert_right.mpr ⟨hz_not_W₁, hW₁_disj₂⟩,
          hW₁_disj₃,
          disjoint_insert_left.mpr ⟨hz_not_W₃, hdisj_23⟩,
          hW₁_pre,
          preconnected_induce_insert_of_adj hW₂_pre hv₂W hzv₂,
          hW₃_pre,
          ⟨v₁, hv₁_W₁, z, mem_insert _ _, hzv₁.symm⟩,
          ⟨u_hit.1, huhit_W₁, t.1, ht₃, hK_uhit_t⟩,
          ⟨z, mem_insert _ _, v₃, hv₃W, hzv₃⟩⟩

/-- Helper for the star-apex subcase: if `z ∈ D` is directly adjacent to `s₁, s₂, s₃` and `C ⊆ D \ {z}`
is preconnected and adjacent to both `s₁` and `s₂`, then `({s₁} ∪ C, {s₂}, {s₃, z})` is a rooted `K_3`. -/
private theorem rooted_K3_of_apex_and_two_att {N : ℕ} {K : SimpleGraph (Fin N)}
    {D C : Finset (Fin N)} {s₁ s₂ s₃ z : Fin N}
    (h12 : s₁ ≠ s₂) (h13 : s₁ ≠ s₃) (h23 : s₂ ≠ s₃)
    (hs₁D : s₁ ∉ D) (hs₂D : s₂ ∉ D) (hs₃D : s₃ ∉ D)
    (hzD : z ∈ D) (hCD : C ⊆ D.erase z)
    (hC_pre : (K.induce (C : Set (Fin N))).Preconnected)
    (hz1 : K.Adj s₁ z) (hz2 : K.Adj s₂ z) (hz3 : K.Adj s₃ z)
    (hc1 : ∃ x ∈ C, K.Adj s₁ x) (hc2 : ∃ x ∈ C, K.Adj s₂ x) :
    ∃ W₁ W₂ W₃ : Set (Fin N),
      s₁ ∈ W₁ ∧ s₂ ∈ W₂ ∧ s₃ ∈ W₃ ∧
      W₁ ⊆ insert s₁ (D : Set (Fin N)) ∧
      W₂ ⊆ insert s₂ (D : Set (Fin N)) ∧
      W₃ ⊆ insert s₃ (D : Set (Fin N)) ∧
      Disjoint W₁ W₂ ∧ Disjoint W₁ W₃ ∧ Disjoint W₂ W₃ ∧
      (K.induce W₁).Preconnected ∧ (K.induce W₂).Preconnected ∧ (K.induce W₃).Preconnected ∧
      (∃ u ∈ W₁, ∃ v ∈ W₂, K.Adj u v) ∧
      (∃ u ∈ W₁, ∃ v ∈ W₃, K.Adj u v) ∧
      (∃ u ∈ W₂, ∃ v ∈ W₃, K.Adj u v) := by
  obtain ⟨x₁, hx₁C, hs₁x₁⟩ := hc1
  obtain ⟨x₂, hx₂C, hs₂x₂⟩ := hc2
  have hCD' : ∀ u ∈ C, u ∈ D ∧ u ≠ z := fun u hu => by
    have h := Finset.mem_erase.mp (hCD hu)
    exact ⟨h.2, h.1⟩
  refine ⟨insert s₁ (C : Set (Fin N)), {s₂}, {s₃, z},
    mem_insert _ _, rfl, mem_insert _ _,
    fun u hu => hu.imp_right fun h => (hCD' u h).1,
    singleton_subset_iff.mpr (mem_insert _ _),
    by rintro u (rfl | rfl); exact Or.inl rfl; exact Or.inr hzD,
    disjoint_singleton_right.mpr fun h =>
      h.elim h12.symm fun hC => hs₂D (hCD' _ hC).1,
    by
      rw [Set.disjoint_left]
      rintro u (rfl | huC) (rfl | rfl)
      · exact h13 rfl
      · exact hs₁D hzD
      · exact hs₃D (hCD' _ huC).1
      · exact (hCD' _ huC).2 rfl,
    disjoint_singleton_left.mpr fun h =>
      h.elim h23 fun h => hs₂D (h ▸ hzD),
    preconnected_induce_insert_of_adj hC_pre hx₁C hs₁x₁,
    preconnected_induce_singleton K s₂,
    by
      have hpre_z := preconnected_induce_singleton K z
      simpa [pair_comm] using preconnected_induce_insert_of_adj hpre_z rfl hz3,
    ⟨x₂, Or.inr hx₂C, s₂, rfl, hs₂x₂.symm⟩,
    ⟨s₁, Or.inl rfl, z, Or.inr rfl, hz1⟩,
    ⟨s₂, rfl, z, Or.inr rfl, hz2⟩⟩

/-- Permuting a rooted `K_3` `(W₁, W₂, W₃)` by swapping the first two slots. -/
private theorem perm_rooted_K3_12 {N : ℕ} {K : SimpleGraph (Fin N)} {D : Finset (Fin N)}
    {a b c : Fin N}
    (hex : ∃ Wb Wa Wc : Set (Fin N),
      b ∈ Wb ∧ a ∈ Wa ∧ c ∈ Wc ∧
      Wb ⊆ insert b (D : Set (Fin N)) ∧
      Wa ⊆ insert a (D : Set (Fin N)) ∧
      Wc ⊆ insert c (D : Set (Fin N)) ∧
      Disjoint Wb Wa ∧ Disjoint Wb Wc ∧ Disjoint Wa Wc ∧
      (K.induce Wb).Preconnected ∧ (K.induce Wa).Preconnected ∧ (K.induce Wc).Preconnected ∧
      (∃ u ∈ Wb, ∃ v ∈ Wa, K.Adj u v) ∧
      (∃ u ∈ Wb, ∃ v ∈ Wc, K.Adj u v) ∧
      (∃ u ∈ Wa, ∃ v ∈ Wc, K.Adj u v)) :
    ∃ Wa Wb Wc : Set (Fin N),
      a ∈ Wa ∧ b ∈ Wb ∧ c ∈ Wc ∧
      Wa ⊆ insert a (D : Set (Fin N)) ∧
      Wb ⊆ insert b (D : Set (Fin N)) ∧
      Wc ⊆ insert c (D : Set (Fin N)) ∧
      Disjoint Wa Wb ∧ Disjoint Wa Wc ∧ Disjoint Wb Wc ∧
      (K.induce Wa).Preconnected ∧ (K.induce Wb).Preconnected ∧ (K.induce Wc).Preconnected ∧
      (∃ u ∈ Wa, ∃ v ∈ Wb, K.Adj u v) ∧
      (∃ u ∈ Wa, ∃ v ∈ Wc, K.Adj u v) ∧
      (∃ u ∈ Wb, ∃ v ∈ Wc, K.Adj u v) := by
  obtain ⟨Wb, Wa, Wc, hb, ha, hc, hsB, hsA, hsC, hdBA, hdBC, hdAC, hcB, hcA, hcC,
    ⟨u, hu, v, hv, huv⟩, eBC, eAC⟩ := hex
  exact ⟨Wa, Wb, Wc, ha, hb, hc, hsA, hsB, hsC, hdBA.symm, hdAC, hdBC, hcA, hcB, hcC,
    ⟨v, hv, u, hu, huv.symm⟩, eAC, eBC⟩

/-- Permuting a rooted `K_3` `(W₁, W₂, W₃)` by swapping the first and third slots. -/
private theorem perm_rooted_K3_13 {N : ℕ} {K : SimpleGraph (Fin N)} {D : Finset (Fin N)}
    {a b c : Fin N}
    (hex : ∃ Wc Wb Wa : Set (Fin N),
      c ∈ Wc ∧ b ∈ Wb ∧ a ∈ Wa ∧
      Wc ⊆ insert c (D : Set (Fin N)) ∧
      Wb ⊆ insert b (D : Set (Fin N)) ∧
      Wa ⊆ insert a (D : Set (Fin N)) ∧
      Disjoint Wc Wb ∧ Disjoint Wc Wa ∧ Disjoint Wb Wa ∧
      (K.induce Wc).Preconnected ∧ (K.induce Wb).Preconnected ∧ (K.induce Wa).Preconnected ∧
      (∃ u ∈ Wc, ∃ v ∈ Wb, K.Adj u v) ∧
      (∃ u ∈ Wc, ∃ v ∈ Wa, K.Adj u v) ∧
      (∃ u ∈ Wb, ∃ v ∈ Wa, K.Adj u v)) :
    ∃ Wa Wb Wc : Set (Fin N),
      a ∈ Wa ∧ b ∈ Wb ∧ c ∈ Wc ∧
      Wa ⊆ insert a (D : Set (Fin N)) ∧
      Wb ⊆ insert b (D : Set (Fin N)) ∧
      Wc ⊆ insert c (D : Set (Fin N)) ∧
      Disjoint Wa Wb ∧ Disjoint Wa Wc ∧ Disjoint Wb Wc ∧
      (K.induce Wa).Preconnected ∧ (K.induce Wb).Preconnected ∧ (K.induce Wc).Preconnected ∧
      (∃ u ∈ Wa, ∃ v ∈ Wb, K.Adj u v) ∧
      (∃ u ∈ Wa, ∃ v ∈ Wc, K.Adj u v) ∧
      (∃ u ∈ Wb, ∃ v ∈ Wc, K.Adj u v) := by
  obtain ⟨Wc, Wb, Wa, hc, hb, ha, hsC, hsB, hsA, hdCB, hdCA, hdBA, hcC, hcB, hcA,
    ⟨u₁, hu₁, v₁, hv₁, h1⟩, ⟨u₂, hu₂, v₂, hv₂, h2⟩, ⟨u₃, hu₃, v₃, hv₃, h3⟩⟩ := hex
  exact ⟨Wa, Wb, Wc, ha, hb, hc, hsA, hsB, hsC, hdBA.symm, hdCA.symm, hdCB.symm, hcA, hcB, hcC,
    ⟨v₃, hv₃, u₃, hu₃, h3.symm⟩, ⟨v₂, hv₂, u₂, hu₂, h2.symm⟩, ⟨v₁, hv₁, u₁, hu₁, h1.symm⟩⟩

/-- **`3`-Cut Reduction 3**: if `K` is `3`-connected, `S = {a, b, c}` is a `3`-cut, and `D` is a
connected component of `K - S` with `2 ≤ D.card` adjacent to `a, b, c`, then `S ∪ D` contains a
rooted `K_3` on `(a, b, c)`, so any `K_5` minor of `torsoOn K A S` (`D ⊆ Aᶜ`) lifts to `K`. -/
private theorem hasK5MinorSimple_of_three_cut_comp_ge_two {N : ℕ} {K : SimpleGraph (Fin N)}
    (h3 : Is3ConnectedFin K) {A S D : Finset (Fin N)} {a b c : Fin N}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hS : S = {a, b, c}) (hSA : S ⊆ A)
    (hDA : Disjoint D A) (hD_card : 2 ≤ D.card)
    (hD_pre : (K.induce (D : Set (Fin N))).Preconnected)
    (hclosed : ∀ x ∈ D, ∀ y ∉ S, K.Adj x y → y ∈ D)
    (haD : ∃ x ∈ D, K.Adj a x) (hbD : ∃ x ∈ D, K.Adj b x) (hcD : ∃ x ∈ D, K.Adj c x)
    (hm : HasK5MinorSimple (torsoOn K A S)) : HasK5MinorSimple K := by
  classical
  have hDS : Disjoint D S := hDA.mono_right hSA
  have hs_notD : ∀ s ∈ S, s ∉ D := fun s hs hD => Finset.disjoint_left.mp hDS hD hs
  have ha_notD : a ∉ D := hs_notD a (by simp [hS])
  have hb_notD : b ∉ D := hs_notD b (by simp [hS])
  have hc_notD : c ∉ D := hs_notD c (by simp [hS])
  -- Suffices to construct `(Wa, Wb, Wc)` inside `insert s D`!
  suffices hrootK3 : ∃ Wa Wb Wc : Set (Fin N),
      a ∈ Wa ∧ b ∈ Wb ∧ c ∈ Wc ∧
      Wa ⊆ insert a (D : Set (Fin N)) ∧
      Wb ⊆ insert b (D : Set (Fin N)) ∧
      Wc ⊆ insert c (D : Set (Fin N)) ∧
      Disjoint Wa Wb ∧ Disjoint Wa Wc ∧ Disjoint Wb Wc ∧
      (K.induce Wa).Preconnected ∧ (K.induce Wb).Preconnected ∧ (K.induce Wc).Preconnected ∧
      (∃ u ∈ Wa, ∃ v ∈ Wb, K.Adj u v) ∧
      (∃ u ∈ Wa, ∃ v ∈ Wc, K.Adj u v) ∧
      (∃ u ∈ Wb, ∃ v ∈ Wc, K.Adj u v) by
    obtain ⟨Wa, Wb, Wc, ha, hb, hc, hsA, hsB, hsC, hdAB, hdAC, hdBC, hcA, hcB, hcC,
      eAB, eAC, eBC⟩ := hrootK3
    exact hasK5MinorSimple_of_three_cut_witness hab hac hbc hS hSA Wa Wb Wc ha hb hc
      (fun z hz hzA => (hsA hz).elim id fun hzD => (Finset.disjoint_left.mp hDA hzD hzA).elim)
      (fun z hz hzA => (hsB hz).elim id fun hzD => (Finset.disjoint_left.mp hDA hzD hzA).elim)
      (fun z hz hzA => (hsC hz).elim id fun hzD => (Finset.disjoint_left.mp hDA hzD hzA).elim)
      hdAB hdAC hdBC hcA hcB hcC eAB eAC eBC hm
  by_cases hapex : ∃ z ∈ D, K.Adj a z ∧ K.Adj b z ∧ K.Adj c z
  · -- Subcase 3b: some `z ∈ D` is directly adjacent to `a, b, c`. Pick `w ∈ D \ {z}`.
    obtain ⟨z, hzD, hza, hzb, hzc⟩ := hapex
    have hDz_pos : 0 < (D.erase z).card := by
      rw [Finset.card_erase_of_mem hzD]
      omega
    obtain ⟨w, hwDz⟩ := Finset.card_pos.mp hDz_pos
    let Z₀ : Finset (Fin N) := insert z S
    have hw_notZ₀ : w ∉ Z₀ := by
      simp only [Z₀, Finset.mem_insert, not_or]
      exact ⟨(Finset.mem_erase.mp hwDz).1, fun hS' => hs_notD w hS' (Finset.mem_of_mem_erase hwDz)⟩
    let C : Finset (Fin N) := compFinset K Z₀ ⟨w, hw_notZ₀⟩
    have hwC : w ∈ C := mem_compFinset_self ⟨w, hw_notZ₀⟩
    have hC_pre : (K.induce (C : Set (Fin N))).Preconnected := preconnected_compFinset ⟨w, hw_notZ₀⟩
    have hCD : C ⊆ D.erase z := by
      intro u hu
      obtain ⟨_, huZ₀, ⟨q⟩⟩ := Finset.mem_filter.mp hu
      have hwalk : ∀ {x y : {v : Fin N | v ∉ Z₀}}
          (r : (K.induce {v : Fin N | v ∉ Z₀}).Walk x y),
          x.1 ∈ D → y.1 ∈ D := by
        intro x y r
        induction r with
        | nil => exact id
        | @cons x₁ x₂ x₃ hx12 r' ih =>
          intro hx₁D
          have hx₂S : x₂.1 ∉ S := fun hs => x₂.2 (Finset.mem_insert_of_mem hs)
          exact ih (hclosed x₁.1 hx₁D x₂.1 hx₂S hx12)
      refine Finset.mem_erase.mpr ⟨fun h => huZ₀ (h ▸ Finset.mem_insert_self z S), ?_⟩
      exact hwalk q (Finset.mem_of_mem_erase hwDz)
    -- For any `s ∈ S`, `K - {z, s}` is connected, so `C` is adjacent to one of `S \ {s}`!
    have hC_att : ∀ (s t₁ t₂ : Fin N), S = {s, t₁, t₂} → s ≠ t₁ →
        (∃ x ∈ C, K.Adj t₁ x) ∨ (∃ x ∈ C, K.Adj t₂ x) := by
      intro s t₁ t₂ hSt hst₁
      have hcard2 : ({z, s} : Finset (Fin N)).card ≤ 2 := Finset.card_le_two
      have hconn2 : (K.induce {v : Fin N | v ∉ ({z, s} : Finset (Fin N))}).Connected :=
        h3.2 {z, s} hcard2
      have hw_not2 : w ∉ ({z, s} : Finset (Fin N)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨(Finset.mem_erase.mp hwDz).1,
          fun hws => hs_notD s (by simp [hSt]) (hws ▸ Finset.mem_of_mem_erase hwDz)⟩
      have ht₁_not2 : t₁ ∉ ({z, s} : Finset (Fin N)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun htz => hs_notD t₁ (by simp [hSt]) (htz ▸ hzD), hst₁.symm⟩
      obtain ⟨q⟩ := hconn2.preconnected ⟨w, hw_not2⟩ ⟨t₁, ht₁_not2⟩
      have hwalk : ∀ {x y : {v : Fin N | v ∉ ({z, s} : Finset (Fin N))}}
          (r : (K.induce {v : Fin N | v ∉ ({z, s} : Finset (Fin N))}).Walk x y),
          x.1 ∈ C → y.1 ∉ C → (∃ u ∈ C, K.Adj t₁ u) ∨ (∃ u ∈ C, K.Adj t₂ u) := by
        intro x y r
        induction r with
        | nil => intro hx hy; exact (hy hx).elim
        | @cons x₁ x₂ x₃ hx12 r' ih =>
          intro hx₁C hx₃C
          by_cases hx₂S : x₂.1 ∈ S
          · rw [hSt] at hx₂S
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx₂S
            rcases hx₂S with hxs | hxt₁ | hxt₂
            · exact (x₂.2 (by simp [hxs])).elim
            · exact Or.inl ⟨x₁.1, hx₁C, hxt₁ ▸ hx12.symm⟩
            · exact Or.inr ⟨x₁.1, hx₁C, hxt₂ ▸ hx12.symm⟩
          · have hx₂Z₀ : x₂.1 ∉ Z₀ := by
              simp only [Z₀, Finset.mem_insert, not_or]
              exact ⟨fun h => x₂.2 (by simp [h]), hx₂S⟩
            exact ih (compFinset_closed hx₁C hx₂Z₀ hx12) hx₃C
      exact hwalk q hwC (fun htC => hs_notD t₁ (by simp [hSt])
        (Finset.mem_of_mem_erase (hCD htC)))
    rcases hC_att a b c hS hab with hCb | hCc
    · have hS_bac : S = {b, a, c} := by ext u; rw [hS]; simp; tauto
      rcases hC_att b a c hS_bac hab.symm with hCa | hCc
      · exact rooted_K3_of_apex_and_two_att hab hac hbc ha_notD hb_notD hc_notD
          hzD hCD hC_pre hza hzb hzc hCa hCb
      · exact perm_rooted_K3_12 (rooted_K3_of_apex_and_two_att hbc hab.symm hac.symm hb_notD
          hc_notD ha_notD hzD hCD hC_pre hzb hzc hza hCb hCc |> fun hex => by
            obtain ⟨Wb, Wc, Wa, hb, hc, ha, sB, sC, sA, dBC, dBA, dCA, cB, cC, cA,
              eBC, eBA, ⟨u, hu, v, hv, huv⟩⟩ := hex
            exact ⟨Wb, Wa, Wc, hb, ha, hc, sB, sA, sC, dBA, dBC, dCA.symm, cB, cA, cC,
              eBA, eBC, ⟨v, hv, u, hu, huv.symm⟩⟩)
    · have hS_cab : S = {c, a, b} := by ext u; rw [hS]; simp; tauto
      rcases hC_att c a b hS_cab hac.symm with hCa | hCb
      · obtain ⟨Wa, Wc, Wb, ha, hc, hb, sA, sC, sB, dAC, dAB, dCB, cA, cC, cB,
          eAC, eAB, ⟨u, hu, v, hv, huv⟩⟩ :=
          rooted_K3_of_apex_and_two_att hac hab hbc.symm ha_notD hc_notD hb_notD
            hzD hCD hC_pre hza hzc hzb hCa hCc
        exact ⟨Wa, Wb, Wc, ha, hb, hc, sA, sB, sC, dAB, dAC, dCB.symm, cA, cB, cC,
          eAB, eAC, ⟨v, hv, u, hu, huv.symm⟩⟩
      · obtain ⟨Wc, Wb, Wa, hc, hb, ha, sC, sB, sA, dCB, dCA, dBA, cC, cB, cA,
          eCB, eCA, eBA⟩ :=
          rooted_K3_of_apex_and_two_att hbc.symm hac.symm hab.symm hc_notD hb_notD ha_notD
            hzD hCD hC_pre hzc hzb hza hCc hCb
        exact perm_rooted_K3_13 ⟨Wc, Wb, Wa, hc, hb, ha, sC, sB, sA, dCB, dCA, dBA, cC, cB, cA,
          eCB, eCA, eBA⟩
  · -- Subcase 3a: build a `3`-star at some `z ∈ D` to `xa, xb, xc ∈ D`; at least one spoke is nontrivial!
    obtain ⟨xa, hxa, hax⟩ := haD
    obtain ⟨xb, hxb, hbx⟩ := hbD
    obtain ⟨xc, hxc, hcx⟩ := hcD
    obtain ⟨P_ab, hP_ab⟩ := (hD_pre ⟨xa, hxa⟩ ⟨xb, hxb⟩).exists_isPath
    obtain ⟨W_ca⟩ := hD_pre ⟨xc, hxc⟩ ⟨xa, hxa⟩
    obtain ⟨z, hz_sup, Q₀, _, hQ₀_avoid, _⟩ :=
      HP25.exists_first_hit {u : (D : Set (Fin N)) | u ∈ P_ab.support} W_ca P_ab.start_mem_support
    let Q_c := Q₀.bypass
    have hQ_c : Q_c.IsPath := Q₀.bypass_isPath
    have hQ_avoid : ∀ u ∈ Q_c.support, u ≠ z → u ∉ P_ab.support :=
      fun u hu hne => hQ₀_avoid u (Q₀.support_bypass_subset_support hu) hne
    let fD : K.induce (D : Set (Fin N)) →g K := ⟨Subtype.val, fun h => h⟩
    have isPath_map_fD : ∀ {u v : (D : Set (Fin N))} {w : (K.induce (D : Set (Fin N))).Walk u v},
        w.IsPath → (w.map fD).IsPath := by
      intro u v w hw
      rw [Walk.isPath_def, Walk.support_map]
      exact ((Walk.isPath_def w).mp hw).map Subtype.val_injective
    let q_a := (P_ab.takeUntil z hz_sup).reverse
    let q_b := P_ab.dropUntil z hz_sup
    let q_c := Q_c.reverse
    let p_a : K.Walk z.1 xa := q_a.map fD
    let p_b : K.Walk z.1 xb := q_b.map fD
    let p_c : K.Walk z.1 xc := q_c.map fD
    have hp_a : p_a.IsPath := isPath_map_fD (hP_ab.takeUntil hz_sup).reverse
    have hp_b : p_b.IsPath := isPath_map_fD (hP_ab.dropUntil hz_sup)
    have hp_c : p_c.IsPath := isPath_map_fD hQ_c.reverse
    have mem_map_fD : ∀ {u v : (D : Set (Fin N))} (w : (K.induce (D : Set (Fin N))).Walk u v)
        {y : Fin N}, y ∈ (w.map fD).support ↔ ∃ u' ∈ w.support, u'.1 = y := by
      intro u v w y
      rw [Walk.support_map, List.mem_map]
      rfl
    have hp_aD : ∀ y ∈ p_a.support, y ∈ D := by
      intro y hy; obtain ⟨u', _, rfl⟩ := (mem_map_fD q_a).mp hy; exact u'.2
    have hp_bD : ∀ y ∈ p_b.support, y ∈ D := by
      intro y hy; obtain ⟨u', _, rfl⟩ := (mem_map_fD q_b).mp hy; exact u'.2
    have hp_cD : ∀ y ∈ p_c.support, y ∈ D := by
      intro y hy; obtain ⟨u', _, rfl⟩ := (mem_map_fD q_c).mp hy; exact u'.2
    have hab_int : ∀ y ∈ p_a.support, y ∈ p_b.support → y = z.1 := by
      intro y hya hyb
      obtain ⟨u₁, hu₁, rfl⟩ := (mem_map_fD q_a).mp hya
      obtain ⟨u₂, hu₂, heq⟩ := (mem_map_fD q_b).mp hyb
      have hu12 : u₁ = u₂ := Subtype.ext heq.symm
      subst hu12
      have h_app : ((P_ab.takeUntil z hz_sup).append (P_ab.dropUntil z hz_sup)).IsPath := by
        simpa only [Walk.take_spec] using hP_ab
      exact congrArg Subtype.val
        (HP25.eq_of_mem_append_path h_app
          ((mem_support_reverse_iff (P_ab.takeUntil z hz_sup)).mp hu₁) hu₂)
    have hac_int : ∀ y ∈ p_a.support, y ∈ p_c.support → y = z.1 := by
      intro y hya hyc
      obtain ⟨u₁, hu₁, rfl⟩ := (mem_map_fD q_a).mp hya
      obtain ⟨u₂, hu₂, heq⟩ := (mem_map_fD q_c).mp hyc
      have hu12 : u₁ = u₂ := Subtype.ext heq.symm
      subst hu12
      by_contra hne_z
      have hne_sub : u₁ ≠ z := fun h => hne_z (congrArg Subtype.val h)
      exact hQ_avoid u₁ ((mem_support_reverse_iff Q_c).mp hu₂) hne_sub
        (P_ab.support_takeUntil_subset_support hz_sup
          ((mem_support_reverse_iff (P_ab.takeUntil z hz_sup)).mp hu₁))
    have hbc_int : ∀ y ∈ p_b.support, y ∈ p_c.support → y = z.1 := by
      intro y hyb hyc
      obtain ⟨u₁, hu₁, rfl⟩ := (mem_map_fD q_b).mp hyb
      obtain ⟨u₂, hu₂, heq⟩ := (mem_map_fD q_c).mp hyc
      have hu12 : u₁ = u₂ := Subtype.ext heq.symm
      subst hu12
      by_contra hne_z
      have hne_sub : u₁ ≠ z := fun h => hne_z (congrArg Subtype.val h)
      have hmem_P : u₁ ∈ P_ab.support := by
        rw [← P_ab.take_spec hz_sup]
        exact (Walk.mem_support_append_iff _ _).mpr (Or.inr hu₁)
      exact hQ_avoid u₁ ((mem_support_reverse_iff Q_c).mp hu₂) hne_sub hmem_P
    by_cases hza_ne : z.1 ≠ xa
    · exact rooted_K3_of_nontrivial_spoke h3 hab hac hbc hS hDS hclosed z.2
        p_a hp_a hp_aD hax.symm p_b hp_b hp_bD hbx.symm p_c hp_c hp_cD hcx.symm
        hab_int hac_int hbc_int hza_ne
    · by_cases hzb_ne : z.1 ≠ xb
      · have hS_bac : S = {b, a, c} := by ext u; rw [hS]; simp; tauto
        exact perm_rooted_K3_12 (rooted_K3_of_nontrivial_spoke h3 hab.symm hbc hac hS_bac hDS
          hclosed z.2 p_b hp_b hp_bD hbx.symm p_a hp_a hp_aD hax.symm p_c hp_c hp_cD hcx.symm
          (fun u hb' ha' => hab_int u ha' hb') hbc_int hac_int hzb_ne)
      · have hzc_ne : z.1 ≠ xc := by
          push Not at hza_ne hzb_ne
          intro hzc_eq
          exact hapex ⟨z.1, z.2, hza_ne ▸ hax, hzb_ne ▸ hbx, hzc_eq ▸ hcx⟩
        have hS_cba : S = {c, b, a} := by ext u; rw [hS]; simp; tauto
        exact perm_rooted_K3_13 (rooted_K3_of_nontrivial_spoke h3 hbc.symm hac.symm hab.symm
          hS_cba hDS hclosed z.2 p_c hp_c hp_cD hcx.symm p_b hp_b hp_bD hbx.symm p_a hp_a hp_aD
          hax.symm (fun u hc' hb' => hbc_int u hb' hc') (fun u hc' ha' => hac_int u ha' hc')
          (fun u hb' ha' => hab_int u ha' hb') hzc_ne)

/-! ### Part 6: Main Connectivity Reduction to `IsInternally4ConnFin` -/

/-- Helper packaging the standard separation properties of `A₁ = S ∪ D` and `A₂ = Finset.univ \ D`
for a component `D` of `K - S` with `p ∈ D` and `q ∉ S ∪ D`. -/
private theorem sep_of_compFinset {N : ℕ} {K : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    (hS : S.card ≤ 3) {p q : {x : Fin N // x ∉ S}} (hq : q.1 ∉ compFinset K S p) :
    let D := compFinset K S p
    let A₁ := S ∪ D
    let A₂ := Finset.univ \ D
    A₁ ∪ A₂ = Finset.univ ∧ A₁.card < N ∧ A₂.card < N ∧ A₁ ∩ A₂ = S ∧ (A₁ ∩ A₂).card ≤ 3 ∧
    (∀ x y, K.Adj x y → (x ∈ A₁ ∧ y ∈ A₁) ∨ (x ∈ A₂ ∧ y ∈ A₂)) := by
  classical
  intro D A₁ A₂
  have hDS : Disjoint D S := Finset.disjoint_left.mpr fun _ hx => notMem_of_mem_compFinset hx
  have hA₁_union : A₁ ∪ A₂ = Finset.univ := by
    ext x
    simp only [A₁, A₂, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    exact (em (x ∈ D)).imp_left Or.inr
  have hq_notA₁ : q.1 ∉ A₁ := by
    simp only [A₁, Finset.mem_union, not_or]
    exact ⟨q.2, hq⟩
  have hp_notA₂ : p.1 ∉ A₂ := by
    simp only [A₂, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
    exact mem_compFinset_self p
  have hA₁_lt : A₁.card < N := by
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ A₁, fun h => hq_notA₁ (h ▸ Finset.mem_univ q.1)⟩)
    simpa using hlt
  have hA₂_lt : A₂.card < N := by
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ A₂, fun h => hp_notA₂ (h ▸ Finset.mem_univ p.1)⟩)
    simpa using hlt
  have hInter : A₁ ∩ A₂ = S := by
    ext x
    simp only [A₁, A₂, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨hxS | hxD, hx_notD⟩
      · exact hxS
      · exact (hx_notD hxD).elim
    · intro hxS
      exact ⟨Or.inl hxS, fun hxD => notMem_of_mem_compFinset hxD hxS⟩
  refine ⟨hA₁_union, hA₁_lt, hA₂_lt, hInter, hInter ▸ hS, ?_⟩
  intro x y hxy
  by_cases hxD : x ∈ D
  · left
    refine ⟨Finset.mem_union_right _ hxD, ?_⟩
    by_cases hyS : y ∈ S
    · exact Finset.mem_union_left _ hyS
    · exact Finset.mem_union_right _ (compFinset_closed hxD hyS hxy)
  · by_cases hyD : y ∈ D
    · left
      refine ⟨?_, Finset.mem_union_right _ hyD⟩
      by_cases hxS : x ∈ S
      · exact Finset.mem_union_left _ hxS
      · exact Finset.mem_union_right _ (compFinset_closed hyD hxS hxy.symm)
    · right
      exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxD⟩,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyD⟩⟩

/-- Unpacks `S.card = 3` into three pairwise distinct elements `S = {a, b, c}`, optionally starting
from a specified edge `K.Adj a b` in `S`. -/
private theorem finset_card_three_eq {α' : Type*} [DecidableEq α'] {S : Finset α'}
    (hS : S.card = 3) : ∃ a b c : α', a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ S = {a, b, c} := by
  obtain ⟨a, T, haT, rfl, hT⟩ := Finset.card_eq_succ.mp hS
  obtain ⟨b, U, hbU, rfl, hU⟩ := Finset.card_eq_succ.mp hT
  obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp hU
  refine ⟨a, b, c, ?_, ?_, ?_, rfl⟩
  · exact fun h => haT (by simp [h])
  · exact fun h => haT (by simp [h])
  · exact fun h => hbU (by simp [h])

private theorem finset_card_three_of_pair {α' : Type*} [DecidableEq α'] {S : Finset α'}
    (hS : S.card = 3) {a b : α'} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    ∃ c : α', a ≠ c ∧ b ≠ c ∧ S = {a, b, c} := by
  have hsub : ({a, b} : Finset α') ⊆ S := by
    rintro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    exact hx.elim (fun h => h ▸ ha) (fun h => h ▸ hb)
  have hcard1 : (S \ {a, b}).card = 1 := by
    have hc := Finset.card_sdiff_add_card_eq_card hsub
    rw [Finset.card_pair hab, hS] at hc
    omega
  obtain ⟨c, hc_eq⟩ := Finset.card_eq_one.mp hcard1
  have hc_mem : c ∈ S \ {a, b} := hc_eq ▸ Finset.mem_singleton_self c
  obtain ⟨hcS, hc_not⟩ := Finset.mem_sdiff.mp hc_mem
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc_not
  refine ⟨c, Ne.symm hc_not.1, Ne.symm hc_not.2, ?_⟩
  ext x
  constructor
  · intro hx
    by_cases hxab : x ∈ ({a, b} : Finset α')
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxab ⊢
      exact hxab.elim Or.inl (Or.inr ∘ Or.inl)
    · have hxc : x = c := Finset.mem_singleton.mp (hc_eq ▸ Finset.mem_sdiff.mpr ⟨hx, hxab⟩)
      simp [hxc]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl | rfl) <;> assumption

/-- **Main Connectivity Reduction**: if every internally `4`-connected `K_5`-minor-free simple graph
on `Fin N` (`6 ≤ N`) is either planar or isomorphic to `V_8`, then every `K_5`-minor-free simple
graph on `Fin N` (`5 ≤ N`) satisfies the structural dichotomy of
`hasTreeStructureOver_of_finSimple_step`. -/
theorem finSimple_dichotomy_of_internally4Conn
    (h4 : ∀ (N : ℕ) (K : SimpleGraph (Fin N)), IsInternally4ConnFin K → ¬ HasK5MinorSimple K →
      Nonempty (HP25.PlaneEmbedding K Set.univ) ∨
      Nonempty (Iso (Graph.ofSimpleGraph K) GM16.wagnerGraphV8))
    (N : ℕ) (hN : 5 ≤ N) (K : SimpleGraph (Fin N)) (hnoK5 : ¬ HasK5MinorSimple K) :
    Nonempty (HP25.PlaneEmbedding K Set.univ) ∨
    Nonempty (Iso (Graph.ofSimpleGraph K) GM16.wagnerGraphV8) ∨
    ∃ A₁ A₂ : Finset (Fin N),
      A₁ ∪ A₂ = Finset.univ ∧ A₁.card < N ∧ A₂.card < N ∧ (A₁ ∩ A₂).card ≤ 3 ∧
      (∀ x y, K.Adj x y → (x ∈ A₁ ∧ y ∈ A₁) ∨ (x ∈ A₂ ∧ y ∈ A₂)) ∧
      ¬ HasK5MinorSimple (torsoOn K A₁ (A₁ ∩ A₂)) ∧
      ¬ HasK5MinorSimple (torsoOn K A₂ (A₁ ∩ A₂)) := by
  classical
  -- Step 1: `N = 5` splits immediately across any missing edge `uv` into two `4`-vertex torsos!
  by_cases hN5 : N = 5
  · right; right
    have hmiss : ∃ u v : Fin N, u ≠ v ∧ ¬ K.Adj u v := by
      by_contra hall
      push Not at hall
      apply hnoK5
      let e : Fin 5 ≃ Fin N := (Fin.castOrderIso hN5.symm).toEquiv
      refine ⟨fun i => {e i}, fun i => ⟨e i, rfl⟩,
        fun i => preconnected_induce_singleton K (e i),
        fun i j hij => disjoint_singleton.mpr (e.injective.ne hij),
        fun i j hij => ⟨e i, rfl, e j, rfl, hall (e i) (e j) (e.injective.ne hij)⟩⟩
    obtain ⟨u, v, huv, hnot_uv⟩ := hmiss
    let A₁ : Finset (Fin N) := Finset.univ.erase v
    let A₂ : Finset (Fin N) := Finset.univ.erase u
    have hA₁_card : A₁.card = 4 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin, hN5]
    have hA₂_card : A₂.card = 4 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin, hN5]
    have hInter_card : (A₁ ∩ A₂).card = 3 := by
      have h_eq : A₁ ∩ A₂ = A₁.erase u := by
        ext x
        simp only [A₁, A₂, Finset.mem_inter, Finset.mem_erase, Finset.mem_univ, and_true]
        tauto
      rw [h_eq, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv, Finset.mem_univ u⟩),
        hA₁_card]
    refine ⟨A₁, A₂, ?_, by omega, by omega, by omega, ?_,
      not_hasK5MinorSimple_torsoOn_of_card_le_four (by omega),
      not_hasK5MinorSimple_torsoOn_of_card_le_four (by omega)⟩
    · ext x
      simp only [A₁, A₂, Finset.mem_union, Finset.mem_erase, Finset.mem_univ, and_true, iff_true]
      by_cases hxv : x = v
      · exact Or.inr (hxv ▸ huv.symm)
      · exact Or.inl hxv
    · intro x y hxy
      by_cases hxv : x = v
      · subst hxv
        have hyu : y ≠ u := fun h => hnot_uv (h ▸ hxy.symm)
        exact Or.inr ⟨Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ _⟩,
          Finset.mem_erase.mpr ⟨hyu, Finset.mem_univ _⟩⟩
      · by_cases hyv : y = v
        · subst hyv
          have hxu : x ≠ u := fun h => hnot_uv (h ▸ hxy)
          exact Or.inr ⟨Finset.mem_erase.mpr ⟨hxu, Finset.mem_univ _⟩,
            Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ _⟩⟩
        · exact Or.inl ⟨Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ _⟩,
            Finset.mem_erase.mpr ⟨hyv, Finset.mem_univ _⟩⟩
  have hN6 : 6 ≤ N := by omega
  have houtside_nonempty : ∀ {S : Finset (Fin N)}, S.card ≤ 3 → (Finset.univ \ S).Nonempty := by
    intro S hS
    apply Finset.card_pos.mp
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ, Fintype.card_fin] at hc
    omega
  -- Step 2: `(≤ 2)`-cut reductions (`k = 0, 1, 2`) to `Is3ConnectedFin K`.
  by_cases h0 : ¬ (K.induce {x : Fin N | x ∉ (∅ : Finset (Fin N))}).Connected
  · -- `0`-cut
    right; right
    obtain ⟨p, q, hq⟩ := exists_two_outside_of_not_connected (houtside_nonempty (by simp)) h0
    obtain ⟨hU, hlt₁, hlt₂, hInt, hle3, hsep⟩ := sep_of_compFinset (by simp) hq
    refine ⟨∅ ∪ compFinset K ∅ p, Finset.univ \ compFinset K ∅ p,
      hU, hlt₁, hlt₂, hle3, hsep, ?_, ?_⟩
    · rw [hInt]
      exact fun hm => hnoK5 (hasK5MinorSimple_of_torsoOn_card_le_one (Finset.empty_subset _)
        (by simp) hm)
    · rw [hInt]
      exact fun hm => hnoK5 (hasK5MinorSimple_of_torsoOn_card_le_one (Finset.empty_subset _)
        (by simp) hm)
  push Not at h0
  by_cases h1 : ∃ a : Fin N, ¬ (K.induce {x : Fin N | x ∉ ({a} : Finset (Fin N))}).Connected
  · -- `1`-cut
    right; right
    obtain ⟨a, ha_cut⟩ := h1
    have hSa : ({a} : Finset (Fin N)).card ≤ 3 := by simp
    obtain ⟨p, q, hq⟩ := exists_two_outside_of_not_connected (houtside_nonempty hSa) ha_cut
    obtain ⟨hU, hlt₁, hlt₂, hInt, hle3, hsep⟩ := sep_of_compFinset hSa hq
    refine ⟨{a} ∪ compFinset K {a} p, Finset.univ \ compFinset K {a} p,
      hU, hlt₁, hlt₂, hle3, hsep, ?_, ?_⟩
    · rw [hInt]
      exact fun hm => hnoK5 (hasK5MinorSimple_of_torsoOn_card_le_one Finset.subset_union_left
        (by simp) hm)
    · rw [hInt]
      have hsub2 : ({a} : Finset (Fin N)) ⊆ Finset.univ \ compFinset K {a} p :=
        Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ a,
          fun haD => notMem_of_mem_compFinset haD (Finset.mem_singleton_self a)⟩)
      exact fun hm => hnoK5 (hasK5MinorSimple_of_torsoOn_card_le_one hsub2 (by simp) hm)
  push Not at h1
  have hle1_conn : ∀ S : Finset (Fin N), S.card ≤ 1 →
      (K.induce {x : Fin N | x ∉ S}).Connected := by
    intro S hS
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hS with hc0 | hc1
    · rw [Finset.card_eq_zero.mp hc0]; exact h0
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc1; exact h1 a
  by_cases h2 : ∃ S : Finset (Fin N), S.card = 2 ∧ ¬ (K.induce {x : Fin N | x ∉ S}).Connected
  · -- Minimal `2`-cut (`K - {a}` and `K - {b}` are connected!)
    right; right
    obtain ⟨S, hS2, hS_cut⟩ := h2
    obtain ⟨a, b, hab, hS_eq⟩ := Finset.card_eq_two.mp hS2
    have hS_le3 : S.card ≤ 3 := by omega
    obtain ⟨p, q, hq⟩ := exists_two_outside_of_not_connected (houtside_nonempty hS_le3) hS_cut
    let D₁ := compFinset K S p
    let D₂ := compFinset K S q
    have hD₁₂ : Disjoint D₁ D₂ := compFinset_disjoint_of_notMem hq
    have hp_notD₂ : p.1 ∉ D₂ := Finset.disjoint_left.mp hD₁₂ (mem_compFinset_self p)
    obtain ⟨hU, hlt₁, hlt₂, hInt, hle3, hsep⟩ := sep_of_compFinset hS_le3 hq
    let A₁ := S ∪ D₁
    let A₂ := Finset.univ \ D₁
    have herase_le1 : ∀ s ∈ S, (S.erase s).card ≤ 1 := by
      intro s hs; rw [Finset.card_erase_of_mem hs, hS2]
    have haS : a ∈ S := by simp [hS_eq]
    have hbS : b ∈ S := by simp [hS_eq]
    have haD₁ : ∃ x ∈ D₁, K.Adj a x := exists_adj_in_closed_set haS
      (fun _ hx _ hy hxy => compFinset_closed hx hy hxy)
      (mem_compFinset_self p) p.2 hq q.2 (hle1_conn _ (herase_le1 a haS))
    have hbD₁ : ∃ x ∈ D₁, K.Adj b x := exists_adj_in_closed_set hbS
      (fun _ hx _ hy hxy => compFinset_closed hx hy hxy)
      (mem_compFinset_self p) p.2 hq q.2 (hle1_conn _ (herase_le1 b hbS))
    have haD₂ : ∃ x ∈ D₂, K.Adj a x := exists_adj_in_closed_set haS
      (fun _ hx _ hy hxy => compFinset_closed hx hy hxy)
      (mem_compFinset_self q) q.2 hp_notD₂ p.2 (hle1_conn _ (herase_le1 a haS))
    have hbD₂ : ∃ x ∈ D₂, K.Adj b x := exists_adj_in_closed_set hbS
      (fun _ hx _ hy hxy => compFinset_closed hx hy hxy)
      (mem_compFinset_self q) q.2 hp_notD₂ p.2 (hle1_conn _ (herase_le1 b hbS))
    have hD₂A₁ : Disjoint D₂ A₁ := by
      rw [Finset.disjoint_left]
      intro z hz₂ hzA₁
      rcases Finset.mem_union.mp hzA₁ with hzS | hz₁
      · exact notMem_of_mem_compFinset hz₂ hzS
      · exact Finset.disjoint_left.mp hD₁₂.symm hz₂ hz₁
    have hD₁A₂ : Disjoint D₁ A₂ := Finset.disjoint_sdiff
    refine ⟨A₁, A₂, hU, hlt₁, hlt₂, hle3, hsep, ?_, ?_⟩
    · rw [hInt]
      exact fun hm => hnoK5 (hasK5MinorSimple_of_two_cut_comp hab hS_eq Finset.subset_union_left
        hD₂A₁ (preconnected_compFinset q) haD₂ hbD₂ hm)
    · rw [hInt]
      have hSA₂ : S ⊆ A₂ := by rw [← hInt]; exact Finset.inter_subset_right
      exact fun hm => hnoK5 (hasK5MinorSimple_of_two_cut_comp hab hS_eq hSA₂
        hD₁A₂ (preconnected_compFinset p) haD₁ hbD₁ hm)
  push Not at h2
  have h3 : Is3ConnectedFin K := by
    refine ⟨by omega, fun S hS => ?_⟩
    by_cases hle1 : S.card ≤ 1
    · exact hle1_conn S hle1
    · exact h2 S (by omega)
  -- Step 3: `3`-cut reductions from `Is3ConnectedFin K` to `IsInternally4ConnFin K`!
  by_cases h4conn : IsInternally4ConnFin K
  · exact (h4 N K h4conn hnoK5).imp_right Or.inl
  · right; right
    have hbad3 : ∃ S : Finset (Fin N), S.card = 3 ∧
        ¬ (K.induce {x : Fin N | x ∉ S}).Connected ∧
        ¬ ((∀ x ∈ S, ∀ y ∈ S, ¬ K.Adj x y) ∧
          ∃ u : Fin N, u ∉ S ∧ (∀ y : Fin N, K.Adj u y ↔ y ∈ S) ∧
            (K.induce {x : Fin N | x ∉ S ∧ x ≠ u}).Connected) := by
      by_contra hno_bad
      apply h4conn ⟨hN6, h3, fun S hS hcut =>
        by_contra fun hneg => hno_bad ⟨S, hS, hcut, hneg⟩⟩
    obtain ⟨S, hS3, hS_cut, hS_neg⟩ := hbad3
    have hS_le3 : S.card ≤ 3 := by omega
    have herase_le2 : ∀ s ∈ S, (S.erase s).card ≤ 2 := by
      intro s hs; rw [Finset.card_erase_of_mem hs, hS3]
    -- Helper: any component `compFinset K S p` (when `q ∉ compFinset K S p`) attaches to every `s ∈ S`.
    have hcomp_att : ∀ {p q : {x : Fin N // x ∉ S}}, q.1 ∉ compFinset K S p →
        ∀ s ∈ S, ∃ x ∈ compFinset K S p, K.Adj s x := fun {p q} hq s hs =>
      exists_adj_in_closed_set hs (fun _ hx _ hy hxy => compFinset_closed hx hy hxy)
        (mem_compFinset_self p) p.2 hq q.2 (h3.2 _ (herase_le2 s hs))
    by_cases hS_edge : ∃ a ∈ S, ∃ b ∈ S, K.Adj a b
    · -- Branch 3.1: `S` contains an edge `K.Adj a b`.
      obtain ⟨a, haS, b, hbS, hK_ab⟩ := hS_edge
      have hab : a ≠ b := hK_ab.ne
      obtain ⟨c, hac, hbc, hS_eq⟩ := finset_card_three_of_pair hS3 haS hbS hab
      have hcS : c ∈ S := by simp [hS_eq]
      obtain ⟨p, q, hq⟩ := exists_two_outside_of_not_connected (houtside_nonempty hS_le3) hS_cut
      let D₁ := compFinset K S p
      let D₂ := compFinset K S q
      have hD₁₂ : Disjoint D₁ D₂ := compFinset_disjoint_of_notMem hq
      have hp_notD₂ : p.1 ∉ D₂ := Finset.disjoint_left.mp hD₁₂ (mem_compFinset_self p)
      obtain ⟨hU, hlt₁, hlt₂, hInt, hle3, hsep⟩ := sep_of_compFinset hS_le3 hq
      let A₁ := S ∪ D₁
      let A₂ := Finset.univ \ D₁
      have hD₂A₁ : Disjoint D₂ A₁ := by
        rw [Finset.disjoint_left]
        intro z hz₂ hzA₁
        rcases Finset.mem_union.mp hzA₁ with hzS | hz₁
        · exact notMem_of_mem_compFinset hz₂ hzS
        · exact Finset.disjoint_left.mp hD₁₂.symm hz₂ hz₁
      refine ⟨A₁, A₂, hU, hlt₁, hlt₂, hle3, hsep, ?_, ?_⟩
      · rw [hInt]
        exact fun hm => hnoK5 (hasK5MinorSimple_of_three_cut_edge hab hac hbc hS_eq
          Finset.subset_union_left hK_ab hD₂A₁ (preconnected_compFinset q)
          (hcomp_att hp_notD₂ a haS) (hcomp_att hp_notD₂ b hbS) (hcomp_att hp_notD₂ c hcS) hm)
      · rw [hInt]
        have hSA₂ : S ⊆ A₂ := by rw [← hInt]; exact Finset.inter_subset_right
        exact fun hm => hnoK5 (hasK5MinorSimple_of_three_cut_edge hab hac hbc hS_eq
          hSA₂ hK_ab Finset.disjoint_sdiff (preconnected_compFinset p)
          (hcomp_att hq a haS) (hcomp_att hq b hbS) (hcomp_att hq c hcS) hm)
    · -- Branch 3.2: `S` is an independent set in `K`.
      have hS_indep : ∀ x ∈ S, ∀ y ∈ S, ¬ K.Adj x y := fun x hx y hy hxy =>
        hS_edge ⟨x, hx, y, hy, hxy⟩
      have hnot_deg3 : ¬ ∃ u : Fin N, u ∉ S ∧ (∀ y : Fin N, K.Adj u y ↔ y ∈ S) ∧
          (K.induce {x : Fin N | x ∉ S ∧ x ≠ u}).Connected :=
        fun hex => hS_neg ⟨hS_indep, hex⟩
      obtain ⟨a, b, c, hab, hac, hbc, hS_eq⟩ := finset_card_three_eq hS3
      have haS : a ∈ S := by simp [hS_eq]
      have hbS : b ∈ S := by simp [hS_eq]
      have hcS : c ∈ S := by simp [hS_eq]
      by_cases hout_edge : ∃ u₀ ∉ S, ∃ v₀ ∉ S, K.Adj u₀ v₀
      · -- Subbranch 3.2b: `K - S` has at least one edge `u₀v₀`, so `D₁ := compFinset K S u₀` has `2 ≤ D₁.card`!
        obtain ⟨u₀, hu₀S, v₀, hv₀S, huv₀⟩ := hout_edge
        let p : {x : Fin N // x ∉ S} := ⟨u₀, hu₀S⟩
        let D₁ := compFinset K S p
        have hu₀D₁ : u₀ ∈ D₁ := mem_compFinset_self p
        have hv₀D₁ : v₀ ∈ D₁ := compFinset_closed hu₀D₁ hv₀S huv₀
        have hD₁_ge2 : 2 ≤ D₁.card :=
          Finset.one_lt_card.mpr ⟨u₀, hu₀D₁, v₀, hv₀D₁, huv₀.ne⟩
        -- Since `K - S` is not connected, there exists `q ∉ S` with `q.1 ∉ D₁`!
        have hex_q : ∃ q : {x : Fin N // x ∉ S}, q.1 ∉ D₁ := by
          by_contra hall
          push Not at hall
          apply hS_cut
          have : Nonempty {x : Fin N | x ∉ S} := ⟨⟨u₀, hu₀S⟩⟩
          refine ⟨fun x y => ?_⟩
          have hx := (Finset.mem_filter.mp (hall ⟨x.1, x.2⟩)).2.2
          have hy := (Finset.mem_filter.mp (hall ⟨y.1, y.2⟩)).2.2
          exact hx.symm.trans hy
        obtain ⟨q, hq⟩ := hex_q
        let D₂ := compFinset K S q
        have hD₁₂ : Disjoint D₁ D₂ := compFinset_disjoint_of_notMem hq
        have hp_notD₂ : p.1 ∉ D₂ := Finset.disjoint_left.mp hD₁₂ hu₀D₁
        obtain ⟨hU, hlt₁, hlt₂, hInt, hle3, hsep⟩ := sep_of_compFinset hS_le3 hq
        let A₁ := S ∪ D₁
        let A₂ := Finset.univ \ D₁
        have hSA₂ : S ⊆ A₂ := by rw [← hInt]; exact Finset.inter_subset_right
        have hD₂A₁ : Disjoint D₂ A₁ := by
          rw [Finset.disjoint_left]
          intro z hz₂ hzA₁
          rcases Finset.mem_union.mp hzA₁ with hzS | hz₁
          · exact notMem_of_mem_compFinset hz₂ hzS
          · exact Finset.disjoint_left.mp hD₁₂.symm hz₂ hz₁
        -- Either `A₂` has `¬ HasK5MinorSimple (torsoOn K A₂ S)` via `2 ≤ D₁.card` ALWAYS:
        have hnoT₂ : ¬ HasK5MinorSimple (torsoOn K A₂ S) := fun hm =>
          hnoK5 (hasK5MinorSimple_of_three_cut_comp_ge_two h3 hab hac hbc hS_eq hSA₂
            Finset.disjoint_sdiff hD₁_ge2 (preconnected_compFinset p)
            (fun _ hx _ hy hxy => compFinset_closed hx hy hxy)
            (hcomp_att hq a haS) (hcomp_att hq b hbS) (hcomp_att hq c hcS) hm)
        -- Now examine `A₂ \ S`: either `2 ≤ D₂.card`, or there is a third component `D₃`, or `D₂ = {q.1}` is ALL of `A₂ \ S`!
        by_cases hD₂_ge2 : 2 ≤ D₂.card
        · -- Both `D₁` and `D₂` have size `≥ 2`!
          refine ⟨A₁, A₂, hU, hlt₁, hlt₂, hle3, hsep, ?_, hInt ▸ hnoT₂⟩
          rw [hInt]
          exact fun hm => hnoK5 (hasK5MinorSimple_of_three_cut_comp_ge_two h3 hab hac hbc hS_eq
            Finset.subset_union_left hD₂A₁ hD₂_ge2 (preconnected_compFinset q)
            (fun _ hx _ hy hxy => compFinset_closed hx hy hxy)
            (hcomp_att hp_notD₂ a haS) (hcomp_att hp_notD₂ b hbS) (hcomp_att hp_notD₂ c hcS) hm)
        · by_cases hex_r : ∃ r : {x : Fin N // x ∉ S}, r.1 ∉ D₁ ∧ r.1 ∉ D₂
          · -- Third component `D₃ ⊆ A₂ \ S` disjoint from `D₂`!
            obtain ⟨r, hr₁, hr₂⟩ := hex_r
            let D₃ := compFinset K S r
            have hD₁₃ : Disjoint D₁ D₃ := compFinset_disjoint_of_notMem hr₁
            have hD₂₃ : Disjoint D₂ D₃ := compFinset_disjoint_of_notMem hr₂
            have hp_notD₃ : p.1 ∉ D₃ := Finset.disjoint_left.mp hD₁₃ hu₀D₁
            have hD₃A₁ : Disjoint D₃ A₁ := by
              rw [Finset.disjoint_left]
              intro z hz₃ hzA₁
              rcases Finset.mem_union.mp hzA₁ with hzS | hz₁
              · exact notMem_of_mem_compFinset hz₃ hzS
              · exact Finset.disjoint_left.mp hD₁₃.symm hz₃ hz₁
            refine ⟨A₁, A₂, hU, hlt₁, hlt₂, hle3, hsep, ?_, hInt ▸ hnoT₂⟩
            rw [hInt]
            exact fun hm => hnoK5 (hasK5MinorSimple_of_three_cut_two_comps hab hac hbc hS_eq
              Finset.subset_union_left hD₂A₁ hD₃A₁ hD₂₃
              (preconnected_compFinset q) (preconnected_compFinset r)
              (hcomp_att hp_notD₂ a haS) (hcomp_att hp_notD₂ b hbS)
              (hcomp_att hp_notD₃ a haS) (hcomp_att hp_notD₃ b hbS) (hcomp_att hp_notD₃ c hcS) hm)
          · -- `D₂ = {q.1}` AND every vertex outside `S` is in `D₁ ∪ D₂`, contradicting `hnot_deg3`!
            exfalso
            push Not at hex_r
            have hD₂_eq : D₂ = {q.1} := by
              have hpos : 0 < D₂.card := Finset.card_pos.mpr ⟨q.1, mem_compFinset_self q⟩
              have hc1 : D₂.card = 1 := by omega
              obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hc1
              have hqz : q.1 = z := Finset.mem_singleton.mp (hz ▸ mem_compFinset_self q)
              exact hqz ▸ hz
            apply hnot_deg3
            refine ⟨q.1, q.2, ?_, ?_⟩
            · intro y
              constructor
              · intro hqy
                by_contra hyS
                have hyD₂ : y ∈ D₂ := compFinset_closed (mem_compFinset_self q) hyS hqy
                have hyq : y = q.1 := Finset.mem_singleton.mp (hD₂_eq ▸ hyD₂)
                exact hqy.ne hyq.symm
              · intro hyS
                obtain ⟨x, hxD₂, hsy⟩ := hcomp_att hp_notD₂ y hyS
                have hxq : x = q.1 := Finset.mem_singleton.mp (hD₂_eq ▸ hxD₂)
                exact hxq ▸ hsy.symm
            · -- `{x | x ∉ S ∧ x ≠ q.1}` equals `(D₁ : Set (Fin N))`, which is connected!
              have hset_eq : {x : Fin N | x ∉ S ∧ x ≠ q.1} = (D₁ : Set (Fin N)) := by
                ext x
                simp only [Set.mem_ofPred_eq, Finset.mem_coe]
                constructor
                · rintro ⟨hxS, hxq⟩
                  by_contra hxD₁
                  have hxD₂ : x ∈ D₂ := hex_r ⟨x, hxS⟩ hxD₁
                  exact hxq (Finset.mem_singleton.mp (hD₂_eq ▸ hxD₂))
                · intro hxD₁
                  exact ⟨notMem_of_mem_compFinset hxD₁,
                    fun hxq => hq (hxq ▸ hxD₁)⟩
              rw [hset_eq]
              have : Nonempty (D₁ : Set (Fin N)) := ⟨⟨u₀, hu₀D₁⟩⟩
              exact ⟨preconnected_compFinset p⟩
      · -- Subbranch 3.2a: `Finset.univ \ S` is an independent set of `K`!
        push Not at hout_edge
        obtain ⟨u₀, hu₀⟩ := houtside_nonempty hS_le3
        have hu₀S : u₀ ∉ S := (Finset.mem_sdiff.mp hu₀).2
        let A₁ : Finset (Fin N) := insert u₀ S
        let A₂ : Finset (Fin N) := Finset.univ.erase u₀
        have hA₁_card : A₁.card = 4 := by
          rw [Finset.card_insert_of_notMem hu₀S, hS3]
        have hA₂_card : A₂.card = N - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ u₀), Finset.card_univ, Fintype.card_fin]
        have hInter : A₁ ∩ A₂ = S := by
          ext x
          simp only [A₁, A₂, Finset.mem_inter, Finset.mem_insert, Finset.mem_erase,
            Finset.mem_univ, and_true]
          constructor
          · rintro ⟨rfl | hxS, hne⟩
            · exact (hne rfl).elim
            · exact hxS
          · intro hxS
            exact ⟨Or.inr hxS, fun h => hu₀S (h ▸ hxS)⟩
        refine ⟨A₁, A₂, ?_, by omega, by omega, hInter ▸ hS_le3, ?_, ?_, ?_⟩
        · ext x
          simp only [A₁, A₂, Finset.mem_union, Finset.mem_insert, Finset.mem_erase,
            Finset.mem_univ, and_true, iff_true]
          exact (em (x = u₀)).imp_left Or.inl
        · intro x y hxy
          by_cases hxu₀ : x = u₀
          · subst hxu₀
            have hyS : y ∈ S := by_contra fun hyS => hout_edge x hu₀S y hyS hxy
            exact Or.inl ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hyS⟩
          · by_cases hyu₀ : y = u₀
            · subst hyu₀
              have hxS : x ∈ S := by_contra fun hxS => hout_edge x hxS y hu₀S hxy
              exact Or.inl ⟨Finset.mem_insert_of_mem hxS, Finset.mem_insert_self _ _⟩
            · exact Or.inr ⟨Finset.mem_erase.mpr ⟨hxu₀, Finset.mem_univ _⟩,
                Finset.mem_erase.mpr ⟨hyu₀, Finset.mem_univ _⟩⟩
        · exact not_hasK5MinorSimple_torsoOn_of_card_le_four (by omega)
        · rw [hInter]
          refine not_hasK5MinorSimple_torsoOn_of_indep_sdiff hS_le3 ?_
          intro x hx y hy
          exact hout_edge x (Finset.mem_sdiff.mp hx).2 y (Finset.mem_sdiff.mp hy).2

end GraphMinor.Wagner

