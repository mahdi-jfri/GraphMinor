module

public import GraphMinor.Wagner.ConnectivityReduction
public import GraphMinor.Crossing.PlanarSubdiv

/-!
# Thomassen's Contractible Edge Lemma and Minor Lifting Across Contractions

This file proves Thomassen's contractible edge lemma for finite `3`-connected simple graphs
(Reinhard Diestel, *Graph Theory*, 6th ed., Springer, Lemma 3.2.4, page 68 of the author's
preview of Chapter 3), following Diestel's proof:
every `3`-connected simple graph `K` on `M + 1 ≥ 5` vertices has an edge `x₀y₀` whose contraction
`K'` on `M` vertices remains `3`-connected.

It also defines `HasK33Subdiv` and `HasK33MinorSimple`, proves `HasK33Subdiv K → HasK33MinorSimple K`,
and shows that contracting an edge lifts both `K_5` minor models and `K_{3,3}` minor models back to
`K`.
-/

public section

namespace GraphMinor.Wagner

open Set Function SimpleGraph

/-- `K : SimpleGraph γ` contains a topological subdivision of `K_{3,3}`: six distinct branch
vertices `a 0, a 1, a 2, b 0, b 1, b 2` joined by nine internally disjoint path lists `L i j` from
`a i` to `b j`. -/
@[expose] def HasK33Subdiv {γ : Type*} (K : SimpleGraph γ) : Prop :=
  ∃ (a b : Fin 3 → γ) (L : Fin 3 → Fin 3 → List γ),
    Injective a ∧ Injective b ∧ (∀ i j, a i ≠ b j) ∧
    (∀ i j, HP25.IsPathList K Set.univ (L i j)) ∧
    (∀ i j, ∃ mid, L i j = a i :: mid ++ [b j]) ∧
    (∀ i j i' j', (i, j) ≠ (i', j') →
      ∀ x ∈ L i j, x ∈ L i' j' → (i = i' ∧ x = a i) ∨ (j = j' ∧ x = b j))

/-- `K : SimpleGraph γ` contains `K_{3,3}` as a minor: six pairwise disjoint nonempty connected
vertex subsets `A 0, A 1, A 2` and `B 0, B 1, B 2` with an edge of `K` between `A i` and `B j` for
all `i, j : Fin 3`. -/
@[expose] def HasK33MinorSimple {γ : Type*} (K : SimpleGraph γ) : Prop :=
  ∃ A B : Fin 3 → Set γ,
    (∀ i, (A i).Nonempty) ∧ (∀ j, (B j).Nonempty) ∧
    (∀ i, (K.induce (A i)).Preconnected) ∧ (∀ j, (K.induce (B j)).Preconnected) ∧
    (∀ ⦃i₁ i₂⦄, i₁ ≠ i₂ → Disjoint (A i₁) (A i₂)) ∧
    (∀ ⦃j₁ j₂⦄, j₁ ≠ j₂ → Disjoint (B j₁) (B j₂)) ∧
    (∀ i j, Disjoint (A i) (B j)) ∧
    (∀ i j, ∃ u ∈ A i, ∃ v ∈ B j, K.Adj u v)

/-- No planar simple graph contains a subdivision of `K_{3,3}`. -/
theorem not_planar_of_hasK33Subdiv {γ : Type*} {K : SimpleGraph γ} (h : HasK33Subdiv K) :
    ¬ Nonempty (HP25.PlaneEmbedding K Set.univ) := by
  obtain ⟨a, b, L, hainj, hbinj, hab, hpath, hends, hdisj⟩ := h
  exact Crossing.not_planar_of_K33_subdivision hainj hbinj hab hpath hends hdisj

/-! ### Part 1: `HasK33Subdiv K → HasK33MinorSimple K` -/

private theorem walk_of_isChain_cons {γ : Type*} {K : SimpleGraph γ} :
    ∀ (u : γ) (l : List γ), (u :: l).IsChain K.Adj →
      ∃ v : γ, ∃ w : K.Walk u v, w.support = u :: l ∧ (u :: l).getLast (List.cons_ne_nil _ _) = v
  | u, [], _ => ⟨u, .nil, rfl, rfl⟩
  | u, x :: tl, hch => by
    have hux : K.Adj u x := List.isChain_cons_cons.mp hch |>.1
    have htl : (x :: tl).IsChain K.Adj := List.isChain_cons_cons.mp hch |>.2
    obtain ⟨v, w, hsup, hlast⟩ := walk_of_isChain_cons x tl htl
    refine ⟨v, .cons hux w, ?_, ?_⟩
    · rw [Walk.support_cons, hsup]
    · simpa using hlast

/-- Every `K_{3,3}` subdivision in `K` yields a `K_{3,3}` minor model in `K` (putting the internal
vertices of each `L i j` into `A i` and setting `B j = {b j}`). -/
theorem hasK33MinorSimple_of_hasK33Subdiv {γ : Type*} {K : SimpleGraph γ}
    (h : HasK33Subdiv K) : HasK33MinorSimple K := by
  obtain ⟨a, b, L, hainj, hbinj, hab, hpath, hends, hdisj⟩ := h
  choose mid hmid using hends
  let stem : Fin 3 → Fin 3 → List γ := fun i j => a i :: mid i j
  have hstem_chain : ∀ i j, (stem i j).IsChain K.Adj := by
    intro i j
    have hch := (hpath i j).2.1
    rw [hmid i j] at hch
    exact hch.left_of_append
  have hstem_sub : ∀ i j x, x ∈ stem i j → x ∈ L i j ∧ x ≠ b j := by
    intro i j x hx
    have hnd := (hpath i j).1
    rw [hmid i j] at hnd
    refine ⟨by rw [hmid i j]; exact List.mem_append_left _ hx, ?_⟩
    rintro rfl
    exact (List.nodup_append.mp hnd).2.2 _ hx _ (by simp) rfl
  have hstem_last_adj : ∀ i j, ∃ u ∈ stem i j, K.Adj u (b j) := by
    intro i j
    have hch := (hpath i j).2.1
    rw [hmid i j] at hch
    -- Last element of `stem i j = a i :: mid i j` is adjacent to `b j` in `(stem i j) ++ [b j]`.
    let u := (stem i j).getLast (List.cons_ne_nil _ _)
    have hu_mem : u ∈ stem i j := List.getLast_mem (List.cons_ne_nil _ _)
    have hsplit : stem i j = (stem i j).dropLast ++ [u] :=
      (List.dropLast_append_getLast (List.cons_ne_nil _ _)).symm
    have hch' : ((stem i j).dropLast ++ [u, b j]).IsChain K.Adj := by
      have heq : (stem i j) ++ [b j] = (stem i j).dropLast ++ [u, b j] := by
        conv_lhs => rw [hsplit]
        simp
      exact heq ▸ hch
    have hub : K.Adj u (b j) := List.isChain_cons_cons.mp hch'.right_of_append |>.1
    exact ⟨u, hu_mem, hub⟩
  let A : Fin 3 → Set γ := fun i => ⋃ j : Fin 3, {x : γ | x ∈ stem i j}
  let B : Fin 3 → Set γ := fun j => {b j}
  refine ⟨A, B, ?_, fun j => ⟨b j, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨a i, mem_iUnion.mpr ⟨0, List.mem_cons_self⟩⟩
  · intro i
    have haiA : a i ∈ A i := mem_iUnion.mpr ⟨0, List.mem_cons_self⟩
    have hto_ai : ∀ z : ↥(A i), (K.induce (A i)).Reachable ⟨a i, haiA⟩ z := by
      rintro ⟨z, hzA⟩
      obtain ⟨j, hzj⟩ := mem_iUnion.mp hzA
      obtain ⟨v, w, hsup, _⟩ := walk_of_isChain_cons (a i) (mid i j) (hstem_chain i j)
      have hwA : ∀ q ∈ w.support, q ∈ A i := fun q hq =>
        mem_iUnion.mpr ⟨j, by rw [hsup] at hq; exact hq⟩
      have hzw : z ∈ w.support := by rw [hsup]; exact hzj
      -- Reachability along walk `w` inside `A i`
      have hreach : ∀ {p q : γ} (r : K.Walk p q) (hrA : ∀ t ∈ r.support, t ∈ A i)
          {t : γ} (ht : t ∈ r.support),
          (K.induce (A i)).Reachable ⟨p, hrA p r.start_mem_support⟩ ⟨t, hrA t ht⟩ := by
        intro p q r
        induction r with
        | nil =>
          intro _ t ht
          rw [Walk.support_nil, List.mem_singleton] at ht
          subst ht; exact Reachable.rfl
        | @cons p₁ p₂ p₃ hp12 r' ih =>
          intro hrA t ht
          rw [Walk.support_cons, List.mem_cons] at ht
          rcases ht with rfl | ht
          · exact Reachable.rfl
          · have hstep : (K.induce (A i)).Reachable
                ⟨p₁, hrA p₁ (by simp)⟩ ⟨p₂, hrA p₂ (by simp)⟩ :=
              Adj.reachable (G := K.induce (A i))
                (u := ⟨p₁, hrA p₁ (by simp)⟩) (v := ⟨p₂, hrA p₂ (by simp)⟩) hp12
            exact hstep.trans (ih (fun x hx => hrA x (by simp [hx])) ht)
      exact hreach w hwA hzw
    exact fun z₁ z₂ => (hto_ai z₁).symm.trans (hto_ai z₂)
  · intro j
    rintro ⟨u, hu⟩ ⟨v, hv⟩
    rw [mem_singleton_iff] at hu hv
    subst hu; subst hv
    exact Reachable.rfl
  · intro i₁ i₂ hii
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    obtain ⟨j₁, hxj₁⟩ := mem_iUnion.mp hx₁
    obtain ⟨j₂, hxj₂⟩ := mem_iUnion.mp hx₂
    have h1 := hstem_sub i₁ j₁ x hxj₁
    have h2 := hstem_sub i₂ j₂ x hxj₂
    have hne_pair : (i₁, j₁) ≠ (i₂, j₂) := fun h => hii (Prod.mk.inj h).1
    rcases hdisj i₁ j₁ i₂ j₂ hne_pair x h1.1 h2.1 with ⟨hi_eq, _⟩ | ⟨hj_eq, hxb⟩
    · exact hii hi_eq
    · exact h1.2 hxb
  · intro j₁ j₂ hjj
    exact disjoint_singleton.mpr (hbinj.ne hjj)
  · intro i j
    rw [Set.disjoint_right]
    rintro x (rfl : x = b j) hxA
    obtain ⟨j', hxj'⟩ := mem_iUnion.mp hxA
    have h1 := hstem_sub i j' (b j) hxj'
    by_cases hjj' : j' = j
    · exact h1.2 (by rw [hjj'])
    · have hbel : b j ∈ L i j := by rw [hmid i j]; simp
      rcases hdisj i j' i j (fun h => hjj' (Prod.mk.inj h).2) (b j) h1.1 hbel with
        ⟨_, hba⟩ | ⟨hj_eq, _⟩
      · exact hab i j hba.symm
      · exact hjj' hj_eq
  · intro i j
    obtain ⟨u, hu, hub⟩ := hstem_last_adj i j
    exact ⟨u, mem_iUnion.mpr ⟨j, hu⟩, b j, rfl, hub⟩

/-! ### Part 2: Minimum Degree `≥ 3` of `Is3ConnectedFin` Graphs -/

/-- Every vertex of a `3`-connected graph on `Fin N` has at least `3` distinct neighbors. -/
theorem exists_three_neighbors_of_is3ConnectedFin {N : ℕ} {K : SimpleGraph (Fin N)}
    (h3 : Is3ConnectedFin K) (u : Fin N) :
    ∃ v₁ v₂ v₃ : Fin N, v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ ∧
      K.Adj u v₁ ∧ K.Adj u v₂ ∧ K.Adj u v₃ := by
  classical
  have hN4 : 4 ≤ N := h3.1
  have hex_outside : ∀ S : Finset (Fin N), S.card ≤ 2 → u ∉ S →
      ∃ v : Fin N, v ∉ S ∧ K.Adj u v := by
    intro S hS huS
    have hrem : 2 ≤ (Finset.univ \ insert u S).card + 1 := by
      have hsub : insert u S ⊆ Finset.univ := Finset.subset_univ _
      have hc := Finset.card_sdiff_add_card_eq_card hsub
      rw [Finset.card_univ, Fintype.card_fin, Finset.card_insert_of_notMem huS] at hc
      omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ \ insert u S).card)
    have hw_not : w ∉ insert u S := (Finset.mem_sdiff.mp hw).2
    have hwu : w ≠ u := fun h => hw_not (Finset.mem_insert_self u S |> fun hm => h ▸ hm)
    have hwS : w ∉ S := fun h => hw_not (Finset.mem_insert_of_mem h)
    obtain ⟨p⟩ := (h3.2 S hS).preconnected ⟨u, huS⟩ ⟨w, hwS⟩
    cases p with
    | nil => exact (hwu rfl).elim
    | @cons _ v _ huv _ => exact ⟨v.1, v.2, huv⟩
  obtain ⟨v₁, _, huv₁⟩ := hex_outside ∅ (by simp) (by simp)
  obtain ⟨v₂, hv₂, huv₂⟩ := hex_outside {v₁} (by simp) (Finset.notMem_singleton.mpr huv₁.ne)
  have hv₁₂ : v₁ ≠ v₂ := Ne.symm (Finset.notMem_singleton.mp hv₂)
  have hu_not12 : u ∉ ({v₁, v₂} : Finset (Fin N)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨huv₁.ne, huv₂.ne⟩
  obtain ⟨v₃, hv₃, huv₃⟩ := hex_outside {v₁, v₂} Finset.card_le_two hu_not12
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv₃
  exact ⟨v₁, v₂, v₃, hv₁₂, Ne.symm hv₃.1, Ne.symm hv₃.2, huv₁, huv₂, huv₃⟩

/-- For any edge `K.Adj x y` of a `3`-connected graph `K`, `x` has at least `2` distinct neighbors
outside `{x, y}`. -/
theorem exists_two_neighbors_outside_edge {N : ℕ} {K : SimpleGraph (Fin N)}
    (h3 : Is3ConnectedFin K) {x y : Fin N} (hxy : K.Adj x y) :
    ∃ u₁ u₂ : Fin N, u₁ ≠ u₂ ∧ u₁ ≠ x ∧ u₁ ≠ y ∧ u₂ ≠ x ∧ u₂ ≠ y ∧
      K.Adj x u₁ ∧ K.Adj x u₂ := by
  obtain ⟨v₁, v₂, v₃, h12, h13, h23, hx1, hx2, hx3⟩ :=
    exists_three_neighbors_of_is3ConnectedFin h3 x
  by_cases hv1y : v₁ = y
  · exact ⟨v₂, v₃, h23, hx2.ne.symm, hv1y ▸ h12.symm, hx3.ne.symm, hv1y ▸ h13.symm, hx2, hx3⟩
  · by_cases hv2y : v₂ = y
    · exact ⟨v₁, v₃, h13, hx1.ne.symm, hv1y, hx3.ne.symm, hv2y ▸ h23.symm, hx1, hx3⟩
    · exact ⟨v₁, v₂, h12, hx1.ne.symm, hv1y, hx2.ne.symm, hv2y, hx1, hx2⟩

/-! ### Part 3: Edge Contraction Construction and Minor Lifting -/

/-- Preimage of a preconnected induced set across an edge-contraction surjection `π` whose only
nontrivial fiber `{x₀, y₀}` is joined by `K.Adj x₀ y₀` is induced-preconnected in `K`. -/
private theorem preconnected_preimage_of_contract {M : ℕ} {K : SimpleGraph (Fin (M + 1))}
    {K' : SimpleGraph (Fin M)} {x₀ y₀ : Fin (M + 1)} {z : Fin M}
    (hxy : K.Adj x₀ y₀) (π : Fin (M + 1) → Fin M)
    (hπx : π x₀ = z) (hπy : π y₀ = z)
    (hπ_inj : ∀ u v : Fin (M + 1), π u = π v → u = v ∨ ({u, v} : Set _) = {x₀, y₀})
    (hK'_lift : ∀ a b : Fin M, K'.Adj a b → ∃ u v : Fin (M + 1), π u = a ∧ π v = b ∧ K.Adj u v)
    {X : Set (Fin M)} (hX : (K'.induce X).Preconnected) :
    (K.induce (π ⁻¹' X)).Preconnected := by
  have hsame_fiber : ∀ {u v : Fin (M + 1)} (hu : u ∈ π ⁻¹' X) (hv : v ∈ π ⁻¹' X),
      π u = π v → (K.induce (π ⁻¹' X)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
    intro u v hu hv heq
    rcases hπ_inj u v heq with rfl | hpair
    · exact Reachable.rfl
    · have hu_mem : u ∈ ({x₀, y₀} : Set _) := hpair ▸ mem_insert u {v}
      have hv_mem : v ∈ ({x₀, y₀} : Set _) := hpair ▸ mem_insert_of_mem u rfl
      have hu_mem' : x₀ = u ∨ y₀ = u := by
        rcases hu_mem with h | h
        · exact Or.inl h.symm
        · exact Or.inr (mem_singleton_iff.mp h).symm
      have hv_mem' : x₀ = v ∨ y₀ = v := by
        rcases hv_mem with h | h
        · exact Or.inl h.symm
        · exact Or.inr (mem_singleton_iff.mp h).symm
      rcases hu_mem' with rfl | rfl <;> rcases hv_mem' with rfl | rfl
      · exact Reachable.rfl
      · exact Adj.reachable (G := K.induce (π ⁻¹' X)) (u := ⟨x₀, hu⟩) (v := ⟨y₀, hv⟩) hxy
      · exact Adj.reachable (G := K.induce (π ⁻¹' X)) (u := ⟨y₀, hu⟩) (v := ⟨x₀, hv⟩) hxy.symm
      · exact Reachable.rfl
  have hstep : ∀ {a b : ↥X}, (K'.induce X).Adj a b →
      ∀ (u v : Fin (M + 1)) (hu : u ∈ π ⁻¹' X) (hv : v ∈ π ⁻¹' X),
        π u = a.1 → π v = b.1 → (K.induce (π ⁻¹' X)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
    intro a b hab u v hu hv hπu hπv
    obtain ⟨u', v', hπu', hπv', huv'⟩ := hK'_lift a.1 b.1 hab
    have hu'X : u' ∈ π ⁻¹' X := by show π u' ∈ X; rw [hπu']; exact a.2
    have hv'X : v' ∈ π ⁻¹' X := by show π v' ∈ X; rw [hπv']; exact b.2
    have r1 := hsame_fiber hu hu'X (hπu.trans hπu'.symm)
    have r2 : (K.induce (π ⁻¹' X)).Reachable ⟨u', hu'X⟩ ⟨v', hv'X⟩ :=
      Adj.reachable (G := K.induce (π ⁻¹' X)) (u := ⟨u', hu'X⟩) (v := ⟨v', hv'X⟩) huv'
    have r3 := hsame_fiber hv'X hv (hπv'.trans hπv.symm)
    exact (r1.trans r2).trans r3
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  obtain ⟨w⟩ := hX ⟨π u, hu⟩ ⟨π v, hv⟩
  have hwalk : ∀ {a b : ↥X} (q : (K'.induce X).Walk a b)
      (u' v' : Fin (M + 1)) (hu' : u' ∈ π ⁻¹' X) (hv' : v' ∈ π ⁻¹' X),
      π u' = a.1 → π v' = b.1 → (K.induce (π ⁻¹' X)).Reachable ⟨u', hu'⟩ ⟨v', hv'⟩ := by
    intro a b q
    induction q with
    | nil =>
      intro u' v' hu' hv' h1 h2
      exact hsame_fiber hu' hv' (h1.trans h2.symm)
    | @cons a₁ a₂ a₃ ha12 q' ih =>
      intro u' v' hu' hv' h1 h2
      obtain ⟨_, m, _, hπm, _⟩ := hK'_lift a₁.1 a₂.1 ha12
      have hmX : m ∈ π ⁻¹' X := by show π m ∈ X; rw [hπm]; exact a₂.2
      exact (hstep ha12 u' m hu' hmX h1 hπm).trans (ih m v' hmX hv' hπm h2)
  exact hwalk w u v hu hv rfl rfl

/-- Builds the contracted graph `K' : SimpleGraph (Fin M)` for an edge `K.Adj x₀ y₀` of `K` and
proves minor-lifting and the characterization of `Is3ConnectedFin K'`. -/
private theorem contract_edge_spec {M : ℕ} (hM : 4 ≤ M) {K : SimpleGraph (Fin (M + 1))}
    (h3 : Is3ConnectedFin K) {x₀ y₀ : Fin (M + 1)} (hxy : K.Adj x₀ y₀)
    (hno3cut : ∀ u₀ : Fin (M + 1), u₀ ∉ ({x₀, y₀} : Finset (Fin (M + 1))) →
      (K.induce {v : Fin (M + 1) | v ∉ ({x₀, y₀, u₀} : Finset (Fin (M + 1)))}).Connected) :
    ∃ (z : Fin M) (emb : Fin M → Fin (M + 1)) (K' : SimpleGraph (Fin M)),
      emb z = x₀ ∧
      Injective emb ∧
      (∀ u : Fin (M + 1), u ≠ y₀ → ∃ w : Fin M, emb w = u) ∧
      (∀ w : Fin M, emb w ≠ y₀) ∧
      (∀ a b : Fin M, K'.Adj a b ↔ a ≠ b ∧
        ((a ≠ z ∧ b ≠ z ∧ K.Adj (emb a) (emb b)) ∨
         (a = z ∧ (K.Adj x₀ (emb b) ∨ K.Adj y₀ (emb b))) ∨
         (b = z ∧ (K.Adj x₀ (emb a) ∨ K.Adj y₀ (emb a))))) ∧
      Is3ConnectedFin K' ∧
      (HasK5MinorSimple K' → HasK5MinorSimple K) ∧
      (HasK33MinorSimple K' → HasK33MinorSimple K) := by
  classical
  have hcard_eq : Fintype.card (Fin M) = Fintype.card {u : Fin (M + 1) // u ≠ y₀} := by
    rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
    omega
  let e : Fin M ≃ {u : Fin (M + 1) // u ≠ y₀} := Fintype.equivOfCardEq hcard_eq
  let emb : Fin M → Fin (M + 1) := fun w => (e w).1
  have hemb_inj : Injective emb := Subtype.val_injective.comp e.injective
  have hemb_ne_y₀ : ∀ w : Fin M, emb w ≠ y₀ := fun w => (e w).2
  have hemb_surj : ∀ u : Fin (M + 1), u ≠ y₀ → ∃ w : Fin M, emb w = u := fun u hu =>
    ⟨e.symm ⟨u, hu⟩, congrArg Subtype.val (e.apply_symm_apply ⟨u, hu⟩)⟩
  let z : Fin M := e.symm ⟨x₀, hxy.ne⟩
  have hemb_z : emb z = x₀ := congrArg Subtype.val (e.apply_symm_apply ⟨x₀, hxy.ne⟩)
  let π : Fin (M + 1) → Fin M := fun u => if hu : u = y₀ then z else e.symm ⟨u, hu⟩
  have hπ_emb : ∀ w : Fin M, π (emb w) = w := fun w => by
    simp only [π, hemb_ne_y₀ w, ↓reduceDIte]
    exact e.symm_apply_apply w
  have hπ_x₀ : π x₀ = z := by rw [← hemb_z, hπ_emb]
  have hπ_y₀ : π y₀ = z := by simp [π]
  have hπ_surj : Surjective π := fun w => ⟨emb w, hπ_emb w⟩
  have hπ_inj : ∀ u v : Fin (M + 1), π u = π v → u = v ∨ ({u, v} : Set _) = {x₀, y₀} := by
    intro u v huv
    by_cases huy : u = y₀ <;> by_cases hvy : v = y₀
    · exact Or.inl (huy.trans hvy.symm)
    · rw [huy] at huv ⊢
      rw [hπ_y₀] at huv
      have hvx : v = x₀ := by
        have h1 : emb (π v) = v := by
          simp only [π, hvy, ↓reduceDIte]
          exact congrArg Subtype.val (e.apply_symm_apply ⟨v, hvy⟩)
        rw [← huv, hemb_z] at h1
        exact h1.symm
      rw [hvx]
      exact Or.inr (pair_comm y₀ x₀)
    · rw [hvy] at huv ⊢
      rw [hπ_y₀] at huv
      have hux : u = x₀ := by
        have h1 : emb (π u) = u := by
          simp only [π, huy, ↓reduceDIte]
          exact congrArg Subtype.val (e.apply_symm_apply ⟨u, huy⟩)
        rw [huv, hemb_z] at h1
        exact h1.symm
      rw [hux]
      exact Or.inr rfl
    · left
      have h1 : emb (π u) = u := by
        simp only [π, huy, ↓reduceDIte]
        exact congrArg Subtype.val (e.apply_symm_apply ⟨u, huy⟩)
      have h2 : emb (π v) = v := by
        simp only [π, hvy, ↓reduceDIte]
        exact congrArg Subtype.val (e.apply_symm_apply ⟨v, hvy⟩)
      rw [← h1, ← h2, huv]
  let K' : SimpleGraph (Fin M) :=
    { Adj := fun a b => a ≠ b ∧
        ((a ≠ z ∧ b ≠ z ∧ K.Adj (emb a) (emb b)) ∨
         (a = z ∧ (K.Adj x₀ (emb b) ∨ K.Adj y₀ (emb b))) ∨
         (b = z ∧ (K.Adj x₀ (emb a) ∨ K.Adj y₀ (emb a))))
      symm := ⟨by
        rintro a b ⟨hab, ⟨ha, hb, h⟩ | ⟨ha, h⟩ | ⟨hb, h⟩⟩
        · exact ⟨hab.symm, Or.inl ⟨hb, ha, h.symm⟩⟩
        · exact ⟨hab.symm, Or.inr (Or.inr ⟨ha, h⟩)⟩
        · exact ⟨hab.symm, Or.inr (Or.inl ⟨hb, h⟩)⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  -- Key properties linking `K` and `K'` via `π`:
  have hK'_of_K : ∀ {u v : Fin (M + 1)}, K.Adj u v → π u ≠ π v → K'.Adj (π u) (π v) := by
    intro u v huv hne
    have hemb_π : ∀ {q : Fin (M + 1)}, π q ≠ z → emb (π q) = q := by
      intro q hqz
      have hqy : q ≠ y₀ := fun h => hqz (h ▸ hπ_y₀)
      simp only [π, hqy, ↓reduceDIte]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨q, hqy⟩)
    refine ⟨hne, ?_⟩
    by_cases hu_z : π u = z
    · have hv_z : π v ≠ z := fun h => hne (hu_z.trans h.symm)
      right; left
      refine ⟨hu_z, ?_⟩
      rw [hemb_π hv_z]
      rcases hπ_inj u x₀ (hu_z.trans hπ_x₀.symm) with rfl | hpair
      · exact Or.inl huv
      · have hu_in : u ∈ ({x₀, y₀} : Set _) := hpair ▸ mem_insert u _
        exact hu_in.elim (fun h => Or.inl (h ▸ huv)) (fun h => Or.inr (h ▸ huv))
    · by_cases hv_z : π v = z
      · right; right
        refine ⟨hv_z, ?_⟩
        rw [hemb_π hu_z]
        rcases hπ_inj v x₀ (hv_z.trans hπ_x₀.symm) with rfl | hpair
        · exact Or.inl huv.symm
        · have hv_in : v ∈ ({x₀, y₀} : Set _) := hpair ▸ mem_insert v _
          exact hv_in.elim (fun h => Or.inl (h ▸ huv.symm)) (fun h => Or.inr (h ▸ huv.symm))
      · left
        rw [hemb_π hu_z, hemb_π hv_z]
        exact ⟨hu_z, hv_z, huv⟩
  have hK'_lift : ∀ a b : Fin M, K'.Adj a b →
      ∃ u v : Fin (M + 1), π u = a ∧ π v = b ∧ K.Adj u v := by
    rintro a b ⟨_, ⟨_, _, h⟩ | ⟨rfl, h | h⟩ | ⟨rfl, h | h⟩⟩
    · exact ⟨emb a, emb b, hπ_emb a, hπ_emb b, h⟩
    · exact ⟨x₀, emb b, hπ_x₀, hπ_emb b, h⟩
    · exact ⟨y₀, emb b, hπ_y₀, hπ_emb b, h⟩
    · exact ⟨emb a, x₀, hπ_emb a, hπ_x₀, h.symm⟩
    · exact ⟨emb a, y₀, hπ_emb a, hπ_y₀, h.symm⟩
  -- Connectedness transfer from `K - T` to `K' - S'` whenever `T = π ⁻¹' S'`!
  have hconn_of_preimage : ∀ (S' : Finset (Fin M)) (T : Finset (Fin (M + 1))),
      (∀ u : Fin (M + 1), u ∈ T ↔ π u ∈ S') →
      (K.induce {u : Fin (M + 1) | u ∉ T}).Connected →
      (K'.induce {w : Fin M | w ∉ S'}).Connected := by
    intro S' T hT hconnT
    obtain ⟨u₀, hu₀⟩ := hconnT.nonempty
    have : Nonempty {w : Fin M | w ∉ S'} := ⟨⟨π u₀, fun h => hu₀ ((hT u₀).mpr h)⟩⟩
    refine ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => ?_⟩
    have haT : emb a ∉ T := fun h => ha (by simpa only [hπ_emb] using (hT (emb a)).mp h)
    have hbT : emb b ∉ T := fun h => hb (by simpa only [hπ_emb] using (hT (emb b)).mp h)
    obtain ⟨w⟩ := hconnT.preconnected ⟨emb a, haT⟩ ⟨emb b, hbT⟩
    have hwalk : ∀ {p q : {u : Fin (M + 1) | u ∉ T}}
        (r : (K.induce {u : Fin (M + 1) | u ∉ T}).Walk p q),
        (K'.induce {w : Fin M | w ∉ S'}).Reachable
          ⟨π p.1, fun h => p.2 ((hT p.1).mpr h)⟩
          ⟨π q.1, fun h => q.2 ((hT q.1).mpr h)⟩ := by
      intro p q r
      induction r with
      | nil => exact Reachable.rfl
      | @cons p₁ p₂ p₃ hp12 r' ih =>
        by_cases heq : π p₁.1 = π p₂.1
        · have hsub_eq : (⟨π p₁.1, fun h => p₁.2 ((hT p₁.1).mpr h)⟩ : {w : Fin M | w ∉ S'}) =
              ⟨π p₂.1, fun h => p₂.2 ((hT p₂.1).mpr h)⟩ := Subtype.ext heq
          exact hsub_eq ▸ ih
        · have hadj' : K'.Adj (π p₁.1) (π p₂.1) := hK'_of_K hp12 heq
          have hstep : (K'.induce {w : Fin M | w ∉ S'}).Reachable
              ⟨π p₁.1, fun h => p₁.2 ((hT p₁.1).mpr h)⟩
              ⟨π p₂.1, fun h => p₂.2 ((hT p₂.1).mpr h)⟩ :=
            Adj.reachable (G := K'.induce {w : Fin M | w ∉ S'})
              (u := ⟨π p₁.1, _⟩) (v := ⟨π p₂.1, _⟩) hadj'
          exact hstep.trans ih
    simpa only [hπ_emb] using hwalk w
  -- Prove `Is3ConnectedFin K'`!
  have h3' : Is3ConnectedFin K' := by
    refine ⟨hM, fun S' hS' => ?_⟩
    have hπ_iff_z : ∀ u : Fin (M + 1), π u = z ↔ u = x₀ ∨ u = y₀ := by
      intro u
      constructor
      · intro h
        rcases hπ_inj u x₀ (h.trans hπ_x₀.symm) with rfl | hpair
        · exact Or.inl rfl
        · have hm : u ∈ ({x₀, y₀} : Set (Fin (M + 1))) := hpair ▸ mem_insert u _
          exact hm
      · rintro (rfl | rfl)
        · exact hπ_x₀
        · exact hπ_y₀
    by_cases hzS' : z ∈ S'
    · by_cases hS'1 : S'.card ≤ 1
      · -- `S' = {z}`, so `π ⁻¹' S' = {x₀, y₀}` (`card ≤ 2`)!
        have hS'_eq : S' = {z} := by
          have hpos : 0 < S'.card := Finset.card_pos.mpr ⟨z, hzS'⟩
          obtain ⟨w, hw⟩ := Finset.card_eq_one.mp (by omega : S'.card = 1)
          have hzw : z = w := Finset.mem_singleton.mp (hw ▸ hzS')
          exact hzw ▸ hw
        refine hconn_of_preimage S' {x₀, y₀} ?_ (h3.2 {x₀, y₀} Finset.card_le_two)
        intro u
        rw [hS'_eq, Finset.mem_singleton, Finset.mem_insert, Finset.mem_singleton, hπ_iff_z]
      · -- `S'.card = 2` with `z ∈ S'`, so `S' = {z, w₀}` (`w₀ ≠ z`) and `π ⁻¹' S' = {x₀, y₀, emb w₀}`!
        have hcard_er : (S'.erase z).card = 1 := by
          rw [Finset.card_erase_of_mem hzS']; omega
        obtain ⟨w₀, hw₀_eq⟩ := Finset.card_eq_one.mp hcard_er
        have hw₀_mem : w₀ ∈ S'.erase z := hw₀_eq ▸ Finset.mem_singleton_self w₀
        have hw₀z : w₀ ≠ z := (Finset.mem_erase.mp hw₀_mem).1
        have hS'_eq : S' = {z, w₀} := by
          ext w
          constructor
          · intro hw
            by_cases hwz : w = z
            · simp [hwz]
            · have : w = w₀ := Finset.mem_singleton.mp (hw₀_eq ▸ Finset.mem_erase.mpr ⟨hwz, hw⟩)
              simp [this]
          · simp only [Finset.mem_insert, Finset.mem_singleton]
            rintro (rfl | rfl)
            · exact hzS'
            · exact Finset.mem_of_mem_erase hw₀_mem
        have hu₀_not : emb w₀ ∉ ({x₀, y₀} : Finset (Fin (M + 1))) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨fun h => hw₀z (hemb_inj (h.trans hemb_z.symm)), hemb_ne_y₀ w₀⟩
        refine hconn_of_preimage S' {x₀, y₀, emb w₀} ?_ (hno3cut (emb w₀) hu₀_not)
        intro u
        rw [hS'_eq]
        have key : π u = w₀ ↔ u = emb w₀ := by
          constructor
          · intro hπw₀
            have huy : u ≠ y₀ := fun h => hw₀z (hπw₀.symm.trans (h ▸ hπ_y₀))
            have hemb_u : emb (π u) = u := by
              simp only [π, huy, ↓reduceDIte]
              exact congrArg Subtype.val (e.apply_symm_apply ⟨u, huy⟩)
            rw [← hemb_u, hπw₀]
          · intro h
            rw [h]
            exact hπ_emb w₀
        simp only [Finset.mem_insert, Finset.mem_singleton, hπ_iff_z, key]
        tauto
    · -- `z ∉ S'`: `π ⁻¹' S' = S'.image emb` has cardinality `S'.card ≤ 2`!
      let T : Finset (Fin (M + 1)) := S'.image emb
      have hT_card : T.card ≤ 2 := by
        rw [Finset.card_image_of_injective S' hemb_inj]
        exact hS'
      refine hconn_of_preimage S' T ?_ (h3.2 T hT_card)
      intro u
      simp only [T, Finset.mem_image]
      constructor
      · rintro ⟨w, hwS', rfl⟩
        rwa [hπ_emb]
      · intro hπS'
        have huy : u ≠ y₀ := fun h => hzS' (hπ_y₀ ▸ h ▸ hπS')
        refine ⟨π u, hπS', ?_⟩
        simp only [π, huy, ↓reduceDIte]
        exact congrArg Subtype.val (e.apply_symm_apply ⟨u, huy⟩)
  -- Minor-lifting for `K_5` and `K_{3,3}` via preimages under `π`!
  have hliftK5 : HasK5MinorSimple K' → HasK5MinorSimple K := by
    rintro ⟨B, hne, hpre, hdisj, hadj⟩
    refine ⟨fun i => π ⁻¹' B i, ?_, ?_, ?_, ?_⟩
    · intro i
      obtain ⟨w, hw⟩ := hne i
      exact ⟨emb w, by show π (emb w) ∈ B i; rwa [hπ_emb]⟩
    · intro i
      exact preconnected_preimage_of_contract hxy π hπ_x₀ hπ_y₀ hπ_inj hK'_lift (hpre i)
    · intro i j hij
      exact (hdisj hij).preimage π
    · intro i j hij
      obtain ⟨a, ha, b, hb, hab⟩ := hadj hij
      obtain ⟨u, v, hπu, hπv, huv⟩ := hK'_lift a b hab
      exact ⟨u, by simp only [mem_preimage, hπu]; exact ha, v, by simp only [mem_preimage, hπv]; exact hb, huv⟩
  have hliftK33 : HasK33MinorSimple K' → HasK33MinorSimple K := by
    rintro ⟨A, B, hAne, hBne, hApre, hBpre, hAdisj, hBdisj, hABdisj, hadj⟩
    refine ⟨fun i => π ⁻¹' A i, fun j => π ⁻¹' B j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; obtain ⟨w, hw⟩ := hAne i; exact ⟨emb w, by show π (emb w) ∈ A i; rwa [hπ_emb]⟩
    · intro j; obtain ⟨w, hw⟩ := hBne j; exact ⟨emb w, by show π (emb w) ∈ B j; rwa [hπ_emb]⟩
    · intro i; exact preconnected_preimage_of_contract hxy π hπ_x₀ hπ_y₀ hπ_inj hK'_lift (hApre i)
    · intro j; exact preconnected_preimage_of_contract hxy π hπ_x₀ hπ_y₀ hπ_inj hK'_lift (hBpre j)
    · intro i₁ i₂ hii; exact (hAdisj hii).preimage π
    · intro j₁ j₂ hjj; exact (hBdisj hjj).preimage π
    · intro i j; exact (hABdisj i j).preimage π
    · intro i j
      obtain ⟨a, ha, b, hb, hab⟩ := hadj i j
      obtain ⟨u, v, hπu, hπv, huv⟩ := hK'_lift a b hab
      exact ⟨u, by simp only [mem_preimage, hπu]; exact ha, v, by simp only [mem_preimage, hπv]; exact hb, huv⟩
  exact ⟨z, emb, K', hemb_z, hemb_inj, hemb_surj, hemb_ne_y₀, fun _ _ => Iff.rfl,
    h3', hliftK5, hliftK33⟩

/-! ### Part 4: Thomassen's Contractible Edge Lemma (Diestel, Lemma 3.2.4) -/

private noncomputable def cutComp {N : ℕ} (K : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (p : {u : Fin N // u ∉ S}) : Finset (Fin N) := by
  classical
  exact (Finset.univ \ S).filter fun u =>
    ∃ hu : u ∉ S, (K.induce {v : Fin N | v ∉ S}).Reachable p ⟨u, hu⟩

private theorem mem_cutComp_self {N : ℕ} {K : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    (p : {u : Fin N // u ∉ S}) : p.1 ∈ cutComp K S p := by
  classical
  simp only [cutComp, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact ⟨p.2, p.2, Reachable.rfl⟩

private theorem notMem_of_mem_cutComp {N : ℕ} {K : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {p : {u : Fin N // u ∉ S}} {u : Fin N} (hu : u ∈ cutComp K S p) : u ∉ S := by
  classical
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hu).1).2

private theorem cutComp_closed {N : ℕ} {K : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {p : {u : Fin N // u ∉ S}} {u v : Fin N}
    (hu : u ∈ cutComp K S p) (hvS : v ∉ S) (huv : K.Adj u v) :
    v ∈ cutComp K S p := by
  classical
  obtain ⟨_, huS, hr⟩ := Finset.mem_filter.mp hu
  rw [cutComp, Finset.mem_filter]
  refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvS⟩, hvS, ?_⟩
  exact hr.trans (Adj.reachable (G := K.induce {v : Fin N | v ∉ S})
    (u := ⟨u, huS⟩) (v := ⟨v, hvS⟩) huv)

private theorem cutComp_disjoint {N : ℕ} {K : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {p q : {u : Fin N // u ∉ S}} (hq : q.1 ∉ cutComp K S p) :
    Disjoint (cutComp K S p) (cutComp K S q) := by
  classical
  rw [Finset.disjoint_left]
  intro w hwp hwq
  apply hq
  obtain ⟨_, _, hrp⟩ := Finset.mem_filter.mp hwp
  obtain ⟨_, _, hrq⟩ := Finset.mem_filter.mp hwq
  rw [cutComp, Finset.mem_filter]
  exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, q.2⟩, q.2, hrp.trans hrq.symm⟩

private theorem exists_pair_of_not_conn {N : ℕ} {K : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} (hN : 5 ≤ N) (hS : S.card ≤ 3)
    (hnot : ¬ (K.induce {u : Fin N | u ∉ S}).Connected) :
    ∃ p q : {u : Fin N // u ∉ S}, q.1 ∉ cutComp K S p := by
  classical
  have hpos : 0 < (Finset.univ \ S).card := by
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ, Fintype.card_fin] at hc
    omega
  obtain ⟨p₀, hp₀⟩ := Finset.card_pos.mp hpos
  let p : {u : Fin N // u ∉ S} := ⟨p₀, (Finset.mem_sdiff.mp hp₀).2⟩
  by_contra hall
  push Not at hall
  apply hnot
  have : Nonempty {u : Fin N | u ∉ S} := ⟨⟨p.1, p.2⟩⟩
  refine ⟨fun a b => ?_⟩
  have hr : ∀ w : {u : Fin N | u ∉ S}, (K.induce {u : Fin N | u ∉ S}).Reachable ⟨p.1, p.2⟩ w := by
    intro w
    have h := hall p ⟨w.1, w.2⟩
    simp only [cutComp, Finset.mem_filter] at h
    obtain ⟨_, _, hrw⟩ := h
    exact hrw
  exact (hr a).symm.trans (hr b)

private theorem mem_cutComp_iff {N : ℕ} {K : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {p : {u : Fin N // u ∉ S}} {u : Fin N} :
    u ∈ cutComp K S p ↔ ∃ hu : u ∉ S, (K.induce {v : Fin N | v ∉ S}).Reachable p ⟨u, hu⟩ := by
  classical
  simp only [cutComp, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- A walk of an induced graph whose vertices all lie in `Y` gives reachability in the graph
induced on `Y`. -/
private theorem reachable_of_walk_subset {N : ℕ} {K : SimpleGraph (Fin N)} {X Y : Set (Fin N)}
    {a b : X} (r : (K.induce X).Walk a b) (hY : ∀ t ∈ r.support, t.1 ∈ Y) :
    (K.induce Y).Reachable ⟨a.1, hY a r.start_mem_support⟩ ⟨b.1, hY b r.end_mem_support⟩ := by
  induction r with
  | nil => exact Reachable.rfl
  | @cons a c b hac r ih =>
    have hc : c.1 ∈ Y := hY c (by simp)
    have h1 : (K.induce Y).Reachable ⟨a.1, hY a (by simp)⟩ ⟨c.1, hc⟩ :=
      Adj.reachable (G := K.induce Y) (u := ⟨a.1, hY a (by simp)⟩) (v := ⟨c.1, hc⟩) hac
    exact h1.trans (ih fun t ht => hY t (by simp [ht]))

/-- In a `3`-connected graph, every vertex of a separating set `S` of at most three vertices has a
neighbour in every component of `K - S`. -/
private theorem exists_adj_in_cutComp {N : ℕ} {K : SimpleGraph (Fin N)}
    (h3 : Is3ConnectedFin K) {S : Finset (Fin N)} (hS : S.card ≤ 3)
    {p q : {u : Fin N // u ∉ S}} (hq : q.1 ∉ cutComp K S p) {s : Fin N} (hs : s ∈ S) :
    ∃ v ∈ cutComp K S p, K.Adj s v := by
  classical
  have hcard : (S.erase s).card ≤ 2 := by rw [Finset.card_erase_of_mem hs]; omega
  have hp' : p.1 ∉ S.erase s := fun h => p.2 (Finset.mem_of_mem_erase h)
  have hq' : q.1 ∉ S.erase s := fun h => q.2 (Finset.mem_of_mem_erase h)
  obtain ⟨w⟩ := (h3.2 (S.erase s) hcard).preconnected ⟨p.1, hp'⟩ ⟨q.1, hq'⟩
  have hwalk : ∀ {a b : {x : Fin N | x ∉ S.erase s}}
      (r : (K.induce {x : Fin N | x ∉ S.erase s}).Walk a b),
      a.1 ∈ cutComp K S p → b.1 ∉ cutComp K S p → ∃ v ∈ cutComp K S p, K.Adj s v := by
    intro a b r
    induction r with
    | nil => intro ha hb; exact (hb ha).elim
    | @cons a c b hac r ih =>
      intro ha hb
      by_cases hcs : c.1 = s
      · have hca : K.Adj c.1 a.1 := hac.symm
        rw [hcs] at hca
        exact ⟨a.1, ha, hca⟩
      · have hcS : c.1 ∉ S := fun h => c.2 (Finset.mem_erase.mpr ⟨hcs, h⟩)
        exact ih (cutComp_closed ha hcS hac) hb
  exact hwalk w (mem_cutComp_self p) hq

/-- **Contractible edges** (R. Diestel, *Graph Theory*, 6th ed., Springer, Lemma 3.2.4; the
lemma is due to Thomassen): a `3`-connected graph with at least five vertices has an edge `x₀y₀`
such that deleting `x₀`, `y₀` and any third vertex leaves a connected graph, that is, `K / x₀y₀` is
again `3`-connected. We follow Diestel's proof: if no edge is good, choose an edge `xy`, a vertex
`z` and a component `D` of `K - {x, y, z}` with `|D|` least; a neighbour `v ∈ D` of `z` gives a
separating set `{z, v, w}`, and a component of `K - {z, v, w}` missing `x` and `y` is a smaller
such component, inside `D`. -/
theorem exists_good_edge {M : ℕ} (hM : 4 ≤ M) (K : SimpleGraph (Fin (M + 1)))
    (h3 : Is3ConnectedFin K) :
    ∃ x₀ y₀ : Fin (M + 1), K.Adj x₀ y₀ ∧
      ∀ u₀ : Fin (M + 1), u₀ ∉ ({x₀, y₀} : Finset (Fin (M + 1))) →
        (K.induce {v : Fin (M + 1) | v ∉ ({x₀, y₀, u₀} : Finset (Fin (M + 1)))}).Connected := by
  classical
  by_contra hno
  push Not at hno
  have hN : 5 ≤ M + 1 := by omega
  let Bad (n : ℕ) : Prop :=
    ∃ (x y z : Fin (M + 1)), K.Adj x y ∧ z ∉ ({x, y} : Finset (Fin (M + 1))) ∧
      ∃ p q : {u : Fin (M + 1) // u ∉ ({x, y, z} : Finset (Fin (M + 1)))},
        q.1 ∉ cutComp K {x, y, z} p ∧ (cutComp K {x, y, z} p).card = n
  have hex : ∃ n, Bad n := by
    obtain ⟨v₀, _, _, _, _, _, hv₀, _, _⟩ :=
      exists_three_neighbors_of_is3ConnectedFin h3 ⟨0, by omega⟩
    obtain ⟨z₀, hz₀, hcut₀⟩ := hno _ v₀ hv₀
    obtain ⟨p₀, q₀, hq₀⟩ := exists_pair_of_not_conn hN Finset.card_le_three hcut₀
    exact ⟨_, _, _, _, hv₀, hz₀, p₀, q₀, hq₀, rfl⟩
  obtain ⟨x, y, z, hxy, hz, p, q, hq, hcard⟩ := Nat.find_spec hex
  have hmin : ∀ m, Bad m → Nat.find hex ≤ m := fun m hm => Nat.find_min' hex hm
  have hzS : z ∈ ({x, y, z} : Finset (Fin (M + 1))) := by simp
  obtain ⟨v, hvD, hzv⟩ := exists_adj_in_cutComp h3 Finset.card_le_three hq hzS
  have hvS : v ∉ ({x, y, z} : Finset (Fin (M + 1))) := notMem_of_mem_cutComp hvD
  obtain ⟨w, hw, hcut'⟩ := hno z v hzv
  set S' : Finset (Fin (M + 1)) := {z, v, w} with hS'def
  obtain ⟨p', q', hq'⟩ := exists_pair_of_not_conn hN Finset.card_le_three hcut'
  have hvS' : v ∈ S' := by simp [S']
  have hzS' : z ∈ S' := by simp [S']
  have hxS : x ∈ ({x, y, z} : Finset (Fin (M + 1))) := by simp
  have hyS : y ∈ ({x, y, z} : Finset (Fin (M + 1))) := by simp
  -- A component of `K - S'` that misses `x` and `y`.
  have hdisj := cutComp_disjoint hq'
  have hp'q : p'.1 ∉ cutComp K S' q' := fun h =>
    Finset.disjoint_left.mp hdisj (mem_cutComp_self p') h
  have hpick : ∃ r r' : {u : Fin (M + 1) // u ∉ S'}, r'.1 ∉ cutComp K S' r ∧
      x ∉ cutComp K S' r ∧ y ∉ cutComp K S' r := by
    by_cases h1 : x ∉ cutComp K S' p' ∧ y ∉ cutComp K S' p'
    · exact ⟨p', q', hq', h1.1, h1.2⟩
    · refine ⟨q', p', hp'q, ?_, ?_⟩
      · intro hx2
        have hxS' : x ∉ S' := notMem_of_mem_cutComp hx2
        rcases not_and_or.mp h1 with h | h
        · exact Finset.disjoint_left.mp hdisj (not_not.mp h) hx2
        · have hyS' : y ∉ S' := notMem_of_mem_cutComp (not_not.mp h)
          exact Finset.disjoint_left.mp hdisj (cutComp_closed (not_not.mp h) hxS' hxy.symm) hx2
      · intro hy2
        have hyS' : y ∉ S' := notMem_of_mem_cutComp hy2
        rcases not_and_or.mp h1 with h | h
        · exact Finset.disjoint_left.mp hdisj (cutComp_closed (not_not.mp h) hyS' hxy) hy2
        · exact Finset.disjoint_left.mp hdisj (not_not.mp h) hy2
  obtain ⟨r, r', hr', hxr, hyr⟩ := hpick
  set D' := cutComp K S' r with hD'def
  obtain ⟨u, huD', hvu⟩ := exists_adj_in_cutComp h3 Finset.card_le_three hr' hvS'
  have hnotS : ∀ t ∈ D', t ∉ ({x, y, z} : Finset (Fin (M + 1))) := by
    intro t ht htS
    have htS' : t ∉ S' := notMem_of_mem_cutComp ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at htS
    rcases htS with rfl | rfl | rfl
    · exact hxr ht
    · exact hyr ht
    · exact htS' hzS'
  have huD : u ∈ cutComp K ({x, y, z} : Finset (Fin (M + 1))) p := cutComp_closed hvD (hnotS u huD') hvu
  have hsub : D' ⊆ cutComp K ({x, y, z} : Finset (Fin (M + 1))) p := by
    intro t ht
    obtain ⟨huS', hru⟩ := mem_cutComp_iff.mp huD'
    obtain ⟨htS', hrt⟩ := mem_cutComp_iff.mp ht
    obtain ⟨wk⟩ := hru.symm.trans hrt
    have hY : ∀ t' ∈ wk.support, t'.1 ∈ {a : Fin (M + 1) | a ∉ ({x, y, z} : Finset (Fin (M + 1)))} := by
      intro t' ht'
      have hreach : (K.induce {a : Fin (M + 1) | a ∉ S'}).Reachable r t' :=
        hru.trans (wk.takeUntil t' ht').reachable
      exact hnotS t'.1 (mem_cutComp_iff.mpr ⟨t'.2, hreach⟩)
    have h2 := reachable_of_walk_subset wk hY
    obtain ⟨huS, hpu⟩ := mem_cutComp_iff.mp huD
    exact mem_cutComp_iff.mpr ⟨hnotS t ht, hpu.trans h2⟩
  have hlt : D'.card < (cutComp K ({x, y, z} : Finset (Fin (M + 1))) p).card :=
    Finset.card_lt_card ⟨hsub, fun h => notMem_of_mem_cutComp (h hvD) hvS'⟩
  have hbad : Bad D'.card := ⟨z, v, w, hzv, hw, r, r', hr', rfl⟩
  have := hmin _ hbad
  omega

/-- **Contractible edges** (R. Diestel, *Graph Theory*, 6th ed., Springer, Lemma 3.2.4): every
`3`-connected simple graph `K` on `M + 1 ≥ 5` vertices has an edge `x₀y₀` whose contraction
`K' : SimpleGraph (Fin M)` is `3`-connected; `K_5` and `K_{3,3}` minors of `K'` lift to `K`. -/
theorem exists_contractible_edge {M : ℕ} (hM : 4 ≤ M)
    (K : SimpleGraph (Fin (M + 1))) (h3 : Is3ConnectedFin K) :
    ∃ (x₀ y₀ : Fin (M + 1)) (z : Fin M) (emb : Fin M → Fin (M + 1)) (K' : SimpleGraph (Fin M)),
      K.Adj x₀ y₀ ∧
      emb z = x₀ ∧
      Injective emb ∧
      (∀ u : Fin (M + 1), u ≠ y₀ → ∃ w : Fin M, emb w = u) ∧
      (∀ w : Fin M, emb w ≠ y₀) ∧
      (∀ a b : Fin M, K'.Adj a b ↔ a ≠ b ∧
        ((a ≠ z ∧ b ≠ z ∧ K.Adj (emb a) (emb b)) ∨
         (a = z ∧ (K.Adj x₀ (emb b) ∨ K.Adj y₀ (emb b))) ∨
         (b = z ∧ (K.Adj x₀ (emb a) ∨ K.Adj y₀ (emb a))))) ∧
      Is3ConnectedFin K' ∧
      (HasK5MinorSimple K' → HasK5MinorSimple K) ∧
      (HasK33MinorSimple K' → HasK33MinorSimple K) := by
  obtain ⟨x₀, y₀, hxy, hgood⟩ := exists_good_edge hM K h3
  obtain ⟨z, emb, K', hz, hinj, hsurj, hney, hadj, h3', hK5, hK33⟩ :=
    contract_edge_spec hM h3 hxy hgood
  exact ⟨x₀, y₀, z, emb, K', hxy, hz, hinj, hsurj, hney, hadj, h3', hK5, hK33⟩

end GraphMinor.Wagner
