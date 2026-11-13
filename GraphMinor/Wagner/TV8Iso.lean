module

public import GraphMinor.Wagner.TV8
public import GraphMinor.Wagner.ConnectivityReduction
public import GraphMinor.Wagner.TripodTriangle
public import GraphMinor.Wagner.MultigraphReduction

/-!
# A `3`-connected graph with no `K_5` minor that contains a subdivision of `V_8` is `V_8`

Let `T` be a subdivision of `V_8` in a `3`-connected graph `K` with no `K_5` minor. We show that `K`
is isomorphic to `V_8` (`TV8.iso`), in three steps.

* Every path of `T` is a single edge (`TV8.I_empty`). Otherwise an inner vertex of the path of the
  edge `k` is joined, avoiding the two ends of `k`, to the rest of `T`. A shortest such link joins
  the path of `k` to a branch vertex or path elsewhere, and we can pick ends of the two places that
  are not adjacent in `V_8`. This gives a `K_5` minor by `V8Model.hasK5_of_link`.
* Every vertex is a branch vertex (`TV8.surj`). Otherwise the component `D` of a vertex outside `T`
  in `K` minus the branch vertices has edges to at least three branch vertices, since `K` is
  `3`-connected. Two of them are not adjacent in `V_8`, and `D` gives a `K_5` minor by
  `V8Model.hasK5_of_set`.
* Two branch vertices are adjacent exactly when they are adjacent in `V_8` (`TV8.adj_iff`), since an
  extra edge gives a `K_5` minor.
-/

@[expose] public section

namespace GraphMinor.Wagner

open Set Function SimpleGraph

variable {N : ℕ} {K : SimpleGraph (Fin N)}

namespace TV8

variable (T : TV8 K)

/-- The owner of edge `k` under the choice that gives `k` to the end chosen by `β` and all other
edges to their first ends. -/
theorem owner_update (β : Bool) (k : Fin 12) :
    owner (fun k'' => if k'' = k then β else true) k = if β then v8e1 k else v8e2 k := by
  simp [owner]

theorem owner_update2 (β β' : Bool) {k k' : Fin 12} (hkk : k ≠ k') :
    owner (fun k'' => if k'' = k then β else if k'' = k' then β' else true) k =
        (if β then v8e1 k else v8e2 k) ∧
      owner (fun k'' => if k'' = k then β else if k'' = k' then β' else true) k' =
        (if β' then v8e1 k' else v8e2 k') := by
  simp [owner, Ne.symm hkk]

theorem ite_mem_ends (β : Bool) (k : Fin 12) :
    (if β then v8e1 k else v8e2 k) = v8e1 k ∨ (if β then v8e1 k else v8e2 k) = v8e2 k := by
  cases β <;> simp

/-- **Every path of the subdivision is a single edge.** -/
theorem I_empty (h3 : Is3ConnectedFin K) (hK5 : ¬ HasK5MinorSimple K) (k : Fin 12) :
    T.I k = [] := by
  classical
  by_contra hne
  obtain ⟨u₀, hu₀⟩ := List.exists_mem_of_ne_nil _ hne
  set p₀ := v8e1 k
  set q₀ := v8e2 k
  let S : Finset (Fin N) := {T.w p₀, T.w q₀}
  have hW : (K.induce {y | y ∉ S}).Preconnected :=
    (h3.2 S (Finset.card_le_two)).preconnected
  let A : Fin 2 → Set (Fin N) := ![{x | x ∈ T.I k},
    {x | (∃ i, x = T.w i ∧ i ≠ p₀ ∧ i ≠ q₀) ∨ ∃ k', k' ≠ k ∧ x ∈ T.I k'}]
  have hd01 : Disjoint (A 0) (A 1) := by
    refine disjoint_left.mpr fun x hx hx' => ?_
    rcases hx' with ⟨i, rfl, -, -⟩ | ⟨k', hk', hx'⟩
    · exact T.I_w k _ hx i rfl
    · exact T.I_disj k k' (Ne.symm hk') x hx hx'
  have hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hd01
    · exact hd01.symm
    · exact absurd rfl hij
  have hAW : ∀ i, A i ⊆ {y | y ∉ S} := by
    intro i x hx
    simp only [mem_ofPred_eq, S, Finset.mem_insert, Finset.mem_singleton, not_or]
    fin_cases i
    · exact ⟨T.I_w k x hx p₀, T.I_w k x hx q₀⟩
    · rcases hx with ⟨i, rfl, hi1, hi2⟩ | ⟨k', -, hx⟩
      · exact ⟨fun h => hi1 (T.w_inj h), fun h => hi2 (T.w_inj h)⟩
      · exact ⟨T.I_w k' x hx p₀, T.I_w k' x hx q₀⟩
  obtain ⟨r, hr1, hr2⟩ := v8_third k
  -- Inner vertices of a link avoid the whole subdivision.
  have havoid : ∀ z, z ∈ {y | y ∉ S} → (∀ i, z ∉ A i) → z ∉ T.VS := by
    intro z hzW hzA hzV
    simp only [mem_ofPred_eq, S, Finset.mem_insert, Finset.mem_singleton, not_or] at hzW
    rcases hzV with ⟨i, rfl⟩ | ⟨k'', hz⟩
    · by_cases h1 : i = p₀
      · exact hzW.1 (by rw [h1])
      · by_cases h2 : i = q₀
        · exact hzW.2 (by rw [h2])
        · exact hzA 1 (Or.inl ⟨i, rfl, h1, h2⟩)
    · by_cases hk : k'' = k
      · subst hk
        exact hzA 0 hz
      · exact hzA 1 (Or.inr ⟨k'', hk, hz⟩)
  have key : ∀ (a b : Fin N) (mid : List (Fin N)), a ∈ A 0 → b ∈ A 1 →
      (a :: mid ++ [b]).IsChain K.Adj → (∀ z ∈ mid, z ∉ T.VS) → False := by
    intro a b mid ha hb hch hmid
    rcases hb with ⟨r', rfl, hr1', hr2'⟩ | ⟨k', hk', hb⟩
    · obtain ⟨β, hβ⟩ := v8_choice_vertex k r' hr1' hr2'
      let τ : Fin 12 → Bool := fun k'' => if k'' = k then β else true
      have hown := owner_update β k
      have hne' : (if β then v8e1 k else v8e2 k) ≠ r' := by
        rcases ite_mem_ends β k with h | h <;> rw [h]
        · exact Ne.symm hr1'
        · exact Ne.symm hr2'
      refine hK5 ((T.model τ).hasK5_of_link hne' hβ (a := a) (b := T.w r') ?_ (Or.inl rfl) hch
        fun z hz i hzi => hmid z hz (T.MS_sub τ i hzi))
      exact Or.inr ⟨k, hown, ha⟩
    · obtain ⟨β, β', hne', hna⟩ := v8_choice_edge k k' (Ne.symm hk')
      let τ : Fin 12 → Bool := fun k'' => if k'' = k then β else if k'' = k' then β' else true
      obtain ⟨hown, hown'⟩ := owner_update2 β β' (Ne.symm hk')
      exact hK5 ((T.model τ).hasK5_of_link hne' hna (a := a) (b := b) (Or.inr ⟨k, hown, ha⟩)
        (Or.inr ⟨k', hown', hb⟩) hch fun z hz i hzi => hmid z hz (T.MS_sub τ i hzi))
  obtain ⟨i, j, a, b, mid, hij, ha, hb, hmid, -, hch⟩ :=
    exists_hpath hW A hdisj hAW (i := 0) (j := 1) (by decide) (x := u₀) (y := T.w r) hu₀
      (Or.inl ⟨r, rfl, hr1, hr2⟩)
  have hmid' : ∀ z ∈ mid, z ∉ T.VS := fun z hz => havoid z (hmid z hz).1 (hmid z hz).2
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact key a b mid ha hb hch hmid'
  · exact key b a mid.reverse hb ha (isChain_reverse_path hch)
      fun z hz => hmid' z (List.mem_reverse.mp hz)
  · exact absurd rfl hij

theorem fin8_avoid2 : ∀ i₁ i₂ : Fin 8, ∃ i₃, i₃ ≠ i₁ ∧ i₃ ≠ i₂ := by decide

/-- The vertices reachable from `x` inside `X` induce a preconnected subgraph. -/
theorem pc_reach {X : Set (Fin N)} {x : Fin N} (hx : x ∈ X) :
    (K.induce {y | ∃ hy : y ∈ X, (K.induce X).Reachable ⟨x, hx⟩ ⟨y, hy⟩}).Preconnected := by
  refine pc_of_star (c := x) fun z ⟨hzX, hz⟩ => ?_
  obtain ⟨l, -, hch, hlX, hh, hl⟩ := exists_pathList_of_reachable hx hzX hz
  refine ⟨{y | y ∈ l}, ?_, List.mem_of_mem_head? hh, List.mem_of_getLast? hl, pc_of_isChain hch⟩
  intro y hy
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hy
  have hch' : (l₁ ++ [y]).IsChain K.Adj := by
    have e : l₁ ++ y :: l₂ = (l₁ ++ [y]) ++ l₂ := by simp
    rw [e] at hch
    exact hch.left_of_append
  have hxin : x ∈ l₁ ++ [y] := by
    rcases l₁ with _ | ⟨a, l₁⟩
    · simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hh
      simp [hh]
    · simp only [List.cons_append, List.head?_cons, Option.some.injEq] at hh
      simp [hh]
  have hsub : {w | w ∈ l₁ ++ [y]} ⊆ X := fun w hw => hlX w (by
    simp only [mem_ofPred_eq, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact List.mem_append_left _ hw
    · exact List.mem_append_right _ List.mem_cons_self)
  exact ⟨hlX y hy, induce_reach_mono hsub
    (pc_of_isChain hch' ⟨x, hxin⟩ ⟨y, List.mem_append_right _ (List.mem_singleton_self y)⟩)⟩

/-- **Every vertex is a branch vertex.** -/
theorem surj (h3 : Is3ConnectedFin K) (hK5 : ¬ HasK5MinorSimple K) (hI : ∀ k, T.I k = [])
    (x : Fin N) : ∃ i, T.w i = x := by
  classical
  by_contra hx
  push Not at hx
  set X : Set (Fin N) := {y | ∀ i, T.w i ≠ y} with hX
  have hxX : x ∈ X := hx
  set D : Set (Fin N) := {y | ∃ hy : y ∈ X, (K.induce X).Reachable ⟨x, hxX⟩ ⟨y, hy⟩} with hD
  have hDX : D ⊆ X := fun y ⟨hy, _⟩ => hy
  have hxD : x ∈ D := ⟨hxX, Reachable.rfl⟩
  -- `D` has edges to at least three branch vertices.
  have hatt : ∀ i₁ i₂ : Fin 8, ∃ i, i ≠ i₁ ∧ i ≠ i₂ ∧ Touch K D {T.w i} := by
    intro i₁ i₂
    by_contra hno
    push Not at hno
    let S : Finset (Fin N) := {T.w i₁, T.w i₂}
    have hc := h3.2 S Finset.card_le_two
    obtain ⟨i₃, h31, h32⟩ := fin8_avoid2 i₁ i₂
    refine false_of_closed hc.preconnected (D := D) (x := x) (y := T.w i₃) ?_ hxD ?_ ?_ ?_
    · intro y hy
      have hyX := hDX hy
      simp only [mem_ofPred_eq, S, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hyX i₁ h.symm, fun h => hyX i₂ h.symm⟩
    · simp only [mem_ofPred_eq, S, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => h31 (T.w_inj h), fun h => h32 (T.w_inj h)⟩
    · exact fun h => hDX h i₃ rfl
    · intro a ha b hb hab
      by_cases hbX : b ∈ X
      · obtain ⟨haX, hra⟩ := ha
        exact ⟨hbX, hra.trans (Adj.reachable (G := K.induce X) (u := ⟨a, haX⟩) (v := ⟨b, hbX⟩)
          hab)⟩
      · simp only [hX, mem_ofPred_eq, not_forall, not_not] at hbX
        obtain ⟨i, rfl⟩ := hbX
        simp only [mem_ofPred_eq, S, Finset.mem_insert, Finset.mem_singleton, not_or] at hb
        exact (hno i (fun h => hb.1 (by rw [h])) (fun h => hb.2 (by rw [h]))
          ⟨a, ha, T.w i, rfl, hab⟩).elim
  obtain ⟨i₁, -, -, t₁⟩ := hatt 0 0
  obtain ⟨i₂, h21, -, t₂⟩ := hatt i₁ i₁
  obtain ⟨i₃, h31, h32, t₃⟩ := hatt i₁ i₂
  let τ : Fin 12 → Bool := fun _ => true
  have hVS : ∀ i, T.MS τ i ⊆ range T.w := by
    rintro i y (rfl | ⟨k, -, hy⟩)
    · exact ⟨i, rfl⟩
    · rw [hI k] at hy
      exact (List.not_mem_nil hy).elim
  have hDd : ∀ i, Disjoint D ((T.model τ).M i) := fun i =>
    disjoint_left.mpr fun y hy hyi => by
      obtain ⟨j, rfl⟩ := hVS i hyi
      exact hDX hy j rfl
  have tM : ∀ i, Touch K D {T.w i} → Touch K D ((T.model τ).M i) := fun i h =>
    h.mono subset_rfl fun y hy => Or.inl hy
  rcases v8_tri i₁ i₂ i₃ (Ne.symm h21) (Ne.symm h32) (Ne.symm h31) with h | h | h
  · exact hK5 ((T.model τ).hasK5_of_set (Ne.symm h21) h (pc_reach hxX) (tM _ t₁) (tM _ t₂) hDd)
  · exact hK5 ((T.model τ).hasK5_of_set (Ne.symm h32) h (pc_reach hxX) (tM _ t₂) (tM _ t₃) hDd)
  · exact hK5 ((T.model τ).hasK5_of_set (Ne.symm h31) h (pc_reach hxX) (tM _ t₁) (tM _ t₃) hDd)

/-- **Branch vertices are adjacent exactly as in `V_8`.** -/
theorem adj_iff (hK5 : ¬ HasK5MinorSimple K) (hI : ∀ k, T.I k = []) (i j : Fin 8) :
    K.Adj (T.w i) (T.w j) ↔ v8.Adj i j := by
  constructor
  · intro h
    by_contra hna
    have hij : i ≠ j := fun e => K.loopless.irrefl _ (e ▸ h)
    exact hK5 ((T.model fun _ => true).hasK5 hij hna ⟨T.w i, Or.inl rfl, T.w j, Or.inl rfl, h⟩)
  · intro h
    have hedge : ∀ k, K.Adj (T.w (v8e1 k)) (T.w (v8e2 k)) := by
      intro k
      have hch := (T.path k).2
      rw [hI k] at hch
      simpa using hch
    obtain ⟨k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := v8_exists_edge i j h
    · exact hedge k
    · exact (hedge k).symm

end TV8

/-- The links of `wagnerGraphV8`: edge `e` joins `v8e1 e` and `v8e2 e`. -/
theorem wagnerGraphV8_isLink_iff : ∀ (e : Fin 12) (x y : Fin 8),
    GM16.wagnerGraphV8.IsLink e x y ↔ (x = v8e1 e ∧ y = v8e2 e) ∨ (y = v8e1 e ∧ x = v8e2 e) := by
  simp only [GM16.wagnerGraphV8]
  decide

theorem v8_adj_iff_exists_edge : ∀ x y : Fin 8,
    (∃ e, (x = v8e1 e ∧ y = v8e2 e) ∨ (y = v8e1 e ∧ x = v8e2 e)) ↔ v8.Adj x y := by
  decide

theorem v8e_inj : ∀ e₁ e₂ : Fin 12, (v8e1 e₁ = v8e1 e₂ ∧ v8e2 e₁ = v8e2 e₂) ∨
    (v8e1 e₁ = v8e2 e₂ ∧ v8e2 e₁ = v8e1 e₂) → e₁ = e₂ := by
  decide

theorem v8e_ne : ∀ e : Fin 12, v8e1 e ≠ v8e2 e := by decide

/-- Adjacency in `wagnerGraphV8` is adjacency in `v8`. -/
theorem wagnerGraphV8_adj_iff (x y : Fin 8) : GM16.wagnerGraphV8.Adj x y ↔ v8.Adj x y := by
  rw [← v8_adj_iff_exists_edge]
  exact exists_congr fun e => wagnerGraphV8_isLink_iff e x y

/-- `wagnerGraphV8` has no loops and no parallel edges. -/
theorem isSimpleGraphRep_wagnerGraphV8 : IsSimpleGraphRep GM16.wagnerGraphV8 := by
  refine ⟨fun e x h => ?_, fun e₁ e₂ x y h₁ h₂ => ?_⟩
  · have h' := (wagnerGraphV8_isLink_iff e x x).mp h
    rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact v8e_ne e (by rw [← h1, ← h2])
  · rw [wagnerGraphV8_isLink_iff] at h₁ h₂
    refine v8e_inj e₁ e₂ ?_
    rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inr ⟨h2, h1⟩
    · exact Or.inl ⟨h1, h2⟩

/-- The vertices of `wagnerGraphV8` are all of `Fin 8`. -/
def wagnerVertexEquiv : Fin 8 ≃ GM16.wagnerGraphV8.vertexSet where
  toFun i := ⟨i, Set.mem_univ i⟩
  invFun v := v.1
  left_inv _ := rfl
  right_inv _ := rfl

namespace TV8

/-- **A `3`-connected graph with no `K_5` minor that contains a subdivision of `V_8` is `V_8`.** -/
theorem iso (T : TV8 K) (h3 : Is3ConnectedFin K) (hK5 : ¬ HasK5MinorSimple K) :
    Nonempty (Iso (Graph.ofSimpleGraph K) GM16.wagnerGraphV8) := by
  have hI := T.I_empty h3 hK5
  have hbij : Bijective T.w := ⟨T.w_inj, T.surj h3 hK5 hI⟩
  let e := Equiv.ofBijective T.w hbij
  refine nonempty_iso_ofSimpleGraph_of_equiv isSimpleGraphRep_wagnerGraphV8
    (e.symm.trans wagnerVertexEquiv) fun i j => ?_
  obtain ⟨a, rfl⟩ := hbij.2 i
  obtain ⟨b, rfl⟩ := hbij.2 j
  have ha : e.symm (T.w a) = a := e.symm_apply_apply a
  have hb : e.symm (T.w b) = b := e.symm_apply_apply b
  simp only [Equiv.trans_apply, ha, hb]
  change K.Adj (T.w a) (T.w b) ↔ T.w a ≠ T.w b ∧ GM16.wagnerGraphV8.Adj a b
  rw [wagnerGraphV8_adj_iff, T.adj_iff hK5 hI]
  exact ⟨fun h => ⟨fun hab => v8.loopless.irrefl a (T.w_inj hab ▸ h), h⟩, fun h => h.2⟩

end TV8

end GraphMinor.Wagner
