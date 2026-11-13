module

public import GraphMinor.Wagner.TripodTriangle
public import GraphMinor.Wagner.TriangleFreeEuler
public import GraphMinor.Wagner.ConnectivityReduction

/-!
# The planar part of Wagner's theorem

We show that an internally `4`-connected simple graph `K` with no `K_5` minor and no subdivision
of `K_{3,3}` is planar (`planar_of_noK33`). The tool is Graph Minors IX (2.4): a `3`-connected
society with no cross and no tripod is rural. We apply it to a society whose cyclic permutation
has three vertices, so it never has a cross (`planar_of_society`). There are three cases.

* `K` has a triangle `a b c` (`planar_of_triangle`). We use the society `(K, (a, b, c))`. A tripod
  gives a `K_5` minor by `hasK5_of_triangle_tripod`. This case does not use the hypothesis on
  `K_{3,3}`.
* `K` has a vertex `w` with exactly three neighbours `a`, `b`, `c` (`planar_of_deg3`). We use the
  society `(K, (a, w, b))`. A tripod gives a subdivision of `K_{3,3}` by `hasK33Subdiv_of_deg3`.
* Otherwise every vertex has at least four neighbours and `K` is `4`-connected. Take a vertex `v`
  of least degree and three of its neighbours `a`, `b`, `c`, and use the society
  `(K - v, (a, b, c))`. A tripod gives a subdivision of `K_{3,3}` with `v` as a branch vertex
  (`Tripod.thetaOuter`). So the society is rural and `K - v` is planar. Since `K - v` has no
  triangle, Euler's bound says it has at most `2 (N - 1) - 4` edges. But it has at least
  `δ (N - 2) / 2 ≥ 2 N - 4` edges, where `δ ≥ 4` is the least degree. So this case cannot occur.
-/

@[expose] public section

namespace GraphMinor.Wagner

open Set Function SimpleGraph

variable {γ : Type*} [Finite γ] {K : SimpleGraph γ}

/-- A society `(K restricted to R, L)` with three vertices in `L`, in which deleting two vertices of
`R` leaves a preconnected graph and which has no tripod, gives a plane embedding of `K` restricted
to `R`. -/
theorem planar_of_society {R : Set γ} {L : List γ} (hlen : L.length = 3) (hnd : L.Nodup)
    (hLR : ∀ x ∈ L, x ∈ R)
    (hpc : ∀ T : Set γ, T.ncard ≤ 2 → (K.induce {x | x ∈ R ∧ x ∉ T}).Preconnected)
    (htri : Tripod K R {x | x ∈ L} → False) :
    Nonempty (HP25.PlaneEmbedding (HP25.restrict K R) R) := by
  have hne : L ≠ [] := by
    intro h
    simp [h] at hlen
  have hconn := society_isKConnected_three (hnd := hnd) (hne := hne) (hLR := hLR)
    (noCut_of_preconnected (by omega) hnd hLR hpc)
  have hr := GM09.theorem_2_4_proof (society K R L hnd hne hLR) hconn (society_not_cross hlen)
    (fun ⟨_, _, _, hT⟩ => htri (exists_tripod hT).some)
  exact planeEmbedding_of_rural (by omega) hr

omit [Finite γ] in
/-- A plane embedding of `K` restricted to all vertices is a plane embedding of `K`. -/
theorem planar_of_restrict_univ (h : Nonempty (HP25.PlaneEmbedding (HP25.restrict K univ) univ)) :
    Nonempty (HP25.PlaneEmbedding K univ) := by
  obtain ⟨φ⟩ := h
  exact ⟨planeEmbeddingMono φ fun u _ v _ huv => ⟨huv, trivial, trivial⟩⟩

variable {N : ℕ} {K : SimpleGraph (Fin N)}

/-- In a `3`-connected graph, deleting at most two vertices leaves a preconnected graph. -/
theorem pc_of_three_conn (hi : Is3ConnectedFin K) (T : Set (Fin N)) (hT : T.ncard ≤ 2) :
    (K.induce {x | x ∈ (univ : Set (Fin N)) ∧ x ∉ T}).Preconnected := by
  classical
  have hc := hi.2 T.toFinite.toFinset (by rw [← ncard_eq_toFinset_card T]; exact hT)
  exact pc_congr (by ext; simp) hc.preconnected

/-- Internal `4`-connectivity at a cut of three vertices, in the form used by
`hasK5_of_triangle_tripod`. -/
theorem i4c_cut3 (hi : IsInternally4ConnFin K) (S : Set (Fin N)) (hS : S.ncard = 3) :
    (K.induce {y | y ∉ S}).Preconnected ∨
      ((∀ x ∈ S, ∀ y ∈ S, ¬ K.Adj x y) ∧
        ∃ x, x ∉ S ∧ (K.induce {y | y ∉ S ∧ y ≠ x}).Preconnected) := by
  classical
  have hF : S.toFinite.toFinset.card = 3 := by rw [← ncard_eq_toFinset_card S]; exact hS
  by_cases hc : (K.induce {x | x ∉ S.toFinite.toFinset}).Connected
  · exact Or.inl (pc_congr (by ext; simp) hc.preconnected)
  · obtain ⟨hind, u, huS, -, hconn⟩ := hi.2.2 _ hF hc
    refine Or.inr ⟨fun x hx y hy => hind x (by simpa using hx) y (by simpa using hy),
      u, by simpa using huS, pc_congr (by ext; simp) hconn.preconnected⟩

/-- **The triangle case.** An internally `4`-connected graph with no `K_5` minor and with a triangle
is planar. -/
theorem planar_of_triangle (hi : IsInternally4ConnFin K) (hK5 : ¬ HasK5MinorSimple K)
    {a b c : Fin N} (hab : K.Adj a b) (hbc : K.Adj b c) (hca : K.Adj c a) :
    Nonempty (HP25.PlaneEmbedding K univ) := by
  have hnd : [a, b, c].Nodup := by
    have h1 := K.ne_of_adj hab
    have h2 := K.ne_of_adj hbc
    have h3 := K.ne_of_adj hca
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨h1, h3.symm⟩, h2, not_false⟩
  refine planar_of_restrict_univ (planar_of_society (L := [a, b, c]) rfl hnd
    (fun x _ => mem_univ x) (pc_of_three_conn hi.2.1) fun T => hK5 ?_)
  have hΩ : ∀ i, T.t i = a ∨ T.t i = b ∨ T.t i = c := fun i => by
    have := T.ht i
    simpa using this
  refine hasK5_of_triangle_tripod T (fun i j hij => ?_) (i4c_cut3 hi _ ?_)
  · have hne : T.t i ≠ T.t j := T.t_inj.ne hij
    rcases hΩ i with hi' | hi' | hi' <;> rcases hΩ j with hj' | hj' | hj' <;>
      rw [hi', hj'] at hne ⊢ <;> first
        | exact absurd rfl hne
        | assumption
        | exact SimpleGraph.Adj.symm (by assumption)
  · rw [← image_univ, ncard_image_of_injective _ T.s_inj, ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin]

/-- **The degree-three case.** A `3`-connected graph with no subdivision of `K_{3,3}` and with a
vertex having exactly three neighbours is planar. -/
theorem planar_of_deg3 (hi : Is3ConnectedFin K) (hK33 : ¬ HasK33Subdiv K) {w a b c : Fin N}
    (hN : ∀ y, K.Adj w y ↔ y = a ∨ y = b ∨ y = c) (hab : a ≠ b) :
    Nonempty (HP25.PlaneEmbedding K univ) := by
  have hwa : K.Adj w a := (hN a).mpr (Or.inl rfl)
  have hwb : K.Adj w b := (hN b).mpr (Or.inr (Or.inl rfl))
  have hnd : [a, w, b].Nodup := by
    have h1 := K.ne_of_adj hwa
    have h2 := K.ne_of_adj hwb
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨h1.symm, hab⟩, h2, not_false⟩
  exact planar_of_restrict_univ (planar_of_society (L := [a, w, b]) rfl hnd
    (fun x _ => mem_univ x) (pc_of_three_conn hi) fun T => hK33 (hasK33Subdiv_of_deg3 hnd hN T))

end GraphMinor.Wagner
