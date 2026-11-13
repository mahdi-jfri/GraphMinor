module

public import GraphMinor.Wagner.PlanarPart

/-!
# Internally 4-connected graphs with no `K_5` minor and no subdivision of `K_{3,3}` are planar

This file finishes the planar part of Wagner's theorem (`planar_of_noK33`). After the triangle case
and the degree-three case of `PlanarPart.lean`, every vertex has at least four neighbours and
there is no triangle. We show this cannot happen: the society `(K - v, (a, b, c))` for a vertex `v`
of least degree would be rural, and then `K - v` would be a plane graph with no triangle and too
many edges.
-/

@[expose] public section

namespace GraphMinor.Wagner

open Set Function SimpleGraph Finset

variable {N : ℕ} {K : SimpleGraph (Fin N)}

/-- The edges of `K` with both ends different from `v` are the edges of `K` not at `v`. -/
theorem edgesOn_restrict_ne [DecidableRel K.Adj] (v : Fin N) :
    Crossing.edgesOn (HP25.restrict K {x | x ≠ v}) {x | x ≠ v} =
      ((K.edgeFinset \ K.incidenceFinset v : Finset (Sym2 (Fin N))) : Set (Sym2 (Fin N))) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    rw [Crossing.mem_edgesOn_iff]
    simp only [HP25.restrict, mem_ofPred_eq, coe_sdiff, Set.mem_sdiff, coe_edgeFinset,
      mem_edgeSet, mem_coe, mem_incidenceFinset, incidenceSet, Sym2.mem_iff, not_and]
    constructor
    · rintro ⟨hx, hy, hxy, -, -⟩
      exact ⟨hxy, fun _ h => h.elim (fun h => hx h.symm) (fun h => hy h.symm)⟩
    · rintro ⟨hxy, h⟩
      have hx : x ≠ v := fun e => h hxy (Or.inl e.symm)
      have hy : y ≠ v := fun e => h hxy (Or.inr e.symm)
      exact ⟨hx, hy, hxy, hx, hy⟩

/-- **The planar part of Wagner's theorem.** An internally `4`-connected graph with no `K_5` minor
and no subdivision of `K_{3,3}` is planar. -/
theorem planar_of_noK33 (hi : IsInternally4ConnFin K) (hK5 : ¬ HasK5MinorSimple K)
    (hK33 : ¬ HasK33Subdiv K) : Nonempty (HP25.PlaneEmbedding K Set.univ) := by
  classical
  by_cases htri : ∃ a b c, K.Adj a b ∧ K.Adj b c ∧ K.Adj c a
  · obtain ⟨a, b, c, hab, hbc, hca⟩ := htri
    exact planar_of_triangle hi hK5 hab hbc hca
  by_cases hdeg3 : ∃ w, K.degree w = 3
  · obtain ⟨w, hw⟩ := hdeg3
    rw [← card_neighborFinset_eq_degree] at hw
    obtain ⟨a, b, c, hab, -, -, hS⟩ := card_eq_three.mp hw
    refine planar_of_deg3 hi.2.1 hK33 (w := w) (c := c) (fun y => ?_) hab
    rw [← mem_neighborFinset, hS]
    simp
  exfalso
  have hN6 : 6 ≤ N := hi.1
  -- Every vertex has at least three neighbours, by `3`-connectivity.
  have hdeg_ge3 : ∀ x, 3 ≤ K.degree x := by
    intro x
    by_contra hlt
    rw [← card_neighborFinset_eq_degree] at hlt
    have hc := hi.2.1.2 (K.neighborFinset x) (by omega)
    have hlt' : (insert x (K.neighborFinset x)).card < (univ : Finset (Fin N)).card := by
      rw [card_univ, Fintype.card_fin]
      have := card_insert_le x (K.neighborFinset x)
      omega
    obtain ⟨y, -, hy⟩ := exists_mem_notMem_of_card_lt_card hlt'
    rw [Finset.mem_insert, not_or] at hy
    obtain ⟨a, ha, b, hbW, hb, hab⟩ := exists_adj_out hc.preconnected (D := {x})
      (fun z hz => by
        rw [mem_singleton_iff] at hz
        subst hz
        exact fun h => (K.loopless.irrefl z) ((mem_neighborFinset _ _ _).mp h))
      (Set.mem_singleton x) (y := y) hy.2 (fun h => hy.1 h)
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact hbW ((mem_neighborFinset _ _ _).mpr hab)
  have hdeg4 : ∀ x, 4 ≤ K.degree x := fun x => by
    have := hdeg_ge3 x
    have : K.degree x ≠ 3 := fun h => hdeg3 ⟨x, h⟩
    omega
  -- `K` is `4`-connected.
  have h4c : ∀ S : Finset (Fin N), S.card ≤ 3 → (K.induce {x | x ∉ S}).Connected := by
    intro S hS
    rcases Nat.lt_or_ge S.card 3 with h | h
    · exact hi.2.1.2 S (by omega)
    · by_contra hc
      obtain ⟨-, u, -, hadj, -⟩ := hi.2.2 S (by omega) hc
      have : K.neighborFinset u = S := by
        ext y
        rw [mem_neighborFinset]
        exact hadj y
      have h3 : K.degree u = 3 := by rw [← card_neighborFinset_eq_degree, this]; omega
      exact hdeg3 ⟨u, h3⟩
  -- A vertex `v` of least degree and three of its neighbours.
  have : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  obtain ⟨v, hv⟩ := K.exists_minimal_degree_vertex
  have hvmin : ∀ x, K.degree v ≤ K.degree x := fun x => hv ▸ K.minDegree_le_degree x
  obtain ⟨S3, hS3, hS3c⟩ := exists_subset_card_eq (s := K.neighborFinset v) (n := 3)
    (by rw [card_neighborFinset_eq_degree]; have := hdeg4 v; omega)
  obtain ⟨a, b, c, hab, hac, hbc, hS3eq⟩ := card_eq_three.mp hS3c
  have hva : K.Adj v a := (mem_neighborFinset _ _ _).mp (hS3 (by simp [hS3eq]))
  have hvb : K.Adj v b := (mem_neighborFinset _ _ _).mp (hS3 (by simp [hS3eq]))
  have hvc : K.Adj v c := (mem_neighborFinset _ _ _).mp (hS3 (by simp [hS3eq]))
  set R : Set (Fin N) := {x | x ≠ v} with hR
  have hnd : [a, b, c].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨hab, hac⟩, hbc, not_false⟩
  have hLR : ∀ x ∈ [a, b, c], x ∈ R := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact (K.ne_of_adj hva).symm
    · exact (K.ne_of_adj hvb).symm
    · exact (K.ne_of_adj hvc).symm
  have hpc : ∀ T : Set (Fin N), T.ncard ≤ 2 → (K.induce {x | x ∈ R ∧ x ∉ T}).Preconnected := by
    intro T hT
    have hc := h4c (insert v T.toFinite.toFinset) (by
      have := card_insert_le v T.toFinite.toFinset
      rw [← ncard_eq_toFinset_card T] at this
      omega)
    exact pc_congr (by ext; simp [hR]) hc.preconnected
  have htri' : Tripod K R {x | x ∈ [a, b, c]} → False := by
    intro T
    refine hK33 (T.thetaOuter (z := v) (by simp [hR]) (fun i => ?_)).hasK33Subdiv
    have := T.ht i
    simp only [List.mem_cons, List.not_mem_nil, or_false, mem_ofPred_eq] at this
    rcases this with h | h | h <;> rw [h] <;> assumption
  obtain ⟨φ⟩ := planar_of_society rfl hnd hLR hpc htri'
  -- Euler's bound for `K - v`, which has no triangle.
  have hRcard : R.ncard = N - 1 := by
    have : R = Set.univ \ {v} := by ext; simp [hR]
    rw [this, ncard_sdiff_singleton_of_mem (Set.mem_univ v), Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hEuler := triangleFree_edgesOn_ncard_le φ (fun x _ y _ z _ hxy hyz hzx =>
    htri ⟨x, y, z, hxy.1, hyz.1, hzx.1⟩) (by omega)
  rw [hRcard, edgesOn_restrict_ne v, ncard_coe_finset, card_sdiff_of_subset
    (K.incidenceFinset_subset v), card_incidenceFinset_eq_degree] at hEuler
  have hmd : K.degree v ≤ #K.edgeFinset := by
    rw [← card_incidenceFinset_eq_degree]
    exact card_le_card (K.incidenceFinset_subset v)
  have hsum : N * K.degree v ≤ 2 * #K.edgeFinset := by
    rw [← sum_degrees_eq_twice_card_edges]
    calc N * K.degree v = ∑ _x : Fin N, K.degree v := by simp
      _ ≤ ∑ x : Fin N, K.degree x := sum_le_sum fun x _ => hvmin x
  have hd4 := hdeg4 v
  have hprod : 4 * N + 2 * K.degree v ≤ N * K.degree v + 8 := by nlinarith
  omega

end GraphMinor.Wagner
