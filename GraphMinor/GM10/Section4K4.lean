module

public import GraphMinor.GM10.Section4Minors
public import GraphMinor.Minor.Basic

/-!
# Graph Minors X, Section 4: `K₄`-Minors and Branch-Width `≤ 2`

This file proves the forward direction of part **(iii)** of **(4.2)** of
Robertson and Seymour, *Graph Minors. X. Obstructions to Tree-Decomposition*,
J. Combin. Theory Ser. B **52** (1991), 153–190 (page 165):

It transfers branch-width through isomorphisms and applies (4.1) and the
branch-width of the complete graph on four vertices.
-/

@[expose] public section

namespace GraphMinor.GM10

open Graph SimpleGraph Hypergraph Relation

universe u v

variable {α : Type u} {β : Type v} {α' β' : Type*} {ι : Type*}

/-! ## The complete graph `K_n` as a `Graph` -/

/-- The complete graph `K_n` on `Fin n` with edge type `Sym2 (Fin n)`, matching the hypergraph
`completeGraph n` from `GraphMinor/GM10/Defs.lean`
(Graph Minors X, Section 4, (4.2)(iii) and (4.4), pages 165–166). -/
def completeGraphGraph (n : ℕ) : Graph (Fin n) (Sym2 (Fin n)) where
  vertexSet := Set.univ
  edgeSet := {e : Sym2 (Fin n) | ¬ e.IsDiag}
  IsLink e x y := x ≠ y ∧ e = s(x, y)
  isLink_symm _ _ := ⟨fun _ _ ⟨hne, he⟩ ↦ ⟨hne.symm, he.trans Sym2.eq_swap⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h1 h2 := by
    have heq : s(_, _) = s(_, _) := h1.2.symm.trans h2.2
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  edge_mem_iff_exists_isLink e := by
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Set.mem_ofPred_eq, Sym2.mk_isDiag_iff]
      refine ⟨fun hne ↦ ⟨x, y, hne, rfl⟩, ?_⟩
      rintro ⟨a, b, hab, heq⟩
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · exact hab.symm
  left_mem_of_isLink _ _ _ _ := Set.mem_univ _

/-- `Hypergraph.ofGraph (completeGraphGraph n)` is equal to `completeGraph n`. -/
theorem ofGraph_completeGraphGraph (n : ℕ)
    (hV : V(completeGraphGraph n).Finite := Set.finite_univ)
    (hE : E(completeGraphGraph n).Finite := Set.toFinite _) :
    Hypergraph.ofGraph (completeGraphGraph n) hV hE = completeGraph n := by
  refine Hypergraph.ext rfl rfl ?_
  funext e x
  apply propext
  change (completeGraphGraph n).Inc e x ↔ ¬ e.IsDiag ∧ x ∈ e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [Graph.Inc, completeGraphGraph, Sym2.mk_isDiag_iff, Sym2.mem_iff]
    constructor
    · rintro ⟨y, hne, heq⟩
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hne, Or.inl rfl⟩
      · exact ⟨Ne.symm hne, Or.inr rfl⟩
    · rintro ⟨hne, rfl | rfl⟩
      · exact ⟨b, hne, rfl⟩
      · exact ⟨a, Ne.symm hne, Sym2.eq_swap⟩

/-- By (4.4), `completeGraphGraph 4` has branch-width `3`. -/
theorem branchWidth_completeGraphGraph_four
    (hV : V(completeGraphGraph 4).Finite := Set.finite_univ)
    (hE : E(completeGraphGraph 4).Finite := Set.toFinite _) :
    branchWidth (Hypergraph.ofGraph (completeGraphGraph 4) hV hE) = 3 := by
  rw [ofGraph_completeGraphGraph 4 hV hE, (theorem_4_4_proof 4).2 (by omega)]

/-! ## Isomorphism invariance of `branchWidth` and the "only if" direction of (4.2)(iii) -/

/-- A graph isomorphism `φ : Iso H G` preserves incidence. -/
theorem iso_inc_iff {H : Graph α' β'} {G : Graph α β} (φ : Iso H G)
    (e : E(H)) (x : V(H)) :
    H.Inc e.1 x.1 ↔ G.Inc (φ.edgeEquiv e).1 (φ.vertexEquiv x).1 := by
  constructor
  · rintro ⟨y, hxy⟩
    have hy : y ∈ V(H) := hxy.right_mem
    exact ⟨(φ.vertexEquiv ⟨y, hy⟩).1, (φ.isLink_iff e x ⟨y, hy⟩).1 hxy⟩
  · rintro ⟨y, hxy⟩
    have hy : y ∈ V(G) := hxy.right_mem
    obtain ⟨y₀, hy₀⟩ := φ.vertexEquiv.surjective ⟨y, hy⟩
    have hy_eq : y = (φ.vertexEquiv y₀).1 := congrArg Subtype.val hy₀.symm
    rw [hy_eq] at hxy
    exact ⟨y₀.1, (φ.isLink_iff e x y₀).2 hxy⟩

/-- If `φ : Iso H G` is a graph isomorphism, then `branchWidth` of `H` is at least `branchWidth`
of `G`. -/
theorem iso_branchWidth_le {H : Graph α' β'} {G : Graph α β} (φ : Iso H G)
    (hVH : V(H).Finite) (hEH : E(H).Finite) (hVG : V(G).Finite) (hEG : E(G).Finite) :
    branchWidth (Hypergraph.ofGraph G hVG hEG) ≤
      branchWidth (Hypergraph.ofGraph H hVH hEH) := by
  classical
  let H_hyp := Hypergraph.ofGraph H hVH hEH
  let G_hyp := Hypergraph.ofGraph G hVG hEG
  change branchWidth G_hyp ≤ branchWidth H_hyp
  by_cases hcardH : 2 ≤ H_hyp.edgeSet.ncard
  · have hneH : E(H).Nonempty := by
      by_contra! hemp
      have : H_hyp.edgeSet = ∅ := hemp
      rw [this, Set.ncard_empty] at hcardH
      omega
    obtain ⟨e₀, he₀⟩ := hneH
    have hγH : 1 ≤ maxEdgeSize H_hyp := one_le_maxEdgeSize_ofGraph ⟨e₀, he₀⟩
    obtain ⟨ι, _, T, τ, hbd, hw_eq⟩ := exists_branchDecomposition_eq_branchWidth hγH hcardH
    let e₀G : β := (φ.edgeEquiv ⟨e₀, he₀⟩).1
    let τG (t : ι) : β :=
      if ht : τ t ∈ E(H) then (φ.edgeEquiv ⟨τ t, ht⟩).1 else e₀G
    have hτG_leaf : ∀ {t : ι} (ht : t ∈ leafSet T),
        τG t = (φ.edgeEquiv ⟨τ t, hbd.bijOn.mapsTo ht⟩).1 := by
      intro t ht
      have hmem : τ t ∈ E(H) := hbd.bijOn.mapsTo ht
      simp [τG, hmem]
    have hbdG : IsBranchDecomposition G_hyp T τG := by
      refine ⟨hbd.isTernaryTree, ⟨?_, ?_, ?_⟩⟩
      · intro t ht
        rw [hτG_leaf ht]
        exact (φ.edgeEquiv ⟨τ t, hbd.bijOn.mapsTo ht⟩).2
      · intro t₁ ht₁ t₂ ht₂ heq
        rw [hτG_leaf ht₁, hτG_leaf ht₂] at heq
        have heq_sub : (⟨τ t₁, hbd.bijOn.mapsTo ht₁⟩ : E(H)) = ⟨τ t₂, hbd.bijOn.mapsTo ht₂⟩ :=
          φ.edgeEquiv.injective (Subtype.ext heq)
        exact hbd.bijOn.injOn ht₁ ht₂ (congrArg Subtype.val heq_sub)
      · intro e heG
        obtain ⟨eH, heH_eq⟩ := φ.edgeEquiv.surjective ⟨e, heG⟩
        obtain ⟨t, ht, hτt⟩ := hbd.bijOn.surjOn eH.2
        refine ⟨t, ht, ?_⟩
        rw [hτG_leaf ht]
        have hsub : (⟨τ t, hbd.bijOn.mapsTo ht⟩ : E(H)) = eH := Subtype.ext hτt
        rw [hsub]
        exact congrArg Subtype.val heH_eq
    have hord_le : ∀ e ∈ T.edgeSet, branchEdgeOrder G_hyp T τG e ≤ branchEdgeOrder H_hyp T τ e := by
      intro e _
      let SH : Set α' := {v ∈ H_hyp.vertexSet | ∃ t₁ ∈ leafSet T, ∃ t₂ ∈ leafSet T,
        ¬ (T.deleteEdges {e}).Reachable t₁ t₂ ∧ H_hyp.Inc (τ t₁) v ∧ H_hyp.Inc (τ t₂) v}
      let SG : Set α := {v ∈ G_hyp.vertexSet | ∃ t₁ ∈ leafSet T, ∃ t₂ ∈ leafSet T,
        ¬ (T.deleteEdges {e}).Reachable t₁ t₂ ∧ G_hyp.Inc (τG t₁) v ∧ G_hyp.Inc (τG t₂) v}
      let f (v : α') : α := if hv : v ∈ V(H) then (φ.vertexEquiv ⟨v, hv⟩).1 else
        (φ.vertexEquiv ⟨(exists_isLink_of_mem_edgeSet he₀).choose,
          (exists_isLink_of_mem_edgeSet he₀).choose_spec.choose_spec.left_mem⟩).1
      have hSG_sub : SG ⊆ f '' SH := by
        rintro v ⟨hvG, t₁, ht₁, t₂, ht₂, hnr, hinc₁, hinc₂⟩
        obtain ⟨vH, hvH_eq⟩ := φ.vertexEquiv.surjective ⟨v, hvG⟩
        have hv_eq : v = (φ.vertexEquiv vH).1 := congrArg Subtype.val hvH_eq.symm
        refine ⟨vH.1, ⟨vH.2, t₁, ht₁, t₂, ht₂, hnr, ?_, ?_⟩, ?_⟩
        · rw [hτG_leaf ht₁, hv_eq] at hinc₁
          exact (iso_inc_iff φ ⟨τ t₁, hbd.bijOn.mapsTo ht₁⟩ vH).2 hinc₁
        · rw [hτG_leaf ht₂, hv_eq] at hinc₂
          exact (iso_inc_iff φ ⟨τ t₂, hbd.bijOn.mapsTo ht₂⟩ vH).2 hinc₂
        · simp [f, vH.2, hv_eq]
      exact (Set.ncard_le_ncard hSG_sub ((H_hyp.vertexSet_finite.subset fun _ h ↦ h.1).image f)).trans
        (Set.ncard_image_le (H_hyp.vertexSet_finite.subset fun _ h ↦ h.1))
    have hwG : branchDecompWidth G_hyp T τG ≤ branchWidth H_hyp := by
      rw [← hw_eq, branchDecompWidth_le_iff]
      intro e he
      exact (hord_le e he).trans (branchEdgeOrder_le_branchDecompWidth he)
    have hmem : branchDecompWidth G_hyp T τG ∈
        {w : ℕ | ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → β),
          IsBranchDecomposition G_hyp T τ ∧ branchDecompWidth G_hyp T τ = w} :=
      ⟨ι, inferInstance, T, τG, hbdG, rfl⟩
    exact (Nat.sInf_le hmem).trans hwG
  · have hle1 : H_hyp.edgeSet.ncard ≤ 1 := by omega
    have hcardG_le1 : G_hyp.edgeSet.ncard ≤ 1 := by
      rw [Set.ncard_le_one_iff G_hyp.edgeSet_finite]
      intro e₁ e₂ he₁ he₂
      obtain ⟨e₁H, he₁_eq⟩ := φ.edgeEquiv.surjective ⟨e₁, he₁⟩
      obtain ⟨e₂H, he₂_eq⟩ := φ.edgeEquiv.surjective ⟨e₂, he₂⟩
      have heqH : e₁H.1 = e₂H.1 :=
        (Set.ncard_le_one_iff H_hyp.edgeSet_finite).1 hle1 e₁H.2 e₂H.2
      have hsub : e₁H = e₂H := Subtype.ext heqH
      have hval := congrArg (fun x ↦ (φ.edgeEquiv x).1) hsub
      simpa [he₁_eq, he₂_eq] using hval
    rw [branchWidth_eq_zero_of_ncard_edgeSet_le_one hcardG_le1]
    exact Nat.zero_le _

/-- Isomorphic finite graphs have equal `branchWidth`. -/
theorem iso_branchWidth_eq {H : Graph α' β'} {G : Graph α β} (φ : Iso H G)
    (hVH : V(H).Finite) (hEH : E(H).Finite) (hVG : V(G).Finite) (hEG : E(G).Finite) :
    branchWidth (Hypergraph.ofGraph H hVH hEH) =
      branchWidth (Hypergraph.ofGraph G hVG hEG) :=
  le_antisymm (iso_branchWidth_le φ.symm hVG hEG hVH hEH) (iso_branchWidth_le φ hVH hEH hVG hEG)

/-- The "only if" direction of **Graph Minors X, (4.2)(iii)** (page 165):
If `branchWidth (Hypergraph.ofGraph G hV hE) ≤ 2`, then `G` has no `K₄` minor. -/
theorem not_isIsoMinor_completeGraphGraph_four_of_branchWidth_le_two
    {G : Graph α β} (hV : V(G).Finite) (hE : E(G).Finite)
    (hbw : branchWidth (Hypergraph.ofGraph G hV hE) ≤ 2) :
    ¬ IsIsoMinor (completeGraphGraph 4) G := by
  rintro ⟨G', hG', C, hC, ⟨φ⟩⟩
  have hVG' : V(G').Finite := hV.subset hG'.vertexSet_mono
  have hEG' : E(G').Finite := hE.subset hG'.edgeSet_mono
  have hVH : V(contract G' C).Finite := by
    have : V(contract G' C) = contractComp G' C '' V(G') := by simp [contract, contractComp]
    rw [this]
    exact hVG'.image _
  have hEH : E(contract G' C).Finite := by
    have : E(contract G' C) = E(G') \ C := by simp [contract]
    rw [this]
    exact hEG'.subset Set.sdiff_subset
  have hminor : IsMinor (contract G' C) G := ⟨G', hG', C, hC, rfl⟩
  have hle1 := theorem_4_1_proof hV hE hVH hEH hminor
  have heq := iso_branchWidth_eq φ Set.finite_univ (Set.toFinite _) hVH hEH
  have h3 := branchWidth_completeGraphGraph_four
  omega

end GraphMinor.GM10
