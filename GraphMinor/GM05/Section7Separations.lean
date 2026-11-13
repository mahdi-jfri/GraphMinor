module

public import GraphMinor.GM05.Defs
import GraphMinor.GM05.Basic
import GraphMinor.GM05.Section3
import GraphMinor.GM05.Section5
import GraphMinor.GM05.Section6
import GraphMinor.GM01.Basic
import GraphMinor.Minor.Basic
import Mathlib.Data.Set.Card

/-!
# Graph Minors V, Section 7: Meshes and Tree-Width (Theorems 7.1 and 7.2)

This file formalizes the first part of Section 7 of Robertson and Seymour,
*Graph Minors. V. Excluding a Planar Graph*, J. Combin. Theory Ser. B 41 (1986), 92–114
(pages 106–108):

- `GraphMinor.GM05.theorem_7_1_simple`: Graph Minors V, (7.1), existence of a balanced vertex separation
  in any graph `G ∈ 𝓕_θ`.
- `GraphMinor.GM05.theorem_7_2_simple`: Graph Minors V, (7.2), existence of a separation of `G ∈ 𝓕_θ`
  that balances a specified subset `X ⊆ V(G)`.
-/

namespace GraphMinor.GM05

open SimpleGraph Graph GM01

public section

universe u

variable {V : Type u}

/-! ## Proof of Theorem (7.1) -/

/-- Graph Minors V, (7.1) (page 106):
"If $G\in \mathcal{F}_\theta$ then $G$ has a separation $(V_1, V_2)$ such that $|V_1\cap
V_2|\le \theta_7$ and $|V_1 - V_2|, |V_2 - V_1|\le (1 - \theta_8^{-1})|V(G)|$, where
$\theta_7, \theta_8$ are as defined in Section 2." -/
theorem theorem_7_1_simple
    {G : (⊤ : SimpleGraph V).Subgraph} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ) :
    ∃ V₁ V₂ : Set V, IsSeparation G V₁ V₂ ∧
      (V₁ ∩ V₂).ncard ≤ θ₇ θ ∧
      θ₈ θ * (V₁ \ V₂).ncard ≤ (θ₈ θ - 1) * G.verts.ncard ∧
      θ₈ θ * (V₂ \ V₁).ncard ≤ (θ₈ θ - 1) * G.verts.ncard := by
  classical
  have hk_pos : 0 < θ₅ θ := θ₅_pos hθ
  have h3_le_θ₈ : 3 ≤ θ₈ θ := three_le_θ₈ hθ heven
  have hθ₅_le_θ₇ : θ₅ θ ≤ θ₇ θ := θ₅_le_θ₇ hθ
  rcases theorem_6_4_simple hG_fin hk_pos with h64_i | h64_ii
  · -- Case where (6.4)(i) holds: there are `θ₅` disjoint connected subgraphs `A i` of `G`.
    obtain ⟨A, hA, hA_disj⟩ := h64_i
    have hA_size : ∀ i : Fin (θ₅ θ),
        θ₅ θ * G.verts.ncard ≤ θ₈ θ * (A i).verts.ncard := by
      intro i
      have hcard := (hA i).2.2
      have h4 := four_mul_θ₈ hθ heven
      have hmul := Nat.mul_le_mul_left (θ₅ θ) hcard
      have hlhs : θ₅ θ * (4 * G.verts.ncard) = 4 * (θ₅ θ * G.verts.ncard) :=
        Nat.mul_left_comm (θ₅ θ) 4 G.verts.ncard
      have hrhs : θ₅ θ * (3 * (3 ^ θ₅ θ - 1) * (A i).verts.ncard) =
          4 * (θ₈ θ * (A i).verts.ncard) := by
        calc θ₅ θ * (3 * (3 ^ θ₅ θ - 1) * (A i).verts.ncard)
            = (θ₅ θ * (3 * (3 ^ θ₅ θ - 1))) * (A i).verts.ncard :=
              (Nat.mul_assoc _ _ _).symm
          _ = (3 * θ₅ θ * (3 ^ θ₅ θ - 1)) * (A i).verts.ncard := by
              rw [← Nat.mul_assoc, Nat.mul_comm (θ₅ θ) 3]
          _ = (4 * θ₈ θ) * (A i).verts.ncard := by rw [← h4]
          _ = 4 * (θ₈ θ * (A i).verts.ncard) := Nat.mul_assoc 4 _ _
      rw [hlhs, hrhs] at hmul
      omega
    -- By (5.3), `G` has no `(θ₅, θ₆)`-mesh.
    have hno_mesh : ¬ HasMesh G (θ₅ θ) (θ₆ θ) :=
      theorem_5_3_simple hθ heven hG_fin hG
    let S : Fin (θ₅ θ) → Set V := fun i ↦ (A i).verts
    have hS_sub : ∀ i, S i ⊆ G.verts := fun i ↦ (hA i).1.1
    have hno_meeting : ¬ HasDisjointConnectedMeeting G S (θ₆ θ) := by
      rintro ⟨B, hB_le, hB_conn, hB_disj, hB_meet⟩
      refine hno_mesh ⟨A, B, ?_⟩
      exact {
        le_left := fun i ↦ (hA i).1
        le_right := hB_le
        connected_left := fun i ↦ (hA i).2.1
        connected_right := hB_conn
        disjoint_left := hA_disj
        disjoint_right := hB_disj
        meets := fun i j ↦ Set.inter_comm (B j).verts (A i).verts ▸ hB_meet i j
      }
    -- By (3.2), there exists `X ⊆ V(G)` with `|X| < α(θ₅, θ₆) = θ₇` meeting every connected
    -- subgraph of `G` that meets all `A i`.
    rcases theorem_3_2_simple hθ heven hG_fin hG (two_le_θ₅ hθ) S hS_sub with
      h_has | ⟨X, hX_sub, hX_lt, hX_meet⟩
    · exact absurd h_has hno_meeting
    · let i₀ : Fin (θ₅ θ) := ⟨0, hk_pos⟩
      -- For each `v ∈ V(A₁)`, `X` separates `{v}` from some `A_i`.
      have hex_sep : ∀ v ∈ (A i₀).verts, ∃ i : Fin (θ₅ θ),
          Separates G X {v} (A i).verts := by
        intro v hv
        by_cases hvX : v ∈ X
        · refine ⟨i₀, fun P hP ↦ Set.not_disjoint_iff.2 ⟨P.first, P.first_mem_verts, ?_⟩⟩
          have hfirst_eq : P.first = v := Set.mem_singleton_iff.1 hP.2.1
          exact hfirst_eq ▸ hvX
        · let H := G.deleteVerts X
          have hvG : v ∈ G.verts := (hA i₀).1.1 hv
          have hvH : v ∈ H.verts := ⟨hvG, hvX⟩
          let c_v := H.coe.connectedComponentMk ⟨v, hvH⟩
          let C_v := componentSubgraph H c_v
          have hCv_comp : IsComponentOf C_v H := isComponentOf_componentSubgraph H c_v
          have hv_Cv : v ∈ C_v.verts := ⟨⟨v, hvH⟩, rfl, rfl⟩
          have hCv_le_G : C_v ≤ G := hCv_comp.le.trans Subgraph.deleteVerts_le
          have hCv_not_X : ¬ (C_v.verts ∩ X).Nonempty := by
            rintro ⟨x, hxCv, hxX⟩
            exact (hCv_comp.le.1 hxCv).2 hxX
          have hnot_all : ¬ ∀ i : Fin (θ₅ θ), (C_v.verts ∩ S i).Nonempty :=
            fun hall ↦ hCv_not_X (hX_meet C_v hCv_le_G hCv_comp.connected hall)
          push Not at hnot_all
          obtain ⟨i, hi_empty⟩ := hnot_all
          refine ⟨i, fun P hP hP_avoid ↦ ?_⟩
          have hP_le_G : P.toSubgraph ≤ G := hP.1
          have hP_disj_X : Disjoint P.toSubgraph.verts X := hP_avoid
          have hP_verts_H : P.toSubgraph.verts ⊆ H.verts :=
            fun x hx ↦ ⟨hP_le_G.1 hx, Set.disjoint_left.1 hP_disj_X hx⟩
          have hP_le_H : P.toSubgraph ≤ H :=
            ⟨hP_verts_H, fun x y hadj ↦
              ⟨hP_verts_H hadj.fst_mem, hP_verts_H hadj.snd_mem, hP_le_G.2 hadj⟩⟩
          have hfirst_eq : P.first = v := Set.mem_singleton_iff.1 hP.2.1
          have hv_P : v ∈ P.toSubgraph.verts := hfirst_eq ▸ P.first_mem_verts
          have hP_le_Cv : P.toSubgraph ≤ C_v := by
            have hle := le_componentSubgraph_of_preconnected hP_le_H
              P.connected_toSubgraph.preconnected hv_P
            exact hle
          have hlast_Cv : P.last ∈ C_v.verts := hP_le_Cv.1 P.last_mem_verts
          have hlast_Ai : P.last ∈ S i := hP.2.2
          exact Set.eq_empty_iff_forall_notMem.1 hi_empty P.last ⟨hlast_Cv, hlast_Ai⟩
      -- By pigeonhole, choose `i₁ : Fin (θ₅ θ)` and `V' ⊆ (A i₀).verts` with
      -- `(A i₀).verts.ncard ≤ θ₅ θ * V'.ncard`.
      let idx_of : V → Fin (θ₅ θ) := fun v ↦
        if hv : v ∈ (A i₀).verts then (hex_sep v hv).choose else i₀
      let fiber : Fin (θ₅ θ) → Set V := fun i ↦
        {v ∈ (A i₀).verts | idx_of v = i}
      have hfiber_sub : ∀ i, fiber i ⊆ (A i₀).verts := fun i _ hv ↦ hv.1
      have hfiber_disj : Pairwise (fun i j ↦ Disjoint (fiber i) (fiber j)) := by
        intro i j hij
        rw [Set.disjoint_left]
        intro v hvi hvj
        exact hij (hvi.2.symm.trans hvj.2)
      have hfiber_union : (⋃ i : Fin (θ₅ θ), fiber i) = (A i₀).verts := by
        ext v
        simp only [fiber, Set.mem_iUnion, Set.mem_sep_iff]
        exact ⟨fun ⟨_, hv, _⟩ ↦ hv, fun hv ↦ ⟨idx_of v, hv, rfl⟩⟩
      have hA₀_fin : (A i₀).verts.Finite := hG_fin.subset (hA i₀).1.1
      have hsum_fibers : ∀ T : Finset (Fin (θ₅ θ)),
          (⋃ i ∈ T, fiber i).ncard = ∑ i ∈ T, (fiber i).ncard := by
        intro T
        induction T using Finset.induction_on with
        | empty => simp
        | @insert a T ha ih =>
          rw [Finset.set_biUnion_insert, Finset.sum_insert ha, ← ih]
          have hdisj : Disjoint (fiber a) (⋃ i ∈ T, fiber i) := by
            rw [Set.disjoint_iUnion₂_right]
            intro i hiT
            exact hfiber_disj (fun h ↦ ha (h ▸ hiT))
          exact Set.ncard_union_eq hdisj (hA₀_fin.subset (hfiber_sub a))
            (hA₀_fin.subset (Set.iUnion₂_subset fun i _ ↦ hfiber_sub i))
      have htotal_fiber : ∑ i : Fin (θ₅ θ), (fiber i).ncard = (A i₀).verts.ncard := by
        have h := hsum_fibers Finset.univ
        simp only [Finset.mem_univ, Set.iUnion_true, hfiber_union] at h
        exact h.symm
      have hex_i₁ : ∃ i₁ : Fin (θ₅ θ), (A i₀).verts.ncard ≤ θ₅ θ * (fiber i₁).ncard := by
        by_contra! hall_lt
        have hsum_lt : ∑ i : Fin (θ₅ θ), θ₅ θ * (fiber i).ncard <
            ∑ _i : Fin (θ₅ θ), (A i₀).verts.ncard := by
          refine Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 ⟨i₀⟩) ?_
          intro i _
          exact hall_lt i
        rw [← Finset.mul_sum, htotal_fiber, Finset.sum_const, Finset.card_fin, smul_eq_mul]
          at hsum_lt
        exact lt_irrefl _ hsum_lt
      obtain ⟨i₁, hi₁_card⟩ := hex_i₁
      let V' := fiber i₁
      have hV'_sub : V' ⊆ G.verts := (hfiber_sub i₁).trans (hA i₀).1.1
      have hV'_size : G.verts.ncard ≤ θ₈ θ * V'.ncard := by
        have h1 : θ₅ θ * G.verts.ncard ≤ θ₈ θ * (A i₀).verts.ncard := hA_size i₀
        have h2 : θ₈ θ * (A i₀).verts.ncard ≤ θ₅ θ * (θ₈ θ * V'.ncard) := by
          calc θ₈ θ * (A i₀).verts.ncard
              ≤ θ₈ θ * (θ₅ θ * V'.ncard) := Nat.mul_le_mul_left (θ₈ θ) hi₁_card
            _ = θ₅ θ * (θ₈ θ * V'.ncard) := Nat.mul_left_comm (θ₈ θ) (θ₅ θ) V'.ncard
        have h3 : θ₅ θ * G.verts.ncard ≤ θ₅ θ * (θ₈ θ * V'.ncard) := h1.trans h2
        exact Nat.le_of_mul_le_mul_left h3 hk_pos
      have hAi₁_size : G.verts.ncard ≤ θ₈ θ * (A i₁).verts.ncard := by
        have h1 : θ₅ θ * G.verts.ncard ≤ θ₈ θ * (A i₁).verts.ncard := hA_size i₁
        have h2 : G.verts.ncard ≤ θ₅ θ * G.verts.ncard := by
          calc G.verts.ncard = 1 * G.verts.ncard := (one_mul _).symm
            _ ≤ θ₅ θ * G.verts.ncard := Nat.mul_le_mul_right _ hk_pos
        exact h2.trans h1
      have hsep_V' : Separates G X V' (A i₁).verts := by
        intro P hP
        have hfirst_V' : P.first ∈ V' := hP.2.1
        have hfirst_A₀ : P.first ∈ (A i₀).verts := hfirst_V'.1
        have hidx : idx_of P.first = i₁ := hfirst_V'.2
        have hsep_first : Separates G X {P.first} (A i₁).verts := by
          have h := (hex_sep P.first hfirst_A₀).choose_spec
          have heq : (hex_sep P.first hfirst_A₀).choose = i₁ := by
            dsimp [idx_of] at hidx
            simp only [hfirst_A₀, ↓reduceDIte] at hidx
            exact hidx
          rwa [heq] at h
        exact hsep_first P ⟨hP.1, Set.mem_singleton P.first, hP.2.2⟩
      obtain ⟨V₁, V₂, hsep, hinter_X, hV'_V₁, hAi₁_V₂⟩ :=
        exists_isSeparation_of_separates hX_sub hV'_sub (hA i₁).1.1 hsep_V'
      refine ⟨V₁, V₂, hsep, ?_, ?_, ?_⟩
      · rw [hinter_X]
        unfold θ₇
        omega
      · have hsub : V₁ \ V₂ ⊆ G.verts \ (A i₁).verts :=
          fun x ⟨hxV₁, hx_notV₂⟩ ↦ ⟨hsep.subset_left hxV₁, fun hxA ↦ hx_notV₂ (hAi₁_V₂ hxA)⟩
        have hle_diff : (V₁ \ V₂).ncard ≤ G.verts.ncard - (A i₁).verts.ncard := by
          rw [← Set.ncard_sdiff' (hA i₁).1.1 hG_fin]
          exact Set.ncard_le_ncard hsub (hG_fin.subset Set.sdiff_subset)
        have hAi₁_le_G : (A i₁).verts.ncard ≤ G.verts.ncard :=
          Set.ncard_le_ncard (hA i₁).1.1 hG_fin
        calc θ₈ θ * (V₁ \ V₂).ncard
            ≤ θ₈ θ * (G.verts.ncard - (A i₁).verts.ncard) := Nat.mul_le_mul_left _ hle_diff
          _ = θ₈ θ * G.verts.ncard - θ₈ θ * (A i₁).verts.ncard := Nat.mul_sub _ _ _
          _ ≤ θ₈ θ * G.verts.ncard - G.verts.ncard := Nat.sub_le_sub_left hAi₁_size _
          _ = (θ₈ θ - 1) * G.verts.ncard := by
            rw [Nat.sub_mul, one_mul]
      · have hsub : V₂ \ V₁ ⊆ G.verts \ V' :=
          fun x ⟨hxV₂, hx_notV₁⟩ ↦ ⟨hsep.subset_right hxV₂, fun hxV' ↦ hx_notV₁ (hV'_V₁ hxV')⟩
        have hle_diff : (V₂ \ V₁).ncard ≤ G.verts.ncard - V'.ncard := by
          rw [← Set.ncard_sdiff' hV'_sub hG_fin]
          exact Set.ncard_le_ncard hsub (hG_fin.subset Set.sdiff_subset)
        have hV'_le_G : V'.ncard ≤ G.verts.ncard :=
          Set.ncard_le_ncard hV'_sub hG_fin
        calc θ₈ θ * (V₂ \ V₁).ncard
            ≤ θ₈ θ * (G.verts.ncard - V'.ncard) := Nat.mul_le_mul_left _ hle_diff
          _ = θ₈ θ * G.verts.ncard - θ₈ θ * V'.ncard := Nat.mul_sub _ _ _
          _ ≤ θ₈ θ * G.verts.ncard - G.verts.ncard := Nat.sub_le_sub_left hV'_size _
          _ = (θ₈ θ - 1) * G.verts.ncard := by
            rw [Nat.sub_mul, one_mul]
  · -- Case where (6.4)(ii) holds: `|V₁ ∩ V₂| < θ₅ ≤ θ₇` and `3 |V_i \ V_j| ≤ 2 |V(G)|`.
    obtain ⟨V₁, V₂, hsep, hinter_lt, h1, h2⟩ := h64_ii
    refine ⟨V₁, V₂, hsep, by omega, ?_, ?_⟩
    · have hmul : 3 * (θ₈ θ * (V₁ \ V₂).ncard) ≤ 3 * ((θ₈ θ - 1) * G.verts.ncard) := by
        calc 3 * (θ₈ θ * (V₁ \ V₂).ncard)
            = θ₈ θ * (3 * (V₁ \ V₂).ncard) := Nat.mul_left_comm 3 (θ₈ θ) _
          _ ≤ θ₈ θ * (2 * G.verts.ncard) := Nat.mul_le_mul_left (θ₈ θ) h1
          _ = (θ₈ θ * 2) * G.verts.ncard := (Nat.mul_assoc _ _ _).symm
          _ ≤ (3 * (θ₈ θ - 1)) * G.verts.ncard :=
            Nat.mul_le_mul_right _ (by omega)
          _ = 3 * ((θ₈ θ - 1) * G.verts.ncard) := Nat.mul_assoc 3 _ _
      omega
    · have hmul : 3 * (θ₈ θ * (V₂ \ V₁).ncard) ≤ 3 * ((θ₈ θ - 1) * G.verts.ncard) := by
        calc 3 * (θ₈ θ * (V₂ \ V₁).ncard)
            = θ₈ θ * (3 * (V₂ \ V₁).ncard) := Nat.mul_left_comm 3 (θ₈ θ) _
          _ ≤ θ₈ θ * (2 * G.verts.ncard) := Nat.mul_le_mul_left (θ₈ θ) h2
          _ = (θ₈ θ * 2) * G.verts.ncard := (Nat.mul_assoc _ _ _).symm
          _ ≤ (3 * (θ₈ θ - 1)) * G.verts.ncard :=
            Nat.mul_le_mul_right _ (by omega)
          _ = 3 * ((θ₈ θ - 1) * G.verts.ncard) := Nat.mul_assoc 3 _ _
      omega

/-! ## Leaf-Blowup Graph for Theorem (7.2) -/

/-- The graph `G'` in the proof of Theorem (7.2) (page 107), obtained from `G` by attaching `N` new
degree-1 vertices `Sum.inr (v, j)` (`j : Fin N`) adjacent only to `Sum.inl v` for each `v ∈ X`. -/
private def blowupGraph (G : (⊤ : SimpleGraph V).Subgraph) (X : Set V) (N : ℕ) :
    (⊤ : SimpleGraph (V ⊕ (V × Fin N))).Subgraph where
  verts := (Sum.inl '' G.verts) ∪ (Sum.inr '' ((X ∩ G.verts) ×ˢ (Set.univ : Set (Fin N))))
  Adj w₁ w₂ :=
    match w₁, w₂ with
    | Sum.inl u₁, Sum.inl u₂ => G.Adj u₁ u₂
    | Sum.inl v, Sum.inr (v', _) => v = v' ∧ v ∈ X ∩ G.verts
    | Sum.inr (v', _), Sum.inl v => v = v' ∧ v ∈ X ∩ G.verts
    | Sum.inr _, Sum.inr _ => False
  adj_sub {w₁ w₂} h := by
    intro heq
    subst heq
    cases w₁ with
    | inl u => exact G.loopless.irrefl u h
    | inr p => exact h
  edge_vert {w₁ w₂} h := by
    cases w₁ with
    | inl u₁ =>
      cases w₂ with
      | inl _ => exact Or.inl ⟨u₁, h.fst_mem, rfl⟩
      | inr _ => exact Or.inl ⟨u₁, h.2.2, rfl⟩
    | inr p =>
      cases w₂ with
      | inl _ => exact Or.inr ⟨p, ⟨h.1 ▸ h.2, trivial⟩, rfl⟩
      | inr _ => exact False.elim h
  symm := ⟨fun {w₁ w₂} h ↦ by
    cases w₁ <;> cases w₂ <;> first | exact h.symm | exact h⟩

private def projV {N : ℕ} : V ⊕ (V × Fin N) → V
  | Sum.inl u => u
  | Sum.inr (v, _) => v

private lemma adj_blowupGraph_imp {G : (⊤ : SimpleGraph V).Subgraph} {X : Set V} {N : ℕ}
    {z₁ z₂ : V ⊕ (V × Fin N)} (h : (blowupGraph G X N).Adj z₁ z₂) :
    projV z₁ = projV z₂ ∨ G.Adj (projV z₁) (projV z₂) := by
  cases z₁ with
  | inl u₁ =>
    cases z₂ with
    | inl u₂ => exact Or.inr h
    | inr p => exact Or.inl h.1
  | inr p =>
    cases z₂ with
    | inl u₂ => exact Or.inl h.1.symm
    | inr q => exact False.elim h

private lemma grid_exists_two_neighbors {θ : ℕ} (hθ : 6 ≤ θ) (u : Fin θ × Fin θ) :
    ∃ q₁ q₂ : Fin θ × Fin θ, q₁ ≠ q₂ ∧
      (pathGraph θ □ pathGraph θ).Adj u q₁ ∧
      (pathGraph θ □ pathGraph θ).Adj u q₂ := by
  let a := u.1
  let b := u.2
  let a' : Fin θ := if a.1 = 0 then ⟨1, by omega⟩ else ⟨a.1 - 1, by omega⟩
  let b' : Fin θ := if b.1 = 0 then ⟨1, by omega⟩ else ⟨b.1 - 1, by omega⟩
  have ha : (pathGraph θ).Adj a a' := by
    rw [pathGraph_adj]
    dsimp [a']
    split_ifs with h0
    · left
      change a.1 + 1 = 1
      omega
    · right
      change a.1 - 1 + 1 = a.1
      omega
  have hb : (pathGraph θ).Adj b b' := by
    rw [pathGraph_adj]
    dsimp [b']
    split_ifs with h0
    · left
      change b.1 + 1 = 1
      omega
    · right
      change b.1 - 1 + 1 = b.1
      omega
  have ha_ne : a ≠ a' := ha.ne
  refine ⟨(a', b), (a, b'), ?_, Or.inl ⟨ha, rfl⟩, Or.inr ⟨hb, rfl⟩⟩
  intro heq
  exact ha_ne (Prod.mk.inj heq).1.symm

private lemma blowupGraph_mem_𝓕 {G : (⊤ : SimpleGraph V).Subgraph} {X : Set V} {N θ : ℕ}
    (hθ : 6 ≤ θ) (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ) :
    blowupGraph G X N ∈ 𝓕 θ := by
  classical
  let G' := blowupGraph G X N
  have hG'_fin : G'.verts.Finite := by
    refine (hG_fin.image Sum.inl).union ?_
    exact ((hG_fin.subset Set.inter_subset_right).prod Set.finite_univ).image Sum.inr
  intro hminor'
  apply hG
  -- Extract a minor model of `gridGraph θ` in `toGraph G'`.
  have hV_nonempty : Nonempty (Sym2 (V ⊕ (V × Fin N))) := by
    obtain ⟨G₁, _, C₁, _, ⟨φ⟩⟩ := hminor'
    have h0 : (⟨0, by omega⟩, ⟨0, by omega⟩) ∈ V(gridGraph θ) := trivial
    let S₀ := φ.vertexEquiv ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), h0⟩
    obtain ⟨w₀, _, _⟩ := S₀.2
    exact ⟨s(w₀, w₀)⟩
  obtain ⟨ηv, ηe, hm⟩ :=
    @exists_isMinorModel_of_isIsoMinor _ _ _ _ hV_nonempty (gridGraph θ) (toGraph G')
      hG'_fin (finite_edgeSet_of_finite_verts hG'_fin) hminor'
  let S : Fin θ × Fin θ → Set V := fun u ↦ {x ∈ G.verts | Sum.inl x ∈ ηv u}
  -- Helper: any edge of `gridGraph θ` yields an edge of `G'` between the branch sets.
  have hmodel_adj : ∀ {u q : Fin θ × Fin θ},
      (pathGraph θ □ pathGraph θ).Adj u q →
      ∃ x ∈ ηv u, ∃ y ∈ ηv q, G'.Adj x y := by
    intro u q hadj
    have he_mem : s(u, q) ∈ E(gridGraph θ) := hadj
    have hinc_u : (gridGraph θ).Inc s(u, q) u := ⟨q, rfl, hadj⟩
    have hinc_q : (gridGraph θ).Inc s(u, q) q := ⟨u, Sym2.eq_swap, hadj⟩
    obtain ⟨x, hx_u, hinc_x⟩ := (hm.inc_iff u trivial s(u, q) he_mem).1 hinc_u
    obtain ⟨y, hl_xy⟩ := hinc_x
    have hy_q : y ∈ ηv q := by
      obtain ⟨x', hx'_q, hinc_x'⟩ := (hm.inc_iff q trivial s(u, q) he_mem).1 hinc_q
      have hne_uq : u ≠ q := hadj.ne
      have hxx' : x ≠ x' :=
        (hm.vertex_disjoint u trivial q trivial hne_uq).ne_of_mem hx_u hx'_q
      have hx'y : x' = y := hinc_x'.eq_of_isLink_of_ne_left hl_xy hxx'.symm
      exact hx'y ▸ hx'_q
    exact ⟨x, hx_u, y, hy_q, hl_xy.2⟩
  -- Key property: if `z ∈ ηv u`, then `projV z ∈ S u` (in particular, if a leaf is in `ηv u`,
  -- its unique neighbor `Sum.inl v` is also in `ηv u`).
  have hproj_mem : ∀ (u : Fin θ × Fin θ) {z : V ⊕ (V × Fin N)},
      z ∈ ηv u → projV z ∈ S u := by
    intro u z hz
    have hz_verts : z ∈ G'.verts := hm.vertex_subset u trivial hz
    cases z with
    | inl x =>
      rcases hz_verts with ⟨x', hx'G, heq⟩ | ⟨p, _, heq⟩
      · cases heq
        exact ⟨hx'G, hz⟩
      · cases heq
    | inr p =>
      rcases hz_verts with ⟨x', _, heq⟩ | ⟨p', ⟨hp'X, _⟩, heq⟩
      · cases heq
      · cases heq
        refine ⟨hp'X.2, ?_⟩
        -- Show `ηv u` cannot be `{Sum.inr p}` because `u` has two distinct neighbors in `gridGraph θ`.
        have hnot_sub_single : ¬ (ηv u ⊆ {Sum.inr p}) := by
          intro hsub
          obtain ⟨q₁, q₂, hq₁₂, hadj₁, hadj₂⟩ := grid_exists_two_neighbors hθ u
          obtain ⟨x₁, hx₁, y₁, hy₁, hxy₁⟩ := hmodel_adj hadj₁
          obtain ⟨x₂, hx₂, y₂, hy₂, hxy₂⟩ := hmodel_adj hadj₂
          rw [Set.mem_singleton_iff.1 (hsub hx₁)] at hxy₁
          rw [Set.mem_singleton_iff.1 (hsub hx₂)] at hxy₂
          have hy₁_eq : y₁ = Sum.inl p.1 := by
            cases y₁ with
            | inl v => exact congrArg Sum.inl hxy₁.1
            | inr _ => exact False.elim hxy₁
          have hy₂_eq : y₂ = Sum.inl p.1 := by
            cases y₂ with
            | inl v => exact congrArg Sum.inl hxy₂.1
            | inr _ => exact False.elim hxy₂
          rw [hy₁_eq] at hy₁
          rw [hy₂_eq] at hy₂
          exact (hm.vertex_disjoint q₁ trivial q₂ trivial hq₁₂).notMem_of_mem_left hy₁ hy₂
        obtain ⟨w, hw_u, hw_ne⟩ := Set.not_subset.1 hnot_sub_single
        rw [Set.mem_singleton_iff] at hw_ne
        obtain ⟨K', hK'_le, hK'_V, hK'_conn⟩ := hm.connected u trivial
        have hrt := hK'_conn.2 w (hK'_V.symm ▸ hw_u) (Sum.inr p) (hK'_V.symm ▸ hz)
        cases hrt with
        | refl => exact absurd rfl hw_ne
        | @tail b _ _ hadj_K' =>
          have hb_u : b ∈ ηv u := hK'_V ▸ hadj_K'.left_mem
          obtain ⟨e, hl_K'⟩ := hadj_K'
          have hl_G' : (toGraph G').IsLink e b (Sum.inr p) :=
            (hl_K'.mono (hK'_le.trans deleteEdges_le))
          have hadj_G' : G'.Adj b (Sum.inr p) := hl_G'.2
          have hb_eq : b = Sum.inl p.1 := by
            cases b with
            | inl v => exact congrArg Sum.inl hadj_G'.1
            | inr _ => exact False.elim hadj_G'
          exact hb_eq ▸ hb_u
  -- Now construct the connected subgraphs `K u = G.induce (S u)` in `G`.
  let K : Fin θ × Fin θ → (⊤ : SimpleGraph V).Subgraph := fun u ↦ G.induce (S u)
  have hS_disj : Pairwise fun u₁ u₂ ↦ Disjoint (S u₁) (S u₂) := by
    intro u₁ u₂ hne
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    exact (hm.vertex_disjoint u₁ trivial u₂ trivial hne).notMem_of_mem_left hx₁.2 hx₂.2
  refine isIsoMinor_ofSimpleGraph_of_connected_subgraphs (pathGraph θ □ pathGraph θ) hG_fin K
    (fun u ↦ ⟨fun _ hx ↦ hx.1, fun _ _ h ↦ h.2.2⟩) ?_ hS_disj ?_
  · intro u
    obtain ⟨z₀, hz₀⟩ := hm.vertex_nonempty u trivial
    rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
    refine ⟨⟨projV z₀, hproj_mem u hz₀⟩, fun {x y} hx hy ↦ ?_⟩
    obtain ⟨K', hK'_le, hK'_V, hK'_conn⟩ := hm.connected u trivial
    have hrt := hK'_conn.2 (Sum.inl x) (hK'_V.symm ▸ hx.2) (Sum.inl y) (hK'_V.symm ▸ hy.2)
    have hwalk : ∀ {z₁ z₂ : V ⊕ (V × Fin N)},
        Relation.ReflTransGen K'.Adj z₁ z₂ → z₁ ∈ ηv u → z₂ ∈ ηv u →
        ∃ p : (⊤ : SimpleGraph V).Walk (projV z₁) (projV z₂), p.toSubgraph ≤ K u := by
      intro z₁ z₂ h
      induction h with
      | refl =>
        intro hz₁ _
        exact ⟨.nil, by simp [K, hproj_mem u hz₁]⟩
      | @tail a b _ hadj_K' ih =>
        intro hz₁ hb
        have ha : a ∈ ηv u := hK'_V ▸ hadj_K'.left_mem
        obtain ⟨p, hp⟩ := ih hz₁ ha
        obtain ⟨e, hl_K'⟩ := hadj_K'
        have hl_G' : (toGraph G').IsLink e a b := hl_K'.mono (hK'_le.trans deleteEdges_le)
        rcases adj_blowupGraph_imp hl_G'.2 with heq | hadj_G
        · have hsub_copy : ∀ {w₁ w₂ : V} (hw : w₁ = w₂)
              (q : (⊤ : SimpleGraph V).Walk (projV z₁) w₁),
              (q.copy rfl hw).toSubgraph = q.toSubgraph := by
            rintro _ _ rfl q
            rfl
          exact ⟨p.copy rfl heq, by rw [hsub_copy heq p]; exact hp⟩
        · have hadj_Ku : (K u).Adj (projV a) (projV b) :=
            ⟨hproj_mem u ha, hproj_mem u hb, hadj_G⟩
          refine ⟨p.append (.cons hadj_Ku.adj_sub .nil), ?_⟩
          rw [Walk.toSubgraph_append, Walk.toSubgraph_cons_nil_eq_subgraphOfAdj]
          exact sup_le hp (subgraphOfAdj_le_of_adj (K u) hadj_Ku)
    exact hwalk hrt hx.2 hy.2
  · intro u₁ u₂ hadj
    obtain ⟨z₁, hz₁, z₂, hz₂, hadj_G'⟩ := hmodel_adj hadj
    have hp₁ : projV z₁ ∈ S u₁ := hproj_mem u₁ hz₁
    have hp₂ : projV z₂ ∈ S u₂ := hproj_mem u₂ hz₂
    rcases adj_blowupGraph_imp hadj_G' with heq | hadj_G
    · exfalso
      exact Set.disjoint_left.1 (hS_disj hadj.ne) hp₁ (heq ▸ hp₂)
    · exact ⟨projV z₁, hp₁, projV z₂, hp₂, hadj_G⟩

/-! ## Proof of Theorem (7.2) -/

private lemma ncard_prod_univ_fin {S : Set V} (hS : S.Finite) (N : ℕ) :
    (S ×ˢ (Set.univ : Set (Fin N))).ncard = N * S.ncard := by
  classical
  have hprod_eq : S ×ˢ (Set.univ : Set (Fin N)) =
      (((hS.toFinset ×ˢ (Finset.univ : Finset (Fin N))) : Finset (V × Fin N)) : Set (V × Fin N)) := by
    ext ⟨v, j⟩
    simp
  rw [hprod_eq, Set.ncard_coe_finset, Finset.card_product, Finset.card_fin,
    ← Set.ncard_eq_toFinset_card S hS, Nat.mul_comm]

private lemma blowup_sdiff_inter_bound {G : (⊤ : SimpleGraph V).Subgraph} {X : Set V} {N θ : ℕ}
    (hG_fin : G.verts.Finite) (hX : X ⊆ G.verts)
    (hN : N = (θ₈ θ - 1) * G.verts.ncard + θ₈ θ * θ₇ θ + 1)
    {A' B' : Set (V ⊕ (V × Fin N))}
    (hsep' : IsSeparation (blowupGraph G X N) A' B')
    (hinter' : (A' ∩ B').ncard ≤ θ₇ θ)
    (hdiff' : θ₈ θ * (A' \ B').ncard ≤ (θ₈ θ - 1) * (blowupGraph G X N).verts.ncard)
    (hG'_fin : (blowupGraph G X N).verts.Finite)
    (hG'_ncard : (blowupGraph G X N).verts.ncard = G.verts.ncard + N * X.ncard) :
    θ₈ θ * (((Sum.inl ⁻¹' A') \ (Sum.inl ⁻¹' B')) ∩ X).ncard ≤ (θ₈ θ - 1) * X.ncard := by
  let G' := blowupGraph G X N
  let S := ((Sum.inl ⁻¹' A') \ (Sum.inl ⁻¹' B')) ∩ X
  have hS_fin : S.Finite := hG_fin.subset (Set.inter_subset_right.trans hX)
  have hsub_A' : Sum.inr '' (S ×ˢ (Set.univ : Set (Fin N))) ⊆ A' := by
    rintro _ ⟨⟨v, j⟩, ⟨⟨⟨hvA, hv_notB⟩, hvX⟩, _⟩, rfl⟩
    have hvG : v ∈ G.verts := hX hvX
    have hj_mem : Sum.inr (v, j) ∈ G'.verts :=
      Or.inr ⟨(v, j), ⟨⟨hvX, hvG⟩, trivial⟩, rfl⟩
    rw [← hsep'.union_eq] at hj_mem
    rcases hj_mem with hjA | hjB
    · exact hjA
    · by_contra hj_notA
      have hadj : G'.Adj (Sum.inl v) (Sum.inr (v, j)) := ⟨rfl, hvX, hvG⟩
      exact hsep'.not_adj ⟨hvA, hv_notB⟩ ⟨hjB, hj_notA⟩ hadj
  have hA'_fin : A'.Finite := hG'_fin.subset hsep'.subset_left
  have hN_mul_S : N * S.ncard ≤ A'.ncard := by
    have hle := Set.ncard_le_ncard hsub_A' hA'_fin
    rw [Set.ncard_image_of_injective _ Sum.inr_injective, ncard_prod_univ_fin hS_fin N] at hle
    exact hle
  have hA'_le : A'.ncard ≤ (A' \ B').ncard + θ₇ θ := by
    have hunion : (A' \ B') ∪ (A' ∩ B') = A' := Set.sdiff_union_inter A' B'
    have hle := Set.ncard_union_le (A' \ B') (A' ∩ B')
    rw [hunion] at hle
    omega
  have hmul : N * (θ₈ θ * S.ncard) < N * ((θ₈ θ - 1) * X.ncard + 1) := by
    calc N * (θ₈ θ * S.ncard)
        = θ₈ θ * (N * S.ncard) := Nat.mul_left_comm N (θ₈ θ) S.ncard
      _ ≤ θ₈ θ * A'.ncard := Nat.mul_le_mul_left (θ₈ θ) hN_mul_S
      _ ≤ θ₈ θ * ((A' \ B').ncard + θ₇ θ) := Nat.mul_le_mul_left (θ₈ θ) hA'_le
      _ = θ₈ θ * (A' \ B').ncard + θ₈ θ * θ₇ θ := Nat.mul_add _ _ _
      _ ≤ (θ₈ θ - 1) * G'.verts.ncard + θ₈ θ * θ₇ θ := Nat.add_le_add_right hdiff' _
      _ = (θ₈ θ - 1) * (G.verts.ncard + N * X.ncard) + θ₈ θ * θ₇ θ := by rw [hG'_ncard]
      _ = N * ((θ₈ θ - 1) * X.ncard) + ((θ₈ θ - 1) * G.verts.ncard + θ₈ θ * θ₇ θ) := by
          rw [Nat.mul_add, Nat.mul_left_comm (θ₈ θ - 1) N X.ncard,
            Nat.add_comm ((θ₈ θ - 1) * G.verts.ncard), Nat.add_assoc]
      _ < N * ((θ₈ θ - 1) * X.ncard) + N := by omega
      _ = N * ((θ₈ θ - 1) * X.ncard + 1) := by rw [Nat.mul_add, mul_one]
  have hlt := Nat.lt_of_mul_lt_mul_left hmul
  change θ₈ θ * S.ncard ≤ (θ₈ θ - 1) * X.ncard
  omega

/-- Graph Minors V, (7.2) (page 107):
"If $G\in \mathcal{F}_\theta$ and $X\subseteq V(G)$ then $G$ has a separation $(V_1, V_2)$
such that $|V_1\cap V_2|\le \theta_7$ and $|(V_1 - V_2)\cap X|, |(V_2 - V_1)\cap X|\le (1 -
\theta_8^{-1})|X|$." -/
theorem theorem_7_2_simple
    {G : (⊤ : SimpleGraph V).Subgraph} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    {X : Set V} (hX : X ⊆ G.verts) :
    ∃ V₁ V₂ : Set V, IsSeparation G V₁ V₂ ∧
      (V₁ ∩ V₂).ncard ≤ θ₇ θ ∧
      θ₈ θ * ((V₁ \ V₂) ∩ X).ncard ≤ (θ₈ θ - 1) * X.ncard ∧
      θ₈ θ * ((V₂ \ V₁) ∩ X).ncard ≤ (θ₈ θ - 1) * X.ncard := by
  classical
  let N : ℕ := (θ₈ θ - 1) * G.verts.ncard + θ₈ θ * θ₇ θ + 1
  let G' := blowupGraph G X N
  have hX_inter : X ∩ G.verts = X := Set.inter_eq_self_of_subset_left hX
  have hX_fin : X.Finite := hG_fin.subset hX
  have hG'_verts : G'.verts = (Sum.inl '' G.verts) ∪ (Sum.inr '' (X ×ˢ (Set.univ : Set (Fin N)))) := by
    simp [G', blowupGraph, hX_inter]
  have hG'_fin : G'.verts.Finite := by
    rw [hG'_verts]
    exact (hG_fin.image Sum.inl).union ((hX_fin.prod Set.finite_univ).image Sum.inr)
  have hG'_ncard : G'.verts.ncard = G.verts.ncard + N * X.ncard := by
    rw [hG'_verts]
    have hdisj : Disjoint (Sum.inl '' G.verts) (Sum.inr '' (X ×ˢ (Set.univ : Set (Fin N)))) := by
      rw [Set.disjoint_left]
      rintro _ ⟨_, _, rfl⟩ ⟨_, _, heq⟩
      cases heq
    rw [Set.ncard_union_eq hdisj (hG_fin.image Sum.inl) ((hX_fin.prod Set.finite_univ).image Sum.inr),
      Set.ncard_image_of_injective G.verts Sum.inl_injective,
      Set.ncard_image_of_injective _ Sum.inr_injective,
      ncard_prod_univ_fin hX_fin N]
  have hG'_mem : G' ∈ 𝓕 θ := blowupGraph_mem_𝓕 hθ hG_fin hG
  obtain ⟨V₁', V₂', hsep', hinter_le', hdiff₁', hdiff₂'⟩ :=
    theorem_7_1_simple hθ heven hG'_fin hG'_mem
  let V₁ : Set V := Sum.inl ⁻¹' V₁'
  let V₂ : Set V := Sum.inl ⁻¹' V₂'
  have hV₁_sub : V₁ ⊆ G.verts := by
    intro x hx
    have hx' := hsep'.subset_left hx
    rw [hG'_verts] at hx'
    rcases hx' with ⟨x', hx'G, heq⟩ | ⟨_, _, heq⟩
    · cases heq; exact hx'G
    · cases heq
  have hV₂_sub : V₂ ⊆ G.verts := by
    intro x hx
    have hx' := hsep'.subset_right hx
    rw [hG'_verts] at hx'
    rcases hx' with ⟨x', hx'G, heq⟩ | ⟨_, _, heq⟩
    · cases heq; exact hx'G
    · cases heq
  have hsep : IsSeparation G V₁ V₂ := {
    subset_left := hV₁_sub
    subset_right := hV₂_sub
    union_eq := by
      ext x
      simp only [V₁, V₂, Set.mem_union, Set.mem_preimage]
      refine ⟨fun h ↦ h.elim (fun hx₁ ↦ hV₁_sub hx₁) (fun hx₂ ↦ hV₂_sub hx₂), fun hxG ↦ ?_⟩
      have hx' : Sum.inl x ∈ V₁' ∪ V₂' := by
        rw [hsep'.union_eq, hG'_verts]
        exact Or.inl ⟨x, hxG, rfl⟩
      exact hx'
    not_adj := fun _ _ hu hv hadjG ↦
      hsep'.not_adj hu hv hadjG
  }
  have hinter_le : (V₁ ∩ V₂).ncard ≤ θ₇ θ := by
    have hsub_inter : Sum.inl '' (V₁ ∩ V₂) ⊆ V₁' ∩ V₂' := by
      rintro _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
      exact ⟨hx₁, hx₂⟩
    have hle := Set.ncard_le_ncard hsub_inter
      ((hG'_fin.subset hsep'.subset_left).subset Set.inter_subset_left)
    rw [Set.ncard_image_of_injective _ Sum.inl_injective] at hle
    exact hle.trans hinter_le'
  refine ⟨V₁, V₂, hsep, hinter_le,
    blowup_sdiff_inter_bound hG_fin hX rfl hsep' hinter_le' hdiff₁' hG'_fin hG'_ncard,
    blowup_sdiff_inter_bound hG_fin hX rfl hsep'.symm (Set.inter_comm V₁' V₂' ▸ hinter_le')
      hdiff₂' hG'_fin hG'_ncard⟩

end

end GraphMinor.GM05
