module

public import GraphMinor.GM05.Defs
public import GraphMinor.GM05.Section6Bipolar
public import GraphMinor.GM05.Section6Weight
public import GraphMinor.GM05.Section6Subgraphs
import GraphMinor.GM05.Basic
import Mathlib.Data.Set.Card

/-!
# Graph Minors V, Section 6: Finding Connected Subgraphs (Theorem 6.4)

This file completes Section 6 of Robertson and Seymour, *Graph Minors. V. Excluding a Planar Graph*,
J. Combin. Theory Ser. B 41 (1986), 92–114 (page 106), by proving Theorem (6.4), which extends
Theorem (6.3) from connected graphs to arbitrary finite graphs.

## Main results

- `GraphMinor.GM05.exists_isSeparation_of_components_le`: if `X ⊆ V(G)` is such that every
  component of `G \ X` has at most `2 |V(G)| / 3` vertices, then there is a separation `(V₁, V₂)`
  of `G` with `V₁ ∩ V₂ = X` and `|V₁ \ V₂|, |V₂ \ V₁| ≤ 2 |V(G)| / 3`.
- `GraphMinor.GM05.theorem_6_4_simple`: Graph Minors V, (6.4).
-/

namespace GraphMinor.GM05

open SimpleGraph

public section

universe u

variable {V : Type u}

/-- Condition (i) of Theorem (6.4) (page 106): there are `k` disjoint connected subgraphs of `G`,
each with at least `4(3^k - 1)⁻¹ |V(G)| / 3` vertices (written without division as
`4 * G.verts.ncard ≤ 3 * (3 ^ k - 1) * (A i).verts.ncard`). -/
@[expose]
def Cond64_i (G : (⊤ : SimpleGraph V).Subgraph) (k : ℕ) : Prop :=
  ∃ A : Fin k → (⊤ : SimpleGraph V).Subgraph,
    (∀ i, A i ≤ G ∧ (A i).Connected ∧
      4 * G.verts.ncard ≤ 3 * (3 ^ k - 1) * (A i).verts.ncard) ∧
    Pairwise (fun i j ↦ Disjoint (A i).verts (A j).verts)

/-- Condition (ii) of Theorem (6.4) (page 106): there is a separation `(V₁, V₂)` of `G` such that
`|V₁ ∩ V₂| < k` and `|V₁ \ V₂|, |V₂ \ V₁| ≤ 2 |V(G)| / 3` (written without division as
`3 * (V₁ \ V₂).ncard ≤ 2 * G.verts.ncard` and `3 * (V₂ \ V₁).ncard ≤ 2 * G.verts.ncard`). -/
@[expose]
def Cond64_ii (G : (⊤ : SimpleGraph V).Subgraph) (k : ℕ) : Prop :=
  ∃ V₁ V₂ : Set V, IsSeparation G V₁ V₂ ∧
    (V₁ ∩ V₂).ncard < k ∧
    3 * (V₁ \ V₂).ncard ≤ 2 * G.verts.ncard ∧
    3 * (V₂ \ V₁).ncard ≤ 2 * G.verts.ncard

/-! ## Grouping Components into a Balanced Separation -/

private lemma isSeparation_component_verts {H C : (⊤ : SimpleGraph V).Subgraph}
    (hC : IsComponentOf C H) :
    IsSeparation H C.verts (H.verts \ C.verts) where
  subset_left := hC.le.1
  subset_right := Set.sdiff_subset
  union_eq := Set.union_sdiff_cancel hC.le.1
  not_adj u v hu hv hadj := by
    obtain ⟨c, rfl⟩ := isComponentOf_iff_exists_connectedComponent.1 hC
    obtain ⟨⟨u', hu'⟩, hu'_c, rfl⟩ := hu.1
    have hvH : v ∈ H.verts := hv.1.1
    have hadj_coe : H.coe.Adj ⟨u', hu'⟩ ⟨v, hvH⟩ := hadj
    have hv_c : H.coe.connectedComponentMk ⟨v, hvH⟩ = c := by
      rw [← hu'_c]
      exact ConnectedComponent.eq.2 ⟨.cons hadj_coe.symm .nil⟩
    exact hv.1.2 ⟨⟨v, hvH⟩, hv_c, rfl⟩

private lemma isSeparation_union_component {H C : (⊤ : SimpleGraph V).Subgraph} {A : Set V}
    (hA : IsSeparation H A (H.verts \ A)) (hC : IsComponentOf C H) :
    IsSeparation H (A ∪ C.verts) (H.verts \ (A ∪ C.verts)) where
  subset_left := Set.union_subset hA.subset_left hC.le.1
  subset_right := Set.sdiff_subset
  union_eq := Set.union_sdiff_cancel (Set.union_subset hA.subset_left hC.le.1)
  not_adj u v hu hv hadj := by
    have hv_notA : v ∉ A := fun h ↦ hv.1.2 (Set.mem_union_left _ h)
    have hv_notC : v ∉ C.verts := fun h ↦ hv.1.2 (Set.mem_union_right _ h)
    rcases hu.1 with huA | huC
    · exact hA.not_adj ⟨huA, fun h ↦ h.2 huA⟩ ⟨⟨hv.1.1, hv_notA⟩, hv_notA⟩ hadj
    · exact (isSeparation_component_verts hC).not_adj
        ⟨huC, fun h ↦ h.2 huC⟩ ⟨⟨hv.1.1, hv_notC⟩, hv_notC⟩ hadj

private lemma isSeparation_add_separator {G : (⊤ : SimpleGraph V).Subgraph} {X A : Set V}
    (hX : X ⊆ G.verts) (hA : IsSeparation (G.deleteVerts X) A ((G.deleteVerts X).verts \ A)) :
    IsSeparation G (A ∪ X) (((G.deleteVerts X).verts \ A) ∪ X) ∧
    (A ∪ X) ∩ (((G.deleteVerts X).verts \ A) ∪ X) = X ∧
    (A ∪ X) \ (((G.deleteVerts X).verts \ A) ∪ X) = A ∧
    (((G.deleteVerts X).verts \ A) ∪ X) \ (A ∪ X) = (G.deleteVerts X).verts \ A := by
  let H := G.deleteVerts X
  have hAH : A ⊆ H.verts := hA.subset_left
  have hA_disj_X : Disjoint A X :=
    Set.disjoint_left.2 fun x hxA hxX ↦ (hAH hxA).2 hxX
  have hdiff_disj_X : Disjoint (H.verts \ A) X :=
    Set.disjoint_left.2 fun x hx hxX ↦ hx.1.2 hxX
  have h_inter : (A ∪ X) ∩ ((H.verts \ A) ∪ X) = X := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff]
    refine ⟨?_, fun hx ↦ ⟨Or.inr hx, Or.inr hx⟩⟩
    rintro ⟨hxA | hxX, ⟨_, hx_notA⟩ | hxX⟩
    · exact absurd hxA hx_notA
    · exact hxX
    · exact hxX
    · exact hxX
  have h_sdiff₁ : (A ∪ X) \ ((H.verts \ A) ∪ X) = A := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_union, not_or, not_and, Classical.not_not]
    refine ⟨?_, fun hxA ↦ ⟨Or.inl hxA, fun _ ↦ hxA, Set.disjoint_left.1 hA_disj_X hxA⟩⟩
    rintro ⟨hxA | hxX, _, hx_notX⟩
    · exact hxA
    · exact absurd hxX hx_notX
  have h_sdiff₂ : ((H.verts \ A) ∪ X) \ (A ∪ X) = H.verts \ A := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_union, not_or]
    refine ⟨?_, fun ⟨hxH, hx_notA⟩ ↦ ⟨Or.inl ⟨hxH, hx_notA⟩, hx_notA, hxH.2⟩⟩
    rintro ⟨⟨hxH, hx_notA⟩ | hxX, _, hx_notX⟩
    · exact ⟨hxH, hx_notA⟩
    · exact absurd hxX hx_notX
  refine ⟨?_, h_inter, h_sdiff₁, h_sdiff₂⟩
  refine {
    subset_left := Set.union_subset (hAH.trans Subgraph.deleteVerts_le.1) hX
    subset_right := Set.union_subset (Set.sdiff_subset.trans Subgraph.deleteVerts_le.1) hX
    union_eq := by
      ext x
      simp only [Subgraph.deleteVerts_verts, Set.mem_union, Set.mem_sdiff]
      refine ⟨?_, fun hxG ↦ ?_⟩
      · rintro ((hxA | hxX) | (⟨⟨hxG, _⟩, _⟩ | hxX))
        · exact (hAH hxA).1
        · exact hX hxX
        · exact hxG
        · exact hX hxX
      · by_cases hxX : x ∈ X
        · exact Or.inl (Or.inr hxX)
        · by_cases hxA : x ∈ A
          · exact Or.inl (Or.inl hxA)
          · exact Or.inr (Or.inl ⟨⟨hxG, hxX⟩, hxA⟩)
    not_adj := by
      intro u v hu hv hadjG
      rw [h_sdiff₁] at hu
      rw [h_sdiff₂] at hv
      have huH : u ∈ H.verts := hAH hu
      have hvH : v ∈ H.verts := hv.1
      have hadjH : H.Adj u v := ⟨huH, hvH, hadjG⟩
      exact hA.not_adj ⟨hu, fun h ↦ h.2 hu⟩ ⟨hv, hv.2⟩ hadjH
  }

/-- If `X ⊆ V(G)` and every component of `G \ X` has at most `2 |V(G)| / 3` vertices, then there is
a separation `(V₁, V₂)` of `G` with `V₁ ∩ V₂ = X` and `|V₁ \ V₂|, |V₂ \ V₁| ≤ 2 |V(G)| / 3`. -/
theorem exists_isSeparation_of_components_le {G : (⊤ : SimpleGraph V).Subgraph}
    (hG_fin : G.verts.Finite) {X : Set V} (hX : X ⊆ G.verts)
    (hcomp : ∀ C : (⊤ : SimpleGraph V).Subgraph,
      IsComponentOf C (G.deleteVerts X) → 3 * C.verts.ncard ≤ 2 * G.verts.ncard) :
    ∃ V₁ V₂ : Set V, IsSeparation G V₁ V₂ ∧
      V₁ ∩ V₂ = X ∧
      3 * (V₁ \ V₂).ncard ≤ 2 * G.verts.ncard ∧
      3 * (V₂ \ V₁).ncard ≤ 2 * G.verts.ncard := by
  classical
  let H := G.deleteVerts X
  let n := G.verts.ncard
  have hH_fin : H.verts.Finite := hG_fin.subset Subgraph.deleteVerts_le.1
  have hH_le_n : H.verts.ncard ≤ n := Set.ncard_le_ncard Subgraph.deleteVerts_le.1 hG_fin
  -- Consider all clopen vertex sets `A ⊆ H.verts` with `3 * A.ncard ≤ 2 * n`.
  let P : ℕ → Prop := fun m ↦
    ∃ A : Set V, IsSeparation H A (H.verts \ A) ∧ 3 * A.ncard ≤ 2 * n ∧ A.ncard = m
  have hP0 : P 0 := by
    refine ⟨∅, ?_, by simp, Set.ncard_empty V⟩
    exact {
      subset_left := Set.empty_subset _
      subset_right := Set.sdiff_subset
      union_eq := by simp
      not_adj := fun _ _ hu ↦ absurd hu.1 (Set.notMem_empty _)
    }
  let m_max := Nat.findGreatest P n
  have hm_spec : P m_max := Nat.findGreatest_spec (Nat.zero_le n) hP0
  obtain ⟨A, hA_sep, hA_le, hA_card⟩ := hm_spec
  have hA_max : ∀ A' : Set V, IsSeparation H A' (H.verts \ A') → 3 * A'.ncard ≤ 2 * n →
      A'.ncard ≤ A.ncard := by
    intro A' hA'_sep hA'_le
    have hle_n : A'.ncard ≤ n :=
      (Set.ncard_le_ncard hA'_sep.subset_left hH_fin).trans hH_le_n
    rw [hA_card]
    exact Nat.le_findGreatest hle_n ⟨A', hA'_sep, hA'_le, rfl⟩
  -- Either `3 * (H.verts \ A).ncard ≤ 2 * n`, or we find a component `C` with `n ≤ 3 * C.verts.ncard`.
  by_cases hcompl_le : 3 * (H.verts \ A).ncard ≤ 2 * n
  · obtain ⟨hsep, hinter, hsdiff₁, hsdiff₂⟩ := isSeparation_add_separator hX hA_sep
    refine ⟨A ∪ X, (H.verts \ A) ∪ X, hsep, hinter, ?_, ?_⟩
    · rw [hsdiff₁]; exact hA_le
    · rw [hsdiff₂]; exact hcompl_le
  · push Not at hcompl_le
    have hcompl_ne : (H.verts \ A).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, Set.ncard_empty] at hcompl_le
      omega
    obtain ⟨v, hvH, hv_notA⟩ := hcompl_ne
    let c := H.coe.connectedComponentMk ⟨v, hvH⟩
    let C := componentSubgraph H c
    have hC_comp : IsComponentOf C H := isComponentOf_componentSubgraph H c
    have hvC : v ∈ C.verts := ⟨⟨v, hvH⟩, rfl, rfl⟩
    have hC_le_2n : 3 * C.verts.ncard ≤ 2 * n := hcomp C hC_comp
    have hC_ge_n : n ≤ 3 * C.verts.ncard := by
      by_contra! hC_lt_n
      have hC_sub_compl : C.verts ⊆ H.verts \ A := by
        have h := hA_sep.symm.verts_subset_diff_of_preconnected
          hC_comp.le hC_comp.connected.preconnected
          (by rw [Set.sdiff_inter_self]; exact disjoint_bot_right)
          ⟨v, hvC, hvH, hv_notA⟩
        simpa using h
      have hdisj_AC : Disjoint A C.verts :=
        Disjoint.mono_right hC_sub_compl disjoint_sdiff_self_right
      have hAC_sep : IsSeparation H (A ∪ C.verts) (H.verts \ (A ∪ C.verts)) :=
        isSeparation_union_component hA_sep hC_comp
      have hAC_card : (A ∪ C.verts).ncard = A.ncard + C.verts.ncard :=
        Set.ncard_union_eq hdisj_AC (hH_fin.subset hA_sep.subset_left) (hH_fin.subset hC_comp.le.1)
      have hA_plus_compl : A.ncard + (H.verts \ A).ncard = H.verts.ncard := by
        rw [← Set.ncard_union_eq disjoint_sdiff_self_right
          (hH_fin.subset hA_sep.subset_left) (hH_fin.subset Set.sdiff_subset),
          Set.union_sdiff_cancel hA_sep.subset_left]
      have h3A_lt_n : 3 * A.ncard < n := by omega
      have h3AC_le : 3 * (A ∪ C.verts).ncard ≤ 2 * n := by omega
      have hC_pos : 0 < C.verts.ncard :=
        (Set.ncard_pos (hH_fin.subset hC_comp.le.1)).2 ⟨v, hvC⟩
      have hle_max := hA_max (A ∪ C.verts) hAC_sep h3AC_le
      omega
    -- Since `n ≤ 3 * C.verts.ncard ≤ 2 * n`, taking `C.verts` itself gives the desired separation.
    have hC_sep : IsSeparation H C.verts (H.verts \ C.verts) :=
      isSeparation_component_verts hC_comp
    obtain ⟨hsep, hinter, hsdiff₁, hsdiff₂⟩ := isSeparation_add_separator hX hC_sep
    refine ⟨C.verts ∪ X, (H.verts \ C.verts) ∪ X, hsep, hinter, ?_, ?_⟩
    · rw [hsdiff₁]; exact hC_le_2n
    · rw [hsdiff₂, Set.ncard_sdiff' hC_comp.le.1 hH_fin]
      omega

/-! ## Proof of Theorem (6.4) -/

/-- Graph Minors V, (6.4) (page 106):
"Let $G$ be a graph and let $k>0$ be an integer. Then at least one of the following holds:*
(i) *there are $k$ disjoint connected subgraphs of $G$, each with at least
$4(3^k-1)^{-1}|V(G)|/3$ vertices;* (ii) *there is a separation $(V_1, V_2)$ of $G$ such that
$|V_1\cap V_2|<k$ and $|V_1 - V_2|, |V_2 - V_1|\le 2|V(G)|/3$." -/
theorem theorem_6_4_simple {G : (⊤ : SimpleGraph V).Subgraph} (hG_fin : G.verts.Finite)
    {k : ℕ} (hk_pos : 0 < k) :
    Cond64_i G k ∨ Cond64_ii G k := by
  classical
  by_cases hall_le : ∀ G₁ : (⊤ : SimpleGraph V).Subgraph,
      IsComponentOf G₁ G → 3 * G₁.verts.ncard ≤ 2 * G.verts.ncard
  · right
    have hcomp_empty : ∀ C : (⊤ : SimpleGraph V).Subgraph,
        IsComponentOf C (G.deleteVerts ∅) → 3 * C.verts.ncard ≤ 2 * G.verts.ncard := by
      intro C hC
      rw [Subgraph.deleteVerts_empty] at hC
      exact hall_le C hC
    obtain ⟨V₁, V₂, hsep, hinter, h1, h2⟩ :=
      exists_isSeparation_of_components_le hG_fin (Set.empty_subset G.verts) hcomp_empty
    refine ⟨V₁, V₂, hsep, ?_, h1, h2⟩
    rw [hinter, Set.ncard_empty]
    exact hk_pos
  · push Not at hall_le
    obtain ⟨G₁, hG₁_comp, hG₁_gt⟩ := hall_le
    have hG₁_fin : G₁.verts.Finite := hG_fin.subset hG₁_comp.le.1
    rcases theorem_6_3_simple hG₁_fin hG₁_comp.connected hk_pos with h1 | h2
    · left
      obtain ⟨A, hA, hdisj⟩ := h1
      refine ⟨A, ⟨fun i ↦ ?_, hdisj⟩⟩
      obtain ⟨hAi_le, hAi_conn, hAi_card⟩ := hA i
      refine ⟨hAi_le.trans hG₁_comp.le, hAi_conn, ?_⟩
      calc 4 * G.verts.ncard ≤ 3 * (2 * G₁.verts.ncard) := by omega
        _ ≤ 3 * ((3 ^ k - 1) * (A i).verts.ncard) := Nat.mul_le_mul_left 3 hAi_card
        _ = 3 * (3 ^ k - 1) * (A i).verts.ncard := by rw [← Nat.mul_assoc]
    · right
      obtain ⟨X, hX_sub_G₁, hX_lt_k, hX_comp⟩ := h2
      have hX_sub_G : X ⊆ G.verts := hX_sub_G₁.trans hG₁_comp.le.1
      have hcomp_GX : ∀ C : (⊤ : SimpleGraph V).Subgraph,
          IsComponentOf C (G.deleteVerts X) → 3 * C.verts.ncard ≤ 2 * G.verts.ncard := by
        intro C hC
        obtain ⟨v, hvC⟩ := hC.connected.nonempty
        have hvGX : v ∈ (G.deleteVerts X).verts := hC.le.1 hvC
        have hvG : v ∈ G.verts := hvGX.1
        let c_v := G.coe.connectedComponentMk ⟨v, hvG⟩
        let G_v := componentSubgraph G c_v
        have hGv_comp : IsComponentOf G_v G := isComponentOf_componentSubgraph G c_v
        have hC_le_G : C ≤ G := hC.le.trans Subgraph.deleteVerts_le
        have hC_le_Gv : C ≤ G_v :=
          le_componentSubgraph_of_preconnected hC_le_G hC.connected.preconnected hvC
        rcases hGv_comp.disjoint_or_eq hG₁_comp with hdisj_Gv | hGv_eq
        · have hdisj_C : Disjoint C.verts G₁.verts :=
            Disjoint.mono_left hC_le_Gv.1 hdisj_Gv
          have hunion_le : (C.verts ∪ G₁.verts).ncard ≤ G.verts.ncard :=
            Set.ncard_le_ncard (Set.union_subset hC_le_G.1 hG₁_comp.le.1) hG_fin
          rw [Set.ncard_union_eq hdisj_C (hG_fin.subset hC_le_G.1) hG₁_fin] at hunion_le
          omega
        · rw [hGv_eq] at hC_le_Gv
          have hC_le_G₁X : C ≤ G₁.deleteVerts X := by
            refine ⟨fun x hx ↦ ⟨hC_le_Gv.1 hx, (hC.le.1 hx).2⟩, fun x y hadj ↦ ?_⟩
            exact ⟨⟨hC_le_Gv.1 hadj.fst_mem, (hC.le.1 hadj.fst_mem).2⟩,
              ⟨hC_le_Gv.1 hadj.snd_mem, (hC.le.1 hadj.snd_mem).2⟩, hC_le_Gv.2 hadj⟩
          have hG₁X_le_GX : G₁.deleteVerts X ≤ G.deleteVerts X :=
            Subgraph.deleteVerts_mono hG₁_comp.le
          have hC_comp_G₁X : IsComponentOf C (G₁.deleteVerts X) := {
            le := hC_le_G₁X
            connected := hC.connected
            eq_of_le := fun {C'} hle hC' hC'_conn ↦
              hC.eq_of_le hle (hC'.trans hG₁X_le_GX) hC'_conn
          }
          have hlt := hX_comp C hC_comp_G₁X
          have hG₁_le_G : G₁.verts.ncard ≤ G.verts.ncard :=
            Set.ncard_le_ncard hG₁_comp.le.1 hG_fin
          omega
      obtain ⟨V₁, V₂, hsep, hinter, h1, h2⟩ :=
        exists_isSeparation_of_components_le hG_fin hX_sub_G hcomp_GX
      refine ⟨V₁, V₂, hsep, ?_, h1, h2⟩
      rw [hinter]
      exact hX_lt_k

end

end GraphMinor.GM05
