module

public import GraphMinor.GM01.Defs
import GraphMinor.GM01.Basic
import GraphMinor.GM01.Separators
import GraphMinor.GM01.DisconnectedSeparators
import GraphMinor.Menger.SimpleGraph
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Graph Minors I, (2.9): Menger-Type Separation for Connected Subgraphs in `𝓕_θ`

This file formalizes (2.9) of Robertson and Seymour, *Graph Minors I. Excluding a forest*
(pages 49–50):
* `exists_paths_or_separator_of_subgraphs`: the contracted form of Menger's theorem used on page 50,
  derived from `GraphMinor.Menger.exists_disjointPaths` by contracting each `B_j` (`j ∈ J'`) into a
  single vertex in the quotient simple graph on
  `{u : G.verts // ∀ j ∈ J', u.1 ∉ (B j).verts} ⊕ J'`.
* `exists_separator_of_no_disjoint_paths`: Menger's theorem in `G.deleteVerts X'`.
* `arith_2_9`: the arithmetic inequality `(r * θ ^ 4) / 2 + r * v ≤ 2 ^ (r * θ ^ 4)` at the end of
  the proof of (2.9) (page 50).
* `GM01.theorem_2_9`: for disjoint connected subgraphs `B₁, …, Bₙ` of `G ∈ 𝓕_θ`, `V' ⊆ V(G)`, and
  `r ≥ 0`, either (i) there are `r` disjoint paths from `r` distinct `B_j` to `V'` with no internal
  vertices in `V' ∪ ⋃_{j ∈ J} V(B_j)`, or (ii) there exist `X ⊆ V(G)` and `J ⊆ {1, …, n}` with
  `|X| + |J| ≤ 2^{r θ⁴}` such that `X` separates `V'` from every `B_j` (`j ∉ J`).
-/

public section

namespace GraphMinor.GM01

open SimpleGraph Set

variable {α : Type*}

/-! ### Shortening a walk between two sets in a simple graph -/

/-- Given a walk `w : K.Walk u v` with `u ∈ A` and `v ∈ B`, there is a path `p : K.Walk a b` with
`a ∈ A` and `b ∈ B` whose support is contained in `w.support`, such that `a` is the only vertex of
`p` in `A` and `b` is the only vertex of `p` in `B`. -/
private lemma exists_minimal_pathFromTo {V : Type*} (K : SimpleGraph V)
    (A B : Set V) {u v : V} (hu : u ∈ A) (hv : v ∈ B) (w : K.Walk u v) :
    ∃ (a b : V) (p : K.Walk a b),
      p.IsPath ∧ a ∈ A ∧ b ∈ B ∧
      (∀ z ∈ p.support, z ∈ w.support) ∧
      (∀ z ∈ p.support, z ∈ A → z = a) ∧
      (∀ z ∈ p.support, z ∈ B → z = b) := by
  classical
  -- Step 1: truncate at the first vertex in `B`.
  have h_first_B : ∀ {x y : V} (q : K.Walk x y), y ∈ B →
      ∃ (b : V) (q₁ : K.Walk x b),
        b ∈ B ∧ (∀ z ∈ q₁.support, z ∈ q.support) ∧ (∀ z ∈ q₁.support, z ∈ B → z = b) := by
    intro x y q hy
    induction q with
    | @nil x =>
      refine ⟨x, .nil, hy, fun z hz ↦ hz, fun z hz _ ↦ ?_⟩
      simpa using hz
    | @cons x x' y hadj q' ih =>
      by_cases hxB : x ∈ B
      · refine ⟨x, .nil, hxB, fun z hz ↦ ?_, fun z hz _ ↦ ?_⟩
        · simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
          subst hz
          exact Walk.start_mem_support _
        · simpa using hz
      · rcases ih hy with ⟨b, q₁, hbB, hsub, honlyB⟩
        refine ⟨b, .cons hadj q₁, hbB, fun z hz ↦ ?_, fun z hz hzB ↦ ?_⟩
        · rw [Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz'
          · exact Walk.start_mem_support _
          · exact List.mem_cons_of_mem _ (hsub z hz')
        · rw [Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz'
          · exact (hxB hzB).elim
          · exact honlyB z hz' hzB
  rcases h_first_B w hv with ⟨b, w₁, hbB, hw₁_sub, hw₁_B⟩
  -- Step 2: truncate at the last vertex in `A`.
  have h_last_A : ∀ {x y : V} (q : K.Walk x y), (∃ z ∈ q.support, z ∈ A) →
      ∃ (a : V) (q₂ : K.Walk a y),
        a ∈ A ∧ (∀ z ∈ q₂.support, z ∈ q.support) ∧ (∀ z ∈ q₂.support, z ∈ A → z = a) := by
    intro x y q hex
    induction q with
    | @nil x =>
      rcases hex with ⟨z, hz, hzA⟩
      simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
      subst hz
      refine ⟨z, .nil, hzA, fun y hy ↦ hy, fun y hy _ ↦ ?_⟩
      simpa using hy
    | @cons x x' y hadj q' ih =>
      by_cases hex' : ∃ z ∈ q'.support, z ∈ A
      · rcases ih hex' with ⟨a, q₂, haA, hsub, honlyA⟩
        exact ⟨a, q₂, haA, fun z hz ↦ List.mem_cons_of_mem _ (hsub z hz), honlyA⟩
      · have hxA : x ∈ A := by
          rcases hex with ⟨z, hz, hzA⟩
          rw [Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz'
          · exact hzA
          · exact (hex' ⟨z, hz', hzA⟩).elim
        refine ⟨x, .cons hadj q', hxA, fun z hz ↦ hz, fun z hz hzA ↦ ?_⟩
        rw [Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz'
        · rfl
        · exact (hex' ⟨z, hz', hzA⟩).elim
  rcases h_last_A w₁ ⟨u, w₁.start_mem_support, hu⟩ with ⟨a, w₂, haA, hw₂_sub, hw₂_A⟩
  let p := w₂.bypass
  have hp_sub : ∀ z ∈ p.support, z ∈ w₂.support := fun z hz ↦ w₂.support_bypass_subset_support hz
  refine ⟨a, b, p, w₂.bypass_isPath, haA, hbB,
    fun z hz ↦ hw₁_sub z (hw₂_sub z (hp_sub z hz)),
    fun z hz hzA ↦ hw₂_A z (hp_sub z hz) hzA,
    fun z hz hzB ↦ hw₁_B z (hw₂_sub z (hp_sub z hz)) hzB⟩

/-! ### Contracted Menger lemma for disjoint connected subgraphs `B_j` (`j ∈ J'`) -/

/-- The form of Menger's theorem used on page 50 of Graph Minors I:
given disjoint connected subgraphs `B_j` (`j : Fin n`) of `G`, a subset `J' ⊆ Fin n`, and `V' ⊆ V(G)`,
either:
(i) there is a subset `J ⊆ J'` of size `r` and disjoint paths `P_j` (`j ∈ J`) in `G` from `B_j` to
`V'` with no internal vertices in `V' ∪ ⋃_{j' ∈ J'} V(B_{j'})`, or
(ii) there exist `X_i ⊆ V(G)` and `J_i ⊆ J'` with `|X_i| + |J_i| < r` such that every path in `G`
from any `B_j` (`j ∈ J'`) to `V'` meets `X_i ∪ ⋃_{j' ∈ J_i} V(B_{j'})`.

Derived from `GraphMinor.Menger.exists_disjointPaths` by contracting each `B_j` (`j ∈ J'`) into a
single vertex `Sum.inr ⟨j, hj⟩` in `{u : G.verts // ∀ j ∈ J', u.1 ∉ (B j).verts} ⊕ J'`. -/
private lemma exists_paths_or_separator_of_subgraphs {n r : ℕ}
    {G : (⊤ : SimpleGraph α).Subgraph} (hfin : G.verts.Finite)
    (B : Fin n → (⊤ : SimpleGraph α).Subgraph)
    (hB_disj : Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts)
    (V' : Set α) (J' : Set (Fin n)) :
    (∃ (J : Set (Fin n)) (P : J → Path α),
      J ⊆ J' ∧ J.ncard = r ∧
      (∀ j : J, (P j).IsFromTo G (B j.1).verts V') ∧
      Pairwise (fun j₁ j₂ : J ↦ Disjoint (P j₁).verts (P j₂).verts) ∧
      (∀ j : J, Disjoint (P j).internalVerts (V' ∪ ⋃ j' ∈ J', (B j').verts))) ∨
    (∃ (X_i : Set α) (J_i : Set (Fin n)),
      X_i ⊆ G.verts ∧ J_i ⊆ J' ∧
      X_i.ncard + J_i.ncard < r ∧
      ∀ j ∈ J', Separates G (X_i ∪ ⋃ j' ∈ J_i, (B j').verts) (B j).verts V') := by
  classical
  have : Finite G.verts := hfin.to_subtype
  let OutV := {u : G.verts // ∀ j ∈ J', u.1 ∉ (B j).verts}
  let V := OutV ⊕ J'
  let φ (u : G.verts) : V :=
    if h : ∃ j ∈ J', u.1 ∈ (B j).verts then
      Sum.inr ⟨Classical.choose h, (Classical.choose_spec h).1⟩
    else
      Sum.inl ⟨u, by
        intro j hj huB
        exact h ⟨j, hj, huB⟩⟩
  have hφ_of_mem_B : ∀ {u : G.verts} {j : J'}, u.1 ∈ (B j.1).verts → φ u = Sum.inr j := by
    intro u j huB
    have hex : ∃ j' ∈ J', u.1 ∈ (B j').verts := ⟨j.1, j.2, huB⟩
    have hφ_eq : φ u = Sum.inr ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩ := by
      dsimp [φ]
      rw [dite_eq_left_of_eq_true (eq_true hex)]
    rcases Classical.choose_spec hex with ⟨hj', huB'⟩
    have hj_eq : Classical.choose hex = j.1 := by
      by_contra hne
      exact (hB_disj hne).notMem_of_mem_left huB' huB
    rw [hφ_eq]
    exact congrArg Sum.inr (Subtype.ext hj_eq)
  have hφ_inr_iff : ∀ {u : G.verts} {j : J'}, φ u = Sum.inr j ↔ u.1 ∈ (B j.1).verts := by
    intro u j
    refine ⟨fun h ↦ ?_, hφ_of_mem_B⟩
    dsimp [φ] at h
    by_cases hex : ∃ j' ∈ J', u.1 ∈ (B j').verts
    · rw [dite_eq_left_of_eq_true (eq_true hex)] at h
      have hj_eq : Classical.choose hex = j.1 :=
        congrArg Subtype.val (Sum.inr.inj h)
      rw [← hj_eq]
      exact (Classical.choose_spec hex).2
    · rw [dite_eq_right_of_eq_false (eq_false hex)] at h
      cases h
  have hφ_inl_iff : ∀ {u : G.verts} {x : OutV}, φ u = Sum.inl x ↔ u = x.1 := by
    intro u x
    constructor
    · intro h
      dsimp [φ] at h
      by_cases hex : ∃ j' ∈ J', u.1 ∈ (B j').verts
      · rw [dite_eq_left_of_eq_true (eq_true hex)] at h
        cases h
      · rw [dite_eq_right_of_eq_false (eq_false hex)] at h
        exact congrArg Subtype.val (Sum.inl.inj h)
    · rintro rfl
      have hnot : ¬ ∃ j ∈ J', x.1.1 ∈ (B j).verts := by
        rintro ⟨j, hj, hxB⟩
        exact x.2 j hj hxB
      dsimp [φ]
      rw [dite_eq_right_of_eq_false (eq_false hnot)]
  let K : SimpleGraph V := {
    Adj x y := x ≠ y ∧ ∃ u v : G.verts, φ u = x ∧ φ v = y ∧ G.Adj u.1 v.1
    symm := ⟨fun _ _ ⟨hne, u, v, hφu, hφv, hadj⟩ ↦ ⟨hne.symm, v, u, hφv, hφu, hadj.symm⟩⟩
    loopless := ⟨fun _ h ↦ h.1 rfl⟩
  }
  have : Finite OutV := Subtype.finite
  have : Finite J' := Set.toFinite J'
  let : Fintype OutV := Fintype.ofFinite OutV
  let : Fintype J' := Fintype.ofFinite J'
  have : Finite V := Finite.of_fintype (OutV ⊕ J')
  let A : Set V := Set.range Sum.inr
  let B_set : Set V := φ '' {u : G.verts | u.1 ∈ V'}
  by_cases hMenger : ∀ S : Set V,
      (∀ P : PathFromTo K A B_set, ∃ x ∈ P.walk.support, x ∈ S) → r ≤ S.ncard
  · -- Case 1: Menger's theorem gives `r` disjoint paths in `K` from `A` to `B_set`.
    left
    rcases GraphMinor.Menger.exists_disjointPaths K A B_set inferInstance r hMenger with
      ⟨Q, hQ_disj⟩
    have hshort : ∀ k : Fin r, ∃ (j_k : J') (b_k : V) (p_k : K.Walk (Sum.inr j_k) b_k),
        p_k.IsPath ∧ b_k ∈ B_set ∧
        (∀ z ∈ p_k.support, z ∈ (Q k).walk.support) ∧
        (∀ z ∈ p_k.support, z ∈ A → z = Sum.inr j_k) ∧
        (∀ z ∈ p_k.support, z ∈ B_set → z = b_k) := by
      intro k
      rcases exists_minimal_pathFromTo K A B_set (Q k).first_mem (Q k).last_mem (Q k).walk with
        ⟨a_k, b_k, p_k, hp_path, ha_A, hb_B, hp_sub, hp_onlyA, hp_onlyB⟩
      rcases ha_A with ⟨j_k, rfl⟩
      exact ⟨j_k, b_k, p_k, hp_path, hb_B, hp_sub, hp_onlyA, hp_onlyB⟩
    choose j_fn b_fn p_fn hp_path hb_B hp_sub hp_onlyA hp_onlyB using hshort
    -- Lift each `p_fn k` to a path `P_fn k` in `G`.
    have hlift_tail :
        ∀ {x y : V} (q : K.Walk x y) (hq_path : q.IsPath)
          (hq_no_A : ∀ z ∈ q.support, z ∉ A)
          (hx_inl : ∃ ux : OutV, x = Sum.inl ux),
          ∃ (uy : OutV) (w : (⊤ : SimpleGraph α).Walk (Classical.choose hx_inl).1.1 uy.1.1),
            y = Sum.inl uy ∧
            w.IsPath ∧
            w.toSubgraph ≤ G ∧
            (∀ z ∈ w.support, ∃ uz : OutV, z = uz.1.1 ∧ Sum.inl uz ∈ q.support) := by
      intro x y q hq_path hq_no_A hx_inl
      induction q with
      | @nil x =>
        let ux := Classical.choose hx_inl
        have hx_eq : x = Sum.inl ux := Classical.choose_spec hx_inl
        refine ⟨ux, .nil, hx_eq, Walk.IsPath.nil, ?_, ?_⟩
        · rw [Walk.toSubgraph, singletonSubgraph_le_iff]
          exact ux.1.2
        · intro z hz
          simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hz
          exact ⟨ux, hz, hx_eq ▸ Walk.start_mem_support _⟩
      | @cons x x' y hadj q' ih =>
        let ux := Classical.choose hx_inl
        have hx_eq : x = Sum.inl ux := Classical.choose_spec hx_inl
        have hq'_path : q'.IsPath := ((Walk.cons_isPath_iff _ _).1 hq_path).1
        have hx_not_q' : x ∉ q'.support := ((Walk.cons_isPath_iff _ _).1 hq_path).2
        have hq'_no_A : ∀ z ∈ q'.support, z ∉ A :=
          fun z hz ↦ hq_no_A z (List.mem_cons_of_mem _ hz)
        have hx'_no_A : x' ∉ A := hq'_no_A x' q'.start_mem_support
        have hx'_inl : ∃ ux' : OutV, x' = Sum.inl ux' := by
          rcases x' with ux' | j'
          · exact ⟨ux', rfl⟩
          · exact (hx'_no_A ⟨j', rfl⟩).elim
        let ux' := Classical.choose hx'_inl
        have hx'_eq : x' = Sum.inl ux' := Classical.choose_spec hx'_inl
        rcases ih hq'_path hq'_no_A hx'_inl with ⟨uy, w', hy_eq, hw'_path, hw'_le, hw'_supp⟩
        rcases hadj.2 with ⟨u₁, v₁, hφu₁, hφv₁, hadj_G⟩
        have hu₁_eq : u₁ = ux.1 := (hφ_inl_iff).1 (hφu₁.trans hx_eq)
        have hv₁_eq : v₁ = ux'.1 := (hφ_inl_iff).1 (hφv₁.trans hx'_eq)
        have hadj_ux : G.Adj ux.1.1 ux'.1.1 := hu₁_eq ▸ hv₁_eq ▸ hadj_G
        have hux_not_w' : ux.1.1 ∉ w'.support := by
          intro hmem
          rcases hw'_supp ux.1.1 hmem with ⟨uz, huz_eq, huz_q'⟩
          have huz_ux : uz = ux := Subtype.ext (Subtype.ext huz_eq.symm)
          exact hx_not_q' (hx_eq ▸ huz_ux ▸ huz_q')
        let w := Walk.cons ((top_adj _ _).2 hadj_ux.ne) w'
        refine ⟨uy, w, hy_eq, (Walk.cons_isPath_iff _ _).2 ⟨hw'_path, hux_not_w'⟩, ?_, ?_⟩
        · change (⊤ : SimpleGraph α).subgraphOfAdj _ ⊔ w'.toSubgraph ≤ G
          exact sup_le (subgraphOfAdj_le_of_adj G hadj_ux) hw'_le
        · intro z hz
          rw [Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz'
          · exact ⟨ux, rfl, hx_eq ▸ Walk.start_mem_support _⟩
          · rcases hw'_supp z hz' with ⟨uz, huz_eq, huz_q'⟩
            exact ⟨uz, huz_eq, List.mem_cons_of_mem _ huz_q'⟩
    have hlift_path_gen : ∀ {a b : V} (p : K.Walk a b) (j : J') (ha_eq : a = Sum.inr j)
        (hp_path : p.IsPath) (hb_B : b ∈ B_set)
        (hp_onlyA : ∀ z ∈ p.support, z ∈ A → z = Sum.inr j)
        (hp_onlyB : ∀ z ∈ p.support, z ∈ B_set → z = b),
        ∃ P_k : Path α,
          P_k.IsFromTo G (B j.1).verts V' ∧
          Disjoint P_k.internalVerts (V' ∪ ⋃ j' ∈ J', (B j').verts) ∧
          (∀ z ∈ P_k.verts, ∃ hzG : z ∈ G.verts, φ ⟨z, hzG⟩ ∈ p.support) := by
      intro a b p j ha_eq hp_path_k hb_B_k hp_onlyA_k hp_onlyB_k
      cases p with
      | @nil a =>
        rcases hb_B_k with ⟨u₀, hu₀_V', hφu₀⟩
        have hu₀_B : u₀.1 ∈ (B j.1).verts := hφ_inr_iff.1 (hφu₀.trans ha_eq)
        let P_k : Path α := ⟨u₀.1, u₀.1, .nil, Walk.IsPath.nil⟩
        refine ⟨P_k, ⟨?_, hu₀_B, hu₀_V'⟩, ?_, ?_⟩
        · change (Walk.nil : (⊤ : SimpleGraph α).Walk u₀.1 u₀.1).toSubgraph ≤ G
          rw [Walk.toSubgraph, singletonSubgraph_le_iff]
          exact u₀.2
        · have hint : P_k.internalVerts = ∅ := by
            ext z; simp [P_k, Path.internalVerts, Path.verts, Path.toSubgraph, Path.ends, Walk.toSubgraph]
          simp [hint]
        · intro z hz
          have hz_eq : z = u₀.1 := by
            simpa [P_k, Path.verts, Path.toSubgraph, Walk.toSubgraph] using hz
          subst hz_eq
          exact ⟨u₀.2, by simp [hφu₀]⟩
      | @cons a x₁ b hadj p' =>
        have hp'_path : p'.IsPath := ((Walk.cons_isPath_iff _ _).1 hp_path_k).1
        have hstart_not_p' : Sum.inr j ∉ p'.support :=
          ha_eq ▸ ((Walk.cons_isPath_iff _ _).1 hp_path_k).2
        have hp'_no_A : ∀ z ∈ p'.support, z ∉ A := by
          intro z hz hzA
          have hzeq := hp_onlyA_k z (List.mem_cons_of_mem _ hz) hzA
          exact hstart_not_p' (hzeq ▸ hz)
        have hx₁_inl : ∃ ux₁ : OutV, x₁ = Sum.inl ux₁ := by
          rcases x₁ with ux₁ | j₁
          · exact ⟨ux₁, rfl⟩
          · exact (hp'_no_A (Sum.inr j₁) p'.start_mem_support ⟨j₁, rfl⟩).elim
        let ux₁ := Classical.choose hx₁_inl
        have hx₁_eq : x₁ = Sum.inl ux₁ := Classical.choose_spec hx₁_inl
        rcases hlift_tail p' hp'_path hp'_no_A hx₁_inl with
          ⟨uy, w', hy_eq, hw'_path, hw'_le, hw'_supp⟩
        rcases hadj.2 with ⟨u₀, v₁, hφu₀, hφv₁, hadj_G⟩
        have hu₀_B : u₀.1 ∈ (B j.1).verts := hφ_inr_iff.1 (hφu₀.trans ha_eq)
        have hv₁_eq : v₁ = ux₁.1 := (hφ_inl_iff).1 (hφv₁.trans hx₁_eq)
        have hadj_u₀ : G.Adj u₀.1 ux₁.1.1 := hv₁_eq ▸ hadj_G
        have hu₀_not_w' : u₀.1 ∉ w'.support := by
          intro hmem
          rcases hw'_supp u₀.1 hmem with ⟨uz, huz_eq, _⟩
          have hu₀_uz : u₀.1 ∈ (B j.1).verts := hu₀_B
          rw [huz_eq] at hu₀_uz
          exact uz.2 j.1 j.2 hu₀_uz
        have huy_V' : uy.1.1 ∈ V' := by
          rcases hb_B_k with ⟨u_last, hu_last_V', hφ_last⟩
          have hu_last_eq : u_last = uy.1 := (hφ_inl_iff).1 (hφ_last.trans hy_eq)
          exact hu_last_eq ▸ hu_last_V'
        let P_k : Path α :=
          ⟨u₀.1, uy.1.1, Walk.cons ((top_adj _ _).2 hadj_u₀.ne) w',
            (Walk.cons_isPath_iff _ _).2 ⟨hw'_path, hu₀_not_w'⟩⟩
        refine ⟨P_k, ⟨?_, hu₀_B, huy_V'⟩, ?_, ?_⟩
        · change (⊤ : SimpleGraph α).subgraphOfAdj _ ⊔ w'.toSubgraph ≤ G
          exact sup_le (subgraphOfAdj_le_of_adj G hadj_u₀) hw'_le
        · rw [Set.disjoint_left]
          intro z ⟨hz_verts, hz_not_ends⟩ hz_union
          have hz_supp : z ∈ (Walk.cons ((top_adj _ _).2 hadj_u₀.ne) w').support :=
            (Walk.mem_verts_toSubgraph _).1 hz_verts
          rw [Walk.support_cons, List.mem_cons] at hz_supp
          have hz_ne_u₀ : z ≠ u₀.1 := fun h ↦ hz_not_ends (Or.inl h)
          have hz_ne_uy : z ≠ uy.1.1 := fun h ↦ hz_not_ends (Or.inr h)
          rcases hz_supp with rfl | hz_w'
          · exact hz_ne_u₀ rfl
          · rcases hw'_supp z hz_w' with ⟨uz, rfl, huz_p'⟩
            rcases hz_union with hz_V' | hz_B
            · have huz_B_set : Sum.inl uz ∈ B_set :=
                ⟨uz.1, hz_V', hφ_inl_iff.2 rfl⟩
              have huz_eq_b : Sum.inl uz = b :=
                hp_onlyB_k (Sum.inl uz) (List.mem_cons_of_mem _ huz_p') huz_B_set
              have huz_eq_uy : uz = uy := Sum.inl.inj (huz_eq_b.trans hy_eq)
              exact hz_ne_uy (congrArg (fun x : OutV ↦ x.1.1) huz_eq_uy)
            · rcases mem_iUnion₂.1 hz_B with ⟨j', hj', huz_Bj'⟩
              exact uz.2 j' hj' huz_Bj'
        · intro z hz_verts
          have hz_supp : z ∈ (Walk.cons ((top_adj _ _).2 hadj_u₀.ne) w').support :=
            (Walk.mem_verts_toSubgraph _).1 hz_verts
          rw [Walk.support_cons, List.mem_cons] at hz_supp
          rcases hz_supp with rfl | hz_w'
          · exact ⟨u₀.2, hφu₀.symm ▸ Walk.start_mem_support _⟩
          · rcases hw'_supp z hz_w' with ⟨uz, rfl, huz_p'⟩
            exact ⟨uz.1.2, (hφ_inl_iff.2 rfl).symm ▸ List.mem_cons_of_mem _ huz_p'⟩
    have hlift_path : ∀ k : Fin r, ∃ P_k : Path α,
        P_k.IsFromTo G (B (j_fn k).1).verts V' ∧
        Disjoint P_k.internalVerts (V' ∪ ⋃ j' ∈ J', (B j').verts) ∧
        (∀ z ∈ P_k.verts, ∃ hzG : z ∈ G.verts, φ ⟨z, hzG⟩ ∈ (p_fn k).support) :=
      fun k ↦ hlift_path_gen (p_fn k) (j_fn k) rfl (hp_path k) (hb_B k) (hp_onlyA k) (hp_onlyB k)
    choose P_fn hP_fromTo hP_int hP_supp using hlift_path
    have hj_inj : Function.Injective (fun k : Fin r ↦ (j_fn k).1) := by
      intro k₁ k₂ heq
      by_contra hne
      have hj_eq : j_fn k₁ = j_fn k₂ := Subtype.ext heq
      have hmem₁ : Sum.inr (j_fn k₁) ∈ (Q k₁).walk.support :=
        hp_sub k₁ _ (Walk.start_mem_support _)
      have hmem₂ : Sum.inr (j_fn k₁) ∈ (Q k₂).walk.support := by
        rw [hj_eq]
        exact hp_sub k₂ _ (Walk.start_mem_support _)
      exact (hQ_disj hne).notMem_of_mem_left hmem₁ hmem₂
    let J : Set (Fin n) := Set.range (fun k : Fin r ↦ (j_fn k).1)
    have hJ_sub : J ⊆ J' := by
      rintro _ ⟨k, rfl⟩
      exact (j_fn k).2
    have hJ_card : J.ncard = r := by
      dsimp [J]
      rw [← Set.image_univ, Set.ncard_image_of_injective Set.univ hj_inj,
        Set.ncard_univ, Nat.card_fin]
    let eJ : J ≃ Fin r := (Equiv.ofInjective (fun k : Fin r ↦ (j_fn k).1) hj_inj).symm
    have heJ_val : ∀ j : J, (j_fn (eJ j)).1 = j.1 := fun j ↦
      Subtype.ext_iff.1 ((Equiv.ofInjective (fun k : Fin r ↦ (j_fn k).1) hj_inj).apply_symm_apply j)
    let P_out (j : J) : Path α := P_fn (eJ j)
    refine ⟨J, P_out, hJ_sub, hJ_card, ?_, ?_, ?_⟩
    · intro j
      dsimp [P_out]
      rw [← heJ_val j]
      exact hP_fromTo (eJ j)
    · intro j₁ j₂ hne
      have hk_ne : eJ j₁ ≠ eJ j₂ := fun h ↦ hne (eJ.injective h)
      rw [Set.disjoint_left]
      intro z hz₁ hz₂
      rcases hP_supp (eJ j₁) z hz₁ with ⟨hzG₁, hφ₁⟩
      rcases hP_supp (eJ j₂) z hz₂ with ⟨_, hφ₂⟩
      have hmem₁ : φ ⟨z, hzG₁⟩ ∈ (Q (eJ j₁)).walk.support := hp_sub (eJ j₁) _ hφ₁
      have hmem₂ : φ ⟨z, hzG₁⟩ ∈ (Q (eJ j₂)).walk.support := hp_sub (eJ j₂) _ hφ₂
      exact (hQ_disj hk_ne).notMem_of_mem_left hmem₁ hmem₂
    · intro j
      exact hP_int (eJ j)
  · -- Case 2: There is a separator `S : Set V` with `S.ncard < r`.
    right
    push Not at hMenger
    rcases hMenger with ⟨S, hS_sep, hS_card⟩
    let X_i : Set α := (fun x : OutV ↦ x.1.1) '' (Sum.inl ⁻¹' S)
    let J_i : Set (Fin n) := Subtype.val '' (Sum.inr ⁻¹' S)
    have hXi_G : X_i ⊆ G.verts := by
      rintro _ ⟨x, _, rfl⟩
      exact x.1.2
    have hJi_J' : J_i ⊆ J' := by
      rintro _ ⟨j', _, rfl⟩
      exact j'.2
    have hcard_lt : X_i.ncard + J_i.ncard < r := by
      let S_inl : Set V := Sum.inl '' (Sum.inl ⁻¹' S)
      let S_inr : Set V := Sum.inr '' (Sum.inr ⁻¹' S)
      have hXi_card : X_i.ncard = S_inl.ncard := by
        have hinj : Function.Injective (fun x : OutV ↦ x.1.1) :=
          Subtype.val_injective.comp Subtype.val_injective
        rw [Set.ncard_image_of_injective _ hinj,
          Set.ncard_image_of_injective _ Sum.inl_injective]
      have hJi_card : J_i.ncard = S_inr.ncard := by
        rw [Set.ncard_image_of_injective _ Subtype.val_injective,
          Set.ncard_image_of_injective _ Sum.inr_injective]
      have hdisj : Disjoint S_inl S_inr := by
        rw [Set.disjoint_left]
        rintro _ ⟨x, _, rfl⟩ ⟨j', _, heq⟩
        cases heq
      have hunion : S_inl ∪ S_inr = S := by
        ext v
        simp only [S_inl, S_inr, mem_union, mem_image, mem_preimage]
        constructor
        · rintro (⟨x, hxS, rfl⟩ | ⟨j', hj'S, rfl⟩)
          · exact hxS
          · exact hj'S
        · intro hvS
          rcases v with x | j'
          · exact Or.inl ⟨x, hvS, rfl⟩
          · exact Or.inr ⟨j', hvS, rfl⟩
      have hsum_eq : X_i.ncard + J_i.ncard = S.ncard := by
        rw [hXi_card, hJi_card, ← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
          hunion]
      omega
    -- Any walk in `G` projects via `φ` to a walk in `K`.
    have hproj_walk : ∀ {u v : α} (w : (⊤ : SimpleGraph α).Walk u v) (hw : w.toSubgraph ≤ G)
        (hu : u ∈ G.verts) (hv : v ∈ G.verts),
        ∃ w_K : K.Walk (φ ⟨u, hu⟩) (φ ⟨v, hv⟩),
          ∀ x ∈ w_K.support, ∃ z ∈ w.support, ∃ hzG : z ∈ G.verts, φ ⟨z, hzG⟩ = x := by
      intro u v w hw hu hv
      induction w with
      | @nil u =>
        refine ⟨.nil, fun x hx ↦ ?_⟩
        simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
        exact ⟨u, Walk.start_mem_support _, hu, hx.symm⟩
      | @cons u u' v hadj w' ih =>
        have hadj_G : G.Adj u u' := by
          have hle_adj : (⊤ : SimpleGraph α).subgraphOfAdj hadj ≤ G :=
            le_sup_left.trans hw
          exact (subgraphOfAdj_le_iff _ _).1 hle_adj
        have hw'_le : w'.toSubgraph ≤ G := le_sup_right.trans hw
        have hu' : u' ∈ G.verts := G.edge_vert hadj_G.symm
        rcases ih hw'_le hu' hv with ⟨w'_K, hw'_supp⟩
        by_cases hφ_eq : φ ⟨u, hu⟩ = φ ⟨u', hu'⟩
        · refine ⟨w'_K.copy hφ_eq.symm rfl, fun x hx ↦ ?_⟩
          rw [Walk.support_copy] at hx
          rcases hw'_supp x hx with ⟨z, hz, hzG, hφz⟩
          exact ⟨z, List.mem_cons_of_mem _ hz, hzG, hφz⟩
        · have hadj_K : K.Adj (φ ⟨u, hu⟩) (φ ⟨u', hu'⟩) :=
            ⟨hφ_eq, ⟨u, hu⟩, ⟨u', hu'⟩, rfl, rfl, hadj_G⟩
          refine ⟨.cons hadj_K w'_K, fun x hx ↦ ?_⟩
          rw [Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx'
          · exact ⟨u, Walk.start_mem_support _, hu, rfl⟩
          · rcases hw'_supp x hx' with ⟨z, hz, hzG, hφz⟩
            exact ⟨z, List.mem_cons_of_mem _ hz, hzG, hφz⟩
    refine ⟨X_i, J_i, hXi_G, hJi_J', hcard_lt, fun j hj P hP hP_avoids ↦ ?_⟩
    have hfirst_G : P.first ∈ G.verts := hP.1.1 P.first_mem_verts
    have hlast_G : P.last ∈ G.verts := hP.1.1 P.last_mem_verts
    rcases hproj_walk P.walk hP.1 hfirst_G hlast_G with ⟨w_K, hw_K_supp⟩
    have hfirst_A : φ ⟨P.first, hfirst_G⟩ ∈ A :=
      ⟨⟨j, hj⟩, (hφ_of_mem_B (j := ⟨j, hj⟩) hP.2.1).symm⟩
    have hlast_B : φ ⟨P.last, hlast_G⟩ ∈ B_set :=
      ⟨⟨P.last, hlast_G⟩, hP.2.2, rfl⟩
    let p_K : PathFromTo K A B_set :=
      ⟨_, _, w_K.bypass, w_K.bypass_isPath, hfirst_A, hlast_B⟩
    rcases hS_sep p_K with ⟨x, hx_pK, hxS⟩
    have hx_wK : x ∈ w_K.support := w_K.support_bypass_subset_support hx_pK
    rcases hw_K_supp x hx_wK with ⟨z, hz_supp, hzG, hφz⟩
    have hz_P : z ∈ P.verts := (Walk.mem_verts_toSubgraph _).2 hz_supp
    have hz_sep : z ∈ X_i ∪ ⋃ j' ∈ J_i, (B j').verts := by
      rcases x with ux | j'
      · have huz : ⟨z, hzG⟩ = ux.1 := hφ_inl_iff.1 hφz
        have hz_eq : z = ux.1.1 := congrArg Subtype.val huz
        exact Or.inl ⟨ux, hxS, hz_eq.symm⟩
      · have hz_B : z ∈ (B j'.1).verts := hφ_inr_iff.1 hφz
        have hj'_Ji : j'.1 ∈ J_i := ⟨j', hxS, rfl⟩
        exact Or.inr (mem_biUnion hj'_Ji hz_B)
    exact hP_avoids.notMem_of_mem_left hz_P hz_sep

/-! ### Component bound for a union of connected subgraphs -/

/-- If `B j` (`j ∈ S`) are connected subgraphs of a finite subgraph `G`, then `⨆ j ∈ S, B j` has
at most `S.ncard` connected components. -/
private lemma numComponents_biSup_le {n : ℕ}
    {G : (⊤ : SimpleGraph α).Subgraph} (hfin : G.verts.Finite)
    (B : Fin n → (⊤ : SimpleGraph α).Subgraph) (hB_le : ∀ j, B j ≤ G)
    (hB_conn : ∀ j, (B j).Connected) (S : Set (Fin n)) :
    numComponents (⨆ j ∈ S, B j) ≤ S.ncard := by
  classical
  let H := ⨆ j ∈ S, B j
  have hH_le : H ≤ G := iSup₂_le fun j _ ↦ hB_le j
  have hH_fin : H.verts.Finite := hfin.subset hH_le.1
  have : Finite H.verts := hH_fin.to_subtype
  have : Finite S := Set.toFinite S
  let f (j : S) : H.coe.ConnectedComponent :=
    let v := Classical.choose (hB_conn j.1).nonempty
    have hv_B : v ∈ (B j.1).verts := Classical.choose_spec (hB_conn j.1).nonempty
    have hv_H : v ∈ H.verts := (le_biSup B j.2).1 hv_B
    H.coe.connectedComponentMk ⟨v, hv_H⟩
  have hf_surj : Function.Surjective f := by
    intro c
    rcases c.exists_rep with ⟨⟨u, hu_H⟩, rfl⟩
    have hu_union : u ∈ ⋃ j ∈ S, (B j).verts := by
      simpa [H, Subgraph.verts_iSup] using hu_H
    rcases mem_iUnion₂.1 hu_union with ⟨j, hjS, hu_Bj⟩
    refine ⟨⟨j, hjS⟩, ?_⟩
    dsimp [f]
    let v := Classical.choose (hB_conn j).nonempty
    have hv_Bj : v ∈ (B j).verts := Classical.choose_spec (hB_conn j).nonempty
    rcases (hB_conn j).preconnected ⟨v, hv_Bj⟩ ⟨u, hu_Bj⟩ with ⟨w⟩
    exact ConnectedComponent.eq.2
      ((w.map (Subgraph.inclusion (le_biSup B hjS))).reachable)
  calc
    numComponents H = Nat.card H.coe.ConnectedComponent := rfl
    _ ≤ Nat.card S := Nat.card_le_card_of_surjective f hf_surj
    _ = S.ncard := Nat.card_coe_set_eq S

/-! ### Menger's theorem in `G.deleteVerts X'` -/

/-- If there is no family of `M` disjoint paths in `G` from `A₁` to `A₂` avoiding `X'`, then there
is a subset `X'' ⊆ V(G)` with `X''.ncard < M` such that `X' ∪ X''` separates `A₁` and `A₂` in `G`. -/
lemma exists_separator_of_no_disjoint_paths {M : ℕ}
    {G : (⊤ : SimpleGraph α).Subgraph} (hfin : G.verts.Finite)
    (X' A₁ A₂ : Set α)
    (h_no_paths : ¬ ∃ P : Fin M → Path α,
      IsDisjointPathFamily G A₁ A₂ P ∧ ∀ k, (P k).Avoids X') :
    ∃ X'' ⊆ G.verts, X''.ncard < M ∧ Separates G (X' ∪ X'') A₁ A₂ := by
  classical
  let H := G.deleteVerts X'
  have hH_le : H ≤ G := Subgraph.deleteVerts_le
  have hH_fin : H.verts.Finite := hfin.subset hH_le.1
  have : Finite H.verts := hH_fin.to_subtype
  let A_H : Set H.verts := {u : H.verts | u.1 ∈ A₁}
  let B_H : Set H.verts := {u : H.verts | u.1 ∈ A₂}
  have h_not_all : ¬ ∀ S : Set H.verts,
      (∀ P : PathFromTo H.coe A_H B_H, ∃ x ∈ P.walk.support, x ∈ S) → M ≤ S.ncard := by
    intro hMenger
    rcases GraphMinor.Menger.exists_disjointPaths H.coe A_H B_H inferInstance M hMenger with
      ⟨Q, hQ_disj⟩
    have hhom_inj : Function.Injective H.hom := Subtype.val_injective
    let P (k : Fin M) : Path α :=
      ⟨(Q k).first.1, (Q k).last.1, (Q k).walk.map H.hom,
        (Q k).isPath.map hhom_inj⟩
    have hP_supp : ∀ (k : Fin M) {z : α}, z ∈ (P k).verts ↔
        ∃ u ∈ (Q k).walk.support, u.1 = z := by
      intro k z
      rw [Path.mem_verts_iff]
      change z ∈ ((Q k).walk.map H.hom).support ↔ _
      rw [Walk.support_map, List.mem_map]
      rfl
    have hP_le_H : ∀ k : Fin M, (P k).toSubgraph ≤ H := by
      intro k
      have hwalk_le : ∀ {u v : H.verts} (w : H.coe.Walk u v),
          (w.map H.hom).toSubgraph ≤ H := by
        intro u v w
        induction w with
        | @nil u =>
          rw [Walk.map_nil, Walk.toSubgraph, singletonSubgraph_le_iff]
          exact u.2
        | @cons u u' v hadj w' ih =>
          rw [Walk.map_cons]
          change (⊤ : SimpleGraph α).subgraphOfAdj _ ⊔ (w'.map H.hom).toSubgraph ≤ H
          exact sup_le (subgraphOfAdj_le_of_adj H hadj) ih
      exact hwalk_le (Q k).walk
    refine h_no_paths ⟨P, ⟨fun k ↦ ⟨(hP_le_H k).trans hH_le, (Q k).first_mem, (Q k).last_mem⟩,
      fun k₁ k₂ hne ↦ ?_⟩, fun k ↦ ?_⟩
    · dsimp only
      rw [Set.disjoint_left]
      intro z hz₁ hz₂
      rcases (hP_supp k₁).1 hz₁ with ⟨u₁, hu₁, rfl⟩
      rcases (hP_supp k₂).1 hz₂ with ⟨u₂, hu₂, hu₂_eq⟩
      have hu_eq : u₁ = u₂ := Subtype.ext hu₂_eq.symm
      exact (hQ_disj hne).notMem_of_mem_left hu₁ (hu_eq ▸ hu₂)
    · rw [Path.Avoids, Set.disjoint_left]
      intro z hzP hzX'
      rcases (hP_supp k).1 hzP with ⟨u, _, rfl⟩
      exact u.2.2 hzX'
  push Not at h_not_all
  rcases h_not_all with ⟨S, hS_sep, hS_lt⟩
  let X'' : Set α := Subtype.val '' S
  have hX''_G : X'' ⊆ G.verts := by
    rintro _ ⟨u, _, rfl⟩
    exact u.2.1
  have hX''_card : X''.ncard < M := by
    rw [Set.ncard_image_of_injective S Subtype.val_injective]
    omega
  refine ⟨X'', hX''_G, hX''_card, fun P hP hP_avoids ↦ ?_⟩
  have hP_disj_X' : Disjoint P.verts X' :=
    hP_avoids.mono_right subset_union_left
  have hP_disj_X'' : Disjoint P.verts X'' :=
    hP_avoids.mono_right subset_union_right
  have hwalk_lift : ∀ {u v : α} (w : (⊤ : SimpleGraph α).Walk u v)
      (hw_G : w.toSubgraph ≤ G) (hw_X' : ∀ z ∈ w.support, z ∉ X')
      (hu_H : u ∈ H.verts) (hv_H : v ∈ H.verts),
      ∃ w_H : H.coe.Walk ⟨u, hu_H⟩ ⟨v, hv_H⟩,
        ∀ x ∈ w_H.support, x.1 ∈ w.support := by
    intro u v w hw_G hw_X' hu_H hv_H
    induction w with
    | nil =>
      refine ⟨.nil, fun x hx ↦ ?_⟩
      simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx
      exact Walk.start_mem_support _
    | @cons u u' v hadj w' ih =>
      have hadj_G : G.Adj u u' :=
        (subgraphOfAdj_le_iff _ _).1 (le_sup_left.trans hw_G)
      have hw'_G : w'.toSubgraph ≤ G := le_sup_right.trans hw_G
      have hw'_X' : ∀ z ∈ w'.support, z ∉ X' :=
        fun z hz ↦ hw_X' z (List.mem_cons_of_mem _ hz)
      have hu'_H : u' ∈ H.verts :=
        ⟨G.edge_vert hadj_G.symm, hw'_X' u' w'.start_mem_support⟩
      have hadj_H : H.coe.Adj ⟨u, hu_H⟩ ⟨u', hu'_H⟩ :=
        ⟨hu_H, hu'_H, hadj_G⟩
      rcases ih hw'_G hw'_X' hu'_H hv_H with ⟨w'_H, hw'_supp⟩
      refine ⟨.cons hadj_H w'_H, fun x hx ↦ ?_⟩
      rw [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx'
      · exact Walk.start_mem_support _
      · exact List.mem_cons_of_mem _ (hw'_supp x hx')
  have hP_no_X' : ∀ z ∈ P.walk.support, z ∉ X' :=
    fun z hz ↦ hP_disj_X'.notMem_of_mem_left ((Walk.mem_verts_toSubgraph _).2 hz)
  have hfirst_H : P.first ∈ H.verts :=
    ⟨hP.1.1 P.first_mem_verts, hP_no_X' P.first P.walk.start_mem_support⟩
  have hlast_H : P.last ∈ H.verts :=
    ⟨hP.1.1 P.last_mem_verts, hP_no_X' P.last P.walk.end_mem_support⟩
  rcases hwalk_lift P.walk hP.1 hP_no_X' hfirst_H hlast_H with ⟨w_H, hw_H_supp⟩
  let p_H : PathFromTo H.coe A_H B_H :=
    ⟨⟨P.first, hfirst_H⟩, ⟨P.last, hlast_H⟩, w_H.bypass, w_H.bypass_isPath, hP.2.1, hP.2.2⟩
  rcases hS_sep p_H with ⟨x, hx_pH, hxS⟩
  have hx_P : x.1 ∈ P.verts :=
    (Walk.mem_verts_toSubgraph _).2 (hw_H_supp x (w_H.support_bypass_subset_support hx_pH))
  have hx_X'' : x.1 ∈ X'' := ⟨x, hxS, rfl⟩
  exact hP_disj_X''.notMem_of_mem_left hx_P hx_X''

/-- Symmetry of `Separates` via `Path.reverse`. -/
private lemma Separates.symm {G : (⊤ : SimpleGraph α).Subgraph} {X A₁ A₂ : Set α}
    (h : Separates G X A₁ A₂) : Separates G X A₂ A₁ := by
  intro P hP hP_avoids
  have hrev : P.reverse.IsFromTo G A₁ A₂ := by
    refine ⟨?_, ?_, ?_⟩
    · rw [P.reverse_toSubgraph]
      exact hP.1
    · rw [P.reverse_first]
      exact hP.2.2
    · rw [P.reverse_last]
      exact hP.2.1
  have hrev_avoids : P.reverse.Avoids X := by
    rw [Path.Avoids, P.reverse_verts]
    exact hP_avoids
  exact h P.reverse hrev hrev_avoids

/-! ### Arithmetic bound at the end of (2.9) (page 50) -/

/-- Auxiliary inequality `r ^ 2 ≤ 2 ^ (2 * r)` for all `r : ℕ`. -/
private lemma sq_le_two_pow_two_mul (r : ℕ) : r ^ 2 ≤ 2 ^ (2 * r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · decide
    · have hr2 : 1 ≤ r ^ 2 := by nlinarith
      have hstep : (r + 1) ^ 2 ≤ 4 * r ^ 2 := by nlinarith
      calc
        (r + 1) ^ 2 ≤ 4 * r ^ 2 := hstep
        _ ≤ 4 * 2 ^ (2 * r) := Nat.mul_le_mul_left 4 ih
        _ = 2 ^ (2 * (r + 1)) := by
          have : 2 * (r + 1) = 2 * r + 2 := by ring
          rw [this, pow_add]
          ring

/-- The final arithmetic inequality on page 50 of Graph Minors I:
for `6 ≤ θ`, `Even θ`, `1 ≤ r`, and `v = 2 ^ (r * θ ^ 4 / 2) * (θ ^ 2 + 2 * r * θ ^ (2 * θ + 2))`,
we have `(r * θ ^ 4) / 2 + r * v ≤ 2 ^ (r * θ ^ 4)`. -/
private lemma arith_2_9 {θ r : ℕ} (hθ : 6 ≤ θ) (heven : Even θ) (hr : 1 ≤ r) :
    let v := 2 ^ (r * θ ^ 4 / 2) * (θ ^ 2 + 2 * r * θ ^ (2 * θ + 2))
    r * θ ^ 4 / 2 + r * v ≤ 2 ^ (r * θ ^ 4) := by
  intro v
  let M := r * θ ^ 4 / 2
  have h2M : M + M = r * θ ^ 4 := by
    rcases heven with ⟨k, hk⟩
    have h4 : r * θ ^ 4 = 2 * (8 * r * k ^ 4) := by rw [hk]; ring
    have hM_eq : M = 8 * r * k ^ 4 := by
      dsimp [M]
      rw [h4, Nat.mul_div_cancel_left _ (by omega)]
    omega
  have hM_ge : 2 + 2 * r + θ * (2 * θ + 2) ≤ M := by
    rcases heven with ⟨k, hk⟩
    have hk_ge : 3 ≤ k := by omega
    have h4 : r * θ ^ 4 = 2 * (8 * r * k ^ 4) := by rw [hk]; ring
    have hM_eq : M = 8 * r * k ^ 4 := by
      dsimp [M]
      rw [h4, Nat.mul_div_cancel_left _ (by omega)]
    rw [hM_eq, hk]
    have hk2 : 9 ≤ k ^ 2 := by nlinarith
    have hk3 : 27 ≤ k ^ 3 := by nlinarith
    have hk4 : 81 ≤ k ^ 4 := by nlinarith
    have hrk2 : k ^ 2 ≤ r * k ^ 2 := le_mul_of_one_le_left (by positivity) hr
    have hrk : k ≤ r * k := le_mul_of_one_le_left (by positivity) hr
    have hk_le_k4 : k ^ 2 ≤ k ^ 4 := by nlinarith
    have hk1_le_k4 : k ≤ k ^ 4 := by nlinarith
    nlinarith
  have hterm_le : 1 + r * θ ^ 2 + 2 * r ^ 2 * θ ^ (2 * θ + 2) ≤ 2 ^ M := by
    have hθ_pow_pos : 1 ≤ θ ^ (2 * θ + 2) := Nat.one_le_pow _ _ (by omega)
    have hr2_pos : 1 ≤ r ^ 2 := by nlinarith
    have h1_le : 1 ≤ r ^ 2 * θ ^ (2 * θ + 2) := Nat.mul_le_mul hr2_pos hθ_pow_pos
    have hr_le_r2 : r ≤ r ^ 2 := by nlinarith
    have hθ2_le : θ ^ 2 ≤ θ ^ (2 * θ + 2) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hrθ2_le : r * θ ^ 2 ≤ r ^ 2 * θ ^ (2 * θ + 2) :=
      Nat.mul_le_mul hr_le_r2 hθ2_le
    have hsum_le_4 : 1 + r * θ ^ 2 + 2 * r ^ 2 * θ ^ (2 * θ + 2) ≤
        4 * r ^ 2 * θ ^ (2 * θ + 2) := by linarith
    have hθ_pow_le : θ ^ (2 * θ + 2) ≤ 2 ^ (θ * (2 * θ + 2)) := by
      calc
        θ ^ (2 * θ + 2) ≤ (2 ^ θ) ^ (2 * θ + 2) :=
          Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
        _ = 2 ^ (θ * (2 * θ + 2)) := (pow_mul 2 θ (2 * θ + 2)).symm
    calc
      1 + r * θ ^ 2 + 2 * r ^ 2 * θ ^ (2 * θ + 2)
        ≤ 4 * r ^ 2 * θ ^ (2 * θ + 2) := hsum_le_4
      _ ≤ 2 ^ 2 * 2 ^ (2 * r) * 2 ^ (θ * (2 * θ + 2)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4 (sq_le_two_pow_two_mul r)) hθ_pow_le
      _ = 2 ^ (2 + 2 * r + θ * (2 * θ + 2)) := by
        rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ M := Nat.pow_le_pow_right (by omega) hM_ge
  have hM_le_pow : M ≤ 2 ^ M := (Nat.lt_two_pow_self).le
  calc
    M + r * v
      = M + 2 ^ M * (r * θ ^ 2 + 2 * r ^ 2 * θ ^ (2 * θ + 2)) := by
        dsimp [v, M]
        ring
    _ ≤ 2 ^ M + 2 ^ M * (r * θ ^ 2 + 2 * r ^ 2 * θ ^ (2 * θ + 2)) :=
      Nat.add_le_add_right hM_le_pow _
    _ = 2 ^ M * (1 + r * θ ^ 2 + 2 * r ^ 2 * θ ^ (2 * θ + 2)) := by ring
    _ ≤ 2 ^ M * 2 ^ M := Nat.mul_le_mul_left (2 ^ M) hterm_le
    _ = 2 ^ (M + M) := (pow_add 2 M M).symm
    _ = 2 ^ (r * θ ^ 4) := by rw [h2M]

/-! ### Proof of (2.9) (pages 49–50) -/

/-- **Graph Minors I, (2.9)** (pages 49–50):
"If $B_1, \dots, B_n$ are disjoint connected subgraphs of a graph $G \in \mathscr{F}_\theta$, and
$V' \subseteq V(G)$ and $r \ge 0$ is an integer, then one of the following is true:
(i) there exists $J \subseteq \{1, \dots, n\}$ with $|J| = r$ such that for each $j \in J$ there is
a path $P_j$ in $G$ from $B_j$ to $V'$, and the paths $P_j$ ($j \in J$) are disjoint, and each has
no internal vertex in $V' \cup \bigcup_{j \in J} V(B_j)$;"
"(ii) there exist $X \subseteq V(G)$ and $J \subseteq \{1, \dots, n\}$ with
$|X| + |J| \le 2^{r\theta^4}$, such that $X$ separates $V'$ from every $B_j$
($j \in \{1, \dots, n\} - J$)."
This is the simple special case. The full statement is `GM01.Full.theorem_2_9_proof`. -/
theorem theorem_2_9_simple {θ r n : ℕ} (hθ : 6 ≤ θ) (heven : Even θ)
    {G : (⊤ : SimpleGraph α).Subgraph} (hfin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    {V' : Set α} (hV' : V' ⊆ G.verts)
    (B : Fin n → (⊤ : SimpleGraph α).Subgraph) (hB_le : ∀ j, B j ≤ G)
    (hB_conn : ∀ j, (B j).Connected)
    (hB_disj : Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts) :
    (∃ (J : Set (Fin n)) (P : J → Path α),
      J.ncard = r ∧
      (∀ j : J, (P j).IsFromTo G (B j.1).verts V') ∧
      Pairwise (fun j₁ j₂ : J ↦ Disjoint (P j₁).verts (P j₂).verts) ∧
      (∀ j : J, Disjoint (P j).internalVerts (V' ∪ ⋃ j' ∈ J, (B j').verts))) ∨
    (∃ (X : Set α) (J : Set (Fin n)),
      X ⊆ G.verts ∧
      X.ncard + J.ncard ≤ 2 ^ (r * θ ^ 4) ∧
      ∀ j ∉ J, Separates G X V' (B j).verts) := by
  classical
  by_cases hi : ∃ (J : Set (Fin n)) (P : J → Path α),
      J.ncard = r ∧
      (∀ j : J, (P j).IsFromTo G (B j.1).verts V') ∧
      Pairwise (fun j₁ j₂ : J ↦ Disjoint (P j₁).verts (P j₂).verts) ∧
      (∀ j : J, Disjoint (P j).internalVerts (V' ∪ ⋃ j' ∈ J, (B j').verts))
  · exact Or.inl hi
  · right
    have hr_pos : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · exfalso
        refine hi ⟨∅, IsEmpty.elim inferInstance, Set.ncard_empty _,
          fun j ↦ j.2.elim, fun j ↦ j.2.elim, fun j ↦ j.2.elim⟩
      · exact hr
    -- Since (i) fails, for every `J' ⊆ Fin n`, Menger's theorem gives `X_i` and `J_i ⊆ J'`
    -- with `X_i.ncard + J_i.ncard < r` separating `B j` (`j ∈ J'`) from `V'`.
    have hex_sep : ∀ J' : Set (Fin n),
        ∃ (X_i : Set α) (J_i : Set (Fin n)),
          X_i ⊆ G.verts ∧ J_i ⊆ J' ∧
          X_i.ncard + J_i.ncard < r ∧
          ∀ j ∈ J', Separates G (X_i ∪ ⋃ j' ∈ J_i, (B j').verts) (B j).verts V' := by
      intro J'
      rcases exists_paths_or_separator_of_subgraphs (r := r) hfin B hB_disj V' J' with
        ⟨J, P, hJ_sub, hJ_card, hP_fromTo, hP_disj, hP_int⟩ | hsep
      · exfalso
        refine hi ⟨J, P, hJ_card, hP_fromTo, hP_disj, fun j ↦ ?_⟩
        exact (hP_int j).mono_right
          (union_subset_union_right V' (biUnion_subset_biUnion_left hJ_sub))
      · exact hsep
    choose X_fn J_fn hX_fn_G hJ_fn_sub hXJ_fn_card hXJ_fn_sep using hex_sep
    let v := 2 ^ (r * θ ^ 4 / 2) * (θ ^ 2 + 2 * r * θ ^ (2 * θ + 2))
    -- Inductively define `J_rem k = {1, …, n} \ (J_0 ∪ … ∪ J_{k - 1})`.
    let J_rem : ℕ → Set (Fin n) :=
      fun k ↦ Nat.rec Set.univ (fun _ Ji ↦ Ji \ J_fn Ji) k
    have hJ_rem_zero : J_rem 0 = Set.univ := rfl
    have hJ_rem_succ : ∀ k : ℕ, J_rem (k + 1) = J_rem k \ J_fn (J_rem k) := fun _ ↦ rfl
    have hmem_J_rem_iff : ∀ (k : ℕ) (j : Fin n),
        j ∈ J_rem k ↔ ∀ t < k, j ∉ J_fn (J_rem t) := by
      intro k j
      induction k with
      | zero => simp [hJ_rem_zero]
      | succ k ih =>
        rw [hJ_rem_succ, mem_sdiff, ih]
        constructor
        · rintro ⟨hlt, hk⟩ t ht
          rcases Nat.lt_succ_iff_lt_or_eq.1 ht with hlt_k | rfl
          · exact hlt t hlt_k
          · exact hk
        · intro hall
          exact ⟨fun t ht ↦ hall t (Nat.lt_succ_of_lt ht), hall k (Nat.lt_succ_self k)⟩
    let X_seq (i : Fin v) : Set α := X_fn (J_rem i.1)
    let J_seq (i : Fin v) : Set (Fin n) := J_fn (J_rem i.1)
    have hJ_seq_disj : Pairwise fun i₁ i₂ : Fin v ↦ Disjoint (J_seq i₁) (J_seq i₂) := by
      have hlt_disj : ∀ {i₁ i₂ : Fin v}, i₁.1 < i₂.1 → Disjoint (J_seq i₁) (J_seq i₂) := by
        intro i₁ i₂ hlt
        rw [Set.disjoint_left]
        intro j hj₁ hj₂
        have hj_rem₂ : j ∈ J_rem i₂.1 := hJ_fn_sub (J_rem i₂.1) hj₂
        exact (hmem_J_rem_iff i₂.1 j).1 hj_rem₂ i₁.1 hlt hj₁
      intro i₁ i₂ hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · exact hlt_disj hlt
      · exact (hlt_disj hgt).symm
    let X' : Set α := ⋃ i : Fin v, X_seq i
    let J : Set (Fin n) := ⋃ i : Fin v, J_seq i
    let B' (i : Fin v) : (⊤ : SimpleGraph α).Subgraph := ⨆ j ∈ J_seq i, B j
    let A₁ : Set α := ⋃ j ∉ J, (B j).verts
    let A₂ : Set α := V'
    have hA₁_G : A₁ ⊆ G.verts := iUnion₂_subset fun j _ ↦ (hB_le j).1
    have hX'_G : X' ⊆ G.verts := iUnion_subset fun i ↦ hX_fn_G (J_rem i.1)
    -- Bound `(⋃ i ∈ T, X_seq i).ncard + (⋃ i ∈ T, J_seq i).ncard ≤ T.card * r`.
    have hXJ_sum_le : ∀ (T : Finset (Fin v)),
        (⋃ i ∈ T, X_seq i).ncard + (⋃ i ∈ T, J_seq i).ncard ≤ T.card * r := by
      intro T
      induction T using Finset.induction with
      | empty => simp
      | @insert i T hi_not_mem ih =>
        have hunion_X : (⋃ i' ∈ insert i T, X_seq i') = X_seq i ∪ ⋃ i' ∈ T, X_seq i' := by
          ext x; simp
        have hunion_J : (⋃ i' ∈ insert i T, J_seq i') = J_seq i ∪ ⋃ i' ∈ T, J_seq i' := by
          ext j; simp
        have hXi_Ji : (X_seq i).ncard + (J_seq i).ncard ≤ r :=
          (hXJ_fn_card (J_rem i.1)).le
        calc
          (⋃ i' ∈ insert i T, X_seq i').ncard + (⋃ i' ∈ insert i T, J_seq i').ncard
            ≤ ((X_seq i).ncard + (⋃ i' ∈ T, X_seq i').ncard) +
              ((J_seq i).ncard + (⋃ i' ∈ T, J_seq i').ncard) := by
              rw [hunion_X, hunion_J]
              exact Nat.add_le_add (Set.ncard_union_le _ _) (Set.ncard_union_le _ _)
          _ = ((X_seq i).ncard + (J_seq i).ncard) +
              ((⋃ i' ∈ T, X_seq i').ncard + (⋃ i' ∈ T, J_seq i').ncard) := by ring
          _ ≤ r + T.card * r := Nat.add_le_add hXi_Ji ih
          _ = (insert i T).card * r := by
            rw [Finset.card_insert_of_notMem hi_not_mem, add_mul, one_mul, add_comm]
    have hX'_J_card : X'.ncard + J.ncard ≤ r * v := by
      have hX'_eq : X' = ⋃ i ∈ (Finset.univ : Finset (Fin v)), X_seq i := by ext x; simp [X']
      have hJ_eq : J = ⋃ i ∈ (Finset.univ : Finset (Fin v)), J_seq i := by ext j; simp [J]
      rw [hX'_eq, hJ_eq, mul_comm r v]
      simpa using hXJ_sum_le Finset.univ
    have hX'_card : X'.ncard ≤ r * v := by omega
    have hB'_le : ∀ i : Fin v, B' i ≤ G := fun i ↦ iSup₂_le fun j _ ↦ hB_le j
    have hB'_comp : ∀ i : Fin v, numComponents (B' i) ≤ r := by
      intro i
      have hJi_le : (J_seq i).ncard ≤ r := by
        dsimp [J_seq]
        have := hXJ_fn_card (J_rem i.1)
        omega
      exact (numComponents_biSup_le hfin B hB_le hB_conn (J_seq i)).trans hJi_le
    have hB'_disj : Pairwise fun i₁ i₂ : Fin v ↦ Disjoint (B' i₁).verts (B' i₂).verts := by
      intro i₁ i₂ hne
      simp only [B', Subgraph.verts_iSup]
      rw [Set.disjoint_iUnion₂_left]
      intro j₁ hj₁
      rw [Set.disjoint_iUnion₂_right]
      intro j₂ hj₂
      have hj_ne : j₁ ≠ j₂ := by
        rintro rfl
        exact (hJ_seq_disj hne).notMem_of_mem_left hj₁ hj₂
      exact hB_disj hj_ne
    have hB'_sep : ∀ i : Fin v, Separates G (X' ∪ (B' i).verts) A₁ A₂ := by
      intro i P hP hP_avoids
      rcases mem_iUnion₂.1 hP.2.1 with ⟨j, hj_not_J, hfirst_Bj⟩
      have hj_rem : j ∈ J_rem i.1 := by
        rw [hmem_J_rem_iff]
        intro t ht hjt
        have ht_v : t < v := ht.trans i.2
        exact hj_not_J (mem_iUnion.2 ⟨⟨t, ht_v⟩, hjt⟩)
      have hsep_i := hXJ_fn_sep (J_rem i.1) j hj_rem P ⟨hP.1, hfirst_Bj, hP.2.2⟩
      have hsub_sep : X_seq i ∪ ⋃ j' ∈ J_seq i, (B j').verts ⊆ X' ∪ (B' i).verts := by
        refine union_subset_union (subset_iUnion X_seq i) ?_
        simp [B', Subgraph.verts_iSup]
      exact hsep_i (hP_avoids.mono_right hsub_sep)
    -- Apply `theorem_2_8_simple` with `d = r` to show there cannot be `M = r * θ ^ 4 / 2` disjoint
    -- paths in `G` from `A₁` to `A₂` avoiding `X'`.
    let M := r * θ ^ 4 / 2
    have h_no_M_paths : ¬ ∃ P : Fin M → Path α,
        IsDisjointPathFamily G A₁ A₂ P ∧ ∀ k, (P k).Avoids X' := by
      rintro ⟨P, hP_fam, hP_avoids⟩
      have hs_pos : 0 < r + r := by omega
      have h28 := theorem_2_8_simple (d := r) (r := r) (m := M) (n := v) hθ heven hs_pos hfin hG
        hA₁_G hV' hX'_G hX'_card P hP_fam hP_avoids B' hB'_le hB'_comp hB'_disj hB'_sep
      dsimp only at h28
      have hs_eq : r + r * (θ ^ 2 - 1) = r * θ ^ 2 := by
        have hθ2_pos : 1 ≤ θ ^ 2 := by nlinarith
        zify [hθ2_pos]
        ring
      have hsθ2_eq : (r + r * (θ ^ 2 - 1)) * θ ^ 2 / 2 = M := by
        rw [hs_eq]
        have : r * θ ^ 2 * θ ^ 2 = r * θ ^ 4 := by ring
        rw [this]
      have hv_eq : 2 ^ M *
          (θ ^ 2 + 2 * (r + r * (θ ^ 2 - 1)) * θ ^ (2 * θ)) = v := by
        rw [hs_eq]
        dsimp [v, M]
        have hpow : 2 * (r * θ ^ 2) * θ ^ (2 * θ) = 2 * r * θ ^ (2 * θ + 2) := by
          calc
            2 * (r * θ ^ 2) * θ ^ (2 * θ) = 2 * r * (θ ^ (2 * θ) * θ ^ 2) := by ring
            _ = 2 * r * θ ^ (2 * θ + 2) := by rw [← pow_add]
        rw [hpow]
      rw [hsθ2_eq, hv_eq] at h28
      omega
    -- Apply Menger's theorem in `G.deleteVerts X'`.
    rcases exists_separator_of_no_disjoint_paths hfin X' A₁ A₂ h_no_M_paths with
      ⟨X'', hX''_G, hX''_card, hX''_sep⟩
    let X := X' ∪ X''
    refine ⟨X, J, union_subset hX'_G hX''_G, ?_, ?_⟩
    · calc
        X.ncard + J.ncard
          ≤ (X'.ncard + X''.ncard) + J.ncard :=
            Nat.add_le_add_right (Set.ncard_union_le X' X'') J.ncard
        _ = X''.ncard + (X'.ncard + J.ncard) := by ring
        _ ≤ M + r * v := Nat.add_le_add hX''_card.le hX'_J_card
        _ ≤ 2 ^ (r * θ ^ 4) := arith_2_9 hθ heven hr_pos
    · intro j hj_not_J
      have hsep_Bj : Separates G X (B j).verts V' := by
        intro P hP hP_avoids
        have hfirst_A₁ : P.first ∈ A₁ := mem_biUnion hj_not_J hP.2.1
        exact hX''_sep P ⟨hP.1, hfirst_A₁, hP.2.2⟩ hP_avoids
      exact hsep_Bj.symm

end GraphMinor.GM01
end
