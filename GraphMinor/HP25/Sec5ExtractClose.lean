module

public import GraphMinor.HP25.Sec5Extract
public import GraphMinor.HP25.Sec5Complete
public import GraphMinor.HP25.Sec5Search
public import GraphMinor.HP25.Sec5LiftSearch
public import GraphMinor.HP25.Sec5UndoExhaust
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.CrossTools
import GraphMinor.HP25.CycleEdges
import GraphMinor.HP25.Method
import GraphMinor.HP25.Prop52Converse
import GraphMinor.HP25.Completion

/-!
# Closing the crossing extraction: Rule 4, the residual subcase, and one-level search extraction

This file completes the crossing extraction of Section 5.3 of Humeau and Pous (see the correction
to Section 5.3 in `corrections/HP25.md`):

1. **Rule 4 and the residual subcase (`exists_rule_four_path_left`, `exists_rule_four_path_right`,
   `undo_of_bridge_rule_four_left`, `undo_of_bridge_rule_four_right`,
   `undo_of_bridge_residual_left`, `undo_of_bridge_residual_right`):**
   When both `y` and `s` are internal vertices of `P = L₁ ++ y :: N ++ s :: L₂` and the bridge
   `σ :: t :: K ++ [z]` from `σ ∈ N` to `z ∈ L₁` gives a rerouted path `P_new` that bypasses `y`
   while keeping `s ∈ P_new.support`, the side-`A` path `p_A` from `t` can reach `A` through an
   internal vertex `w` of `Q₂` (the `s`-side of `Q`) rather than `Q₁`. In that case `s ∈ P_new.support`
   can block `Q₂` from reaching `y` or `B` in `G - P_new`, so Rules 1, 2, and 3 all fail (`ExR3` in
   `Checks/HP25Examples.lean`).
   **Rule 4** resolves this residual subcase: splicing `y`'s (or `s`'s) side-`B` path `p_B` with the
   pocket segment `P[y..σ]` (or `P[σ..s]`) and a walk `q_A` from `σ` to `a₀ ∈ A` (either along the
   `A`-side of `R` from `σ` or a side-`A` path from `σ`) produces a `C`-path `R_new` in `G` between
   `B` and `A`; the walk along `P[a..z]`, the bridge `z :: K.reverse ++ [t]`, `p_A[t..w]`, and `Q₂`
   then avoids `R_new`, so searching `G - R_new` extracts a crossing of `C` in `G`.

2. **One-level extraction defined by searches (`CrossingWalks`, `searchCrossWalk`,
   `undoEdgeBySearches`, `liftSubCrossingBySearches`, `extractCrossingOneLevel`):**
   - `liftSubCrossingBySearches`: lifts a crossing `(Q_in, R_in)` of either subinstance of
     Proposition 5.1 along `P' = a :: m ++ [b]` to a crossing of `C` in `H` using Observations 1–3
     and the five cases of Figure 11 (`isCrossed_of_sub_crossed`), making at most `28` searches
     (`liftSubCrossingBySearches_searches_le`);
   - `undoEdgeBySearches`: removes one added edge `ys` from a crossing of `C` in `G₀ ⊔ edge y s`
     using Rules 1 to 4 (`searchCrossWalk`), making at most `44` searches (`O(1)`,
     `undoEdgeBySearches_searches_le`);
   - `extractCrossingOneLevel`: after `liftSubCrossingBySearches`, applies `undoEdgeBySearches` in
     reverse order to the added edges of one completion level (`undoChainBySearches`), returning a
     crossing of `C` in `G` (`extractCrossingOneLevel_valid`) in at most `28 + 44 * chain.length`
     searches, which is at most `72 * P'.support.length` when the chain is shorter than
     `P'.support` (`extractCrossingOneLevel_searches_le`, `O(|P'|)`).
-/

public section

namespace GraphMinor.HP25

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}
variable {C A B L₁ N L₂ : List V} {a b y s : V} {k : ℕ} {P : G.Walk a b}

/-! ### Part 1: Rule 4 and the residual subcase -/

/-- **Rule 4 path construction (`y`-side).** Given `σ ∈ N` on `P.support = L₁ ++ y :: N ++ s :: L₂`,
a walk `p_B : G.Walk y b₀` to `b₀ ∈ B` whose vertices other than `b₀` avoid `C`, and a walk
`q_A : G.Walk σ a₀` to `a₀ ∈ A` whose vertices other than `a₀` avoid `C`, concatenating `p_B.reverse`,
the pocket segment `y .. σ` of `P`, and `q_A` and bypassing produces a `C`-path `R_new : G.Walk b₀ a₀`
in `G` whose support is contained in `p_B.support ∪ (y :: N) ∪ q_A.support`. -/
theorem exists_rule_four_path_left [DecidableEq V] {σ b₀ a₀ : V}
    (_hCnd : C.Nodup) (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂) (hσ : σ ∈ N)
    (hb₀ : b₀ ∈ B) (ha₀ : a₀ ∈ A)
    (p_B : G.Walk y b₀) (hpB_C : ∀ w ∈ p_B.support, w ≠ b₀ → w ∉ C)
    (q_A : G.Walk σ a₀) (hqA_C : ∀ w ∈ q_A.support, w ≠ a₀ → w ∉ C) :
    ∃ R_new : G.Walk b₀ a₀, IsTPath G C R_new ∧
      ∀ w ∈ R_new.support, w ∈ p_B.support ∨ w ∈ y :: N ∨ w ∈ q_A.support := by
  obtain ⟨N₀, N₁, rfl⟩ := List.append_of_mem hσ
  have hch_N₀ : (y :: N₀ ++ [σ]).IsChain G.Adj := by
    have hch := P.isChain_adj_support
    rw [hsupp] at hch
    exact hch.infix ⟨L₁, N₁ ++ s :: L₂, by simp⟩
  obtain ⟨W_N₀, hW_N₀⟩ := exists_walk_of_chain (u := y) (v := σ) (y :: N₀ ++ [σ]) hch_N₀
    (by simp) (List.getLast?_concat ..)
  set W := p_B.reverse.append (W_N₀.append q_A)
  have hW_sub : ∀ w ∈ W.support, w ∈ p_B.support ∨ w ∈ y :: (N₀ ++ σ :: N₁) ∨ w ∈ q_A.support := by
    intro w hw
    rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse, hW_N₀] at hw
    rcases hw with hw | hw | hw
    · exact Or.inl hw
    · right; left
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hw ⊢
      tauto
    · exact Or.inr (Or.inr hw)
  have hb₀C : b₀ ∈ C := List.mem_rotate.mp (by rw [hrot]; simp [hb₀])
  have ha₀C : a₀ ∈ C := List.mem_rotate.mp (by rw [hrot]; simp [ha₀])
  refine ⟨W.bypass, ⟨W.bypass_isPath, hb₀C, ha₀C, fun w hw hwb hwa => ?_⟩,
    fun w hw => hW_sub w (W.support_bypass_subset_support hw)⟩
  have hwC : w ∉ C := by
    rcases hW_sub w (W.support_bypass_subset_support hw) with hwB | hwN | hwA
    · exact hpB_C w hwB hwb
    · rcases List.mem_cons.mp hwN with rfl | hwN'
      · exact hpB_C w p_B.start_mem_support hwb
      · exact not_mem_C_of_mem_window hP hsupp hwN'
    · exact hqA_C w hwA hwa
  exact ⟨hwC, hwC⟩

/-- **Rule 4 path construction (`s`-side).** Symmetrically, splicing `s`'s side-`B` walk
`p_B : G.Walk s b₀`, the pocket segment `s .. σ` of `P`, and `q_A : G.Walk σ a₀` and bypassing
produces a `C`-path `R_new : G.Walk b₀ a₀` in `G` whose support lies in
`p_B.support ∪ (s :: N) ∪ q_A.support`. -/
theorem exists_rule_four_path_right [DecidableEq V] {σ b₀ a₀ : V}
    (_hCnd : C.Nodup) (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂) (hσ : σ ∈ N)
    (hb₀ : b₀ ∈ B) (ha₀ : a₀ ∈ A)
    (p_B : G.Walk s b₀) (hpB_C : ∀ w ∈ p_B.support, w ≠ b₀ → w ∉ C)
    (q_A : G.Walk σ a₀) (hqA_C : ∀ w ∈ q_A.support, w ≠ a₀ → w ∉ C) :
    ∃ R_new : G.Walk b₀ a₀, IsTPath G C R_new ∧
      ∀ w ∈ R_new.support, w ∈ p_B.support ∨ w ∈ s :: N ∨ w ∈ q_A.support := by
  obtain ⟨N₀, N₁, rfl⟩ := List.append_of_mem hσ
  have hch_N₁ : (σ :: N₁ ++ [s]).IsChain G.Adj := by
    have hch := P.isChain_adj_support
    rw [hsupp] at hch
    exact hch.infix ⟨L₁ ++ y :: N₀, L₂, by simp⟩
  obtain ⟨W_N₁, hW_N₁⟩ := exists_walk_of_chain (u := σ) (v := s) (σ :: N₁ ++ [s]) hch_N₁
    (by simp) (List.getLast?_concat ..)
  set W := p_B.reverse.append (W_N₁.reverse.append q_A)
  have hW_sub : ∀ w ∈ W.support, w ∈ p_B.support ∨ w ∈ s :: (N₀ ++ σ :: N₁) ∨ w ∈ q_A.support := by
    intro w hw
    rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff, Walk.support_reverse,
      Walk.support_reverse, List.mem_reverse, List.mem_reverse, hW_N₁] at hw
    rcases hw with hw | hw | hw
    · exact Or.inl hw
    · right; left
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hw ⊢
      tauto
    · exact Or.inr (Or.inr hw)
  have hb₀C : b₀ ∈ C := List.mem_rotate.mp (by rw [hrot]; simp [hb₀])
  have ha₀C : a₀ ∈ C := List.mem_rotate.mp (by rw [hrot]; simp [ha₀])
  refine ⟨W.bypass, ⟨W.bypass_isPath, hb₀C, ha₀C, fun w hw hwb hwa => ?_⟩,
    fun w hw => hW_sub w (W.support_bypass_subset_support hw)⟩
  have hwC : w ∉ C := by
    rcases hW_sub w (W.support_bypass_subset_support hw) with hwB | hwN | hwA
    · exact hpB_C w hwB hwb
    · rcases List.mem_cons.mp hwN with rfl | hwN'
      · exact hpB_C w p_B.start_mem_support hwb
      · exact not_mem_C_of_mem_window hP hsupp hwN'
    · exact hqA_C w hwA hwa
  exact ⟨hwC, hwC⟩

/-- **Rule 4 from the bridge (`y`-side).** When `z ∈ L₁` (`L₁ = L₁₀ ++ z :: L₁₁`) and the side-`A`
walk from the bridge vertex `t` meets the `s`-side `Q₂` of `Q` at a vertex `w` via a walk
`p_tw : G.Walk t w`, concatenating `P[a..z]`, the bridge `z :: K.reverse ++ [t]`, `p_tw`, and
`Q₂[w..v₁]` gives a walk `W_cross` in `G` from `a` to `v₁`. Whenever `Alternate C a v₁ b₀ a₀` and
`W_cross` avoids `p_B.support ∪ (y :: N) ∪ q_A.support`, `W_cross` avoids the Rule 4 `C`-path
`R_new : G.Walk b₀ a₀`, so searching `G - R_new` (Rule 4) extracts a crossing of `C` in `G`. -/
theorem undo_of_bridge_rule_four_left [DecidableEq V] {K : List V} {σ t z w v₁ b₀ a₀ : V}
    (hCnd : C.Nodup) (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂) (hσ : σ ∈ N) (hz : z ∈ L₁)
    (hcM : (σ :: t :: K ++ [z]).IsChain G.Adj)
    (hb₀ : b₀ ∈ B) (ha₀ : a₀ ∈ A)
    (p_B : G.Walk y b₀) (hpB_C : ∀ x ∈ p_B.support, x ≠ b₀ → x ∉ C)
    (q_A : G.Walk σ a₀) (hqA_C : ∀ x ∈ q_A.support, x ≠ a₀ → x ∉ C)
    (p_tw : G.Walk t w) (q₂ : G.Walk w v₁) (halt : Alternate C a v₁ b₀ a₀)
    (havoid : ∀ x, (x ∈ L₁ ∨ x ∈ t :: K ∨ x ∈ p_tw.support ∨ x ∈ q₂.support) →
      x ∉ p_B.support ∧ x ∉ y :: N ∧ x ∉ q_A.support) :
    IsCrossed G C := by
  obtain ⟨R_new, hR_new, hR_sub⟩ :=
    exists_rule_four_path_left hCnd hrot hP hsupp hσ hb₀ ha₀ p_B hpB_C q_A hqA_C
  obtain ⟨L₁₀, L₁₁, rfl⟩ := List.append_of_mem hz
  have hch_az : (L₁₀ ++ [z]).IsChain G.Adj := by
    have hch := P.isChain_adj_support
    rw [hsupp] at hch
    exact hch.infix ⟨[], L₁₁ ++ y :: N ++ s :: L₂, by simp⟩
  have hhead_az : (L₁₀ ++ [z]).head? = some a := by
    have h0 : P.support.head? = some a := by rw [← Walk.cons_tail_support]; rfl
    rw [hsupp] at h0
    cases L₁₀ <;> simpa using h0
  obtain ⟨W_az, hW_az⟩ := exists_walk_of_chain (u := a) (v := z) (L₁₀ ++ [z]) hch_az
    hhead_az (List.getLast?_concat ..)
  have hch_zt : (z :: K.reverse ++ [t]).IsChain G.Adj := by
    have hc_tkz : (t :: K ++ [z]).IsChain G.Adj := (List.isChain_cons_cons.mp hcM).2
    have hrev : (t :: K ++ [z]).reverse = z :: K.reverse ++ [t] := by simp
    rw [← hrev, List.isChain_reverse]
    exact hc_tkz.imp fun _ _ h => h.symm
  obtain ⟨W_zt, hW_zt⟩ := exists_walk_of_chain (u := z) (v := t) (z :: K.reverse ++ [t]) hch_zt
    (by simp) (List.getLast?_concat ..)
  set W_cross := W_az.append (W_zt.append (p_tw.append q₂))
  refine isCrossed_of_walk_avoiding halt hR_new W_cross fun x hx hxR => ?_
  have hx_in : x ∈ L₁₀ ++ z :: L₁₁ ∨ x ∈ t :: K ∨ x ∈ p_tw.support ∨ x ∈ q₂.support := by
    rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff, Walk.mem_support_append_iff,
      hW_az, hW_zt] at hx
    rcases hx with hx | hx | hx | hx
    · left
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      tauto
    · simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_reverse,
        List.not_mem_nil, or_false] at hx
      rcases hx with rfl | hx | rfl
      · exact Or.inl (by simp)
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ hx))
      · exact Or.inr (Or.inl List.mem_cons_self)
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr hx))
  have hno := havoid x hx_in
  rcases hR_sub x hxR with h1 | h2 | h3
  · exact hno.1 h1
  · exact hno.2.1 h2
  · exact hno.2.2 h3

/-- **Rule 4 from the bridge (`s`-side).** Symmetrically, when `z ∈ L₂` and the walk from `t` hits
`Q₁` (the `u₁`–`y` part of `Q`) at `w` via `p_tw : G.Walk t w` and `q₁ : G.Walk w u₁`, concatenating
`P[b..z]`, `z :: K.reverse ++ [t]`, `p_tw`, and `q₁` gives a walk from `b` to `u₁` avoiding the
`s`-side Rule 4 path `R_new : G.Walk b₀ a₀`, so searching `G - R_new` extracts a crossing of `C` in
`G`. -/
theorem undo_of_bridge_rule_four_right [DecidableEq V] {K : List V} {σ t z w u₁ b₀ a₀ : V}
    (hCnd : C.Nodup) (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂) (hσ : σ ∈ N) (hz : z ∈ L₂)
    (hcM : (σ :: t :: K ++ [z]).IsChain G.Adj)
    (hb₀ : b₀ ∈ B) (ha₀ : a₀ ∈ A)
    (p_B : G.Walk s b₀) (hpB_C : ∀ x ∈ p_B.support, x ≠ b₀ → x ∉ C)
    (q_A : G.Walk σ a₀) (hqA_C : ∀ x ∈ q_A.support, x ≠ a₀ → x ∉ C)
    (p_tw : G.Walk t w) (q₁ : G.Walk w u₁) (halt : Alternate C b u₁ b₀ a₀)
    (havoid : ∀ x, (x ∈ L₂ ∨ x ∈ t :: K ∨ x ∈ p_tw.support ∨ x ∈ q₁.support) →
      x ∉ p_B.support ∧ x ∉ s :: N ∧ x ∉ q_A.support) :
    IsCrossed G C := by
  obtain ⟨R_new, hR_new, hR_sub⟩ :=
    exists_rule_four_path_right hCnd hrot hP hsupp hσ hb₀ ha₀ p_B hpB_C q_A hqA_C
  obtain ⟨L₂₀, L₂₁, rfl⟩ := List.append_of_mem hz
  have hch_zb : (z :: L₂₁).IsChain G.Adj := by
    have hch := P.isChain_adj_support
    rw [hsupp] at hch
    exact hch.infix ⟨L₁ ++ y :: N ++ s :: L₂₀, [], by simp⟩
  have hlast_zb : (z :: L₂₁).getLast? = some b := by
    have h0 : P.support.getLast? = some b := by
      rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
    rw [hsupp, show L₁ ++ y :: N ++ s :: (L₂₀ ++ z :: L₂₁) =
      (L₁ ++ y :: N ++ s :: L₂₀) ++ (z :: L₂₁) by simp,
      List.getLast?_append_of_ne_nil _ (by simp)] at h0
    exact h0
  obtain ⟨W_zb, hW_zb⟩ := exists_walk_of_chain (u := z) (v := b) (z :: L₂₁) hch_zb
    (by simp) hlast_zb
  have hch_zt : (z :: K.reverse ++ [t]).IsChain G.Adj := by
    have hc_tkz : (t :: K ++ [z]).IsChain G.Adj := (List.isChain_cons_cons.mp hcM).2
    have hrev : (t :: K ++ [z]).reverse = z :: K.reverse ++ [t] := by simp
    rw [← hrev, List.isChain_reverse]
    exact hc_tkz.imp fun _ _ h => h.symm
  obtain ⟨W_zt, hW_zt⟩ := exists_walk_of_chain (u := z) (v := t) (z :: K.reverse ++ [t]) hch_zt
    (by simp) (List.getLast?_concat ..)
  set W_cross := W_zb.reverse.append (W_zt.append (p_tw.append q₁))
  refine isCrossed_of_walk_avoiding halt hR_new W_cross fun x hx hxR => ?_
  have hx_in : x ∈ L₂₀ ++ z :: L₂₁ ∨ x ∈ t :: K ∨ x ∈ p_tw.support ∨ x ∈ q₁.support := by
    rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff, Walk.mem_support_append_iff,
      Walk.support_reverse, List.mem_reverse, hW_zb, hW_zt] at hx
    rcases hx with hx | hx | hx | hx
    · exact Or.inl (by simp [hx])
    · simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_reverse,
        List.not_mem_nil, or_false] at hx
      rcases hx with rfl | hx | rfl
      · exact Or.inl (by simp)
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ hx))
      · exact Or.inr (Or.inl List.mem_cons_self)
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inr (Or.inr (Or.inr hx))
  have hno := havoid x hx_in
  rcases hR_sub x hxR with h1 | h2 | h3
  · exact hno.1 h1
  · exact hno.2.1 h2
  · exact hno.2.2 h3

/-- **The residual subcase dichotomy (`y`-side): Rule 3 or Rule 4.** When `z ∈ L₁` gives the
rerouted path `P_new : G.Walk a b` missing `y`, either `y` reaches `A` off `P_new` (so Rule 3
extracts a crossing of `C` in `G` via `undo_of_bridge_rule_three_left`), or the walk from `t` through
`Q₂` avoids the Rule 4 path `R_new` (so Rule 4 extracts a crossing of `C` in `G` via
`undo_of_bridge_rule_four_left`). -/
theorem undo_of_bridge_residual_left [DecidableEq V] {K : List V} {σ t z w v₁ b₀ a₀ : V}
    (hCnd : C.Nodup) (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    (hN : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
    (hyB : IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} y)
    (hσ : σ ∈ N) (hz : z ∈ L₁) (hcM : (σ :: t :: K ++ [z]).IsChain G.Adj)
    (hK : ∀ x ∈ t :: K, x ∉ C ∧ x ∉ P.support)
    {P_new : G.Walk a b} (hP_new : IsTPath G C P_new)
    (hsub : ∀ x ∈ P_new.support, x ∈ P.support ∨ x ∈ t :: K) (hyP : y ∉ P_new.support)
    (hb₀ : b₀ ∈ B) (ha₀ : a₀ ∈ A)
    (p_B : G.Walk y b₀) (hpB_C : ∀ x ∈ p_B.support, x ≠ b₀ → x ∉ C)
    (q_A : G.Walk σ a₀) (hqA_C : ∀ x ∈ q_A.support, x ≠ a₀ → x ∉ C)
    (p_tw : G.Walk t w) (q₂ : G.Walk w v₁)
    (hdich : ReachesOff G P_new.support A y ∨
      (Alternate C a v₁ b₀ a₀ ∧
        ∀ x, (x ∈ L₁ ∨ x ∈ t :: K ∨ x ∈ p_tw.support ∨ x ∈ q₂.support) →
          x ∉ p_B.support ∧ x ∉ y :: N ∧ x ∉ q_A.support)) :
    IsCrossed G C := by
  rcases hdich with hyA | ⟨halt, havoid⟩
  · exact undo_of_bridge_rule_three_left hCnd hrot hP hsupp hN hyB hσ hcM hK hP_new hsub hyP hyA
  · exact undo_of_bridge_rule_four_left hCnd hrot hP hsupp hσ hz hcM hb₀ ha₀ p_B hpB_C q_A hqA_C
      p_tw q₂ halt havoid

/-- **The residual subcase dichotomy (`s`-side): Rule 3 or Rule 4.** Symmetrically for `z ∈ L₂`. -/
theorem undo_of_bridge_residual_right [DecidableEq V] {K : List V} {σ t z w u₁ b₀ a₀ : V}
    (hCnd : C.Nodup) (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    (hN : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
    (hsB : IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} s)
    (hσ : σ ∈ N) (hz : z ∈ L₂) (hcM : (σ :: t :: K ++ [z]).IsChain G.Adj)
    (hK : ∀ x ∈ t :: K, x ∉ C ∧ x ∉ P.support)
    {P_new : G.Walk a b} (hP_new : IsTPath G C P_new)
    (hsub : ∀ x ∈ P_new.support, x ∈ P.support ∨ x ∈ t :: K) (hsP : s ∉ P_new.support)
    (hb₀ : b₀ ∈ B) (ha₀ : a₀ ∈ A)
    (p_B : G.Walk s b₀) (hpB_C : ∀ x ∈ p_B.support, x ≠ b₀ → x ∉ C)
    (q_A : G.Walk σ a₀) (hqA_C : ∀ x ∈ q_A.support, x ≠ a₀ → x ∉ C)
    (p_tw : G.Walk t w) (q₁ : G.Walk w u₁)
    (hdich : ReachesOff G P_new.support A s ∨
      (Alternate C b u₁ b₀ a₀ ∧
        ∀ x, (x ∈ L₂ ∨ x ∈ t :: K ∨ x ∈ p_tw.support ∨ x ∈ q₁.support) →
          x ∉ p_B.support ∧ x ∉ s :: N ∧ x ∉ q_A.support)) :
    IsCrossed G C := by
  rcases hdich with hsA | ⟨halt, havoid⟩
  · exact undo_of_bridge_rule_three_right hCnd hrot hP hsupp hN hsB hσ hcM hK hP_new hsub hsP hsA
  · exact undo_of_bridge_rule_four_right hCnd hrot hP hsupp hσ hz hcM hb₀ ha₀ p_B hpB_C q_A hqA_C
      p_tw q₁ halt havoid

/-! ### Part 2: Computable one-level search extraction, soundness, and `O(|P'|)` search bound -/

/-- **Data of one added-edge step `(G₀, P₀, y, s)` in the completion of `(G, P)`.**
Each unskipped collapse edge and each loop edge adds `edge y s` across a pocket `N` of an induced,
separating, tight `C`-path `P₀` of `G₀`, where either `y, s` are on side `B` and `N` is off side `B`
(`strip_safe`) or `y, s` are on side `A` and `N` is off side `A` (`strip_safe_rev`). -/
structure AddedEdgeStep (V : Type*) (C A B : List V) (a b : V) (k : ℕ) where
  /-- Graph before adding the edge `y s`. -/
  G₀ : SimpleGraph V
  /-- First endpoint of the added edge. -/
  y : V
  /-- Second endpoint of the added edge. -/
  s : V
  /-- Prefix of `P₀` before `y`. -/
  L₁ : List V
  /-- Pocket of `P₀` strictly between `y` and `s`. -/
  N : List V
  /-- Suffix of `P₀` after `s`. -/
  L₂ : List V
  /-- The `C`-path `P₀` before adding `y s`. -/
  P₀ : G₀.Walk a b
  /-- `C` is a cycle of `G₀`. -/
  hC : IsCycleList G₀ C
  /-- `C` rotated by `k` is `a :: A ++ b :: B`. -/
  hrot : C.rotate k = a :: A ++ b :: B
  /-- `P₀` is a `C`-path of `G₀`. -/
  hP₀ : IsTPath G₀ C P₀
  /-- Support decomposition `P₀.support = L₁ ++ y :: N ++ s :: L₂`. -/
  hsupp : P₀.support = L₁ ++ y :: N ++ s :: L₂
  /-- `P₀` is induced in `G₀`. -/
  hind : ∀ u ∈ P₀.support, ∀ v ∈ P₀.support, G₀.Adj u v → IsListEdge P₀.support u v
  /-- `P₀` separates `A` from `B` in `G₀`. -/
  hsep : Separates G₀ {v | v ∈ P₀.support} {v | v ∈ A} {v | v ∈ B}
  /-- `P₀` is tight in `G₀`. -/
  htight : IsTight G₀ C A B P₀.support
  /-- Either `y, s` are on side `B` with `N` off side `B`, or `y, s` are on side `A` with `N` off
  side `A`. -/
  hstrip :
    (IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ B} y ∧
      IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ B} s ∧
      ∀ v ∈ N, ¬ IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ B} v) ∨
    (IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ A} y ∧
      IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ A} s ∧
      ∀ v ∈ N, ¬ IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ A} v)

/-- The graph after adding `edge step.y step.s`. -/
@[expose] def AddedEdgeStep.G₁ (step : AddedEdgeStep V C A B a b k) : SimpleGraph V :=
  step.G₀ ⊔ edge step.y step.s

/-- Every `AddedEdgeStep` is safe for `C` (`strip_safe` / `strip_safe_rev`). -/
theorem AddedEdgeStep.isSafe [Finite V] (step : AddedEdgeStep V C A B a b k) :
    IsSafe step.G₀ (edge step.y step.s) C := by
  rcases step.hstrip with ⟨hy, hs, hN⟩ | ⟨hy, hs, hN⟩
  · exact strip_safe step.hC step.hrot step.hP₀ step.hsupp step.hind step.htight hy hs hN
  · exact strip_safe_rev step.hC step.hrot step.hP₀ step.hsupp step.hind step.htight hy hs hN

/-- Computably construct the candidate walks in `step.G₀` for Rules 1 to 4 from `step` and the
supports `Q_supp`, `R_supp` of the crossing paths (`Q` using `s(y, s)`, `R` in `step.G₀`).
Uses `8` `findWalkFromTo` side-path searches and produces at most `36` candidate walks. -/
@[expose] def undoEdgeCandidateWalks [DecidableEq V] [WalkSearch V]
    (step : AddedEdgeStep V C A B a b k) [DecidableRel step.G₀.Adj]
    (verts : List V) (Q_supp R_supp : List V) :
    List (Σ u v : V, step.G₀.Walk u v) :=
  (undoEdgeCandidateChains step.G₀ verts C A B step.P₀.support step.L₁ step.N step.L₂
    step.y step.s Q_supp R_supp).filterMap (walkOfChainOption step.G₀)

theorem undoEdgeCandidateWalks_length_le [DecidableEq V] [WalkSearch V]
    (step : AddedEdgeStep V C A B a b k) [DecidableRel step.G₀.Adj]
    (verts : List V) (Q_supp R_supp : List V) :
    (undoEdgeCandidateWalks step verts Q_supp R_supp).length ≤ 36 := by
  refine (List.length_filterMap_le _ _).trans_eq ?_
  exact undoEdgeCandidateChains_length step.G₀ verts C A B step.P₀.support step.L₁ step.N step.L₂
    step.y step.s Q_supp R_supp

/-- **Undoing one added edge by searches (`undoEdgeBySearches`), with no fallback.**
Given an `AddedEdgeStep` `step`, the vertex list `verts`, and a crossing `cr` of `C` in
`step.G₁ = step.G₀ ⊔ edge y s`:
1. If both `cr.Q` and `cr.R` transfer directly to `step.G₀` via `transferWalkOption`, return the
   transferred crossing in `step.G₀` with `0` searches.
2. Otherwise, compute the candidate walks `cands` of Rules 1 to 4 (`undoEdgeCandidateWalks`, using
   `8` side-walk searches) from `step` and `cr`, and run `runCandidateSearches step.G₀ verts C cands`
   (at most `36` crossing searches, for at most `44` searches total).
Purely computable (`Option`-returning, no `IsCrossed`, no `Classical.choice`, no fallback). -/
@[expose] def undoEdgeBySearches [DecidableEq V] [WalkSearch V]
    (step : AddedEdgeStep V C A B a b k) [DecidableRel step.G₀.Adj]
    (verts : List V) (cr : CrossingWalks step.G₁ C) :
    Option (CrossingWalks step.G₀ C) × ℕ :=
  match transferWalkOption (G := step.G₀) cr.Q, transferWalkOption (G := step.G₀) cr.R with
  | some Q₀, some R₀ =>
    (some ⟨cr.u₁, cr.v₁, cr.u₂, cr.v₂, Q₀, R₀⟩, 0)
  | none, _ =>
    let cands := undoEdgeCandidateWalks step verts cr.Q.support cr.R.support
    let res := runCandidateSearches step.G₀ verts C cands
    (res.1, 8 + res.2)
  | some _, none =>
    let cands := undoEdgeCandidateWalks step verts cr.R.support cr.Q.support
    let res := runCandidateSearches step.G₀ verts C cands
    (res.1, 8 + res.2)

/-- Every crossing returned by `undoEdgeBySearches` is a valid crossing of `C` in `step.G₀`
whenever `cr` is a valid crossing of `C` in `step.G₁`. -/
theorem undoEdgeBySearches_valid [DecidableEq V] [WalkSearch V] [LawfulWalkSearch V]
    (step : AddedEdgeStep V C A B a b k) [DecidableRel step.G₀.Adj]
    (verts : List V) {cr : CrossingWalks step.G₁ C} (hcr : cr.Valid)
    {cr₀ : CrossingWalks step.G₀ C} (h : (undoEdgeBySearches step verts cr).1 = some cr₀) :
    cr₀.Valid := by
  unfold undoEdgeBySearches at h
  rcases hQ : transferWalkOption (G := step.G₀) cr.Q with _ | Q₀ <;>
    rcases hR : transferWalkOption (G := step.G₀) cr.R with _ | R₀ <;>
    rw [hQ, hR] at h
  · exact runCandidateSearches_valid h
  · exact runCandidateSearches_valid h
  · exact runCandidateSearches_valid h
  · simp only [Option.some.injEq] at h
    subst h
    refine ⟨hcr.1, transferWalkOption_isTPath hQ hcr.2.1, transferWalkOption_isTPath hR hcr.2.2.1, ?_⟩
    rw [transferWalkOption_support hQ, transferWalkOption_support hR]
    exact hcr.2.2.2

/-- `undoEdgeBySearches` makes at most `44` searches (`O(1)`). -/
theorem undoEdgeBySearches_searches_le [DecidableEq V] [WalkSearch V]
    (step : AddedEdgeStep V C A B a b k) [DecidableRel step.G₀.Adj]
    (verts : List V) (cr : CrossingWalks step.G₁ C) :
    (undoEdgeBySearches step verts cr).2 ≤ 44 := by
  unfold undoEdgeBySearches
  have hQ_len := (runCandidateSearches_searches_le step.G₀ verts C
    (undoEdgeCandidateWalks step verts cr.Q.support cr.R.support)).trans
    (undoEdgeCandidateWalks_length_le step verts cr.Q.support cr.R.support)
  have hR_len := (runCandidateSearches_searches_le step.G₀ verts C
    (undoEdgeCandidateWalks step verts cr.R.support cr.Q.support)).trans
    (undoEdgeCandidateWalks_length_le step verts cr.R.support cr.Q.support)
  rcases transferWalkOption (G := step.G₀) cr.Q with _ | Q₀ <;>
    rcases transferWalkOption (G := step.G₀) cr.R with _ | R₀ <;>
    dsimp only <;> omega

/-- For any valid crossing `cr` of `C` in `step.G₁`, at least one of `cr.Q` and `cr.R` avoids
`s(step.y, step.s)` and therefore transfers to `step.G₀` via `transferWalkOption`. -/
theorem transferWalkOption_or_isSome_of_valid [DecidableEq V]
    (step : AddedEdgeStep V C A B a b k) [DecidableRel step.G₀.Adj]
    {cr : CrossingWalks step.G₁ C} (hcr : cr.Valid) :
    (transferWalkOption (G := step.G₀) cr.Q).isSome = true ∨
      (transferWalkOption (G := step.G₀) cr.R).isSome = true := by
  rcases hQ : transferWalkOption (G := step.G₀) cr.Q with _ | Q₀
  · rcases hR : transferWalkOption (G := step.G₀) cr.R with _ | R₀
    · exfalso
      have heQ := mem_edges_of_transferWalkOption_none hQ
      have heR := mem_edges_of_transferWalkOption_none hR
      exact hcr.2.2.2 (cr.Q.fst_mem_support_of_mem_edges heQ)
        (cr.R.fst_mem_support_of_mem_edges heR)
    · exact Or.inr rfl
  · exact Or.inl rfl

/-- **Case 3 bridge dichotomy for `undoEdgeCandidateWalks` (`BridgeSearchExhaustive`):**
When `R₀` meets both the pocket `step.N` and the lower world, so `bridgeOfList step.N (step.L₁ ++ step.L₂) L`
on `L ∈ {R₀.support, R₀.support.reverse}` extracts a bridge `(σ, t :: K, z)` with `σ ∈ step.N`,
`z ∈ step.L₁ ∨ z ∈ step.L₂`, `t :: K` off `C ∪ step.P₀.support ∪ Q.support`, and rerouted `C`-path
`P_new : step.G₀.Walk a b`, one of the following three rules applies:
- **Subcase 3a (Rule 2):** there is a walk `W : step.G₀.Walk c d` between `c, d` with
  `Alternate C c d u₁ v₁` that avoids `Q.support ∪ step.N`;
- **Subcase 3b (Rule 3):** the rerouted `C`-path `P_new` fails to separate `A` from `B` in `step.G₀`;
- **Subcase 3c (Rule 4):** one of the `16` candidate chains `X ∈ rule4ChainsForSigma ... σ` is a
  `step.G₀.Adj`-chain between `c ∈ C` and `d ∈ C` with internal vertices off `C`, and there is a
  walk `W : step.G₀.Walk u v` with `Alternate C u v c d` avoiding `X`. -/
@[expose] def BridgeSearchExhaustive [DecidableEq V] [WalkSearch V]
    (step : AddedEdgeStep V C A B a b k) [DecidableRel step.G₀.Adj]
    (verts : List V) {u₁ v₁ u₂ v₂ : V}
    (Q : step.G₁.Walk u₁ v₁) (R₀ : step.G₀.Walk u₂ v₂) : Prop :=
  ∀ {L : List V} (_hL_or : L = R₀.support ∨ L = R₀.support.reverse)
    {σ t z : V} {K : List V}
    (_hb : bridgeOfList step.N (step.L₁ ++ step.L₂) L = some (σ, t :: K, z))
    (_hσ : σ ∈ step.N) (_hz : z ∈ step.L₁ ∨ z ∈ step.L₂)
    (_hcM : (σ :: t :: K ++ [z]).IsChain step.G₀.Adj)
    (_hndM : (σ :: t :: K ++ [z]).Nodup)
    (_hK : ∀ w ∈ t :: K, w ∈ R₀.support ∧ w ∉ C ∧ w ∉ step.P₀.support ∧ w ∉ Q.support ∧
      ¬ IsThirdKind step.G₀ C A B step.P₀.support w)
    {P_new : step.G₀.Walk a b} (_hP_new : IsTPath step.G₀ C P_new)
    (_hr3_eq : rule3ChainOfBridge step.P₀.support step.L₁ (some (σ, t :: K, z)) = P_new.support)
    (_hsub : ∀ w ∈ P_new.support, w ∈ step.P₀.support ∨ w ∈ t :: K)
    (_hmiss : (z ∈ step.L₁ ∧ step.y ∉ P_new.support) ∨ (z ∈ step.L₂ ∧ step.s ∉ P_new.support)),
    (∃ c d : V, ∃ W : step.G₀.Walk c d,
      Alternate C c d u₁ v₁ ∧ ∀ w ∈ W.support, w ∉ Q.support ∧ w ∉ step.N) ∨
    ¬ Separates step.G₀ {v | v ∈ P_new.support} {v | v ∈ A} {v | v ∈ B} ∨
    ∃ (X : List V) (u v c d : V) (W : step.G₀.Walk u v),
      X ∈ rule4ChainsForSigma step.N R₀.support
        (sideWalkSupport step.G₀ verts C step.P₀.support step.y B)
        (sideWalkSupport step.G₀ verts C step.P₀.support step.s B)
        (sideWalkSupport step.G₀ verts C step.P₀.support step.y A)
        (sideWalkSupport step.G₀ verts C step.P₀.support step.s A)
        (sideWalkSupport step.G₀ verts C step.P₀.support σ A)
        (sideWalkSupport step.G₀ verts C step.P₀.support σ B) σ ∧
      X.IsChain step.G₀.Adj ∧ X.head? = some c ∧ X.getLast? = some d ∧
      c ∈ C ∧ d ∈ C ∧ (∀ w ∈ X, w ∈ C → w = c ∨ w = d) ∧
      Alternate C u v c d ∧ ∀ w ∈ W.support, w ∉ X

/-- **Exhaustiveness and search completeness of `undoEdgeCandidateWalks`:**
For any `step : AddedEdgeStep V C A B a b k` and any crossing `(Q, R₀)` of `C` in `step.G₁`
where `s(step.y, step.s) ∈ Q.edges` and `R₀` is in `step.G₀`:
- **Case 1 (`R₀` misses `step.N`)** and **Case 2 (`R₀` misses the side-`B` / side-`A` lower world)**
  succeed unconditionally via candidate `r1 = R₀.support`;
- **Case 3 (`R₀` meets both `step.N` and the lower world)** extracts a bridge `(σ, t :: K, z)` via
  `bridgeOfList` on `R₀.support` or `R₀.support.reverse` and succeeds via Rules 2, 3, or 4 whenever
  `BridgeSearchExhaustive` holds on that bridge. -/
theorem undoEdgeCandidateWalks_isSome_of_bridge_exhaustive [DecidableEq V]
    [WalkSearch V] [LawfulWalkSearch V]
    (step : AddedEdgeStep V C A B a b k) [DecidableRel step.G₀.Adj]
    {verts : List V} (hverts : ∀ v : V, v ∈ verts)
    {u₁ v₁ u₂ v₂ : V} (Q : step.G₁.Walk u₁ v₁) (R₀ : step.G₀.Walk u₂ v₂)
    (halt : Alternate C u₁ v₁ u₂ v₂ ∨ Alternate C v₁ u₁ u₂ v₂)
    (hQ : IsTPath step.G₁ C Q) (hQe : s(step.y, step.s) ∈ Q.edges)
    (hR₀ : IsTPath step.G₀ C R₀) (hdisj : Q.support.Disjoint R₀.support)
    (hbr : BridgeSearchExhaustive step verts Q R₀) :
    (runCandidateSearches step.G₀ verts C
      (undoEdgeCandidateWalks step verts Q.support R₀.support)).1.isSome = true := by
  unfold undoEdgeCandidateWalks
  have hCnd : C.Nodup := step.hC.2.1
  -- Case 1: `R₀` misses `step.N`
  by_cases hRN : ∀ x ∈ step.N, x ∉ R₀.support
  · exact undoEdgeCandidateWalks_isSome_of_pocket_free hverts hCnd step.hsupp Q R₀ halt
      hQ hQe hR₀ hdisj hRN
  push Not at hRN
  obtain ⟨w₀, hw₀N, hw₀R⟩ := hRN
  -- Split on the two symmetric cases of `step.hstrip` (`B`-side or `A`-side)
  rcases step.hstrip with ⟨hyB, hsB, hNB⟩ | ⟨hyA, hsA, hNA⟩
  · -- Case 2 (`B`-side): `R₀` misses the `B`-side lower world
    by_cases hRL : ∀ x ∈ R₀.support, x ∉ B ∧
        ¬ (x ∉ {x | x ∈ C ∨ x ∈ step.P₀.support} ∧
          IsConnectedAvoiding step.G₀ {x | x ∈ C ∨ x ∈ step.P₀.support} x {x | x ∈ B})
    · exact undoEdgeCandidateWalks_isSome_of_lower_free hverts step.hC step.hrot hyB hsB Q R₀
        halt hQ hQe hR₀ hdisj hRL
    -- Case 3 (`B`-side): `R₀` meets both `step.N` and the `B`-side lower world
    have hRL' : ∃ w₁ ∈ R₀.support, w₁ ∈ B ∨ (w₁ ∉ {x | x ∈ C ∨ x ∈ step.P₀.support} ∧
        IsConnectedAvoiding step.G₀ {x | x ∈ C ∨ x ∈ step.P₀.support} w₁ {x | x ∈ B}) := by
      by_contra hno
      apply hRL
      intro x hxR
      exact ⟨fun hxB => hno ⟨x, hxR, Or.inl hxB⟩, fun hxC => hno ⟨x, hxR, Or.inr hxC⟩⟩
    obtain ⟨w₁, hw₁R, hw₁B⟩ := hRL'
    have hBC : ∀ x ∈ B, x ∈ C ∧ x ∉ step.P₀.support := fun x hx =>
      ⟨List.mem_rotate.mp (by rw [step.hrot]; simp [hx]),
        notMem_support_of_arc hCnd step.hrot step.hP₀ (Or.inr hx)⟩
    obtain ⟨L, hL_or, hb_some⟩ :=
      exists_bridgeOfList_of_meets_pocket_and_side step.hP₀ step.hsupp hBC hNB Q R₀ hQe hR₀ hdisj
        hw₀R hw₀N hw₁R hw₁B
    obtain ⟨⟨σ, M, z⟩, hb⟩ := Option.isSome_iff_exists.mp hb_some
    obtain ⟨t, K, rfl, hσN, hzL, hch_M, hnd_M, hK_props⟩ :=
      bridgeOfList_props_of_mem_R hCnd step.hrot step.hP₀ step.hsupp step.hind step.htight
        Q R₀ hQe hR₀ hdisj hL_or hb
    obtain ⟨P_new, hP_new, hr3_eq, hsub, hmiss⟩ :=
      rule3ChainOfBridge_spec step.hP₀ step.hsupp hσN hzL hch_M hnd_M
        fun w hw => ⟨(hK_props w hw).2.1, (hK_props w hw).2.2.1⟩
    rcases hbr hL_or hb hσN hzL hch_M hnd_M hK_props hP_new hr3_eq hsub hmiss with
      ⟨c, d, W, halt_r2, hW_r2⟩ | hns_r3 |
      ⟨X, u, v, c, d, W, hX_mem, hX_ch, hh, hl, hc, hd, hin, halt_r4, hW_r4⟩
    · exact undoEdgeCandidateWalks_isSome_of_rule_two hverts hCnd step.hP₀ step.hsupp Q R₀.support
        hQ hQe halt_r2 W hW_r2
    · exact undoEdgeCandidateWalks_isSome_of_rule_three Q.support R₀.support hverts hCnd step.hrot
        hL_or hb hP_new hr3_eq hns_r3
    · exact undoEdgeCandidateWalks_isSome_of_rule_four Q.support R₀.support hverts hCnd hL_or hb
        hX_mem hX_ch hh hl hc hd hin halt_r4 W hW_r4
  · -- Case 2 (`A`-side): `R₀` misses the `A`-side world
    by_cases hRU : ∀ x ∈ R₀.support, x ∉ A ∧
        ¬ (x ∉ {x | x ∈ C ∨ x ∈ step.P₀.support} ∧
          IsConnectedAvoiding step.G₀ {x | x ∈ C ∨ x ∈ step.P₀.support} x {x | x ∈ A})
    · exact undoEdgeCandidateWalks_isSome_of_upper_free hverts step.hC step.hrot hyA hsA Q R₀
        halt hQ hQe hR₀ hdisj hRU
    -- Case 3 (`A`-side): `R₀` meets both `step.N` and the `A`-side world
    have hRU' : ∃ w₁ ∈ R₀.support, w₁ ∈ A ∨ (w₁ ∉ {x | x ∈ C ∨ x ∈ step.P₀.support} ∧
        IsConnectedAvoiding step.G₀ {x | x ∈ C ∨ x ∈ step.P₀.support} w₁ {x | x ∈ A}) := by
      by_contra hno
      apply hRU
      intro x hxR
      exact ⟨fun hxA => hno ⟨x, hxR, Or.inl hxA⟩, fun hxC => hno ⟨x, hxR, Or.inr hxC⟩⟩
    obtain ⟨w₁, hw₁R, hw₁A⟩ := hRU'
    have hAC : ∀ x ∈ A, x ∈ C ∧ x ∉ step.P₀.support := fun x hx =>
      ⟨List.mem_rotate.mp (by rw [step.hrot]; simp [hx]),
        notMem_support_of_arc hCnd step.hrot step.hP₀ (Or.inl hx)⟩
    obtain ⟨L, hL_or, hb_some⟩ :=
      exists_bridgeOfList_of_meets_pocket_and_side step.hP₀ step.hsupp hAC hNA Q R₀ hQe hR₀ hdisj
        hw₀R hw₀N hw₁R hw₁A
    obtain ⟨⟨σ, M, z⟩, hb⟩ := Option.isSome_iff_exists.mp hb_some
    obtain ⟨t, K, rfl, hσN, hzL, hch_M, hnd_M, hK_props⟩ :=
      bridgeOfList_props_of_mem_R hCnd step.hrot step.hP₀ step.hsupp step.hind step.htight
        Q R₀ hQe hR₀ hdisj hL_or hb
    obtain ⟨P_new, hP_new, hr3_eq, hsub, hmiss⟩ :=
      rule3ChainOfBridge_spec step.hP₀ step.hsupp hσN hzL hch_M hnd_M
        fun w hw => ⟨(hK_props w hw).2.1, (hK_props w hw).2.2.1⟩
    rcases hbr hL_or hb hσN hzL hch_M hnd_M hK_props hP_new hr3_eq hsub hmiss with
      ⟨c, d, W, halt_r2, hW_r2⟩ | hns_r3 |
      ⟨X, u, v, c, d, W, hX_mem, hX_ch, hh, hl, hc, hd, hin, halt_r4, hW_r4⟩
    · exact undoEdgeCandidateWalks_isSome_of_rule_two hverts hCnd step.hP₀ step.hsupp Q R₀.support
        hQ hQe halt_r2 W hW_r2
    · exact undoEdgeCandidateWalks_isSome_of_rule_three Q.support R₀.support hverts hCnd step.hrot
        hL_or hb hP_new hr3_eq hns_r3
    · exact undoEdgeCandidateWalks_isSome_of_rule_four Q.support R₀.support hverts hCnd hL_or hb
        hX_mem hX_ch hh hl hc hd hin halt_r4 W hW_r4

/-- Step-level bridge dichotomy hypothesis for `undoEdgeBySearches_isSome`. -/
@[expose] def StepSearchExhaustive [DecidableEq V] [WalkSearch V]
    (step : AddedEdgeStep V C A B a b k) [DecidableRel step.G₀.Adj] (verts : List V) : Prop :=
  ∀ {u₁ v₁ u₂ v₂ : V} (Q : step.G₁.Walk u₁ v₁) (R₀ : step.G₀.Walk u₂ v₂),
    (Alternate C u₁ v₁ u₂ v₂ ∨ Alternate C v₁ u₁ u₂ v₂) →
    IsTPath step.G₁ C Q → s(step.y, step.s) ∈ Q.edges →
    IsTPath step.G₀ C R₀ → Q.support.Disjoint R₀.support →
    BridgeSearchExhaustive step verts Q R₀

/-- When the added edge joins the two ends of `P₀` (`y = a` and `s = b`, so `L₁ = L₂ = []`), the
bridge condition holds for every crossing: a bridge ends at a vertex `z` of `L₁ ++ L₂`, and there
is none. -/
theorem stepSearchExhaustive_of_nil [DecidableEq V] [WalkSearch V]
    (step : AddedEdgeStep V C A B a b k) [DecidableRel step.G₀.Adj] (verts : List V)
    (h₁ : step.L₁ = []) (h₂ : step.L₂ = []) : StepSearchExhaustive step verts := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hz
  simp [h₁, h₂] at hz

/-- **Completeness of `undoEdgeBySearches` (`undoEdgeBySearches_isSome`):**
For any valid crossing `cr` of `C` in `step.G₁`, `undoEdgeBySearches step verts cr` returns `some`
valid crossing of `C` in `step.G₀` whenever `StepSearchExhaustive step verts` holds on the Case 3
bridge. -/
theorem undoEdgeBySearches_isSome [DecidableEq V] [WalkSearch V] [LawfulWalkSearch V]
    (step : AddedEdgeStep V C A B a b k) [DecidableRel step.G₀.Adj]
    {verts : List V} (hverts : ∀ v : V, v ∈ verts)
    (hexh : StepSearchExhaustive step verts)
    {cr : CrossingWalks step.G₁ C} (hcr : cr.Valid) :
    (undoEdgeBySearches step verts cr).1.isSome = true := by
  unfold undoEdgeBySearches
  rcases hQ : transferWalkOption (G := step.G₀) cr.Q with _ | Q₀ <;>
    rcases hR : transferWalkOption (G := step.G₀) cr.R with _ | R₀
  · exfalso
    have heQ := mem_edges_of_transferWalkOption_none hQ
    have heR := mem_edges_of_transferWalkOption_none hR
    exact hcr.2.2.2 (cr.Q.fst_mem_support_of_mem_edges heQ)
      (cr.R.fst_mem_support_of_mem_edges heR)
  · dsimp only
    have hQe : s(step.y, step.s) ∈ cr.Q.edges := mem_edges_of_transferWalkOption_none hQ
    have hR₀_path : IsTPath step.G₀ C R₀ := transferWalkOption_isTPath hR hcr.2.2.1
    have hR₀_supp : R₀.support = cr.R.support := transferWalkOption_support hR
    have hdisj : cr.Q.support.Disjoint R₀.support := by rw [hR₀_supp]; exact hcr.2.2.2
    have halt : Alternate C cr.u₁ cr.v₁ cr.u₂ cr.v₂ ∨ Alternate C cr.v₁ cr.u₁ cr.u₂ cr.v₂ :=
      Or.inl hcr.alternate
    rw [← hR₀_supp]
    exact undoEdgeCandidateWalks_isSome_of_bridge_exhaustive step hverts cr.Q R₀ halt
      hcr.2.1 hQe hR₀_path hdisj (hexh cr.Q R₀ halt hcr.2.1 hQe hR₀_path hdisj)
  · dsimp only
    have hRe : s(step.y, step.s) ∈ cr.R.edges := mem_edges_of_transferWalkOption_none hR
    have hQ₀_path : IsTPath step.G₀ C Q₀ := transferWalkOption_isTPath hQ hcr.2.1
    have hQ₀_supp : Q₀.support = cr.Q.support := transferWalkOption_support hQ
    have hdisj : cr.R.support.Disjoint Q₀.support := by rw [hQ₀_supp]; exact hcr.2.2.2.symm
    have halt' : Alternate C cr.u₂ cr.v₂ cr.u₁ cr.v₁ ∨ Alternate C cr.v₂ cr.u₂ cr.u₁ cr.v₁ :=
      Or.inr hcr.alternate.comm.swap
    rw [← hQ₀_supp]
    exact undoEdgeCandidateWalks_isSome_of_bridge_exhaustive step hverts cr.R Q₀ halt'
      hcr.2.2.1 hRe hQ₀_path hdisj (hexh cr.R Q₀ halt' hcr.2.2.1 hRe hQ₀_path hdisj)
  · rfl

/-- A chain of `AddedEdgeStep`s starting at `G` and ending at `H`, with decidable adjacency at each
step so candidate walks and searches can be computed directly. -/
inductive AddedEdgeChain (V : Type*) (C A B : List V) (a b : V) (k : ℕ) (G : SimpleGraph V) :
    SimpleGraph V → Type _
  | nil : AddedEdgeChain V C A B a b k G G
  | snoc (step : AddedEdgeStep V C A B a b k) (dec : DecidableRel step.G₀.Adj)
      (chain : AddedEdgeChain V C A B a b k G step.G₀) :
      AddedEdgeChain V C A B a b k G step.G₁

/-- Number of added edges in an `AddedEdgeChain`. -/
@[expose] def AddedEdgeChain.length {G H : SimpleGraph V} :
    AddedEdgeChain V C A B a b k G H → ℕ
  | .nil => 0
  | .snoc _ _ chain => chain.length + 1

/-- Fold `undoEdgeBySearches` in reverse order over an `AddedEdgeChain` from `H` back to `G`.
Purely computable (`Option`-returning, no fallback). -/
@[expose] def undoChainBySearches [DecidableEq V]
    [WalkSearch V] (verts : List V) {G H : SimpleGraph V} :
    AddedEdgeChain V C A B a b k G H → CrossingWalks H C →
    Option (CrossingWalks G C) × ℕ
  | .nil, cr => (some cr, 0)
  | .snoc step dec chain, cr =>
    let _ := dec
    let stepRes := undoEdgeBySearches step verts cr
    match stepRes.1 with
    | some cr₀ =>
      let prevRes := undoChainBySearches verts chain cr₀
      (prevRes.1, stepRes.2 + prevRes.2)
    | none => (none, stepRes.2)

/-- Every crossing returned by `undoChainBySearches` is a valid crossing of `C` in `G` whenever
`cr` is a valid crossing of `C` in `H`. -/
theorem undoChainBySearches_valid [DecidableEq V]
    [WalkSearch V] [LawfulWalkSearch V] (verts : List V) {G H : SimpleGraph V}
    (chain : AddedEdgeChain V C A B a b k G H) {cr : CrossingWalks H C} (hcr : cr.Valid)
    {crG : CrossingWalks G C} (h : (undoChainBySearches verts chain cr).1 = some crG) :
    crG.Valid := by
  induction chain with
  | nil =>
    simp only [undoChainBySearches, Option.some.injEq] at h
    subst h
    exact hcr
  | snoc step dec chain ih =>
    let _ := dec
    simp only [undoChainBySearches] at h
    rcases hstep : (undoEdgeBySearches step verts cr).1 with _ | cr₀ <;> rw [hstep] at h
    · simp at h
    · exact ih (undoEdgeBySearches_valid step verts hcr hstep) h

/-- `undoChainBySearches` makes at most `44 * chain.length` searches. -/
theorem undoChainBySearches_searches_le [DecidableEq V]
    [WalkSearch V] (verts : List V) {G H : SimpleGraph V}
    (chain : AddedEdgeChain V C A B a b k G H) (cr : CrossingWalks H C) :
    (undoChainBySearches verts chain cr).2 ≤ 44 * chain.length := by
  induction chain with
  | nil => simp [undoChainBySearches, AddedEdgeChain.length]
  | snoc step dec chain ih =>
    let _ := dec
    simp only [undoChainBySearches, AddedEdgeChain.length]
    have h1 := undoEdgeBySearches_searches_le step verts cr
    rcases (undoEdgeBySearches step verts cr).1 with _ | cr₀
    · dsimp only; omega
    · dsimp only
      have h2 := ih cr₀
      omega

/-- Chain-level bridge dichotomy hypothesis (`AddedEdgeChain.Exhaustive`): `StepSearchExhaustive`
holds at every step of the `AddedEdgeChain`. -/
@[expose] def AddedEdgeChain.Exhaustive [DecidableEq V]
    [WalkSearch V] (verts : List V) {G H : SimpleGraph V} :
    AddedEdgeChain V C A B a b k G H → Prop
  | .nil => True
  | .snoc step dec chain =>
    let _ := dec
    StepSearchExhaustive step verts ∧ chain.Exhaustive verts

/-- **Completeness of `undoChainBySearches` (`undoChainBySearches_isSome`):**
Whenever `cr` is a valid crossing of `C` in `H` and `chain.Exhaustive verts` holds,
`undoChainBySearches verts chain cr` returns `some` valid crossing of `C` in `G`. -/
theorem undoChainBySearches_isSome [DecidableEq V]
    [WalkSearch V] [LawfulWalkSearch V] {verts : List V} (hverts : ∀ v : V, v ∈ verts)
    {G H : SimpleGraph V} (chain : AddedEdgeChain V C A B a b k G H)
    (hexh : chain.Exhaustive verts) {cr : CrossingWalks H C} (hcr : cr.Valid) :
    (undoChainBySearches verts chain cr).1.isSome = true := by
  induction chain with
  | nil => rfl
  | snoc step dec chain ih =>
    let _ := dec
    simp only [undoChainBySearches]
    have hstep_some := undoEdgeBySearches_isSome step hverts hexh.1 hcr
    obtain ⟨cr₀, hcr₀⟩ := Option.isSome_iff_exists.mp hstep_some
    rw [hcr₀]
    dsimp only
    exact ih hexh.2 (undoEdgeBySearches_valid step verts hcr hcr₀)

/-- **Lifting a subinstance crossing to `H` (`liftSubCrossingBySearches`), with no fallback.**
Given a crossing `subCr` of either subinstance of Proposition 5.1 along `P_supp` (`P'.support =
a :: m ++ [b]`) in `H`, construct the `28` candidate chains of Figure 11 (`figure11CandidateChains`),
convert those that are `H.Adj`-chains into walks in `H` (`walkOfChainOption`), and run
`runCandidateSearches H verts C` over them (at most `28` searches).
Purely computable (`Option`-returning, no `IsCrossed`, no `Classical.choice`, no fallback). -/
@[expose] def liftSubCrossingBySearches [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]
    [WalkSearch V]
    {m : List V} (verts C P_supp : List V)
    (subCr : CrossingWalks (restrict H (sideSetOf G (a :: m ++ [b]) A)) (a :: A ++ b :: m.reverse) ⊕
      CrossingWalks (restrict H (sideComplOf G (a :: m ++ [b]) A)) (b :: B ++ a :: m)) :
    Option (CrossingWalks H C) × ℕ :=
  let (Q_supp, R_supp) := match subCr with
    | .inl cr₁ => (cr₁.Q.support, cr₁.R.support)
    | .inr cr₂ => (cr₂.Q.support, cr₂.R.support)
  let cands := (figure11CandidateChains P_supp Q_supp R_supp).filterMap (walkOfChainOption H)
  runCandidateSearches H verts C cands

/-- Every crossing returned by `liftSubCrossingBySearches` is a valid crossing of `C` in `H`. -/
theorem liftSubCrossingBySearches_valid [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {m : List V} {verts C P_supp : List V}
    {subCr : CrossingWalks (restrict H (sideSetOf G (a :: m ++ [b]) A)) (a :: A ++ b :: m.reverse) ⊕
      CrossingWalks (restrict H (sideComplOf G (a :: m ++ [b]) A)) (b :: B ++ a :: m)}
    {crH : CrossingWalks H C}
    (h : (liftSubCrossingBySearches (G := G) (A := A) (B := B) (a := a) (b := b)
      verts C P_supp subCr).1 = some crH) :
    crH.Valid :=
  runCandidateSearches_valid h

/-- `liftSubCrossingBySearches` makes at most `28` searches (`O(1)`). -/
theorem liftSubCrossingBySearches_searches_le [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]
    [WalkSearch V]
    {m : List V} (verts C P_supp : List V)
    (subCr : CrossingWalks (restrict H (sideSetOf G (a :: m ++ [b]) A)) (a :: A ++ b :: m.reverse) ⊕
      CrossingWalks (restrict H (sideComplOf G (a :: m ++ [b]) A)) (b :: B ++ a :: m)) :
    (liftSubCrossingBySearches (G := G) (A := A) (B := B) (a := a) (b := b)
      verts C P_supp subCr).2 ≤ 28 := by
  unfold liftSubCrossingBySearches
  rcases subCr with cr₁ | cr₂ <;> dsimp only
  · exact (runCandidateSearches_searches_le H verts C _).trans
      ((List.length_filterMap_le _ _).trans
        (figure11CandidateChains_length P_supp cr₁.Q.support cr₁.R.support))
  · exact (runCandidateSearches_searches_le H verts C _).trans
      ((List.length_filterMap_le _ _).trans
        (figure11CandidateChains_length P_supp cr₂.Q.support cr₂.R.support))

/-- **Completeness of `liftSubCrossingBySearches`:** under the hypotheses of
`isCrossed_of_sub_crossed`, if `subCr` is a valid crossing of either subinstance of Proposition 5.1
in `H` and `∀ v : V, v ∈ verts`, then `liftSubCrossingBySearches verts C P'.support subCr` returns
`some` valid crossing of `C` in `H`. -/
theorem liftSubCrossingBySearches_isSome [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {m verts : List V} (hverts : ∀ v : V, v ∈ verts)
    (hC : IsCycleList G C) (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ []) (hB : B ≠ [])
    (hle : G ≤ H) {P' : H.Walk a b}
    (hH : ∀ u v, H.Adj u v → G.Adj u v ∨ IsListEdge P'.support u v)
    (hP' : IsTPath H C P') (hm : P'.support = a :: m ++ [b])
    (hind : ∀ u ∈ P'.support, ∀ v ∈ P'.support, H.Adj u v → IsListEdge P'.support u v)
    (hsep : Separates G {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B})
    (hsides : OnBothSidesList G C A B P'.support)
    (htight : IsTight H C A B P'.support)
    (subCr : CrossingWalks (restrict H (sideSetOf G (a :: m ++ [b]) A)) (a :: A ++ b :: m.reverse) ⊕
      CrossingWalks (restrict H (sideComplOf G (a :: m ++ [b]) A)) (b :: B ++ a :: m))
    (hvalid : Sum.elim CrossingWalks.Valid CrossingWalks.Valid subCr) :
    (liftSubCrossingBySearches (G := G) (A := A) (B := B) (a := a) (b := b)
      verts C P'.support subCr).1.isSome = true := by
  have hS := setting_of_onBothSidesList hC hrot hA hB hle hP' hm hind hsep hsides
  unfold liftSubCrossingBySearches
  rcases subCr with cr₁ | cr₂
  · dsimp only [Sum.elim_inl] at hvalid ⊢
    exact hS.cross_of_side_search hverts (by simp [hm]) hvalid rfl rfl
  · dsimp only [Sum.elim_inr] at hvalid ⊢
    have hrest : restrict H {w | w ∉ a :: m ++ [b]} = restrict G {w | w ∉ a :: m ++ [b]} :=
      hm ▸ restrict_notMem_eq_of_adj_or_mem hle fun u v huv =>
        (hH u v huv).imp_right fun h => ⟨h.mem_left, h.mem_right⟩
    have hcompl_eq : sideComplOf G (a :: m ++ [b]) A = sideComplOf H (a :: m ++ [b]) A := by
      simp only [sideComplOf, hrest]
    have hsideB_eq : sideSetOf H (a :: m ++ [b]) B = sideSetOf G (a :: m ++ [b]) B := by
      simp only [sideSetOf, hrest]
    have hnd : (b :: B ++ a :: m).Nodup := hS.cycK.2.1
    rcases cr₂ with ⟨u₁, v₁, u₂, v₂, Q, R⟩
    unfold CrossingWalks.Valid at hvalid
    dsimp only at hvalid ⊢
    obtain ⟨k₁, M₁, M₂, hrot₁, hc₁, hd₁⟩ := hvalid.alternate
    obtain ⟨k₂, N₁, N₂, hrot₂, hc₂, hd₂⟩ := hvalid.alternate.comm
    have hnotQ : ¬ PlaneEmbedding.IsCycleEdge (b :: B ++ a :: m) u₁ v₁ :=
      not_isCycleEdge_of_rotate hnd hrot₁ (List.ne_nil_of_mem hc₁) (List.ne_nil_of_mem hd₁)
    have hnotR : ¬ PlaneEmbedding.IsCycleEdge (b :: B ++ a :: m) u₂ v₂ :=
      not_isCycleEdge_of_rotate hnd hrot₂ (List.ne_nil_of_mem hc₂) (List.ne_nil_of_mem hd₂)
    have hle_compl : restrict H (sideComplOf G (a :: m ++ [b]) A) ≤
        restrict H (sideComplOf H (a :: m ++ [b]) A) := by rw [hcompl_eq]
    have hle_sideB : restrict H (sideSetOf H (a :: m ++ [b]) B) ≤
        restrict H (sideSetOf G (a :: m ++ [b]) B) := by rw [hsideB_eq]
    have hQ_H : IsTPath (restrict H (sideComplOf H (a :: m ++ [b]) A)) (b :: B ++ a :: m)
        (Q.mapLe hle_compl) := by
      refine ⟨(hvalid.2.1.1).mapLe _, hvalid.2.1.2.1, hvalid.2.1.2.2.1, ?_⟩
      rw [support_mapLe]; exact hvalid.2.1.2.2.2
    have hR_H : IsTPath (restrict H (sideComplOf H (a :: m ++ [b]) A)) (b :: B ++ a :: m)
        (R.mapLe hle_compl) := by
      refine ⟨(hvalid.2.2.1.1).mapLe _, hvalid.2.2.1.2.1, hvalid.2.2.1.2.2.1, ?_⟩
      rw [support_mapLe]; exact hvalid.2.2.1.2.2.2
    obtain ⟨Q₁, hQ₁, hQs₁⟩ := exists_tPath_sideSetOf_B_of_tight (hC.mono hle) hrot hP' hm htight
      hQ_H hnotQ
    obtain ⟨R₁, hR₁, hRs₁⟩ := exists_tPath_sideSetOf_B_of_tight (hC.mono hle) hrot hP' hm htight
      hR_H hnotR
    rw [support_mapLe] at hQs₁ hRs₁
    set Q' := Q₁.mapLe hle_sideB
    set R' := R₁.mapLe hle_sideB
    have hQs : Q'.support = Q.support := by rw [support_mapLe, hQs₁]
    have hRs : R'.support = R.support := by rw [support_mapLe, hRs₁]
    have hQ' : IsTPath (restrict H (sideSetOf G (a :: m ++ [b]) B)) (b :: B ++ a :: m) Q' := by
      refine ⟨hQ₁.1.mapLe _, hQ₁.2.1, hQ₁.2.2.1, ?_⟩
      rw [support_mapLe]; exact hQ₁.2.2.2
    have hR' : IsTPath (restrict H (sideSetOf G (a :: m ++ [b]) B)) (b :: B ++ a :: m) R' := by
      refine ⟨hR₁.1.mapLe _, hR₁.2.1, hR₁.2.2.1, ?_⟩
      rw [support_mapLe]; exact hR₁.2.2.2
    have hcr' : IsCrossing (restrict H (sideSetOf G (a :: m ++ [b]) B))
        (b :: B ++ a :: m.reverse.reverse) Q' R' := by
      rw [List.reverse_reverse]
      exact ⟨hvalid.1, hQ', hR', by rw [hQs, hRs]; exact hvalid.2.2.2⟩
    exact hS.symm.cross_of_side_search hverts (by simp [hm]) hcr' hQs hRs

/-- **Full one-level crossing extraction (`extractCrossingOneLevel`), with no fallback.**
Given a crossing `subCr` of either subinstance of Proposition 5.1 along `P_supp` (`P'.support =
a :: m ++ [b]`) in `H` and the chain `chain` of added edges from `G` to `H`,
`extractCrossingOneLevel` lifts `subCr` to a crossing of `C` in `H` via Figure 11
(`liftSubCrossingBySearches`) and then undoes each added edge in reverse order via
`undoChainBySearches` (`undoEdgeBySearches`), returning `Option (CrossingWalks G C)` and the total
number of searches performed.
Purely computable (`Option`-returning, no `IsCrossed`, no `Classical.choice`, no fallback). -/
@[expose] def extractCrossingOneLevel [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]
    [WalkSearch V]
    {m : List V} (verts C P_supp : List V)
    (chain : AddedEdgeChain V C A B a b k G H)
    (subCr : CrossingWalks (restrict H (sideSetOf G (a :: m ++ [b]) A)) (a :: A ++ b :: m.reverse) ⊕
      CrossingWalks (restrict H (sideComplOf G (a :: m ++ [b]) A)) (b :: B ++ a :: m)) :
    Option (CrossingWalks G C) × ℕ :=
  let liftRes := liftSubCrossingBySearches (G := G) (A := A) (B := B) (a := a) (b := b)
    verts C P_supp subCr
  match liftRes.1 with
  | some crH =>
    let undoRes := undoChainBySearches verts chain crH
    (undoRes.1, liftRes.2 + undoRes.2)
  | none => (none, liftRes.2)

/-- **Soundness of one-level extraction:** any crossing returned by `extractCrossingOneLevel` is a
valid crossing of `C` in `G`. -/
theorem extractCrossingOneLevel_valid [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {m : List V} {verts C P_supp : List V}
    (chain : AddedEdgeChain V C A B a b k G H)
    {subCr : CrossingWalks (restrict H (sideSetOf G (a :: m ++ [b]) A)) (a :: A ++ b :: m.reverse) ⊕
      CrossingWalks (restrict H (sideComplOf G (a :: m ++ [b]) A)) (b :: B ++ a :: m)}
    {crG : CrossingWalks G C}
    (h : (extractCrossingOneLevel verts C P_supp chain subCr).1 = some crG) :
    crG.Valid := by
  simp only [extractCrossingOneLevel] at h
  rcases hlift : (liftSubCrossingBySearches (G := G) (A := A) (B := B) (a := a) (b := b)
    verts C P_supp subCr).1 with _ | crH <;> rw [hlift] at h
  · simp at h
  · exact undoChainBySearches_valid verts chain (liftSubCrossingBySearches_valid hlift) h

/-- **Search count bound of one-level extraction (`O(|P'|)`):** `extractCrossingOneLevel` makes at
most `28 + 44 * chain.length` searches, and when `chain.length < P_supp.length`, at most
`72 * P_supp.length` searches in total. -/
theorem extractCrossingOneLevel_searches_le [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]
    [WalkSearch V]
    {m : List V} (verts C P_supp : List V)
    (chain : AddedEdgeChain V C A B a b k G H) (hlen : chain.length < P_supp.length)
    (subCr : CrossingWalks (restrict H (sideSetOf G (a :: m ++ [b]) A)) (a :: A ++ b :: m.reverse) ⊕
      CrossingWalks (restrict H (sideComplOf G (a :: m ++ [b]) A)) (b :: B ++ a :: m)) :
    (extractCrossingOneLevel verts C P_supp chain subCr).2 ≤ 28 + 44 * chain.length ∧
    (extractCrossingOneLevel verts C P_supp chain subCr).2 ≤ 72 * P_supp.length := by
  simp only [extractCrossingOneLevel]
  have h1 := liftSubCrossingBySearches_searches_le (G := G) (A := A) (B := B) (a := a) (b := b)
    verts C P_supp subCr
  rcases (liftSubCrossingBySearches (G := G) (A := A) (B := B) (a := a) (b := b)
    verts C P_supp subCr).1 with _ | crH
  · dsimp only; refine ⟨by omega, by omega⟩
  · dsimp only
    have h2 := undoChainBySearches_searches_le verts chain crH
    refine ⟨by omega, by omega⟩

/-- **Completeness of `extractCrossingOneLevel` (`extractCrossingOneLevel_isSome`):**
Under the hypotheses of `liftSubCrossingBySearches_isSome` and `chain.Exhaustive verts`,
`extractCrossingOneLevel verts C P'.support chain subCr` returns `some` valid crossing of `C`
in `G`. -/
theorem extractCrossingOneLevel_isSome [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {m verts : List V} (hverts : ∀ v : V, v ∈ verts)
    (hC : IsCycleList G C) (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ []) (hB : B ≠ [])
    (hle : G ≤ H) {P' : H.Walk a b}
    (hH : ∀ u v, H.Adj u v → G.Adj u v ∨ IsListEdge P'.support u v)
    (hP' : IsTPath H C P') (hm : P'.support = a :: m ++ [b])
    (hind : ∀ u ∈ P'.support, ∀ v ∈ P'.support, H.Adj u v → IsListEdge P'.support u v)
    (hsep : Separates G {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B})
    (hsides : OnBothSidesList G C A B P'.support)
    (htight : IsTight H C A B P'.support)
    (chain : AddedEdgeChain V C A B a b k G H) (hexh : chain.Exhaustive verts)
    (subCr : CrossingWalks (restrict H (sideSetOf G (a :: m ++ [b]) A)) (a :: A ++ b :: m.reverse) ⊕
      CrossingWalks (restrict H (sideComplOf G (a :: m ++ [b]) A)) (b :: B ++ a :: m))
    (hvalid : Sum.elim CrossingWalks.Valid CrossingWalks.Valid subCr) :
    (extractCrossingOneLevel verts C P'.support chain subCr).1.isSome = true := by
  simp only [extractCrossingOneLevel]
  have hlift_some :=
    liftSubCrossingBySearches_isSome hverts hC hrot hA hB hle hH hP' hm hind hsep hsides htight
      subCr hvalid
  obtain ⟨crH, hcrH⟩ := Option.isSome_iff_exists.mp hlift_some
  rw [hcrH]
  dsimp only
  exact undoChainBySearches_isSome hverts chain hexh (liftSubCrossingBySearches_valid hcrH)

/-! ### The number of rerouting steps (`reroute_all_count` and `completion_loop_count`) -/

/-- Shortening a path to a sublist can only enlarge its live set in `G`. -/
theorem liveSet_mono_of_sublist {l₁ l₂ : List V} (h : l₁.Sublist l₂) :
    liveSet G A B l₂ ⊆ liveSet G A B l₁ :=
  fun _ ⟨hnot, z, hz, p, hp, hin⟩ => ⟨fun hm => hnot (h.subset hm),
    z, hz, p, hp, fun x hx h1 h2 hx₁ => hin x hx h1 h2 (h.subset hx₁)⟩

/-- **The number of rerouting steps (`reroute_all_count`).** Starting from `P`, repeating
`reroute_step` takes at most `r ≤ (liveSet G A B P.support)ᶜ.ncard ≤ Nat.card V` steps: either it
finds that `C` is crossed after `r < (liveSet G A B P.support)ᶜ.ncard` steps, or it produces an
induced, separating, weakly tight `C`-path `P'` in `r` steps with
`liveSet G A B P.support ⊆ liveSet G A B P'.support` and
`r + (liveSet G A B P.support).ncard ≤ (liveSet G A B P'.support).ncard`. -/
theorem reroute_all_count [Finite V] (hrot : C.rotate k = a :: A ++ b :: B) (hCnd : C.Nodup) :
    ∀ (n : ℕ) (P : G.Walk a b), (liveSet G A B P.support)ᶜ.ncard = n → IsTPath G C P →
      (∀ x ∈ P.support, ∀ y ∈ P.support, G.Adj x y → IsListEdge P.support x y) →
      Separates G {x | x ∈ P.support} {x | x ∈ A} {x | x ∈ B} →
      (∃ r < (liveSet G A B P.support)ᶜ.ncard, r < Nat.card V ∧ IsCrossed G C) ∨
        ∃ (r : ℕ) (P' : G.Walk a b),
          r ≤ (liveSet G A B P.support)ᶜ.ncard ∧
          r ≤ Nat.card V ∧
          liveSet G A B P.support ⊆ liveSet G A B P'.support ∧
          r + (liveSet G A B P.support).ncard ≤ (liveSet G A B P'.support).ncard ∧
          IsTPath G C P' ∧
          (∀ x ∈ P'.support, ∀ y ∈ P'.support, G.Adj x y → IsListEdge P'.support x y) ∧
          Separates G {x | x ∈ P'.support} {x | x ∈ A} {x | x ∈ B} ∧
          IsWeaklyTight G C A B P'.support := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hP hind hsep
  have hle_card : (liveSet G A B P.support)ᶜ.ncard ≤ Nat.card V :=
    (Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)).trans_eq (Set.ncard_univ V)
  by_cases hwt : IsWeaklyTight G C A B P.support
  · exact Or.inr ⟨0, P, Nat.zero_le _, Nat.zero_le _, subset_rfl, by omega, hP, hind, hsep, hwt⟩
  rcases reroute_step hrot hCnd hP hind hsep hwt with hcr | ⟨P₁, hP₁, hind₁, hsep₁, hlt⟩
  · have hpos : 0 < (liveSet G A B P.support)ᶜ.ncard := by
      rw [Set.ncard_pos (Set.toFinite _)]
      simp only [IsWeaklyTight, not_forall] at hwt
      obtain ⟨w, hwC, hwl, hwd, -⟩ := hwt
      refine ⟨w, fun h => hwd ?_⟩
      exact isConnectedAvoiding_CP_of_P hrot h.2
    exact Or.inl ⟨0, hpos, Nat.lt_of_lt_of_le hpos hle_card, hcr⟩
  · have hcompl_lt : (liveSet G A B P₁.support)ᶜ ⊂ (liveSet G A B P.support)ᶜ :=
      compl_lt_compl_iff_lt.mpr hlt
    have hnc_compl : (liveSet G A B P₁.support)ᶜ.ncard < (liveSet G A B P.support)ᶜ.ncard :=
      Set.ncard_lt_ncard hcompl_lt (Set.toFinite _)
    have hnc_live : (liveSet G A B P.support).ncard < (liveSet G A B P₁.support).ncard :=
      Set.ncard_lt_ncard hlt (Set.toFinite _)
    rcases ih _ (hn ▸ hnc_compl) P₁ rfl hP₁ hind₁ hsep₁ with
      ⟨r, hr, _, hcr⟩ | ⟨r, P', hr, _, hsub, hadd, hP', hind', hsep', hwt'⟩
    · exact Or.inl ⟨r + 1, by omega, by omega, hcr⟩
    · exact Or.inr ⟨r + 1, P', by omega, by omega, hlt.subset.trans hsub, by omega,
        hP', hind', hsep', hwt'⟩

/-- **The whole completion loop, with the number of rerouting steps (`completion_loop_count`).** In
`completion_loop`, the number `r` of rerouting steps satisfies
`r ≤ (liveSet G A B P.support)ᶜ.ncard ≤ Nat.card V` and
`r + (liveSet G A B P.support).ncard ≤ (liveSet G A B P'.support).ncard`. -/
theorem completion_loop_count [Finite V] (hC : IsCycleList G C) (hrot : C.rotate k = a :: A ++ b :: B)
    (hA : A ≠ []) (hB : B ≠ []) {P : G.Walk a b} (hP : IsTPath G C P)
    (hind : ∀ x ∈ P.support, ∀ y ∈ P.support, G.Adj x y → IsListEdge P.support x y)
    (hsep : Separates G {x | x ∈ P.support} {x | x ∈ A} {x | x ∈ B}) :
    (∃ r < (liveSet G A B P.support)ᶜ.ncard, r < Nat.card V ∧ IsCrossed G C) ∨
      ∃ (r : ℕ) (H : SimpleGraph V), G ≤ H ∧ (IsCrossed H C → IsCrossed G C) ∧
        ∃ P' : H.Walk a b,
          r ≤ (liveSet G A B P.support)ᶜ.ncard ∧
          r ≤ Nat.card V ∧
          liveSet G A B P.support ⊆ liveSet G A B P'.support ∧
          r + (liveSet G A B P.support).ncard ≤ (liveSet G A B P'.support).ncard ∧
          IsTPath H C P' ∧ OnBothSides H C A B P' ∧
          OnBothSidesList G C A B P'.support ∧
          Separates H {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} ∧
          (∀ u ∈ P'.support, ∀ v ∈ P'.support, H.Adj u v → IsListEdge P'.support u v) ∧
          IsTight H C A B P'.support ∧
          ∀ u v, H.Adj u v → G.Adj u v ∨ IsListEdge P'.support u v := by
  rcases reroute_all_count hrot hC.2.1 _ P rfl hP hind hsep with
    h | ⟨r, P₁, hr_c, hr_V, hsub₁, hadd₁, hP₁, hind₁, hsep₁, hwt₁⟩
  · exact Or.inl h
  right
  obtain ⟨G₂, hle₂, hcr₂, P₂, hP₂, hind₂, hsep₂, ht₂, hsd₂, hsub₂, hconn₂⟩ :=
    collapse_all hrot hA hB _ G P₁ rfl hC hP₁ hind₁ hsep₁ hwt₁
  obtain ⟨H, hle, hcr, P', hP', hboth, hsep', hind', ht', hedge, hsub', -⟩ :=
    complete_loop_edges hrot hA hB _ G₂ P₂ rfl (hC.mono hle₂) hP₂ hind₂ hsep₂ ht₂ hsd₂
  set H' := keepEdges G H P'.support
  have hGH' : G ≤ H' := fun _ _ h => Or.inl h
  have hH'H : H' ≤ H := by
    rintro _ _ (hG | ⟨hH, _⟩)
    · exact (hle₂.trans hle) hG
    · exact hH
  have hsubE : ∀ e ∈ P'.edges, e ∈ H'.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      exact Or.inr ⟨P'.adj_of_mem_edges he, P'.fst_mem_support_of_mem_edges he,
        P'.snd_mem_support_of_mem_edges he⟩
  set P₀ : H'.Walk a b := P'.transfer H' hsubE
  have hP₀s : P₀.support = P'.support := Walk.support_transfer P' hsubE
  have hP₀ : IsTPath H' C P₀ :=
    ⟨hP'.1.transfer hsubE, hP'.2.1, hP'.2.2.1, fun x hx => hP'.2.2.2 x (hP₀s ▸ hx)⟩
  have hedge' : ∀ u v, H'.Adj u v → G.Adj u v ∨ IsListEdge P₀.support u v := by
    intro u v huv
    rw [hP₀s]
    exact huv.imp id fun ⟨hH, hu, hv⟩ => hind' u hu v hv hH
  have hmemH' : ∀ x y, H'.Adj x y → G.Adj x y ∨ (x ∈ P'.support ∧ y ∈ P'.support) :=
    fun _ _ h => h.imp id fun ⟨_, hx, hy⟩ => ⟨hx, hy⟩
  have hmemH : ∀ x y, H.Adj x y → G₂.Adj x y ∨ (x ∈ P'.support ∧ y ∈ P'.support) :=
    fun x y h => (hedge x y h).imp id fun hle => ⟨hle.mem_left, hle.mem_right⟩
  set X' : Set V := {x | x ∈ C ∨ x ∈ P'.support}
  have hX' : ∀ v ∈ P₁.support, v ∉ P₂.support → v ∉ X' := by
    rintro v hv₁ hv₂ (hvC | hvP')
    · have hva : v ≠ a := fun h => hv₂ (h ▸ P₂.start_mem_support)
      have hvb : v ≠ b := fun h => hv₂ (h ▸ P₂.end_mem_support)
      exact (hP₁.2.2.2 v hv₁ hva hvb).1 hvC
    · exact hv₂ (hsub'.subset hvP')
  have hconn : ∀ u S, (u ∉ P'.support ∨ ∀ s ∈ S, s ∉ P'.support) →
      (IsConnectedAvoiding H X' u S ↔ IsConnectedAvoiding G X' u S) ∧
      (IsConnectedAvoiding H' X' u S ↔ IsConnectedAvoiding G X' u S) := by
    intro u S huS
    have h1 := isConnectedAvoiding_iff_of_adj_or_mem (X := X') hle hmemH (fun _ h => Or.inr h) huS
    have h2 := hconn₂ X' hX' u S
    have h3 := isConnectedAvoiding_iff_of_adj_or_mem (X := X') hGH' hmemH' (fun _ h => Or.inr h) huS
    exact ⟨h1.trans h2, h3⟩
  have hAoff : ∀ s ∈ {x | x ∈ A}, s ∉ P'.support :=
    fun s hs => notMem_support_of_arc hC.2.1 hrot hP' (Or.inl hs)
  have hBoff : ∀ s ∈ {x | x ∈ B}, s ∉ P'.support :=
    fun s hs => notMem_support_of_arc hC.2.1 hrot hP' (Or.inr hs)
  have hbothG : OnBothSidesList G C A B P₀.support := by
    intro v hv
    rw [hP₀s] at hv ⊢
    exact ⟨((hconn v {x | x ∈ A} (Or.inr hAoff)).1).mp (hboth v hv).1,
      ((hconn v {x | x ∈ B} (Or.inr hBoff)).1).mp (hboth v hv).2⟩
  have hbothH' : OnBothSides H' C A B P₀ := by
    intro v hv
    have hG := hbothG v hv
    rw [hP₀s] at hG ⊢
    exact ⟨((hconn v {x | x ∈ A} (Or.inr hAoff)).2).mpr hG.1,
      ((hconn v {x | x ∈ B} (Or.inr hBoff)).2).mpr hG.2⟩
  have htH' : IsTight H' C A B P₀.support := by
    rw [hP₀s]
    intro u huC huP' hnAB
    have hnAB' : ¬ IsConnectedAvoiding H X' u {x | x ∈ A ∨ x ∈ B} := fun h =>
      hnAB (((hconn u _ (Or.inl huP')).2).mpr (((hconn u _ (Or.inl huP')).1).mp h))
    obtain ⟨v, w, hvw, hall⟩ := ht' u huC huP' hnAB'
    refine ⟨v, w, hvw, fun p hp hup => hall p hp ?_⟩
    exact ((hconn u {p} (Or.inl huP')).1).mpr (((hconn u {p} (Or.inl huP')).2).mp hup)
  have hlivesub : liveSet G A B P₁.support ⊆ liveSet G A B P₀.support := by
    rw [hP₀s]
    exact liveSet_mono_of_sublist (hsub'.trans hsub₂)
  have hlive_nc : (liveSet G A B P₁.support).ncard ≤ (liveSet G A B P₀.support).ncard :=
    Set.ncard_le_ncard hlivesub (Set.toFinite _)
  refine ⟨r, H', hGH', fun h => hcr₂ (hcr (h.mono hH'H)), P₀, hr_c, hr_V, hsub₁.trans hlivesub,
    by omega, hP₀, hbothH', hbothG, ?_, ?_, htH', hedge'⟩
  · intro u hu w hw p
    rw [hP₀s]
    obtain ⟨v, hv, hvP'⟩ := hsep' u hu w hw (p.mapLe hH'H)
    exact ⟨v, by simpa using hv, hvP'⟩
  · intro u hu v hv huv
    rw [hP₀s] at hu hv ⊢
    exact hind' u hu v hv (hH'H huv)

/-! ### Default walk search

The searches above take the walk search as an instance of `WalkSearch V`. Files that import this
one and give no search get `findWalkInSearch`. It is declared here, after the searches, so that
every statement above holds for any lawful search. -/

/-- The default walk search, `findWalkIn`. -/
instance (priority := low) instWalkSearchDefault [DecidableEq V] : WalkSearch V :=
  findWalkInSearch

instance (priority := low) instLawfulWalkSearchDefault [DecidableEq V] :
    @LawfulWalkSearch V instWalkSearchDefault :=
  findWalkInSearch_lawful

end GraphMinor.HP25
