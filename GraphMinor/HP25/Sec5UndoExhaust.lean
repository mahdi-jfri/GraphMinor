module

public import GraphMinor.HP25.Sec5Extract
public import GraphMinor.HP25.Sec5Search
public import GraphMinor.HP25.Sec5LiftSearch
import GraphMinor.HP25.Lemma33
import GraphMinor.HP25.Sec5Lemma54
import GraphMinor.HP25.Sec5StripTools
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.CrossTools
import GraphMinor.HP25.CycleEdges
import GraphMinor.HP25.Method
import GraphMinor.HP25.Prop52Converse
import GraphMinor.HP25.Completion

/-!
# Search completeness and exhaustiveness of Rules 1 to 4 (`undoEdgeCandidateChains`)

This file proves the search completeness of the candidate chains in `undoEdgeCandidateChains`
for each of Rules 1 to 4 when undoing an added edge `ys` across a pocket `N` of `P₀`:

1. **Rule 1 (`r1 = R₀.support`):**
   - `undoEdgeCandidateWalks_isSome_of_walk_ys`: if any walk `W : G₀.Walk y s` in `G₀` avoids
     `R₀.support`, then `r1` succeeds under `runCandidateSearches`;
   - `undoEdgeCandidateWalks_isSome_of_pocket_free`: Case 1 (`R₀` misses `N`);
   - `undoEdgeCandidateWalks_isSome_of_lower_free` and
     `undoEdgeCandidateWalks_isSome_of_upper_free`: Case 2 (`R₀` misses the side-`B` or side-`A`
     lower world).
2. **Rule 2 (`r2 = rule2PocketChain y s N Q.support`):**
   - `undoEdgeCandidateWalks_isSome_of_rule_two`: Subcase 3a (replacing `s(y, s)` in `Q` by the
     pocket `y :: N ++ [s]` when an `A`–`B` walk in `G₀` avoids `Q.support ∪ N`).
3. **Bridge extraction (`bridgeOfList`) and Rule 3 (`r3_1`, `r3_2 = rule3ChainOfBridge`):**
   - `exists_bridgeOfList_of_meets_pocket_and_side`: when `R₀` meets both `N` and the side-`B`
     (or side-`A`) world, `bridgeOfList N (L₁ ++ L₂)` on `R₀.support` or `R₀.support.reverse`
     returns `some (σ, t :: K, z)` with `σ ∈ N`, `z ∈ L₁ ∪ L₂`, and `t :: K` off `C ∪ P₀ ∪ Q`;
   - `undoEdgeCandidateWalks_isSome_of_rule_three_left` and
     `undoEdgeCandidateWalks_isSome_of_rule_three_right`: Subcase 3b (searching `G₀ - P_new`
     when `P_new` fails to separate `A` from `B`, in particular when the bypassed vertex `y` or `s`
     reaches the opposite arc off `P_new`).
4. **Rule 4 (`r4_1`, `r4_2 = rule4ChainsForSigma`):**
   - `undoEdgeCandidateWalks_isSome_of_rule_four`: Subcase 3c (splicing the side path of `y` or `s`
     with the pocket segment to `σ` and the `A`-walk from `σ`).
-/

public section

namespace GraphMinor.HP25

open SimpleGraph

variable {V : Type*} {G₀ : SimpleGraph V}

/-! ### Part 1: List indexing lemmas for nodup decompositions -/

theorem idxOf_eq_length_left [DecidableEq V] {l₁ l₂ : List V} {x : V}
    (hnd : (l₁ ++ x :: l₂).Nodup) :
    (l₁ ++ x :: l₂).idxOf x = l₁.length := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    simp only [List.cons_append, List.nodup_cons, List.mem_append, List.mem_cons] at hnd
    have hax : a ≠ x := fun h => hnd.1 (Or.inr (Or.inl h))
    simp [List.idxOf_cons_ne _ hax, ih hnd.2]

theorem take_idxOf_of_nodup [DecidableEq V] {l₁ l₂ : List V} {x : V}
    (hnd : (l₁ ++ x :: l₂).Nodup) :
    (l₁ ++ x :: l₂).take ((l₁ ++ x :: l₂).idxOf x) = l₁ := by
  rw [idxOf_eq_length_left hnd, List.take_left]

theorem take_idxOf_succ_of_nodup [DecidableEq V] {l₁ l₂ : List V} {x : V}
    (hnd : (l₁ ++ x :: l₂).Nodup) :
    (l₁ ++ x :: l₂).take ((l₁ ++ x :: l₂).idxOf x + 1) = l₁ ++ [x] := by
  rw [idxOf_eq_length_left hnd]
  have h : l₁ ++ x :: l₂ = (l₁ ++ [x]) ++ l₂ := by simp
  rw [h, ← List.length_singleton (a := x), ← List.length_append, List.take_left]

theorem drop_idxOf_of_nodup [DecidableEq V] {l₁ l₂ : List V} {x : V}
    (hnd : (l₁ ++ x :: l₂).Nodup) :
    (l₁ ++ x :: l₂).drop ((l₁ ++ x :: l₂).idxOf x) = x :: l₂ := by
  rw [idxOf_eq_length_left hnd, List.drop_left]

theorem drop_idxOf_succ_of_nodup [DecidableEq V] {l₁ l₂ : List V} {x : V}
    (hnd : (l₁ ++ x :: l₂).Nodup) :
    (l₁ ++ x :: l₂).drop ((l₁ ++ x :: l₂).idxOf x + 1) = l₂ := by
  rw [idxOf_eq_length_left hnd]
  have h : l₁ ++ x :: l₂ = (l₁ ++ [x]) ++ l₂ := by simp
  rw [h, ← List.length_singleton (a := x), ← List.length_append, List.drop_left]

/-! ### Part 2: Membership in `undoEdgeCandidateChains` -/

theorem mem_undoEdgeCandidateChains_r1 [DecidableEq V] [DecidableRel G₀.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    (verts C A B P_supp L₁ N L₂ : List V) (y s : V) (Q_supp R_supp : List V) :
    R_supp ∈ undoEdgeCandidateChains G₀ verts C A B P_supp L₁ N L₂ y s Q_supp R_supp := by
  simp [undoEdgeCandidateChains]

theorem mem_undoEdgeCandidateChains_r2 [DecidableEq V] [DecidableRel G₀.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    (verts C A B P_supp L₁ N L₂ : List V) (y s : V) (Q_supp R_supp : List V) :
    rule2PocketChain y s N Q_supp ∈
      undoEdgeCandidateChains G₀ verts C A B P_supp L₁ N L₂ y s Q_supp R_supp := by
  simp [undoEdgeCandidateChains]

theorem mem_undoEdgeCandidateChains_r3_left [DecidableEq V] [DecidableRel G₀.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    (verts C A B P_supp L₁ N L₂ : List V) (y s : V) (Q_supp R_supp : List V) :
    rule3ChainOfBridge P_supp L₁ (bridgeOfList N (L₁ ++ L₂) R_supp) ∈
      undoEdgeCandidateChains G₀ verts C A B P_supp L₁ N L₂ y s Q_supp R_supp := by
  simp [undoEdgeCandidateChains]

theorem mem_undoEdgeCandidateChains_r3_right [DecidableEq V] [DecidableRel G₀.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    (verts C A B P_supp L₁ N L₂ : List V) (y s : V) (Q_supp R_supp : List V) :
    rule3ChainOfBridge P_supp L₁ (bridgeOfList N (L₁ ++ L₂) R_supp.reverse) ∈
      undoEdgeCandidateChains G₀ verts C A B P_supp L₁ N L₂ y s Q_supp R_supp := by
  simp [undoEdgeCandidateChains]

theorem mem_rule4ChainsForSigma [DecidableEq V]
    {N R_supp pBy pBs pAy pAs pAσ pBσ : List V} {σ : V} {bp at_ : List V}
    (hbp : bp ∈ [
      pBy.reverse ++ N.take (N.idxOf σ + 1),
      pBs.reverse ++ (N.drop (N.idxOf σ)).reverse,
      pAy.reverse ++ N.take (N.idxOf σ + 1),
      pAs.reverse ++ (N.drop (N.idxOf σ)).reverse
    ])
    (hat : at_ ∈ [
      (R_supp.take (R_supp.idxOf σ)).reverse,
      R_supp.drop (R_supp.idxOf σ + 1),
      pAσ.tail,
      pBσ.tail
    ]) :
    bp ++ at_ ∈ rule4ChainsForSigma N R_supp pBy pBs pAy pAs pAσ pBσ σ := by
  unfold rule4ChainsForSigma
  exact List.mem_flatMap.mpr ⟨bp, hbp, List.mem_map.mpr ⟨at_, hat, rfl⟩⟩

/-! ### Part 3: Rule 1 search completeness (`r1 = R₀.support`) -/

/-- **Rule 1 search completeness (`undoEdgeCandidateWalks_isSome_of_walk_ys`):**
Let `(Q, R₀)` be a crossing of `C` in `G₀ ⊔ edge y s` with `s(y, s) ∈ Q.edges` and `R₀` in `G₀`.
If there is a walk `W : G₀.Walk y s` in `G₀` whose support is disjoint from `R₀.support`, then
running `runCandidateSearches` on `undoEdgeCandidateChains` returns `some` valid crossing of `C`
in `G₀` (specifically, candidate `r1 = R₀.support` succeeds). -/
theorem undoEdgeCandidateWalks_isSome_of_walk_ys [DecidableEq V] [DecidableRel G₀.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {verts C A B P_supp L₁ N L₂ : List V} {y s u₁ v₁ u₂ v₂ : V}
    (hverts : ∀ v : V, v ∈ verts) (hCnd : C.Nodup)
    (Q : (G₀ ⊔ edge y s).Walk u₁ v₁) (R₀ : G₀.Walk u₂ v₂)
    (halt : Alternate C u₁ v₁ u₂ v₂ ∨ Alternate C v₁ u₁ u₂ v₂)
    (hQ : IsTPath (G₀ ⊔ edge y s) C Q) (hQe : s(y, s) ∈ Q.edges)
    (hR₀ : IsTPath G₀ C R₀) (hdisj : Q.support.Disjoint R₀.support)
    (W : G₀.Walk y s) (hW : ∀ x ∈ W.support, x ∉ R₀.support) :
    (runCandidateSearches G₀ verts C
      ((undoEdgeCandidateChains G₀ verts C A B P_supp L₁ N L₂ y s Q.support R₀.support).filterMap
        (walkOfChainOption G₀))).1.isSome = true := by
  have hmem_r1 :=
    mem_undoEdgeCandidateChains_r1 (G₀ := G₀) verts C A B P_supp L₁ N L₂ y s Q.support R₀.support
  have hhead : R₀.support.head? = some u₂ := by rw [← Walk.cons_tail_support]; rfl
  have hlast : R₀.support.getLast? = some v₂ := by
    rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
  obtain ⟨p, hp, hsupp_p⟩ := walkOfChainOption_eq_some_of_isChain R₀.isChain_adj_support hhead hlast
  have hmem_p : (⟨u₂, v₂, p⟩ : Σ u v : V, G₀.Walk u v) ∈
      (undoEdgeCandidateChains G₀ verts C A B P_supp L₁ N L₂ y s Q.support R₀.support).filterMap
        (walkOfChainOption G₀) :=
    List.mem_filterMap.mpr ⟨R₀.support, hmem_r1, hp⟩
  have hp_tpath : IsTPath G₀ C p := by
    refine ⟨?_, hR₀.2.1, hR₀.2.2.1, ?_⟩
    · rw [Walk.isPath_def, hsupp_p]
      exact hR₀.1.support_nodup
    · rw [hsupp_p]
      exact hR₀.2.2.2
  have hdisj_p : Q.support.Disjoint p.support := by
    rw [hsupp_p]
    exact hdisj
  have hW_p : ∀ x ∈ W.support, x ∉ p.support := by
    rw [hsupp_p]
    exact hW
  have hsearch : (searchCrossWalk G₀ verts C p).1.isSome = true := by
    rcases halt with halt₁ | halt₂
    · exact searchCrossWalk_isSome_of_sup_edge_walk hverts hCnd Q p halt₁ hQ hQe hp_tpath hdisj_p
        W hW_p
    · have hQ_rev : IsTPath (G₀ ⊔ edge y s) C Q.reverse := by
        refine ⟨hQ.1.reverse, hQ.2.2.1, hQ.2.1, fun x hx h1 h2 => ?_⟩
        rw [Walk.support_reverse, List.mem_reverse] at hx
        exact hQ.2.2.2 x hx h2 h1
      have hQe_rev : s(y, s) ∈ Q.reverse.edges := by
        rw [Walk.edges_reverse, List.mem_reverse]
        exact hQe
      have hdisj_rev : Q.reverse.support.Disjoint p.support := by
        intro x hxQ hxp
        rw [Walk.support_reverse, List.mem_reverse] at hxQ
        exact hdisj_p hxQ hxp
      exact searchCrossWalk_isSome_of_sup_edge_walk hverts hCnd Q.reverse p halt₂ hQ_rev hQe_rev
        hp_tpath hdisj_rev W hW_p
  exact runCandidateSearches_isSome_of_mem hmem_p hsearch

/-- **Case 1 (`R₀` misses `N`): search completeness of `undoEdgeCandidateChains`.**
When `R₀.support` misses the pocket `N`, the pocket walk `y :: N ++ [s]` in `G₀` avoids `R₀.support`,
so `undoEdgeCandidateWalks_isSome_of_walk_ys` returns `some` valid crossing. -/
theorem undoEdgeCandidateWalks_isSome_of_pocket_free [DecidableEq V] [DecidableRel G₀.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {verts C A B L₁ N L₂ : List V} {a b y s u₁ v₁ u₂ v₂ : V} {P₀ : G₀.Walk a b}
    (hverts : ∀ v : V, v ∈ verts) (hCnd : C.Nodup)
    (hsupp : P₀.support = L₁ ++ y :: N ++ s :: L₂)
    (Q : (G₀ ⊔ edge y s).Walk u₁ v₁) (R₀ : G₀.Walk u₂ v₂)
    (halt : Alternate C u₁ v₁ u₂ v₂ ∨ Alternate C v₁ u₁ u₂ v₂)
    (hQ : IsTPath (G₀ ⊔ edge y s) C Q) (hQe : s(y, s) ∈ Q.edges)
    (hR₀ : IsTPath G₀ C R₀) (hdisj : Q.support.Disjoint R₀.support)
    (hRN : ∀ x ∈ N, x ∉ R₀.support) :
    (runCandidateSearches G₀ verts C
      ((undoEdgeCandidateChains G₀ verts C A B P₀.support L₁ N L₂ y s Q.support R₀.support).filterMap
        (walkOfChainOption G₀))).1.isSome = true := by
  have hch : (y :: N ++ [s]).IsChain G₀.Adj := by
    have h := P₀.isChain_adj_support
    rw [hsupp] at h
    exact h.infix ⟨L₁, L₂, by simp⟩
  obtain ⟨W, hW⟩ := exists_walk_of_chain (u := y) (v := s) _ hch (by simp) (List.getLast?_concat ..)
  have hyR : y ∉ R₀.support := fun h => hdisj (Q.fst_mem_support_of_mem_edges hQe) h
  have hsR : s ∉ R₀.support := fun h => hdisj (Q.snd_mem_support_of_mem_edges hQe) h
  refine undoEdgeCandidateWalks_isSome_of_walk_ys hverts hCnd Q R₀ halt hQ hQe hR₀ hdisj W
    fun x hx => ?_
  rw [hW] at hx
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | hx | rfl
  · exact hyR
  · exact hRN x hx
  · exact hsR

/-- A vertex `w ≠ y` on a simple path `p` from `y` to `t ∈ S` whose inner vertices avoid `X` is
connected to `S` avoiding `X`. -/
private theorem isConnectedAvoiding_of_mem_path_aux [DecidableEq V] {X S : Set V} {y t w : V}
    (ht : t ∈ S) (p : G₀.Walk y t) (hp : p.IsPath) (hin : ∀ x ∈ p.support, x ≠ y → x ≠ t → x ∉ X)
    (hw : w ∈ p.support) (hwy : w ≠ y) : IsConnectedAvoiding G₀ X w S := by
  refine isConnectedAvoiding_of_walk_mem ht (p.dropUntil w hw) fun x hx hxX => ?_
  have hx' := Walk.support_dropUntil_subset_support p hw hx
  have hxy : x ≠ y := fun h => start_notMem_support_dropUntil hp hw hwy (h ▸ hx)
  by_cases hxt : x = t
  · exact Or.inr hxt
  · exact absurd hxX (hin x hx' hxy hxt)

/-- **Case 2 (`R₀` misses the side-`B` world): search completeness of `undoEdgeCandidateChains`.**
When `y` and `s` are on side `B` and `R₀.support` misses both `B` and all vertices off `C ∪ P₀`
connected to `B` avoiding `C ∪ P₀`, the detour walk via `B` and the side-`B` paths of `y` and `s`
avoids `R₀.support`, so `undoEdgeCandidateWalks_isSome_of_walk_ys` returns `some` valid crossing. -/
theorem undoEdgeCandidateWalks_isSome_of_lower_free [DecidableEq V] [DecidableRel G₀.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {verts C A B L₁ N L₂ : List V} {a b y s u₁ v₁ u₂ v₂ : V} {k : ℕ} {P₀ : G₀.Walk a b}
    (hverts : ∀ v : V, v ∈ verts) (hC : IsCycleList G₀ C)
    (hrot : C.rotate k = a :: A ++ b :: B)
    (hy : IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ B} y)
    (hs : IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ B} s)
    (Q : (G₀ ⊔ edge y s).Walk u₁ v₁) (R₀ : G₀.Walk u₂ v₂)
    (halt : Alternate C u₁ v₁ u₂ v₂ ∨ Alternate C v₁ u₁ u₂ v₂)
    (hQ : IsTPath (G₀ ⊔ edge y s) C Q) (hQe : s(y, s) ∈ Q.edges)
    (hR₀ : IsTPath G₀ C R₀) (hdisj : Q.support.Disjoint R₀.support)
    (hRL : ∀ x ∈ R₀.support, x ∉ B ∧
      ¬ (x ∉ {x | x ∈ C ∨ x ∈ P₀.support} ∧
        IsConnectedAvoiding G₀ {x | x ∈ C ∨ x ∈ P₀.support} x {x | x ∈ B})) :
    (runCandidateSearches G₀ verts C
      ((undoEdgeCandidateChains G₀ verts C A B P₀.support L₁ N L₂ y s Q.support R₀.support).filterMap
        (walkOfChainOption G₀))).1.isSome = true := by
  set X : Set V := {x | x ∈ C ∨ x ∈ P₀.support}
  obtain ⟨t, ht, py, hpy, hpyin⟩ := hy
  obtain ⟨t', ht', ps, hps, hpsin⟩ := hs
  have hBch : B.IsChain G₀.Adj := by
    have h := ((hC.rotate k).isPathList (R := Set.univ) fun _ _ => trivial).2.1
    rw [hrot] at h
    exact h.infix ⟨a :: A ++ [b], [], by simp⟩
  obtain ⟨σ, hσ⟩ := exists_walk_of_isChain hBch ht ht'
  have hyR : y ∉ R₀.support := fun h => hdisj (Q.fst_mem_support_of_mem_edges hQe) h
  have hsR : s ∉ R₀.support := fun h => hdisj (Q.snd_mem_support_of_mem_edges hQe) h
  have hside : ∀ {z t₀} (p : G₀.Walk z t₀), t₀ ∈ B → p.IsPath →
      (∀ x ∈ p.support, x ≠ z → x ≠ t₀ → x ∉ X) → z ∉ R₀.support →
      ∀ x ∈ p.support, x ∉ R₀.support := by
    intro z t₀ p ht₀ hp hpin hz x hx hxR
    by_cases hxz : x = z
    · exact hz (hxz ▸ hxR)
    · by_cases hxt : x = t₀
      · exact (hRL x hxR).1 (hxt ▸ ht₀)
      · exact (hRL x hxR).2 ⟨hpin x hx hxz hxt,
          isConnectedAvoiding_of_mem_path_aux ht₀ p hp hpin hx hxz⟩
  refine undoEdgeCandidateWalks_isSome_of_walk_ys hverts hC.2.1 Q R₀ halt hQ hQe hR₀ hdisj
    (py.append (σ.append ps.reverse)) fun x hx hxR => ?_
  rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff, Walk.support_reverse,
    List.mem_reverse] at hx
  rcases hx with hx | hx | hx
  · exact hside py ht hpy hpyin hyR x hx hxR
  · exact (hRL x hxR).1 (hσ x hx)
  · exact hside ps ht' hps hpsin hsR x hx hxR

/-- **Case 2 (`R₀` misses the side-`A` world): search completeness of `undoEdgeCandidateChains`.**
Symmetrically, when `y` and `s` are on side `A` and `R₀.support` misses both `A` and all vertices
off `C ∪ P₀` connected to `A` avoiding `C ∪ P₀`, the detour walk via `A` and the side-`A` paths of
`y` and `s` avoids `R₀.support`, so `undoEdgeCandidateWalks_isSome_of_walk_ys` returns `some`. -/
theorem undoEdgeCandidateWalks_isSome_of_upper_free [DecidableEq V] [DecidableRel G₀.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {verts C A B L₁ N L₂ : List V} {a b y s u₁ v₁ u₂ v₂ : V} {k : ℕ} {P₀ : G₀.Walk a b}
    (hverts : ∀ v : V, v ∈ verts) (hC : IsCycleList G₀ C)
    (hrot : C.rotate k = a :: A ++ b :: B)
    (hy : IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ A} y)
    (hs : IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ A} s)
    (Q : (G₀ ⊔ edge y s).Walk u₁ v₁) (R₀ : G₀.Walk u₂ v₂)
    (halt : Alternate C u₁ v₁ u₂ v₂ ∨ Alternate C v₁ u₁ u₂ v₂)
    (hQ : IsTPath (G₀ ⊔ edge y s) C Q) (hQe : s(y, s) ∈ Q.edges)
    (hR₀ : IsTPath G₀ C R₀) (hdisj : Q.support.Disjoint R₀.support)
    (hRU : ∀ x ∈ R₀.support, x ∉ A ∧
      ¬ (x ∉ {x | x ∈ C ∨ x ∈ P₀.support} ∧
        IsConnectedAvoiding G₀ {x | x ∈ C ∨ x ∈ P₀.support} x {x | x ∈ A})) :
    (runCandidateSearches G₀ verts C
      ((undoEdgeCandidateChains G₀ verts C A B P₀.support L₁ N L₂ y s Q.support R₀.support).filterMap
        (walkOfChainOption G₀))).1.isSome = true := by
  set X : Set V := {x | x ∈ C ∨ x ∈ P₀.support}
  obtain ⟨t, ht, py, hpy, hpyin⟩ := hy
  obtain ⟨t', ht', ps, hps, hpsin⟩ := hs
  have hAch : A.IsChain G₀.Adj := by
    have h := ((hC.rotate k).isPathList (R := Set.univ) fun _ _ => trivial).2.1
    rw [hrot] at h
    exact h.infix ⟨[a], b :: B, by simp⟩
  obtain ⟨σ, hσ⟩ := exists_walk_of_isChain hAch ht ht'
  have hyR : y ∉ R₀.support := fun h => hdisj (Q.fst_mem_support_of_mem_edges hQe) h
  have hsR : s ∉ R₀.support := fun h => hdisj (Q.snd_mem_support_of_mem_edges hQe) h
  have hside : ∀ {z t₀} (p : G₀.Walk z t₀), t₀ ∈ A → p.IsPath →
      (∀ x ∈ p.support, x ≠ z → x ≠ t₀ → x ∉ X) → z ∉ R₀.support →
      ∀ x ∈ p.support, x ∉ R₀.support := by
    intro z t₀ p ht₀ hp hpin hz x hx hxR
    by_cases hxz : x = z
    · exact hz (hxz ▸ hxR)
    · by_cases hxt : x = t₀
      · exact (hRU x hxR).1 (hxt ▸ ht₀)
      · exact (hRU x hxR).2 ⟨hpin x hx hxz hxt,
          isConnectedAvoiding_of_mem_path_aux ht₀ p hp hpin hx hxz⟩
  refine undoEdgeCandidateWalks_isSome_of_walk_ys hverts hC.2.1 Q R₀ halt hQ hQe hR₀ hdisj
    (py.append (σ.append ps.reverse)) fun x hx hxR => ?_
  rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff, Walk.support_reverse,
    List.mem_reverse] at hx
  rcases hx with hx | hx | hx
  · exact hside py ht hpy hpyin hyR x hx hxR
  · exact (hRU x hxR).1 (hσ x hx)
  · exact hside ps ht' hps hpsin hsR x hx hxR

/-! ### Part 4: Rule 2 search completeness (`r2 = rule2PocketChain`) -/

/-- When `s(y, s) ∈ Q.edges`, `rule2PocketChain y s N Q.support` is a `G₀.Adj`-chain from `u₁`
to `v₁` whose vertices lie in `Q.support ∪ N` and whose internal vertices avoid `C`. -/
theorem rule2PocketChain_spec [DecidableEq V]
    {C L₁ N L₂ : List V} {a b y s u₁ v₁ : V} {P₀ : G₀.Walk a b}
    (hP₀ : IsTPath G₀ C P₀) (hsupp : P₀.support = L₁ ++ y :: N ++ s :: L₂)
    (Q : (G₀ ⊔ edge y s).Walk u₁ v₁) (hQ : IsTPath (G₀ ⊔ edge y s) C Q) (hQe : s(y, s) ∈ Q.edges) :
    let X := rule2PocketChain y s N Q.support
    X.IsChain G₀.Adj ∧ X.head? = some u₁ ∧ X.getLast? = some v₁ ∧
      (∀ w ∈ X, w ∈ Q.support ∨ w ∈ N) ∧
      (∀ w ∈ X, w ∈ C → w = u₁ ∨ w = v₁) := by
  have hchN : (y :: N ++ [s]).IsChain G₀.Adj := by
    have h := P₀.isChain_adj_support
    rw [hsupp] at h
    exact h.infix ⟨L₁, L₂, by simp⟩
  have hheadQ : Q.support.head? = some u₁ := by rw [← Walk.cons_tail_support]; rfl
  have hlastQ : Q.support.getLast? = some v₁ := by
    rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
  have hndQ := hQ.1.support_nodup
  have hchQ := Q.isChain_adj_support
  obtain ⟨X₁, X₂, hsplit | hsplit⟩ := Walk.exists_split_of_mem_edges hQe
  · have hnd' : (X₁ ++ y :: s :: X₂).Nodup := hsplit ▸ hndQ
    have hidx_y : (X₁ ++ y :: s :: X₂).idxOf y = X₁.length := idxOf_eq_length_left hnd'
    have hnd'' : ((X₁ ++ [y]) ++ s :: X₂).Nodup := by simpa using hnd'
    have hidx_s : (X₁ ++ y :: s :: X₂).idxOf s = X₁.length + 1 := by
      have h := idxOf_eq_length_left hnd''
      simpa using h
    have hlt : Q.support.idxOf y < Q.support.idxOf s := by
      rw [hsplit, hidx_y, hidx_s]; omega
    have htake : Q.support.take (Q.support.idxOf y) = X₁ := by
      rw [hsplit]; exact take_idxOf_of_nodup hnd'
    have hdrop : Q.support.drop (Q.support.idxOf s + 1) = X₂ := by
      have h := drop_idxOf_succ_of_nodup hnd''
      rw [hsplit]; simpa using h
    have hX_eq : rule2PocketChain y s N Q.support = X₁ ++ (y :: N ++ [s]) ++ X₂ := by
      unfold rule2PocketChain
      simp [hlt, htake, hdrop]
    dsimp only
    rw [hX_eq]
    have hnd_dec := hnd'
    rw [List.nodup_append, List.nodup_cons, List.nodup_cons] at hnd_dec
    have hys : y ≠ s := fun e => hnd_dec.2.1.1 (by simp [e])
    have hsX₁ : s ∉ X₁ := fun e => hnd_dec.2.2 s e s (by simp) rfl
    have hyX₂ : y ∉ s :: X₂ := hnd_dec.2.1.1
    have hchQ' := hsplit ▸ hchQ
    have e1 : X₁ ++ y :: s :: X₂ = (X₁ ++ [y]) ++ (s :: X₂) := by simp
    rw [e1] at hchQ'
    have c1 : (X₁ ++ [y]).IsChain G₀.Adj := isChain_of_sup_edge hchQ'.left_of_append (by
      simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨hsX₁, hys.symm⟩)
    have c2 : (s :: X₂).IsChain G₀.Adj := by
      rw [edge_comm] at hchQ'
      exact isChain_of_sup_edge hchQ'.right_of_append hyX₂
    have hch_all : (X₁ ++ (y :: N ++ [s]) ++ X₂).IsChain G₀.Adj := by
      have h1 := c1.append_overlap (show ([y] ++ (N ++ [s])).IsChain G₀.Adj by simpa using hchN)
        (by simp)
      have h2 := List.IsChain.append_overlap (l₁ := X₁ ++ [y] ++ N) (l₂ := [s]) (l₃ := X₂)
        (by simpa using h1) c2 (by simp)
      simpa using h2
    have hh_all : (X₁ ++ (y :: N ++ [s]) ++ X₂).head? = some u₁ := by
      rw [hsplit] at hheadQ
      cases X₁ <;> simpa using hheadQ
    have hl_all : (X₁ ++ (y :: N ++ [s]) ++ X₂).getLast? = some v₁ := by
      rw [hsplit] at hlastQ
      have e_old : X₁ ++ y :: s :: X₂ = (X₁ ++ [y]) ++ (s :: X₂) := by simp
      have e_new : X₁ ++ (y :: N ++ [s]) ++ X₂ = (X₁ ++ y :: N) ++ (s :: X₂) := by simp
      rw [e_old, List.getLast?_append_of_ne_nil _ (by simp)] at hlastQ
      rw [e_new, List.getLast?_append_of_ne_nil _ (by simp)]
      exact hlastQ
    have hsub : ∀ w ∈ X₁ ++ (y :: N ++ [s]) ++ X₂, w ∈ Q.support ∨ w ∈ N := by
      intro w hw
      rw [hsplit]
      simp only [List.cons_append, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hw ⊢
      tauto
    refine ⟨hch_all, hh_all, hl_all, hsub, fun w hw hwC => ?_⟩
    rcases hsub w hw with hwQ | hwN
    · by_contra hne
      push Not at hne
      exact (hQ.2.2.2 w hwQ hne.1 hne.2).1 hwC
    · exact absurd hwC (not_mem_C_of_mem_window hP₀ hsupp hwN)
  · have hnd' : (X₁ ++ s :: y :: X₂).Nodup := hsplit ▸ hndQ
    have hidx_s : (X₁ ++ s :: y :: X₂).idxOf s = X₁.length := idxOf_eq_length_left hnd'
    have hnd'' : ((X₁ ++ [s]) ++ y :: X₂).Nodup := by simpa using hnd'
    have hidx_y : (X₁ ++ s :: y :: X₂).idxOf y = X₁.length + 1 := by
      have h := idxOf_eq_length_left hnd''
      simpa using h
    have hnlt : ¬ (Q.support.idxOf y < Q.support.idxOf s) := by
      rw [hsplit, hidx_y, hidx_s]; omega
    have htake : Q.support.take (Q.support.idxOf s) = X₁ := by
      rw [hsplit]; exact take_idxOf_of_nodup hnd'
    have hdrop : Q.support.drop (Q.support.idxOf y + 1) = X₂ := by
      have h := drop_idxOf_succ_of_nodup hnd''
      rw [hsplit]; simpa using h
    have hX_eq : rule2PocketChain y s N Q.support = X₁ ++ (y :: N ++ [s]).reverse ++ X₂ := by
      unfold rule2PocketChain
      simp [hnlt, htake, hdrop]
    dsimp only
    rw [hX_eq]
    have hnd_dec := hnd'
    rw [List.nodup_append, List.nodup_cons, List.nodup_cons] at hnd_dec
    have hsy : s ≠ y := fun e => hnd_dec.2.1.1 (by simp [e])
    have hyX₁ : y ∉ X₁ := fun e => hnd_dec.2.2 y e y (by simp) rfl
    have hsX₂ : s ∉ y :: X₂ := hnd_dec.2.1.1
    have hchQ' := hsplit ▸ hchQ
    have e1 : X₁ ++ s :: y :: X₂ = (X₁ ++ [s]) ++ (y :: X₂) := by simp
    rw [e1] at hchQ'
    have c1 : (X₁ ++ [s]).IsChain G₀.Adj := by
      rw [edge_comm] at hchQ'
      exact isChain_of_sup_edge hchQ'.left_of_append (by
        simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨hyX₁, hsy.symm⟩)
    have c2 : (y :: X₂).IsChain G₀.Adj := isChain_of_sup_edge hchQ'.right_of_append hsX₂
    have hchN_rev : (s :: N.reverse ++ [y]).IsChain G₀.Adj := by
      have hrev : (y :: N ++ [s]).reverse = s :: N.reverse ++ [y] := by simp
      rw [← hrev, List.isChain_reverse]
      exact hchN.imp fun _ _ h => h.symm
    have hch_all : (X₁ ++ (y :: N ++ [s]).reverse ++ X₂).IsChain G₀.Adj := by
      have hrev : (y :: N ++ [s]).reverse = [s] ++ (N.reverse ++ [y]) := by simp
      rw [hrev]
      have h1 := c1.append_overlap (by simpa using hchN_rev) (by simp)
      have h2 := List.IsChain.append_overlap (l₁ := X₁ ++ [s] ++ N.reverse) (l₂ := [y]) (l₃ := X₂)
        (by simpa using h1) c2 (by simp)
      simpa using h2
    have hh_all : (X₁ ++ (y :: N ++ [s]).reverse ++ X₂).head? = some u₁ := by
      rw [hsplit] at hheadQ
      cases X₁ <;> simpa using hheadQ
    have hl_all : (X₁ ++ (y :: N ++ [s]).reverse ++ X₂).getLast? = some v₁ := by
      rw [hsplit] at hlastQ
      have e_old : X₁ ++ s :: y :: X₂ = (X₁ ++ [s]) ++ (y :: X₂) := by simp
      have e_new : X₁ ++ (y :: N ++ [s]).reverse ++ X₂ = (X₁ ++ s :: N.reverse) ++ (y :: X₂) := by
        simp
      rw [e_old, List.getLast?_append_of_ne_nil _ (by simp)] at hlastQ
      rw [e_new, List.getLast?_append_of_ne_nil _ (by simp)]
      exact hlastQ
    have hsub : ∀ w ∈ X₁ ++ (y :: N ++ [s]).reverse ++ X₂, w ∈ Q.support ∨ w ∈ N := by
      intro w hw
      rw [hsplit]
      simp only [List.cons_append, List.mem_append, List.mem_cons, List.mem_reverse,
        List.not_mem_nil, or_false] at hw ⊢
      tauto
    refine ⟨hch_all, hh_all, hl_all, hsub, fun w hw hwC => ?_⟩
    rcases hsub w hw with hwQ | hwN
    · by_contra hne
      push Not at hne
      exact (hQ.2.2.2 w hwQ hne.1 hne.2).1 hwC
    · exact absurd hwC (not_mem_C_of_mem_window hP₀ hsupp hwN)

/-- **Rule 2 search completeness (`undoEdgeCandidateWalks_isSome_of_rule_two`):**
Whenever `Alternate C c d u₁ v₁` and a walk `W : G₀.Walk c d` in `G₀` avoids `Q.support ∪ N`,
candidate `r2 = rule2PocketChain y s N Q.support` in `undoEdgeCandidateChains` succeeds under
`runCandidateSearches`. -/
theorem undoEdgeCandidateWalks_isSome_of_rule_two [DecidableEq V] [DecidableRel G₀.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {verts C A B L₁ N L₂ : List V} {a b y s u₁ v₁ c d : V} {P₀ : G₀.Walk a b}
    (hverts : ∀ v : V, v ∈ verts) (hCnd : C.Nodup)
    (hP₀ : IsTPath G₀ C P₀) (hsupp : P₀.support = L₁ ++ y :: N ++ s :: L₂)
    (Q : (G₀ ⊔ edge y s).Walk u₁ v₁) (R_supp : List V)
    (hQ : IsTPath (G₀ ⊔ edge y s) C Q) (hQe : s(y, s) ∈ Q.edges)
    (halt : Alternate C c d u₁ v₁) (W : G₀.Walk c d)
    (hW : ∀ w ∈ W.support, w ∉ Q.support ∧ w ∉ N) :
    (runCandidateSearches G₀ verts C
      ((undoEdgeCandidateChains G₀ verts C A B P₀.support L₁ N L₂ y s Q.support R_supp).filterMap
        (walkOfChainOption G₀))).1.isSome = true := by
  obtain ⟨hch, hh, hl, hsub, hin⟩ := rule2PocketChain_spec hP₀ hsupp Q hQ hQe
  have hmem :=
    mem_undoEdgeCandidateChains_r2 (G₀ := G₀) verts C A B P₀.support L₁ N L₂ y s Q.support R_supp
  refine runCandidateSearches_isSome_of_chain hverts hCnd hmem hch hh hl hQ.2.1 hQ.2.2.1 hin
    halt W fun w hw hwX => ?_
  rcases hsub w hwX with hwQ | hwN
  · exact (hW w hw).1 hwQ
  · exact (hW w hw).2 hwN

/-! ### Part 5: Direct bridge extraction via `bridgeOfList` and Rule 3 search completeness -/

/-- If `[u, w]` is a sublist of a nodup list `l`, then `w` is not the head of `l`. -/
private theorem ne_head_of_sublist_two' {l : List V} (hnd : l.Nodup) {u w c : V}
    (hh : l.head? = some c) (hsub : [u, w].Sublist l) : w ≠ c := by
  match l, hh with
  | c :: t, rfl =>
    rintro rfl
    have hct : w ∉ t := (List.nodup_cons.mp hnd).1
    rcases List.sublist_cons_iff.mp hsub with h | ⟨r, hr, h⟩
    · exact hct (h.subset (by simp))
    · simp only [List.cons.injEq] at hr
      exact hct (h.subset (hr.2 ▸ by simp))

/-- If `[u, w, v]` is a sublist of a nodup list `l`, then `w` is neither the first nor the last
entry of `l`. -/
private theorem ne_ends_of_sublist_three' {l : List V} (hnd : l.Nodup) {u w v c d : V}
    (hh : l.head? = some c) (hl : l.getLast? = some d) (hsub : [u, w, v].Sublist l) :
    w ≠ c ∧ w ≠ d := by
  have hsub1 : [u, w].Sublist l := (show [u, w].Sublist [u, w, v] by simp).trans hsub
  have hsub2 : [v, w].Sublist l.reverse :=
    (show [v, w].Sublist [v, w, u] by simp).trans (List.sublist_reverse_iff.mpr hsub)
  exact ⟨ne_head_of_sublist_two' hnd hh hsub1,
    ne_head_of_sublist_two' (List.nodup_reverse.mpr hnd) (by rw [List.head?_reverse]; exact hl)
      hsub2⟩

/-- **Properties of any bridge `(σ, M, z)` returned by `bridgeOfList N (L₁ ++ L₂) L`** on
`L ∈ {R₀.support, R₀.support.reverse}`:
`M = t :: K` is non-empty, `σ ∈ N`, `z ∈ L₁ ∨ z ∈ L₂`, `(σ :: t :: K ++ [z]).IsChain G₀.Adj` and
`Nodup`, every `w ∈ t :: K` is off `C ∪ P₀.support ∪ Q.support`, and when `N` is off side `B`
(resp. `A`), `t` reaches `A` (resp. `B`) off `P₀.support`. -/
theorem bridgeOfList_props_of_mem_R [DecidableEq V]
    {C A B L₁ N L₂ : List V} {a b y s u₁ v₁ u₂ v₂ : V} {k : ℕ} {P₀ : G₀.Walk a b}
    (_hCnd : C.Nodup) (_hrot : C.rotate k = a :: A ++ b :: B) (hP₀ : IsTPath G₀ C P₀)
    (hsupp : P₀.support = L₁ ++ y :: N ++ s :: L₂)
    (hind : ∀ u ∈ P₀.support, ∀ v ∈ P₀.support, G₀.Adj u v → IsListEdge P₀.support u v)
    (htight : IsTight G₀ C A B P₀.support)
    (Q : (G₀ ⊔ edge y s).Walk u₁ v₁) (R₀ : G₀.Walk u₂ v₂)
    (hQe : s(y, s) ∈ Q.edges) (hR₀ : IsTPath G₀ C R₀) (hdisj : Q.support.Disjoint R₀.support)
    {L : List V} (hL_or : L = R₀.support ∨ L = R₀.support.reverse)
    {σ z : V} {M : List V} (hb : bridgeOfList N (L₁ ++ L₂) L = some (σ, M, z)) :
    ∃ (t : V) (K : List V),
      M = t :: K ∧ σ ∈ N ∧ (z ∈ L₁ ∨ z ∈ L₂) ∧
      (σ :: t :: K ++ [z]).IsChain G₀.Adj ∧ (σ :: t :: K ++ [z]).Nodup ∧
      (∀ w ∈ t :: K, w ∈ R₀.support ∧ w ∉ C ∧ w ∉ P₀.support ∧ w ∉ Q.support ∧
        ¬ IsThirdKind G₀ C A B P₀.support w) := by
  obtain ⟨hσN, hzOut, hM_not, hinf⟩ := bridgeOfList_spec hb
  have hzL : z ∈ L₁ ∨ z ∈ L₂ := List.mem_append.mp hzOut
  have hyQ : y ∈ Q.support := Q.fst_mem_support_of_mem_edges hQe
  have hsQ : s ∈ Q.support := Q.snd_mem_support_of_mem_edges hQe
  have hL_ch : L.IsChain G₀.Adj := by
    rcases hL_or with rfl | rfl
    · exact R₀.isChain_adj_support
    · exact List.isChain_reverse.mpr (R₀.isChain_adj_support.imp fun _ _ h => h.symm)
  have hL_nd : L.Nodup := by
    rcases hL_or with rfl | rfl
    · exact hR₀.1.support_nodup
    · exact List.nodup_reverse.mpr hR₀.1.support_nodup
  have hch_M : (σ :: M ++ [z]).IsChain G₀.Adj := hL_ch.infix hinf
  have hnd_M : (σ :: M ++ [z]).Nodup := hL_nd.sublist hinf.sublist
  have hL_mem_R : ∀ w ∈ L, w ∈ R₀.support := by
    intro w hw
    rcases hL_or with rfl | rfl
    · exact hw
    · exact List.mem_reverse.mp hw
  have hNP : ∀ w ∈ N, w ∈ P₀.support := fun w hw => by rw [hsupp]; simp [hw]
  have hzP : z ∈ P₀.support := by
    rw [hsupp]
    rcases hzL with hz₁ | hz₂
    · simp [hz₁]
    · simp [hz₂]
  have hndP : (L₁ ++ y :: N ++ s :: L₂).Nodup := hsupp ▸ hP₀.1.support_nodup
  have hnot_edge_σz : ¬ IsListEdge P₀.support σ z := by
    intro hl
    rw [hsupp] at hl
    have hzw := hl.mem_window hndP hσN
    have hzR : z ∈ R₀.support := hL_mem_R z (hinf.sublist.subset (by simp))
    have hzQ : z ∉ Q.support := fun h => hdisj h hzR
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hzw
    rcases hzw with rfl | h | rfl
    · exact hzQ hyQ
    · have hndP' : (L₁ ++ (y :: N) ++ (s :: L₂)).Nodup := by simpa using hndP
      rw [List.nodup_append, List.nodup_append] at hndP'
      rcases hzL with hz₁ | hz₂
      · exact hndP'.1.2.2 z hz₁ z (List.mem_cons_of_mem _ h) rfl
      · exact hndP'.2.2 z (List.mem_append_right _ (List.mem_cons_of_mem _ h))
          z (List.mem_cons_of_mem _ hz₂) rfl
    · exact hzQ hsQ
  -- `M` cannot be empty, otherwise `G₀.Adj σ z` would give `IsListEdge P₀.support σ z`
  have hM_ne : M ≠ [] := by
    rintro rfl
    have hadj : G₀.Adj σ z := (List.isChain_cons_cons.mp hch_M).1
    exact hnot_edge_σz (hind σ (hNP σ hσN) z hzP hadj)
  obtain ⟨t, K, rfl⟩ := List.exists_cons_of_ne_nil hM_ne
  have hheadR : R₀.support.head? = some u₂ := by rw [← Walk.cons_tail_support]; rfl
  have hlastR : R₀.support.getLast? = some v₂ := by
    rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
  have hK_off : ∀ w ∈ t :: K, w ∈ R₀.support ∧ w ∉ C ∧ w ∉ P₀.support ∧ w ∉ Q.support := by
    intro w hw
    have hwL : w ∈ L := hinf.sublist.subset (List.mem_cons_of_mem _ (List.mem_append_left _ hw))
    have hwR : w ∈ R₀.support := hL_mem_R w hwL
    have hwQ : w ∉ Q.support := fun h => hdisj h hwR
    have hw_not := hM_not w hw
    have hwP : w ∉ P₀.support := by
      intro hwP_in
      rw [hsupp] at hwP_in
      simp only [List.mem_append, List.mem_cons] at hwP_in
      rcases hwP_in with (h | rfl | h) | rfl | h
      · exact hw_not.2 (List.mem_append_left _ h)
      · exact hwQ hyQ
      · exact hw_not.1 h
      · exact hwQ hsQ
      · exact hw_not.2 (List.mem_append_right _ h)
    have hw_sub : [σ, w, z].Sublist L := by
      have h1 : [σ, w, z].Sublist (σ :: (t :: K) ++ [z]) := by
        rw [List.cons_append]
        refine List.Sublist.cons_cons σ ?_
        have h2 : ([w] ++ [z]).Sublist ((t :: K) ++ [z]) :=
          List.Sublist.append (List.singleton_sublist.mpr hw) (by simp)
        simpa using h2
      exact (by simpa using h1 : [σ, w, z].Sublist (σ :: t :: K ++ [z])).trans hinf.sublist
    have hwc_d : w ≠ u₂ ∧ w ≠ v₂ := by
      rcases hL_or with rfl | rfl
      · exact ne_ends_of_sublist_three' hR₀.1.support_nodup hheadR hlastR hw_sub
      · have hrev : [z, w, σ].Sublist R₀.support :=
          List.sublist_reverse_iff.mp (show [z, w, σ].reverse.Sublist R₀.support.reverse from hw_sub)
        exact ne_ends_of_sublist_three' hR₀.1.support_nodup hheadR hlastR hrev
    exact ⟨hwR, (hR₀.2.2.2 w hwR hwc_d.1 hwc_d.2).1, hwP, hwQ⟩
  refine ⟨t, K, rfl, hσN, hzL, hch_M, hnd_M, fun w hw => ?_⟩
  obtain ⟨hwR, hwC, hwP, hwQ⟩ := hK_off w hw
  refine ⟨hwR, hwC, hwP, hwQ, fun hw3 => hnot_edge_σz ?_⟩
  have hch_tK : (t :: K).IsChain G₀.Adj := (List.isChain_cons_cons.mp hch_M.left_of_append).2
  have hch_tKz : (t :: K ++ [z]).IsChain G₀.Adj := (List.isChain_cons_cons.mp hch_M).2
  have hadj_tσ : G₀.Adj t σ := (List.isChain_cons_cons.mp hch_M).1.symm
  obtain ⟨q_wt, hq_wt⟩ := exists_walk_of_isChain hch_tK hw List.mem_cons_self
  obtain ⟨q_wz, hq_wz⟩ := exists_walk_of_isChain hch_tKz (List.mem_append_left _ hw)
    (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  obtain ⟨v', w', hvw, hall⟩ := htight w hwC hwP hw3.2.2
  have hσ_vw := hall σ (hNP σ hσN) (isConnectedAvoiding_of_walk_mem
    (show σ ∈ ({σ} : Set V) from rfl) (q_wt.append (Walk.cons hadj_tσ .nil)) fun x hx hxX => by
      rw [Walk.mem_support_append_iff, Walk.support_cons, Walk.support_nil] at hx
      rcases hx with hx | hx
      · have hxK := hq_wt x hx
        exact absurd hxX (by rintro (h | h); exacts [(hK_off x hxK).2.1 h, (hK_off x hxK).2.2.1 h])
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact absurd hxX (by
            rintro (h | h)
            · exact (hK_off x List.mem_cons_self).2.1 h
            · exact (hK_off x List.mem_cons_self).2.2.1 h)
        · exact Or.inr rfl)
  have hz_vw := hall z hzP (isConnectedAvoiding_of_walk_mem
    (show z ∈ ({z} : Set V) from rfl) q_wz fun x hx hxX => by
      have hx' := hq_wz x hx
      rcases List.mem_append.mp hx' with hxK | hxz
      · exact absurd hxX (by rintro (h | h); exacts [(hK_off x hxK).2.1 h, (hK_off x hxK).2.2.1 h])
      · exact Or.inr (List.mem_singleton.mp hxz))
  have hσz_ne : σ ≠ z := fun e => by
    subst e
    exact (List.nodup_cons.mp hnd_M).1 (by simp)
  rcases hσ_vw with rfl | rfl <;> rcases hz_vw with rfl | rfl
  · exact absurd rfl hσz_ne
  · exact hvw
  · exact hvw.symm
  · exact absurd rfl hσz_ne

/-- **Direct bridge existence on `R₀.support` or `R₀.support.reverse` (`exists_bridgeOfList_of_meets_pocket_and_side`):**
When `R₀` meets both `N` (`v₀ ∈ R₀.support`, `v₀ ∈ N`) and the side-`S` world (`v₁ ∈ R₀.support`,
`v₁ ∈ S ∨ (v₁ ∉ C ∪ P₀.support ∧ IsConnectedAvoiding G₀ (C ∪ P₀.support) v₁ S)`), where `S ⊆ C \ P₀.support`
and no vertex of `N` is on side `S`, `bridgeOfList N (L₁ ++ L₂) L` returns `some (σ, M, z)` on
either `L = R₀.support` or `L = R₀.support.reverse`. -/
theorem exists_bridgeOfList_of_meets_pocket_and_side [DecidableEq V]
    {C L₁ N L₂ S : List V} {a b y s u₁ v₁ u₂ v₂ : V} {P₀ : G₀.Walk a b}
    (hP₀ : IsTPath G₀ C P₀) (hsupp : P₀.support = L₁ ++ y :: N ++ s :: L₂)
    (hSC : ∀ x ∈ S, x ∈ C ∧ x ∉ P₀.support)
    (hN : ∀ v ∈ N, ¬ IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ S} v)
    (Q : (G₀ ⊔ edge y s).Walk u₁ v₁) (R₀ : G₀.Walk u₂ v₂)
    (hQe : s(y, s) ∈ Q.edges) (hR₀ : IsTPath G₀ C R₀) (hdisj : Q.support.Disjoint R₀.support)
    {w₀ w₁ : V} (hw₀R : w₀ ∈ R₀.support) (hw₀N : w₀ ∈ N) (hw₁R : w₁ ∈ R₀.support)
    (hw₁S : w₁ ∈ S ∨ (w₁ ∉ {x | x ∈ C ∨ x ∈ P₀.support} ∧
      IsConnectedAvoiding G₀ {x | x ∈ C ∨ x ∈ P₀.support} w₁ {x | x ∈ S})) :
    ∃ L, (L = R₀.support ∨ L = R₀.support.reverse) ∧
      (bridgeOfList N (L₁ ++ L₂) L).isSome = true := by
  have hyQ : y ∈ Q.support := Q.fst_mem_support_of_mem_edges hQe
  have hsQ : s ∈ Q.support := Q.snd_mem_support_of_mem_edges hQe
  have hNP : ∀ w ∈ N, w ∈ P₀.support := fun w hw => by rw [hsupp]; simp [hw]
  have hw₁P : w₁ ∉ P₀.support := by
    rcases hw₁S with hS | ⟨hw₁X, -⟩
    · exact (hSC w₁ hS).2
    · exact fun h => hw₁X (Or.inr h)
  have hw₁N : w₁ ∉ N := fun h => hw₁P (hNP w₁ h)
  obtain ⟨α₀, β₀, hR_eq⟩ := List.append_of_mem hw₁R
  have hw₀_ab : w₀ ∈ α₀ ∨ w₀ ∈ β₀ := by
    have h := hw₀R
    rw [hR_eq] at h
    rcases List.mem_append.mp h with h | h
    · exact Or.inl h
    · rcases List.mem_cons.mp h with rfl | h
      · exact absurd hw₀N hw₁N
      · exact Or.inr h
  obtain ⟨L, α, β, hL_or, hL_eq, hw₀α⟩ :
      ∃ L α β, (L = R₀.support ∨ L = R₀.support.reverse) ∧ L = α ++ w₁ :: β ∧ w₀ ∈ α := by
    rcases hw₀_ab with h | h
    · exact ⟨R₀.support, α₀, β₀, Or.inl rfl, hR_eq, h⟩
    · refine ⟨R₀.support.reverse, β₀.reverse, α₀.reverse, Or.inr rfl, ?_, List.mem_reverse.mpr h⟩
      rw [hR_eq]; simp
  obtain ⟨α₁, σ, α₂, rfl, hσN, hα₂⟩ :=
    exists_last_mem (Z := {w | w ∈ N}) α ⟨w₀, hw₀α, hw₀N⟩
  have hndP : (L₁ ++ y :: N ++ s :: L₂).Nodup := hsupp ▸ hP₀.1.support_nodup
  have hdisj_N_out : ∀ x ∈ N, x ∉ L₁ ++ L₂ := by
    intro x hxN hxOut
    have hndP' : (L₁ ++ (y :: N) ++ (s :: L₂)).Nodup := by simpa using hndP
    rw [List.nodup_append, List.nodup_append] at hndP'
    rcases List.mem_append.mp hxOut with hx₁ | hx₂
    · exact hndP'.1.2.2 x hx₁ x (List.mem_cons_of_mem _ hxN) rfl
    · exact hndP'.2.2 x (List.mem_append_right _ (List.mem_cons_of_mem _ hxN))
        x (List.mem_cons_of_mem _ hx₂) rfl
  refine ⟨L, hL_or, ?_⟩
  have hL_split : L = α₁ ++ σ :: (α₂ ++ w₁ :: β) := by rw [hL_eq]; simp
  rw [hL_split]
  refine bridgeOfList_isSome hdisj_N_out hσN ?_
  -- Show there is some `z₀ ∈ α₂ ++ w₁ :: β` with `z₀ ∈ L₁ ++ L₂` (in fact in `α₂`).
  by_contra hno
  push Not at hno
  have hL_ch : L.IsChain G₀.Adj := by
    rcases hL_or with rfl | rfl
    · exact R₀.isChain_adj_support
    · exact List.isChain_reverse.mpr (R₀.isChain_adj_support.imp fun _ _ h => h.symm)
  have hinf : (σ :: α₂ ++ [w₁]) <:+: L := ⟨α₁, β, by rw [hL_eq]; simp⟩
  have hch_seg : (σ :: α₂ ++ [w₁]).IsChain G₀.Adj := hL_ch.infix hinf
  obtain ⟨W_seg, hW_seg⟩ := exists_walk_of_chain (u := σ) (v := w₁) (σ :: α₂ ++ [w₁]) hch_seg
    (by simp) (List.getLast?_concat ..)
  have hheadR : R₀.support.head? = some u₂ := by rw [← Walk.cons_tail_support]; rfl
  have hlastR : R₀.support.getLast? = some v₂ := by
    rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
  have hα₂_off : ∀ x ∈ α₂, x ∉ C ∧ x ∉ P₀.support := by
    intro x hx
    have hxL : x ∈ L := hinf.sublist.subset (by simp [hx])
    have hxR : x ∈ R₀.support := by
      rcases hL_or with rfl | rfl
      · exact hxL
      · exact List.mem_reverse.mp hxL
    have hxQ : x ∉ Q.support := fun h => hdisj h hxR
    have hxN : x ∉ N := hα₂ x hx
    have hxOut : x ∉ L₁ ++ L₂ := hno x (List.mem_append_left _ hx)
    have hxP : x ∉ P₀.support := by
      intro hxP_in
      rw [hsupp] at hxP_in
      simp only [List.mem_append, List.mem_cons] at hxP_in
      rcases hxP_in with (h | rfl | h) | rfl | h
      · exact hxOut (List.mem_append_left _ h)
      · exact hxQ hyQ
      · exact hxN h
      · exact hxQ hsQ
      · exact hxOut (List.mem_append_right _ h)
    have hx_sub : [σ, x, w₁].Sublist L := by
      have h1 : [σ, x, w₁].Sublist (σ :: α₂ ++ [w₁]) := by
        rw [List.cons_append]
        refine List.Sublist.cons_cons σ ?_
        have h2 : ([x] ++ [w₁]).Sublist (α₂ ++ [w₁]) :=
          List.Sublist.append (List.singleton_sublist.mpr hx) (by simp)
        simpa using h2
      exact h1.trans hinf.sublist
    have hxc_d : x ≠ u₂ ∧ x ≠ v₂ := by
      rcases hL_or with rfl | rfl
      · exact ne_ends_of_sublist_three' hR₀.1.support_nodup hheadR hlastR hx_sub
      · have hrev : [w₁, x, σ].Sublist R₀.support :=
          List.sublist_reverse_iff.mp (show [w₁, x, σ].reverse.Sublist R₀.support.reverse from hx_sub)
        exact ne_ends_of_sublist_three' hR₀.1.support_nodup hheadR hlastR hrev
    exact ⟨(hR₀.2.2.2 x hxR hxc_d.1 hxc_d.2).1, hxP⟩
  -- Now `σ` reaches `S` avoiding `C ∪ P₀.support`, contradicting `hN σ hσN`!
  apply hN σ hσN
  rcases hw₁S with hw₁_in_S | ⟨hw₁X, s₀, hs₀, p_S, -, hp_S⟩
  · refine isConnectedAvoiding_of_walk_mem hw₁_in_S W_seg fun x hx hxX => ?_
    rw [hW_seg] at hx
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | hx | rfl
    · exact Or.inl rfl
    · exact absurd hxX (by rintro (h | h); exacts [(hα₂_off x hx).1 h, (hα₂_off x hx).2 h])
    · exact Or.inr rfl
  · refine isConnectedAvoiding_of_walk_mem hs₀ (W_seg.append p_S) fun x hx hxX => ?_
    rw [Walk.mem_support_append_iff, hW_seg] at hx
    rcases hx with hx | hx
    · simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | hx | rfl
      · exact Or.inl rfl
      · exact absurd hxX (by rintro (h | h); exacts [(hα₂_off x hx).1 h, (hα₂_off x hx).2 h])
      · exact absurd hxX hw₁X
    · by_cases hxw₁ : x = w₁
      · subst hxw₁; exact absurd hxX hw₁X
      · by_cases hxs₀ : x = s₀
        · exact Or.inr hxs₀
        · exact absurd hxX (hp_S x hx hxw₁ hxs₀)

/-- **Characterization of `rule3ChainOfBridge P₀.support L₁ (some (σ, t :: K, z))`:**
It equals the support `P_new.support` of a rerouted `C`-path `P_new : G₀.Walk a b` in `G₀`
whose vertices lie in `P₀.support ∪ (t :: K)` and which misses `y` when `z ∈ L₁` and misses `s`
when `z ∈ L₂`. -/
theorem rule3ChainOfBridge_spec [DecidableEq V]
    {C L₁ N L₂ : List V} {a b y s σ t z : V} {K : List V} {P₀ : G₀.Walk a b}
    (hP₀ : IsTPath G₀ C P₀) (hsupp : P₀.support = L₁ ++ y :: N ++ s :: L₂)
    (hσ : σ ∈ N) (hz : z ∈ L₁ ∨ z ∈ L₂)
    (hcM : (σ :: t :: K ++ [z]).IsChain G₀.Adj) (hndM : (σ :: t :: K ++ [z]).Nodup)
    (hK : ∀ w ∈ t :: K, w ∉ C ∧ w ∉ P₀.support) :
    ∃ P_new : G₀.Walk a b, IsTPath G₀ C P_new ∧
      rule3ChainOfBridge P₀.support L₁ (some (σ, t :: K, z)) = P_new.support ∧
      (∀ w ∈ P_new.support, w ∈ P₀.support ∨ w ∈ t :: K) ∧
      ((z ∈ L₁ ∧ y ∉ P_new.support) ∨ (z ∈ L₂ ∧ s ∉ P_new.support)) := by
  have hndP : (L₁ ++ y :: N ++ s :: L₂).Nodup := hsupp ▸ hP₀.1.support_nodup
  obtain ⟨N₀, N₁, rfl⟩ := List.append_of_mem hσ
  by_cases hz₁ : z ∈ L₁
  · obtain ⟨L₁₀, L₁₁, rfl⟩ := List.append_of_mem hz₁
    have hsupp' : P₀.support = L₁₀ ++ z :: (L₁₁ ++ y :: N₀) ++ σ :: (N₁ ++ s :: L₂) := by
      rw [hsupp]; simp
    have hrev_eq : (σ :: (t :: K) ++ [z]).reverse = z :: (t :: K).reverse ++ [σ] := by simp
    have hcM' : (z :: (t :: K).reverse ++ [σ]).IsChain G₀.Adj := by
      rw [← hrev_eq, List.isChain_reverse]
      exact hcM.imp fun _ _ h => h.symm
    have hndM' : (z :: (t :: K).reverse ++ [σ]).Nodup := by
      rw [← hrev_eq]
      exact List.nodup_reverse.mpr hndM
    have hK' : ∀ w ∈ (t :: K).reverse, w ∉ C ∧ w ∉ P₀.support :=
      fun w hw => hK w (List.mem_reverse.mp hw)
    obtain ⟨P_new, hP_new, hP_new_supp, hsub, hmiss⟩ :=
      exists_reroute_path_of_off hP₀ hsupp' hcM' hndM' hK'
    have hnd_z : (L₁₀ ++ z :: (L₁₁ ++ y :: (N₀ ++ σ :: N₁) ++ s :: L₂)).Nodup := by
      have h := hP₀.1.support_nodup; rw [hsupp] at h; simpa using h
    have hnd_σ : ((L₁₀ ++ z :: L₁₁ ++ y :: N₀) ++ σ :: (N₁ ++ s :: L₂)).Nodup := by
      have h := hP₀.1.support_nodup; rw [hsupp] at h; simpa using h
    have htake : P₀.support.take (P₀.support.idxOf z + 1) = L₁₀ ++ [z] := by
      have h := take_idxOf_succ_of_nodup hnd_z
      rw [hsupp]; simpa using h
    have hdrop : P₀.support.drop (P₀.support.idxOf σ) = σ :: (N₁ ++ s :: L₂) := by
      have h := drop_idxOf_of_nodup hnd_σ
      rw [hsupp]; simpa using h
    have hr3_eq : rule3ChainOfBridge P₀.support (L₁₀ ++ z :: L₁₁) (some (σ, t :: K, z)) =
        P_new.support := by
      unfold rule3ChainOfBridge
      simp [hz₁, htake, hdrop, hP_new_supp]
    exact ⟨P_new, hP_new, hr3_eq, fun w hw => (hsub w hw).imp id List.mem_reverse.mp,
      Or.inl ⟨hz₁, hmiss y (by simp)⟩⟩
  · have hz₂ : z ∈ L₂ := hz.resolve_left hz₁
    obtain ⟨L₂₀, L₂₁, rfl⟩ := List.append_of_mem hz₂
    have hsupp' : P₀.support = (L₁ ++ y :: N₀) ++ σ :: (N₁ ++ s :: L₂₀) ++ z :: L₂₁ := by
      rw [hsupp]; simp
    obtain ⟨P_new, hP_new, hP_new_supp, hsub, hmiss⟩ :=
      exists_reroute_path_of_off hP₀ hsupp' hcM hndM hK
    have hnd_σ : ((L₁ ++ y :: N₀) ++ σ :: (N₁ ++ s :: (L₂₀ ++ z :: L₂₁))).Nodup := by
      have h := hP₀.1.support_nodup; rw [hsupp] at h; simpa using h
    have hnd_z : ((L₁ ++ y :: (N₀ ++ σ :: N₁) ++ s :: L₂₀) ++ z :: L₂₁).Nodup := by
      have h := hP₀.1.support_nodup; rw [hsupp] at h; simpa using h
    have htake : P₀.support.take (P₀.support.idxOf σ + 1) = (L₁ ++ y :: N₀) ++ [σ] := by
      have h := take_idxOf_succ_of_nodup hnd_σ
      rw [hsupp]; simpa using h
    have hdrop : P₀.support.drop (P₀.support.idxOf z) = z :: L₂₁ := by
      have h := drop_idxOf_of_nodup hnd_z
      rw [hsupp]; simpa using h
    have hr3_eq : rule3ChainOfBridge P₀.support L₁ (some (σ, t :: K, z)) = P_new.support := by
      unfold rule3ChainOfBridge
      simp [hz₁, htake, hdrop, hP_new_supp]
    exact ⟨P_new, hP_new, hr3_eq, hsub, Or.inr ⟨hz₂, hmiss s (by simp)⟩⟩

/-- **Rule 3 search completeness (`undoEdgeCandidateWalks_isSome_of_rule_three`):**
When `bridgeOfList N (L₁ ++ L₂) L = some (σ, t :: K, z)` on `L ∈ {R₀.support, R₀.support.reverse}`
and the rerouted `C`-path `P_new : G₀.Walk a b` fails to separate `A` from `B` in `G₀`, running
`runCandidateSearches` on `undoEdgeCandidateChains` returns `some` valid crossing (candidate
`r3_1` or `r3_2` succeeds). -/
theorem undoEdgeCandidateWalks_isSome_of_rule_three [DecidableEq V] [DecidableRel G₀.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {verts C A B L₁ N L₂ : List V} {a b y s σ t z : V} {k : ℕ} {K : List V}
    {P₀ P_new : G₀.Walk a b} (Q_supp R_supp : List V)
    (hverts : ∀ v : V, v ∈ verts) (hCnd : C.Nodup) (hrot : C.rotate k = a :: A ++ b :: B)
    {L : List V} (hL_or : L = R_supp ∨ L = R_supp.reverse)
    (hb : bridgeOfList N (L₁ ++ L₂) L = some (σ, t :: K, z))
    (hP_new : IsTPath G₀ C P_new)
    (hr3_eq : rule3ChainOfBridge P₀.support L₁ (some (σ, t :: K, z)) = P_new.support)
    (hns : ¬ Separates G₀ {v | v ∈ P_new.support} {v | v ∈ A} {v | v ∈ B}) :
    (runCandidateSearches G₀ verts C
      ((undoEdgeCandidateChains G₀ verts C A B P₀.support L₁ N L₂ y s Q_supp R_supp).filterMap
        (walkOfChainOption G₀))).1.isSome = true := by
  have hmem_chain : P_new.support ∈
      undoEdgeCandidateChains G₀ verts C A B P₀.support L₁ N L₂ y s Q_supp R_supp := by
    rw [← hr3_eq, ← hb]
    rcases hL_or with hL | hL <;> rw [hL]
    · exact mem_undoEdgeCandidateChains_r3_left verts C A B P₀.support L₁ N L₂ y s Q_supp R_supp
    · exact mem_undoEdgeCandidateChains_r3_right verts C A B P₀.support L₁ N L₂ y s Q_supp R_supp
  have hhead : P_new.support.head? = some a := by rw [← Walk.cons_tail_support]; rfl
  have hlast : P_new.support.getLast? = some b := by
    rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
  obtain ⟨p, hp, hsupp_p⟩ := walkOfChainOption_eq_some_of_isChain P_new.isChain_adj_support hhead hlast
  have hmem_p : (⟨a, b, p⟩ : Σ u v : V, G₀.Walk u v) ∈
      (undoEdgeCandidateChains G₀ verts C A B P₀.support L₁ N L₂ y s Q_supp R_supp).filterMap
        (walkOfChainOption G₀) :=
    List.mem_filterMap.mpr ⟨P_new.support, hmem_chain, hp⟩
  have hp_tpath : IsTPath G₀ C p := by
    refine ⟨?_, hP_new.2.1, hP_new.2.2.1, ?_⟩
    · rw [Walk.isPath_def, hsupp_p]; exact hP_new.1.support_nodup
    · rw [hsupp_p]; exact hP_new.2.2.2
  have hns_p : ¬ Separates G₀ {v | v ∈ p.support} {v | v ∈ A} {v | v ∈ B} := by
    rw [hsupp_p]; exact hns
  have hsearch := searchCrossWalk_isSome_of_not_separates hverts hCnd hrot hp_tpath hns_p
  exact runCandidateSearches_isSome_of_mem hmem_p hsearch

/-- **Rule 3 search completeness (`y`-side, `undoEdgeCandidateWalks_isSome_of_rule_three_left`):**
When `bridgeOfList N (L₁ ++ L₂) L = some (σ, t :: K, z)` with `z ∈ L₁` (`y ∉ P_new.support`)
and `y` reaches `A` off `P_new.support`, `P_new` fails to separate `A` from `B` in `G₀`, so
`undoEdgeCandidateWalks_isSome_of_rule_three` returns `some` valid crossing. -/
theorem undoEdgeCandidateWalks_isSome_of_rule_three_left [DecidableEq V] [DecidableRel G₀.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {verts C A B L₁ N L₂ : List V} {a b y s σ t z : V} {k : ℕ} {K : List V}
    {P₀ P_new : G₀.Walk a b} (Q_supp R_supp : List V)
    (hverts : ∀ v : V, v ∈ verts) (hCnd : C.Nodup) (hrot : C.rotate k = a :: A ++ b :: B)
    (hP₀ : IsTPath G₀ C P₀) (hsupp : P₀.support = L₁ ++ y :: N ++ s :: L₂)
    (hN : ∀ v ∈ N, ¬ IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ B} v)
    (hyB : IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ B} y)
    (hσ : σ ∈ N) (hcM : (σ :: t :: K ++ [z]).IsChain G₀.Adj)
    (hK : ∀ w ∈ t :: K, w ∉ C ∧ w ∉ P₀.support)
    {L : List V} (hL_or : L = R_supp ∨ L = R_supp.reverse)
    (hb : bridgeOfList N (L₁ ++ L₂) L = some (σ, t :: K, z))
    (hP_new : IsTPath G₀ C P_new)
    (hr3_eq : rule3ChainOfBridge P₀.support L₁ (some (σ, t :: K, z)) = P_new.support)
    (hsub : ∀ w ∈ P_new.support, w ∈ P₀.support ∨ w ∈ t :: K)
    (hyP : y ∉ P_new.support) (hyA : ReachesOff G₀ P_new.support A y) :
    (runCandidateSearches G₀ verts C
      ((undoEdgeCandidateChains G₀ verts C A B P₀.support L₁ N L₂ y s Q_supp R_supp).filterMap
        (walkOfChainOption G₀))).1.isSome = true := by
  refine undoEdgeCandidateWalks_isSome_of_rule_three Q_supp R_supp hverts hCnd hrot hL_or hb
    hP_new hr3_eq fun hsep => ?_
  obtain ⟨a₀, ha₀, p_A, hp_A⟩ := hyA
  obtain ⟨b₀, hb₀, p_B, hp_B, hin_B⟩ := hyB
  have hcK : (σ :: t :: K).IsChain G₀.Adj := hcM.left_of_append
  have hyP₀ : y ∈ P₀.support := by rw [hsupp]; simp
  have hp_B_bridge := notMem_bridge_of_onSide_B hsupp hN hσ hcK hK hyP₀ hb₀ p_B hp_B hin_B
  have hb₀P : b₀ ∉ P₀.support := notMem_support_of_arc hCnd hrot hP₀ (Or.inr hb₀)
  obtain ⟨x, hx, hxP'⟩ := hsep a₀ ha₀ b₀ hb₀ (p_A.reverse.append p_B)
  rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hx
  rcases hx with hx | hx
  · exact hp_A x hx hxP'
  · rcases hsub x hxP' with hxP₀ | hxK
    · by_cases h1 : x = y
      · exact hyP (h1 ▸ hxP')
      · by_cases h2 : x = b₀
        · exact hb₀P (h2 ▸ hxP₀)
        · exact hin_B x hx h1 h2 (Or.inr hxP₀)
    · exact hp_B_bridge x hxK hx

/-- **Rule 3 search completeness (`s`-side, `undoEdgeCandidateWalks_isSome_of_rule_three_right`):**
Symmetrically, when `z ∈ L₂` (`s ∉ P_new.support`) and `s` reaches `A` off `P_new.support`,
`undoEdgeCandidateWalks_isSome_of_rule_three` returns `some` valid crossing. -/
theorem undoEdgeCandidateWalks_isSome_of_rule_three_right [DecidableEq V] [DecidableRel G₀.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {verts C A B L₁ N L₂ : List V} {a b y s σ t z : V} {k : ℕ} {K : List V}
    {P₀ P_new : G₀.Walk a b} (Q_supp R_supp : List V)
    (hverts : ∀ v : V, v ∈ verts) (hCnd : C.Nodup) (hrot : C.rotate k = a :: A ++ b :: B)
    (hP₀ : IsTPath G₀ C P₀) (hsupp : P₀.support = L₁ ++ y :: N ++ s :: L₂)
    (hN : ∀ v ∈ N, ¬ IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ B} v)
    (hsB : IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ B} s)
    (hσ : σ ∈ N) (hcM : (σ :: t :: K ++ [z]).IsChain G₀.Adj)
    (hK : ∀ w ∈ t :: K, w ∉ C ∧ w ∉ P₀.support)
    {L : List V} (hL_or : L = R_supp ∨ L = R_supp.reverse)
    (hb : bridgeOfList N (L₁ ++ L₂) L = some (σ, t :: K, z))
    (hP_new : IsTPath G₀ C P_new)
    (hr3_eq : rule3ChainOfBridge P₀.support L₁ (some (σ, t :: K, z)) = P_new.support)
    (hsub : ∀ w ∈ P_new.support, w ∈ P₀.support ∨ w ∈ t :: K)
    (hsP : s ∉ P_new.support) (hsA : ReachesOff G₀ P_new.support A s) :
    (runCandidateSearches G₀ verts C
      ((undoEdgeCandidateChains G₀ verts C A B P₀.support L₁ N L₂ y s Q_supp R_supp).filterMap
        (walkOfChainOption G₀))).1.isSome = true := by
  refine undoEdgeCandidateWalks_isSome_of_rule_three Q_supp R_supp hverts hCnd hrot hL_or hb
    hP_new hr3_eq fun hsep => ?_
  obtain ⟨a₀, ha₀, p_A, hp_A⟩ := hsA
  obtain ⟨b₀, hb₀, p_B, hp_B, hin_B⟩ := hsB
  have hcK : (σ :: t :: K).IsChain G₀.Adj := hcM.left_of_append
  have hsP₀ : s ∈ P₀.support := by rw [hsupp]; simp
  have hp_B_bridge := notMem_bridge_of_onSide_B hsupp hN hσ hcK hK hsP₀ hb₀ p_B hp_B hin_B
  have hb₀P : b₀ ∉ P₀.support := notMem_support_of_arc hCnd hrot hP₀ (Or.inr hb₀)
  obtain ⟨x, hx, hxP'⟩ := hsep a₀ ha₀ b₀ hb₀ (p_A.reverse.append p_B)
  rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hx
  rcases hx with hx | hx
  · exact hp_A x hx hxP'
  · rcases hsub x hxP' with hxP₀ | hxK
    · by_cases h1 : x = s
      · exact hsP (h1 ▸ hxP')
      · by_cases h2 : x = b₀
        · exact hb₀P (h2 ▸ hxP₀)
        · exact hin_B x hx h1 h2 (Or.inr hxP₀)
    · exact hp_B_bridge x hxK hx

/-! ### Part 6: Rule 4 search completeness (`r4_1`, `r4_2 = rule4ChainsForSigma`) -/

/-- Membership of `rule4ChainsForSigma` in `undoEdgeCandidateChains`. -/
theorem mem_undoEdgeCandidateChains_r4 [DecidableEq V] [DecidableRel G₀.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    (verts C A B P_supp L₁ N L₂ : List V) (y s : V) (Q_supp R_supp : List V)
    {L : List V} (hL_or : L = R_supp ∨ L = R_supp.reverse)
    {σ z : V} {M : List V} (hb : bridgeOfList N (L₁ ++ L₂) L = some (σ, M, z))
    {X : List V}
    (hX : X ∈ rule4ChainsForSigma N R_supp
      (sideWalkSupport G₀ verts C P_supp y B)
      (sideWalkSupport G₀ verts C P_supp s B)
      (sideWalkSupport G₀ verts C P_supp y A)
      (sideWalkSupport G₀ verts C P_supp s A)
      (sideWalkSupport G₀ verts C P_supp σ A)
      (sideWalkSupport G₀ verts C P_supp σ B) σ) :
    X ∈ undoEdgeCandidateChains G₀ verts C A B P_supp L₁ N L₂ y s Q_supp R_supp := by
  unfold undoEdgeCandidateChains
  dsimp only
  rcases hL_or with rfl | rfl
  · rw [hb]
    dsimp only
    exact List.mem_append_left _ (List.mem_append_right _ hX)
  · rw [hb]
    dsimp only
    exact List.mem_append_right _ hX

/-- **Rule 4 search completeness (`undoEdgeCandidateWalks_isSome_of_rule_four`):**
When `bridgeOfList N (L₁ ++ L₂) L = some (σ, M, z)` on `L ∈ {R_supp, R_supp.reverse}`, and a
candidate chain `X ∈ rule4ChainsForSigma ... σ` is a `G₀.Adj`-chain between `c ∈ C` and `d ∈ C`
whose internal vertices avoid `C`, with `Alternate C u v c d` and a walk `W : G₀.Walk u v` avoiding
`X`, running `runCandidateSearches` on `undoEdgeCandidateChains` returns `some` valid crossing. -/
theorem undoEdgeCandidateWalks_isSome_of_rule_four [DecidableEq V] [DecidableRel G₀.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {verts C A B P_supp L₁ N L₂ : List V} {y s σ z u v c d : V} {M X : List V}
    (Q_supp R_supp : List V)
    (hverts : ∀ v : V, v ∈ verts) (hCnd : C.Nodup)
    {L : List V} (hL_or : L = R_supp ∨ L = R_supp.reverse)
    (hb : bridgeOfList N (L₁ ++ L₂) L = some (σ, M, z))
    (hX_mem : X ∈ rule4ChainsForSigma N R_supp
      (sideWalkSupport G₀ verts C P_supp y B)
      (sideWalkSupport G₀ verts C P_supp s B)
      (sideWalkSupport G₀ verts C P_supp y A)
      (sideWalkSupport G₀ verts C P_supp s A)
      (sideWalkSupport G₀ verts C P_supp σ A)
      (sideWalkSupport G₀ verts C P_supp σ B) σ)
    (hX_ch : X.IsChain G₀.Adj) (hh : X.head? = some c) (hl : X.getLast? = some d)
    (hc : c ∈ C) (hd : d ∈ C) (hin : ∀ w ∈ X, w ∈ C → w = c ∨ w = d)
    (halt : Alternate C u v c d) (W : G₀.Walk u v) (hW : ∀ w ∈ W.support, w ∉ X) :
    (runCandidateSearches G₀ verts C
      ((undoEdgeCandidateChains G₀ verts C A B P_supp L₁ N L₂ y s Q_supp R_supp).filterMap
        (walkOfChainOption G₀))).1.isSome = true := by
  have hmem :=
    mem_undoEdgeCandidateChains_r4 verts C A B P_supp L₁ N L₂ y s Q_supp R_supp hL_or hb hX_mem
  exact runCandidateSearches_isSome_of_chain hverts hCnd hmem hX_ch hh hl hc hd hin halt W hW

/-- Splicing a chain `bp` ending at `σ` with a chain `σ :: at_` starting at `σ` gives a chain
`bp ++ at_`. -/
theorem rule4_splice_chain {C bp at_ : List V} {c σ d : V}
    (hbp_ch : bp.IsChain G₀.Adj) (hbp_h : bp.head? = some c) (hbp_l : bp.getLast? = some σ)
    (hbp_C : ∀ w ∈ bp, w ∈ C → w = c)
    (hat_ch : (σ :: at_).IsChain G₀.Adj) (hat_l : (σ :: at_).getLast? = some d)
    (hat_C : ∀ w ∈ σ :: at_, w ∈ C → w = d) :
    (bp ++ at_).IsChain G₀.Adj ∧ (bp ++ at_).head? = some c ∧ (bp ++ at_).getLast? = some d ∧
      (∀ w ∈ bp ++ at_, w ∈ C → w = c ∨ w = d) ∧
      (∀ w ∈ bp ++ at_, w ∈ bp ∨ w ∈ σ :: at_) := by
  have hbp_ne : bp ≠ [] := fun e => by simp [e] at hbp_l
  have hbp_drop : bp.dropLast ++ [σ] = bp := by
    have h1 := List.dropLast_append_getLast hbp_ne
    have h2 : bp.getLast hbp_ne = σ := by
      rw [← Option.some_inj, ← List.getLast?_eq_some_getLast hbp_ne, hbp_l]
    rwa [h2] at h1
  have hch : (bp ++ at_).IsChain G₀.Adj := by
    rw [← hbp_drop] at hbp_ch ⊢
    simpa using hbp_ch.append_overlap (show ([σ] ++ at_).IsChain G₀.Adj from hat_ch) (by simp)
  have hh : (bp ++ at_).head? = some c := by
    cases bp with
    | nil => contradiction
    | cons x tl => simpa using hbp_h
  have hl : (bp ++ at_).getLast? = some d := by
    rw [← hbp_drop, List.append_assoc, List.singleton_append,
      List.getLast?_append_of_ne_nil _ (by simp)]
    exact hat_l
  refine ⟨hch, hh, hl, fun w hw hwC => ?_, fun w hw => ?_⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact Or.inl (hbp_C w hw hwC)
    · exact Or.inr (hat_C w (List.mem_cons_of_mem _ hw) hwC)
  · rcases List.mem_append.mp hw with hw | hw
    · exact Or.inl hw
    · exact Or.inr (List.mem_cons_of_mem _ hw)

/-- When `L₁` is non-empty (`z ∈ L₁`), `y` is an internal vertex of `P₀`, hence `y ∉ C`. -/
theorem not_mem_C_of_mem_L₁ {C L₁ N L₂ : List V} {a b y s z : V} {P₀ : G₀.Walk a b}
    (hP₀ : IsTPath G₀ C P₀) (hsupp : P₀.support = L₁ ++ y :: N ++ s :: L₂) (hz : z ∈ L₁) :
    y ∉ C := by
  have hnd : (L₁ ++ y :: N ++ s :: L₂).Nodup := hsupp ▸ hP₀.1.support_nodup
  have hyP : y ∈ P₀.support := by rw [hsupp]; simp
  have hya : y ≠ a := by
    rintro rfl
    have h0 : P₀.support.head? = some y := by rw [← Walk.cons_tail_support]; rfl
    rw [hsupp] at h0
    rcases L₁ with _ | ⟨x, tl⟩
    · simp at hz
    · simp only [List.cons_append, List.head?_cons, Option.some.injEq] at h0
      subst h0
      simp only [List.cons_append, List.nodup_cons, List.mem_append, List.mem_cons] at hnd
      exact hnd.1 (by simp)
  have hyb : y ≠ b := by
    rintro rfl
    have h0 : P₀.support.getLast? = some y := by
      rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
    have e : L₁ ++ y :: N ++ s :: L₂ = (L₁ ++ y :: N) ++ (s :: L₂) := by simp
    rw [hsupp, e, List.getLast?_append_of_ne_nil _ (by simp)] at h0
    have hy_mem : y ∈ s :: L₂ := List.mem_of_getLast? h0
    rw [e, List.nodup_append] at hnd
    exact hnd.2.2 y (by simp) y hy_mem rfl
  exact (hP₀.2.2.2 y hyP hya hyb).1

/-- When `L₂` is non-empty (`z ∈ L₂`), `s` is an internal vertex of `P₀`, hence `s ∉ C`. -/
theorem not_mem_C_of_mem_L₂ {C L₁ N L₂ : List V} {a b y s z : V} {P₀ : G₀.Walk a b}
    (hP₀ : IsTPath G₀ C P₀) (hsupp : P₀.support = L₁ ++ y :: N ++ s :: L₂) (hz : z ∈ L₂) :
    s ∉ C := by
  have hnd : (L₁ ++ y :: N ++ s :: L₂).Nodup := hsupp ▸ hP₀.1.support_nodup
  have hsP : s ∈ P₀.support := by rw [hsupp]; simp
  have hsa : s ≠ a := by
    rintro rfl
    have h0 : P₀.support.head? = some s := by rw [← Walk.cons_tail_support]; rfl
    have e : L₁ ++ y :: N ++ s :: L₂ = (L₁ ++ y :: N) ++ (s :: L₂) := by simp
    rw [hsupp, e, List.head?_append_of_ne_nil _ (by simp)] at h0
    have hs_mem : s ∈ L₁ ++ y :: N := List.mem_of_head? h0
    rw [e, List.nodup_append] at hnd
    exact hnd.2.2 s hs_mem s (by simp) rfl
  have hsb : s ≠ b := by
    rintro rfl
    have h0 : P₀.support.getLast? = some s := by
      rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
    rcases L₂ with _ | ⟨x, tl⟩
    · simp at hz
    · have e : L₁ ++ y :: N ++ s :: x :: tl = (L₁ ++ y :: N ++ [s]) ++ (x :: tl) := by simp
      rw [hsupp, e, List.getLast?_append_of_ne_nil _ (by simp)] at h0
      have hs_mem : s ∈ x :: tl := List.mem_of_getLast? h0
      rw [e, List.nodup_append] at hnd
      exact hnd.2.2 s (by simp) s hs_mem rfl
  exact (hP₀.2.2.2 s hsP hsa hsb).1

/-- Characterization of `bp = (sideWalkSupport G₀ verts C P₀.support y S).reverse ++ N.take (N.idxOf σ + 1)`. -/
theorem rule4_bp_y_spec [DecidableEq V] [DecidableRel G₀.Adj] [WalkSearch V] [LawfulWalkSearch V]
    {verts C L₁ N L₂ S : List V} {a b y s σ : V} {P₀ : G₀.Walk a b}
    (hverts : ∀ v : V, v ∈ verts)
    (hP₀ : IsTPath G₀ C P₀) (hsupp : P₀.support = L₁ ++ y :: N ++ s :: L₂)
    (hyC : y ∉ C) (hσ : σ ∈ N)
    (hyS : IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ S} y) :
    ∃ b₀ ∈ S, ∃ p : G₀.Walk y b₀, p.IsPath ∧
      (∀ x ∈ p.support, x ≠ y → x ≠ b₀ → x ∉ C ∧ x ∉ P₀.support) ∧
      let bp := (sideWalkSupport G₀ verts C P₀.support y S).reverse ++ N.take (N.idxOf σ + 1)
      bp.IsChain G₀.Adj ∧ bp.head? = some b₀ ∧ bp.getLast? = some σ ∧
        (∀ w ∈ bp, w ∈ C → w = b₀) ∧
        (∀ w ∈ bp, w ∈ p.support ∨ w ∈ y :: N.take (N.idxOf σ + 1)) := by
  obtain ⟨b₀, hb₀, p, hp, hpin, hp_eq⟩ := sideWalkSupport_of_isOnSide G₀ hverts hyS
  refine ⟨b₀, hb₀, p, hp, hpin, ?_⟩
  dsimp only
  rw [hp_eq]
  have hndP : (L₁ ++ y :: N ++ s :: L₂).Nodup := hsupp ▸ hP₀.1.support_nodup
  have hndN : N.Nodup := by
    have h := hndP
    rw [List.nodup_append, List.nodup_cons, List.nodup_append] at h
    exact (List.nodup_cons.mp h.1.2.1).2
  obtain ⟨N₀, N₁, hN_eq⟩ := List.append_of_mem hσ
  have htakeN : N.take (N.idxOf σ + 1) = N₀ ++ [σ] := by
    rw [hN_eq]; exact take_idxOf_succ_of_nodup (hN_eq ▸ hndN)
  rw [htakeN]
  have hp_rev_ch : p.support.reverse.IsChain G₀.Adj :=
    List.isChain_reverse.mpr (p.isChain_adj_support.imp fun _ _ h => h.symm)
  have hp_rev_last : p.support.reverse.getLast? = some y := by
    rw [List.getLast?_reverse, ← Walk.cons_tail_support]; rfl
  have hp_rev_head : p.support.reverse.head? = some b₀ := by
    rw [List.head?_reverse, List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
  have hp_drop : p.support.reverse.dropLast ++ [y] = p.support.reverse := by
    have hne : p.support.reverse ≠ [] := by simp
    have h1 := List.dropLast_append_getLast hne
    have h2 : p.support.reverse.getLast hne = y := by
      rw [← Option.some_inj, ← List.getLast?_eq_some_getLast hne, hp_rev_last]
    rwa [h2] at h1
  have hch_N₀ : (y :: N₀ ++ [σ]).IsChain G₀.Adj := by
    have hch := P₀.isChain_adj_support
    rw [hsupp, hN_eq] at hch
    exact hch.infix ⟨L₁, N₁ ++ s :: L₂, by simp⟩
  have hbp_ch : (p.support.reverse ++ (N₀ ++ [σ])).IsChain G₀.Adj := by
    rw [← hp_drop] at hp_rev_ch ⊢
    simpa using hp_rev_ch.append_overlap
      (show ([y] ++ (N₀ ++ [σ])).IsChain G₀.Adj by simpa using hch_N₀) (by simp)
  have hbp_h : (p.support.reverse ++ (N₀ ++ [σ])).head? = some b₀ := by
    rw [List.head?_append_of_ne_nil _ (by simp)]
    exact hp_rev_head
  have hbp_l : (p.support.reverse ++ (N₀ ++ [σ])).getLast? = some σ := by
    rw [List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_concat]
  refine ⟨hbp_ch, hbp_h, hbp_l, fun w hw hwC => ?_, fun w hw => ?_⟩
  · rcases List.mem_append.mp hw with hw | hw
    · have hwp : w ∈ p.support := List.mem_reverse.mp hw
      by_contra hwb
      by_cases hwy : w = y
      · exact hyC (hwy ▸ hwC)
      · exact (hpin w hwp hwy hwb).1 hwC
    · have hwN : w ∈ N := by rw [hN_eq]; simp only [List.mem_append, List.mem_cons] at hw ⊢; tauto
      exact absurd hwC (not_mem_C_of_mem_window hP₀ hsupp hwN)
  · rcases List.mem_append.mp hw with hw | hw
    · exact Or.inl (List.mem_reverse.mp hw)
    · exact Or.inr (List.mem_cons_of_mem _ hw)

/-- Characterization of `bp = (sideWalkSupport G₀ verts C P₀.support s S).reverse ++ (N.drop (N.idxOf σ)).reverse`. -/
theorem rule4_bp_s_spec [DecidableEq V] [DecidableRel G₀.Adj] [WalkSearch V] [LawfulWalkSearch V]
    {verts C L₁ N L₂ S : List V} {a b y s σ : V} {P₀ : G₀.Walk a b}
    (hverts : ∀ v : V, v ∈ verts)
    (hP₀ : IsTPath G₀ C P₀) (hsupp : P₀.support = L₁ ++ y :: N ++ s :: L₂)
    (hsC : s ∉ C) (hσ : σ ∈ N)
    (hsS : IsOnSide G₀ {x | x ∈ C ∨ x ∈ P₀.support} {x | x ∈ S} s) :
    ∃ b₀ ∈ S, ∃ p : G₀.Walk s b₀, p.IsPath ∧
      (∀ x ∈ p.support, x ≠ s → x ≠ b₀ → x ∉ C ∧ x ∉ P₀.support) ∧
      let bp := (sideWalkSupport G₀ verts C P₀.support s S).reverse ++ (N.drop (N.idxOf σ)).reverse
      bp.IsChain G₀.Adj ∧ bp.head? = some b₀ ∧ bp.getLast? = some σ ∧
        (∀ w ∈ bp, w ∈ C → w = b₀) ∧
        (∀ w ∈ bp, w ∈ p.support ∨ w ∈ s :: (N.drop (N.idxOf σ)).reverse) := by
  obtain ⟨b₀, hb₀, p, hp, hpin, hp_eq⟩ := sideWalkSupport_of_isOnSide G₀ hverts hsS
  refine ⟨b₀, hb₀, p, hp, hpin, ?_⟩
  dsimp only
  rw [hp_eq]
  have hndP : (L₁ ++ y :: N ++ s :: L₂).Nodup := hsupp ▸ hP₀.1.support_nodup
  have hndN : N.Nodup := by
    have h := hndP
    rw [List.nodup_append, List.nodup_cons, List.nodup_append] at h
    exact (List.nodup_cons.mp h.1.2.1).2
  obtain ⟨N₀, N₁, hN_eq⟩ := List.append_of_mem hσ
  have hdropN : (N.drop (N.idxOf σ)).reverse = N₁.reverse ++ [σ] := by
    rw [hN_eq, drop_idxOf_of_nodup (hN_eq ▸ hndN)]; simp
  rw [hdropN]
  have hp_rev_ch : p.support.reverse.IsChain G₀.Adj :=
    List.isChain_reverse.mpr (p.isChain_adj_support.imp fun _ _ h => h.symm)
  have hp_rev_last : p.support.reverse.getLast? = some s := by
    rw [List.getLast?_reverse, ← Walk.cons_tail_support]; rfl
  have hp_rev_head : p.support.reverse.head? = some b₀ := by
    rw [List.head?_reverse, List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
  have hp_drop : p.support.reverse.dropLast ++ [s] = p.support.reverse := by
    have hne : p.support.reverse ≠ [] := by simp
    have h1 := List.dropLast_append_getLast hne
    have h2 : p.support.reverse.getLast hne = s := by
      rw [← Option.some_inj, ← List.getLast?_eq_some_getLast hne, hp_rev_last]
    rwa [h2] at h1
  have hch_N₁ : (s :: N₁.reverse ++ [σ]).IsChain G₀.Adj := by
    have hch := P₀.isChain_adj_support
    rw [hsupp, hN_eq] at hch
    have hinf : (σ :: N₁ ++ [s]).IsChain G₀.Adj := hch.infix ⟨L₁ ++ y :: N₀, L₂, by simp⟩
    have hrev : (σ :: N₁ ++ [s]).reverse = s :: N₁.reverse ++ [σ] := by simp
    rw [← hrev, List.isChain_reverse]
    exact hinf.imp fun _ _ h => h.symm
  have hbp_ch : (p.support.reverse ++ (N₁.reverse ++ [σ])).IsChain G₀.Adj := by
    rw [← hp_drop] at hp_rev_ch ⊢
    simpa using hp_rev_ch.append_overlap
      (show ([s] ++ (N₁.reverse ++ [σ])).IsChain G₀.Adj by simpa using hch_N₁) (by simp)
  have hbp_h : (p.support.reverse ++ (N₁.reverse ++ [σ])).head? = some b₀ := by
    rw [List.head?_append_of_ne_nil _ (by simp)]
    exact hp_rev_head
  have hbp_l : (p.support.reverse ++ (N₁.reverse ++ [σ])).getLast? = some σ := by
    rw [List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_concat]
  refine ⟨hbp_ch, hbp_h, hbp_l, fun w hw hwC => ?_, fun w hw => ?_⟩
  · rcases List.mem_append.mp hw with hw | hw
    · have hwp : w ∈ p.support := List.mem_reverse.mp hw
      by_contra hwb
      by_cases hws : w = s
      · exact hsC (hws ▸ hwC)
      · exact (hpin w hwp hws hwb).1 hwC
    · have hwN : w ∈ N := by
        rw [hN_eq]
        simp only [List.mem_append, List.mem_reverse, List.mem_cons] at hw ⊢
        tauto
      exact absurd hwC (not_mem_C_of_mem_window hP₀ hsupp hwN)
  · rcases List.mem_append.mp hw with hw | hw
    · exact Or.inl (List.mem_reverse.mp hw)
    · exact Or.inr (List.mem_cons_of_mem _ hw)

/-- Characterization of `at_ = (R₀.support.take (R₀.support.idxOf σ)).reverse` when `σ ∈ R₀.support`. -/
theorem rule4_at_take_spec [DecidableEq V]
    {C : List V} {u₂ v₂ σ : V} {R₀ : G₀.Walk u₂ v₂}
    (hR₀ : IsTPath G₀ C R₀) (hσR : σ ∈ R₀.support) (hσC : σ ∉ C) :
    let at_ := (R₀.support.take (R₀.support.idxOf σ)).reverse
    (σ :: at_).IsChain G₀.Adj ∧ (σ :: at_).getLast? = some u₂ ∧
      (∀ w ∈ σ :: at_, w ∈ C → w = u₂) ∧
      (∀ w ∈ σ :: at_, w ∈ R₀.support.take (R₀.support.idxOf σ + 1)) := by
  have hndR := hR₀.1.support_nodup
  obtain ⟨R₁, R₂, hR_eq⟩ := List.append_of_mem hσR
  have htake : R₀.support.take (R₀.support.idxOf σ) = R₁ := by
    rw [hR_eq]; exact take_idxOf_of_nodup (hR_eq ▸ hndR)
  have htake_succ : R₀.support.take (R₀.support.idxOf σ + 1) = R₁ ++ [σ] := by
    rw [hR_eq]; exact take_idxOf_succ_of_nodup (hR_eq ▸ hndR)
  dsimp only
  rw [htake, htake_succ]
  have hR₁_ne : R₁ ≠ [] := by
    rintro rfl
    have h0 : R₀.support.head? = some u₂ := by rw [← Walk.cons_tail_support]; rfl
    rw [hR_eq] at h0
    simp only [List.nil_append, List.head?_cons, Option.some.injEq] at h0
    subst h0
    exact hσC hR₀.2.1
  have hch_pre : (R₁ ++ [σ]).IsChain G₀.Adj := by
    have hch := R₀.isChain_adj_support
    rw [hR_eq] at hch
    exact hch.infix ⟨[], R₂, by simp⟩
  have hch_rev : (σ :: R₁.reverse).IsChain G₀.Adj := by
    have hrev : (R₁ ++ [σ]).reverse = σ :: R₁.reverse := by simp
    rw [← hrev, List.isChain_reverse]
    exact hch_pre.imp fun _ _ h => h.symm
  have hlast_rev : (σ :: R₁.reverse).getLast? = some u₂ := by
    have hrev : (R₁ ++ [σ]).reverse = σ :: R₁.reverse := by simp
    rw [← hrev, List.getLast?_reverse]
    have h0 : R₀.support.head? = some u₂ := by rw [← Walk.cons_tail_support]; rfl
    rw [hR_eq] at h0
    cases R₁ with
    | nil => contradiction
    | cons x tl => simpa using h0
  refine ⟨hch_rev, hlast_rev, fun w hw hwC => ?_, fun w hw => ?_⟩
  · rcases List.mem_cons.mp hw with rfl | hw
    · exact absurd hwC hσC
    · have hwR₁ : w ∈ R₁ := List.mem_reverse.mp hw
      have hwR : w ∈ R₀.support := by rw [hR_eq]; simp [hwR₁]
      have hwv₂ : w ≠ v₂ := by
        rintro rfl
        have h0 : R₀.support.getLast? = some w := by
          rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
        rw [hR_eq, List.getLast?_append_of_ne_nil _ (by simp)] at h0
        have hw_mem : w ∈ σ :: R₂ := List.mem_of_getLast? h0
        have hnd' := hR_eq ▸ hndR
        rw [List.nodup_append] at hnd'
        exact hnd'.2.2 w hwR₁ w hw_mem rfl
      by_contra hwu₂
      exact (hR₀.2.2.2 w hwR hwu₂ hwv₂).1 hwC
  · simp only [List.mem_cons, List.mem_reverse, List.mem_append] at hw ⊢
    tauto

/-- Characterization of `at_ = R₀.support.drop (R₀.support.idxOf σ + 1)` when `σ ∈ R₀.support`. -/
theorem rule4_at_drop_spec [DecidableEq V]
    {C : List V} {u₂ v₂ σ : V} {R₀ : G₀.Walk u₂ v₂}
    (hR₀ : IsTPath G₀ C R₀) (hσR : σ ∈ R₀.support) (hσC : σ ∉ C) :
    let at_ := R₀.support.drop (R₀.support.idxOf σ + 1)
    (σ :: at_).IsChain G₀.Adj ∧ (σ :: at_).getLast? = some v₂ ∧
      (∀ w ∈ σ :: at_, w ∈ C → w = v₂) ∧
      (∀ w ∈ σ :: at_, w ∈ R₀.support.drop (R₀.support.idxOf σ)) := by
  have hndR := hR₀.1.support_nodup
  obtain ⟨R₁, R₂, hR_eq⟩ := List.append_of_mem hσR
  have hdrop_succ : R₀.support.drop (R₀.support.idxOf σ + 1) = R₂ := by
    rw [hR_eq]; exact drop_idxOf_succ_of_nodup (hR_eq ▸ hndR)
  have hdrop : R₀.support.drop (R₀.support.idxOf σ) = σ :: R₂ := by
    rw [hR_eq]; exact drop_idxOf_of_nodup (hR_eq ▸ hndR)
  dsimp only
  rw [hdrop_succ, hdrop]
  have hch_suf : (σ :: R₂).IsChain G₀.Adj := by
    have hch := R₀.isChain_adj_support
    rw [hR_eq] at hch
    exact hch.infix ⟨R₁, [], by simp⟩
  have hlast_suf : (σ :: R₂).getLast? = some v₂ := by
    have h0 : R₀.support.getLast? = some v₂ := by
      rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
    rw [hR_eq, List.getLast?_append_of_ne_nil _ (by simp)] at h0
    exact h0
  refine ⟨hch_suf, hlast_suf, fun w hw hwC => ?_, fun _ hw => hw⟩
  rcases List.mem_cons.mp hw with rfl | hwR₂
  · exact absurd hwC hσC
  · have hwR : w ∈ R₀.support := by rw [hR_eq]; simp [hwR₂]
    have hwu₂ : w ≠ u₂ := by
      rintro rfl
      have h0 : R₀.support.head? = some w := by rw [← Walk.cons_tail_support]; rfl
      rw [hR_eq] at h0
      have hnd' := hR_eq ▸ hndR
      rcases R₁ with _ | ⟨x, tl⟩
      · simp only [List.nil_append, List.head?_cons, Option.some.injEq] at h0
        subst h0
        exact hσC hwC
      · simp only [List.cons_append, List.head?_cons, Option.some.injEq] at h0
        subst h0
        rw [List.nodup_append] at hnd'
        exact hnd'.2.2 x (by simp) x (List.mem_cons_of_mem _ hwR₂) rfl
    by_contra hwv₂
    exact (hR₀.2.2.2 w hwR hwu₂ hwv₂).1 hwC

/-- Characterization of `at_ = (sideWalkSupport G₀ verts C P₀.support σ S).tail` when `σ` is on side `S`. -/
theorem rule4_at_side_spec [DecidableEq V] [DecidableRel G₀.Adj] [WalkSearch V] [LawfulWalkSearch V]
    {verts C P_supp S : List V} {σ : V}
    (hverts : ∀ v : V, v ∈ verts) (hσC : σ ∉ C)
    (hσS : IsOnSide G₀ {x | x ∈ C ∨ x ∈ P_supp} {x | x ∈ S} σ) :
    ∃ a₀ ∈ S, ∃ p : G₀.Walk σ a₀, p.IsPath ∧
      (∀ x ∈ p.support, x ≠ σ → x ≠ a₀ → x ∉ C ∧ x ∉ P_supp) ∧
      let at_ := (sideWalkSupport G₀ verts C P_supp σ S).tail
      (σ :: at_).IsChain G₀.Adj ∧ (σ :: at_).getLast? = some a₀ ∧
        (∀ w ∈ σ :: at_, w ∈ C → w = a₀) ∧
        (∀ w ∈ σ :: at_, w ∈ p.support) := by
  obtain ⟨a₀, ha₀, p, hp, hpin, hp_eq⟩ := sideWalkSupport_of_isOnSide G₀ hverts hσS
  refine ⟨a₀, ha₀, p, hp, hpin, ?_⟩
  dsimp only
  have hcons : σ :: (sideWalkSupport G₀ verts C P_supp σ S).tail = p.support := by
    rw [hp_eq, Walk.cons_tail_support]
  rw [hcons]
  have hlast : p.support.getLast? = some a₀ := by
    rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
  refine ⟨p.isChain_adj_support, hlast, fun w hw hwC => ?_, fun _ hw => hw⟩
  by_contra hwa
  by_cases hwσ : w = σ
  · exact hσC (hwσ ▸ hwC)
  · exact (hpin w hw hwσ hwa).1 hwC

end GraphMinor.HP25
