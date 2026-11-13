module

public import GraphMinor.GM21.Section12Three

/-!
# Graph Minors XXI, (12.3): the number of vertices of degree `3`

The step of the proof of (12.3) after claim (2): "Since $T$ has maximum degree $\le 3$, it follows
from (2) that $|N(T)| \le 2^n$." We prove this bound (`ncard_branchSet_le`).

Root `T` at a vertex `r` of degree `≤ 1`. It is not in `N(T)`, so the vertices of `N(T)` lie in
the one branch of `T` at `r`. In a branch at `u` through the neighbour `v`, let `y` be the vertex
of `N(T)` closest to `u`. Every other vertex of `N(T)` in the branch lies beyond `y`, since the vertices between `u`
and `y` have degree `≤ 2` (`onTreePath_first`). So these vertices lie in the two branches at `y`
away from `u`, and paths from `y` into them have one vertex of `N(T)` fewer. By induction a branch
holds at most `2 ^ j - 1` vertices of `N(T)` if every path from `u` into it has at most `j` of them
(`ncard_branch_le`).

For (12.4), `ncard_le_of_paths` bounds by `3 · 2 ^ n` any set `N` that contains the vertices of
degree `3`, rooting `T` at a vertex of `N`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set SimpleGraph

variable {ι : Type*} [Fintype ι] {T : SimpleGraph ι}

/-- The path between two adjacent vertices has no other vertex. -/
theorem onTreePath_adj_iff (hT : T.IsTree) {a b x : ι} (hab : T.Adj a b) :
    Thomas.OnTreePath T a b x ↔ x = a ∨ x = b := by
  rw [Thomas.onTreePath_iff_mem_treePath hT, ← Thomas.eq_treePath hT hab.toWalk hab.isPath_toWalk]
  simp

/-- The path from `u` to `y` has only one vertex adjacent to `u`. -/
theorem eq_of_adj_of_onTreePath (hT : T.IsTree) {u a b y : ι} (ha : T.Adj u a) (hb : T.Adj u b)
    (hya : Thomas.OnTreePath T u y a) (hyb : Thomas.OnTreePath T u y b) : a = b := by
  rcases (Thomas.onTreePath_split_iff hT hya).1 hyb with h | h
  · rcases (onTreePath_adj_iff hT ha).1 h with h | h
    · exact absurd h hb.ne'
    · exact h.symm
  · rcases (Thomas.onTreePath_split_iff hT hyb).1 hya with h' | h'
    · rcases (onTreePath_adj_iff hT hb).1 h' with h' | h'
      · exact absurd h' ha.ne'
      · exact h'
    · exact Thomas.onTreePath_antisymm hT (Thomas.onTreePath_symm h') (Thomas.onTreePath_symm h)

/-- If `x ≠ t`, the path from `x` to `t` has a vertex adjacent to `x`. -/
theorem exists_adj_onTreePath (hT : T.IsTree) {x t : ι} (hxt : x ≠ t) :
    ∃ z, T.Adj x z ∧ Thomas.OnTreePath T x t z := by
  set q := Thomas.treePath hT x t
  have hlen : 0 < q.length := by
    rcases Nat.eq_zero_or_pos q.length with h | h
    · exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero h) hxt
    · exact h
  refine ⟨q.getVert 1, ?_, ?_⟩
  · simpa using q.adj_getVert_succ hlen
  · rw [Thomas.onTreePath_iff_mem_treePath hT]
    exact q.getVert_mem_support 1

/-- A vertex on the path from `u` to `y`, other than `u`, sees the neighbour `v` of `u` on this
path between `u` and itself. -/
theorem onTreePath_adj_of_between (hT : T.IsTree) {u v y x : ι} (huv : T.Adj u v)
    (hyv : Thomas.OnTreePath T u y v) (hyx : Thomas.OnTreePath T u y x) (hxu : x ≠ u) :
    Thomas.OnTreePath T u x v := by
  rcases (Thomas.onTreePath_split_iff hT hyx).1 hyv with h | h
  · exact h
  rcases (Thomas.onTreePath_split_iff hT hyv).1 hyx with h' | h'
  · rcases (onTreePath_adj_iff hT huv).1 h' with h' | rfl
    · exact absurd h' hxu
    · exact Thomas.onTreePath_right T _ _
  · obtain rfl : v = x :=
      Thomas.onTreePath_antisymm hT (Thomas.onTreePath_symm h) (Thomas.onTreePath_symm h')
    exact Thomas.onTreePath_right T _ _

/-- Walking along a path `q` from `a` to `y` through vertices of degree `≤ 2` (except perhaps `y`),
coming from `w`: if `a` is on the path from `w` to a vertex `t` of degree `3`, then so is `y`. -/
theorem onTreePath_of_walk (hT : T.IsTree) {N : Set ι}
    (hN2 : ∀ s ∉ N, (T.neighborSet s).ncard ≤ 2) {t y : ι}
    (htN : t ∈ N) {a : ι} (q : T.Walk a y) : q.IsPath → ∀ w, T.Adj w a →
      w ∉ q.support → Thomas.OnTreePath T w t a →
      (∀ x ∈ q.support, x ≠ y → x ∉ N) → Thomas.OnTreePath T a t y := by
  induction q with
  | nil => intros; exact Thomas.onTreePath_left T _ _
  | @cons a b y hab q' ih =>
    intro hq w hwa hw hwt hN
    rw [Walk.cons_isPath_iff] at hq
    have hay : a ≠ y := fun h ↦ hq.2 (h ▸ q'.end_mem_support)
    have haN : a ∉ N := hN a (Walk.start_mem_support _) hay
    have hat : a ≠ t := fun h ↦ haN (h ▸ htN)
    have hdeg2 : (T.neighborSet a).ncard ≤ 2 := hN2 a haN
    obtain ⟨z, haz, hz⟩ := exists_adj_onTreePath hT hat
    have hzw : z ≠ w := by
      rintro rfl
      exact hwa.ne (Thomas.onTreePath_antisymm hT (Thomas.onTreePath_symm hwt)
        (Thomas.onTreePath_symm hz)).symm
    have hbw : b ≠ w := fun h ↦ hw (h ▸ List.mem_cons_of_mem _ q'.start_mem_support)
    have hzb : z = b := by
      by_contra hzb
      have hsub : ({w, b, z} : Set ι) ⊆ T.neighborSet a := by
        intro x hx
        rcases hx with rfl | rfl | rfl
        exacts [hwa.symm, hab, haz]
      have h3 : ({w, b, z} : Set ι).ncard = 3 :=
        ncard_eq_three.2 ⟨w, b, z, hbw.symm, hzw.symm, Ne.symm hzb, rfl⟩
      have := ncard_le_ncard hsub (toFinite _)
      omega
    subst hzb
    have := ih hq.1 a hab hq.2 hz fun x hx hxy ↦ hN x (List.mem_cons_of_mem _ hx) hxy
    exact Thomas.onTreePath_trans_right hT hz this

/-- **The first vertex of `N(T)` in a branch.** Let `v` be a neighbour of `u`, and let `y` be a
vertex beyond `v` such that no vertex strictly between `u` and `y` is in `N(T)`. Then every vertex
`t` of `N(T)` beyond `v` is beyond `y`. -/
theorem onTreePath_first (hT : T.IsTree) {N : Set ι}
    (hN2 : ∀ s ∉ N, (T.neighborSet s).ncard ≤ 2) {u v y t : ι}
    (huv : T.Adj u v) (hyv : Thomas.OnTreePath T u y v)
    (hmid : ∀ x, Thomas.OnTreePath T u y x → x ≠ u → x ≠ y → x ∉ N)
    (htv : Thomas.OnTreePath T u t v) (htN : t ∈ N) : Thomas.OnTreePath T u t y := by
  have hsupp : ∀ (q : T.Walk u y), q.IsPath → ∀ x ∈ q.support, Thomas.OnTreePath T u y x :=
    fun q hq x hx ↦ by
      rw [Thomas.onTreePath_iff_mem_treePath hT, ← Thomas.eq_treePath hT q hq]
      exact hx
  have key : ∀ (q : T.Walk u y), q.IsPath → Thomas.OnTreePath T u t y := by
    intro q hq
    cases q with
    | nil =>
      rw [Thomas.onTreePath_self] at hyv
      exact absurd hyv huv.ne'
    | @cons _ b _ hab q' =>
      have hb := hsupp _ hq b (List.mem_cons_of_mem _ q'.start_mem_support)
      obtain rfl := eq_of_adj_of_onTreePath hT hab huv hb hyv
      rw [Walk.cons_isPath_iff] at hq
      have := onTreePath_of_walk hT hN2 htN q' hq.1 u hab hq.2 htv fun x hx hxy ↦
        hmid x (hsupp (Walk.cons hab q') ((Walk.cons_isPath_iff hab q').2 hq) x
          (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hx))
          (fun h ↦ hq.2 (h ▸ hx)) hxy
      exact Thomas.onTreePath_trans_right hT htv this
  exact key _ (Thomas.treePath_isPath hT u y)

/-- A set with at most two elements lies in a pair. -/
theorem exists_subset_pair {s : Set ι} (hs : s.ncard ≤ 2) (d : ι) : ∃ a b, s ⊆ {a, b} := by
  interval_cases h : s.ncard
  · rw [ncard_eq_zero (toFinite s)] at h
    exact ⟨d, d, h ▸ empty_subset _⟩
  · obtain ⟨a, rfl⟩ := ncard_eq_one.1 h
    exact ⟨a, a, by simp⟩
  · obtain ⟨a, b, -, rfl⟩ := ncard_eq_two.1 h
    exact ⟨a, b, subset_rfl⟩

/-- A set with at most three elements lies in a triple. -/
theorem exists_subset_triple {s : Set ι} (hs : s.ncard ≤ 3) (d : ι) :
    ∃ a b c, s ⊆ {a, b, c} := by
  interval_cases h : s.ncard
  · rw [ncard_eq_zero (toFinite s)] at h
    exact ⟨d, d, d, h ▸ empty_subset _⟩
  · obtain ⟨a, rfl⟩ := ncard_eq_one.1 h
    exact ⟨a, a, a, by simp⟩
  · obtain ⟨a, b, -, rfl⟩ := ncard_eq_two.1 h
    exact ⟨a, a, b, by simp⟩
  · obtain ⟨a, b, c, -, -, -, rfl⟩ := ncard_eq_three.1 h
    exact ⟨a, b, c, subset_rfl⟩

/-- **A branch holds at most `2 ^ j - 1` vertices of `N`** if every path from `u` into the branch
through `v` has at most `j` vertices of `N` other than `u`. Here `N` contains every vertex of
degree `3`. -/
theorem ncard_branch_le (hT : T.IsTree) (hdeg : ∀ s, (T.neighborSet s).ncard ≤ 3) {N : Set ι}
    (hN2 : ∀ s ∉ N, (T.neighborSet s).ncard ≤ 2) :
    ∀ (j : ℕ) {u v : ι}, T.Adj u v →
      (∀ t, Thomas.OnTreePath T u t v →
        (N ∩ {x | Thomas.OnTreePath T u t x ∧ x ≠ u}).ncard ≤ j) →
      (N ∩ {t | Thomas.OnTreePath T u t v}).ncard ≤ 2 ^ j - 1 := by
  classical
  intro j
  induction j with
  | zero =>
    intro u v huv hH
    suffices hE : N ∩ {t | Thomas.OnTreePath T u t v} = ∅ by
      rw [hE, ncard_empty]; exact Nat.zero_le _
    refine eq_empty_of_forall_notMem fun y hy ↦ ?_
    obtain ⟨hyN, hyv⟩ := hy
    have hyu : y ≠ u := by
      rintro rfl
      exact huv.ne' ((Thomas.onTreePath_self T _ _).1 hyv)
    have := hH y hyv
    rw [Nat.le_zero, ncard_eq_zero (toFinite _)] at this
    exact (eq_empty_iff_forall_notMem.1 this) y ⟨hyN, Thomas.onTreePath_right T _ _, hyu⟩
  | succ j ih =>
    intro u v huv hH
    set S := N ∩ {t | Thomas.OnTreePath T u t v}
    rcases S.eq_empty_or_nonempty with hS | hS
    · rw [hS, ncard_empty]; exact Nat.zero_le _
    -- The vertex `y` of `S` closest to `u`.
    obtain ⟨y, hyS, hymin⟩ := (toFinite S).toFinset.exists_min_image
      (fun y ↦ {x | Thomas.OnTreePath T u y x}.ncard) ((toFinite S).toFinset_nonempty.2 hS)
    rw [Finite.mem_toFinset] at hyS
    obtain ⟨hyN, hyv⟩ := hyS
    have hyu : y ≠ u := by
      rintro rfl
      exact huv.ne' ((Thomas.onTreePath_self T _ _).1 hyv)
    have hmid : ∀ x, Thomas.OnTreePath T u y x → x ≠ u → x ≠ y → x ∉ N := by
      intro x hx hxu hxy hxN
      have hxv := onTreePath_adj_of_between hT huv hyv hx hxu
      have := hymin x ((toFinite S).mem_toFinset.2 ⟨hxN, hxv⟩)
      refine absurd this (not_le.2 (ncard_lt_ncard ⟨fun z hz ↦ Thomas.onTreePath_trans_left hT hx hz,
        fun hsub ↦ hxy ?_⟩ (toFinite _)))
      exact Thomas.onTreePath_antisymm hT hx (hsub (Thomas.onTreePath_right T u y))
    have hfirst : ∀ t ∈ S, Thomas.OnTreePath T u t y := fun t ⟨htN, htv⟩ ↦
      onTreePath_first hT hN2 huv hyv hmid htv htN
    -- The neighbour `p` of `y` towards `u`, and the two other neighbours.
    obtain ⟨p, hyp, hp⟩ := exists_adj_onTreePath hT hyu
    have h2 : (T.neighborSet y \ {p}).ncard ≤ 2 := by
      have hp' : p ∈ T.neighborSet y := hyp
      rw [ncard_sdiff_singleton_of_mem hp']
      have := hdeg y
      omega
    obtain ⟨z₁, z₂, hz⟩ := exists_subset_pair h2 y
    -- A neighbour `z ≠ p` of `y`: its branch satisfies the hypothesis with `j`.
    have hbranch : ∀ z, T.Adj y z → z ≠ p →
        (N ∩ {t | Thomas.OnTreePath T y t z}).ncard ≤ 2 ^ j - 1 := by
      intro z hyz hzp
      refine ih hyz fun t' ht' ↦ ?_
      have hs₁ : Thomas.OnTreePath T u z y := by
        rcases Thomas.onTreePath_adj_dichotomy hT hyz u with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact h1
        · exact absurd (eq_of_adj_of_onTreePath hT hyz hyp (Thomas.onTreePath_symm h1) hp) hzp
      have hyt' : Thomas.OnTreePath T u t' y :=
        (Thomas.onTreePath_of_sides hT hyz hs₁ (Thomas.onTreePath_symm ht')).1
      have hvt' : Thomas.OnTreePath T u t' v := Thomas.onTreePath_trans_left hT hyt' hyv
      have := hH t' hvt'
      have hsub : insert y (N ∩ {x | Thomas.OnTreePath T y t' x ∧ x ≠ y}) ⊆
          N ∩ {x | Thomas.OnTreePath T u t' x ∧ x ≠ u} := by
        rintro x (rfl | ⟨hxN, hx, hxy⟩)
        · exact ⟨hyN, hyt', hyu⟩
        · refine ⟨hxN, Thomas.onTreePath_trans_right hT hyt' hx, ?_⟩
          rintro rfl
          exact hyu (Thomas.onTreePath_antisymm hT (Thomas.onTreePath_symm hyt')
            (Thomas.onTreePath_symm hx))
      have h' := ncard_le_ncard hsub (toFinite _)
      rw [ncard_insert_of_notMem (fun h ↦ h.2.2 rfl) (toFinite _)] at h'
      omega
    -- Every vertex of `S` other than `y` lies in a branch at `y` other than that of `p`.
    let F : ι → Set ι := fun z ↦
      if T.Adj y z ∧ z ≠ p then N ∩ {t | Thomas.OnTreePath T y t z} else ∅
    have hF : ∀ z, (F z).ncard ≤ 2 ^ j - 1 := fun z ↦ by
      by_cases hc : T.Adj y z ∧ z ≠ p
      · rw [show F z = _ from if_pos hc]
        exact hbranch z hc.1 hc.2
      · rw [show F z = ∅ from if_neg hc, ncard_empty]
        exact Nat.zero_le _
    have hcover : S ⊆ insert y (F z₁ ∪ F z₂) := by
      intro t htS
      by_cases hty : t = y
      · exact Or.inl hty
      obtain ⟨z, hyz, hzt⟩ := exists_adj_onTreePath hT (Ne.symm hty)
      have hzp : z ≠ p := by
        rintro rfl
        exact hyz.ne (Thomas.onTreePath_inter_eq_of_onTreePath hT (hfirst t htS)
          (Thomas.onTreePath_symm hp) hzt).symm
      have hzS : z ∈ T.neighborSet y \ {p} := ⟨hyz, hzp⟩
      have hmem : t ∈ F z := by
        rw [show F z = _ from if_pos ⟨hyz, hzp⟩]
        exact ⟨htS.1, hzt⟩
      rcases hz hzS with rfl | rfl
      · exact Or.inr (Or.inl hmem)
      · exact Or.inr (Or.inr hmem)
    have hb₁ := hF z₁
    have hb₂ := hF z₂
    have := (ncard_le_ncard hcover (toFinite _)).trans ((ncard_insert_le _ _).trans
      (Nat.add_le_add_right (ncard_union_le _ _) 1))
    have hp2 : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
    have hpos : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    omega

/-- **The bound on `|N|`.** Let `N` be a set of vertices of `T` that contains every vertex of
degree `3`. If every path of `T` has at most `n` vertices of `N`, then `|N| ≤ 3 · 2 ^ n`. -/
theorem ncard_le_of_paths (hT : T.IsTree) (hdeg : ∀ s, (T.neighborSet s).ncard ≤ 3) {N : Set ι}
    (hN2 : ∀ s ∉ N, (T.neighborSet s).ncard ≤ 2) {n : ℕ}
    (hpath : ∀ x z, (N ∩ {t | Thomas.OnTreePath T x z t}).ncard ≤ n) :
    N.ncard ≤ 3 * 2 ^ n := by
  classical
  rcases N.eq_empty_or_nonempty with hN | ⟨r, hrN⟩
  · rw [hN, ncard_empty]; exact Nat.zero_le _
  obtain ⟨z₁, z₂, z₃, hz⟩ := exists_subset_triple (hdeg r) r
  let F : ι → Set ι := fun z ↦ if T.Adj r z then N ∩ {t | Thomas.OnTreePath T r t z} else ∅
  have hF : ∀ z, (F z).ncard ≤ 2 ^ n - 1 := fun z ↦ by
    by_cases hrz : T.Adj r z
    · rw [show F z = _ from if_pos hrz]
      exact ncard_branch_le hT hdeg hN2 n hrz fun t _ ↦
        (ncard_le_ncard (fun x (hx : x ∈ N ∩ {x | Thomas.OnTreePath T r t x ∧ x ≠ r}) ↦
          (⟨hx.1, hx.2.1⟩ : x ∈ N ∩ {x | Thomas.OnTreePath T r t x})) (toFinite _)).trans
          (hpath r t)
    · rw [show F z = ∅ from if_neg hrz, ncard_empty]
      exact Nat.zero_le _
  have hcover : N ⊆ insert r (F z₁ ∪ F z₂ ∪ F z₃) := by
    intro t htN
    by_cases htr : t = r
    · exact Or.inl htr
    obtain ⟨z, hrz, hzt⟩ := exists_adj_onTreePath hT (Ne.symm htr)
    have hmem : t ∈ F z := by
      rw [show F z = _ from if_pos hrz]
      exact ⟨htN, hzt⟩
    rcases hz (show z ∈ T.neighborSet r from hrz) with rfl | rfl | rfl
    · exact Or.inr (Or.inl (Or.inl hmem))
    · exact Or.inr (Or.inl (Or.inr hmem))
    · exact Or.inr (Or.inr hmem)
  have h1 := hF z₁
  have h2 := hF z₂
  have h3 := hF z₃
  have := (ncard_le_ncard hcover (toFinite _)).trans ((ncard_insert_le _ _).trans
    (Nat.add_le_add_right ((ncard_union_le _ _).trans
      (Nat.add_le_add_right (ncard_union_le _ _) _)) 1))
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

/-- **The bound on `|N(T)|`**, as in the paper: "Since $T$ has maximum degree $\le 3$, it follows
from (2) that $|N(T)| \le 2^n$." If every path of `T` has at most `n` vertices of `N(T)`, then
`|N(T)| ≤ 2 ^ n`. Root `T` at a vertex `r` of degree `≤ 1` (`exists_ncard_neighborSet_le_one`). It
is not in `N(T)`, so all of `N(T)` lies in the one branch at `r`, and `ncard_branch_le` bounds it by
`2 ^ n - 1`. -/
theorem ncard_branchSet_le (hT : T.IsTree) (hdeg : ∀ s, (T.neighborSet s).ncard ≤ 3) {n : ℕ}
    (hpath : ∀ x z, (branchSet T ∩ {t | Thomas.OnTreePath T x z t}).ncard ≤ n) :
    (branchSet T).ncard ≤ 2 ^ n := by
  classical
  have hN2 : ∀ s ∉ branchSet T, (T.neighborSet s).ncard ≤ 2 := fun s hs ↦ by
    have := hdeg s
    have h3 : (T.neighborSet s).ncard ≠ 3 := hs
    omega
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Set.eq_empty_of_isEmpty (branchSet T), ncard_empty]
    exact Nat.zero_le _
  obtain ⟨r, hr⟩ := exists_ncard_neighborSet_le_one hT
  have hrN : r ∉ branchSet T := fun h ↦ by
    have h3 : (T.neighborSet r).ncard = 3 := h
    omega
  -- Every vertex of `N(T)` lies beyond a neighbour of `r`.
  have hbeyond : ∀ t ∈ branchSet T, ∃ z, T.Adj r z ∧ Thomas.OnTreePath T r t z := fun t ht ↦
    exists_adj_onTreePath hT fun h ↦ hrN (h ▸ ht)
  by_cases hv : ∃ v, T.Adj r v
  · obtain ⟨v, hrv⟩ := hv
    -- `v` is the only neighbour of `r`.
    have honly : ∀ z, T.Adj r z → z = v := fun z hrz ↦
      (Set.ncard_le_one (T.neighborSet r).toFinite).1 hr z hrz v hrv
    have hsub : branchSet T ⊆ branchSet T ∩ {t | Thomas.OnTreePath T r t v} := fun t ht ↦ by
      obtain ⟨z, hrz, hzt⟩ := hbeyond t ht
      exact ⟨ht, honly z hrz ▸ hzt⟩
    refine (ncard_le_ncard hsub (toFinite _)).trans ((ncard_branch_le hT hdeg hN2 n hrv
      fun t _ ↦ (ncard_le_ncard (fun x (hx : x ∈ branchSet T ∩
        {x | Thomas.OnTreePath T r t x ∧ x ≠ r}) ↦
          (⟨hx.1, hx.2.1⟩ : x ∈ branchSet T ∩ {x | Thomas.OnTreePath T r t x})) (toFinite _)).trans
          (hpath r t)).trans (Nat.sub_le _ _))
  · have : branchSet T = ∅ := eq_empty_of_forall_notMem fun t ht ↦ by
      obtain ⟨z, hrz, -⟩ := hbeyond t ht
      exact hv ⟨z, hrz⟩
    rw [this, ncard_empty]
    exact Nat.zero_le _

end GM21
end GraphMinor
