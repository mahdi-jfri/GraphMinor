module

public import GraphMinor.HP25.CrossTools
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Crossings built from lists of vertices

The proof of Lemma 4.1 (Humeau and Pous, arXiv:2505.16431v2, page 12) glues paths: it extends the
paths of a crossing along the path of a web composition, or by paths in the other web. Gluing is
easier on lists of vertices than on walks. This file turns lists back into walks and crossings:
* a chain of adjacent vertices from `u` to `v` is the support of a walk (`exists_walk_of_chain`);
* two disjoint such lists whose ends alternate on the frame give a crossing
  (`isCrossed_of_lists`, `isCrossed_of_lists_idx`);
* some list facts: gluing two chains at a common vertex (`isChain_append_of_last`), the position of
  an entry in a prefix or a suffix of a list without repetition, and the last entry of a list that
  lies in a set (`exists_last_mem`).
-/

public section

namespace GraphMinor.HP25

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### Lists -/

/-- Two chains glued at a common vertex `z`, the last entry of the first. -/
theorem isChain_append_of_last {R : V → V → Prop} {X W : List V} {z : V} (hX : X.IsChain R)
    (hl : X.getLast? = some z) (hW : (z :: W).IsChain R) : (X ++ W).IsChain R := by
  rw [List.isChain_append]
  refine ⟨hX, hW.tail, fun x hx y hy => ?_⟩
  rw [hl, Option.mem_some_iff] at hx
  subst hx
  exact (List.isChain_cons.mp hW).1 y hy

/-- An entry of a list without repetition lies in the prefix of length `p` exactly when its
position is below `p`. -/
theorem getElem_mem_take_iff {l : List V} (hnd : l.Nodup) {q : ℕ} (hq : q < l.length) (p : ℕ) :
    l[q] ∈ l.take p ↔ q < p := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨i, hi, he⟩
    have := (hnd.getElem_inj_iff (hi := by omega) (hj := hq)).mp he
    omega
  · intro h
    exact ⟨q, by omega, rfl⟩

/-- An entry of a list without repetition lies in the suffix after `p` entries exactly when its
position is at least `p`. -/
theorem getElem_mem_drop_iff {l : List V} (hnd : l.Nodup) {q : ℕ} (hq : q < l.length) (p : ℕ) :
    l[q] ∈ l.drop p ↔ p ≤ q := by
  rw [List.mem_drop_iff_getElem]
  constructor
  · rintro ⟨i, hi, he⟩
    have := (hnd.getElem_inj_iff (hi := by omega) (hj := hq)).mp he
    omega
  · intro h
    exact ⟨q - p, by omega, by congr 1; omega⟩

/-- The last entry of a list that lies in a set `Z`: the list is `α ++ u :: β` with `u ∈ Z` and no
entry of `β` in `Z`. -/
theorem exists_last_mem {Z : Set V} : ∀ (l : List V), (∃ w ∈ l, w ∈ Z) →
    ∃ α u β, l = α ++ u :: β ∧ u ∈ Z ∧ ∀ w ∈ β, w ∉ Z
  | [], h => by simp at h
  | x :: t, h => by
    by_cases ht : ∃ w ∈ t, w ∈ Z
    · obtain ⟨α, u, β, rfl, hu, hβ⟩ := exists_last_mem t ht
      exact ⟨x :: α, u, β, rfl, hu, hβ⟩
    · push Not at ht
      obtain ⟨w, hw, hwZ⟩ := h
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ⟨[], w, t, rfl, hwZ, ht⟩
      · exact absurd hwZ (ht w hw)

/-- An entry of the prefix of length `p` is an entry of position below `p`. -/
theorem exists_idx_of_mem_take {l : List V} {p : ℕ} {w : V} (h : w ∈ l.take p) :
    ∃ q, ∃ hq : q < l.length, l[q] = w ∧ q < p := by
  obtain ⟨i, hi, he⟩ := List.mem_take_iff_getElem.mp h
  exact ⟨i, by omega, he, by omega⟩

/-- An entry of the suffix after `p` entries is an entry of position at least `p`. -/
theorem exists_idx_of_mem_drop {l : List V} {p : ℕ} {w : V} (h : w ∈ l.drop p) :
    ∃ q, ∃ hq : q < l.length, l[q] = w ∧ p ≤ q := by
  obtain ⟨i, hi, he⟩ := List.mem_drop_iff_getElem.mp h
  exact ⟨_, hi, by simpa [Nat.add_comm] using he, by omega⟩

/-- **Splicing a path into a path.** Replace the part of the chain `lp` between its entries
`z₂ = lp[p₂]` and `z₄ = lp[p₄]` by a chain `Y₀` from `z₂` to `z₄` that meets `lp` only in its ends.
The result is a chain without repetition with the same ends as `lp`, and its entries are entries of
`Y₀` or entries of `lp` before `p₂` or after `p₄`. -/
theorem splice {R : V → V → Prop} {lp Y₀ : List V} (hlp : lp.IsChain R) (hnd : lp.Nodup)
    {p₂ p₄ : ℕ} (h24 : p₂ < p₄) (h4 : p₄ < lp.length) {z₂ z₄ : V} (hz₂ : lp[p₂]? = some z₂)
    (hz₄ : lp[p₄]? = some z₄) (hY : Y₀.IsChain R) (hYnd : Y₀.Nodup) (hYh : Y₀.head? = some z₂)
    (hYl : Y₀.getLast? = some z₄) (hYlp : ∀ w ∈ Y₀, w ∈ lp → w = z₂ ∨ w = z₄) :
    (lp.take p₂ ++ Y₀ ++ lp.drop (p₄ + 1)).IsChain R ∧
      (lp.take p₂ ++ Y₀ ++ lp.drop (p₄ + 1)).Nodup ∧
      (lp.take p₂ ++ Y₀ ++ lp.drop (p₄ + 1)).head? = lp.head? ∧
      (lp.take p₂ ++ Y₀ ++ lp.drop (p₄ + 1)).getLast? = lp.getLast? ∧
      ∀ w ∈ lp.take p₂ ++ Y₀ ++ lp.drop (p₄ + 1),
        w ∈ Y₀ ∨ ∃ q, ∃ hq : q < lp.length, lp[q] = w ∧ (q < p₂ ∨ p₄ < q) := by
  obtain ⟨h2, hz₂'⟩ := List.getElem?_eq_some_iff.mp hz₂
  obtain ⟨h4', hz₄'⟩ := List.getElem?_eq_some_iff.mp hz₄
  obtain ⟨Y', rfl⟩ : ∃ Y', Y₀ = z₂ :: Y' := by
    match Y₀, hYh with
    | x :: Y', hh => exact ⟨Y', by rw [Option.some_injective _ hh]⟩
  have htake : lp.take (p₂ + 1) = lp.take p₂ ++ [z₂] := by rw [List.take_add_one, hz₂]; rfl
  have hdrop : lp.drop p₄ = z₄ :: lp.drop (p₄ + 1) := by
    rw [List.drop_eq_getElem_cons h4, hz₄']
  have c1 : (lp.take p₂ ++ [z₂]).IsChain R := htake ▸ hlp.take _
  have c3 : (lp.take p₂ ++ [z₂] ++ Y').IsChain R :=
    c1.append_overlap (by simpa using hY) (by simp)
  have c4 : (z₄ :: lp.drop (p₄ + 1)).IsChain R := hdrop ▸ hlp.drop _
  have hl3 : (lp.take p₂ ++ [z₂] ++ Y').getLast? = some z₄ := by
    rw [List.append_assoc, List.getLast?_append]
    simp only [List.singleton_append]
    rw [hYl]
    rfl
  have hmt : ∀ w ∈ lp.take p₂, ∃ q, ∃ hq : q < lp.length, lp[q] = w ∧ q < p₂ :=
    fun w hw => exists_idx_of_mem_take hw
  have hmd : ∀ w ∈ lp.drop (p₄ + 1), ∃ q, ∃ hq : q < lp.length, lp[q] = w ∧ p₄ + 1 ≤ q :=
    fun w hw => exists_idx_of_mem_drop hw
  have hY0 : ∀ w ∈ z₂ :: Y', w ∈ lp → ∃ q, ∃ hq : q < lp.length, lp[q] = w ∧ (q = p₂ ∨ q = p₄) :=
    fun w hw hwl => by
      rcases hYlp w hw hwl with rfl | rfl
      · exact ⟨p₂, h2, hz₂', Or.inl rfl⟩
      · exact ⟨p₄, h4, hz₄', Or.inr rfl⟩
  have hinj : ∀ {q q' : ℕ} (hq : q < lp.length) (hq' : q' < lp.length), lp[q] = lp[q'] → q = q' :=
    fun hq hq' h => (hnd.getElem_inj_iff).mp h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := isChain_append_of_last c3 hl3 c4
    simpa using this
  · rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨hnd.sublist (List.take_sublist _ _), hYnd, fun u hu v hv huv => ?_⟩,
      (hnd.sublist (List.drop_sublist _ _)), fun u hu v hv huv => ?_⟩
    · subst huv
      obtain ⟨q, hq, rfl, hlt⟩ := hmt u hu
      obtain ⟨q', hq', he, hq'e⟩ := hY0 _ hv (List.getElem_mem _)
      have := hinj hq' hq he
      omega
    · subst huv
      obtain ⟨q, hq, rfl, hlt⟩ := hmd u hv
      rcases List.mem_append.mp hu with hu | hu
      · obtain ⟨q', hq', he, hlt'⟩ := hmt _ hu
        have := hinj hq' hq he
        omega
      · obtain ⟨q', hq', he, hq'e⟩ := hY0 _ hu (List.getElem_mem _)
        have := hinj hq' hq he
        omega
  · rw [List.append_assoc, List.head?_append, List.head?_take]
    split_ifs with h0
    · subst h0
      simp only [Option.none_or, List.head?_append, List.head?_cons, Option.some_or]
      rw [List.head?_eq_getElem?, ← hz₂]
    · simp [List.head?_eq_getElem?, List.getElem?_eq_getElem (show 0 < lp.length by omega)]
  · have hlast : lp.getLast? = some (lp.getLast (List.ne_nil_of_length_pos (by omega))) :=
      List.getLast?_eq_some_getLast _
    by_cases hlen : lp.length ≤ p₄ + 1
    · rw [List.drop_eq_nil_of_le hlen, List.append_nil, List.getLast?_append, hYl,
        Option.some_or, List.getLast?_eq_getElem? (l := lp), show lp.length - 1 = p₄ by omega, hz₄]
    · simp only [List.getLast?_append, List.getLast?_drop, hlen, ↓reduceIte, hlast,
        Option.some_or]
  · intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨q, hq, he, hlt⟩ := hmt w hw
        exact Or.inr ⟨q, hq, he, Or.inl hlt⟩
      · exact Or.inl hw
    · obtain ⟨q, hq, he, hlt⟩ := hmd w hw
      exact Or.inr ⟨q, hq, he, Or.inr (by omega)⟩

/-- **Extending a path to the start of a path.** A chain `X₀` that ends at the entry `z = lp[p]` of
a chain `lp`, and meets `lp` only there, continues along `lp` back to its first entry. -/
theorem extend_start {R : V → V → Prop} (hR : ∀ u v, R u v → R v u) {lp X₀ : List V}
    (hlp : lp.IsChain R) (hnd : lp.Nodup) {p : ℕ} (hp : p < lp.length) {z : V}
    (hz : lp[p]? = some z) (hX : X₀.IsChain R) (hXnd : X₀.Nodup) (hXl : X₀.getLast? = some z)
    (hXlp : ∀ w ∈ X₀, w ∈ lp → w = z) :
    (X₀ ++ (lp.take p).reverse).IsChain R ∧ (X₀ ++ (lp.take p).reverse).Nodup ∧
      (X₀ ++ (lp.take p).reverse).head? = X₀.head? ∧
      (X₀ ++ (lp.take p).reverse).getLast? = lp.head? ∧
      ∀ w ∈ X₀ ++ (lp.take p).reverse, w ∈ X₀ ∨ ∃ q, ∃ hq : q < lp.length, lp[q] = w ∧ q < p := by
  obtain ⟨hp', hz'⟩ := List.getElem?_eq_some_iff.mp hz
  have htake : lp.take (p + 1) = lp.take p ++ [z] := by rw [List.take_add_one, hz]; rfl
  have hc : (z :: (lp.take p).reverse).IsChain R := by
    have : ((lp.take (p + 1)).reverse).IsChain R :=
      List.isChain_reverse.mpr ((hlp.take _).imp fun u v h => hR u v h)
    rw [htake] at this
    simpa using this
  have hne : X₀ ≠ [] := by rintro rfl; simp at hXl
  refine ⟨isChain_append_of_last hX hXl hc, ?_, ?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hXnd, List.nodup_reverse.mpr (hnd.sublist (List.take_sublist _ _)),
      fun u hu v hv huv => ?_⟩
    subst huv
    rw [List.mem_reverse] at hv
    obtain ⟨q, hq, he, hlt⟩ := exists_idx_of_mem_take hv
    have h1 := hXlp u hu (he ▸ List.getElem_mem hq)
    rw [← he, ← hz'] at h1
    have := (hnd.getElem_inj_iff).mp h1
    omega
  · rw [List.head?_append]
    cases h : X₀.head? with
    | none => simp_all
    | some x => rfl
  · rw [List.getLast?_append, List.getLast?_reverse, List.head?_take]
    split_ifs with h0
    · subst h0
      rw [Option.none_or, hXl, List.head?_eq_getElem?, hz]
    · cases h : lp.head? <;> simp_all
  · intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact Or.inl hw
    · rw [List.mem_reverse] at hw
      exact Or.inr (exists_idx_of_mem_take hw)

/-! ### From lists to walks and crossings -/

/-- A chain of `G` from `u` to `v` is the support of a walk from `u` to `v`. -/
theorem exists_walk_of_chain : ∀ (l : List V) {u v : V}, l.IsChain G.Adj → l.head? = some u →
    l.getLast? = some v → ∃ p : G.Walk u v, p.support = l
  | [], _, _, _, h, _ => by simp at h
  | [x], u, v, _, hh, hl => by
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at hh hl
    subst hh hl
    exact ⟨Walk.nil, rfl⟩
  | x :: y :: t, u, v, hc, hh, hl => by
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    have hc' := List.isChain_cons_cons.mp hc
    obtain ⟨p, hp⟩ := exists_walk_of_chain (y :: t) hc'.2 rfl
      (by rwa [List.getLast?_cons_cons] at hl)
    exact ⟨Walk.cons hc'.1 p, by simp [hp]⟩

/-- A chain without repetition from `u` to `v`, with no other entry in `T`, is a `T`-path. -/
theorem exists_tPath_of_list {T X : List V} {u v : V} (hX : X.IsChain G.Adj) (hnd : X.Nodup)
    (hh : X.head? = some u) (hl : X.getLast? = some v) (hu : u ∈ T) (hv : v ∈ T)
    (hin : ∀ w ∈ X, w ∈ T → w = u ∨ w = v) : ∃ p : G.Walk u v, IsTPath G T p ∧ p.support = X := by
  obtain ⟨p, hp⟩ := exists_walk_of_chain X hX hh hl
  refine ⟨p, ⟨?_, hu, hv, fun w hw h1 h2 => ?_⟩, hp⟩
  · rw [Walk.isPath_def, hp]
    exact hnd
  · have : w ∉ T := fun hwT => by
      rcases hin w (hp ▸ hw) hwT with h | h
      · exact h1 h
      · exact h2 h
    exact ⟨this, this⟩

/-- **Alternating lists give a crossing.** If `T` is, up to rotation, `a L₁ b L₂`, a chain from
`a` to `b` and a chain from `c ∈ L₁` to `d ∈ L₂`, disjoint, without repetition and with no other
entry in `T`, form a crossing of `T`. -/
theorem isCrossed_of_lists {T : List V} {a b c d : V} {k : ℕ} {L₁ L₂ X Y : List V}
    (hrot : T.rotate k = a :: L₁ ++ b :: L₂) (hc : c ∈ L₁) (hd : d ∈ L₂)
    (hX : X.IsChain G.Adj) (hXnd : X.Nodup) (hXh : X.head? = some a) (hXl : X.getLast? = some b)
    (hXin : ∀ w ∈ X, w ∈ T → w = a ∨ w = b)
    (hY : Y.IsChain G.Adj) (hYnd : Y.Nodup) (hYh : Y.head? = some c) (hYl : Y.getLast? = some d)
    (hYin : ∀ w ∈ Y, w ∈ T → w = c ∨ w = d) (hdisj : X.Disjoint Y) : IsCrossed G T := by
  have hmem : ∀ w, w ∈ a :: L₁ ++ b :: L₂ → w ∈ T := fun w hw => by
    rw [← hrot] at hw
    exact List.mem_rotate.mp hw
  obtain ⟨Q, hQ, hQs⟩ := exists_tPath_of_list hX hXnd hXh hXl (hmem a (by simp)) (hmem b (by simp))
    hXin
  obtain ⟨R, hR, hRs⟩ := exists_tPath_of_list hY hYnd hYh hYl (hmem c (by simp [hc]))
    (hmem d (by simp [hd])) hYin
  exact isCrossed_of_alternate hrot hc hd Q R hQ hR (by rw [hQs, hRs]; exact hdisj)

/-- **Lists with alternating positions give a crossing.** A chain from the entry `i` to the entry
`j` of a rotation of `T`, and one from the entry `r` to the entry `s`, with `i < r < j < s`,
disjoint, without repetition and with no other entry in `T`, form a crossing of `T`. -/
theorem isCrossed_of_lists_idx {T T' : List V} {k : ℕ} (hrot : T.rotate k = T') {i r j s : ℕ}
    (hir : i < r) (hrj : r < j) (hjs : j < s) (hs : s < T'.length) {X Y : List V}
    (hX : X.IsChain G.Adj) (hXnd : X.Nodup) (hXh : X.head? = T'[i]?) (hXl : X.getLast? = T'[j]?)
    (hXin : ∀ w ∈ X, w ∈ T → X.head? = some w ∨ X.getLast? = some w)
    (hY : Y.IsChain G.Adj) (hYnd : Y.Nodup) (hYh : Y.head? = T'[r]?) (hYl : Y.getLast? = T'[s]?)
    (hYin : ∀ w ∈ Y, w ∈ T → Y.head? = some w ∨ Y.getLast? = some w) (hdisj : X.Disjoint Y) :
    IsCrossed G T := by
  have hmem : ∀ w, w ∈ T' → w ∈ T := fun w hw => by
    rw [← hrot] at hw
    exact List.mem_rotate.mp hw
  rw [List.getElem?_eq_getElem (by omega)] at hXh hXl hYh
  rw [List.getElem?_eq_getElem hs] at hYl
  have hin : ∀ {Z : List V} {u v : V}, Z.head? = some u → Z.getLast? = some v →
      (∀ w ∈ Z, w ∈ T → Z.head? = some w ∨ Z.getLast? = some w) →
      ∀ w ∈ Z, w ∈ T → w = u ∨ w = v := fun {Z u v} hh hl h w hw hwT => by
    rcases h w hw hwT with h' | h'
    · exact Or.inl (Option.some_injective _ (h'.symm.trans hh))
    · exact Or.inr (Option.some_injective _ (h'.symm.trans hl))
  obtain ⟨Q, hQ, hQs⟩ := exists_tPath_of_list hX hXnd hXh hXl (hmem _ (List.getElem_mem _))
    (hmem _ (List.getElem_mem _)) (hin hXh hXl hXin)
  obtain ⟨R, hR, hRs⟩ := exists_tPath_of_list hY hYnd hYh hYl (hmem _ (List.getElem_mem _))
    (hmem _ (List.getElem_mem _)) (hin hYh hYl hYin)
  refine IsCrossed.of_rotate k ⟨_, _, _, _, Q, R, ⟨⟨i, r, j, s, hir, hrj, hjs, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_⟩⟩
  · rw [hrot]; exact List.getElem?_eq_getElem _
  · rw [hrot]; exact List.getElem?_eq_getElem _
  · rw [hrot]; exact List.getElem?_eq_getElem _
  · rw [hrot]; exact List.getElem?_eq_getElem _
  · exact (isTPath_congr (fun w => List.mem_rotate.symm) Q).mp hQ
  · exact (isTPath_congr (fun w => List.mem_rotate.symm) R).mp hR
  · rw [hQs, hRs]
    exact hdisj

end GraphMinor.HP25
