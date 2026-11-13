module

public import GraphMinor.Wagner.TripodK33

/-!
# Tripods at a vertex of degree three

Let `w` be a vertex whose neighbours are exactly `a`, `b`, `c`, and consider the society whose
cyclic permutation is `(a, w, b)`. We show that a tripod of this society gives a subdivision of
`K_{3,3}` (`hasK33Subdiv_of_deg3`).

The three redirecting paths of the tripod end at `a`, `w` and `b` in some order. The path ending at
`w` has at least one edge: otherwise `w` would be an inner vertex of one of the three paths of the
tripod, and its two neighbours on that path would both have to be `c`. Then `w` is the third
branch vertex of the subdivision: it reaches `a` and `b` by an edge, and its own redirecting path
by that path (`Tripod.thetaInner`).
-/

@[expose] public section

namespace GraphMinor.Wagner

open Set Function SimpleGraph

variable {γ : Type*} {K : SimpleGraph γ} {R Ω : Set γ}

namespace Tripod

variable (T : Tripod K R Ω)

theorem t_mem (i : Fin 3) : T.t i ∈ T.s i :: T.r i := List.mem_of_getLast? (T.hq i).2.2.2.2

theorem t_inj : Injective T.t := by
  intro i j h
  by_contra hne
  exact T.hqq i j hne (T.t i) (T.t_mem i) (h ▸ T.t_mem j)

theorem s_ne_u (k : Fin 3) : T.s k ≠ T.u := fun h => (nodup_five (T.hp k).1).2.1 h.symm

theorem s_ne_v (k : Fin 3) : T.s k ≠ T.v := (nodup_five (T.hp k).1).2.2.2.2.2.2.1

/-- When every vertex of `Ω` is some `t k`, a vertex of `Ω` on the `j`-th path from `u` to `v` is
`s j`. -/
theorem eq_s_of_mem_P (hcov : ∀ x ∈ Ω, ∃ k, T.t k = x) {j : Fin 3} {x : γ}
    (hx : x ∈ T.u :: T.pre j ++ T.s j :: T.post j ++ [T.v]) (hxΩ : x ∈ Ω) : x = T.s j := by
  obtain ⟨k, rfl⟩ := hcov x hxΩ
  rcases List.mem_cons.mp (T.t_mem k) with h | h
  · by_cases hkj : k = j
    · subst hkj
      exact h
    · exfalso
      have hk : T.t k ∈ T.u :: T.pre k ++ T.s k :: T.post k ++ [T.v] := by rw [h]; simp
      rcases T.hpp k j hkj _ hk hx with h' | h'
      · exact T.s_ne_u k (h ▸ h')
      · exact T.s_ne_v k (h ▸ h')
  · exact (T.hqX k j _ h hx).elim

/-- The last redirecting path, when it has an edge, ends at `t j`. -/
theorem r_eq_concat {j : Fin 3} (hrj : T.r j ≠ []) : T.r j = (T.r j).dropLast ++ [T.t j] := by
  obtain ⟨r', y, hr⟩ := (List.eq_nil_or_concat (T.r j)).resolve_left hrj
  rw [List.concat_eq_append] at hr
  have hlast := (T.hq j).2.2.2.2
  rw [hr, ← List.cons_append, List.getLast?_append] at hlast
  simp only [List.getLast?_singleton, Option.some_or, Option.some.injEq] at hlast
  rw [hr, List.dropLast_concat, hlast]

theorem m_sub {j i : Fin 3} {x : γ} :
    x ∈ (if i = j then (T.r j).dropLast.reverse else (T.r i).reverse) → x ∈ T.r i := by
  split_ifs with h
  · subst h
    intro hx
    exact List.dropLast_subset _ (List.mem_reverse.mp hx)
  · exact fun hx => List.mem_reverse.mp hx

/-- A tripod whose `j`-th redirecting path has an edge, and whose end `t j` is adjacent to the two
other ends, gives a `Theta` with `t j` as the third branch vertex. -/
def thetaInner (j : Fin 3) (hadj : ∀ i, i ≠ j → K.Adj (T.t j) (T.t i)) (hrj : T.r j ≠ []) :
    Theta K where
  u := T.u
  v := T.v
  z := T.t j
  s := T.s
  pre := T.pre
  post := T.post
  m := fun i => if i = j then (T.r j).dropLast.reverse else (T.r i).reverse
  huv := T.huv
  hP i := ⟨(T.hp i).1, (T.hp i).2.1⟩
  hPP := T.hpp
  hC i := by
    obtain ⟨hnd, hch, -, -, hlast⟩ := T.hq i
    by_cases hij : i = j
    · subst hij
      simp only [ite_true]
      have e : T.t i :: (T.r i).dropLast.reverse ++ [T.s i] = (T.s i :: T.r i).reverse := by
        conv_rhs => rw [T.r_eq_concat hrj]
        simp
      rw [e]
      exact ⟨List.nodup_reverse.mpr hnd, isChain_reverse_of_symm hch⟩
    · simp only [hij, ite_false]
      have e : T.t j :: (T.r i).reverse ++ [T.s i] = T.t j :: (T.s i :: T.r i).reverse := by simp
      rw [e]
      refine ⟨List.nodup_cons.mpr ⟨fun h => T.hqq j i (Ne.symm hij) _ (T.t_mem j)
        (List.mem_reverse.mp h), List.nodup_reverse.mpr hnd⟩,
        List.isChain_cons.mpr ⟨?_, isChain_reverse_of_symm hch⟩⟩
      intro y hy
      rw [List.head?_reverse, hlast] at hy
      cases hy
      exact hadj i hij
  hmP i k x hx := T.hqX i k x (T.m_sub hx)
  hmm i k hik x hx hx' :=
    T.hqq i k hik x (List.mem_cons_of_mem _ (T.m_sub hx)) (List.mem_cons_of_mem _ (T.m_sub hx'))
  hzP i h := by
    have hmem : T.t j ∈ T.r j := by
      rw [T.r_eq_concat hrj]
      simp
    exact T.hqX j i _ hmem h

end Tripod

/-- A tripod of the society `(K, (a, w, b))`, where the neighbours of `w` are exactly `a`, `b` and
`c`, gives a subdivision of `K_{3,3}`. -/
theorem hasK33Subdiv_of_deg3 {a w b c : γ} (hL : [a, w, b].Nodup)
    (hN : ∀ y, K.Adj w y ↔ y = a ∨ y = b ∨ y = c) (T : Tripod K R {x | x ∈ [a, w, b]}) :
    HasK33Subdiv K := by
  classical
  -- The three ends `t k` are the three vertices `a`, `w`, `b`.
  have hcov : ∀ x ∈ ({x | x ∈ [a, w, b]} : Set γ), ∃ k, T.t k = x := by
    have hsub : Finset.univ.image T.t ⊆ [a, w, b].toFinset := by
      intro y hy
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hy
      exact List.mem_toFinset.mpr (T.ht k)
    have hcard : [a, w, b].toFinset.card ≤ (Finset.univ.image T.t).card := by
      rw [List.toFinset_card_of_nodup hL, Finset.card_image_of_injective _ T.t_inj]
      simp
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    intro x hx
    have : x ∈ Finset.univ.image T.t := by
      rw [heq]
      exact List.mem_toFinset.mpr hx
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp this
    exact ⟨k, hk⟩
  obtain ⟨j, hj⟩ := hcov w (by simp)
  have hadj : ∀ i, i ≠ j → K.Adj (T.t j) (T.t i) := by
    intro i hij
    rw [hj, hN]
    have hti : T.t i ∈ [a, w, b] := T.ht i
    have htw : T.t i ≠ w := fun h => hij (T.t_inj (h.trans hj.symm))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hti
    rcases hti with h | h | h
    · exact Or.inl h
    · exact (htw h).elim
    · exact Or.inr (Or.inl h)
  -- The redirecting path ending at `w` has an edge.
  have hrj : T.r j ≠ [] := by
    intro hr
    have hts : T.t j = T.s j := by
      have hlast := (T.hq j).2.2.2.2
      rw [hr] at hlast
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      exact hlast.symm
    -- The two neighbours of `s j` on its path.
    set l₁ := T.u :: T.pre j with hl₁
    have e : T.u :: T.pre j ++ T.s j :: T.post j ++ [T.v] =
        l₁ ++ T.s j :: (T.post j ++ [T.v]) := by simp [hl₁]
    have hnd := (T.hp j).1
    have hch := (T.hp j).2.1
    rw [e] at hnd hch
    have hl₁ne : l₁ ≠ [] := by simp [hl₁]
    have hl₃ne : T.post j ++ [T.v] ≠ [] := by simp
    set p := l₁.getLast hl₁ne with hp
    set q := (T.post j ++ [T.v]).head hl₃ne with hq
    have hpmem : p ∈ l₁ := List.getLast_mem hl₁ne
    have hqmem : q ∈ T.post j ++ [T.v] := List.head_mem hl₃ne
    have hps : K.Adj p (T.s j) := by
      have := (List.isChain_append.mp hch).2.2
      exact this p (by rw [List.getLast?_eq_some_getLast hl₁ne]; rfl) (T.s j) rfl
    have hsq : K.Adj (T.s j) q := by
      have := List.isChain_cons.mp (List.isChain_append.mp hch).2.1
      exact this.1 q (by rw [List.head?_eq_some_head hl₃ne]; rfl)
    have hdis := (List.nodup_append.mp hnd).2.2
    have hpq : p ≠ q := hdis p hpmem q (List.mem_cons_of_mem _ hqmem)
    -- Neither neighbour lies in `Ω`, so both are `c`.
    have hPj : ∀ y, y ∈ l₁ ∨ y ∈ T.post j ++ [T.v] →
        y ∈ T.u :: T.pre j ++ T.s j :: T.post j ++ [T.v] := by
      intro y hy
      rw [e]
      rcases hy with hy | hy
      · exact List.mem_append_left _ hy
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hy)
    have hps' : p ≠ T.s j := hdis p hpmem (T.s j) List.mem_cons_self
    have hqs' : q ≠ T.s j := by
      have := (List.nodup_append.mp hnd).2.1
      exact fun h => (List.nodup_cons.mp this).1 (h ▸ hqmem)
    have hc : ∀ y, K.Adj (T.s j) y → y ≠ T.s j →
        y ∈ T.u :: T.pre j ++ T.s j :: T.post j ++ [T.v] → y = c := by
      intro y hy hys hyP
      rw [← hts, hj, hN] at hy
      rcases hy with rfl | rfl | h
      · exact (hys (T.eq_s_of_mem_P hcov hyP (by simp))).elim
      · exact (hys (T.eq_s_of_mem_P hcov hyP (by simp))).elim
      · exact h
    exact hpq ((hc p hps.symm hps' (hPj p (Or.inl hpmem))).trans
      (hc q hsq hqs' (hPj q (Or.inr hqmem))).symm)
  exact (T.thetaInner j hadj hrj).hasK33Subdiv

end GraphMinor.Wagner
