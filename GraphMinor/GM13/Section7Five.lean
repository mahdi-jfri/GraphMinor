module

public import GraphMinor.GM13.Section7
public import GraphMinor.GM09.Section2c
public import GraphMinor.GM09.Section4a
public import GraphMinor.GM13.Section7Cells
public import GraphMinor.GM16.Defs

/-!
# Graph Minors XIII, (7.5): many stars give many far `H`-paths

The proof of (7.5) (page 91) proves by induction on `k` that `k` external `(l, m)`-stars with
distinct centers, `l = 2k² - k + 3`, give `k` disjoint `H`-paths whose `2k` ends are mutually at
distance at least `m / 2`. In the step, either many rays of the last star meet one of the old
paths `Q_j`, and pairs of them are joined along `Q_j`, or two rays of the last star miss all old
paths and are far from their ends, and they form the new path.

This file first proves the step that joins pairs of rays along `Q_j`, as a lemma on a single
path (`exists_disjoint_subpaths_of_marks`): a path with `2n` marked vertices has `n` disjoint
subpaths, each joining two marked vertices and meeting no other marked vertex and no end of the
path except its own ends.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function
open Graph
open GraphMinor
open GraphMinor.GM09
open GraphMinor.Surface

universe u v

variable {α : Type u} {β : Type v}

/-- **Split at the first hit.** A path from `a` to `b` that meets `X` splits at its first vertex
`z` in `X` into a path from `a` to `z` that meets `X` only in `z`, and a path from `z` to `b`. -/
theorem exists_split_first_hit {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) {X : Set α} (hne : (V(P) ∩ X).Nonempty) :
    ∃ z ∈ V(P) ∩ X, ∃ P₁ P₂ : Graph α β, P₁ ≤ P ∧ P₂ ≤ P ∧
      IsGraphPathWithEnds G P₁ a z ∧ IsGraphPathWithEnds G P₂ z b ∧
      V(P₁) ∩ V(P₂) = {z} ∧ V(P₁) ∩ X = {z} ∧ V(P) = V(P₁) ∪ V(P₂) := by
  obtain ⟨z, hz, Q, -, hQ, hQX, -⟩ := hP.exists_first_hit hne
  obtain ⟨P₁, P₂, h1, h2, hp1, hp2, hU, hI, -⟩ := hP.exists_split_at hz.1
  have hQP : Q = P₁ := hP.subpath_unique_of_left hQ hp1
  subst hQP
  refine ⟨z, hz, Q, P₂, h1, h2, hp1.mono hP.le, hp2.mono hP.le, hI, hQX, ?_⟩
  rw [← vertexSet_subgraphUnion P Q P₂, hU]

/-- **Pairing marked vertices along a path.** A path from `a` to `b` with at least `2n` marked
vertices has `n` vertex-disjoint subpaths, each joining two distinct marked vertices and meeting
the marked vertices and the ends of the path only in its own ends. -/
theorem exists_disjoint_subpaths_of_marks [DecidableEq α] {G : Graph α β} :
    ∀ (n : ℕ) {P : Graph α β} {a b : α}, IsGraphPathWithEnds G P a b →
      ∀ X : Finset α, (↑X : Set α) ⊆ V(P) → 2 * n ≤ X.card →
      ∃ (B : Fin n → Graph α β) (x y : Fin n → α),
        (∀ t, B t ≤ P ∧ IsGraphPathWithEnds G (B t) (x t) (y t) ∧ x t ∈ X ∧ y t ∈ X ∧
          x t ≠ y t ∧ V(B t) ∩ ((↑X : Set α) ∪ {a, b}) ⊆ {x t, y t}) ∧
        Pairwise (fun t t' => Disjoint V(B t) V(B t'))
  | 0, _, _, _, _, _, _, _ =>
    ⟨Fin.elim0, Fin.elim0, Fin.elim0, fun t => t.elim0, fun t => t.elim0⟩
  | n + 1, P, a, b, hP, X, hXP, hcard => by
    -- the first marked vertex `x₁` from `a`
    have hne1 : (V(P) ∩ (↑X : Set α)).Nonempty := by
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < X.card)
      exact ⟨x, hXP hx, hx⟩
    obtain ⟨x₁, ⟨-, hx₁X⟩, P₁, P₂, hP₁P, hP₂P, hp₁, hp₂, hI₁, hX₁, hV₁⟩ :=
      exists_split_first_hit hP hne1
    -- the next marked vertex `x₂` after `x₁`
    set X₁ := X.erase x₁ with hX₁def
    have hX₁P₂ : (↑X₁ : Set α) ⊆ V(P₂) := by
      intro x hx
      have hx' := Finset.mem_erase.mp hx
      have hxP := hXP hx'.2
      rw [hV₁] at hxP
      rcases hxP with h | h
      · have : x ∈ V(P₁) ∩ (↑X : Set α) := ⟨h, hx'.2⟩
        rw [hX₁] at this
        exact absurd this hx'.1
      · exact h
    have hcard1 : 2 * n + 1 ≤ X₁.card := by
      rw [Finset.card_erase_of_mem hx₁X]; omega
    have hne2 : (V(P₂) ∩ (↑X₁ : Set α)).Nonempty := by
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < X₁.card)
      exact ⟨x, hX₁P₂ hx, hx⟩
    obtain ⟨x₂, ⟨-, hx₂X₁⟩, C, P₃, hCP₂, hP₃P₂, hC, hp₃, hI₂, hX₂, hV₂⟩ :=
      exists_split_first_hit hp₂ hne2
    have hx₂ := Finset.mem_erase.mp hx₂X₁
    set X₂ := X₁.erase x₂ with hX₂def
    have hX₂P₃ : (↑X₂ : Set α) ⊆ V(P₃) := by
      intro x hx
      have hx' := Finset.mem_erase.mp hx
      have hxP := hX₁P₂ hx'.2
      rw [hV₂] at hxP
      rcases hxP with h | h
      · have : x ∈ V(C) ∩ (↑X₁ : Set α) := ⟨h, hx'.2⟩
        rw [hX₂] at this
        exact absurd this hx'.1
      · exact h
    have hcard2 : 2 * n ≤ X₂.card := by
      rw [Finset.card_erase_of_mem hx₂X₁]; omega
    obtain ⟨B', x', y', hB', hdisj'⟩ := exists_disjoint_subpaths_of_marks n hp₃ X₂ hX₂P₃ hcard2
    -- facts on where `x₁` and `a` lie
    have hx₁C : x₁ ∈ V(C) := hC.left_mem
    have hx₁P₃ : x₁ ∉ V(P₃) := by
      intro h
      have : x₁ ∈ V(C) ∩ V(P₃) := ⟨hx₁C, h⟩
      rw [hI₂] at this
      exact hx₂.1 this.symm
    have haP₂ : a ∈ V(P₂) → a = x₁ := by
      intro h
      have : a ∈ V(P₁) ∩ V(P₂) := ⟨hp₁.left_mem, h⟩
      rwa [hI₁] at this
    have hP₃P : P₃ ≤ P := hP₃P₂.trans hP₂P
    refine ⟨Fin.cons C B', Fin.cons x₁ x', Fin.cons x₂ y', ?_, ?_⟩
    · intro t
      refine Fin.cases ?_ (fun t => ?_) t
      · simp only [Fin.cons_zero]
        refine ⟨hCP₂.trans hP₂P, hC, hx₁X, hx₂.2, fun h => hx₂.1 h.symm, ?_⟩
        rintro w ⟨hwC, hw⟩
        rcases hw with hwX | hwab
        · by_cases hw1 : w = x₁
          · exact Or.inl hw1
          · have : w ∈ V(C) ∩ (↑X₁ : Set α) := ⟨hwC, Finset.mem_erase.mpr ⟨hw1, hwX⟩⟩
            rw [hX₂] at this
            exact Or.inr this
        · rcases hwab with rfl | rfl
          · exact Or.inl (haP₂ (hCP₂.vertexSet_mono hwC))
          · have : w ∈ V(C) ∩ V(P₃) := ⟨hwC, hp₃.right_mem⟩
            rw [hI₂] at this
            exact Or.inr this
      · simp only [Fin.cons_succ]
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hB' t
        refine ⟨h1.trans hP₃P, h2, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h3),
          Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h4), h5, ?_⟩
        rintro w ⟨hwB, hw⟩
        have hwP₃ : w ∈ V(P₃) := h1.vertexSet_mono hwB
        apply h6
        refine ⟨hwB, ?_⟩
        rcases hw with hwX | hwab
        · by_cases hw1 : w = x₁
          · exact absurd (hw1 ▸ hwP₃) hx₁P₃
          by_cases hw2 : w = x₂
          · exact Or.inr (Or.inl hw2)
          · exact Or.inl (Finset.mem_erase.mpr ⟨hw2, Finset.mem_erase.mpr ⟨hw1, hwX⟩⟩)
        · rcases hwab with rfl | rfl
          · have := haP₂ (hP₃P₂.vertexSet_mono hwP₃)
            exact absurd (this ▸ hwP₃) hx₁P₃
          · exact Or.inr (Or.inr rfl)
    · -- disjointness
      have hCB : ∀ t, Disjoint V(C) V(B' t) := by
        intro t
        rw [Set.disjoint_left]
        intro w hwC hwB
        obtain ⟨h1, -, h3, h4, -, h6⟩ := hB' t
        have : w ∈ V(C) ∩ V(P₃) := ⟨hwC, h1.vertexSet_mono hwB⟩
        rw [hI₂] at this
        rw [mem_singleton_iff] at this
        subst this
        have hw := h6 ⟨hwB, Or.inr (Or.inl rfl)⟩
        rcases hw with h | h
        · rw [← h] at h3; exact (Finset.mem_erase.mp h3).1 rfl
        · rw [← h] at h4; exact (Finset.mem_erase.mp h4).1 rfl
      intro t t' htt'
      refine Fin.cases (fun htt' => ?_) (fun t htt' => ?_) t htt'
      · refine Fin.cases (fun h => absurd rfl h) (fun t' _ => ?_) t' htt'
        simpa using hCB t'
      · refine Fin.cases (fun _ => ?_) (fun t' h => ?_) t' htt'
        · simpa using (hCB t).symm
        · simpa using hdisj' (fun e => h (by rw [e]))

/-! ## Joining rays along a path -/

/-- The data of the rays of a star with center `w` and ends `u`: paths from `w` to `u i` that meet
`H` at most in their ends, avoid the edges of `H`, and meet each other only in `w`. -/
structure IsRays (G Hg : Graph α β) {l : ℕ} (P : Fin l → Graph α β) (w : α) (u : Fin l → α) :
    Prop where
  path : ∀ i, IsGraphPathWithEnds G (P i) w (u i)
  ne : ∀ i, u i ≠ w
  mem : ∀ i, u i ∈ V(Hg)
  inter : ∀ i, V(P i) ∩ V(Hg) ⊆ {w, u i}
  edges : ∀ i, Disjoint E(P i) E(Hg)
  disj : ∀ i j, i ≠ j → V(P i) ∩ V(P j) = {w}
  center : w ∉ V(Hg)

theorem IsRays.u_injective {G Hg : Graph α β} {l : ℕ} {P : Fin l → Graph α β} {w : α}
    {u : Fin l → α} (hR : IsRays G Hg P w u) : Injective u := by
  intro i j h
  by_contra hij
  have : u i ∈ V(P i) ∩ V(P j) := ⟨(hR.path i).right_mem, h ▸ (hR.path j).right_mem⟩
  rw [hR.disj i j hij] at this
  exact hR.ne i this

/-- **Case A of the step of (7.5).** If at least `2n` rays of a star meet an `H`-path `Q` that
avoids the center, then there are `n` disjoint `H`-paths, each made of two pieces of rays and a
piece of `Q`, whose ends are the ends of `2n` distinct rays. -/
theorem exists_hPaths_of_rays_meet [DecidableEq α] {G Hg : Graph α β} {l : ℕ}
    {P : Fin l → Graph α β} {w : α} {u : Fin l → α} (hR : IsRays G Hg P w u)
    {Q : Graph α β} {a b : α} (hQ : IsHPathWithEnds G Hg Q a b) (hwQ : w ∉ V(Q))
    (n : ℕ) (I : Finset (Fin l)) (hI : ∀ i ∈ I, (V(P i) ∩ V(Q)).Nonempty) (hcard : 2 * n ≤ I.card) :
    ∃ (R : Fin n → Graph α β) (i j : Fin n → Fin l),
      (∀ t, IsHPathWithEnds G Hg (R t) (u (i t)) (u (j t)) ∧
        V(R t) ⊆ V(Q) ∪ V(P (i t)) ∪ V(P (j t))) ∧
      Injective (fun x : Fin n ⊕ Fin n => Sum.elim i j x) ∧
      Pairwise (fun t t' => Disjoint V(R t) V(R t')) := by
  classical
  obtain ⟨hHG, hQp, hab, ha, hb, hQH, hQE⟩ := hQ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨Fin.elim0, Fin.elim0, Fin.elim0, fun t => t.elim0, ?_, fun t => t.elim0⟩
    rintro (t | t) <;> exact t.elim0
  have : Nonempty (Fin l) := ⟨(Finset.card_pos.mp (by omega : 0 < I.card)).choose⟩
  have : Nonempty α := ⟨a⟩
  -- the first vertex of each ray, from its end `u i`, on `Q`
  have hfirst : ∀ i ∈ I, ∃ z ∈ V(P i) ∩ V(Q), ∃ A : Graph α β, A ≤ P i ∧
      IsGraphPathWithEnds G A (u i) z ∧ V(A) ∩ V(Q) = {z} ∧ w ∉ V(A) := by
    intro i hi
    obtain ⟨z, hz, A, hAP, hA, hAQ, hw⟩ := (hR.path i).symm.exists_first_hit (hI i hi)
    refine ⟨z, hz, A, hAP, hA.mono (hR.path i).le, hAQ, fun hwA => hwQ ?_⟩
    rw [hw hwA] at hz
    exact hz.2
  choose! z hz A hAP hA hAQ hwA using hfirst
  -- the marks on `Q`
  have hzinj : InjOn z (↑I : Set (Fin l)) := by
    intro i hi j hj h
    by_contra hij
    have : z i ∈ V(P i) ∩ V(P j) := ⟨(hz i hi).1, h ▸ (hz j hj).1⟩
    rw [hR.disj i j hij] at this
    exact hwQ (this ▸ (hz i hi).2)
  set X := I.image z
  have hXcard : X.card = I.card := Finset.card_image_of_injOn hzinj
  obtain ⟨B, x, y, hB, hBdisj⟩ := exists_disjoint_subpaths_of_marks n hQp X
    (by intro p hp; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp; exact (hz i hi).2)
    (by omega)
  have hpick : ∀ p ∈ X, ∃ i ∈ I, z i = p := fun p hp => by
    obtain ⟨i, hi, e⟩ := Finset.mem_image.mp hp; exact ⟨i, hi, e⟩
  choose! idx hidxI hidx using hpick
  let i : Fin n → Fin l := fun t => idx (x t)
  let j : Fin n → Fin l := fun t => idx (y t)
  have hiI : ∀ t, i t ∈ I := fun t => hidxI _ (hB t).2.2.1
  have hjI : ∀ t, j t ∈ I := fun t => hidxI _ (hB t).2.2.2.1
  have hzi : ∀ t, z (i t) = x t := fun t => hidx _ (hB t).2.2.1
  have hzj : ∀ t, z (j t) = y t := fun t => hidx _ (hB t).2.2.2.1
  -- a ray piece meets `H` only in its end
  have hAH : ∀ k ∈ I, V(A k) ∩ V(Hg) ⊆ {u k} := by
    intro k hk p ⟨hpA, hpH⟩
    rcases hR.inter k ⟨(hAP k hk).vertexSet_mono hpA, hpH⟩ with h | h
    · exact absurd (h ▸ hpA) (hwA k hk)
    · exact h
  -- two ray pieces of different rays are disjoint
  have hAA : ∀ k ∈ I, ∀ k' ∈ I, k ≠ k' → Disjoint V(A k) V(A k') := by
    intro k hk k' hk' hne
    rw [Set.disjoint_left]
    intro p hp hp'
    have : p ∈ V(P k) ∩ V(P k') :=
      ⟨(hAP k hk).vertexSet_mono hp, (hAP k' hk').vertexSet_mono hp'⟩
    rw [hR.disj k k' hne] at this
    exact hwA k hk (this ▸ hp)
  -- a ray piece meets a piece of `Q` only in its mark
  have hAB : ∀ k ∈ I, ∀ t, V(A k) ∩ V(B t) ⊆ {z k} := by
    intro k hk t p ⟨hpA, hpB⟩
    have : p ∈ V(A k) ∩ V(Q) := ⟨hpA, (hB t).1.vertexSet_mono hpB⟩
    rwa [hAQ k hk] at this
  have hxy : ∀ t, i t ≠ j t := fun t h => (hB t).2.2.2.2.1 (by rw [← hzi, ← hzj, h])
  -- the indices are distinct
  have hmark : ∀ t t', x t ∈ V(B t') ∨ y t ∈ V(B t') → t = t' := by
    intro t t' h
    by_contra hne
    have hd := hBdisj hne
    rcases h with h | h
    · exact Set.disjoint_left.mp hd (hB t).2.1.left_mem h
    · exact Set.disjoint_left.mp hd (hB t).2.1.right_mem h
  have hinj : Injective (fun x : Fin n ⊕ Fin n => Sum.elim i j x) := by
    have key : ∀ t t', z (i t) = z (i t') ∨ z (i t) = z (j t') ∨ z (j t) = z (i t') ∨
        z (j t) = z (j t') → t = t' := by
      intro t t' h
      rw [hzi, hzi, hzj, hzj] at h
      rcases h with h | h | h | h
      · exact hmark t t' (Or.inl (h ▸ (hB t').2.1.left_mem))
      · exact hmark t t' (Or.inl (h ▸ (hB t').2.1.right_mem))
      · exact hmark t t' (Or.inr (h ▸ (hB t').2.1.left_mem))
      · exact hmark t t' (Or.inr (h ▸ (hB t').2.1.right_mem))
    rintro (t | t) (t' | t') h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · rw [key t t' (Or.inl (by rw [h]))]
    · have := key t t' (Or.inr (Or.inl (by rw [h])))
      subst this; exact absurd h (hxy t)
    · have := key t t' (Or.inr (Or.inr (Or.inl (by rw [h]))))
      subst this; exact absurd h.symm (hxy t)
    · rw [key t t' (Or.inr (Or.inr (Or.inr (by rw [h]))))]
  -- the paths
  let R : Fin n → Graph α β := fun t =>
    subgraphUnion G (subgraphUnion G (A (i t)) (B t)) (A (j t))
  have hRV : ∀ t, V(R t) = V(A (i t)) ∪ V(B t) ∪ V(A (j t)) := fun t => rfl
  refine ⟨R, i, j, fun t => ?_, hinj, ?_⟩
  · have hAi := hA _ (hiI t)
    have hAj := hA _ (hjI t)
    have hBt := (hB t).2.1
    have hI1 : V(A (i t)) ∩ V(B t) = {x t} := by
      apply Subset.antisymm
      · rw [← hzi t]; exact hAB _ (hiI t) t
      · rintro p rfl; exact ⟨hzi t ▸ hAi.right_mem, hBt.left_mem⟩
    have h1 : IsGraphPathWithEnds G (subgraphUnion G (A (i t)) (B t)) (u (i t)) (y t) := by
      have hAi' : IsGraphPathWithEnds G (A (i t)) (u (i t)) (x t) := hzi t ▸ hAi
      exact hAi'.subgraphUnion hBt hI1
    have hI2 : V(subgraphUnion G (A (i t)) (B t)) ∩ V(A (j t)) = {y t} := by
      apply Subset.antisymm
      · rintro p ⟨hp1 | hp1, hp2⟩
        · exact absurd hp2 (Set.disjoint_left.mp (hAA _ (hiI t) _ (hjI t) (hxy t)) hp1)
        · rw [← hzj t]; exact hAB _ (hjI t) t ⟨hp2, hp1⟩
      · rintro p rfl; exact ⟨Or.inr hBt.right_mem, hzj t ▸ hAj.right_mem⟩
    have h2 : IsGraphPathWithEnds G (R t) (u (i t)) (u (j t)) :=
      h1.subgraphUnion (hzj t ▸ hAj.symm) hI2
    refine ⟨⟨hHG, h2, hR.u_injective.ne (hxy t), hR.mem _, hR.mem _, ?_, ?_⟩, ?_⟩
    · apply Subset.antisymm
      · rintro p ⟨hp, hpH⟩
        rw [hRV] at hp
        rcases hp with (hp | hp) | hp
        · exact Or.inl (hAH _ (hiI t) ⟨hp, hpH⟩)
        · have hpQ : p ∈ V(Q) ∩ V(Hg) := ⟨(hB t).1.vertexSet_mono hp, hpH⟩
          rw [hQH] at hpQ
          have hpe : p ∈ ({x t, y t} : Set α) := (hB t).2.2.2.2.2 ⟨hp, Or.inr hpQ⟩
          rcases hpe with rfl | rfl
          · exact Or.inl (hAH _ (hiI t) ⟨hzi t ▸ hAi.right_mem, hpH⟩)
          · exact Or.inr (hAH _ (hjI t) ⟨hzj t ▸ hAj.right_mem, hpH⟩)
        · exact Or.inr (hAH _ (hjI t) ⟨hp, hpH⟩)
      · rintro p (rfl | rfl)
        · exact ⟨Or.inl (Or.inl hAi.left_mem), hR.mem _⟩
        · exact ⟨Or.inr hAj.left_mem, hR.mem _⟩
    · rw [Set.disjoint_left]
      intro e he heH
      have he' := edgeSet_subgraphUnion_subset _ _ _ he
      rcases he' with he' | he'
      · rcases edgeSet_subgraphUnion_subset _ _ _ he' with he'' | he''
        · exact Set.disjoint_left.mp (hR.edges _) ((hAP _ (hiI t)).edgeSet_mono he'') heH
        · exact Set.disjoint_left.mp hQE ((hB t).1.edgeSet_mono he'') heH
      · exact Set.disjoint_left.mp (hR.edges _) ((hAP _ (hjI t)).edgeSet_mono he') heH
    · rw [hRV]
      rintro p ((hp | hp) | hp)
      · exact Or.inl (Or.inr ((hAP _ (hiI t)).vertexSet_mono hp))
      · exact Or.inl (Or.inl ((hB t).1.vertexSet_mono hp))
      · exact Or.inr ((hAP _ (hjI t)).vertexSet_mono hp)
  · intro t t' htt'
    rw [Set.disjoint_left]
    intro p hp hp'
    rw [hRV] at hp hp'
    have hne : ∀ (k k' : Fin l), (k = i t ∨ k = j t) → (k' = i t' ∨ k' = j t') → k ≠ k' := by
      intro k k' hk hk' e
      subst e
      rcases hk with rfl | rfl <;> rcases hk' with h | h
      · exact htt' (Sum.inl_injective (hinj (show Sum.elim i j (Sum.inl t) = Sum.elim i j (Sum.inl t') by simp [h])))
      · exact absurd (hinj (show Sum.elim i j (Sum.inl t) = Sum.elim i j (Sum.inr t') by simp [h]))
          Sum.inl_ne_inr
      · exact absurd (hinj (show Sum.elim i j (Sum.inr t) = Sum.elim i j (Sum.inl t') by simp [h]))
          Sum.inr_ne_inl
      · exact htt' (Sum.inr_injective (hinj (show Sum.elim i j (Sum.inr t) = Sum.elim i j (Sum.inr t') by simp [h])))
    -- a piece of a ray of `R t` meets `R t'` nowhere
    have hApiece : ∀ k, (k = i t ∨ k = j t) → p ∈ V(A k) → False := by
      intro k hk hpk
      have hkI : k ∈ I := by rcases hk with rfl | rfl; exacts [hiI t, hjI t]
      rcases hp' with (hp' | hp') | hp'
      · exact Set.disjoint_left.mp (hAA k hkI _ (hiI t') (hne k _ hk (Or.inl rfl))) hpk hp'
      · have hpz : p = z k := hAB k hkI t' ⟨hpk, hp'⟩
        have hzB : z k ∈ V(B t) := by
          rcases hk with rfl | rfl
          · rw [hzi]; exact (hB t).2.1.left_mem
          · rw [hzj]; exact (hB t).2.1.right_mem
        exact Set.disjoint_left.mp (hBdisj htt') hzB (hpz ▸ hp')
      · exact Set.disjoint_left.mp (hAA k hkI _ (hjI t') (hne k _ hk (Or.inr rfl))) hpk hp'
    rcases hp with (hp | hp) | hp
    · exact hApiece _ (Or.inl rfl) hp
    · rcases hp' with (hp' | hp') | hp'
      · have hpz : p = z (i t') := hAB _ (hiI t') t ⟨hp', hp⟩
        rw [hzi] at hpz
        exact Set.disjoint_left.mp (hBdisj htt') hp (hpz ▸ (hB t').2.1.left_mem)
      · exact Set.disjoint_left.mp (hBdisj htt') hp hp'
      · have hpz : p = z (j t') := hAB _ (hjI t') t ⟨hp', hp⟩
        rw [hzj] at hpz
        exact Set.disjoint_left.mp (hBdisj htt') hp (hpz ▸ (hB t').2.1.right_mem)
    · exact hApiece _ (Or.inr rfl) hp

/-! ## A wall drawn as in Fig. 1 is thinly drawn -/

/-- A drawing made of cells, none a square, is thinly drawn: between two distinct points some
line meets it in finitely many points, by `exists_line_ncard_eq_planeWallDist_cellSet`. -/
theorem isThinPlaneDrawing_cellSet {𝒰 : Set (ℤ × ℤ)} (h𝒰 : ∀ c ∈ 𝒰, ¬ IsSquareCell c) :
    IsThinPlaneDrawing (fig1PlaneEquiv '' cellSet 𝒰) := fun _ _ hst => by
  obtain ⟨L, hL, hfin, -⟩ := exists_line_ncard_eq_planeWallDist_cellSet h𝒰 hst
  exact ⟨L, hL, hfin⟩

/-- Thinness does not see homeomorphisms of the plane: a line from `φ⁻¹ s` to `φ⁻¹ t` meeting
`U` finitely is carried by `φ` to a line from `s` to `t` meeting `φ '' U` finitely. -/
theorem IsThinPlaneDrawing.image_homeomorph {U : Set EuclideanPlane}
    (hU : IsThinPlaneDrawing U) (φ : EuclideanPlane ≃ₜ EuclideanPlane) :
    IsThinPlaneDrawing (φ '' U) := fun s t hst => by
  obtain ⟨L, hL, hfin⟩ := hU (φ.symm s) (φ.symm t) (fun h => hst (φ.symm.injective h))
  refine ⟨φ '' L, ?_, ?_⟩
  · have := isLineWithEnds_image_homeomorph φ hL
    rwa [φ.apply_symm_apply, φ.apply_symm_apply] at this
  · rw [← image_inter φ.injective]
    exact hfin.image φ

/-- **A wall drawn as in Fig. 1 is thinly drawn.** Its point set is the image under a
homeomorphism of the Fig. 1 set, which is made of cells, none a square
(`fig1WallSet_eq_cellSet`, `fig1WallCells_not_square`). -/
theorem DrawnWall.IsFigure1.isThin {W : DrawnWall α β} (hW : W.IsFigure1) :
    IsThinPlaneDrawing W.drawingU := by
  obtain ⟨φ, Γ, hΓ, hU, -⟩ := hW
  rw [hU, hΓ.drawing_U_eq, fig1WallSet_eq_cellSet]
  exact (isThinPlaneDrawing_cellSet (fig1WallCells_not_square _)).image_homeomorph φ

/-! ## The claim in the proof of (7.5) -/

/-- `k` disjoint `H`-paths with ends `s i, t i`, whose ends are mutually at distance at least
`m / 2` (written `m ≤ 2 d`). -/
def FarHPaths (G : Graph α β) (H : DrawnWall α β) (m k : ℕ) (Q : Fin k → Graph α β)
    (s t : Fin k → α) : Prop :=
  (∀ i, IsHPathWithEnds G H.graph (Q i) (s i) (t i)) ∧
  Pairwise (fun i j => Disjoint V(Q i) V(Q j)) ∧
  ∀ x ∈ range s ∪ range t, ∀ y ∈ range s ∪ range t, x ≠ y → m ≤ 2 * H.dist x y

/-- The rays of a star. -/
theorem IsExternalLMStarOver.exists_rays {G : Graph α β} {H : DrawnWall α β} {l m : ℕ}
    {S : Graph α β} {w : α} (hS : IsExternalLMStarOver G H l m S w) :
    ∃ (P : Fin l → Graph α β) (u : Fin l → α), IsRays G H.graph P w u ∧
      (∀ i, V(P i) ⊆ V(S)) ∧ (∀ i j, i ≠ j → m ≤ H.dist (u i) (u j)) := by
  obtain ⟨⟨-, -, -, P, u, hSeq, hP, hdisj, hdist⟩, hw⟩ := hS
  refine ⟨P, u, ⟨fun i => (hP i).1, fun i => (hP i).2.1, fun i => (hP i).2.2.1,
    fun i => (hP i).2.2.2.1, fun i => (hP i).2.2.2.2, hdisj, hw⟩, fun i => ?_, hdist⟩
  rw [hSeq, vertexSet_subgraphSUnion]
  intro x hx
  exact mem_iUnion₂.mpr ⟨P i, ⟨i, rfl⟩, hx⟩

/-- **The claim in the proof of (7.5)** (page 91): "Let $l = 2k^2 - k + 3$. For any $k$ external
$(l, m)$-stars $S_1, \dots, S_k$ over $H$ with distinct centers there are $k$ mutually
vertex-disjoint $H$-paths of $G$, each a subgraph of $S_1 \cup \dots \cup S_k$, with their $2k$
ends mutually at distance $\ge \frac{1}{2}m$." We prove it for every `l ≥ 2k² - k + 3`, and keep
of "each a subgraph of $S_1 \cup \dots \cup S_k$" the part on vertices, which is what the induction
uses. -/
theorem lemma_7_5_claim {G : Graph α β} {H : DrawnWall α β}
    (hthin : IsThinPlaneDrawing H.drawingU) (m : ℕ) :
    ∀ (k l : ℕ), 2 * k ^ 2 - k + 3 ≤ l → ∀ (S : Fin k → Graph α β) (v : Fin k → α),
      (∀ a, IsExternalLMStarOver G H l m (S a) (v a)) → Injective v →
      ∃ (Q : Fin k → Graph α β) (s t : Fin k → α), FarHPaths G H m k Q s t ∧
        ∀ i, V(Q i) ⊆ ⋃ a, V(S a)
  | 0, _, _, _, _, _, _ =>
    ⟨Fin.elim0, Fin.elim0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0,
      by simp⟩, fun i => i.elim0⟩
  | k + 1, l, hl, S, v, hS, hv => by
    classical
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by
      have : 1 ≤ 2 * (k + 1) ^ 2 - (k + 1) + 3 := by omega
      omega⟩
    have hk2 : k + 1 ≤ 2 * (k + 1) ^ 2 := by nlinarith
    have hl' : 2 * k ^ 2 - k + 3 ≤ l' := by
      have : k ≤ 2 * k ^ 2 := by nlinarith
      zify [hk2, this] at hl ⊢
      nlinarith
    have h3 : 3 ≤ l' := by omega
    set w := v (Fin.last k)
    -- the earlier stars, made to avoid the last center
    have hsub : ∀ a : Fin k, ∃ S' : Graph α β, S' ≤ S a.castSucc ∧ w ∉ V(S') ∧
        IsExternalLMStarOver G H l' m S' (v a.castSucc) := fun a =>
      exists_substar_avoiding_vertex h3 (hS a.castSucc)
        (fun h => (Fin.castSucc_lt_last a).ne (hv h).symm)
    choose S' hS'le hwS' hS' using hsub
    obtain ⟨Q, s, t, ⟨hQ, hQdisj, hQfar⟩, hQS⟩ := lemma_7_5_claim hthin m k l' hl' S'
      (fun a => v a.castSucc) hS' (hv.comp (Fin.castSucc_injective _))
    have hwQ : ∀ j, w ∉ V(Q j) := by
      intro j hw
      obtain ⟨a, ha⟩ := mem_iUnion.mp (hQS j hw)
      exact hwS' a ha
    have hQSS : ∀ j, V(Q j) ⊆ ⋃ a, V(S a) := by
      intro j x hx
      obtain ⟨a, ha⟩ := mem_iUnion.mp (hQS j hx)
      exact mem_iUnion.mpr ⟨a.castSucc, (hS'le a).vertexSet_mono ha⟩
    -- the rays of the last star
    obtain ⟨P, u, hR, hPS, hudist⟩ := (hS (Fin.last k)).exists_rays
    have hPSS : ∀ i, V(P i) ⊆ ⋃ a, V(S a) := fun i x hx =>
      mem_iUnion.mpr ⟨Fin.last k, hPS i hx⟩
    let meet : Fin k → Finset (Fin (l' + 1)) := fun j =>
      Finset.univ.filter (fun i => (V(P i) ∩ V(Q j)).Nonempty)
    by_cases hA : ∃ j, 2 * (k + 1) ≤ (meet j).card
    · -- Case A: many rays meet one old path
      obtain ⟨j, hj⟩ := hA
      obtain ⟨R, i, i', hRp, hinj, hRdisj⟩ := exists_hPaths_of_rays_meet hR (hQ j) (hwQ j) (k + 1)
        (meet j) (fun i hi => (Finset.mem_filter.mp hi).2) hj
      refine ⟨R, fun t => u (i t), fun t => u (i' t), ⟨fun t => (hRp t).1, hRdisj, ?_⟩, ?_⟩
      · rintro x hx y hy hxy
        have hidx : ∀ z ∈ range (fun t => u (i t)) ∪ range (fun t => u (i' t)),
            ∃ c : Fin (k + 1) ⊕ Fin (k + 1), z = u (Sum.elim i i' c) := by
          rintro z (⟨t, rfl⟩ | ⟨t, rfl⟩)
          · exact ⟨Sum.inl t, rfl⟩
          · exact ⟨Sum.inr t, rfl⟩
        obtain ⟨c, rfl⟩ := hidx x hx
        obtain ⟨c', rfl⟩ := hidx y hy
        have hne : Sum.elim i i' c ≠ Sum.elim i i' c' := fun h => hxy (by rw [h])
        have := hudist _ _ hne
        omega
      · intro t x hx
        rcases (hRp t).2 hx with (h | h) | h
        · exact hQSS j h
        · exact hPSS _ h
        · exact hPSS _ h
    · -- Case B: two rays miss all old paths and are far from their ends
      push Not at hA
      let ends : Finset α := Finset.univ.image s ∪ Finset.univ.image t
      let close : Finset (Fin (l' + 1)) :=
        Finset.univ.filter (fun i => ∃ x ∈ ends, 2 * H.dist (u i) x < m)
      have hclose : close.card ≤ 2 * k := by
        have hmap : ∀ i ∈ close, ∃ x ∈ ends, 2 * H.dist (u i) x < m := fun i hi =>
          (Finset.mem_filter.mp hi).2
        have : Nonempty α := ⟨w⟩
        choose! f hf hfm using hmap
        have hinj : Set.InjOn f (↑close : Set (Fin (l' + 1))) := by
          intro i hi i' hi' h
          by_contra hne
          have h1 := hfm i hi
          have h2 := hfm i' hi'
          rw [h] at h1
          have h3 := hudist i i' hne
          have h4 := H.dist_triangle hthin (u i) (f i') (u i')
          rw [H.dist_comm (f i') (u i')] at h4
          omega
        have h1 := Finset.card_le_card_of_injOn f (fun i hi => hf i hi) hinj
        have h2 : ends.card ≤ 2 * k := by
          refine (Finset.card_union_le _ _).trans ?_
          have := Finset.card_image_le (s := Finset.univ) (f := s)
          have := Finset.card_image_le (s := Finset.univ) (f := t)
          simp only [Finset.card_univ, Fintype.card_fin] at *
          omega
        omega
      let bad := (Finset.univ.biUnion meet) ∪ close
      have hbad : bad.card ≤ k * (2 * k + 1) + 2 * k := by
        refine (Finset.card_union_le _ _).trans ?_
        have := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin k))) (t := meet)
        have h2 : ∑ j : Fin k, (meet j).card ≤ ∑ _j : Fin k, (2 * k + 1) :=
          Finset.sum_le_sum (fun j _ => by have := hA j; omega)
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
        omega
      have hgood : 2 ≤ (Finset.univ \ bad).card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
          Fintype.card_fin]
        have : 2 * (k + 1) ^ 2 - (k + 1) + 3 = 2 * k ^ 2 + 3 * k + 4 := by
          have : k + 1 ≤ 2 * (k + 1) ^ 2 := hk2
          zify [this]; ring
        rw [this] at hl
        have : k * (2 * k + 1) + 2 * k = 2 * k ^ 2 + 3 * k := by ring
        omega
      obtain ⟨i₁, hi₁, i₂, hi₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ \ bad).card)
      have hgood' : ∀ i ∈ Finset.univ \ bad, (∀ j, Disjoint V(P i) V(Q j)) ∧
          ∀ x ∈ ends, m ≤ 2 * H.dist (u i) x := by
        intro i hi
        have hi' := (Finset.mem_sdiff.mp hi).2
        refine ⟨fun j => ?_, fun x hx => ?_⟩
        · rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
          intro hne
          exact hi' (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
            ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩⟩))
        · by_contra hlt
          exact hi' (Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, x, hx, by omega⟩))
      obtain ⟨hd₁, hf₁⟩ := hgood' i₁ hi₁
      obtain ⟨hd₂, hf₂⟩ := hgood' i₂ hi₂
      -- the new path through the last center
      let R := subgraphUnion G (P i₁) (P i₂)
      have hRV : V(R) = V(P i₁) ∪ V(P i₂) := rfl
      have hRp : IsHPathWithEnds G H.graph R (u i₁) (u i₂) := by
        have hI : V(P i₁) ∩ V(P i₂) = {w} := hR.disj i₁ i₂ hne
        refine ⟨(hS (Fin.last k)).1.wall_le, (hR.path i₁).symm.subgraphUnion (hR.path i₂) hI,
          hR.u_injective.ne hne, hR.mem i₁, hR.mem i₂, ?_, ?_⟩
        · apply Subset.antisymm
          · rintro x ⟨hx | hx, hxH⟩
            · rcases hR.inter i₁ ⟨hx, hxH⟩ with h | h
              · exact absurd (h ▸ hxH) hR.center
              · exact Or.inl h
            · rcases hR.inter i₂ ⟨hx, hxH⟩ with h | h
              · exact absurd (h ▸ hxH) hR.center
              · exact Or.inr h
          · rintro x (rfl | rfl)
            · exact ⟨Or.inl (hR.path i₁).right_mem, hR.mem i₁⟩
            · exact ⟨Or.inr (hR.path i₂).right_mem, hR.mem i₂⟩
        · rw [Set.disjoint_left]
          intro e he heH
          rcases edgeSet_subgraphUnion_subset _ _ _ he with he | he
          · exact Set.disjoint_left.mp (hR.edges i₁) he heH
          · exact Set.disjoint_left.mp (hR.edges i₂) he heH
      have hRQ : ∀ j, Disjoint V(R) V(Q j) := fun j => by
        rw [hRV]; exact Set.disjoint_union_left.mpr ⟨hd₁ j, hd₂ j⟩
      have hends : ∀ x, x ∈ range s ∪ range t → x ∈ ends := by
        rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
        · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
        · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
      refine ⟨Fin.snoc Q R, Fin.snoc s (u i₁), Fin.snoc t (u i₂), ⟨?_, ?_, ?_⟩, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa using hRp
        · simpa using hQ i
      · intro i j hij
        induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last => exact absurd rfl hij
          | cast j => simpa using hRQ j
        | cast i =>
          induction j using Fin.lastCases with
          | last => simpa using (hRQ i).symm
          | cast j => simpa using hQdisj (fun h => hij (by rw [h]))
      · have hmem : ∀ z ∈ range (Fin.snoc s (u i₁) : Fin (k + 1) → α) ∪
            range (Fin.snoc t (u i₂) : Fin (k + 1) → α),
            z ∈ range s ∪ range t ∨ z = u i₁ ∨ z = u i₂ := by
          rintro z (⟨i, rfl⟩ | ⟨i, rfl⟩)
          · induction i using Fin.lastCases with
            | last => simp
            | cast i => simp
          · induction i using Fin.lastCases with
            | last => simp
            | cast i => simp
        intro x hx y hy hxy
        have hfar12 := hudist i₁ i₂ hne
        rcases hmem x hx with hx' | rfl | rfl <;> rcases hmem y hy with hy' | rfl | rfl
        · exact hQfar x hx' y hy' hxy
        · rw [H.dist_comm]; exact hf₁ x (hends x hx')
        · rw [H.dist_comm]; exact hf₂ x (hends x hx')
        · exact hf₁ y (hends y hy')
        · exact absurd rfl hxy
        · omega
        · exact hf₂ y (hends y hy')
        · rw [H.dist_comm]; omega
        · exact absurd rfl hxy
      · intro i
        induction i using Fin.lastCases with
        | last =>
          simp only [Fin.snoc_last]
          rw [hRV]
          exact union_subset (hPSS i₁) (hPSS i₂)
        | cast i => simpa using hQSS i

/-! ## (7.5) from (7.4) -/

/-- The assertion of (7.4) for a fixed `p` and a fixed `r`: in every graph with a wall `H` drawn
as in Fig. 1, `C(p, 2)` disjoint `H`-paths with their ends mutually at distance at least `r`
give a `K_p` model. This is the form of `GM13Theorem74Statement` for one `p`. -/
def Theorem74For (p r : ℕ) : Prop :=
  ∀ (G : Graph α β) (H : DrawnWall α β), H.IsFigure1 → IsWallIn G H.toWall →
    ∀ (P : Fin (p.choose 2) → Graph α β) (s t : Fin (p.choose 2) → α),
      (∀ i, IsHPathWithEnds G H.graph (P i) (s i) (t i)) →
      Pairwise (fun i j => Disjoint V(P i) V(P j)) →
      (∀ i j, i ≠ j →
        r ≤ H.dist (s i) (s j) ∧ r ≤ H.dist (s i) (t j) ∧
        r ≤ H.dist (t i) (s j) ∧ r ≤ H.dist (t i) (t j)) →
      (∀ i, r ≤ H.dist (s i) (t i)) →
      HasGraphModel (GM16.completeGraph p) G

/-- **(7.5) from (7.4)** (page 91): "In particular, the statement holds if $k = \binom{p}{2}$. Let
$l = 2\binom{p}{2}^2 - \binom{p}{2} + 3$, choose $r$ as in (7.4) and let $m = 2r$. Then $l, m$
satisfy the theorem, by (7.4)." So if `r` works in (7.4) for `p`, then `l = 2C(p,2)² - C(p,2) + 3`
and `m = 2r` work in (7.5): `C(p, 2)` external `(l, m)`-stars over `H` with distinct centers give
a `K_p` model. The wall is drawn as in Fig. 1 (`IsFigure1`), which gives the triangle inequality
used in the claim (`DrawnWall.IsFigure1.isThin`). -/
theorem theorem_7_5_of_theorem_7_4 {p r : ℕ} (h74 : Theorem74For (α := α) (β := β) p r)
    (G : Graph α β) (H : DrawnWall α β) (hH : H.IsFigure1) (hHG : IsWallIn G H.toWall)
    (S : Fin (p.choose 2) → Graph α β) (v : Fin (p.choose 2) → α)
    (hS : ∀ a, IsExternalLMStarOver G H (2 * p.choose 2 ^ 2 - p.choose 2 + 3) (2 * r) (S a) (v a))
    (hv : Injective v) :
    HasGraphModel (GM16.completeGraph p) G := by
  obtain ⟨Q, s, t, ⟨hQ, hQdisj, hfar⟩, -⟩ :=
    lemma_7_5_claim hH.isThin (2 * r) (p.choose 2) _ le_rfl S v hS hv
  have hfar' : ∀ x ∈ range s ∪ range t, ∀ y ∈ range s ∪ range t, x ≠ y → r ≤ H.dist x y :=
    fun x hx y hy hxy => by have := hfar x hx y hy hxy; omega
  have hne : ∀ i j, i ≠ j → ∀ x ∈ ({s i, t i} : Set α), ∀ y ∈ ({s j, t j} : Set α), x ≠ y := by
    rintro i j hij x hx y hy rfl
    have hxi : x ∈ V(Q i) := by
      rcases hx with rfl | rfl
      · exact (hQ i).2.1.left_mem
      · exact (hQ i).2.1.right_mem
    have hxj : x ∈ V(Q j) := by
      rcases hy with rfl | rfl
      · exact (hQ j).2.1.left_mem
      · exact (hQ j).2.1.right_mem
    exact Set.disjoint_left.mp (hQdisj hij) hxi hxj
  refine h74 G H hH hHG Q s t hQ hQdisj (fun i j hij => ⟨?_, ?_, ?_, ?_⟩) (fun i => ?_)
  · exact hfar' _ (Or.inl ⟨i, rfl⟩) _ (Or.inl ⟨j, rfl⟩) (hne i j hij _ (Or.inl rfl) _ (Or.inl rfl))
  · exact hfar' _ (Or.inl ⟨i, rfl⟩) _ (Or.inr ⟨j, rfl⟩) (hne i j hij _ (Or.inl rfl) _ (Or.inr rfl))
  · exact hfar' _ (Or.inr ⟨i, rfl⟩) _ (Or.inl ⟨j, rfl⟩) (hne i j hij _ (Or.inr rfl) _ (Or.inl rfl))
  · exact hfar' _ (Or.inr ⟨i, rfl⟩) _ (Or.inr ⟨j, rfl⟩) (hne i j hij _ (Or.inr rfl) _ (Or.inr rfl))
  · exact hfar' _ (Or.inl ⟨i, rfl⟩) _ (Or.inr ⟨i, rfl⟩) (hQ i).2.2.1

end GraphMinor.GM13
