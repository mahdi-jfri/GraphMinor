module

public import GraphMinor.GM03.Defs
public import GraphMinor.GM03.Section2g
public import GraphMinor.GM03.Section2h

/-!
# Graph Minors III, Section 2i: Cyclic Models and Doubling in $N(d, \lambda)$ (for (2.3))

This file proves the cyclic-boundary minor-model framework and parameter-doubling lemmas for
`(2.3)` (page 55) of N. Robertson and P. D. Seymour, *Graph Minors. III. Planar Tree-Width*,
J. Combin. Theory Ser. B **36** (1984), 49–64:
1. `CircuitCycle` and `HasCyclicModel`: cyclic minor models in `graphN d lam` maintaining disjoint
   contiguous spoke arcs along the outermost cylinder circle `0`;
2. `double_graphN_model`, `graphN_minor_mono_lam`, and `iterate_double_cyclic_model`: lifting minor
   models from `graphN d lam` to `graphN d (lam + 1)` while doubling every boundary slot length.
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function Classical
open Graph
open GraphMinor GraphMinor.Surface GraphMinor.GM09

universe u v

/-! ## 1. Cyclic Circuit Enumeration and Circle-`0` Arcs in `graphN d lam` -/

/-- Cyclic enumeration of the `p` vertices (`2 ≤ p`) and `p` edges of a simple circuit `C`. -/
structure CircuitCycle {α : Type u} {β : Type v} (C : Graph α β) (p : ℕ) where
  hp : 2 ≤ p
  u : Fin p → α
  ce : Fin p → β
  u_inj : Injective u
  ce_inj : Injective ce
  vertexSet_eq : V(C) = range u
  edgeSet_eq : E(C) = range ce
  isLink_ce : ∀ t : Fin p, C.IsLink (ce t) (u t) (u (nextSpoke t))

/-- Vertex `(i, 0)` on the outermost circle (`j = 0`) of `graphN d lam`. -/
def circle0Vert (d lam : ℕ) (i : Fin (3 * 2 ^ (lam - 1))) : GraphNVertex d lam :=
  Sum.inr (i, ⟨0, by omega⟩)

/-- Circular edge `Sum.inr (Sum.inl (i, 0))` on circle `0` of `graphN d lam`. -/
def circle0Edge (d lam : ℕ) (i : Fin (3 * 2 ^ (lam - 1))) : GraphNEdge d lam :=
  Sum.inr (Sum.inl (i, ⟨0, by omega⟩))

theorem circle0Vert_inj {d lam : ℕ} : Injective (circle0Vert d lam) := by
  intro i₁ i₂ h
  unfold circle0Vert at h
  injection h with hp
  exact Prod.mk.inj hp |>.1

theorem circle0Edge_inj {d lam : ℕ} : Injective (circle0Edge d lam) := by
  intro i₁ i₂ h
  unfold circle0Edge at h
  injection h with h1
  injection h1 with hp
  exact Prod.mk.inj hp |>.1

theorem graphN_isLink_circle0 {d lam : ℕ} (hd : 1 ≤ d) (i : Fin (3 * 2 ^ (lam - 1))) :
    (graphN d lam).IsLink (circle0Edge d lam i)
      (circle0Vert d lam i) (circle0Vert d lam (nextSpoke i)) :=
  ⟨by omega, Or.inl ⟨rfl, rfl⟩⟩

theorem three_pow_ge_three (lam : ℕ) : 3 ≤ 3 * 2 ^ (lam - 1) := by
  have : 1 ≤ 2 ^ (lam - 1) := Nat.one_le_pow _ _ (by omega)
  omega

/-- Spoke arc on circle `0` of `graphN d lam` assigned to circuit vertex `t : Fin p` given dividers
`0 < b 0 < ... < b (p - 1) < 3 * 2 ^ (lam - 1)`:
- `t = 0` owns `[0, b 0) ∪ [b (p - 1), 3 * 2 ^ (lam - 1))`,
- `t > 0` owns `[b (t - 1), b t)`. -/
def circle0ArcSet (d lam : ℕ) {p : ℕ} (hp : 2 ≤ p) (b : Fin p → ℕ) (t : Fin p) :
    Set (GraphNVertex d lam) :=
  if ht : t.1 = 0 then
    {v | ∃ i : Fin (3 * 2 ^ (lam - 1)),
      (i.1 < b ⟨0, by omega⟩ ∨ b ⟨p - 1, by omega⟩ ≤ i.1) ∧ v = circle0Vert d lam i}
  else
    {v | ∃ i : Fin (3 * 2 ^ (lam - 1)),
      b ⟨t.1 - 1, by omega⟩ ≤ i.1 ∧ i.1 < b t ∧ v = circle0Vert d lam i}

theorem circle0ArcSet_nonempty {d lam : ℕ} {p : ℕ} (hp : 2 ≤ p)
    {b : Fin p → ℕ} (hb_bd : ∀ t : Fin p, 1 ≤ b t ∧ b t < 3 * 2 ^ (lam - 1))
    (hb_mono : StrictMono b) (t : Fin p) :
    (circle0ArcSet d lam hp b t).Nonempty := by
  unfold circle0ArcSet
  have hR := three_pow_ge_three lam
  split_ifs with ht
  · exact ⟨circle0Vert d lam ⟨0, by omega⟩, ⟨0, by omega⟩,
      Or.inl (by dsimp only; exact (hb_bd ⟨0, by omega⟩).1), rfl⟩
  · have hlt : b ⟨t.1 - 1, by omega⟩ < b t :=
      hb_mono (Fin.lt_def.mpr (by dsimp only; omega))
    have hbt := (hb_bd t).2
    exact ⟨circle0Vert d lam ⟨b ⟨t.1 - 1, by omega⟩, by omega⟩,
      ⟨b ⟨t.1 - 1, by omega⟩, by omega⟩, le_rfl, hlt, rfl⟩

theorem circle0ArcSet_disjoint {d lam : ℕ} {p : ℕ} (hp : 2 ≤ p)
    {b : Fin p → ℕ} (hb_mono : StrictMono b) {t₁ t₂ : Fin p} (hne : t₁ ≠ t₂) :
    Disjoint (circle0ArcSet d lam hp b t₁) (circle0ArcSet d lam hp b t₂) := by
  rw [Set.disjoint_left]
  intro v hv₁ hv₂
  have hmono_le : ∀ s₁ s₂ : Fin p, s₁ ≤ s₂ → b s₁ ≤ b s₂ := hb_mono.monotone
  unfold circle0ArcSet at hv₁ hv₂
  split_ifs at hv₁ with ht₁ <;> split_ifs at hv₂ with ht₂
  · exact hne (Fin.ext (ht₁.trans ht₂.symm))
  · obtain ⟨i₁, h₁, rfl⟩ := hv₁
    obtain ⟨i₂, h₂a, h₂b, heq⟩ := hv₂
    have hi := circle0Vert_inj heq; subst hi
    have h0_le : b ⟨0, by omega⟩ ≤ b ⟨t₂.1 - 1, by omega⟩ :=
      hmono_le _ _ (Fin.le_def.mpr (by dsimp only; omega))
    have ht2_le : b t₂ ≤ b ⟨p - 1, by omega⟩ :=
      hmono_le _ _ (Fin.le_def.mpr (by dsimp only; have := t₂.2; omega))
    rcases h₁ with h1l | h1r <;> omega
  · obtain ⟨i₁, h₁a, h₁b, rfl⟩ := hv₁
    obtain ⟨i₂, h₂, heq⟩ := hv₂
    have hi := circle0Vert_inj heq; subst hi
    have h0_le : b ⟨0, by omega⟩ ≤ b ⟨t₁.1 - 1, by omega⟩ :=
      hmono_le _ _ (Fin.le_def.mpr (by dsimp only; omega))
    have ht1_le : b t₁ ≤ b ⟨p - 1, by omega⟩ :=
      hmono_le _ _ (Fin.le_def.mpr (by dsimp only; have := t₁.2; omega))
    rcases h₂ with h2l | h2r <;> omega
  · obtain ⟨i₁, h₁a, h₁b, rfl⟩ := hv₁
    obtain ⟨i₂, h₂a, h₂b, heq⟩ := hv₂
    have hi := circle0Vert_inj heq; subst hi
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlt' : t₁.1 < t₂.1 := Fin.lt_def.mp hlt
      have hle : b t₁ ≤ b ⟨t₂.1 - 1, by omega⟩ :=
        hmono_le _ _ (Fin.le_def.mpr (by dsimp only; omega))
      omega
    · have hgt' : t₂.1 < t₁.1 := Fin.lt_def.mp hgt
      have hle : b t₂ ≤ b ⟨t₁.1 - 1, by omega⟩ :=
        hmono_le _ _ (Fin.le_def.mpr (by dsimp only; omega))
      omega

theorem circle0_divider_endpoints {d lam : ℕ} {p : ℕ} (hp : 2 ≤ p)
    {b : Fin p → ℕ} (hb_bd : ∀ t : Fin p, 1 ≤ b t ∧ b t < 3 * 2 ^ (lam - 1))
    (hb_mono : StrictMono b) (t : Fin p) :
    let iL : Fin (3 * 2 ^ (lam - 1)) := ⟨b t - 1, by have := (hb_bd t).2; omega⟩
    circle0Vert d lam iL ∈ circle0ArcSet d lam hp b t ∧
    circle0Vert d lam (nextSpoke iL) ∈ circle0ArcSet d lam hp b (nextSpoke t) := by
  intro iL
  have hbt1 := (hb_bd t).1
  have hbt2 := (hb_bd t).2
  have hn_eq : nextSpoke iL = ⟨b t, hbt2⟩ := by
    apply Fin.ext
    dsimp only [nextSpoke, iL]
    rw [show b t - 1 + 1 = b t by omega, Nat.mod_eq_of_lt hbt2]
  constructor
  · unfold circle0ArcSet
    split_ifs with ht
    · have ht0 : t = ⟨0, by omega⟩ := Fin.ext (by dsimp only; exact ht)
      exact ⟨iL, Or.inl (by dsimp only [iL]; rw [← ht0]; omega), rfl⟩
    · have hlt : b ⟨t.1 - 1, by omega⟩ < b t :=
        hb_mono (Fin.lt_def.mpr (by dsimp only; omega))
      exact ⟨iL, by dsimp only [iL]; omega, by dsimp only [iL]; omega, rfl⟩
  · rw [hn_eq]
    unfold circle0ArcSet
    by_cases hlast : t.1 + 1 = p
    · have hns0 : (nextSpoke t).1 = 0 := by
        dsimp only [nextSpoke]; rw [hlast, Nat.mod_self]
      simp only [hns0, ↓reduceDIte]
      have hteq : t = ⟨p - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
      exact ⟨⟨b t, hbt2⟩, Or.inr (by dsimp only; rw [← hteq]), rfl⟩
    · have ht_lt : t.1 + 1 < p := by have := t.2; omega
      have hns_val : (nextSpoke t).1 = t.1 + 1 := by
        dsimp only [nextSpoke]; exact Nat.mod_eq_of_lt ht_lt
      have hns_ne : (nextSpoke t).1 ≠ 0 := by omega
      simp only [hns_ne, ↓reduceDIte]
      have hpred : (⟨(nextSpoke t).1 - 1, by omega⟩ : Fin p) = t :=
        Fin.ext (by dsimp only; omega)
      have hlt : b t < b (nextSpoke t) :=
        hb_mono (Fin.lt_def.mpr (by rw [hns_val]; omega))
      exact ⟨⟨b t, hbt2⟩, by dsimp only; rw [hpred], by dsimp only; exact hlt, rfl⟩

/-- Every `circle0ArcSet d lam hp b t` is connected in `(graphN d lam).deleteEdges D` whenever
`D` contains none of the non-divider circle-`0` edges `{circle0Edge d lam i | ∀ s, i.1 ≠ b s - 1}`. -/
theorem circle0ArcSet_connected {d lam : ℕ} (hd : 1 ≤ d) {p : ℕ} (hp : 2 ≤ p)
    {b : Fin p → ℕ} (hb_bd : ∀ t : Fin p, 1 ≤ b t ∧ b t < 3 * 2 ^ (lam - 1))
    (hb_mono : StrictMono b) {S : Set (GraphNVertex d lam)} {D : Set (GraphNEdge d lam)}
    (t : Fin p) (hS_sub : circle0ArcSet d lam hp b t ⊆ S)
    (hD_avoid : ∀ i : Fin (3 * 2 ^ (lam - 1)), (∀ s : Fin p, i.1 ≠ b s - 1) →
      circle0Edge d lam i ∉ D)
    {x y : GraphNVertex d lam}
    (hx : x ∈ circle0ArcSet d lam hp b t) (hy : y ∈ circle0ArcSet d lam hp b t) :
    Relation.ReflTransGen (((graphN d lam).deleteEdges D).induce S).Adj x y := by
  let R := 3 * 2 ^ (lam - 1)
  have hR : 3 ≤ R := three_pow_ge_three lam
  let G_sub := ((graphN d lam).deleteEdges D).induce S
  have hstep_nat : ∀ k : ℕ, (hk : k + 1 < R) →
      (∀ s : Fin p, k ≠ b s - 1) →
      circle0Vert d lam ⟨k, by omega⟩ ∈ circle0ArcSet d lam hp b t →
      circle0Vert d lam ⟨k + 1, hk⟩ ∈ circle0ArcSet d lam hp b t →
      G_sub.Adj (circle0Vert d lam ⟨k, by omega⟩) (circle0Vert d lam ⟨k + 1, hk⟩) := by
    intro k hk hnot_div hk_mem hk1_mem
    let ik : Fin R := ⟨k, by omega⟩
    have hns : nextSpoke ik = ⟨k + 1, hk⟩ := by
      apply Fin.ext; dsimp only [nextSpoke, ik]; exact Nat.mod_eq_of_lt hk
    refine ⟨circle0Edge d lam ik, ?_⟩
    rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
    exact ⟨⟨hns ▸ graphN_isLink_circle0 hd ik, hD_avoid ik hnot_div⟩,
      hS_sub hk_mem, hS_sub hk1_mem⟩
  have hchain : ∀ lo : ℕ, ∀ m : ℕ, (hhi : lo + m < R) →
      (∀ k, lo ≤ k → k < lo + m → ∀ s : Fin p, k ≠ b s - 1) →
      (∀ k, (hk : k ≤ lo + m) → lo ≤ k →
        circle0Vert d lam ⟨k, by omega⟩ ∈ circle0ArcSet d lam hp b t) →
      Relation.ReflTransGen G_sub.Adj
        (circle0Vert d lam ⟨lo, by omega⟩) (circle0Vert d lam ⟨lo + m, hhi⟩) := by
    intro lo m
    induction m with
    | zero => intro _ _ _; simpa using Relation.ReflTransGen.refl
    | succ m ih =>
      intro hhi hnd hmem
      have hprev := ih (by omega)
        (fun k h1 h2 => hnd k h1 (by omega))
        (fun k hk h1 => hmem k (by omega) h1)
      refine Relation.ReflTransGen.tail hprev ?_
      have hstep := hstep_nat (lo + m) (by omega) (hnd (lo + m) (by omega) (by omega))
        (hmem (lo + m) (by omega) (by omega)) (hmem (lo + m + 1) le_rfl (by omega))
      simpa [Nat.add_assoc] using hstep
  have hmono_le : ∀ s₁ s₂ : Fin p, s₁ ≤ s₂ → b s₁ ≤ b s₂ := hb_mono.monotone
  by_cases ht : t.1 = 0
  · have hb0_pos := (hb_bd ⟨0, by omega⟩).1
    have hbp_lt := (hb_bd ⟨p - 1, by omega⟩).2
    have h0_arc : circle0Vert d lam ⟨0, by omega⟩ ∈ circle0ArcSet d lam hp b t := by
      unfold circle0ArcSet; simp only [ht, ↓reduceDIte]
      exact ⟨⟨0, by omega⟩, Or.inl (by dsimp only; omega), rfl⟩
    have hlast_arc : circle0Vert d lam ⟨R - 1, by omega⟩ ∈ circle0ArcSet d lam hp b t := by
      unfold circle0ArcSet; simp only [ht, ↓reduceDIte]
      exact ⟨⟨R - 1, by omega⟩, Or.inr (by dsimp only; omega), rfl⟩
    have hwrap : G_sub.Adj (circle0Vert d lam ⟨R - 1, by omega⟩)
        (circle0Vert d lam ⟨0, by omega⟩) := by
      let ilast : Fin R := ⟨R - 1, by omega⟩
      have hns : nextSpoke ilast = ⟨0, by omega⟩ := by
        apply Fin.ext; dsimp only [nextSpoke, ilast]
        rw [show R - 1 + 1 = R by omega, Nat.mod_self]
      have hnd_last : ∀ s : Fin p, (R - 1) ≠ b s - 1 := by
        intro s
        have := (hb_bd s).1; have := (hb_bd s).2; omega
      refine ⟨circle0Edge d lam ilast, ?_⟩
      rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
      exact ⟨⟨hns ▸ graphN_isLink_circle0 hd ilast, hD_avoid ilast hnd_last⟩,
        hS_sub hlast_arc, hS_sub h0_arc⟩
    have hto_0 : ∀ z ∈ circle0ArcSet d lam hp b t,
        Relation.ReflTransGen G_sub.Adj (circle0Vert d lam ⟨0, by omega⟩) z := by
      intro z hz
      unfold circle0ArcSet at hz
      simp only [ht, ↓reduceDIte] at hz
      obtain ⟨i, hi_cond, rfl⟩ := hz
      rcases hi_cond with hi_lo | hi_hi
      · have hc := hchain 0 i.1 (by have := i.2; dsimp only [R]; omega)
          (fun k _ hk s => by
            have : b ⟨0, by omega⟩ ≤ b s :=
              hmono_le _ _ (Fin.le_def.mpr (by dsimp only; omega))
            omega)
          (fun k hk _ => by
            unfold circle0ArcSet; simp only [ht, ↓reduceDIte]
            exact ⟨⟨k, by have := i.2; omega⟩, Or.inl (by dsimp only; omega), rfl⟩)
        convert hc using 2
        apply Fin.ext; dsimp only; omega
      · have hm : i.1 + (R - 1 - i.1) = R - 1 := by have := i.2; omega
        have hc := hchain i.1 (R - 1 - i.1) (by omega)
          (fun k hk _ s => by
            have : b s ≤ b ⟨p - 1, by omega⟩ :=
              hmono_le _ _ (Fin.le_def.mpr (by dsimp only; have := s.2; omega))
            have := (hb_bd s).1
            omega)
          (fun k hk hlo => by
            unfold circle0ArcSet; simp only [ht, ↓reduceDIte]
            exact ⟨⟨k, by omega⟩, Or.inr (by dsimp only; omega), rfl⟩)
        have hc' : Relation.ReflTransGen G_sub.Adj
            (circle0Vert d lam i) (circle0Vert d lam ⟨R - 1, by omega⟩) := by
          convert hc using 2
          apply Fin.ext; dsimp only; exact hm.symm
        exact Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single hwrap.symm)
          (reflTransGen_symm_of (fun _ _ h => h.symm) hc')
    exact Relation.ReflTransGen.trans
      (reflTransGen_symm_of (fun _ _ h => h.symm) (hto_0 x hx)) (hto_0 y hy)
  · let lo := b ⟨t.1 - 1, by omega⟩
    have hbt_lt := (hb_bd t).2
    have hlo_lt : lo < b t := hb_mono (Fin.lt_def.mpr (by dsimp only; omega))
    have hto_lo : ∀ z ∈ circle0ArcSet d lam hp b t,
        Relation.ReflTransGen G_sub.Adj (circle0Vert d lam ⟨lo, by omega⟩) z := by
      intro z hz
      unfold circle0ArcSet at hz
      simp only [ht, ↓reduceDIte] at hz
      obtain ⟨i, hi_lo, hi_hi, rfl⟩ := hz
      have hc := hchain lo (i.1 - lo) (by omega)
        (fun k hk1 hk2 s => by
          rcases lt_or_ge s.1 t.1 with hslt | hsge
          · have : b s ≤ lo :=
              hmono_le _ _ (Fin.le_def.mpr (by dsimp only; omega))
            have := (hb_bd s).1; omega
          · have : b t ≤ b s :=
              hmono_le _ _ (Fin.le_def.mpr hsge)
            omega)
        (fun k _ hk1 => by
          unfold circle0ArcSet; simp only [ht, ↓reduceDIte]
          exact ⟨⟨k, by omega⟩, by dsimp only; exact hk1, by dsimp only; omega, rfl⟩)
      convert hc using 2
      apply Fin.ext; dsimp only; omega
    exact Relation.ReflTransGen.trans
      (reflTransGen_symm_of (fun _ _ h => h.symm) (hto_lo x hx)) (hto_lo y hy)

/-- Divider-separation condition from `exists_monotone_dividers_and_spokes` places spoke `spk r`
inside `circle0ArcSet d lam hp b ⟨(f r).1 % p, _⟩`. -/
theorem mem_circle0ArcSet_of_sep {d lam : ℕ} {p : ℕ} (hp : 2 ≤ p)
    {b : Fin p → ℕ} {k : ℕ} (hk_lt : k < 3 * 2 ^ (lam - 1)) (fv : Fin (p + 1))
    (hsep : ∀ t : Fin p, (fv.1 ≤ t.1 → k < b t) ∧ (t.1 < fv.1 → b t < k)) :
    circle0Vert d lam ⟨k, hk_lt⟩ ∈
      circle0ArcSet d lam hp b ⟨fv.1 % p, Nat.mod_lt _ (by omega)⟩ := by
  unfold circle0ArcSet
  by_cases hfv0 : fv.1 = 0
  · have hmod0 : fv.1 % p = 0 := by rw [hfv0, Nat.zero_mod]
    simp only [hmod0, ↓reduceDIte]
    exact ⟨⟨k, hk_lt⟩, Or.inl ((hsep ⟨0, by omega⟩).1 (by dsimp only; omega)), rfl⟩
  · by_cases hfvp : fv.1 = p
    · have hmod0 : fv.1 % p = 0 := by rw [hfvp, Nat.mod_self]
      simp only [hmod0, ↓reduceDIte]
      have hgt := (hsep ⟨p - 1, by omega⟩).2 (by dsimp only; omega)
      exact ⟨⟨k, hk_lt⟩, Or.inr (le_of_lt hgt), rfl⟩
    · have hlt_p : fv.1 < p := by have := fv.2; omega
      have hmod : fv.1 % p = fv.1 := Nat.mod_eq_of_lt hlt_p
      simp only [hmod, hfv0, ↓reduceDIte]
      have hlo := (hsep ⟨fv.1 - 1, by omega⟩).2 (by dsimp only; omega)
      have hhi := (hsep ⟨fv.1, hlt_p⟩).1 le_rfl
      exact ⟨⟨k, hk_lt⟩, le_of_lt hlo, hhi, rfl⟩

/-- Cyclic minor-model invariant for `G₀` in `graphN d lam` (`1 ≤ d`, `1 ≤ lam`) with outermost
circuit `C₀ ≤ G₀` enumerated by `cyc : CircuitCycle C₀ p`. -/
def HasCyclicModel {α : Type u} {β : Type v}
    (G₀ C₀ : Graph α β) {p : ℕ} (cyc : CircuitCycle C₀ p) (d lam : ℕ) : Prop :=
  1 ≤ d ∧ 1 ≤ lam ∧ C₀ ≤ G₀ ∧
  ∃ (ηv : α → Set (GraphNVertex d lam)) (ηe : β → GraphNEdge d lam) (b : Fin p → ℕ),
    IsMinorModel G₀ (graphN d lam) ηv ηe ∧
    (∀ t : Fin p, 1 ≤ b t ∧ b t < 3 * 2 ^ (lam - 1)) ∧
    StrictMono b ∧
    ∀ t : Fin p, circle0ArcSet d lam cyc.hp b t ⊆ ηv (cyc.u t)

/-! ## 2. Doubling `graphN d lam` to `graphN d (lam + 1)` and Monotonicity in `lam` -/

/-- Embed internal vertices of `Y_lam` (`1 ≤ lam`) into the top `lam` levels of `Y_{lam + 1}`. -/
def castTreeYInternal {lam : ℕ} (hlam : 1 ≤ lam) : TreeYInternal lam → TreeYInternal (lam + 1)
  | none => none
  | some (br, m) => some (br, ⟨m.1, by
      have h2 : 2 ^ ((lam + 1) - 1) = 2 * 2 ^ (lam - 1) := by
        rw [Nat.add_sub_cancel, ← pow_succ', show lam - 1 + 1 = lam by omega]
      have := m.2; omega⟩)

/-- Bottom-level internal vertex of `Y_{lam + 1}` above leaf `i` of `Y_lam` (`1 ≤ lam`). -/
def botTreeYInternal {lam : ℕ} (hlam : 1 ≤ lam) (i : Fin (3 * 2 ^ (lam - 1))) :
    TreeYInternal (lam + 1) :=
  have hpow : 1 ≤ 2 ^ (lam - 1) := Nat.one_le_pow _ _ (by omega)
  have h2 : 2 ^ ((lam + 1) - 1) = 2 * 2 ^ (lam - 1) := by
    rw [Nat.add_sub_cancel, ← pow_succ', show lam - 1 + 1 = lam by omega]
  some (⟨i.1 / 2 ^ (lam - 1), Nat.div_lt_of_lt_mul (by linarith [i.2])⟩,
    ⟨2 ^ (lam - 1) + i.1 % 2 ^ (lam - 1) - 1, by
      have := Nat.mod_lt i.1 (by positivity : 0 < 2 ^ (lam - 1))
      omega⟩)

/-- Doubled spoke `2 * i + δ` (`δ : Fin 2`) in `graphN d (lam + 1)` (`1 ≤ lam`). -/
def dblSpoke {lam : ℕ} (hlam : 1 ≤ lam) (i : Fin (3 * 2 ^ (lam - 1))) (δ : Fin 2) :
    Fin (3 * 2 ^ ((lam + 1) - 1)) :=
  ⟨2 * i.1 + δ.1, by
    have h2 : 2 ^ ((lam + 1) - 1) = 2 * 2 ^ (lam - 1) := by
      rw [Nat.add_sub_cancel, ← pow_succ', show lam - 1 + 1 = lam by omega]
    have := i.2; have := δ.2; omega⟩

theorem castTreeYInternal_inj {lam : ℕ} (hlam : 1 ≤ lam) :
    Injective (castTreeYInternal hlam) := by
  rintro (_ | ⟨b₁, m₁⟩) (_ | ⟨b₂, m₂⟩) h
  · rfl
  · cases h
  · cases h
  · unfold castTreeYInternal at h
    injection h with hp
    obtain ⟨rfl, hm⟩ := Prod.mk.inj hp
    congr 2
    exact Fin.ext (Fin.mk.inj hm)

theorem botTreeYInternal_inj {lam : ℕ} (hlam : 1 ≤ lam) :
    Injective (botTreeYInternal hlam) := by
  intro i₁ i₂ h
  unfold botTreeYInternal at h
  injection h with hp
  obtain ⟨hb, hm⟩ := Prod.mk.inj hp
  have hb' : i₁.1 / 2 ^ (lam - 1) = i₂.1 / 2 ^ (lam - 1) := Fin.mk.inj hb
  have hm' : 2 ^ (lam - 1) + i₁.1 % 2 ^ (lam - 1) - 1 =
      2 ^ (lam - 1) + i₂.1 % 2 ^ (lam - 1) - 1 := Fin.mk.inj hm
  have hpos : 1 ≤ 2 ^ (lam - 1) := Nat.one_le_pow _ _ (by omega)
  have hmod : i₁.1 % 2 ^ (lam - 1) = i₂.1 % 2 ^ (lam - 1) := by omega
  ext
  have hd1 := (Nat.div_add_mod i₁.1 (2 ^ (lam - 1))).symm
  have hd2 := (Nat.div_add_mod i₂.1 (2 ^ (lam - 1))).symm
  rw [hd1, hd2, hb', hmod]

theorem castTreeYInternal_ne_botTreeYInternal {lam : ℕ} (hlam : 1 ≤ lam)
    (t : TreeYInternal lam) (i : Fin (3 * 2 ^ (lam - 1))) :
    castTreeYInternal hlam t ≠ botTreeYInternal hlam i := by
  cases t with
  | none => intro h; cases h
  | some p =>
    intro h
    unfold castTreeYInternal botTreeYInternal at h
    injection h with hp
    have hm := Fin.mk.inj (Prod.mk.inj hp).2
    have := p.2.2
    omega

theorem botTreeYInternal_ne_none {lam : ℕ} (hlam : 1 ≤ lam) (i : Fin (3 * 2 ^ (lam - 1))) :
    botTreeYInternal hlam i ≠ none := by
  unfold botTreeYInternal; exact Option.some_ne_none _

theorem treeYInternalParent_cast {lam : ℕ} (hlam : 1 ≤ lam) (t : TreeYInternal lam) :
    treeYInternalParent (castTreeYInternal hlam t) =
      castTreeYInternal hlam (treeYInternalParent t) := by
  cases t with
  | none => rfl
  | some p =>
    rcases p with ⟨br, m⟩
    unfold castTreeYInternal treeYInternalParent
    dsimp only
    split_ifs <;> rfl

theorem treeYInternalParent_bot {lam : ℕ} (hlam : 1 ≤ lam) (i : Fin (3 * 2 ^ (lam - 1))) :
    treeYInternalParent (botTreeYInternal hlam i) =
      castTreeYInternal hlam (treeYLeafParent lam i) := by
  by_cases h1 : lam ≤ 1
  · have hlam1 : lam = 1 := by omega
    subst hlam1
    unfold botTreeYInternal treeYInternalParent treeYLeafParent castTreeYInternal
    simp [Nat.mod_one]
  · have hpow2 : 2 ≤ 2 ^ (lam - 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (lam - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 2 ^ (lam - 1) = 2 * 2 ^ (lam - 2) := by
      rw [← pow_succ', show lam - 2 + 1 = lam - 1 by omega]
    have hne0 : 2 ^ (lam - 1) + i.1 % 2 ^ (lam - 1) - 1 ≠ 0 := by omega
    unfold botTreeYInternal treeYInternalParent treeYLeafParent castTreeYInternal
    simp only [hne0, h1, ↓reduceDIte]
    congr 1; ext
    · rfl
    · dsimp only
      have hsimp : 2 ^ (lam - 1) + i.1 % 2 ^ (lam - 1) - 1 + 1 =
          (i.1 % 2 ^ (lam - 1)) + 2 ^ (lam - 2) * 2 := by omega
      rw [hsimp, Nat.add_mul_div_right _ _ (by omega)]
      omega

theorem treeYLeafParent_dblSpoke {lam : ℕ} (hlam : 1 ≤ lam)
    (i : Fin (3 * 2 ^ (lam - 1))) (δ : Fin 2) :
    treeYLeafParent (lam + 1) (dblSpoke hlam i δ) = botTreeYInternal hlam i := by
  have hnot1 : ¬ lam + 1 ≤ 1 := by omega
  let H := 2 ^ (lam - 1)
  have hH_pos : 0 < H := by positivity
  have h2H : 2 ^ ((lam + 1) - 1) = 2 * H := by
    dsimp only [H]
    rw [Nat.add_sub_cancel, ← pow_succ', show lam - 1 + 1 = lam by omega]
  have hsub2 : (lam + 1) - 2 = lam - 1 := by omega
  have hmod_lt : 2 * (i.1 % H) + δ.1 < 2 * H := by
    have := Nat.mod_lt i.1 hH_pos; have := δ.2; omega
  have hdecomp : 2 * i.1 + δ.1 = (2 * (i.1 % H) + δ.1) + (2 * H) * (i.1 / H) := by
    have := (Nat.div_add_mod i.1 H).symm; have := δ.2; linarith
  unfold treeYLeafParent dblSpoke botTreeYInternal
  simp only [hnot1, ↓reduceDIte]
  congr 1; ext
  · dsimp only
    rw [h2H, hdecomp, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hmod_lt,
      Nat.zero_add]
  · dsimp only
    rw [h2H, hsub2, hdecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmod_lt]
    have hdiv2 : (2 * (i.1 % H) + δ.1) / 2 = i.1 % H := by
      have := δ.2; omega
    rw [hdiv2]

theorem graphN_not_isLoopAt {d lam : ℕ} (_hlam : 1 ≤ lam) :
    ∀ e ∈ E(graphN d lam), ∀ u, ¬ (graphN d lam).IsLoopAt e u := by
  intro e _ u hl
  change (graphN d lam).IsLink e u u at hl
  rcases e with (t | i) | (p | p)
  · obtain ⟨ht_ne, ⟨rfl, heq⟩ | ⟨rfl, heq⟩⟩ := hl <;>
    · injection heq with hp
      cases t with
      | none => exact ht_ne rfl
      | some bm =>
        rcases bm with ⟨br, m⟩
        have hval := congrArg (fun o : TreeYInternal lam =>
          match o with | none => 0 | some (_, x) => x.1 + 1) hp
        unfold treeYInternalParent at hval
        dsimp only at hval
        split_ifs at hval
        dsimp only at hval
        omega
  · rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases h1.symm.trans h2
  · obtain ⟨_, ⟨rfl, heq⟩ | ⟨rfl, heq⟩⟩ := hl <;>
    · injection heq with hp
      have h1 : p.1 = nextSpoke p.1 := (Prod.mk.inj hp).1
      have hval : p.1.1 = (p.1.1 + 1) % (3 * 2 ^ (lam - 1)) := congrArg Fin.val h1
      have hR := three_pow_ge_three lam
      have hp_lt := p.1.2
      by_cases hlast : p.1.1 + 1 = 3 * 2 ^ (lam - 1)
      · rw [hlast, Nat.mod_self] at hval; omega
      · rw [Nat.mod_eq_of_lt (by omega)] at hval; omega
  · rcases p with ⟨i, j⟩
    obtain ⟨_, hs, ⟨rfl, heq⟩ | ⟨rfl, heq⟩⟩ := hl <;>
    · injection heq with hp
      have h2 : j.1 = j.1 + 1 := congrArg Fin.val (Prod.mk.inj hp).2
      omega

/-- Lift any minor model of a loopless graph `G₀` in `graphN d lam` (`1 ≤ d`, `1 ≤ lam`) to a
minor model in `graphN d (lam + 1)` that maps each spoke `i` on every circle `j` to the pair of
spokes `{2 * i, 2 * i + 1}`. -/
theorem double_graphN_model {α : Type u} {β : Type v}
    {G₀ : Graph α β} (hNoLoop : ∀ e ∈ E(G₀), ∀ u, ¬ G₀.IsLoopAt e u)
    {d lam : ℕ} (hd : 1 ≤ d) (hlam : 1 ≤ lam)
    {ηv : α → Set (GraphNVertex d lam)} {ηe : β → GraphNEdge d lam}
    (hm : IsMinorModel G₀ (graphN d lam) ηv ηe) :
    ∃ (ηv' : α → Set (GraphNVertex d (lam + 1))) (ηe' : β → GraphNEdge d (lam + 1)),
      IsMinorModel G₀ (graphN d (lam + 1)) ηv' ηe' ∧
      ∀ (u : α) (i' : Fin (3 * 2 ^ ((lam + 1) - 1))) (j : Fin (max d 1)),
        (Sum.inr (i', j) ∈ ηv' u ↔
          Sum.inr (⟨i'.1 / 2, by
            have h2 : 2 ^ ((lam + 1) - 1) = 2 * 2 ^ (lam - 1) := by
              rw [Nat.add_sub_cancel, ← pow_succ', show lam - 1 + 1 = lam by omega]
            have := i'.2; omega⟩, j) ∈ ηv u) := by
  have h2pow : 2 ^ ((lam + 1) - 1) = 2 * 2 ^ (lam - 1) := by
    rw [Nat.add_sub_cancel, ← pow_succ', show lam - 1 + 1 = lam by omega]
  let cIdx : Fin (max d 1) := ⟨max d 1 - 1, by omega⟩
  let halfSpoke : Fin (3 * 2 ^ ((lam + 1) - 1)) → Fin (3 * 2 ^ (lam - 1)) :=
    fun i' => ⟨i'.1 / 2, by have := i'.2; omega⟩
  let ηv' : α → Set (GraphNVertex d (lam + 1)) := fun u =>
    {z | match z with
      | Sum.inl t' =>
        (∃ t : TreeYInternal lam, Sum.inl t ∈ ηv u ∧ t' = castTreeYInternal hlam t) ∨
        (∃ i : Fin (3 * 2 ^ (lam - 1)), Sum.inr (i, cIdx) ∈ ηv u ∧ t' = botTreeYInternal hlam i)
      | Sum.inr (i', j) => Sum.inr (halfSpoke i', j) ∈ ηv u}
  let mapEdge : GraphNEdge d lam → GraphNEdge d (lam + 1)
    | Sum.inl (Sum.inl t) => Sum.inl (Sum.inl (castTreeYInternal hlam t))
    | Sum.inl (Sum.inr i) => Sum.inl (Sum.inl (botTreeYInternal hlam i))
    | Sum.inr (Sum.inl (i, j)) => Sum.inr (Sum.inl (dblSpoke hlam i 1, j))
    | Sum.inr (Sum.inr (i, j)) => Sum.inr (Sum.inr (dblSpoke hlam i 0, j))
  let ηe' : β → GraphNEdge d (lam + 1) := fun e => mapEdge (ηe e)
  have hmapEdge_inj : Injective mapEdge := by
    intro e₁ e₂ heq
    rcases e₁ with (t₁ | i₁) | (⟨i₁, j₁⟩ | ⟨i₁, j₁⟩) <;>
      rcases e₂ with (t₂ | i₂) | (⟨i₂, j₂⟩ | ⟨i₂, j₂⟩) <;>
      dsimp only [mapEdge] at heq
    · injection heq with h1; injection h1 with h2
      rw [castTreeYInternal_inj hlam h2]
    · injection heq with h1; injection h1 with h2
      exact (castTreeYInternal_ne_botTreeYInternal hlam t₁ i₂ h2).elim
    · cases heq
    · cases heq
    · injection heq with h1; injection h1 with h2
      exact (castTreeYInternal_ne_botTreeYInternal hlam t₂ i₁ h2.symm).elim
    · injection heq with h1; injection h1 with h2
      rw [botTreeYInternal_inj hlam h2]
    · cases heq
    · cases heq
    · cases heq
    · cases heq
    · injection heq with h1; injection h1 with hp
      obtain ⟨hspk, rfl⟩ := Prod.mk.inj hp
      have hv : 2 * i₁.1 + 1 = 2 * i₂.1 + 1 := congrArg Fin.val hspk
      exact congrArg (fun x => Sum.inr (Sum.inl (x, j₁))) (Fin.ext (by omega))
    · cases heq
    · cases heq
    · cases heq
    · cases heq
    · injection heq with h1; injection h1 with hp
      obtain ⟨hspk, rfl⟩ := Prod.mk.inj hp
      have hv : 2 * i₁.1 + 0 = 2 * i₂.1 + 0 := congrArg Fin.val hspk
      exact congrArg (fun x => Sum.inr (Sum.inr (x, j₁))) (Fin.ext (by omega))
  have hhalf_dbl : ∀ (i : Fin (3 * 2 ^ (lam - 1))) (δ : Fin 2),
      halfSpoke (dblSpoke hlam i δ) = i := by
    intro i δ; apply Fin.ext; dsimp only [halfSpoke, dblSpoke]; have := δ.2; omega
  have hns_dbl0 : ∀ i : Fin (3 * 2 ^ (lam - 1)),
      nextSpoke (dblSpoke hlam i 0) = dblSpoke hlam i 1 := by
    intro i; apply Fin.ext; dsimp only [nextSpoke, dblSpoke]
    have hlt : 2 * i.1 + 0 + 1 < 3 * 2 ^ ((lam + 1) - 1) := by have := i.2; omega
    exact Nat.mod_eq_of_lt hlt
  have hns_dbl1 : ∀ i : Fin (3 * 2 ^ (lam - 1)),
      nextSpoke (dblSpoke hlam i 1) = dblSpoke hlam (nextSpoke i) 0 := by
    intro i; apply Fin.ext; dsimp only [nextSpoke, dblSpoke]
    have hi_lt := i.2
    by_cases hlast : i.1 + 1 = 3 * 2 ^ (lam - 1)
    · have h1 : 2 * i.1 + 1 + 1 = 3 * 2 ^ ((lam + 1) - 1) := by omega
      change (2 * i.1 + 1 + 1) % _ = 2 * ((i.1 + 1) % _) + 0
      rw [h1, hlast, Nat.mod_self, Nat.mod_self]
    · have hlt1 : i.1 + 1 < 3 * 2 ^ (lam - 1) := by omega
      have hlt2 : 2 * i.1 + 1 + 1 < 3 * 2 ^ ((lam + 1) - 1) := by omega
      change (2 * i.1 + 1 + 1) % _ = 2 * ((i.1 + 1) % _) + 0
      rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2]; omega
  have hlink_map : ∀ {f : GraphNEdge d lam} {x y : GraphNVertex d lam},
      (graphN d lam).IsLink f x y →
      ∃ x' y' : GraphNVertex d (lam + 1),
        (∀ u, x ∈ ηv u → x' ∈ ηv' u) ∧
        (∀ u, y ∈ ηv u → y' ∈ ηv' u) ∧
        (graphN d (lam + 1)).IsLink (mapEdge f) x' y' := by
    intro f x y hlf
    rcases f with (t | i) | (⟨i, j⟩ | ⟨i, j⟩)
    · obtain ⟨ht_ne, hxy⟩ := hlf
      have ht'_ne : castTreeYInternal hlam t ≠ none := by
        cases t with
        | none => exact (ht_ne rfl).elim
        | some _ => exact Option.some_ne_none _
      have hl' : (graphN d (lam + 1)).IsLink (mapEdge (Sum.inl (Sum.inl t)))
          (Sum.inl (castTreeYInternal hlam t))
          (Sum.inl (castTreeYInternal hlam (treeYInternalParent t))) :=
        ⟨ht'_ne, Or.inl ⟨rfl, by rw [treeYInternalParent_cast]⟩⟩
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, _, fun u h => Or.inl ⟨t, h, rfl⟩,
          fun u h => Or.inl ⟨treeYInternalParent t, h, rfl⟩, hl'⟩
      · exact ⟨_, _, fun u h => Or.inl ⟨treeYInternalParent t, h, rfl⟩,
          fun u h => Or.inl ⟨t, h, rfl⟩, hl'.symm⟩
    · have hl' : (graphN d (lam + 1)).IsLink (mapEdge (Sum.inl (Sum.inr i)))
          (Sum.inl (castTreeYInternal hlam (treeYLeafParent lam i)))
          (Sum.inl (botTreeYInternal hlam i)) :=
        ⟨botTreeYInternal_ne_none hlam i,
          Or.inr ⟨rfl, congrArg Sum.inl (treeYInternalParent_bot hlam i).symm⟩⟩
      rcases hlf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, _, fun u h => Or.inl ⟨_, h, rfl⟩, fun u h => Or.inr ⟨i, h, rfl⟩, hl'⟩
      · exact ⟨_, _, fun u h => Or.inr ⟨i, h, rfl⟩, fun u h => Or.inl ⟨_, h, rfl⟩, hl'.symm⟩
    · obtain ⟨hd0, hxy⟩ := hlf
      have hl' : (graphN d (lam + 1)).IsLink (mapEdge (Sum.inr (Sum.inl (i, j))))
          (Sum.inr (dblSpoke hlam i 1, j)) (Sum.inr (dblSpoke hlam (nextSpoke i) 0, j)) :=
        ⟨hd0, Or.inl ⟨rfl, by rw [hns_dbl1]⟩⟩
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, _,
          fun u h => show Sum.inr (halfSpoke (dblSpoke hlam i 1), j) ∈ ηv u by rwa [hhalf_dbl],
          fun u h => show Sum.inr (halfSpoke (dblSpoke hlam (nextSpoke i) 0), j) ∈ ηv u by
            rwa [hhalf_dbl],
          hl'⟩
      · exact ⟨_, _,
          fun u h => show Sum.inr (halfSpoke (dblSpoke hlam (nextSpoke i) 0), j) ∈ ηv u by
            rwa [hhalf_dbl],
          fun u h => show Sum.inr (halfSpoke (dblSpoke hlam i 1), j) ∈ ηv u by rwa [hhalf_dbl],
          hl'.symm⟩
    · obtain ⟨hd0, hs, hxy⟩ := hlf
      have hl' : (graphN d (lam + 1)).IsLink (mapEdge (Sum.inr (Sum.inr (i, j))))
          (Sum.inr (dblSpoke hlam i 0, j)) (Sum.inr (dblSpoke hlam i 0, ⟨j.1 + 1, hs⟩)) :=
        ⟨hd0, hs, Or.inl ⟨rfl, rfl⟩⟩
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, _,
          fun u h => show Sum.inr (halfSpoke (dblSpoke hlam i 0), j) ∈ ηv u by rwa [hhalf_dbl],
          fun u h => show Sum.inr (halfSpoke (dblSpoke hlam i 0), ⟨j.1 + 1, hs⟩) ∈ ηv u by
            rwa [hhalf_dbl],
          hl'⟩
      · exact ⟨_, _,
          fun u h => show Sum.inr (halfSpoke (dblSpoke hlam i 0), ⟨j.1 + 1, hs⟩) ∈ ηv u by
            rwa [hhalf_dbl],
          fun u h => show Sum.inr (halfSpoke (dblSpoke hlam i 0), j) ∈ ηv u by rwa [hhalf_dbl],
          hl'.symm⟩
  refine ⟨ηv', ηe', isMinorModel_of_loopless_link hNoLoop
    (fun v hv => ?_)
    (fun _ _ => subset_univ _)
    (fun v₁ hv₁ v₂ hv₂ hne => ?_)
    (fun e₁ he₁ e₂ he₂ heq => hm.edge_injOn he₁ he₂ (hmapEdge_inj heq))
    (fun e u v hl => ?_)
    (fun u hu x' hx' y' hy' => ?_),
    fun _ _ _ => Iff.rfl⟩
  · obtain ⟨z, hz⟩ := hm.vertex_nonempty v hv
    rcases z with t | ⟨i, j⟩
    · exact ⟨Sum.inl (castTreeYInternal hlam t), Or.inl ⟨t, hz, rfl⟩⟩
    · exact ⟨Sum.inr (dblSpoke hlam i 0, j),
        show Sum.inr (halfSpoke (dblSpoke hlam i 0), j) ∈ ηv v by rwa [hhalf_dbl]⟩
  · rw [Set.disjoint_left]
    intro z hz₁ hz₂
    have hdisj := Set.disjoint_left.mp (hm.vertex_disjoint v₁ hv₁ v₂ hv₂ hne)
    rcases z with t' | ⟨i', j⟩
    · rcases hz₁ with ⟨t₁, ht₁, rfl⟩ | ⟨i₁, hi₁, rfl⟩ <;>
        rcases hz₂ with ⟨t₂, ht₂, heq⟩ | ⟨i₂, hi₂, heq⟩
      · exact hdisj ht₁ ((castTreeYInternal_inj hlam heq) ▸ ht₂)
      · exact castTreeYInternal_ne_botTreeYInternal hlam t₁ i₂ heq
      · exact castTreeYInternal_ne_botTreeYInternal hlam t₂ i₁ heq.symm
      · exact hdisj hi₁ ((botTreeYInternal_inj hlam heq) ▸ hi₂)
    · exact hdisj hz₁ hz₂
  · have huv : u ≠ v := fun h => hNoLoop e hl.edge_mem u (h ▸ hl)
    obtain ⟨x, hxu, y, hyv, hlf⟩ := exists_isLink_of_isMinorModel hm hl huv
    obtain ⟨x', y', hx', hy', hl'⟩ := hlink_map hlf
    exact ⟨x', hx' u hxu, y', hy' v hyv, hl'⟩
  · let Gu := (((graphN d (lam + 1)).deleteEdges (ηe' '' E(G₀))).induce (ηv' u))
    let rep : GraphNVertex d lam → GraphNVertex d (lam + 1)
      | Sum.inl t => Sum.inl (castTreeYInternal hlam t)
      | Sum.inr (i, j) => Sum.inr (dblSpoke hlam i 0, j)
    -- Even circular edge `(2*i, j) -- (2*i+1, j)` is never in `range mapEdge`
    have heven_adj : ∀ (i : Fin (3 * 2 ^ (lam - 1))) (j : Fin (max d 1)),
        Sum.inr (i, j) ∈ ηv u →
        Gu.Adj (Sum.inr (dblSpoke hlam i 0, j)) (Sum.inr (dblSpoke hlam i 1, j)) := by
      intro i j hij
      refine ⟨Sum.inr (Sum.inl (dblSpoke hlam i 0, j)), ?_⟩
      rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
      refine ⟨⟨⟨by omega, Or.inl ⟨rfl, by rw [hns_dbl0]⟩⟩, ?_⟩,
        show Sum.inr (halfSpoke (dblSpoke hlam i 0), j) ∈ ηv u by rwa [hhalf_dbl],
        show Sum.inr (halfSpoke (dblSpoke hlam i 1), j) ∈ ηv u by rwa [hhalf_dbl]⟩
      rintro ⟨e, _, heq⟩
      change mapEdge (ηe e) = _ at heq
      generalize ηe e = f₀ at heq
      rcases f₀ with (t | i₀) | (⟨i₀, j₀⟩ | ⟨i₀, j₀⟩)
      · cases heq
      · cases heq
      · injection heq with h1; injection h1 with hp
        have hv : 2 * i₀.1 + 1 = 2 * i.1 + 0 := congrArg Fin.val (Prod.mk.inj hp).1
        omega
      · cases heq
    -- Leaf edge `Sum.inl (Sum.inr (dblSpoke i 0))` is never in `range mapEdge`
    have hbot_adj : ∀ i : Fin (3 * 2 ^ (lam - 1)),
        Sum.inr (i, cIdx) ∈ ηv u →
        Gu.Adj (Sum.inr (dblSpoke hlam i 0, cIdx)) (Sum.inl (botTreeYInternal hlam i)) := by
      intro i hic
      refine ⟨Sum.inl (Sum.inr (dblSpoke hlam i 0)), ?_⟩
      rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
      refine ⟨⟨Or.inr ⟨congrArg Sum.inl (treeYLeafParent_dblSpoke hlam i 0).symm, rfl⟩, ?_⟩,
        show Sum.inr (halfSpoke (dblSpoke hlam i 0), cIdx) ∈ ηv u by rwa [hhalf_dbl],
        Or.inr ⟨i, hic, rfl⟩⟩
      rintro ⟨e, _, heq⟩
      change mapEdge (ηe e) = _ at heq
      generalize ηe e = f₀ at heq
      rcases f₀ with (t | i₀) | (⟨i₀, j₀⟩ | ⟨i₀, j₀⟩) <;> cases heq
    have hto_rep : ∀ w' ∈ ηv' u, ∃ z ∈ ηv u, Relation.ReflTransGen Gu.Adj (rep z) w' := by
      rintro (t' | ⟨i', j⟩) hw'
      · rcases hw' with ⟨t, ht, rfl⟩ | ⟨i, hic, rfl⟩
        · exact ⟨Sum.inl t, ht, Relation.ReflTransGen.refl⟩
        · exact ⟨Sum.inr (i, cIdx), hic, Relation.ReflTransGen.single (hbot_adj i hic)⟩
      · have hij : Sum.inr (halfSpoke i', j) ∈ ηv u := hw'
        by_cases hpar : i'.1 % 2 = 0
        · have hi'_eq : i' = dblSpoke hlam (halfSpoke i') 0 := by
            apply Fin.ext; dsimp only [dblSpoke, halfSpoke]; omega
          rw [hi'_eq]
          exact ⟨Sum.inr (halfSpoke i', j), hij, Relation.ReflTransGen.refl⟩
        · have hi'_eq : i' = dblSpoke hlam (halfSpoke i') 1 := by
            apply Fin.ext; dsimp only [dblSpoke, halfSpoke]; omega
          rw [hi'_eq]
          exact ⟨Sum.inr (halfSpoke i', j), hij,
            Relation.ReflTransGen.single (heven_adj (halfSpoke i') j hij)⟩
    have hstep_rep : ∀ a b,
        (((graphN d lam).deleteEdges (ηe '' E(G₀))).induce (ηv u)).Adj a b →
        Relation.ReflTransGen Gu.Adj (rep a) (rep b) := by
      rintro a b ⟨f, hlf⟩
      rw [Graph.induce_isLink, Graph.deleteEdges_isLink] at hlf
      obtain ⟨⟨hlf_N, hf_not⟩, ha_u, hb_u⟩ := hlf
      have hmf_not : mapEdge f ∉ ηe' '' E(G₀) := by
        rintro ⟨e, he, heq⟩
        exact hf_not ⟨e, he, hmapEdge_inj heq⟩
      rcases f with (t | i) | (⟨i, j⟩ | ⟨i, j⟩)
      · obtain ⟨ht_ne, hxy⟩ := hlf_N
        have ht'_ne : castTreeYInternal hlam t ≠ none := by
          cases t with
          | none => exact (ht_ne rfl).elim
          | some _ => exact Option.some_ne_none _
        have hl' : (graphN d (lam + 1)).IsLink (mapEdge (Sum.inl (Sum.inl t)))
            (rep (Sum.inl t)) (rep (Sum.inl (treeYInternalParent t))) :=
          ⟨ht'_ne, Or.inl ⟨rfl, by dsimp only [rep]; rw [treeYInternalParent_cast]⟩⟩
        rcases hxy with ⟨ha, hb⟩ | ⟨hb, ha⟩ <;> rw [ha, hb]
        · exact Relation.ReflTransGen.single ⟨_, (Graph.induce_isLink _ _ _ _ _).mpr
            ⟨(Graph.deleteEdges_isLink _ _ _ _ _).mpr ⟨hl', hmf_not⟩,
              Or.inl ⟨t, ha ▸ ha_u, rfl⟩, Or.inl ⟨_, hb ▸ hb_u, rfl⟩⟩⟩
        · exact Relation.ReflTransGen.single ⟨_, (Graph.induce_isLink _ _ _ _ _).mpr
            ⟨(Graph.deleteEdges_isLink _ _ _ _ _).mpr ⟨hl'.symm, hmf_not⟩,
              Or.inl ⟨_, ha ▸ ha_u, rfl⟩, Or.inl ⟨t, hb ▸ hb_u, rfl⟩⟩⟩
      · have hl' : (graphN d (lam + 1)).IsLink (mapEdge (Sum.inl (Sum.inr i)))
            (rep (Sum.inl (treeYLeafParent lam i))) (Sum.inl (botTreeYInternal hlam i)) :=
          ⟨botTreeYInternal_ne_none hlam i,
            Or.inr ⟨rfl, congrArg Sum.inl (treeYInternalParent_bot hlam i).symm⟩⟩
        rcases hlf_N with ⟨ha, hb⟩ | ⟨hb, ha⟩ <;> rw [ha, hb]
        · have hadj1 : Gu.Adj (rep (Sum.inl (treeYLeafParent lam i)))
              (Sum.inl (botTreeYInternal hlam i)) :=
            ⟨_, (Graph.induce_isLink _ _ _ _ _).mpr
              ⟨(Graph.deleteEdges_isLink _ _ _ _ _).mpr ⟨hl', hmf_not⟩,
                Or.inl ⟨_, ha ▸ ha_u, rfl⟩, Or.inr ⟨i, hb ▸ hb_u, rfl⟩⟩⟩
          exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single hadj1)
            (hbot_adj i (hb ▸ hb_u)).symm
        · have hadj1 : Gu.Adj (Sum.inl (botTreeYInternal hlam i))
              (rep (Sum.inl (treeYLeafParent lam i))) :=
            ⟨_, (Graph.induce_isLink _ _ _ _ _).mpr
              ⟨(Graph.deleteEdges_isLink _ _ _ _ _).mpr ⟨hl'.symm, hmf_not⟩,
                Or.inr ⟨i, ha ▸ ha_u, rfl⟩, Or.inl ⟨_, hb ▸ hb_u, rfl⟩⟩⟩
          exact Relation.ReflTransGen.head (hbot_adj i (ha ▸ ha_u))
            (Relation.ReflTransGen.single hadj1)
      · obtain ⟨hd0, hxy⟩ := hlf_N
        have hl' : (graphN d (lam + 1)).IsLink (mapEdge (Sum.inr (Sum.inl (i, j))))
            (Sum.inr (dblSpoke hlam i 1, j)) (rep (Sum.inr (nextSpoke i, j))) :=
          ⟨hd0, Or.inl ⟨rfl, by dsimp only [rep]; rw [hns_dbl1]⟩⟩
        rcases hxy with ⟨ha, hb⟩ | ⟨hb, ha⟩ <;> rw [ha, hb]
        · have hadj1 : Gu.Adj (Sum.inr (dblSpoke hlam i 1, j))
              (rep (Sum.inr (nextSpoke i, j))) :=
            ⟨_, (Graph.induce_isLink _ _ _ _ _).mpr
              ⟨(Graph.deleteEdges_isLink _ _ _ _ _).mpr ⟨hl', hmf_not⟩,
                show Sum.inr (halfSpoke (dblSpoke hlam i 1), j) ∈ ηv u by
                  rw [hhalf_dbl]; exact ha ▸ ha_u,
                show Sum.inr (halfSpoke (dblSpoke hlam (nextSpoke i) 0), j) ∈ ηv u by
                  rw [hhalf_dbl]; exact hb ▸ hb_u⟩⟩
          exact Relation.ReflTransGen.head (heven_adj i j (ha ▸ ha_u))
            (Relation.ReflTransGen.single hadj1)
        · have hadj1 : Gu.Adj (rep (Sum.inr (nextSpoke i, j)))
              (Sum.inr (dblSpoke hlam i 1, j)) :=
            ⟨_, (Graph.induce_isLink _ _ _ _ _).mpr
              ⟨(Graph.deleteEdges_isLink _ _ _ _ _).mpr ⟨hl'.symm, hmf_not⟩,
                show Sum.inr (halfSpoke (dblSpoke hlam (nextSpoke i) 0), j) ∈ ηv u by
                  rw [hhalf_dbl]; exact ha ▸ ha_u,
                show Sum.inr (halfSpoke (dblSpoke hlam i 1), j) ∈ ηv u by
                  rw [hhalf_dbl]; exact hb ▸ hb_u⟩⟩
          exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single hadj1)
            (heven_adj i j (hb ▸ hb_u)).symm
      · obtain ⟨hd0, hs, hxy⟩ := hlf_N
        have hl' : (graphN d (lam + 1)).IsLink (mapEdge (Sum.inr (Sum.inr (i, j))))
            (rep (Sum.inr (i, j))) (rep (Sum.inr (i, ⟨j.1 + 1, hs⟩))) :=
          ⟨hd0, hs, Or.inl ⟨rfl, rfl⟩⟩
        rcases hxy with ⟨ha, hb⟩ | ⟨hb, ha⟩ <;> rw [ha, hb]
        · exact Relation.ReflTransGen.single ⟨_, (Graph.induce_isLink _ _ _ _ _).mpr
            ⟨(Graph.deleteEdges_isLink _ _ _ _ _).mpr ⟨hl', hmf_not⟩,
              show Sum.inr (halfSpoke (dblSpoke hlam i 0), j) ∈ ηv u by
                rw [hhalf_dbl]; exact ha ▸ ha_u,
              show Sum.inr (halfSpoke (dblSpoke hlam i 0), ⟨j.1 + 1, hs⟩) ∈ ηv u by
                rw [hhalf_dbl]; exact hb ▸ hb_u⟩⟩
        · exact Relation.ReflTransGen.single ⟨_, (Graph.induce_isLink _ _ _ _ _).mpr
            ⟨(Graph.deleteEdges_isLink _ _ _ _ _).mpr ⟨hl'.symm, hmf_not⟩,
              show Sum.inr (halfSpoke (dblSpoke hlam i 0), ⟨j.1 + 1, hs⟩) ∈ ηv u by
                rw [hhalf_dbl]; exact ha ▸ ha_u,
              show Sum.inr (halfSpoke (dblSpoke hlam i 0), j) ∈ ηv u by
                rw [hhalf_dbl]; exact hb ▸ hb_u⟩⟩
    obtain ⟨K, hK_le, hVK, hK_conn⟩ := hm.connected u hu
    have hrep_conn : ∀ z₁ ∈ ηv u, ∀ z₂ ∈ ηv u,
        Relation.ReflTransGen Gu.Adj (rep z₁) (rep z₂) := by
      intro z₁ hz₁ z₂ hz₂
      have hrel := hK_conn.2 z₁ (hVK.symm ▸ hz₁) z₂ (hVK.symm ▸ hz₂); clear hz₂
      induction hrel with
      | refl => exact Relation.ReflTransGen.refl
      | @tail a b _ hab ih_r =>
        obtain ⟨f, hlf⟩ := hab
        have hstep_ab : (((graphN d lam).deleteEdges (ηe '' E(G₀))).induce (ηv u)).Adj a b :=
          ⟨f, (Graph.induce_isLink _ _ f a b).mpr
            ⟨hlf.mono hK_le, hVK ▸ hlf.left_mem, hVK ▸ hlf.right_mem⟩⟩
        exact Relation.ReflTransGen.trans ih_r (hstep_rep a b hstep_ab)
    obtain ⟨z₁, hz₁, hc₁⟩ := hto_rep x' hx'
    obtain ⟨z₂, hz₂, hc₂⟩ := hto_rep y' hy'
    exact Relation.ReflTransGen.trans
      (reflTransGen_symm_of (fun _ _ h => h.symm) hc₁)
      (Relation.ReflTransGen.trans (hrep_conn z₁ hz₁ z₂ hz₂) hc₂)

/-- Monotonicity of `graphN d lam` in `lam` (`1 ≤ d`, `1 ≤ lam₁ ≤ lam₂`) under minors. -/
theorem graphN_minor_mono_lam {d lam₁ lam₂ : ℕ} (hd : 1 ≤ d) (hlam₁ : 1 ≤ lam₁)
    (hle : lam₁ ≤ lam₂) :
    IsIsoMinor (graphN d lam₁) (graphN d lam₂) := by
  rcases Nat.exists_eq_add_of_le hle with ⟨k, hk⟩
  rw [hk]; clear hle hk
  have hid : ∃ (ηv : GraphNVertex d lam₁ → Set (GraphNVertex d (lam₁ + k)))
      (ηe : GraphNEdge d lam₁ → GraphNEdge d (lam₁ + k)),
      IsMinorModel (graphN d lam₁) (graphN d (lam₁ + k)) ηv ηe := by
    induction k with
    | zero =>
      refine ⟨fun v => {v}, id, isMinorModel_of_loopless_link
        (graphN_not_isLoopAt hlam₁)
        (fun v _ => singleton_nonempty v)
        (fun _ _ => subset_univ _)
        (fun _ _ _ _ hne => disjoint_singleton.mpr hne)
        (fun _ _ _ _ h => h)
        (fun e u v hl => ⟨u, rfl, v, rfl, hl⟩)
        (fun _ _ _ hx _ hy => by rw [mem_singleton_iff.mp hx, mem_singleton_iff.mp hy])⟩
    | succ k ih =>
      obtain ⟨ηv, ηe, hm⟩ := ih
      obtain ⟨ηv', ηe', hm', _⟩ :=
        double_graphN_model (graphN_not_isLoopAt hlam₁) hd (by omega) hm
      exact ⟨ηv', ηe', hm'⟩
  obtain ⟨ηv, ηe, hm⟩ := hid
  exact isIsoMinor_of_isMinorModel _ _ (Set.toFinite _) (Set.toFinite _)
    (Set.toFinite _) (Set.toFinite _) ηv ηe hm

/-- Iterating `double_graphN_model` `κ` times scales all circle-`0` dividers `b` by `2 ^ κ`. -/
theorem iterate_double_cyclic_model {α : Type u} {β : Type v}
    {G₀ C₀ : Graph α β} (hSimple : G₀.Simple) {p : ℕ} {cyc : CircuitCycle C₀ p}
    {d lam₀ : ℕ} (hcyc : HasCyclicModel G₀ C₀ cyc d lam₀) (κ : ℕ) :
    ∃ (ηv : α → Set (GraphNVertex d (lam₀ + κ))) (ηe : β → GraphNEdge d (lam₀ + κ))
      (b : Fin p → ℕ),
      IsMinorModel G₀ (graphN d (lam₀ + κ)) ηv ηe ∧
      (∀ t : Fin p, 2 ^ κ ≤ b t ∧ b t + 2 ^ κ ≤ 3 * 2 ^ ((lam₀ + κ) - 1)) ∧
      (∀ t₁ t₂ : Fin p, t₁ < t₂ → b t₁ + 2 ^ κ ≤ b t₂) ∧
      StrictMono b ∧
      ∀ t : Fin p, circle0ArcSet d (lam₀ + κ) cyc.hp b t ⊆ ηv (cyc.u t) := by
  obtain ⟨hd, hlam₀, _, ηv₀, ηe₀, b₀, hm₀, hb₀_bd, hb₀_mono, harc₀⟩ := hcyc
  induction κ with
  | zero =>
    refine ⟨ηv₀, ηe₀, b₀, hm₀, ?_, ?_, hb₀_mono, harc₀⟩
    · intro t; have := (hb₀_bd t).1; have := (hb₀_bd t).2; simp; omega
    · intro t₁ t₂ hlt; have := hb₀_mono hlt; simp; omega
  | succ κ ih =>
    obtain ⟨ηv₁, ηe₁, b₁, hm₁, hb₁_bd, hb₁_gap, hb₁_mono, harc₁⟩ := ih
    obtain ⟨ηv₂, ηe₂, hm₂, hhalf⟩ :=
      double_graphN_model (fun e _ u hl => hSimple.not_isLoopAt e u hl) hd (by omega) hm₁
    let b₂ : Fin p → ℕ := fun t => 2 * b₁ t
    have hpow2 : 2 ^ ((lam₀ + (κ + 1)) - 1) = 2 * 2 ^ ((lam₀ + κ) - 1) := by
      have h1 : lam₀ + (κ + 1) - 1 = (lam₀ + κ - 1) + 1 := by omega
      rw [h1, pow_succ']
    refine ⟨ηv₂, ηe₂, b₂, hm₂, ?_, ?_, ?_, ?_⟩
    · intro t
      have h1 := (hb₁_bd t).1; have h2 := (hb₁_bd t).2
      dsimp only [b₂]; rw [pow_succ', hpow2]; omega
    · intro t₁ t₂ hlt
      have hg := hb₁_gap t₁ t₂ hlt
      dsimp only [b₂]; rw [pow_succ']; omega
    · intro t₁ t₂ hlt
      have hm := hb₁_mono hlt
      dsimp only [b₂]; omega
    · intro t z hz
      unfold circle0ArcSet at hz
      split_ifs at hz with ht
      · obtain ⟨i', hi', rfl⟩ := hz
        change Sum.inr _ ∈ ηv₂ (cyc.u t)
        rw [hhalf]
        apply harc₁ t
        unfold circle0ArcSet; simp only [ht, ↓reduceDIte]
        refine ⟨⟨i'.1 / 2, by have := i'.2; omega⟩, ?_, rfl⟩
        dsimp only [b₂] at hi' ⊢
        rcases hi' with hlo | hhi
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      · obtain ⟨i', hlo, hhi, rfl⟩ := hz
        change Sum.inr _ ∈ ηv₂ (cyc.u t)
        rw [hhalf]
        apply harc₁ t
        unfold circle0ArcSet; simp only [ht, ↓reduceDIte]
        refine ⟨⟨i'.1 / 2, by have := i'.2; omega⟩, ?_, ?_, rfl⟩ <;>
          (dsimp only [b₂] at hlo hhi ⊢; omega)

end GraphMinor.GM03
