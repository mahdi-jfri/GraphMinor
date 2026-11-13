module

public import GraphMinor.LRPlanarity.Statements
import GraphMinor.LRPlanarity.ContourTree

/-!
# The fork-order lemmas

This file proves `ForkOrderAStatement` and `ForkOrderBStatement`, Lemmas (A) and (B) of
Part IV, Section 3 of `docs/planarity/planarity_test.tex`.

The signed order at a vertex puts the `L` edges first in decreasing key, then the `R` edges in
increasing key. The relation `signedLE` is total and transitive, so the merge sort lists the
outgoing edges in this order, and an edge that is strictly smaller comes first
(`idxOf_lt_of_not_signedLE`).

The color of an outgoing edge is the color of a highest return. If a return `b` of `e` lies in a
fork set `I(e,g)`, so does the highest return, and the fork constraints give both the same
color (`edgeColor_eq_of_forkSet`). The two lemmas then compare the colors and keys of the two
fork edges as the note does. Lemma (B) uses weak alignment in its last case, to find a third
outgoing edge with a lower lowpoint.
-/

public section

namespace GraphMinor.LRPlanarity.ForkOrder

open SearchTree

variable {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}

/-! ### The signed order -/

theorem signedLE_total (color : Coloring N) (e f : Arc N) :
    T.signedLE G color e f ∨ T.signedLE G color f e := by
  unfold Forest.signedLE
  generalize T.edgeColor G color e = x
  generalize T.edgeColor G color f = y
  cases x <;> cases y <;> simp <;> omega

theorem signedLE_trans (color : Coloring N) {e f g : Arc N} (h₁ : T.signedLE G color e f)
    (h₂ : T.signedLE G color f g) : T.signedLE G color e g := by
  revert h₁ h₂
  unfold Forest.signedLE
  generalize T.edgeColor G color e = x
  generalize T.edgeColor G color f = y
  generalize T.edgeColor G color g = z
  cases x <;> cases y <;> cases z <;> simp <;> omega

theorem mem_signedOutgoing (color : Coloring N) (v : Fin N) (e : Arc N) :
    e ∈ T.signedOutgoing G color v ↔ T.Outgoing G v e := by
  unfold Forest.signedOutgoing
  simp only [List.mem_mergeSort, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]

theorem nodup_signedOutgoing (color : Coloring N) (v : Fin N) :
    (T.signedOutgoing G color v).Nodup := by
  unfold Forest.signedOutgoing
  exact List.nodup_mergeSort.mpr (Finset.nodup_toList _)

theorem pairwise_signedOutgoing (color : Coloring N) (v : Fin N) :
    (T.signedOutgoing G color v).Pairwise (T.signedLE G color) := by
  unfold Forest.signedOutgoing
  refine (List.pairwise_mergeSort (fun a b c hab hbc => ?_) (fun a b => ?_) _).imp ?_
  · simp only [decide_eq_true_eq] at hab hbc ⊢
    exact signedLE_trans color hab hbc
  · simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact signedLE_total (T := T) (G := G) color a b
  · intro a b h
    simpa only [decide_eq_true_eq] using h

/-- An outgoing edge that is strictly smaller in the signed order comes first. -/
theorem idxOf_lt_of_not_signedLE (color : Coloring N) {v : Fin N} {e f : Arc N}
    (he : T.Outgoing G v e) (hf : T.Outgoing G v f) (h : ¬ T.signedLE G color f e) :
    (T.signedOutgoing G color v).idxOf e < (T.signedOutgoing G color v).idxOf f := by
  have hef : e ≠ f := by
    rintro rfl
    rcases signedLE_total (T := T) (G := G) color e e with h' | h' <;> exact h h'
  have he' := (mem_signedOutgoing color v e).mpr he
  have hf' := (mem_signedOutgoing color v f).mpr hf
  rcases Nat.lt_trichotomy ((T.signedOutgoing G color v).idxOf e)
    ((T.signedOutgoing G color v).idxOf f) with hlt | heq | hgt
  · exact hlt
  · exact absurd ((List.idxOf_inj he').mp heq) hef
  · exfalso
    apply h
    have hpw := pairwise_signedOutgoing (T := T) (G := G) color v
    rw [List.pairwise_iff_getElem] at hpw
    have hfl := List.idxOf_lt_length_of_mem hf'
    have hel := List.idxOf_lt_length_of_mem he'
    have := hpw _ _ hfl hel hgt
    rwa [List.getElem_idxOf, List.getElem_idxOf] at this

theorem not_signedLE_right_left (color : Coloring N) {e f : Arc N}
    (he : T.edgeColor G color e = .left) (hf : T.edgeColor G color f = .right) :
    ¬ T.signedLE G color f e := by
  unfold Forest.signedLE
  rw [he, hf]
  simp

theorem not_signedLE_left_left (color : Coloring N) {e f : Arc N}
    (he : T.edgeColor G color e = .left) (hf : T.edgeColor G color f = .left)
    (hk : T.key G f < T.key G e) : ¬ T.signedLE G color f e := by
  unfold Forest.signedLE
  rw [he, hf]
  simp only [not_le]
  exact hk

theorem not_signedLE_right_right (color : Coloring N) {e f : Arc N}
    (he : T.edgeColor G color e = .right) (hf : T.edgeColor G color f = .right)
    (hk : T.key G e < T.key G f) : ¬ T.signedLE G color f e := by
  unfold Forest.signedLE
  rw [he, hf]
  simp only [not_le]
  exact hk

/-! ### Edge colors and keys -/

/-- The edge color is the color of a highest return. -/
theorem exists_edgeColor_eq (color : Coloring N) {e : Arc N} (h : (T.returns G e).Nonempty) :
    ∃ m ∈ T.returns G e, (∀ c ∈ T.returns G e, T.depth c.2 ≤ T.depth m.2) ∧
      T.edgeColor G color e = color m := by
  have hex := exists_highest h
  unfold Forest.edgeColor
  rw [dite_eq_left hex]
  exact ⟨_, (Classical.choose_spec hex).1, (Classical.choose_spec hex).2, rfl⟩

/-- If a return `b` of `e` lies in a fork set `I(e,g)`, the edge color of `e` is the color
of `b`. "In particular its highest return does, so sigma(e1) is the color of b1." -/
theorem edgeColor_eq_of_forkSet {color : Coloring N} (hFC : T.ForkConstraints G color)
    {v : Fin N} {e g b : Arc N} (he : T.Outgoing G v e) (hg : T.Outgoing G v g) (heg : e ≠ g)
    (hb : b ∈ T.forkSet G e g) : T.edgeColor G color e = color b := by
  obtain ⟨m, hm, hmax, hσ⟩ := exists_edgeColor_eq color ⟨b, hb.1⟩
  have hmF : m ∈ T.forkSet G e g := ⟨hm, lt_of_lt_of_le hb.2 (hmax b hb.1)⟩
  rw [hσ]
  exact (hFC v e g he hg heg).1 m hmF b hb

theorem key_lt_of_low_lt {e f : Arc N} (h : T.low G f < T.low G e) : T.key G f < T.key G e := by
  unfold Forest.key
  have := Bool.toNat_le (T.thick G f)
  omega

/-- An edge with returns at two depths is thick. -/
theorem thick_of_lt {e b c : Arc N} (hb : b ∈ T.returns G e) (hc : c ∈ T.returns G e)
    (h : T.depth b.2 < T.depth c.2) : T.thick G e = true :=
  (thick_eq_true_iff e).mpr ⟨b, hb, c, hc, Nat.ne_of_lt h⟩

/-- An edge whose returns all have one head depth is thin. -/
theorem thick_eq_false {e : Arc N} {d : ℕ} (h : ∀ c ∈ T.returns G e, T.depth c.2 = d) :
    T.thick G e = false := by
  rw [Bool.eq_false_iff, ne_eq, thick_eq_true_iff]
  rintro ⟨b, hb, c, hc, hne⟩
  rw [h b hb, h c hc] at hne
  exact hne rfl

/-! ### Lemma (A) -/

/-- Part IV, Section 3, Lemma (A), the case of equal edge colors: then `k(f) < k(e)`.
"Then the two opposite fork sets cannot both contain their highest returns, so
high(e2)<=low(e1)." -/
theorem key_lt_of_edgeColor_eq {color : Coloring N} (hFC : T.ForkConstraints G color)
    {v : Fin N} {e f b c : Arc N} (he : T.Outgoing G v e) (hf : T.Outgoing G v f) (hef : e ≠ f)
    (hb : b ∈ T.returns G e) (hc : c ∈ T.returns G f) (hd : T.depth c.2 < T.depth b.2)
    (hσ : T.edgeColor G color f = T.edgeColor G color e) : T.key G f < T.key G e := by
  have hcl := low_le_of_returns hc
  have hbF : b ∈ T.forkSet G e f := ⟨hb, by omega⟩
  obtain ⟨m, hm, hmmax, hσf⟩ := exists_edgeColor_eq color ⟨c, hc⟩
  -- The highest return `m` of `f` is not above `low e`.
  have hmlow : T.depth m.2 ≤ T.low G e := by
    by_contra hlt
    have hmF : m ∈ T.forkSet G f e := ⟨hm, Nat.lt_of_not_le hlt⟩
    have hne := (hFC v e f he hf hef).2.2 b hbF m hmF
    rw [← hσf, hσ, edgeColor_eq_of_forkSet hFC he hf hef hbF] at hne
    exact hne rfl
  have hcm := hmmax c hc
  rcases Nat.lt_or_ge (T.low G f) (T.low G e) with hlt | hge
  · exact key_lt_of_low_lt hlt
  · -- Equal lows: `f` is thin and `e` is thick.
    have heq : T.low G f = T.low G e := by omega
    have hthin : T.thick G f = false := by
      refine thick_eq_false (d := T.low G e) fun c' hc' => ?_
      have := low_le_of_returns hc'
      have := hmmax c' hc'
      omega
    have hbv := (returns_spec hb).2.2
    obtain ⟨c₀, hc₀, hc₀d⟩ := exists_returns_of_low_lt (T := T) (G := G) (e := e) (by omega)
    have hthick : T.thick G e = true := thick_of_lt hc₀ hb (by omega)
    unfold Forest.key
    rw [hthin, hthick, heq]
    simp

/-! ### Lemma (B) -/

/-- A back edge leaving the subtree of `v` lies in the return set of an outgoing edge at `v`:
the back edge itself when its source is `v`, and otherwise the tree edge to the child above its
source. -/
theorem exists_outgoing_returns {v : Fin N} {d : Arc N}
    (hd : T.BackEdge G d) (hvd : T.Ancestor v d.1) (hdv : T.depth d.2 < T.depth v) :
    ∃ g, T.Outgoing G v g ∧ d ∈ T.returns G g := by
  by_cases h : v = d.1
  · exact ⟨d, ⟨h.symm, Or.inr hd⟩, hd, Or.inl ⟨hd, rfl⟩⟩
  · obtain ⟨y, hy, hyd⟩ := exists_child_of_ancestor hvd h
    exact ⟨(v, y), ⟨rfl, Or.inl hy⟩, hd, Or.inr ⟨hy, hyd, hdv⟩⟩

/-- Part IV, Section 3, Lemma (B), last case: "Let (p,v) be the incoming tree edge of v. If its
weak minimum head depth were h(u), alignment would force b1 and b2 to have the same color.
Therefore that weak minimum is strictly below h(u). Since h(p)>=h(u), both b1 and b2 are weak
returns of (p,v), so some third outgoing edge e0 of v has low(e0)<h(u)." -/
theorem exists_low_lt_of_weakAlignment (hT : T.IsDFS G) {color : Coloring N}
    (hWA : T.WeakAlignment G color) {v : Fin N} {e f b c : Arc N} (he : T.Outgoing G v e)
    (hf : T.Outgoing G v f) (hb : b ∈ T.returns G e) (hc : c ∈ T.returns G f)
    (hbc : b.2 = c.2) (hcol : color b ≠ color c) :
    ∃ g, T.Outgoing G v g ∧ T.low G g < T.depth b.2 := by
  obtain ⟨hbv, hne⟩ := head_ancestor_of_returns hT hb
  rw [he.1] at hbv hne
  obtain ⟨hbb, hvb, _⟩ := returns_spec hb
  obtain ⟨hcb, hvc, _⟩ := returns_spec hc
  rw [he.1] at hvb
  rw [hf.1] at hvc
  rcases ancestor_cases_tail hbv with h | ⟨p, hbp, hvp⟩
  · exact absurd h.symm hne
  have hpd := depth_le_of_ancestor hT hbp
  have hvd := depth_of_parent hT hvp
  have hbW : b ∈ T.weakReturns G (p, v) := ⟨hbb, hvb, hpd⟩
  have hcW : c ∈ T.weakReturns G (p, v) := ⟨hcb, hvc, hbc ▸ hpd⟩
  by_contra hno
  push Not at hno
  have hmin : ∀ d ∈ T.weakReturns G (p, v), T.depth b.2 ≤ T.depth d.2 := by
    intro d hd
    obtain ⟨hdb, hvd', hdp⟩ := hd
    simp only at hvd' hdp
    by_contra hlt
    push Not at hlt
    obtain ⟨g, hg, hdg⟩ := exists_outgoing_returns hdb hvd' (by omega)
    have := hno g hg
    have := low_le_of_returns hdg
    omega
  exact hcol (hWA (p, v) hvp b ⟨hbW, hmin⟩ c ⟨hcW, hbc ▸ hmin⟩)

end GraphMinor.LRPlanarity.ForkOrder

namespace GraphMinor.LRPlanarity

open SearchTree ForkOrder

/-- Part IV, Section 3, Lemma (A): "Suppose that h(u1)>h(u2). Then e1 precedes e2 in the
outgoing order if and only if b1 is L." -/
theorem forkOrderA_proved : ForkOrderAStatement := by
  intro N G T color _ hFC _ v e f b c he hf hef hb hc hd
  have hbF : b ∈ T.forkSet G e f := ⟨hb, lt_of_le_of_lt (low_le_of_returns hc) hd⟩
  have hσe := edgeColor_eq_of_forkSet hFC he hf hef hbF
  by_cases hσ : T.edgeColor G color f = T.edgeColor G color e
  · have hk := key_lt_of_edgeColor_eq hFC he hf hef hb hc hd hσ
    cases hcol : color b
    · rw [hcol] at hσe
      rw [hσe] at hσ
      exact iff_of_true (idxOf_lt_of_not_signedLE color he hf
        (not_signedLE_left_left color hσe hσ hk)) rfl
    · rw [hcol] at hσe
      rw [hσe] at hσ
      refine iff_of_false (Nat.lt_asymm (idxOf_lt_of_not_signedLE color hf he
        (not_signedLE_right_right color hσ hσe hk))) (by simp)
  · cases hcol : color b
    · rw [hcol] at hσe
      have hσf : T.edgeColor G color f = .right := by
        cases h : T.edgeColor G color f
        · exact absurd (h.trans hσe.symm) hσ
        · rfl
      exact iff_of_true (idxOf_lt_of_not_signedLE color he hf
        (not_signedLE_right_left color hσe hσf)) rfl
    · rw [hcol] at hσe
      have hσf : T.edgeColor G color f = .left := by
        cases h : T.edgeColor G color f
        · rfl
        · exact absurd (h.trans hσe.symm) hσ
      refine iff_of_false (Nat.lt_asymm (idxOf_lt_of_not_signedLE color hf he
        (not_signedLE_right_left color hσf hσe))) (by simp)

/-- Part IV, Section 3, Lemma (B): "Suppose that u1=u2=u, that b1 is L and that b2 is R. Then
e1 precedes e2." -/
theorem forkOrderB_proved : ForkOrderBStatement := by
  intro N G T color hT hFC hWA v e f b c he hf hef hb hc hbc hbL hcR
  apply idxOf_lt_of_not_signedLE color he hf
  have hbl := low_le_of_returns hb
  have hcl := low_le_of_returns hc
  rw [← hbc] at hcl
  have hσe : T.low G f < T.depth b.2 → T.edgeColor G color e = .left := fun h =>
    (edgeColor_eq_of_forkSet hFC he hf hef ⟨hb, h⟩).trans hbL
  have hσf : T.low G e < T.depth b.2 → T.edgeColor G color f = .right := fun h =>
    (edgeColor_eq_of_forkSet hFC hf he (Ne.symm hef) ⟨hc, hbc ▸ h⟩).trans hcR
  rcases Nat.lt_or_ge (T.low G e) (T.depth b.2) with h₁ | h₁ <;>
    rcases Nat.lt_or_ge (T.low G f) (T.depth b.2) with h₂ | h₂
  · -- "If both li<h(u), the fork constraints force sigma(e1)=L and sigma(e2)=R."
    exact not_signedLE_right_left color (hσe h₂) (hσf h₁)
  · -- "If l1<h(u)=l2, they force sigma(e2)=R, and key(e1)<key(e2)."
    have hfR := hσf h₁
    have hk : T.key G e < T.key G f := key_lt_of_low_lt (by omega)
    cases hE : T.edgeColor G color e
    · exact not_signedLE_right_left color hE hfR
    · exact not_signedLE_right_right color hE hfR hk
  · -- "If l2<h(u)=l1, then symmetrically sigma(e1)=L and key(e2)<key(e1)"
    have heL := hσe h₂
    have hk : T.key G f < T.key G e := key_lt_of_low_lt (by omega)
    cases hF : T.edgeColor G color f
    · exact not_signedLE_left_left color heL hF hk
    · exact not_signedLE_right_left color heL hF
  · -- "Suppose l1=l2=h(u)." A third edge `g` has a lower lowpoint.
    obtain ⟨g, hg, hgl⟩ := exists_low_lt_of_weakAlignment hT hWA he hf hb hc hbc
      (by rw [hbL, hcR]; simp)
    have heg : e ≠ g := by rintro rfl; omega
    have hfg : f ≠ g := by rintro rfl; omega
    have hE := (edgeColor_eq_of_forkSet hFC he hg heg ⟨hb, hgl⟩).trans hbL
    have hF := (edgeColor_eq_of_forkSet hFC hf hg hfg ⟨hc, hbc ▸ hgl⟩).trans hcR
    exact not_signedLE_right_left color hE hF

end GraphMinor.LRPlanarity
