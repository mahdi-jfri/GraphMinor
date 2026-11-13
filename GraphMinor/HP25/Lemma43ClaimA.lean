module

public import GraphMinor.HP25.Lemma43Path
public import GraphMinor.HP25.Completion
import GraphMinor.HP25.Lemma43Reroute
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Lemma43Case1
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Prop34
import GraphMinor.HP25.Embedding

/-!
# Lemma 4.3, second case: every inner vertex of `P` reaches `C - {x, y, z}`

Humeau and Pous, proof of Lemma 4.3 (page 14): "Take $u$ an inner vertex of $P$. We prove that $u$
is $C\cup P$-connected to $C-\{x,y,z\}$." We state it as: every vertex of `P` has a neighbour in
the component `𝒞_C^P` (for an inner vertex this is the same: the second vertex of a
`C ∪ P`-path to `C - {x, y, z}` lies in `𝒞_C^P`, and conversely a path inside `𝒞_C^P` reaches `L`).
The ends `x` and `z` have neighbours on `L` (`IsXZPath.ends_good`).

The paper's proof, which we follow (`IsMuMin.claim_A`): take `vPw` the longest stretch of `P`
around `u` whose inner vertices have no such neighbour. `P` is induced, so `vw` is not an edge, and
by maximality `C` is crossed in `G + vw` by `(P₁, P₂)` with `vw ∈ P₁`. The path `P₂` meets the inner
vertices of `vPw`, "as otherwise $(P_2,P_1vPwP_1)$ would be a crossing of $C$ in $G$"
(`reroute_edge`). Orient `P₂` to end off `y` and let `s` be its last vertex inside `vPw`. After `s`,
`P₂` meets `P` again at a vertex `t` outside `vPw` (otherwise `s` has a neighbour in the
component), and the detour `PsQtP` removes `v` or `w` from `P`, which enlarges the component
(`IsMuMin.no_detour`).
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-! ### Lists -/

/-- The stretch `P[a], …, P[b]` of a list. -/
theorem stretch_facts {P : List V} {a b : ℕ} (hab : a ≤ b) (hb : b < P.length) :
    ((P.drop a).take (b - a + 1)).head? = some (P[a]'(by omega)) ∧
      ((P.drop a).take (b - a + 1)).getLast? = some P[b] ∧
      ∀ u ∈ (P.drop a).take (b - a + 1), ∃ t, ∃ ht : t < P.length, a ≤ t ∧ t ≤ b ∧ P[t] = u := by
  refine ⟨?_, ?_, fun u hu => ?_⟩
  · rw [List.head?_take, List.head?_drop]
    simp
  · rw [List.getLast?_eq_getElem?]
    simp only [List.length_take, List.length_drop]
    rw [show min (b - a + 1) (P.length - a) - 1 = b - a by omega]
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, show a + (b - a) = b by omega]
    exact List.getElem?_eq_getElem hb
  · obtain ⟨j, hj, hju⟩ := List.mem_iff_getElem.mp hu
    simp only [List.length_take, List.length_drop, lt_min_iff] at hj
    refine ⟨a + j, by omega, by omega, by omega, ?_⟩
    rw [← hju]
    simp

/-- An entry strictly inside a list without repetition is neither its first nor its last entry. -/
theorem mem_middle_ne {α γ δ : List V} {s t e₁ e₂ g : V}
    (hnd : (α ++ s :: (γ ++ t :: δ)).Nodup) (hh : (α ++ s :: (γ ++ t :: δ)).head? = some e₁)
    (hl : (α ++ s :: (γ ++ t :: δ)).getLast? = some e₂) (hg : g ∈ γ) : g ≠ e₁ ∧ g ≠ e₂ := by
  have e : α ++ s :: (γ ++ t :: δ) = (α ++ [s]) ++ γ ++ (t :: δ) := by simp
  rw [e] at hnd hh hl
  rw [List.nodup_append, List.nodup_append] at hnd
  constructor
  · rintro rfl
    have hg1 : g ∈ α ++ [s] := by
      rw [List.head?_append, List.head?_append] at hh
      cases hα : (α ++ [s]).head? with
      | none => simp at hα
      | some w =>
        rw [hα] at hh
        simp only [Option.some_or] at hh
        rw [← Option.some_injective _ hh]
        exact List.mem_of_mem_head? hα
    exact hnd.1.2.2 g hg1 g hg rfl
  · rintro rfl
    have hg2 : g ∈ t :: δ := by
      rw [List.getLast?_append] at hl
      cases hδ : (t :: δ).getLast? with
      | none => simp at hδ
      | some w =>
        rw [hδ] at hl
        simp only [Option.some_or] at hl
        rw [← Option.some_injective _ hl]
        exact List.mem_of_mem_getLast? hδ
    exact hnd.2.2 g (List.mem_append_right _ hg) g hg2 rfl


/-- The last entry of `A ++ s :: B` lies in `s :: B`. -/
theorem mem_of_getLast?_append_cons {A B : List V} {s e : V}
    (h : (A ++ s :: B).getLast? = some e) : e ∈ s :: B := by
  rw [List.getLast?_append] at h
  cases hB : (s :: B).getLast? with
  | none => simp at hB
  | some w =>
    rw [hB] at h
    simp only [Option.some_or] at h
    rw [← Option.some_injective _ h]
    exact List.mem_of_mem_getLast? hB

/-- **A gap between two indices.** If `p` holds at `0` and at `n` but not at `i ≤ n`, then `i` lies
strictly between two indices where `p` holds, with no index in between where `p` holds. -/
theorem exists_gap (p : ℕ → Prop) {i n : ℕ} (h0 : p 0) (hn : p n) (hi : ¬ p i) (hin : i ≤ n) :
    ∃ a b, a < i ∧ i < b ∧ b ≤ n ∧ p a ∧ p b ∧ ∀ j, a < j → j < b → ¬ p j := by
  classical
  have hin' : i < n := lt_of_le_of_ne hin fun e => hi (e ▸ hn)
  have hex : ∃ k, i < k ∧ p k := ⟨n, hin', hn⟩
  have ha : p (Nat.findGreatest p i) := Nat.findGreatest_spec (Nat.zero_le _) h0
  have hai : Nat.findGreatest p i ≤ i := Nat.findGreatest_le i
  have hai' : Nat.findGreatest p i ≠ i := fun e => hi (e ▸ ha)
  obtain ⟨hb1, hb2⟩ := Nat.find_spec hex
  refine ⟨Nat.findGreatest p i, Nat.find hex, by omega, hb1, Nat.find_min' hex ⟨hin', hn⟩, ha, hb2,
    fun j hj1 hj2 hpj => ?_⟩
  by_cases hji : j ≤ i
  · exact Nat.findGreatest_is_greatest hj1 hji hpj
  · exact Nat.find_min hex hj2 ⟨by omega, hpj⟩

section ClaimA

variable {S : Set V} {x y z ℓ : V} {L P : List V}

/-- The ends of `P` have neighbours in the component: `x` and `z` are adjacent on `C` to the last
and the first vertex of `L`. -/
theorem IsXZPath.ends_good (hC : IsCycleList G (x :: y :: z :: L))
    (hCS : ∀ v ∈ x :: y :: z :: L, v ∈ S) (hP : IsXZPath G (x :: y :: z :: L) x z P)
    (hℓ : ℓ ∈ L) :
    (∃ c ∈ compOf G S {v | v ∈ P} ℓ, G.Adj x c) ∧ ∃ c ∈ compOf G S {v | v ∈ P} ℓ, G.Adj z c := by
  have hLK := hP.L_mem hC hCS hℓ
  have hLne : L ≠ [] := List.ne_nil_of_mem hℓ
  constructor
  · obtain ⟨-, hlast⟩ := hC.adj_first_last (R := y :: z :: L) (by simp)
    have hmem : (y :: z :: L)[(y :: z :: L).length - 1] ∈ L := by
      rw [← List.getLast_eq_getElem (by simp), List.getLast_cons (by simp),
        List.getLast_cons hLne]
      exact List.getLast_mem hLne
    exact ⟨_, hLK _ hmem, hlast.symm⟩
  · have hch := (hC.isPathList (R := univ) fun _ _ => trivial).2.1
    obtain ⟨l₀, L', rfl⟩ := List.exists_cons_of_ne_nil hLne
    exact ⟨l₀, hLK l₀ (by simp), (List.isChain_cons_cons.mp hch.tail.tail).1⟩

theorem IsXZPath.getElem_zero (hP : IsXZPath G (x :: y :: z :: L) x z P) (h0 : 0 < P.length) :
    P[0] = x := by
  have e := hP.2.2.1
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0] at e
  exact Option.some.inj e

theorem IsXZPath.getElem_last (hP : IsXZPath G (x :: y :: z :: L) x z P)
    (h : P.length - 1 < P.length) : P[P.length - 1] = z := by
  have e := hP.2.2.2.1
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem h] at e
  exact Option.some.inj e

/-- `P` has at least two vertices, since its ends `x` and `z` differ. -/
theorem IsXZPath.two_le_length (hC : IsCycleList G (x :: y :: z :: L))
    (hP : IsXZPath G (x :: y :: z :: L) x z P) : 2 ≤ P.length := by
  have hpos : 0 < P.length := List.length_pos_of_ne_nil hP.ne_nil
  by_contra hlt
  have h1 := hP.getElem_zero hpos
  have h2 := hP.getElem_last (by omega)
  simp only [show P.length - 1 = 0 by omega] at h2
  have hnd := hC.2.1
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
  exact hnd.1.2.1 (h1.symm.trans h2)

/-- The inner vertices of `P` are off `C`. -/
theorem IsXZPath.inner_not_mem (hP : IsXZPath G (x :: y :: z :: L) x z P) {t : ℕ}
    (ht : t < P.length) (h0 : 0 < t) (h1 : t < P.length - 1) : P[t] ∉ x :: y :: z :: L := by
  intro hC
  have hnd := hP.2.1
  rcases hP.2.2.2.2 _ (List.getElem_mem _) hC with e | e
  · rw [← hP.getElem_zero (by omega)] at e
    have := hnd.getElem_inj_iff.mp e
    omega
  · rw [← hP.getElem_last (by omega)] at e
    have := hnd.getElem_inj_iff.mp e
    omega

/-- **The core of Claim A.** There is no stretch `P[a] … P[b]` with at least one inner vertex whose
ends have a neighbour in `𝒞_C^P` and whose inner vertices have none. -/
theorem IsMuMin.no_gap [Finite V] (h : IsMaxCrosslessOn G S (x :: y :: z :: L))
    (hC : IsCycleList G (x :: y :: z :: L)) (hCS : ∀ v ∈ x :: y :: z :: L, v ∈ S) (hℓ : ℓ ∈ L)
    (hP : IsMuMin G S (x :: y :: z :: L) x z ℓ P) {a b : ℕ} (hab : a + 2 ≤ b)
    (hb : b < P.length)
    (hga : ∃ c ∈ compOf G S {v | v ∈ P} ℓ, G.Adj (P[a]'(by omega)) c)
    (hgb : ∃ c ∈ compOf G S {v | v ∈ P} ℓ, G.Adj P[b] c)
    (hbad : ∀ j (hj : j < P.length), a < j → j < b →
      ¬ ∃ c ∈ compOf G S {v | v ∈ P} ℓ, G.Adj P[j] c) : False := by
  have hnd := hP.1.2.1
  have hPS : ∀ u ∈ P, u ∈ S := mem_of_isChain h.1 hP.1.1 (hP.1.two_le_length hC)
  have hℓP : ℓ ∉ P := hP.1.L_not_mem hC hℓ
  have hℓS : ℓ ∈ S := hCS ℓ (by simp [hℓ])
  have hKP : ∀ k ∈ compOf G S {v | v ∈ P} ℓ, k ∉ P := fun k hk =>
    (compOf_subset (G := G) (Y := {v | v ∈ P}) ⟨hℓS, hℓP⟩ hk).2
  have hvw : P[a]'(by omega) ≠ P[b] := fun e => by
    have := hnd.getElem_inj_iff.mp e
    omega
  have hnadj : ¬ G.Adj (P[a]'(by omega)) P[b] := hP.induced hℓS hℓP hab hb
  have hcr := h.2.2 _ (hPS _ (List.getElem_mem _)) _ (hPS _ (List.getElem_mem _)) hvw hnadj
  rcases isCrossed_sup_edge_cases' hcr with hG | ⟨a', b', c, d, Q, R, halt, hQ, hQe, hR, hdisj⟩
  · exact h.2.1 hG
  have hvQ : P[a]'(by omega) ∈ Q.support := Q.fst_mem_support_of_mem_edges hQe
  have hwQ : P[b] ∈ Q.support := Q.snd_mem_support_of_mem_edges hQe
  -- "`P₂` meets the inner vertices of `vPw`, as otherwise `(P₂, P₁vPwP₁)` would be a crossing"
  have hA1 : ∃ j, ∃ hj : j < P.length, a < j ∧ j < b ∧ P[j] ∈ R.support := by
    by_contra hno
    push Not at hno
    obtain ⟨hZh, hZl, hZm⟩ := stretch_facts (P := P) (a := a) (b := b) (by omega) hb
    refine h.2.1 (reroute_edge Q R halt hQ hQe hR hdisj ((hP.1.1.drop a).take _) hZh hZl
      (fun u hu huC => ?_) (fun u hu huR => ?_))
    · obtain ⟨t, ht, hat, htb, rfl⟩ := hZm u hu
      by_cases e1 : t = a
      · subst e1; exact Or.inl rfl
      · by_cases e2 : t = b
        · subst e2; exact Or.inr rfl
        · exact absurd huC (hP.1.inner_not_mem ht (by omega) (by omega))
    · obtain ⟨t, ht, hat, htb, rfl⟩ := hZm u hu
      by_cases e1 : t = a
      · subst e1; exact hdisj hvQ huR
      · by_cases e2 : t = b
        · subst e2; exact hdisj hwQ huR
        · exact hno t ht (by omega) (by omega) huR
  obtain ⟨j₀, hj₀, haj, hjb, hjR⟩ := hA1
  -- orient `P₂` so that it ends off `y`
  have hcd : c ≠ d := halt.ne hC.2.1
  obtain ⟨c', e, R', hR', hey, hce, hsupp⟩ : ∃ c' e, ∃ R' : G.Walk c' e, IsTPath G
      (x :: y :: z :: L) R' ∧ e ≠ y ∧ c' ≠ e ∧ ∀ u, u ∈ R'.support ↔ u ∈ R.support := by
    by_cases hdy : d = y
    · exact ⟨d, c, R.reverse, hR.reverse, fun h' => hcd (h'.trans hdy.symm), hcd.symm,
        fun u => by simp⟩
    · exact ⟨c, d, R, hR, hdy, hcd, fun u => Iff.rfl⟩
  have hYQ : ∀ u ∈ R'.support, u ∉ Q.support := fun u hu hQu => hdisj hQu ((hsupp u).mp hu)
  have hYch := R'.isChain_adj_support
  have hYnd := hR'.1.support_nodup
  have hYh := Walk.support_head? R'
  have hYl := Walk.support_getLast? R'
  have heC : e ∈ x :: y :: z :: L := hR'.2.2.1
  have hYS : ∀ u ∈ R'.support, u ∈ S := by
    refine mem_of_isChain h.1 hYch ?_
    rw [Walk.length_support]
    have : R'.length ≠ 0 := fun h0 => hce (Walk.eq_of_length_eq_zero h0)
    omega
  have hYin : ∀ g ∈ R'.support, g ≠ c' → g ≠ e → g ∉ x :: y :: z :: L := fun g hg h1 h2 =>
    (hR'.2.2.2 g hg h1 h2).1
  -- `s`: the last vertex of `P₂` inside `vPw`
  obtain ⟨α, s, β₀, hrev, hsM, hαM⟩ := exists_first_mem
    (Z := {u | ∃ j, ∃ hj : j < P.length, a < j ∧ j < b ∧ P[j] = u}) R'.support.reverse
    ⟨P[j₀], List.mem_reverse.mpr ((hsupp _).mpr hjR), j₀, hj₀, haj, hjb, rfl⟩
  have hY : R'.support = β₀.reverse ++ s :: α.reverse := by
    rw [← List.reverse_reverse R'.support, hrev]; simp
  obtain ⟨r, hr, har, hrb, rfl⟩ := hsM
  have hsC : P[r] ∉ x :: y :: z :: L := hP.1.inner_not_mem hr (by omega) (by omega)
  have hsbad := hbad r hr har hrb
  have hβM : ∀ u ∈ α.reverse, ¬ ∃ j, ∃ hj : j < P.length, a < j ∧ j < b ∧ P[j] = u :=
    fun u hu => hαM u (List.mem_reverse.mp hu)
  rw [hY] at hYch hYnd hYh hYl hYS hYQ hYin
  by_cases hβP : ∃ u ∈ α.reverse, u ∈ P
  · -- `t`: the first vertex of `P` after `s`
    obtain ⟨γ, t, δ, hβ, htP, hγP⟩ := exists_first_mem (Z := {u | u ∈ P}) α.reverse hβP
    have htM := hβM t (by rw [hβ]; simp)
    rw [hβ] at hYch hYnd hYh hYl hYS hYQ hYin
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem htP
    have htY : P[q] ∈ β₀.reverse ++ P[r] :: (γ ++ P[q] :: δ) := by simp
    have hqa : q ≠ a := fun e' => hYQ _ htY (by subst e'; exact hvQ)
    have hqb : q ≠ b := fun e' => hYQ _ htY (by subst e'; exact hwQ)
    have hqM : ¬ (a < q ∧ q < b) := fun ⟨h1, h2⟩ => htM ⟨q, hq, h1, h2, rfl⟩
    have hsplit : β₀.reverse ++ P[r] :: (γ ++ P[q] :: δ) =
        β₀.reverse ++ ((P[r] :: γ ++ [P[q]]) ++ δ) := by simp
    -- facts on the vertices of `γ`
    have hγC : ∀ g ∈ γ, g ∉ x :: y :: z :: L := fun g hg => by
      obtain ⟨h1, h2⟩ := mem_middle_ne hYnd hYh hYl hg
      exact hYin g (by simp [hg]) h1 h2
    have hch1 : (P[r] :: γ ++ [P[q]]).IsChain G.Adj := by
      rw [hsplit] at hYch
      exact hYch.right_of_append.left_of_append
    have hnd1 : (P[r] :: γ ++ [P[q]]).Nodup := by
      rw [hsplit] at hYnd
      exact hYnd.of_append_right.of_append_left
    have hγK : ∀ g ∈ γ, g ∉ compOf G S {v | v ∈ P} ℓ := by
      intro g hg hgK
      obtain ⟨g₀, γ', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hg)
      have hc2 : (P[r] :: g₀ :: γ').IsChain G.Adj := hch1.left_of_append
      have hreach := chain_reach (X := S \ {v | v ∈ P}) (List.isChain_cons_cons.mp hc2).2
        (fun u hu => ⟨hYS u (List.mem_append_right _ (List.mem_cons_of_mem _
          (List.mem_append_left _ hu))), hγP u hu⟩) g hg g₀ (by simp)
      exact hsbad ⟨g₀, hgK.trans hreach, (List.isChain_cons_cons.mp hc2).1⟩
    have h1P : ∀ u ∈ P[r] :: γ ++ [P[q]], u ∈ P → u = P[r] ∨ u = P[q] := by
      intro u hu huP
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hu
      rcases hu with rfl | hu | rfl
      · exact Or.inl rfl
      · exact absurd huP (hγP u hu)
      · exact Or.inr rfl
    have h1C : ∀ u ∈ P[r] :: γ ++ [P[q]], u ∈ x :: y :: z :: L → u ∈ P := by
      intro u hu huC
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hu
      rcases hu with rfl | hu | rfl
      · exact List.getElem_mem _
      · exact absurd huC (hγC u hu)
      · exact List.getElem_mem _
    have h1K : ∀ u ∈ P[r] :: γ ++ [P[q]], u ∉ compOf G S {v | v ∈ P} ℓ := by
      intro u hu
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hu
      rcases hu with rfl | hu | rfl
      · exact fun hk => hKP _ hk (List.getElem_mem _)
      · exact hγK u hu
      · exact fun hk => hKP _ hk (List.getElem_mem _)
    have h1Y : ∀ u ∈ P[r] :: γ ++ [P[q]], u ∈ β₀.reverse ++ P[r] :: (γ ++ P[q] :: δ) := by
      intro u hu
      rw [hsplit]
      exact List.mem_append_right _ (List.mem_append_left _ hu)
    rcases (show q < a ∨ b < q by omega) with hqa' | hbq
    · -- the detour from `t` back to `s` skips `v`
      refine hP.no_detour hℓS hℓP (p₂ := q) (p₄ := r) (m := a) hqa' har hr
        (Y₀ := (P[r] :: γ ++ [P[q]]).reverse)
        (List.isChain_reverse.mpr (hch1.imp fun _ _ h' => h'.symm)) (List.nodup_reverse.mpr hnd1)
        (by simp) (by rw [List.getLast?_reverse]; simp)
        (fun u hu huP => (h1P u (List.mem_reverse.mp hu) huP).symm)
        (fun u hu => h1C u (List.mem_reverse.mp hu)) (fun u hu => h1K u (List.mem_reverse.mp hu))
        (fun hv => hYQ _ (h1Y _ (List.mem_reverse.mp hv)) hvQ) (hPS _ (List.getElem_mem _)) hga
    · -- the detour from `s` to `t` skips `w`
      exact hP.no_detour hℓS hℓP (p₂ := r) (p₄ := q) (m := b) hrb hbq hq
        (Y₀ := P[r] :: γ ++ [P[q]]) hch1 hnd1 (by simp) (by rw [List.getLast?_append]; simp) h1P h1C h1K
        (fun hw => hYQ _ (h1Y _ hw) hwQ) (hPS _ (List.getElem_mem _)) hgb
  · -- after `s`, `P₂` avoids `P` and ends on `L`, so `s` has a neighbour in the component
    push Not at hβP
    have he1 := mem_of_getLast?_append_cons hYl
    have heβ : e ∈ α.reverse := by
      rcases List.mem_cons.mp he1 with rfl | he
      · exact absurd heC hsC
      · exact he
    have heP : e ∉ P := hβP e heβ
    have heL : e ∈ L := by
      simp only [List.mem_cons] at heC
      rcases heC with rfl | rfl | rfl | heL
      · exact absurd hP.1.x_mem heP
      · exact absurd rfl hey
      · exact absurd hP.1.z_mem heP
      · exact heL
    have heK := hP.1.L_mem hC hCS hℓ e heL
    obtain ⟨b₀, β', hβ⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem heβ)
    rw [hβ] at hYch hYS hβP heβ
    have hc2 : (P[r] :: b₀ :: β').IsChain G.Adj := hYch.right_of_append
    have hreach := chain_reach (X := S \ {v | v ∈ P}) (List.isChain_cons_cons.mp hc2).2
      (fun u hu => ⟨hYS u (by simp [hu]), hβP u hu⟩) e heβ b₀ (by simp)
    exact hsbad ⟨b₀, heK.trans hreach, (List.isChain_cons_cons.mp hc2).1⟩

/-- **Claim A** (proof of Lemma 4.3, page 14): "Take $u$ an inner vertex of $P$. We prove that $u$
is $C\cup P$-connected to $C-\{x,y,z\}$." Every vertex of `P` has a neighbour in the component
`𝒞_C^P` of `C - {x, y, z}` in `G - P`. -/
theorem IsMuMin.claim_A [Finite V] (h : IsMaxCrosslessOn G S (x :: y :: z :: L))
    (hC : IsCycleList G (x :: y :: z :: L)) (hCS : ∀ v ∈ x :: y :: z :: L, v ∈ S) (hℓ : ℓ ∈ L)
    (hP : IsMuMin G S (x :: y :: z :: L) x z ℓ P) (i : ℕ) (hi : i < P.length) :
    ∃ c ∈ compOf G S {v | v ∈ P} ℓ, G.Adj P[i] c := by
  by_contra hbad
  have h2 := hP.1.two_le_length hC
  obtain ⟨hx, hz⟩ := hP.1.ends_good hC hCS hℓ
  obtain ⟨a, b, hai, hib, hbn, ⟨ha, hga⟩, ⟨hb, hgb⟩, hmid⟩ := exists_gap
    (fun j => ∃ hj : j < P.length, ∃ c ∈ compOf G S {v | v ∈ P} ℓ, G.Adj P[j] c)
    (i := i) (n := P.length - 1) ⟨by omega, by rw [hP.1.getElem_zero (by omega)]; exact hx⟩
    ⟨by omega, by rw [hP.1.getElem_last (by omega)]; exact hz⟩
    (fun ⟨_, h'⟩ => hbad h') (by omega)
  exact hP.no_gap h hC hCS hℓ (a := a) (b := b) (by omega) hb hga hgb
    fun j hj h1 h2 hg => hmid j h1 h2 ⟨hj, hg⟩

end ClaimA

end GraphMinor.HP25
