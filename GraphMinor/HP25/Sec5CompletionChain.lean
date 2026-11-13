module

public import GraphMinor.HP25.Sec5ExtractTwo
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Sec5Lemma54

/-!
# The steps of the completion, as data for the extraction

The completion of an induced separating `C`-path (`completion_loop`, `Sec5Tighten.lean`) runs
three stages: the rerouting stage, which adds no edge; the collapse stage, which adds the edges of
Claim 5.5 (`collapse_all`); and the loop stage, which adds the edges of the loop of Algorithm 5.2
(`complete_loop_edges`). The extraction of a crossing (`extractCrossingTwoPart`,
`Sec5ExtractTwo.lean`) needs the edges of the collapse stage and of the loop stage one by one, with
the data that each undo uses: a `T2Chain` from `G` to the graph `G₂` after the collapse stage, and
an `AddedEdgeChain` from `G₂` to the graph `H_full` after the loop stage.

This file runs the same three stages again and records these steps.

* `collapse_all_chain` is `collapse_all` with a `T2Chain`: each edge `y z` is added under the
  hypotheses of `claim_5_5_of`, which is what `T2Step` holds.
* `complete_loop_chain` is `complete_loop_edges` with an `AddedEdgeChain`: each edge `y s` is added
  under the hypotheses of the strip lemma, which is what `AddedEdgeStep` holds. It also counts the
  steps: each step makes the prefix of the path on both sides longer by at least one vertex, so the
  number of steps is less than the length of the final path.
* `completion_chain` puts the stages together. It keeps, as `completion_loop` does, only the edges
  of `H_full` with both ends on the final path `P'` (the graph `H`, with `H ≤ H_full`).

The proofs follow those of `collapse_all`, `complete_loop_edges` and `completion_loop`, with the chain
carried as an accumulator: the theorems start from any chain that ends at the current graph.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {C A B : List V} {a b : V} {k : ℕ}

/-- Number of collapse steps in a `T2Chain`. -/
@[expose] def T2Chain.length {G H : SimpleGraph V} : T2Chain V C A B a b k G H → ℕ
  | .nil => 0
  | .snoc _ _ chain => chain.length + 1

/-- **The data of one collapse step.** The hypotheses of `collapse_step` give a `T2Step`: the
window condition comes from weak tightness (`windowClosed_of_weaklyTight`). -/
@[expose] def T2Step.ofCollapse {G : SimpleGraph V} {L₁ N L₂ : List V} {y z : V}
    (hrot : C.rotate k = a :: A ++ b :: B) {P : G.Walk a b} (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ z :: L₂)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (hwt : IsWeaklyTight G C A B P.support)
    (hno : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v ∧
      ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
    (hy : IsSided G {x | x ∈ C ∨ x ∈ P.support} A B y)
    (hz : IsSided G {x | x ∈ C ∨ x ∈ P.support} A B z) : T2Step V C A B a b k :=
  ⟨G, y, z, L₁, N, L₂, P, hrot, hP, hsupp, hind, windowClosed_of_weaklyTight hsupp hwt hy hz, hno⟩

/-- **The edges of Claim 5.5, with their steps.** This is `collapse_all` that also returns the
collapse steps: for every `T2Chain` `c` from `G₀` to `G`, the chain `t` from `G₀` to the final graph
`H` extends `c` by one `T2Step` per added edge. -/
theorem collapse_all_chain (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ []) (hB : B ≠ []) :
    ∀ (n : ℕ) (G : SimpleGraph V) (P : G.Walk a b), P.support.length = n → IsCycleList G C →
      IsTPath G C P →
      (∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v) →
      Separates G {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B} →
      IsWeaklyTight G C A B P.support →
      ∀ (G₀ : SimpleGraph V) (_ : T2Chain V C A B a b k G₀ G),
      ∃ H : SimpleGraph V, ∃ _ : T2Chain V C A B a b k G₀ H, G ≤ H ∧
        (IsCrossed H C → IsCrossed G C) ∧
        ∃ P' : H.Walk a b, IsTPath H C P' ∧
          (∀ u ∈ P'.support, ∀ v ∈ P'.support, H.Adj u v → IsListEdge P'.support u v) ∧
          Separates H {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} ∧
          IsTight H C A B P'.support ∧
          (∀ v ∈ P'.support, IsSided H {x | x ∈ C ∨ x ∈ P'.support} A B v) ∧
          P'.support.Sublist P.support ∧
          ∀ (X' : Set V), (∀ v ∈ P.support, v ∉ P'.support → v ∉ X') →
            ∀ u S, IsConnectedAvoiding H X' u S ↔ IsConnectedAvoiding G X' u S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G P hn hC hP hind hsep hwt G₀ c
  classical
  set X : Set V := {x | x ∈ C ∨ x ∈ P.support} with hX
  have hends := ends_sided (X := X) hC hrot hA hB
  have hab : a ≠ b := by
    intro h
    have hnd : (a :: A ++ b :: B).Nodup := hrot ▸ List.nodup_rotate.mpr hC.2.1
    rw [List.cons_append, List.nodup_cons] at hnd
    exact hnd.1 (by simp [h])
  have hlen : 2 ≤ P.support.length := by
    cases P with
    | nil => exact absurd rfl hab
    | cons h p => simp only [Walk.support_cons, List.length_cons]; have := p.support_ne_nil
                  have := List.length_pos_of_ne_nil this; omega
  by_cases hall : ∀ v ∈ P.support, IsSided G X A B v
  · exact ⟨G, c, le_rfl, id, P, hP, hind, hsep, tight_of_weaklyTight hlen hwt hall, hall,
      List.Sublist.refl _, fun _ _ _ _ => Iff.rfl⟩
  push Not at hall
  have hhead : P.support.head? = some a := by rw [← Walk.cons_tail_support]; rfl
  have hlast : P.support.getLast? = some b := by
    rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
  obtain ⟨L₁, y, N, z, L₂, hsupp, hy, hz, hN, hNo⟩ :=
    exists_run (IsSided G X A B) hhead hends.1 hlast hends.2 hall
  have hno : ∀ v ∈ N, ¬ IsOnSide G X {x | x ∈ A} v ∧ ¬ IsOnSide G X {x | x ∈ B} v :=
    fun v hv => ⟨fun h => hNo v hv (Or.inl h), fun h => hNo v hv (Or.inr h)⟩
  obtain ⟨hsafe, P', hP', hP's, hind', hsep', hwt', -⟩ :=
    collapse_step hC hrot hP hsupp hind hsep hwt hno hy hz
  have hsub : P'.support.Sublist P.support := hsupp ▸ hP's ▸ sublist_collapse
  have hnd : (L₁ ++ y :: N ++ z :: L₂).Nodup := hsupp ▸ hP.1.support_nodup
  have hNP' : ∀ v ∈ N, v ∈ P.support ∧ v ∉ P'.support := fun v hv =>
    ⟨by rw [hsupp]; simp [hv], hP's ▸ not_mem_short_of_mem_N hnd hv⟩
  have hlt : P'.support.length < n := by
    rw [← hn, hsupp, hP's]
    obtain ⟨m, M, rfl⟩ := List.exists_cons_of_ne_nil hN
    simp
  let step : T2Step V C A B a b k := T2Step.ofCollapse hrot hP hsupp hind hwt hno hy hz
  obtain ⟨H, t, hle, hcr, P'', h1, h2, h3, h4, h5, hsub', hconn⟩ :=
    ih _ hlt (G ⊔ edge y z) P' rfl (hC.mono le_sup_left) hP' hind' hsep' hwt' G₀
      (.snoc step (Classical.decRel _) c)
  refine ⟨H, t, le_sup_left.trans hle, fun h => hsafe (hcr h), P'', h1, h2, h3, h4, h5,
    hsub'.trans hsub, fun X' hX' u S => ?_⟩
  have hconn₁ := isConnectedAvoiding_collapse_iff hsupp (X' := X')
    (fun v hv => hX' v (hNP' v hv).1 fun h => (hNP' v hv).2 (hsub'.subset h)) (u := u) (S := S)
  have hconn₂ := hconn X' (fun v hv => hX' v (hsub.subset hv)) u S
  exact hconn₂.trans hconn₁

/-- **The loop of Algorithm 5.2, with its steps.** This is `complete_loop_edges` that also returns
the loop steps: for every `AddedEdgeChain` `c` from `G₀` to `G`, the chain `t` from `G₀` to the final
graph `H` extends `c` by one `AddedEdgeStep` per added edge. The last conclusion counts the steps:
for every prefix `M` of `P` on both sides, `t` has at most `|P'| - |M|` more steps than `c`. -/
theorem complete_loop_chain [Finite V] (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ [])
    (hB : B ≠ []) :
    ∀ (n : ℕ) (G : SimpleGraph V) (P : G.Walk a b), P.support.length = n → IsCycleList G C →
      IsTPath G C P →
      (∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v) →
      Separates G {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B} →
      IsTight G C A B P.support →
      (∀ v ∈ P.support, IsSided G {x | x ∈ C ∨ x ∈ P.support} A B v) →
      ∀ (G₀ : SimpleGraph V) (c : AddedEdgeChain V C A B a b k G₀ G),
      ∃ H : SimpleGraph V, ∃ t : AddedEdgeChain V C A B a b k G₀ H, G ≤ H ∧
        (IsCrossed H C → IsCrossed G C) ∧
        ∃ P' : H.Walk a b, IsTPath H C P' ∧ OnBothSides H C A B P' ∧
          Separates H {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} ∧
          (∀ u ∈ P'.support, ∀ v ∈ P'.support, H.Adj u v → IsListEdge P'.support u v) ∧
          IsTight H C A B P'.support ∧
          (∀ u v, H.Adj u v → G.Adj u v ∨ IsListEdge P'.support u v) ∧
          P'.support.Sublist P.support ∧
          (∀ M, M <+: P.support → (∀ v ∈ M,
              IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v ∧
              IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v) → M <+: P'.support) ∧
          (∀ M, M <+: P.support → (∀ v ∈ M,
              IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v ∧
              IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v) →
            t.length + M.length ≤ c.length + P'.support.length) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G P hn hC hP hind hsep htight hsided G₀ c
  classical
  set X : Set V := {x | x ∈ C ∨ x ∈ P.support} with hX
  by_cases hall : ∀ v ∈ P.support, IsOnSide G X {x | x ∈ A} v ∧ IsOnSide G X {x | x ∈ B} v
  · exact ⟨G, c, le_rfl, id, P, hP, hall, hsep, hind, htight, fun _ _ h => Or.inl h,
      List.Sublist.refl _, fun _ h _ => h, fun M hM _ => by
        have := hM.length_le; omega⟩
  push Not at hall
  have hends := ends_both (X := X) hC hrot hA hB
  -- the first vertex `t` not on both sides, after the prefix `L₁ y`
  obtain ⟨M₁, t, R, hsupp₀, ht, hM₁⟩ := exists_first_of_exists
    (fun v => ¬ (IsOnSide G X {x | x ∈ A} v ∧ IsOnSide G X {x | x ∈ B} v)) P.support
    (by obtain ⟨v, hv, h⟩ := hall; exact ⟨v, hv, fun h' => h h'.1 h'.2⟩)
  have hhead : P.support.head? = some a := by rw [← Walk.cons_tail_support]; rfl
  have hlast : P.support.getLast? = some b := by
    rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
  obtain ⟨L₁, y, rfl⟩ : ∃ L₁ y, M₁ = L₁ ++ [y] := by
    rcases M₁.eq_nil_or_concat with h | ⟨L, y, h⟩
    · subst h
      rw [hsupp₀] at hhead
      simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hhead
      exact absurd (hhead ▸ hends.1) ht
    · exact ⟨L, y, by simpa using h⟩
  have hpre : ∀ v ∈ L₁ ++ [y], IsOnSide G X {x | x ∈ A} v ∧ IsOnSide G X {x | x ∈ B} v :=
    fun v hv => not_not.mp (hM₁ v hv)
  have hy := hpre y (by simp)
  have hbt : b ≠ t := fun h => ht (h ▸ hends.2)
  have hbR : b ∈ R := mem_of_getLast (hsupp₀ ▸ hlast) hbt
  have hlen : ∀ {N s L₂}, P.support = L₁ ++ y :: N ++ s :: L₂ → N ≠ [] →
      (L₁ ++ y :: s :: L₂).length < n := fun {N s L₂} h hN => by
    rw [← hn, h]
    obtain ⟨m, M, rfl⟩ := List.exists_cons_of_ne_nil hN
    simp
  have hsubX : ∀ {H : SimpleGraph V} (hle : G ≤ H) {P' : H.Walk a b},
      P'.support.Sublist P.support → ∀ v ∈ P'.support,
        IsSided H {x | x ∈ C ∨ x ∈ P'.support} A B v := by
    intro H hle P' hsub v hv
    have hX' : {x | x ∈ C ∨ x ∈ P'.support} ⊆ X := fun x hx => hx.imp id (fun h => hsub.subset h)
    rcases hsided v (hsub.subset hv) with h | h
    · exact Or.inl (h.mono hle hX')
    · exact Or.inr (h.mono hle hX')
  have edges_step : ∀ {s : V} {L₂ : List V} {H : SimpleGraph V} {P' : (G ⊔ edge y s).Walk a b}
      {P'' : H.Walk a b}, P'.support = L₁ ++ y :: s :: L₂ →
      (∀ v ∈ L₁ ++ [y, s],
        IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ A} v ∧
        IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ B} v) →
      (∀ u v, H.Adj u v → (G ⊔ edge y s).Adj u v ∨ IsListEdge P''.support u v) →
      (∀ M, M <+: P'.support → (∀ v ∈ M,
        IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ A} v ∧
        IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ B} v) →
        M <+: P''.support) →
      ∀ u v, H.Adj u v → G.Adj u v ∨ IsListEdge P''.support u v := by
    intro s L₂ H P' P'' hP's hboth hedge hpref u v huv
    rcases hedge u v huv with (h | h) | h
    · exact Or.inl h
    · have hys : IsListEdge P''.support y s :=
        isListEdge_of_prefix (hpref _ (by rw [hP's]; exact ⟨L₂, by simp⟩) hboth)
      rw [edge_adj] at h
      rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr hys
      · exact Or.inr hys.symm
    · exact Or.inr h
  -- a prefix of `P` on both sides is a prefix of `L₁ y`, since `t` is not on both sides
  have prefix_short : ∀ {Q : List V}, P.support = L₁ ++ [y] ++ t :: Q → ∀ M, M <+: P.support →
      (∀ v ∈ M, IsOnSide G X {x | x ∈ A} v ∧ IsOnSide G X {x | x ∈ B} v) → M <+: L₁ ++ [y] :=
    fun hsQ M hM hMb => prefix_of_not_mem (hsQ ▸ hM) (fun htM => ht (hMb t htM))
  have prefix_step : ∀ {Q : List V} {s : V} {L₂ : List V} {H : SimpleGraph V}
      {P' : (G ⊔ edge y s).Walk a b} {P'' : H.Walk a b}, P.support = L₁ ++ [y] ++ t :: Q →
      P'.support = L₁ ++ y :: s :: L₂ → P'.support.Sublist P.support →
      (∀ M, M <+: P'.support → (∀ v ∈ M,
        IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ A} v ∧
        IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ B} v) →
        M <+: P''.support) →
      ∀ M, M <+: P.support → (∀ v ∈ M,
        IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v ∧
        IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v) → M <+: P''.support := by
    intro Q s L₂ H P' P'' hsQ hP's hsub' hpref M hM hMb
    have hM₀ : M <+: L₁ ++ [y] := prefix_short hsQ M hM hMb
    refine hpref M (hM₀.trans (by rw [hP's]; exact ⟨s :: L₂, by simp⟩)) fun v hv => ?_
    have hX' : {x | x ∈ C ∨ x ∈ P'.support} ⊆ {x | x ∈ C ∨ x ∈ P.support} :=
      fun x hx => hx.imp id (fun h => hsub'.subset h)
    exact ⟨(hMb v hv).1.mono le_sup_left hX', (hMb v hv).2.mono le_sup_left hX'⟩
  -- the count: the prefix `L₁ y s` of the new path is on both sides
  have count_step : ∀ {Q : List V} {s : V} {L₂ : List V} {H : SimpleGraph V}
      {P' : (G ⊔ edge y s).Walk a b} {P'' : H.Walk a b} {n₁ n₂ : ℕ},
      P.support = L₁ ++ [y] ++ t :: Q → P'.support = L₁ ++ y :: s :: L₂ →
      (∀ v ∈ L₁ ++ [y, s],
        IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ A} v ∧
        IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ B} v) →
      (∀ M, M <+: P'.support → (∀ v ∈ M,
        IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ A} v ∧
        IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ B} v) →
        n₁ + M.length ≤ n₂ + 1 + P''.support.length) →
      ∀ M, M <+: P.support → (∀ v ∈ M,
        IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v ∧
        IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v) →
        n₁ + M.length ≤ n₂ + P''.support.length := by
    intro Q s L₂ H P' P'' n₁ n₂ hsQ hP's hboth hcount M hM hMb
    have h1 := hcount _ (by rw [hP's]; exact ⟨L₂, by simp⟩) hboth
    have h2 := (prefix_short hsQ M hM hMb).length_le
    simp only [List.length_append, List.length_cons, List.length_nil] at h1 h2
    omega
  rcases hsided t (by rw [hsupp₀]; simp) with htA | htB
  · -- `t` is on side `A` only: `y_s` is the first vertex after it on side `B`
    have htB : ¬ IsOnSide G X {x | x ∈ B} t := fun h => ht ⟨htA, h⟩
    obtain ⟨N', s, L₂, rfl, hsB, hN'⟩ := exists_first_of_exists
      (fun v => IsOnSide G X {x | x ∈ B} v) R ⟨b, hbR, hends.2.2⟩
    have hsupp : P.support = L₁ ++ y :: (t :: N') ++ s :: L₂ := by rw [hsupp₀]; simp
    have hNB : ∀ v ∈ t :: N', ¬ IsOnSide G X {x | x ∈ B} v := fun v hv => by
      rcases List.mem_cons.mp hv with rfl | hv
      · exact htB
      · exact hN' v hv
    let step : AddedEdgeStep V C A B a b k :=
      ⟨G, y, s, L₁, t :: N', L₂, P, hC, hrot, hP, hsupp, hind, hsep, htight,
        Or.inl ⟨hy.2, hsB, hNB⟩⟩
    have hsafe := strip_safe hC hrot hP hsupp hind htight hy.2 hsB hNB
    obtain ⟨P', hP', hP's, hboth⟩ := lemma_5_4_sides hrot hP hsupp hpre
      (Or.inr ⟨t, by simp, htA⟩) (Or.inl hsB)
    obtain ⟨hind', hsep', htight'⟩ := loop_invariant hrot hP hsupp hind htight hsep hNB hP's
    have hsub : P'.support.Sublist P.support := by rw [hP's, hsupp]; exact sublist_collapse
    obtain ⟨H, t3, hle, hcr, P'', h1, h2, h3, h4, h5, hedge, hsub', hpref, hcount⟩ :=
      ih _ (hP's ▸ hlen hsupp (by simp)) (G ⊔ edge y s) P' rfl
      (hC.mono le_sup_left) hP' hind' hsep' htight'
      (hsubX le_sup_left hsub) G₀ (.snoc step (Classical.decRel _) c)
    exact ⟨H, t3, le_sup_left.trans hle, fun h => hsafe (hcr h), P'', h1, h2, h3, h4, h5,
      edges_step hP's hboth hedge hpref, hsub'.trans hsub,
      prefix_step hsupp₀ hP's hsub hpref, count_step hsupp₀ hP's hboth hcount⟩
  · -- `t` is on side `B` only: `y_s` is the first vertex after it on side `A`
    have htA : ¬ IsOnSide G X {x | x ∈ A} t := fun h => ht ⟨h, htB⟩
    obtain ⟨N', s, L₂, rfl, hsA, hN'⟩ := exists_first_of_exists
      (fun v => IsOnSide G X {x | x ∈ A} v) R ⟨b, hbR, hends.2.1⟩
    have hsupp : P.support = L₁ ++ y :: (t :: N') ++ s :: L₂ := by rw [hsupp₀]; simp
    have hNA : ∀ v ∈ t :: N', ¬ IsOnSide G X {x | x ∈ A} v := fun v hv => by
      rcases List.mem_cons.mp hv with rfl | hv
      · exact htA
      · exact hN' v hv
    let step : AddedEdgeStep V C A B a b k :=
      ⟨G, y, s, L₁, t :: N', L₂, P, hC, hrot, hP, hsupp, hind, hsep, htight,
        Or.inr ⟨hy.1, hsA, hNA⟩⟩
    have hsafe := strip_safe_rev hC hrot hP hsupp hind htight hy.1 hsA hNA
    obtain ⟨P', hP', hP's, hboth⟩ := lemma_5_4_sides hrot hP hsupp hpre (Or.inl hsA)
      (Or.inr ⟨t, by simp, htB⟩)
    obtain ⟨hind', hsep', htight'⟩ := loop_invariant_rev hrot hP hsupp hind htight hsep hNA hP's
    have hsub : P'.support.Sublist P.support := by rw [hP's, hsupp]; exact sublist_collapse
    obtain ⟨H, t3, hle, hcr, P'', h1, h2, h3, h4, h5, hedge, hsub', hpref, hcount⟩ :=
      ih _ (hP's ▸ hlen hsupp (by simp)) (G ⊔ edge y s) P' rfl
      (hC.mono le_sup_left) hP' hind' hsep' htight'
      (hsubX le_sup_left hsub) G₀ (.snoc step (Classical.decRel _) c)
    exact ⟨H, t3, le_sup_left.trans hle, fun h => hsafe (hcr h), P'', h1, h2, h3, h4, h5,
      edges_step hP's hboth hedge hpref, hsub'.trans hsub,
      prefix_step hsupp₀ hP's hsub hpref, count_step hsupp₀ hP's hboth hcount⟩

/-! ### The whole completion, with its steps -/

/-- **The completion, as data for the extraction.** Let `C = a A b B` (up to rotation) be a cycle
with `A`, `B` nonempty, and let `P` be an induced `C`-path from `a` to `b` that separates `A` from
`B`. Then either `C` is crossed, or the completion gives:

* a `T2Chain` `t2` of collapse steps from `G` to a graph `G₂`;
* an `AddedEdgeChain` `t3` of loop steps from `G₂` to a graph `H_full`;
* the graph `H` of the kept edges: an edge of `H` is an edge of `G` or an edge of `H_full` with both
  ends on the final path `P'`. So `G ≤ H ≤ H_full`;
* a `C`-path `P'` of `H` from `a` to `b` with the hypotheses of `extractCrossingTwoPart_isSome`
  (induced, tight, separating, all vertices on both sides in `G`, every edge of `H` outside `G` a
  list edge of `P'`), and `t3.length < |P'|`. -/
theorem completion_chain [Finite V] {G : SimpleGraph V} (hC : IsCycleList G C)
    (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ []) (hB : B ≠ []) {P : G.Walk a b}
    (hP : IsTPath G C P)
    (hind : ∀ x ∈ P.support, ∀ y ∈ P.support, G.Adj x y → IsListEdge P.support x y)
    (hsep : Separates G {x | x ∈ P.support} {x | x ∈ A} {x | x ∈ B}) :
    IsCrossed G C ∨ ∃ (G₂ H_full : SimpleGraph V) (_ : T2Chain V C A B a b k G G₂)
      (t3 : AddedEdgeChain V C A B a b k G₂ H_full) (H : SimpleGraph V),
      G ≤ H ∧ H ≤ H_full ∧
      ∃ P' : H.Walk a b,
        (∀ u v, H.Adj u v ↔ G.Adj u v ∨ (H_full.Adj u v ∧ u ∈ P'.support ∧ v ∈ P'.support)) ∧
        IsTPath H C P' ∧
        OnBothSidesList G C A B P'.support ∧
        Separates G {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} ∧
        Separates H {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} ∧
        (∀ u ∈ P'.support, ∀ v ∈ P'.support, H.Adj u v → IsListEdge P'.support u v) ∧
        IsTight H C A B P'.support ∧
        (∀ u v, H.Adj u v → G.Adj u v ∨ IsListEdge P'.support u v) ∧
        t3.length < P'.support.length := by
  rcases reroute_all hrot hC.2.1 _ P rfl hP hind hsep with h | ⟨P₁, hP₁, hind₁, hsep₁, hwt₁⟩
  · exact Or.inl h
  right
  obtain ⟨G₂, t2, hle₂, -, P₂, hP₂, hind₂, hsep₂, ht₂, hsd₂, hsub₂, hconn₂⟩ :=
    collapse_all_chain hrot hA hB _ G P₁ rfl hC hP₁ hind₁ hsep₁ hwt₁ G .nil
  obtain ⟨H, t3, hle, -, P', hP', hboth, hsep', hind', ht', hedge, hsub', -, hcount⟩ :=
    complete_loop_chain hrot hA hB _ G₂ P₂ rfl (hC.mono hle₂) hP₂ hind₂ hsep₂ ht₂ hsd₂ G₂ .nil
  have hlen : t3.length < P'.support.length := by
    have ha := (ends_both (X := {x | x ∈ C ∨ x ∈ P₂.support}) (hC.mono hle₂) hrot hA hB).1
    have h := hcount [a] ⟨P₂.support.tail, Walk.cons_tail_support P₂⟩
      (fun v hv => by rw [List.mem_singleton.mp hv]; exact ha)
    simp only [AddedEdgeChain.length, List.length_singleton] at h
    omega
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
  have htH' : IsTight H' C A B P₀.support := by
    rw [hP₀s]
    intro u huC huP' hnAB
    have hnAB' : ¬ IsConnectedAvoiding H X' u {x | x ∈ A ∨ x ∈ B} := fun h =>
      hnAB (((hconn u _ (Or.inl huP')).2).mpr (((hconn u _ (Or.inl huP')).1).mp h))
    obtain ⟨v, w, hvw, hall⟩ := ht' u huC huP' hnAB'
    refine ⟨v, w, hvw, fun p hp hup => hall p hp ?_⟩
    exact ((hconn u {p} (Or.inl huP')).1).mpr (((hconn u {p} (Or.inl huP')).2).mp hup)
  have hsepH' : Separates H' {v | v ∈ P₀.support} {v | v ∈ A} {v | v ∈ B} := by
    intro u hu w hw p
    rw [hP₀s]
    obtain ⟨v, hv, hvP'⟩ := hsep' u hu w hw (p.mapLe hH'H)
    exact ⟨v, by simpa using hv, hvP'⟩
  refine ⟨G₂, H, t2, t3, H', hGH', hH'H, P₀, fun u v => by rw [hP₀s]; rfl, hP₀, hbothG,
    fun u hu w hw p => by
      simpa [Walk.support_mapLe_eq_support] using hsepH' u hu w hw (p.mapLe hGH'), hsepH', ?_, htH', hedge', hP₀s ▸ hlen⟩
  intro u hu v hv huv
  rw [hP₀s] at hu hv ⊢
  exact hind' u hu v hv (hH'H huv)

/-- **The search bound in terms of the final path.** When `t3` has fewer steps than the vertex list
`P_supp` has entries (as `completion_chain` gives for `P_supp = P'.support`),
`extractCrossingTwoPart` makes at most `72 |P'|` searches. -/
theorem extractCrossingTwoPart_searches_le_length [DecidableEq V] [WalkSearch V]
    {G H G₂ H_full : SimpleGraph V} [DecidableRel H.Adj] {m : List V} (verts P_supp : List V)
    (hle : H ≤ H_full) (t2 : T2Chain V C A B a b k G G₂)
    (t3 : AddedEdgeChain V C A B a b k G₂ H_full) (hlen : t3.length < P_supp.length)
    (subCr : CrossingWalks (restrict H (sideSetOf G (a :: m ++ [b]) A)) (a :: A ++ b :: m.reverse) ⊕
      CrossingWalks (restrict H (sideComplOf G (a :: m ++ [b]) A)) (b :: B ++ a :: m)) :
    (extractCrossingTwoPart verts C P_supp hle t2 t3 subCr).2 ≤ 72 * P_supp.length := by
  have h := extractCrossingTwoPart_searches_le verts P_supp hle t2 t3 subCr
  omega

end GraphMinor.HP25
