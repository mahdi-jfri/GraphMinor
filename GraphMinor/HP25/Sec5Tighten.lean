module

public import GraphMinor.HP25.Sec5Complete
public import GraphMinor.HP25.Sec5Reroute
import GraphMinor.HP25.CycleEdges
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Prop36
import GraphMinor.HP25.Sec5Lemma54

/-!
# The whole completion loop, from any induced separating `C`-path

Line 5 of Algorithm 5.1 of Humeau and Pous (page 18) takes "a C-path between non-consecutive
vertices of C", and Algorithm 5.2 (page 23) then adds the edges of Lemma 5.4 until every vertex of the
path is on both sides. Our correction of Lemma 5.4 needs the path to be tight (see the correction to
Lemma 5.4 in `corrections/HP25.md`). This file makes it tight in two steps and then runs the loop.

* **Rerouting** (`reroute_step`, `reroute_all`), with no new edge. Let `w` lie in a component of the
  third kind, with first and last neighbours `u` and `v` on `P`, and let some vertex strictly between
  them be on a side. If the stretch between them has a vertex on each side, then `C` is crossed.
  Otherwise we replace the stretch by an induced path through the component. The new path is still
  induced and separating, and its live set (`liveSet`) grows, so this stops. At the end the path is
  weakly tight.
* **Edges for runs on no side** (`collapse_all`, in `Sec5Collapse.lean`).
* **The loop of Algorithm 5.2** (`complete_loop`, in `Sec5Complete.lean`).

The result is `completion_loop`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-! ### The span of a component on the path -/

/-- If `t` lies strictly between two entries with property `Q`, then the list splits as
`L₁ u N v L₂` with `u` the first and `v` the last entry with `Q`, and `t ∈ N`. -/
theorem exists_span (Q : V → Prop) {l : List V} {p t q : V} (h : [p, t, q].Sublist l) (hp : Q p)
    (hq : Q q) : ∃ L₁ u N v L₂, l = L₁ ++ u :: N ++ v :: L₂ ∧ Q u ∧ Q v ∧ t ∈ N ∧
      (∀ x ∈ L₁, ¬ Q x) ∧ ∀ x ∈ L₂, ¬ Q x := by
  obtain ⟨L₁, u, R, rfl, hu, hL₁⟩ := exists_first_of_exists Q l ⟨p, h.subset (by simp), hp⟩
  have htq : [t, q].Sublist R := by
    obtain ⟨l₁, l₂, he, h₁, h₂⟩ := List.sublist_append_iff.mp h
    rcases l₁ with _ | ⟨x, l₁⟩
    · simp only [List.nil_append] at he
      subst he
      rcases List.sublist_cons_iff.mp h₂ with h₂ | ⟨r, hr, h₂⟩
      · exact (List.sublist_cons_self _ _).trans h₂
      · simp only [List.cons.injEq] at hr
        exact hr.2 ▸ h₂
    · simp only [List.cons_append, List.cons.injEq] at he
      exact absurd (he.1 ▸ hp) (hL₁ x (h₁.subset (by simp)))
  obtain ⟨M₂, v, R', hR, hv, hM₂⟩ := exists_first_of_exists Q R.reverse
    ⟨q, by simpa using htq.subset (by simp), hq⟩
  have hR' : R = R'.reverse ++ v :: M₂.reverse := by
    rw [← List.reverse_reverse R, hR]; simp
  have hL₂ : ∀ x ∈ M₂.reverse, ¬ Q x := fun x hx => hM₂ x (by simpa using hx)
  refine ⟨L₁, u, R'.reverse, v, M₂.reverse, by rw [hR']; simp, hu, hv, ?_, hL₁, hL₂⟩
  rw [hR'] at htq
  obtain ⟨l₁, l₂, he, h₁, h₂⟩ := List.sublist_append_iff.mp htq
  rcases l₁ with _ | ⟨x, l₁⟩
  · simp only [List.nil_append] at he
    subst he
    rcases List.sublist_cons_iff.mp h₂ with h₂ | ⟨r, hr, h₂⟩
    · exact absurd hq (hL₂ q (h₂.subset (by simp)))
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact absurd hq (hL₂ q (h₂.subset (by simp)))
  · simp only [List.cons_append, List.cons.injEq] at he
    exact he.1 ▸ h₁.subset (by simp)

/-! ### Components -/

variable {X S : Set V} {w : V}

/-- A neighbour of a vertex of the component of `w` in `G - X` is joined to `w` avoiding `X`. -/
theorem isConnectedAvoiding_adj {m p : V} (hm : IsConnectedAvoiding G X w {m})
    (hmX : m ∉ X) (hmp : G.Adj m p) : IsConnectedAvoiding G X w {p} := by
  obtain ⟨m', rfl, q, -, hin⟩ := hm
  refine isConnectedAvoiding_of_walk (q.concat hmp) fun x hx hxX => ?_
  rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · by_cases h1 : x = w
    · exact Or.inl h1
    by_cases h2 : x = m'
    · exact absurd (h2 ▸ hxX) hmX
    · exact absurd hxX (hin x hx h1 h2)
  · exact Or.inr rfl

/-- If a vertex of the component of `w` in `G - X` is joined to `S` avoiding `X`, so is `w`. -/
theorem isConnectedAvoiding_trans {m : V} (hm : IsConnectedAvoiding G X w {m})
    (hmX : m ∉ X) (h : IsConnectedAvoiding G X m S) : IsConnectedAvoiding G X w S := by
  obtain ⟨m', rfl, q, -, hin⟩ := hm
  obtain ⟨z, hz, r, -, hin'⟩ := h
  refine isConnectedAvoiding_of_walk_mem hz (q.append r) fun x hx hxX => ?_
  rw [Walk.mem_support_append_iff] at hx
  by_cases h1 : x = w
  · exact Or.inl h1
  by_cases h2 : x = z
  · exact Or.inr h2
  by_cases h3 : x = m'
  · exact absurd (h3 ▸ hxX) hmX
  rcases hx with hx | hx
  · exact absurd hxX (hin x hx h1 h3)
  · exact absurd hxX (hin' x hx h3 h2)

/-- Every vertex `x` of a path from `w` to `u` whose inner vertices miss `X` is joined to `w`
avoiding `X`. -/
theorem isConnectedAvoiding_of_mem_path [DecidableEq V] {u : V} {p : G.Walk w u} (hp : p.IsPath)
    (hin : ∀ y ∈ p.support, y ≠ w → y ≠ u → y ∉ X) {x : V} (hx : x ∈ p.support) (hxu : x ≠ u) :
    IsConnectedAvoiding G X w {x} := by
  refine IsConnectedAvoiding.symm' (isConnectedAvoiding_tail (p := p.reverse) hp.reverse (S := {w}) (mem_singleton w)
    (fun y hy h1 h2 => hin y (by simpa using hy) h2 h1) (by simpa using hx) hxu)

/-! ### One rerouting step -/

variable {C A B : List V} {a b : V} {k : ℕ}

/-- **One rerouting step.** Let `P` be an induced `C`-path that separates `A` from `B` and is not
weakly tight: some component of the third kind (the one of `w`) has neighbours `p` and `q` on `P`
with a sided vertex `t` strictly between them. Let `u` and `v` be the first and the last neighbours
of the component on `P`, and let `N` be the stretch between them, so `t ∈ N`. If some vertex of `N`
is on side `A` and some vertex of `N` is on side `B`, then `C` is crossed (`reroute_crossed`).
Otherwise we replace `N` by the inner vertices of an induced path from `u` to `v` through the
component. The new path is induced and separates, and its live set is strictly larger. -/
theorem reroute_step (hrot : C.rotate k = a :: A ++ b :: B) (hCnd : C.Nodup) {P : G.Walk a b}
    (hP : IsTPath G C P)
    (hind : ∀ x ∈ P.support, ∀ y ∈ P.support, G.Adj x y → IsListEdge P.support x y)
    (hsep : Separates G {x | x ∈ P.support} {x | x ∈ A} {x | x ∈ B})
    (hnwt : ¬ IsWeaklyTight G C A B P.support) :
    IsCrossed G C ∨ ∃ P' : G.Walk a b, IsTPath G C P' ∧
      (∀ x ∈ P'.support, ∀ y ∈ P'.support, G.Adj x y → IsListEdge P'.support x y) ∧
      Separates G {x | x ∈ P'.support} {x | x ∈ A} {x | x ∈ B} ∧
      liveSet G A B P.support ⊂ liveSet G A B P'.support := by
  classical
  set X : Set V := {x | x ∈ C ∨ x ∈ P.support} with hX
  simp only [IsWeaklyTight, not_forall] at hnwt
  obtain ⟨w, hwC, hwl, hwd, p, q, t, hp, hq, hpt, hts⟩ := hnwt
  have hwX : w ∉ X := fun h => h.elim hwC hwl
  -- the first and last neighbours `u`, `v` of the component on `P`
  obtain ⟨L₁, u, N, v, L₂, hsupp, hu, hv, htN, hL₁, hL₂⟩ :=
    exists_span (fun x => IsConnectedAvoiding G X w {x}) hpt hp hq
  have hnd : (L₁ ++ u :: N ++ v :: L₂).Nodup := hsupp ▸ hP.1.support_nodup
  have huv : u ≠ v := by
    intro h
    subst h
    simp [List.nodup_append] at hnd
  obtain ⟨u', hu', p₁, hp₁, hin₁⟩ := hu
  obtain ⟨v', hv', p₂, hp₂, hin₂⟩ := hv
  rw [mem_singleton_iff] at hu' hv'
  subst hu' hv'
  -- the vertices of the walk `u ~ w ~ v` other than `u`, `v` lie in the component of `w`
  set W₀ : G.Walk u' v' := p₁.reverse.append p₂ with hW₀
  have hW₀mem : ∀ x ∈ W₀.support, x ≠ u' → x ≠ v' → x ∉ X ∧ IsConnectedAvoiding G X w {x} := by
    intro x hx hxu hxv
    rw [hW₀, Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hx
    have hxX : ∀ {z} {r : G.Walk w z}, (∀ y ∈ r.support, y ≠ w → y ≠ z → y ∉ X) →
        x ∈ r.support → x ≠ z → x ∉ X := fun {z r} hin hxr hxz => by
      by_cases hxw : x = w
      · exact hxw ▸ hwX
      · exact hin x hxr hxw hxz
    rcases hx with hx | hx
    · exact ⟨hxX hin₁ hx hxu, isConnectedAvoiding_of_mem_path hp₁ hin₁ hx hxu⟩
    · exact ⟨hxX hin₂ hx hxv, isConnectedAvoiding_of_mem_path hp₂ hin₂ hx hxv⟩
  -- an induced path through the component
  have hPL : IsPathList G univ W₀.bypass.support :=
    ⟨W₀.bypass_isPath.support_nodup, W₀.bypass.isChain_adj_support, fun _ _ => trivial⟩
  obtain ⟨l', hPL', hhead, hlast, hsub, hWind⟩ := exists_induced _ _ le_rfl hPL
  have hhead' : l'.head? = some u' := by rw [hhead, ← Walk.cons_tail_support]; rfl
  have hlast' : l'.getLast? = some v' := by
    rw [hlast, List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
  obtain ⟨W, hWs⟩ := exists_walk_of_chain l' hPL'.2.1 hhead' hlast'
  have hWp : W.IsPath := by rw [Walk.isPath_def, hWs]; exact hPL'.1
  obtain ⟨M, hWM⟩ : ∃ M, W.support = u' :: M ++ [v'] := by
    obtain ⟨T, hT⟩ : ∃ T, W.support = u' :: T := ⟨W.support.tail, W.cons_tail_support.symm⟩
    rcases T.eq_nil_or_concat with rfl | ⟨M, z, rfl⟩
    · have := W.getLast_support
      simp only [hT, List.getLast_singleton] at this
      exact absurd this huv
    · refine ⟨M, ?_⟩
      have := W.getLast_support
      simp only [hT, List.concat_eq_append, ← List.cons_append, List.getLast_append_singleton]
        at this
      rw [hT, this]
      simp
  have hMmem : ∀ m ∈ M, m ∉ X ∧ IsConnectedAvoiding G X w {m} := by
    intro m hm
    have hnd' : (u' :: M ++ [v']).Nodup := hWM ▸ hWp.support_nodup
    have hmW : m ∈ W₀.support := W₀.support_bypass_subset_support (hsub m (by
      rw [← hWs, hWM]; simp [hm]))
    refine hW₀mem m hmW (fun h => ?_) (fun h => ?_)
    · subst h; simp [hm] at hnd'
    · rw [h] at hm
      simp [List.nodup_append] at hnd'
      exact hnd'.2.2 _ hm rfl
  have hM : IsDeadList G C A B P M := fun m hm =>
    ⟨fun h => (hMmem m hm).1 (Or.inl h), fun h => (hMmem m hm).1 (Or.inr h),
      fun h => hwd (isConnectedAvoiding_trans (hMmem m hm).2 (hMmem m hm).1 h)⟩
  have hspan : ∀ m ∈ M, ∀ x ∈ L₁ ++ L₂, ¬ G.Adj m x := by
    intro m hm x hx hmx
    have hx' := isConnectedAvoiding_adj (hMmem m hm).2 (hMmem m hm).1 hmx
    rcases List.mem_append.mp hx with hx | hx
    · exact hL₁ x hx hx'
    · exact hL₂ x hx hx'
  have hWind' : ∀ x ∈ W.support, ∀ y ∈ W.support, G.Adj x y → IsListEdge W.support x y := by
    rw [hWs]; exact hWind
  -- the sided vertex `t`
  have htsided : IsOnSide G X {x | x ∈ A} t ∨ IsOnSide G X {x | x ∈ B} t := by tauto
  by_cases hcr : (∃ t₁ ∈ N, IsOnSide G X {x | x ∈ A} t₁) ∧ ∃ t₂ ∈ N, IsOnSide G X {x | x ∈ B} t₂
  · obtain ⟨⟨t₁, ht₁, h₁⟩, ⟨t₂, ht₂, h₂⟩⟩ := hcr
    exact Or.inl (reroute_crossed hrot hCnd hP hsupp hWp hWM hM ht₁ ht₂ h₁ h₂)
  right
  obtain ⟨P', hP', hs⟩ := exists_reroute_path hP hsupp hWp hWM hM
  have hl' : ∀ x ∈ P.support, x ∉ P'.support → x ∈ N := fun x hx hx' => by
    rw [hsupp] at hx
    rw [hs] at hx'
    simp only [List.mem_append, List.mem_cons] at hx hx'
    tauto
  have hCUW : ∀ x ∈ C, x ∉ P.support → x ∈ {x | x ∈ A} ∨ x ∈ {x | x ∈ B} :=
    fun x hx hxP => mem_arcs_of_mem_C hrot hx hxP
  have hAC : ∀ x ∈ {x | x ∈ A}, x ∈ C := fun x hx =>
    List.mem_rotate.mp (by rw [hrot]; simp [show x ∈ A from hx])
  have hBC : ∀ x ∈ {x | x ∈ B}, x ∈ C := fun x hx =>
    List.mem_rotate.mp (by rw [hrot]; simp [show x ∈ B from hx])
  refine ⟨P', hP', reroute_induced hP hsupp hind (List.ne_nil_of_mem htN) hWM hWind' hspan hs,
    ?_, ?_⟩
  · by_cases hNB : ∀ t ∈ N, ¬ IsOnSide G X {x | x ∈ B} t
    · exact separates_of_reroute hP hsupp hCUW hBC hsep hNB hl'
    · have hNA : ∀ t ∈ N, ¬ IsOnSide G X {x | x ∈ A} t := fun t₁ ht₁ h₁ => by
        push Not at hNB
        exact hcr ⟨⟨t₁, ht₁, h₁⟩, hNB⟩
      exact (separates_of_reroute hP hsupp (fun x hx hxP => (hCUW x hx hxP).symm) hAC hsep.symm'
        hNA hl').symm'
  · rw [hs]
    refine liveSet_reroute hrot hP hsupp hM htN ?_
    rcases htsided with ⟨z, hz, r, hr, hin⟩ | ⟨z, hz, r, hr, hin⟩
    · exact ⟨z, Or.inl hz, r, hr, hin⟩
    · exact ⟨z, Or.inr hz, r, hr, hin⟩

/-- **Rerouting until weakly tight.** Repeat `reroute_step`. The number of vertices outside the live
set drops at each step, so the rerouting stops, with `C` crossed or with an induced, separating,
weakly tight `C`-path. -/
theorem reroute_all [Finite V] (hrot : C.rotate k = a :: A ++ b :: B) (hCnd : C.Nodup) :
    ∀ (n : ℕ) (P : G.Walk a b), (liveSet G A B P.support)ᶜ.ncard = n → IsTPath G C P →
      (∀ x ∈ P.support, ∀ y ∈ P.support, G.Adj x y → IsListEdge P.support x y) →
      Separates G {x | x ∈ P.support} {x | x ∈ A} {x | x ∈ B} →
      IsCrossed G C ∨ ∃ P' : G.Walk a b, IsTPath G C P' ∧
        (∀ x ∈ P'.support, ∀ y ∈ P'.support, G.Adj x y → IsListEdge P'.support x y) ∧
        Separates G {x | x ∈ P'.support} {x | x ∈ A} {x | x ∈ B} ∧
        IsWeaklyTight G C A B P'.support := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hP hind hsep
  by_cases hwt : IsWeaklyTight G C A B P.support
  · exact Or.inr ⟨P, hP, hind, hsep, hwt⟩
  rcases reroute_step hrot hCnd hP hind hsep hwt with h | ⟨P', hP', hind', hsep', hlt⟩
  · exact Or.inl h
  · exact ih _ (hn ▸ Set.ncard_lt_ncard (compl_lt_compl_iff_lt.mpr hlt)) P' rfl hP' hind' hsep'

/-! ### Leaving out skipped edges and Observation 1 -/

/-- A walk of `H` that has at most one vertex in `l` is a walk of `G` with the same vertices when
every edge of `H \ G` has both ends in `l`. -/
theorem exists_walk_of_le_of_atMostOne {H : SimpleGraph V} {l : List V}
    (hH : ∀ x y, H.Adj x y → G.Adj x y ∨ (x ∈ l ∧ y ∈ l)) :
    ∀ {u v : V} (p : H.Walk u v),
      (∀ x ∈ p.support, ∀ y ∈ p.support, x ≠ y → ¬ (x ∈ l ∧ y ∈ l)) →
      ∃ q : G.Walk u v, q.support = p.support
  | _, _, .nil, _ => ⟨.nil, rfl⟩
  | u, _, .cons (v := w) h p, hat => by
    have hat' : ∀ x ∈ p.support, ∀ y ∈ p.support, x ≠ y → ¬ (x ∈ l ∧ y ∈ l) :=
      fun x hx y hy => hat x (List.mem_cons_of_mem u hx) y (List.mem_cons_of_mem u hy)
    obtain ⟨q, hq⟩ := exists_walk_of_le_of_atMostOne hH p hat'
    have hadj : G.Adj u w :=
      (hH u w h).resolve_right (hat u (by simp) w (by simp [p.start_mem_support]) (H.ne_of_adj h))
    exact ⟨.cons hadj q, by simp [hq]⟩

/-- **Observation 1: sides and attachments are witnessed in `G`.** If `G ≤ H` and every edge of
`H \ G` has both ends in `l`, then for any set `X` containing `l` and any `u`, `S` with `u ∉ l` or
`S` disjoint from `l`, `IsConnectedAvoiding H X u S ↔ IsConnectedAvoiding G X u S`: a path of `H`
with no inner vertex in `X` has at most one vertex in `l`, so it uses no edge of `H \ G`. -/
theorem isConnectedAvoiding_iff_of_adj_or_mem {H : SimpleGraph V} {l : List V} {X : Set V}
    (hle : G ≤ H) (hH : ∀ x y, H.Adj x y → G.Adj x y ∨ (x ∈ l ∧ y ∈ l))
    (hlX : ∀ x ∈ l, x ∈ X) {u : V} {S : Set V} (huS : u ∉ l ∨ ∀ s ∈ S, s ∉ l) :
    IsConnectedAvoiding H X u S ↔ IsConnectedAvoiding G X u S := by
  refine ⟨?_, fun h => h.mono hle subset_rfl⟩
  rintro ⟨s, hs, p, hp, hin⟩
  have hat : ∀ x ∈ p.support, ∀ y ∈ p.support, x ≠ y → ¬ (x ∈ l ∧ y ∈ l) := by
    rintro x hx y hy hxy ⟨hxl, hyl⟩
    have hxus : x = u ∨ x = s := by
      by_contra hne
      push Not at hne
      exact hin x hx hne.1 hne.2 (hlX x hxl)
    have hyus : y = u ∨ y = s := by
      by_contra hne
      push Not at hne
      exact hin y hy hne.1 hne.2 (hlX y hyl)
    rcases huS with hu | hS
    · rcases hxus with rfl | hxs <;> rcases hyus with rfl | hys
      exacts [hu hxl, hu hxl, hu hyl, hxy (hxs.trans hys.symm)]
    · rcases hxus with rfl | hxs <;> rcases hyus with rfl | hys
      exacts [hxy rfl, hS s hs (hys ▸ hyl), hS s hs (hxs ▸ hxl), hS s hs (hxs ▸ hxl)]
  obtain ⟨q, hq⟩ := exists_walk_of_le_of_atMostOne hH p hat
  exact ⟨s, hs, q, by rw [Walk.isPath_def, hq]; exact hp.support_nodup,
    fun x hx => hin x (hq ▸ hx)⟩

/-- Every vertex of a list `l` is on both `l`-sides in `G`. For `P : G.Walk a b`,
`OnBothSidesList G C A B P.support` is `OnBothSides G C A B P`. -/
@[expose] def OnBothSidesList (G : SimpleGraph V) (C A B l : List V) : Prop :=
  ∀ v ∈ l, IsOnSide G {x | x ∈ C ∨ x ∈ l} {x | x ∈ A} v ∧
    IsOnSide G {x | x ∈ C ∨ x ∈ l} {x | x ∈ B} v

/-- **Sides are witnessed in `G`.** If `G ≤ H` and every edge of `H \ G` has both ends on `P'`, then
`OnBothSides H C A B P' ↔ OnBothSidesList G C A B P'.support`. -/
theorem onBothSides_iff_of_adj_or_mem {H : SimpleGraph V} (hCnd : C.Nodup)
    (hrot : C.rotate k = a :: A ++ b :: B) {P' : H.Walk a b} (hP' : IsTPath H C P')
    (hle : G ≤ H) (hH : ∀ x y, H.Adj x y → G.Adj x y ∨ (x ∈ P'.support ∧ y ∈ P'.support)) :
    OnBothSides H C A B P' ↔ OnBothSidesList G C A B P'.support := by
  have hA : ∀ s ∈ {x | x ∈ A}, s ∉ P'.support :=
    fun s hs => notMem_support_of_arc hCnd hrot hP' (Or.inl hs)
  have hB : ∀ s ∈ {x | x ∈ B}, s ∉ P'.support :=
    fun s hs => notMem_support_of_arc hCnd hrot hP' (Or.inr hs)
  refine forall₂_congr fun v _ => and_congr ?_ ?_
  · exact isConnectedAvoiding_iff_of_adj_or_mem hle hH (fun _ h => Or.inr h) (Or.inr hA)
  · exact isConnectedAvoiding_iff_of_adj_or_mem hle hH (fun _ h => Or.inr h) (Or.inr hB)

/-- The graph obtained from `G` by keeping only the edges of `H` whose ends both lie in `l`. -/
@[expose] def keepEdges (G H : SimpleGraph V) (l : List V) : SimpleGraph V where
  Adj u v := G.Adj u v ∨ (H.Adj u v ∧ u ∈ l ∧ v ∈ l)
  symm := ⟨fun _ _ h => h.imp (fun h1 => h1.symm) fun ⟨h1, h2, h3⟩ => ⟨h1.symm, h3, h2⟩⟩
  loopless := ⟨fun u h => by rcases h with h | ⟨h1, _⟩; exacts [G.ne_of_adj h rfl, H.ne_of_adj h1 rfl]⟩

/-! ### The whole loop -/

/-- **The whole completion loop.** Let `C = a A b B` (up to rotation) be a cycle with `A`, `B`
nonempty, and let `P` be an induced `C`-path from `a` to `b` that separates `A` from `B`. Then either
`C` is crossed, or there is a graph `H ⊇ G` in which `C` is crossed only if it is crossed in `G`
(every added edge is safe), with a `C`-path `P'` from `a` to `b` that is induced, tight and
separating, all of whose vertices are on both sides in `H` and in `G`, and such that every added edge
of `H \ G` is a list edge of `P'` (the edges of `collapse_all` that a later edge of `complete_loop`
skips are left out). -/
theorem completion_loop [Finite V] (hC : IsCycleList G C) (hrot : C.rotate k = a :: A ++ b :: B)
    (hA : A ≠ []) (hB : B ≠ []) {P : G.Walk a b} (hP : IsTPath G C P)
    (hind : ∀ x ∈ P.support, ∀ y ∈ P.support, G.Adj x y → IsListEdge P.support x y)
    (hsep : Separates G {x | x ∈ P.support} {x | x ∈ A} {x | x ∈ B}) :
    IsCrossed G C ∨ ∃ H : SimpleGraph V, G ≤ H ∧ (IsCrossed H C → IsCrossed G C) ∧
      ∃ P' : H.Walk a b, IsTPath H C P' ∧ OnBothSides H C A B P' ∧
        OnBothSidesList G C A B P'.support ∧
        Separates H {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} ∧
        (∀ u ∈ P'.support, ∀ v ∈ P'.support, H.Adj u v → IsListEdge P'.support u v) ∧
        IsTight H C A B P'.support ∧
        ∀ u v, H.Adj u v → G.Adj u v ∨ IsListEdge P'.support u v := by
  rcases reroute_all hrot hC.2.1 _ P rfl hP hind hsep with h | ⟨P₁, hP₁, hind₁, hsep₁, hwt₁⟩
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
  refine ⟨H', hGH', fun h => hcr₂ (hcr (h.mono hH'H)), P₀, hP₀, hbothH', hbothG, ?_, ?_,
    htH', hedge'⟩
  · intro u hu w hw p
    rw [hP₀s]
    obtain ⟨v, hv, hvP'⟩ := hsep' u hu w hw (p.mapLe hH'H)
    exact ⟨v, by simpa using hv, hvP'⟩
  · intro u hu v hv huv
    rw [hP₀s] at hu hv ⊢
    exact hind' u hu v hv (hH'H huv)

/-- **The whole completion loop, for a crossless cycle.** From any induced, separating `C`-path
between non-consecutive vertices of a crossless `C`, the loop ends with a path all of whose vertices
are on both sides in `H` and in `G`, every added edge is on `P'`, and `C` stays crossless. -/
theorem completion_loop_of_not_crossed [Finite V] (hC : IsCycleList G C)
    (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ []) (hB : B ≠ []) (hnc : ¬ IsCrossed G C)
    {P : G.Walk a b} (hP : IsTPath G C P)
    (hind : ∀ x ∈ P.support, ∀ y ∈ P.support, G.Adj x y → IsListEdge P.support x y)
    (hsep : Separates G {x | x ∈ P.support} {x | x ∈ A} {x | x ∈ B}) :
    ∃ H : SimpleGraph V, G ≤ H ∧ ¬ IsCrossed H C ∧
      ∃ P' : H.Walk a b, IsTPath H C P' ∧ OnBothSides H C A B P' ∧
        OnBothSidesList G C A B P'.support ∧
        Separates H {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} ∧
        (∀ u ∈ P'.support, ∀ v ∈ P'.support, H.Adj u v → IsListEdge P'.support u v) ∧
        IsTight H C A B P'.support ∧
        ∀ u v, H.Adj u v → G.Adj u v ∨ IsListEdge P'.support u v := by
  rcases completion_loop hC hrot hA hB hP hind hsep with h | ⟨H, hle, hcr, rest⟩
  · exact absurd h hnc
  · exact ⟨H, hle, fun h => hnc (hcr h), rest⟩

end GraphMinor.HP25
