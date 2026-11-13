module

public import GraphMinor.HP25.Sec5Reroute
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Sec5Lemma54
import GraphMinor.HP25.Sec5StripTools
import GraphMinor.HP25.Lemma43Case1
import GraphMinor.HP25.Alternate

/-!
# Weakly tight paths and the edges of Claim 5.5

The rerouting of `Sec5Reroute.lean` makes a `C`-path *weakly tight* (`IsWeaklyTight`): for every
component of `G - (C ∪ P)` of the third kind (no neighbour in `A ∪ B`), every vertex of `P` strictly
between two of its neighbours on `P` is on no side. Rerouting alone cannot make a path tight, so
this file adds the edges of Claim 5.5 of Humeau and Pous (page 19):
for a stretch `y N z` of `P` with `y` and `z` on some side and every vertex of `N` on no side, the edge
`yz` is safe (the paper's argument: "As vertices $y_t$ with $j<t<r$ have no $P$-sides,
$\{y_j,y_r\}$ separates them from $C$"), which holds under weak tightness (`windowClosed_of_weaklyTight`,
then `claim_5_5_of`).

* `collapse_step`: the edge `yz` is safe, and the path `P y z P` of `G + yz` is a `C`-path that is
  induced, separating and weakly tight, and its vertices have the same sides as in `G`.
* `tight_of_weaklyTight`: a weakly tight path whose vertices are all on some side is tight.

"Strictly between" is written with sublists: `t` is strictly between `p` and `q` on `l` when
`[p, t, q]` is a sublist of `l`. This is kept by removing entries of `l`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-! ### Lists -/

/-- In a list without repetition, two entries do not occur in both orders. -/
theorem not_sublist_pair_swap : ∀ {l : List V}, l.Nodup → ∀ {x y : V}, [x, y].Sublist l →
    [y, x].Sublist l → False
  | [], _, _, _, h, _ => by simp at h
  | c :: l, hnd, x, y, h₁, h₂ => by
    rw [List.nodup_cons] at hnd
    rw [List.sublist_cons_iff] at h₁ h₂
    rcases h₁ with h₁ | ⟨r, hr, h₁⟩ <;> rcases h₂ with h₂ | ⟨r', hr', h₂⟩
    · exact not_sublist_pair_swap hnd.2 h₁ h₂
    · simp only [List.cons.injEq] at hr'
      obtain ⟨rfl, rfl⟩ := hr'
      exact hnd.1 (h₁.subset (by simp))
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact hnd.1 (h₂.subset (by simp))
    · simp only [List.cons.injEq] at hr hr'
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨rfl, -⟩ := hr'
      exact hnd.1 (h₁.subset (by simp))

/-- In a list without repetition, no entry lies strictly between two consecutive entries `y`, `z`. -/
theorem not_sublist_between {L₁ L₂ : List V} {y z p q t : V} (hnd : (L₁ ++ y :: z :: L₂).Nodup)
    (hp : p = y ∨ p = z) (hq : q = y ∨ q = z) (h : [p, t, q].Sublist (L₁ ++ y :: z :: L₂)) :
    False := by
  have hpq : [p, q].Sublist (L₁ ++ y :: z :: L₂) :=
    (List.Sublist.cons_cons p (List.Sublist.cons t (List.Sublist.refl [q]))).trans h
  have hpt : [p, t].Sublist (L₁ ++ y :: z :: L₂) :=
    (List.Sublist.cons_cons p (List.Sublist.cons_cons t (List.nil_sublist [q]))).trans h
  have htq : [t, q].Sublist (L₁ ++ y :: z :: L₂) := (List.Sublist.cons p (List.Sublist.refl _)).trans h
  have hyz : [y, z].Sublist (L₁ ++ y :: z :: L₂) :=
    (List.nil_sublist L₁).append (List.Sublist.cons_cons y (List.Sublist.cons_cons z
      (List.nil_sublist L₂)))
  have hne : ∀ x, ¬ [x, x].Sublist (L₁ ++ y :: z :: L₂) := List.nodup_iff_sublist.mp hnd
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact hne _ hpq
  · -- `t` strictly between `y` and `z`
    have ht : t ∈ L₁ ++ p :: q :: L₂ := hpt.subset (by simp)
    simp only [List.mem_append, List.mem_cons] at ht
    rcases ht with ht | rfl | rfl | ht
    · exact not_sublist_pair_swap hnd hpt ((List.singleton_sublist.mpr ht).append
        (List.Sublist.cons_cons p (List.nil_sublist _)))
    · exact hne _ hpt
    · exact hne _ htq
    · exact not_sublist_pair_swap hnd htq ((List.nil_sublist L₁).append (List.Sublist.cons p
        (List.Sublist.cons_cons q (List.singleton_sublist.mpr ht))))
  · exact not_sublist_pair_swap hnd hyz hpq
  · exact hne _ hpq

/-- The first entry of a list with a property. -/
theorem exists_first_of_exists (Q : V → Prop) :
    ∀ (l : List V), (∃ x ∈ l, Q x) → ∃ L₁ v R, l = L₁ ++ v :: R ∧ Q v ∧ ∀ x ∈ L₁, ¬ Q x
  | [], h => by simp at h
  | c :: l, h => by
    by_cases hc : Q c
    · exact ⟨[], c, l, rfl, hc, by simp⟩
    · obtain ⟨x, hx, hQ⟩ := h
      have hx' : x ∈ l := by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hQ hc
        · exact hx
      obtain ⟨L₁, v, R, rfl, hv, hL⟩ := exists_first_of_exists Q l ⟨x, hx', hQ⟩
      refine ⟨c :: L₁, v, R, rfl, hv, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hc
      · exact hL y hy

/-! ### Weak tightness -/

/-- A `C`-path with vertex list `l` (and arcs `A`, `B`) is *weakly tight* when, for every component
of `G - (C ∪ l)` with no neighbour in `A ∪ B`, every entry of `l` strictly between two of its
neighbours on `l` is on no side. As in `IsTight`, a vertex `w` off `C ∪ l` stands for its component. -/
@[expose] def IsWeaklyTight (G : SimpleGraph V) (C A B l : List V) : Prop :=
  ∀ w, w ∉ C → w ∉ l →
    ¬ IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ l} w {x | x ∈ A ∨ x ∈ B} →
    ∀ p q t, IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ l} w {p} →
      IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ l} w {q} → [p, t, q].Sublist l →
      ¬ IsOnSide G {x | x ∈ C ∨ x ∈ l} {x | x ∈ A} t ∧
        ¬ IsOnSide G {x | x ∈ C ∨ x ∈ l} {x | x ∈ B} t

/-- A vertex is *sided* when it is on side `A` or on side `B`. -/
@[expose] def IsSided (G : SimpleGraph V) (X : Set V) (A B : List V) (v : V) : Prop :=
  IsOnSide G X {x | x ∈ A} v ∨ IsOnSide G X {x | x ∈ B} v

variable {C A B L₁ N L₂ : List V} {a b y z : V} {k : ℕ} {P : G.Walk a b}

/-- **Weak tightness gives the window condition** for a stretch `y N z` with `y`, `z` sided: a
component of the third kind joined to a vertex of `N` and to a vertex of `P` outside `y N z` would
have `y` or `z` strictly between two of its neighbours. -/
theorem windowClosed_of_weaklyTight (hsupp : P.support = L₁ ++ y :: N ++ z :: L₂)
    (hwt : IsWeaklyTight G C A B P.support)
    (hy : IsSided G {x | x ∈ C ∨ x ∈ P.support} A B y)
    (hz : IsSided G {x | x ∈ C ∨ x ∈ P.support} A B z) : WindowClosed G C A B P y z N := by
  intro w hwC hwP hnAB m hm hwm p hp hwp
  by_contra hpw
  have hp' : p ∈ L₁ ++ y :: N ++ z :: L₂ := hsupp ▸ hp
  have hpw' : p ∈ L₁ ∨ p ∈ L₂ := by
    simp only [List.mem_append, List.mem_cons, List.cons_append, List.not_mem_nil, or_false]
      at hp' hpw
    tauto
  rcases hpw' with hpL | hpL
  · have hsub : [p, y, m].Sublist P.support := by
      rw [hsupp, show L₁ ++ y :: N ++ z :: L₂ = L₁ ++ (y :: (N ++ z :: L₂)) by simp]
      exact (List.singleton_sublist.mpr hpL).append (List.Sublist.cons_cons y
        (List.singleton_sublist.mpr (by simp [hm])))
    have := hwt w hwC hwP hnAB p m y hwp hwm hsub
    rcases hy with h | h
    · exact this.1 h
    · exact this.2 h
  · have hsub : [m, z, p].Sublist P.support := by
      rw [hsupp, show L₁ ++ y :: N ++ z :: L₂ = (L₁ ++ y :: N) ++ (z :: L₂) by simp]
      exact (List.singleton_sublist.mpr (by simp [hm])).append (List.Sublist.cons_cons z
        (List.singleton_sublist.mpr hpL))
    have := hwt w hwC hwP hnAB m p z hwm hwp hsub
    rcases hz with h | h
    · exact this.1 h
    · exact this.2 h

/-- **A weakly tight path whose vertices are all sided is tight.** Take the first neighbour `v` of a
component of the third kind on `l` and the next entry `w`; a later neighbour would put `w` strictly
between two neighbours. -/
theorem tight_of_weaklyTight {l : List V} (hlen : 2 ≤ l.length) (hwt : IsWeaklyTight G C A B l)
    (hs : ∀ v ∈ l, IsSided G {x | x ∈ C ∨ x ∈ l} A B v) : IsTight G C A B l := by
  classical
  intro w hwC hwl hnAB
  set X : Set V := {x | x ∈ C ∨ x ∈ l} with hX
  by_cases hatt : ∃ p ∈ l, IsConnectedAvoiding G X w {p}
  · obtain ⟨L₁, v, R, hl, hv, hL₁⟩ := exists_first_of_exists
      (fun p => IsConnectedAvoiding G X w {p}) l hatt
    have hvl : v ∈ l := by rw [hl]; simp
    cases R with
    | nil =>
      obtain ⟨v', hv'⟩ := exists_isListEdge_of_mem hlen hvl
      refine ⟨v, v', hv', fun p hp hwp => Or.inl ?_⟩
      rw [hl] at hp
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with hp | rfl
      · exact absurd hwp (hL₁ p hp)
      · rfl
    | cons u R' =>
      refine ⟨v, u, by rw [hl]; exact IsListEdge.append_right (l₁ := L₁) ⟨(v, u), by simp, rfl⟩,
        fun p hp hwp => ?_⟩
      rw [hl] at hp
      simp only [List.mem_append, List.mem_cons] at hp
      rcases hp with hp | rfl | rfl | hp
      · exact absurd hwp (hL₁ p hp)
      · exact Or.inl rfl
      · exact Or.inr rfl
      · have hsub : [v, u, p].Sublist l := by
          rw [hl]
          exact (List.nil_sublist L₁).append (List.Sublist.cons_cons v (List.Sublist.cons_cons u
            (List.singleton_sublist.mpr hp)))
        have hside := hwt w hwC hwl hnAB v p u hv hwp hsub
        have hul : u ∈ l := by rw [hl]; simp
        rcases hs u hul with h | h
        · exact absurd h hside.1
        · exact absurd h hside.2
  · push Not at hatt
    obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos (by omega : 0 < l.length)
    obtain ⟨x', hx'⟩ := exists_isListEdge_of_mem hlen hx
    exact ⟨x, x', hx', fun p hp hwp => absurd hwp (hatt p hp)⟩

/-! ### The step -/

/-- The list `L₁ ++ y :: z :: L₂` is a sublist of `L₁ ++ y :: N ++ z :: L₂`. -/
theorem sublist_collapse : (L₁ ++ y :: z :: L₂).Sublist (L₁ ++ y :: N ++ z :: L₂) := by
  rw [show L₁ ++ y :: N ++ z :: L₂ = L₁ ++ y :: (N ++ z :: L₂) by simp]
  exact (List.Sublist.refl L₁).append (List.Sublist.cons_cons y
    ((List.nil_sublist N).append (List.Sublist.refl _)))

/-- A walk of `G + yz`, together with a walk `W` of `G` from `y` to `z`, gives a walk of `G` with the
same ends whose vertices lie on the walk or on `W`. -/
theorem exists_walk_of_sup_edge_walk {y z : V} (W : G.Walk y z) :
    ∀ {u v : V} (p : (G ⊔ edge y z).Walk u v),
      ∃ q : G.Walk u v, ∀ x ∈ q.support, x ∈ p.support ∨ x ∈ W.support
  | _, _, .nil => ⟨.nil, fun _ hx => Or.inl hx⟩
  | u, _, .cons (v := w) h p => by
    obtain ⟨q, hq⟩ := exists_walk_of_sup_edge_walk W p
    have hq' : ∀ x ∈ q.support, x ∈ (Walk.cons h p).support ∨ x ∈ W.support := fun x hx =>
      (hq x hx).imp (List.mem_cons_of_mem u) id
    rcases (sup_adj _ _ _ _).mp h with hG | he
    · refine ⟨.cons hG q, fun x hx => ?_⟩
      rcases List.mem_cons.mp (Walk.support_cons hG q ▸ hx) with rfl | hx
      · exact Or.inl (by simp)
      · exact hq' x hx
    · rcases ((edge_adj _ _ _ _).mp he).1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨W.append q, fun x hx => ?_⟩
        rw [Walk.mem_support_append_iff] at hx
        rcases hx with hx | hx
        · exact Or.inr hx
        · exact hq' x hx
      · refine ⟨W.reverse.append q, fun x hx => ?_⟩
        rw [Walk.mem_support_append_iff] at hx
        rcases hx with hx | hx
        · exact Or.inr (List.mem_reverse.mp (Walk.support_reverse W ▸ hx))
        · exact hq' x hx

/-- Adding an edge `yz` whose ends are joined in `G` by a walk `W` with no inner vertex in `X'` does
not change `IsConnectedAvoiding · X'`. -/
theorem isConnectedAvoiding_sup_edge_iff_of_walk {y z : V} {X' : Set V} (W : G.Walk y z)
    (hW : ∀ x ∈ W.support, x ≠ y → x ≠ z → x ∉ X') {u : V} {S : Set V} :
    IsConnectedAvoiding (G ⊔ edge y z) X' u S ↔ IsConnectedAvoiding G X' u S := by
  refine ⟨fun ⟨s, hs, p, hp, hin⟩ => ?_, fun h => h.mono le_sup_left subset_rfl⟩
  by_cases hyz : y ∈ p.support ∧ z ∈ p.support
  · obtain ⟨q, hq⟩ := exists_walk_of_sup_edge_walk W p
    refine isConnectedAvoiding_of_walk_mem hs q fun x hx hxX' => ?_
    have hxp : x ∈ p.support := by
      rcases hq x hx with hxp | hxW
      · exact hxp
      · by_cases hxy : x = y
        · exact hxy ▸ hyz.1
        · by_cases hxz : x = z
          · exact hxz ▸ hyz.2
          · exact absurd hxX' (hW x hxW hxy hxz)
    by_contra hne
    push Not at hne
    exact hin x hxp hne.1 hne.2 hxX'
  · have hor : y ∉ p.support ∨ z ∉ p.support := by tauto
    obtain ⟨q, hq⟩ := exists_walk_of_sup_edge p hor
    exact ⟨s, hs, q, by rw [Walk.isPath_def, hq]; exact hp.support_nodup,
      fun x hx => hin x (hq ▸ hx)⟩

/-- For any set `X'` that misses `N` (the vertices of `P` removed in `P y z P`),
`IsConnectedAvoiding · X'` is the same in `G + yz` as in `G`: the stretch `y N z` of `P` is a walk
of `G` from `y` to `z` whose inner vertices lie in `N`. -/
theorem isConnectedAvoiding_collapse_iff (hsupp : P.support = L₁ ++ y :: N ++ z :: L₂)
    {X' : Set V} (hNX' : ∀ v ∈ N, v ∉ X') {u : V} {S : Set V} :
    IsConnectedAvoiding (G ⊔ edge y z) X' u S ↔ IsConnectedAvoiding G X' u S := by
  have hch : (y :: N ++ [z]).IsChain G.Adj := by
    have := hsupp ▸ P.isChain_adj_support
    exact this.infix ⟨L₁, L₂, by simp⟩
  obtain ⟨W, hWs⟩ := exists_walk_of_chain (u := y) (v := z) _ hch (by simp) (List.getLast?_concat ..)
  refine isConnectedAvoiding_sup_edge_iff_of_walk W fun x hx hxy hxz => ?_
  rw [hWs] at hx
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | hxN | rfl
  · exact absurd rfl hxy
  · exact hNX' x hxN
  · exact absurd rfl hxz

section Step

variable (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
  (hsupp : P.support = L₁ ++ y :: N ++ z :: L₂)
  (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
  (hwc : WindowClosed G C A B P y z N)
  (hno : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v ∧
    ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
  {P' : (G ⊔ edge y z).Walk a b} (hP's : P'.support = L₁ ++ y :: z :: L₂)
include hrot hP hsupp hind hwc hno hP's

/-- **Sides do not change.** In `G + yz`, a vertex of `P y z P` joined to a set `S` of vertices of `C`
off `P` by a path with no inner vertex in `C ∪ P y z P` is joined to `S` in `G` away from `C ∪ P`: such
a path cannot enter the zone of `N`, which it could only leave through `y` or `z`. -/
theorem isConnectedAvoiding_collapse {S : Set V} (hS : ∀ x ∈ S, x ∈ C ∧ x ∉ P.support) {v : V}
    (hv : v ∈ P'.support)
    (h : IsConnectedAvoiding (G ⊔ edge y z) {x | x ∈ C ∨ x ∈ P'.support} v S) :
    IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ P.support} v S := by
  classical
  obtain ⟨s, hs, ρ, hρ, hin⟩ := h
  have hnd : (L₁ ++ y :: N ++ z :: L₂).Nodup := hsupp ▸ hP.1.support_nodup
  have hyP' : y ∈ P'.support := by rw [hP's]; simp
  have hzP' : z ∈ P'.support := by rw [hP's]; simp
  have hsubP : ∀ {x}, x ∈ P'.support → x ∈ P.support := fun hx =>
    hsupp ▸ sublist_collapse.subset (hP's ▸ hx)
  have hsy : s ≠ y := fun h => (hS s hs).2 (h ▸ hsubP hyP')
  have hsz : s ≠ z := fun h => (hS s hs).2 (h ▸ hsubP hzP')
  have hyz : y ≠ z := (List.nodup_append.mp hnd).2.2 y (by simp) z (by simp)
  have hnot : ∀ x ∈ ρ.support, x ≠ v → x ≠ y ∧ x ≠ z := fun x hx hxv => by
    by_cases hxs : x = s
    · subst hxs
      exact ⟨hsy, hsz⟩
    · have := hin x hx hxv hxs
      exact ⟨fun h => this (Or.inr (h ▸ hyP')), fun h => this (Or.inr (h ▸ hzP'))⟩
  have hor : y ∉ ρ.support ∨ z ∉ ρ.support := by
    by_cases hvy : v = y
    · exact Or.inr fun hz => (hnot z hz (fun h => hyz (hvy ▸ h.symm))).2 rfl
    · exact Or.inl fun hy => (hnot y hy (Ne.symm hvy)).1 rfl
  obtain ⟨ρ', hρ'⟩ := exists_walk_of_sup_edge ρ hor
  have hρ'p : ρ'.IsPath := by rw [Walk.isPath_def, hρ']; exact hρ.support_nodup
  refine ⟨s, hs, ρ', hρ'p, fun x hx h1 h2 hxX => ?_⟩
  have hxρ : x ∈ ρ.support := hρ' ▸ hx
  have hxX' := hin x hxρ h1 h2
  have hxP : x ∈ P.support := by
    rcases hxX with hxC | hxP
    · exact absurd (Or.inl hxC) hxX'
    · exact hxP
  have hxN : x ∈ N := mem_N_of_not_mem hsupp hxP (hP's ▸ fun h => hxX' (Or.inr h))
  have hcl : ∀ u ∈ tightZone G {x | x ∈ C ∨ x ∈ P.support} N, ∀ w, G.Adj u w →
      w ∈ tightZone G {x | x ∈ C ∨ x ∈ P.support} N ∨ w = y ∨ w = z :=
    fun u hu w huw => tightZone_closed_of hrot hP hsupp hind hwc hno hu huw
  have hend := mem_of_walk_of_closed hcl (ρ'.dropUntil x hx) (Or.inl hxN) (fun t ht => by
    have htρ : t ∈ ρ.support := hρ' ▸ ρ'.support_dropUntil_subset_support hx ht
    have htv : t ≠ v := fun h => start_not_mem_dropUntil hρ'p hx h1 (h ▸ ht)
    exact hnot t htρ htv)
  exact tightZone_not_mem hP hsupp hend (hS s hs).1

/-- Sidedness of a vertex of `P y z P` is the same in `G + yz` as in `G`. -/
theorem isSided_collapse_iff (hCnd : C.Nodup) {v : V} (hv : v ∈ P'.support) :
    IsSided (G ⊔ edge y z) {x | x ∈ C ∨ x ∈ P'.support} A B v ↔
      IsSided G {x | x ∈ C ∨ x ∈ P.support} A B v := by
  have hsubX : {x | x ∈ C ∨ x ∈ P'.support} ⊆ {x | x ∈ C ∨ x ∈ P.support} := by
    rintro x (hx | hx)
    · exact Or.inl hx
    · exact Or.inr (hsupp ▸ sublist_collapse.subset (hP's ▸ hx))
  have hS : ∀ {S : List V}, (∀ x ∈ S, x ∈ A ∨ x ∈ B) → ∀ x ∈ {x | x ∈ S}, x ∈ C ∧ x ∉ P.support :=
    fun {S} hS x hx => ⟨List.mem_rotate.mp (by rw [hrot]; rcases hS x hx with h | h <;> simp [h]),
      notMem_support_of_arc hCnd hrot hP (hS x hx)⟩
  constructor
  · rintro (h | h)
    · exact Or.inl (isConnectedAvoiding_collapse hrot hP hsupp hind hwc hno hP's
        (hS fun x hx => Or.inl hx) hv h)
    · exact Or.inr (isConnectedAvoiding_collapse hrot hP hsupp hind hwc hno hP's
        (hS fun x hx => Or.inr hx) hv h)
  · rintro (h | h)
    · exact Or.inl (h.mono le_sup_left hsubX)
    · exact Or.inr (h.mono le_sup_left hsubX)

/-- **Weak tightness is kept.** A component of `G + yz - (C ∪ P y z P)` of the third kind that meets
the zone of `N` has only `y` and `z` as neighbours on `P y z P`, and nothing lies strictly between
them; any other one is a component of `G - (C ∪ P)` of the third kind with the same neighbours, and
`P y z P` is a sublist of `P`. -/
theorem weaklyTight_collapse (hCnd : C.Nodup) (hwt : IsWeaklyTight G C A B P.support) :
    IsWeaklyTight (G ⊔ edge y z) C A B P'.support := by
  classical
  set X : Set V := {x | x ∈ C ∨ x ∈ P.support} with hX
  set X' : Set V := {x | x ∈ C ∨ x ∈ P'.support} with hX'
  have hnd : (L₁ ++ y :: N ++ z :: L₂).Nodup := hsupp ▸ hP.1.support_nodup
  have hsubl : P'.support.Sublist P.support := hsupp ▸ hP's ▸ sublist_collapse
  have hsubP : ∀ {v}, v ∈ P'.support → v ∈ P.support := fun hv => hsubl.subset hv
  have hX'X : X' ⊆ X := fun v hv => hv.imp id hsubP
  have hNC : ∀ {v}, v ∈ N → v ∉ C := fun hv => not_mem_C_of_mem_window hP hsupp hv
  have hNP' : ∀ {v}, v ∈ N → v ∉ P'.support := fun hv => hP's ▸ not_mem_short_of_mem_N hnd hv
  have hNX' : ∀ {v}, v ∈ N → v ∉ X' := fun hv h => h.elim (hNC hv) (hNP' hv)
  have hyP' : y ∈ P'.support := by rw [hP's]; simp
  have hzP' : z ∈ P'.support := by rw [hP's]; simp
  have hyz : y ≠ z := (List.nodup_append.mp hnd).2.2 y (by simp) z (by simp)
  intro w hwC hwP' hnAB p q t hwp hwq hsub
  have htP' : t ∈ P'.support := hsub.subset (by simp)
  -- it is enough that `t` is on no side in `G`
  suffices hG : ¬ IsOnSide G X {x | x ∈ A} t ∧ ¬ IsOnSide G X {x | x ∈ B} t by
    have hiff := isSided_collapse_iff hrot hP hsupp hind hwc hno hP's hCnd htP'
    exact ⟨fun h => (hiff.mp (Or.inl h)).elim hG.1 hG.2,
      fun h => (hiff.mp (Or.inr h)).elim hG.1 hG.2⟩
  have hune : w ≠ y ∧ w ≠ z := ⟨fun h => hwP' (h ▸ hyP'), fun h => hwP' (h ▸ hzP')⟩
  -- a path of `G + yz` avoiding `X'` inside, with ends other than `y` and `z`
  have hGwalk : ∀ {x x' : V} (ρ : (G ⊔ edge y z).Walk x x'),
      (∀ v ∈ ρ.support, v ≠ x → v ≠ x' → v ∉ X') → x ≠ y ∧ x ≠ z → x' ≠ y ∧ x' ≠ z →
      ∃ ρ' : G.Walk x x', ∀ v ∈ ρ'.support, v ≠ y ∧ v ≠ z := by
    intro x x' ρ hρ hx hx'
    have hyz' : ∀ v ∈ ρ.support, v ≠ y ∧ v ≠ z := by
      intro v hv
      by_cases h1 : v = x
      · exact h1 ▸ hx
      · by_cases h2 : v = x'
        · exact h2 ▸ hx'
        · have := hρ v hv h1 h2
          exact ⟨fun h => this (Or.inr (h ▸ hyP')), fun h => this (Or.inr (h ▸ hzP'))⟩
    obtain ⟨ρ', hρ'⟩ := exists_walk_of_sup_edge ρ (Or.inl fun h => (hyz' y h).1 rfl)
    exact ⟨ρ', fun v hv => hyz' v (hρ' ▸ hv)⟩
  have hcl : ∀ u ∈ tightZone G X N, ∀ w, G.Adj u w → w ∈ tightZone G X N ∨ w = y ∨ w = z :=
    fun u hu w huw => tightZone_closed_of hrot hP hsupp hind hwc hno hu huw
  by_cases hcase : ∃ m ∈ N, IsConnectedAvoiding (G ⊔ edge y z) X' w {m}
  · -- the component of `w` meets the zone: its neighbours on `P'` are `y` and `z`
    exfalso
    obtain ⟨m, hm, m', hm', π, -, hπin⟩ := hcase
    rw [Set.mem_singleton_iff] at hm'
    subst hm'
    obtain ⟨π', hπ'⟩ := hGwalk π hπin hune ⟨fun h => hNP' hm (h ▸ hyP'), fun h => hNP' hm (h ▸ hzP')⟩
    have hwZ : w ∈ tightZone G X N :=
      mem_of_walk_of_closed hcl π'.reverse (Or.inl hm) (fun v hv => hπ' v (by simpa using hv))
    have hatt : ∀ r ∈ P'.support, IsConnectedAvoiding (G ⊔ edge y z) X' w {r} → r = y ∨ r = z := by
      intro r hr hwr
      by_contra hne
      push Not at hne
      obtain ⟨r', hr', ρ, -, hρin⟩ := hwr
      rw [Set.mem_singleton_iff] at hr'
      subst hr'
      obtain ⟨ρ', hρ'⟩ := hGwalk ρ hρin hune hne
      rcases mem_of_walk_of_closed hcl ρ' hwZ hρ' with h | ⟨h, -⟩
      · exact hNP' h hr
      · exact h (Or.inr (hsubP hr))
    exact not_sublist_between (hP's ▸ hP.1.support_nodup.sublist hsubl)
      (hatt p (hsub.subset (by simp)) hwp) (hatt q (hsub.subset (by simp)) hwq) (hP's ▸ hsub)
  · -- the component of `w` misses `N`: it is a component of `G - (C ∪ P)`
    have hwN : w ∉ N := fun h =>
      hcase ⟨w, h, w, rfl, .nil, Walk.IsPath.nil, fun v hv h1 => by simp at hv; exact absurd hv h1⟩
    have hwP : w ∉ P.support := fun h => hwN (mem_N_of_not_mem hsupp h (hP's ▸ hwP'))
    have hyX : y ∈ X := Or.inr (hsubP hyP')
    have hzX : z ∈ X := Or.inr (hsubP hzP')
    have hattG : ∀ r ∈ P'.support, IsConnectedAvoiding (G ⊔ edge y z) X' w {r} →
        IsConnectedAvoiding G X w {r} := by
      intro r hr hwr
      obtain ⟨r', hr', ρ, -, hρin⟩ := hwr
      rw [Set.mem_singleton_iff] at hr'
      subst hr'
      have hρX : ∀ v ∈ ρ.support, v ∈ X → v ∈ ({w} : Set V) ∨ v ∈ {x | x ∈ N ∨ x = r'} := by
        intro v hv hvX
        by_cases h1 : v = w
        · exact Or.inl h1
        · by_cases h2 : v = r'
          · exact Or.inr (Or.inr h2)
          · have hvX' := hρin v hv h1 h2
            rcases hvX with hvC | hvP
            · exact absurd (Or.inl hvC) hvX'
            · exact Or.inr (Or.inl (mem_N_of_not_mem hsupp hvP
                (hP's ▸ fun h => hvX' (Or.inr h))))
      obtain ⟨b', hb', c', hc', hc⟩ := exists_connected_of_walk (X := X) ρ (Or.inr rfl) hρX w rfl
        Walk.nil (fun v hv h => by simp at hv; exact absurd hv h)
      rw [Set.mem_singleton_iff] at hb'
      subst hb'
      rcases hc' with hc'N | rfl
      · exact absurd ⟨c', hc'N, hc.mono le_rfl hX'X⟩ hcase
      · refine hc.of_sup_edge ?_
        by_cases hcy : c' = y
        · exact Or.inr ⟨hzX, hune.2, fun h => hyz (hcy ▸ h).symm⟩
        · exact Or.inl ⟨hyX, hune.1, fun h => hcy h.symm⟩
    have hnAB' : ¬ IsConnectedAvoiding G X w {x | x ∈ A ∨ x ∈ B} := fun h =>
      hnAB (h.mono le_sup_left hX'X)
    exact hwt w hwC hwP hnAB' p q t (hattG p (hsub.subset (by simp)) hwp)
      (hattG q (hsub.subset (by simp)) hwq) (hsub.trans hsubl)

end Step

/-- **The step of the edges of Claim 5.5.** Let `P` be an induced, weakly tight `C`-path that
separates `A` from `B`, with vertex list `L₁ y N z L₂`, where `y` and `z` are sided and no vertex of
`N` is. Then `yz` is safe (Claim 5.5, page 19), and the path `P y z P` of `G + yz` is an induced,
weakly tight `C`-path that separates `A` from `B`, and whose vertices are sided in `G + yz` exactly
when they are in `G`. -/
theorem collapse_step (hC : IsCycleList G C) (hrot : C.rotate k = a :: A ++ b :: B)
    (hP : IsTPath G C P) (hsupp : P.support = L₁ ++ y :: N ++ z :: L₂)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (hsep : Separates G {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B})
    (hwt : IsWeaklyTight G C A B P.support)
    (hno : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v ∧
      ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
    (hy : IsSided G {x | x ∈ C ∨ x ∈ P.support} A B y)
    (hz : IsSided G {x | x ∈ C ∨ x ∈ P.support} A B z) :
    IsSafe G (edge y z) C ∧ ∃ P' : (G ⊔ edge y z).Walk a b, IsTPath (G ⊔ edge y z) C P' ∧
      P'.support = L₁ ++ y :: z :: L₂ ∧
      (∀ u ∈ P'.support, ∀ v ∈ P'.support, (G ⊔ edge y z).Adj u v → IsListEdge P'.support u v) ∧
      Separates (G ⊔ edge y z) {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} ∧
      IsWeaklyTight (G ⊔ edge y z) C A B P'.support ∧
      ∀ v ∈ P'.support, (IsSided (G ⊔ edge y z) {x | x ∈ C ∨ x ∈ P'.support} A B v ↔
        IsSided G {x | x ∈ C ∨ x ∈ P.support} A B v) := by
  have hwc := windowClosed_of_weaklyTight hsupp hwt hy hz
  obtain ⟨P', hP', hP's⟩ := exists_short_path hrot hP hsupp
  have hIS := loop_induced_separates hrot hP hsupp hind hsep (fun v hv => (hno v hv).2) hP's
  exact ⟨claim_5_5_of hrot hP hsupp hind hwc hno, P', hP', hP's, hIS.1, hIS.2,
    weaklyTight_collapse hrot hP hsupp hind hwc hno hP's hC.2.1 hwt,
    fun v hv => isSided_collapse_iff hrot hP hsupp hind hwc hno hP's hC.2.1 hv⟩

/-- A maximal run of entries without a property, in a list whose first and last entries have it. -/
theorem exists_run (Q : V → Prop) {l : List V} {x w : V} (hx : l.head? = some x) (hQx : Q x)
    (hw : l.getLast? = some w) (hQw : Q w) (ht : ∃ t ∈ l, ¬ Q t) :
    ∃ L₁ y N z L₂, l = L₁ ++ y :: N ++ z :: L₂ ∧ Q y ∧ Q z ∧ N ≠ [] ∧ ∀ v ∈ N, ¬ Q v := by
  classical
  obtain ⟨M₁, t, R, rfl, hQt, hM₁⟩ := exists_first_of_exists (fun v => ¬ Q v) _ ht
  -- `M₁` is not empty, since the first entry has the property
  obtain ⟨L₁, y, rfl⟩ : ∃ L₁ y, M₁ = L₁ ++ [y] := by
    rcases M₁.eq_nil_or_concat with h | ⟨L, y, h⟩
    · subst h
      simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hx
      exact absurd (hx ▸ hQx) hQt
    · exact ⟨L, y, by simpa using h⟩
  have hQy : Q y := not_not.mp (hM₁ y (by simp))
  -- some entry of `R` has the property: the last one
  have hR : ∃ v ∈ R, Q v := by
    rcases R.eq_nil_or_concat with h | ⟨R', v, h⟩
    · subst h
      simp only [List.append_assoc, List.singleton_append, List.getLast?_append,
        List.getLast?_cons, List.getLast?_nil, Option.getD_none, Option.some_or] at hw
      simp at hw
      exact absurd (hw ▸ hQw) hQt
    · rw [List.concat_eq_append] at h
      subst h
      refine ⟨v, by simp, ?_⟩
      have : w = v := by
        rw [show L₁ ++ [y] ++ t :: (R' ++ [v]) = (L₁ ++ [y] ++ t :: R') ++ [v] by simp,
          List.getLast?_concat] at hw
        exact (Option.some.inj hw).symm
      exact this ▸ hQw
  obtain ⟨N', z, L₂, rfl, hQz, hN'⟩ := exists_first_of_exists Q R hR
  exact ⟨L₁, y, t :: N', z, L₂, by simp, hQy, hQz, by simp, fun v hv => by
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hQt
    · exact hN' v hv⟩

/-- The ends of `P` are sided: `a` is next to the first vertex of `A`, and `b` to the first vertex of
`B`. -/
theorem ends_sided (hC : IsCycleList G C) (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ [])
    (hB : B ≠ []) {X : Set V} :
    IsSided G X A B a ∧ IsSided G X A B b := by
  have hside : ∀ {u t : V} {S : List V}, t ∈ S → G.Adj u t → IsOnSide G X {x | x ∈ S} u :=
    fun {u t S} ht hadj => isConnectedAvoiding_of_walk_mem ht hadj.toWalk (fun v hv _ => by
      simp at hv; exact hv)
  have hCa : IsCycleList G (a :: (A ++ b :: B)) := by
    have := hC.rotate k
    rw [hrot] at this
    simpa using this
  have hCb : IsCycleList G (b :: (B ++ a :: A)) := by
    have := hC.rotate k
    rw [hrot] at this
    have h2 := this.rotate (A.length + 1)
    rw [rotate_cons_append_cons'] at h2
    simpa using h2
  obtain ⟨A₀, A', rfl⟩ := List.exists_cons_of_ne_nil hA
  obtain ⟨B₀, B', rfl⟩ := List.exists_cons_of_ne_nil hB
  have h1 := (hCa.adj_first_last (by simp)).1
  have h2 := (hCb.adj_first_last (by simp)).1
  simp only [List.cons_append, List.getElem_cons_zero] at h1 h2
  exact ⟨Or.inl (hside (by simp) h1), Or.inr (hside (by simp) h2)⟩

/-- **The edges of Claim 5.5, repeated.** From an induced, weakly tight `C`-path `P` that separates
`A` from `B`, adding the edges of `collapse_step` one after the other gives a graph `H ⊇ G` in which
`C` is crossed only if it is crossed in `G`, with an induced, tight `C`-path from `a` to `b` that
separates `A` from `B`, is a sublist of `P`, has all its vertices sided, and keeps
`IsConnectedAvoiding · X'` unchanged for every set `X'` disjoint from the removed vertices of `P`. -/
theorem collapse_all (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ []) (hB : B ≠ []) :
    ∀ (n : ℕ) (G : SimpleGraph V) (P : G.Walk a b), P.support.length = n → IsCycleList G C →
      IsTPath G C P →
      (∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v) →
      Separates G {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B} →
      IsWeaklyTight G C A B P.support →
      ∃ H : SimpleGraph V, G ≤ H ∧ (IsCrossed H C → IsCrossed G C) ∧
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
  intro G P hn hC hP hind hsep hwt
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
  · exact ⟨G, le_rfl, id, P, hP, hind, hsep, tight_of_weaklyTight hlen hwt hall, hall,
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
  obtain ⟨H, hle, hcr, P'', h1, h2, h3, h4, h5, hsub', hconn⟩ :=
    ih _ hlt (G ⊔ edge y z) P' rfl (hC.mono le_sup_left) hP' hind' hsep' hwt'
  refine ⟨H, le_sup_left.trans hle, fun h => hsafe (hcr h), P'', h1, h2, h3, h4, h5,
    hsub'.trans hsub, fun X' hX' u S => ?_⟩
  have hconn₁ := isConnectedAvoiding_collapse_iff hsupp (X' := X')
    (fun v hv => hX' v (hNP' v hv).1 fun h => (hNP' v hv).2 (hsub'.subset h)) (u := u) (S := S)
  have hconn₂ := hconn X' (fun v hv => hX' v (hsub.subset hv)) u S
  exact hconn₂.trans hconn₁

end GraphMinor.HP25
