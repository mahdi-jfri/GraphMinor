module

public import GraphMinor.HP25.Sec5Tight
public import GraphMinor.HP25.RibList
import GraphMinor.HP25.Sec5Lemma54
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Embedding

/-!
# The graph steps of the strip argument for Lemma 5.4

This file holds the steps of the proof of the strip lemma (`Sec5Strip.lean`) that do not use the
drawing. As in `Sec5Tight.lean`, `P` is a `C`-path from `a` to `b`, `C = a A b B` up to rotation,
`X = C ∪ P`, and `P.support = L₁ ++ y :: N ++ s :: L₂`.

* `IsThirdKind`: a vertex off `X` that is not joined to `A ∪ B` avoiding `X`. Its component of
  `G - X` is a *third-kind component*.
* Step 0 (`isChain_filter_thirdKind`): when `P` is tight, removing the third-kind vertices from a
  path keeps a chain. A path enters and leaves a third-kind component through its two neighbours on
  `P`, which are consecutive on `P`, so the part through the component can be replaced by an edge of
  `P`.
* Step 1 (`reachesOff_of_pocket_adj`): a neighbour off `P` of a vertex of `N` that is on no side
  `B`, and that is not of the third kind, is joined to `A` by a walk that never meets `P`
  (`ReachesOff`).
* `infix_of_isChain_isListEdge`: a list without repetition whose consecutive entries are consecutive
  on `l` is a stretch of `l` or of its reverse.
* Step 8, graph part (`stretch_cases`): a path that starts at a vertex of `N`, avoids `y`, `s` and the
  third kind, either reaches a vertex joined to `A` off `P`, or runs along `P`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-- `x` is joined to an entry of `T` by a walk that never meets `L`. -/
@[expose] def ReachesOff (G : SimpleGraph V) (L T : List V) (x : V) : Prop :=
  ∃ t ∈ T, ∃ p : G.Walk x t, ∀ v ∈ p.support, v ∉ L

/-- `u` is of the *third kind* for the `C`-path with vertex list `L` and sides `A`, `B`: it is off
`C ∪ L` and not joined to `A ∪ B` by a path with no inner vertex in `C ∪ L`. -/
@[expose] def IsThirdKind (G : SimpleGraph V) (C A B L : List V) (u : V) : Prop :=
  u ∉ C ∧ u ∉ L ∧ ¬ IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ L} u {x | x ∈ A ∨ x ∈ B}

/-! ### Lists -/

/-- Extending a stretch of a list by one entry at the front. -/
private theorem extend_front {l L₀ T : List V} {x₀ x₁ x₂ : V} (hl : l.Nodup)
    (h : l = L₀ ++ x₁ :: x₂ :: T) (he : IsListEdge l x₀ x₁) (hne : x₀ ≠ x₂) :
    ∃ L₀', L₀ = L₀' ++ [x₀] := by
  obtain ⟨F₀, F₁, h' | h'⟩ := he.exists_split
  · have e : l = (F₀ ++ [x₀]) ++ x₁ :: F₁ := by rw [h']; simp
    have := (split_unique (e.symm.trans h) (by rw [← e]; exact hl)).1
    exact ⟨F₀, this.symm⟩
  · obtain ⟨-, h2⟩ := split_unique (h'.symm.trans h) (by rw [← h']; exact hl)
    simp only [List.cons.injEq] at h2
    exact absurd h2.1 hne

/-- **A walk along a list.** A list without repetition, with at least two entries, whose consecutive
entries are consecutive in `l`, is a stretch of `l` or of its reverse. -/
theorem infix_of_isChain_isListEdge {l : List V} (hl : l.Nodup) :
    ∀ {x₀ x₁ : V} {T : List V}, (x₀ :: x₁ :: T).Nodup → (x₀ :: x₁ :: T).IsChain (IsListEdge l) →
      (x₀ :: x₁ :: T) <:+: l ∨ (x₀ :: x₁ :: T) <:+: l.reverse
  | x₀, x₁, [], _, hc => by
    obtain ⟨F₀, F₁, h | h⟩ := (List.isChain_cons_cons.mp hc).1.exists_split
    · exact Or.inl ⟨F₀, F₁, by rw [h]; simp⟩
    · exact Or.inr ⟨F₁.reverse, F₀.reverse, by rw [h]; simp⟩
  | x₀, x₁, x₂ :: T, hnd, hc => by
    have hne : x₀ ≠ x₂ := fun h => by subst h; simp at hnd
    have he := (List.isChain_cons_cons.mp hc).1
    rcases infix_of_isChain_isListEdge hl (List.nodup_cons.mp hnd).2
      (List.isChain_cons_cons.mp hc).2 with ⟨L₀, L₁, h⟩ | ⟨L₀, L₁, h⟩
    · obtain ⟨L₀', rfl⟩ := extend_front (L₀ := L₀) (T := T ++ L₁) hl (h.symm.trans (by simp)) he hne
      exact Or.inl ⟨L₀', L₁, by rw [← h]; simp⟩
    · obtain ⟨L₀', rfl⟩ := extend_front (L₀ := L₀) (T := T ++ L₁) (List.nodup_reverse.mpr hl)
        (h.symm.trans (by simp)) he.reverse hne
      exact Or.inr ⟨L₀', L₁, by rw [← h]; simp⟩

/-- Two entries consecutive in a list of vertices of a walk are adjacent. -/
theorem IsListEdge.adj_of_chain {l : List V} (hc : l.IsChain G.Adj) {u v : V}
    (h : IsListEdge l u v) : G.Adj u v := by
  obtain ⟨pr, hpr, he⟩ := h
  have hadj := isChain_iff_zip.mp hc _ hpr
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hadj
  · exact hadj.symm

variable {C A B L₁ N L₂ : List V} {a b y s : V} {k : ℕ} {P : G.Walk a b}

/-- The vertices of the open arcs `A` and `B` are not on `P`. -/
theorem notMem_support_of_arc (hCnd : C.Nodup) (hrot : C.rotate k = a :: A ++ b :: B)
    (hP : IsTPath G C P) {v : V} (hv : v ∈ A ∨ v ∈ B) : v ∉ P.support := by
  have hnd : (a :: A ++ b :: B).Nodup := hrot ▸ List.nodup_rotate.mpr hCnd
  intro hvP
  have hvC : v ∈ C := by
    have : v ∈ C.rotate k := by rw [hrot]; rcases hv with h | h <;> simp [h]
    exact List.mem_rotate.mp this
  have hva : v ≠ a := by
    rintro rfl
    rw [List.cons_append, List.nodup_cons] at hnd
    rcases hv with h | h <;> simp_all
  have hvb : v ≠ b := by
    rintro rfl
    rw [List.nodup_append] at hnd
    rcases hv with h | h
    · exact hnd.2.2 v (by simp [h]) v (by simp) rfl
    · exact (List.nodup_cons.mp hnd.2.1).1 h
  exact (hP.2.2.2 v hvP hva hvb).1 hvC


/-- **Step 1: the neighbours of the pocket.** A neighbour `w` off `P` of a vertex `σ` that is not
on side `B`, if `w` is not of the third kind, is joined to `A` by a walk that never meets `P`. It is
on `C`, hence in `A`, or it is joined to `A ∪ B` avoiding `C ∪ P`, and not to `B`, since `σ` is not
on side `B`. -/
theorem reachesOff_of_pocket_adj (hCnd : C.Nodup) (hrot : C.rotate k = a :: A ++ b :: B)
    (hP : IsTPath G C P) {σ w : V}
    (hσB : ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} σ) (hadj : G.Adj σ w)
    (hwP : w ∉ P.support) (hw3 : ¬ IsThirdKind G C A B P.support w) :
    ReachesOff G P.support A w := by
  by_cases hwC : w ∈ C
  · rcases mem_of_rotate hrot hwC with rfl | hA | rfl | hB
    · exact absurd P.start_mem_support hwP
    · exact ⟨w, hA, Walk.nil, by simpa using hwP⟩
    · exact absurd P.end_mem_support hwP
    · exact absurd (isConnectedAvoiding_of_walk_mem (show w ∈ {x | x ∈ B} from hB)
        (Walk.cons hadj Walk.nil) fun v hv _ => by simp at hv; tauto) hσB
  · have hconn : IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ P.support} w {x | x ∈ A ∨ x ∈ B} := by
      by_contra h; exact hw3 ⟨hwC, hwP, h⟩
    obtain ⟨z, hz, p, -, hin⟩ := hconn
    have hzP : z ∉ P.support := notMem_support_of_arc hCnd hrot hP hz
    rcases hz with hzA | hzB
    · refine ⟨z, hzA, p, fun v hv hvP => ?_⟩
      by_cases h1 : v = w
      · exact hwP (h1 ▸ hvP)
      by_cases h2 : v = z
      · exact hzP (h2 ▸ hvP)
      exact hin v hv h1 h2 (Or.inr hvP)
    · exfalso
      refine hσB (isConnectedAvoiding_of_walk_mem (show z ∈ {x | x ∈ B} from hzB)
        (Walk.cons hadj p) ?_)
      intro v hv hvX
      rw [Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact Or.inl rfl
      by_cases h1 : v = w
      · subst h1
        exact absurd hvX (by rintro (h | h); exacts [hwC h, hwP h])
      by_cases h2 : v = z
      · exact Or.inr h2
      exact absurd hvX (hin v hv h1 h2)

/-- A neighbour of a third-kind vertex that is not of the third kind is on `P`. -/
theorem mem_support_of_adj_thirdKind (hrot : C.rotate k = a :: A ++ b :: B) {k' u : V}
    (hk : IsThirdKind G C A B P.support k') (hu : ¬ IsThirdKind G C A B P.support u)
    (hadj : G.Adj k' u) : u ∈ P.support := by
  by_contra huP
  apply hk.2.2
  by_cases huC : u ∈ C
  · rcases mem_of_rotate hrot huC with rfl | hA | rfl | hB
    · exact absurd P.start_mem_support huP
    · exact isConnectedAvoiding_of_walk_mem (show u ∈ {x | x ∈ A ∨ x ∈ B} from Or.inl hA)
        (Walk.cons hadj Walk.nil) fun v hv _ => by simp at hv; tauto
    · exact absurd P.end_mem_support huP
    · exact isConnectedAvoiding_of_walk_mem (show u ∈ {x | x ∈ A ∨ x ∈ B} from Or.inr hB)
        (Walk.cons hadj Walk.nil) fun v hv _ => by simp at hv; tauto
  · have hconn : IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ P.support} u {x | x ∈ A ∨ x ∈ B} := by
      by_contra h; exact hu ⟨huC, huP, h⟩
    obtain ⟨z, hz, p, -, hin⟩ := hconn
    refine isConnectedAvoiding_of_walk_mem hz (Walk.cons hadj p) ?_
    intro v hv hvX
    rw [Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact Or.inl rfl
    by_cases h1 : v = u
    · subst h1
      exact absurd hvX (by rintro (h | h); exacts [huC h, huP h])
    by_cases h2 : v = z
    · exact Or.inr h2
    exact absurd hvX (hin v hv h1 h2)

/-- An entry of `l ++ [v]` followed by another entry is an entry of `l`. -/
private theorem mem_of_append_singleton {l l₁ l₂ : List V} {v x x' : V}
    (h : l ++ [v] = l₁ ++ x :: x' :: l₂) : x ∈ l := by
  have := congrArg List.dropLast h
  rw [List.dropLast_concat] at this
  rw [this, List.dropLast_append_of_ne_nil (by simp)]
  simp

/-- **Step 0: removing the third kind.** Let `P` be tight. In a chain of a graph `G' ≥ G` whose edges
at vertices off `P` are edges of `G`, the entries that are not of the third kind form a chain. A
stretch `u K v` with `K` of the third kind lies in one third-kind component, whose neighbours `u`, `v`
on `P` are consecutive on `P`. -/
theorem isChain_filter_thirdKind [DecidablePred (IsThirdKind G C A B P.support)]
    (hrot : C.rotate k = a :: A ++ b :: B) (htight : IsTight G C A B P.support)
    {G' : SimpleGraph V} (hle : G ≤ G') (hG' : ∀ u v, G'.Adj u v → u ∉ P.support → G.Adj u v)
    {L : List V} (hc : L.IsChain G'.Adj) (hnd : L.Nodup) :
    (L.filter fun u => !decide (IsThirdKind G C A B P.support u)).IsChain G'.Adj := by
  classical
  refine isChain_filter fun L₀ u K v L₁ he hu hv hK => ?_
  have hinf : (u :: K ++ [v]) <:+: L := ⟨L₀, L₁, by rw [he]; simp⟩
  have hc' := hc.infix hinf
  have hnd' := hnd.sublist hinf.sublist
  rcases K with _ | ⟨k₁, K⟩
  · simpa using hc'
  have hk3 : ∀ x ∈ k₁ :: K, IsThirdKind G C A B P.support x := fun x hx => by
    simpa using hK x hx
  have hu3 : ¬ IsThirdKind G C A B P.support u := by simpa using hu
  have hv3 : ¬ IsThirdKind G C A B P.support v := by simpa using hv
  have hc2 : (u :: k₁ :: (K ++ [v])).IsChain G'.Adj := by simpa using hc'
  have hcG : (k₁ :: K ++ [v]).IsChain G.Adj := by
    have h1 : (k₁ :: K ++ [v]).IsChain G'.Adj := by simpa using (List.isChain_cons_cons.mp hc2).2
    rw [List.isChain_iff_forall_rel_of_append_cons_cons] at h1 ⊢
    intro x x' l₁ l₂ hl
    exact hG' x x' (h1 hl) (hk3 x (mem_of_append_singleton hl)).2.1
  have hku : G.Adj k₁ u := hG' k₁ u (List.isChain_cons_cons.mp hc2).1.symm (hk3 k₁ (by simp)).2.1
  have huP := mem_support_of_adj_thirdKind hrot (hk3 k₁ (by simp)) hu3 hku
  obtain ⟨K', kl, hKe⟩ : ∃ K' kl, k₁ :: K = K' ++ [kl] :=
    ⟨(k₁ :: K).dropLast, (k₁ :: K).getLast (by simp), (List.dropLast_append_getLast _).symm⟩
  have hkl : kl ∈ k₁ :: K := by rw [hKe]; simp
  have hkv : G.Adj kl v :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp hcG (l₁ := K') (l₂ := [])
      (by rw [hKe]; simp)
  have hvP := mem_support_of_adj_thirdKind hrot (hk3 kl hkl) hv3 hkv
  obtain ⟨v', w', hvw, hall⟩ := htight k₁ (hk3 k₁ (by simp)).1 (hk3 k₁ (by simp)).2.1
    (hk3 k₁ (by simp)).2.2
  have hu' := hall u huP (isConnectedAvoiding_of_walk_mem (show u ∈ ({u} : Set V) from rfl)
    (Walk.cons hku Walk.nil) fun x hx _ => by simp at hx; tauto)
  obtain ⟨p, hp⟩ := exists_walk_of_chain (u := k₁) (v := v) _ hcG (by simp) (List.getLast?_concat ..)
  have hv' := hall v hvP (isConnectedAvoiding_of_walk_mem (show v ∈ ({v} : Set V) from rfl) p
    fun x hx hxX => by
      rw [hp] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact absurd hxX (by rintro (h | h); exacts [(hk3 x hx).1 h, (hk3 x hx).2.1 h])
      · exact Or.inr (List.mem_singleton.mp hx))
  have huv : u ≠ v := fun h => by subst h; simp at hnd'
  have hl : IsListEdge P.support u v := by
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact absurd rfl huv
    · exact hvw
    · exact hvw.symm
    · exact absurd rfl huv
  exact hle (hl.adj_of_chain P.isChain_adj_support)

/-- **Step 8, graph part.** Let `P` be induced, and let the vertices of `N` be on no side `B`. A
path `σ T` of `G` that starts in `N` and whose other vertices avoid `y`, `s` and the third kind,
either reaches a vertex joined to `A` by a walk off `P`, or stays in `N`. -/
theorem stretch_cases [DecidableEq V] (hCnd : C.Nodup) (hrot : C.rotate k = a :: A ++ b :: B)
    (hP : IsTPath G C P) (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (hN : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v) :
    ∀ {σ : V} {T : List V}, σ ∈ N → (σ :: T).IsChain G.Adj →
      (∀ x ∈ T, ¬ IsThirdKind G C A B P.support x ∧ x ≠ y ∧ x ≠ s) →
      (∃ x ∈ T, ReachesOff G P.support A x) ∨ (∀ x ∈ σ :: T, x ∈ N)
  | σ, [], hσ, _, _ => Or.inr fun x hx => by rw [List.mem_singleton.mp hx]; exact hσ
  | σ, t :: T, hσ, hc, hT => by
    have hadj := (List.isChain_cons_cons.mp hc).1
    have hnd : (L₁ ++ y :: N ++ s :: L₂).Nodup := hsupp ▸ hP.1.support_nodup
    have hσP : σ ∈ P.support := by rw [hsupp]; simp [hσ]
    by_cases htP : t ∈ P.support
    · have hl := hind σ hσP t htP hadj
      rw [hsupp] at hl
      have htw := hl.mem_window hnd hσ
      have htN : t ∈ N := by
        simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
          or_false] at htw
        rcases htw with h | h | h
        · exact absurd h (hT t (by simp)).2.1
        · exact h
        · exact absurd h (hT t (by simp)).2.2
      rcases stretch_cases hCnd hrot hP hsupp hind hN htN (List.isChain_cons_cons.mp hc).2
        (fun x hx => hT x (List.mem_cons_of_mem _ hx)) with ⟨x, hx, h⟩ | h
      · exact Or.inl ⟨x, List.mem_cons_of_mem _ hx, h⟩
      · refine Or.inr fun x hx => ?_
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hσ
        · exact h x hx
    · exact Or.inl ⟨t, by simp, reachesOff_of_pocket_adj hCnd hrot hP (hN σ hσ) hadj htP
        (hT t (by simp)).1⟩


/-- **Step 8, graph part, as stretches.** Under the hypotheses of `stretch_cases`, a path `σ T`
either reaches a vertex joined to `A` off `P`, or it is a stretch of `P` or of its reverse. -/
theorem stretch_infix [DecidableEq V] (hCnd : C.Nodup) (hrot : C.rotate k = a :: A ++ b :: B)
    (hP : IsTPath G C P) (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (hN : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v) {σ : V} {T : List V}
    (hσ : σ ∈ N) (hc : (σ :: T).IsChain G.Adj) (hnd : (σ :: T).Nodup)
    (hT : ∀ x ∈ T, ¬ IsThirdKind G C A B P.support x ∧ x ≠ y ∧ x ≠ s) :
    (∃ x ∈ T, ReachesOff G P.support A x) ∨
      ((σ :: T) <:+: P.support ∨ (σ :: T) <:+: P.support.reverse) := by
  rcases stretch_cases hCnd hrot hP hsupp hind hN hσ hc hT with h | hall
  · exact Or.inl h
  right
  have hNP : ∀ x ∈ N, x ∈ P.support := fun x hx => by rw [hsupp]; simp [hx]
  rcases T with _ | ⟨t, T⟩
  · obtain ⟨l₀, l₁, h⟩ := List.append_of_mem (hNP σ hσ)
    exact Or.inl ⟨l₀, l₁, by rw [h]; simp⟩
  refine infix_of_isChain_isListEdge hP.1.support_nodup hnd ?_
  rw [List.isChain_iff_forall_rel_of_append_cons_cons] at hc ⊢
  intro x x' l₁ l₂ hl
  have hx : x ∈ σ :: t :: T := by rw [hl]; simp
  have hx' : x' ∈ σ :: t :: T := by rw [hl]; simp
  exact hind x (hNP x (hall x hx)) x' (hNP x' (hall x' hx')) (hc hl)

end GraphMinor.HP25
