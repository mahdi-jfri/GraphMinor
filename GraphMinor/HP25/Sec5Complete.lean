module

public import GraphMinor.HP25.Sec5Collapse
public import GraphMinor.HP25.Sec5Strip
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Lemma43Case1
import GraphMinor.HP25.Alternate
import GraphMinor.HP25.Completion
import GraphMinor.HP25.Sec5Lemma54

/-!
# The loop of Algorithm 5.2 on a tight path

Algorithm 5.2 of Humeau and Pous (page 23), "Computing $P$-completions", repeats Lemma 5.4 (page 19):
it adds the edge `y_j y_s` and replaces `P` by `P y_j y_s P`, until every vertex of `P` is on both
`P`-sides. This file proves that the loop does this, when it starts from an induced, tight `C`-path
that separates `A` from `B` and whose vertices are all on some side (`complete_loop`), which is what
`collapse_all` (`Sec5Collapse.lean`) provides. Each edge is safe by the strip lemma (`strip_safe`), the
new last vertex `y_s` is on both sides by `lemma_5_4_sides`, and the new path is again induced,
separating and tight by `loop_invariant`. Since every vertex is sided, the vertex `y_r` after the
prefix on both sides is on one side only, so `y_s` comes after it and the path gets shorter.

The strip lemma and the loop invariant are stated with `B` the side that the skipped vertices lack.
When they lack `A` we apply them to the reversed path `P⁻¹` from `b` to `a`, whose cycle is
`b B a A` (`strip_safe_rev`, `loop_invariant_rev`).
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-! ### Reversing the path -/

/-- The reverse of an induced path is induced. -/
theorem induced_reverse {a b : V} {P : G.Walk a b}
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v) :
    ∀ u ∈ P.reverse.support, ∀ v ∈ P.reverse.support, G.Adj u v →
      IsListEdge P.reverse.support u v := by
  intro u hu v hv h
  rw [Walk.support_reverse, List.mem_reverse] at hu hv
  rw [Walk.support_reverse]
  exact (hind u hu v hv h).reverse

/-- Separation is symmetric. -/
theorem Separates.symm' {X U W : Set V} (h : Separates G X U W) : Separates G X W U := by
  intro w hw u hu p
  obtain ⟨x, hx, hxX⟩ := h u hu w hw p.reverse
  exact ⟨x, by simpa using hx, hxX⟩

/-- Tightness does not depend on the direction of the path or on the order of the two sides. -/
theorem isTight_reverse {C A B l : List V} (h : IsTight G C A B l) : IsTight G C B A l.reverse := by
  have e1 : {x | x ∈ B ∨ x ∈ A} = {x | x ∈ A ∨ x ∈ B} := Set.ext fun x => or_comm
  have e2 : {x | x ∈ C ∨ x ∈ l.reverse} = {x | x ∈ C ∨ x ∈ l} := by ext; simp
  unfold IsTight at h ⊢
  intro u huC hul hnAB
  rw [e2, e1] at hnAB
  rw [List.mem_reverse] at hul
  obtain ⟨v, w, he, hall⟩ := h u huC hul hnAB
  refine ⟨v, w, he.reverse, fun p hp hup => ?_⟩
  rw [e2] at hup
  exact hall p (List.mem_reverse.mp hp) hup

variable {C A B L₁ N L₂ : List V} {a b y s : V} {k : ℕ} {P : G.Walk a b}

/-- The rotation of `C` that starts at `b`. -/
theorem rotate_at_b (hrot : C.rotate k = a :: A ++ b :: B) :
    C.rotate (k + (A.length + 1)) = b :: B ++ a :: A := by
  rw [← List.rotate_rotate, hrot, rotate_cons_append_cons']

/-- The vertices of `P⁻¹` are those of `P`. -/
theorem setOf_reverse_support :
    {x | x ∈ C ∨ x ∈ P.reverse.support} = {x | x ∈ C ∨ x ∈ P.support} := by
  ext; simp

/-- **The strip lemma for side `A`** (`strip_safe` on `P⁻¹`). -/
theorem strip_safe_rev [Finite V] (hC : IsCycleList G C) (hrot : C.rotate k = a :: A ++ b :: B)
    (hP : IsTPath G C P) (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (htight : IsTight G C A B P.support)
    (hy : IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} y)
    (hs : IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} s)
    (hN : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v) :
    IsSafe G (edge y s) C := by
  have hsupp' : P.reverse.support = L₂.reverse ++ s :: N.reverse ++ y :: L₁.reverse := by
    rw [Walk.support_reverse, hsupp]; simp
  have hX := setOf_reverse_support (C := C) (P := P)
  have h := strip_safe hC (rotate_at_b hrot) hP.reverse hsupp' (induced_reverse hind)
    (by rw [Walk.support_reverse]; exact isTight_reverse htight) (hX ▸ hs) (hX ▸ hy)
    (fun v hv => hX ▸ hN v (List.mem_reverse.mp hv))
  rwa [edge_comm] at h

/-- **The loop invariant for side `A`** (`loop_invariant` on `P⁻¹`). -/
theorem loop_invariant_rev (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (htight : IsTight G C A B P.support)
    (hsep : Separates G {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B})
    (hNA : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v)
    {P' : (G ⊔ edge y s).Walk a b} (hP's : P'.support = L₁ ++ y :: s :: L₂) :
    (∀ u ∈ P'.support, ∀ v ∈ P'.support, (G ⊔ edge y s).Adj u v →
        IsListEdge P'.support u v) ∧
      Separates (G ⊔ edge y s) {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} ∧
      IsTight (G ⊔ edge y s) C A B P'.support := by
  have e : G ⊔ edge y s = G ⊔ edge s y := by rw [edge_comm]
  have hsupp' : P.reverse.support = L₂.reverse ++ s :: N.reverse ++ y :: L₁.reverse := by
    rw [Walk.support_reverse, hsupp]; simp
  have hX := setOf_reverse_support (C := C) (P := P)
  have hsetP : {v | v ∈ P.reverse.support} = {v | v ∈ P.support} := by ext; simp
  set Q : (G ⊔ edge s y).Walk b a := P'.reverse.mapLe e.le with hQ
  have hQs : Q.support = L₂.reverse ++ s :: y :: L₁.reverse := by
    rw [hQ, support_mapLe, Walk.support_reverse, hP's]; simp
  obtain ⟨h1, h2, h3⟩ := loop_invariant (rotate_at_b hrot) hP.reverse hsupp'
    (induced_reverse hind) (by rw [Walk.support_reverse]; exact isTight_reverse htight) (hsetP ▸ hsep.symm')
    (fun v hv => hX ▸ hNA v (List.mem_reverse.mp hv)) hQs
  have hQs' : Q.support = P'.support.reverse := by
    rw [hQ, support_mapLe, Walk.support_reverse]
  rw [hQs'] at h1 h2 h3
  rw [← e] at h1 h2 h3
  refine ⟨fun u hu v hv huv => ?_, ?_, ?_⟩
  · have := h1 u (List.mem_reverse.mpr hu) v (List.mem_reverse.mpr hv) huv
    simpa using this.reverse
  · have hset : {v | v ∈ P'.support.reverse} = {v | v ∈ P'.support} := by ext; simp
    rw [hset] at h2
    exact h2.symm'
  · simpa using isTight_reverse h3

/-! ### The loop -/

/-- Both ends of `P` are on both sides. -/
theorem ends_both (hC : IsCycleList G C) (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ [])
    (hB : B ≠ []) {X : Set V} :
    (IsOnSide G X {x | x ∈ A} a ∧ IsOnSide G X {x | x ∈ B} a) ∧
      (IsOnSide G X {x | x ∈ A} b ∧ IsOnSide G X {x | x ∈ B} b) := by
  have hside : ∀ {u t : V} {S : List V}, t ∈ S → G.Adj u t → IsOnSide G X {x | x ∈ S} u :=
    fun {u t S} ht hadj => isConnectedAvoiding_of_walk_mem ht hadj.toWalk (fun v hv _ => by
      simp at hv; exact hv)
  have hCa : IsCycleList G (a :: (A ++ b :: B)) := by
    have := hC.rotate k
    rw [hrot] at this
    simpa using this
  have hCb : IsCycleList G (b :: (B ++ a :: A)) := by
    have h2 := hC.rotate (k + (A.length + 1))
    rw [rotate_at_b hrot] at h2
    simpa using h2
  obtain ⟨ha1, ha2⟩ := hCa.adj_first_last (R := A ++ b :: B) (by simp)
  obtain ⟨hb1, hb2⟩ := hCb.adj_first_last (R := B ++ a :: A) (by simp)
  rw [← List.getLast_eq_getElem (h := by simp)] at ha2
  rw [← List.getLast_eq_getElem (h := by simp)] at hb2
  rw [List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _), List.getLast_cons hB] at ha2
  rw [List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _), List.getLast_cons hA] at hb2
  have h0A : (A ++ b :: B)[0]'(by simp) ∈ A := by
    rw [List.getElem_append_left (List.length_pos_of_ne_nil hA)]
    exact List.getElem_mem _
  have h0B : (B ++ a :: A)[0]'(by simp) ∈ B := by
    rw [List.getElem_append_left (List.length_pos_of_ne_nil hB)]
    exact List.getElem_mem _
  exact ⟨⟨hside h0A ha1, hside (List.getLast_mem _) ha2.symm⟩,
    ⟨hside (List.getLast_mem _) hb2.symm, hside h0B hb1⟩⟩

/-- The last entry of `l₀ ++ t :: R`, if it is not `t`, lies in `R`. -/
theorem mem_of_getLast {l₀ R : List V} {t w : V} (h : (l₀ ++ t :: R).getLast? = some w)
    (hw : w ≠ t) : w ∈ R := by
  rcases R.eq_nil_or_concat with rfl | ⟨R', v, rfl⟩
  · rw [List.getLast?_append_of_ne_nil _ (by simp)] at h
    simp at h
    exact absurd h.symm hw
  · rw [show l₀ ++ t :: R'.concat v = (l₀ ++ t :: R') ++ [v] by simp, List.getLast?_concat] at h
    simp only [Option.some.injEq] at h
    simp [h]

/-- A prefix of `l₀ ++ t :: R` that does not contain `t` is a prefix of `l₀`. -/
theorem prefix_of_not_mem {M l₀ R : List V} {t : V} (h : M <+: l₀ ++ t :: R) (ht : t ∉ M) :
    M <+: l₀ := by
  have hl₀ : l₀ <+: l₀ ++ t :: R := List.prefix_append _ _
  rcases le_or_gt M.length l₀.length with hle | hlt
  · exact List.prefix_of_prefix_length_le h hl₀ hle
  · have ht' : l₀ ++ [t] <+: l₀ ++ t :: R := by simp
    have := List.prefix_of_prefix_length_le ht' h (by simp; omega)
    exact absurd (this.subset (by simp)) ht

/-- The edge `y s` is an edge of every list that has `L₁ ++ [y, s]` as a prefix. -/
theorem isListEdge_of_prefix {L₁ l : List V} {y s : V} (h : L₁ ++ [y, s] <+: l) :
    IsListEdge l y s := by
  obtain ⟨t, rfl⟩ := h
  exact (IsListEdge.append_right (l₁ := L₁) ⟨(y, s), by simp, rfl⟩).append_left

/-- **The loop of Algorithm 5.2, with its edges** (Humeau and Pous, page 23). This is
`complete_loop` with three more conclusions, used to count the searches of the loop (Section 5.4,
page 24): every edge of `H` that is not an edge of `G` joins two consecutive vertices of the final
path `P'`, the vertex list of `P'` is a sublist of that of `P`, and every prefix of `P` whose vertices
are all on both sides is a prefix of `P'`. The last one is the reason for the first: the loop only
adds an edge `y_j y_s` after the prefix on both sides, and `y_s` then joins the prefix. -/
theorem complete_loop_edges [Finite V] (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ [])
    (hB : B ≠ []) :
    ∀ (n : ℕ) (G : SimpleGraph V) (P : G.Walk a b), P.support.length = n → IsCycleList G C →
      IsTPath G C P →
      (∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v) →
      Separates G {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B} →
      IsTight G C A B P.support →
      (∀ v ∈ P.support, IsSided G {x | x ∈ C ∨ x ∈ P.support} A B v) →
      ∃ H : SimpleGraph V, G ≤ H ∧ (IsCrossed H C → IsCrossed G C) ∧
        ∃ P' : H.Walk a b, IsTPath H C P' ∧ OnBothSides H C A B P' ∧
          Separates H {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} ∧
          (∀ u ∈ P'.support, ∀ v ∈ P'.support, H.Adj u v → IsListEdge P'.support u v) ∧
          IsTight H C A B P'.support ∧
          (∀ u v, H.Adj u v → G.Adj u v ∨ IsListEdge P'.support u v) ∧
          P'.support.Sublist P.support ∧
          (∀ M, M <+: P.support → (∀ v ∈ M,
              IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v ∧
              IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v) → M <+: P'.support) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G P hn hC hP hind hsep htight hsided
  classical
  set X : Set V := {x | x ∈ C ∨ x ∈ P.support} with hX
  by_cases hall : ∀ v ∈ P.support, IsOnSide G X {x | x ∈ A} v ∧ IsOnSide G X {x | x ∈ B} v
  · exact ⟨G, le_rfl, id, P, hP, hall, hsep, hind, htight, fun _ _ h => Or.inl h,
      List.Sublist.refl _, fun _ h _ => h⟩
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
  have prefix_step : ∀ {Q : List V} {s : V} {L₂ : List V} {H : SimpleGraph V}
      {P' : (G ⊔ edge y s).Walk a b} {P'' : H.Walk a b}, P.support = L₁ ++ [y] ++ t :: Q →
      ¬ (IsOnSide G X {x | x ∈ A} t ∧ IsOnSide G X {x | x ∈ B} t) →
      P'.support = L₁ ++ y :: s :: L₂ → P'.support.Sublist P.support →
      (∀ M, M <+: P'.support → (∀ v ∈ M,
        IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ A} v ∧
        IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ B} v) →
        M <+: P''.support) →
      ∀ M, M <+: P.support → (∀ v ∈ M,
        IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v ∧
        IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v) → M <+: P''.support := by
    intro Q s L₂ H P' P'' hsQ ht' hP's hsub' hpref M hM hMb
    have hM₀ : M <+: L₁ ++ [y] :=
      prefix_of_not_mem (hsQ ▸ hM) (fun htM => ht' (hMb t htM))
    refine hpref M (hM₀.trans (by rw [hP's]; exact ⟨s :: L₂, by simp⟩)) fun v hv => ?_
    have hX' : {x | x ∈ C ∨ x ∈ P'.support} ⊆ {x | x ∈ C ∨ x ∈ P.support} :=
      fun x hx => hx.imp id (fun h => hsub'.subset h)
    exact ⟨(hMb v hv).1.mono le_sup_left hX', (hMb v hv).2.mono le_sup_left hX'⟩
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
    have hsafe := strip_safe hC hrot hP hsupp hind htight hy.2 hsB hNB
    obtain ⟨P', hP', hP's, hboth⟩ := lemma_5_4_sides hrot hP hsupp hpre
      (Or.inr ⟨t, by simp, htA⟩) (Or.inl hsB)
    obtain ⟨hind', hsep', htight'⟩ := loop_invariant hrot hP hsupp hind htight hsep hNB hP's
    have hsub : P'.support.Sublist P.support := by rw [hP's, hsupp]; exact sublist_collapse
    obtain ⟨H, hle, hcr, P'', h1, h2, h3, h4, h5, hedge, hsub', hpref⟩ :=
      ih _ (hP's ▸ hlen hsupp (by simp)) (G ⊔ edge y s) P' rfl
      (hC.mono le_sup_left) hP' hind' hsep' htight'
      (hsubX le_sup_left hsub)
    exact ⟨H, le_sup_left.trans hle, fun h => hsafe (hcr h), P'', h1, h2, h3, h4, h5,
      edges_step hP's hboth hedge hpref, hsub'.trans hsub,
      prefix_step hsupp₀ ht hP's hsub hpref⟩
  · -- `t` is on side `B` only: `y_s` is the first vertex after it on side `A`
    have htA : ¬ IsOnSide G X {x | x ∈ A} t := fun h => ht ⟨h, htB⟩
    obtain ⟨N', s, L₂, rfl, hsA, hN'⟩ := exists_first_of_exists
      (fun v => IsOnSide G X {x | x ∈ A} v) R ⟨b, hbR, hends.2.1⟩
    have hsupp : P.support = L₁ ++ y :: (t :: N') ++ s :: L₂ := by rw [hsupp₀]; simp
    have hNA : ∀ v ∈ t :: N', ¬ IsOnSide G X {x | x ∈ A} v := fun v hv => by
      rcases List.mem_cons.mp hv with rfl | hv
      · exact htA
      · exact hN' v hv
    have hsafe := strip_safe_rev hC hrot hP hsupp hind htight hy.1 hsA hNA
    obtain ⟨P', hP', hP's, hboth⟩ := lemma_5_4_sides hrot hP hsupp hpre (Or.inl hsA)
      (Or.inr ⟨t, by simp, htB⟩)
    obtain ⟨hind', hsep', htight'⟩ := loop_invariant_rev hrot hP hsupp hind htight hsep hNA hP's
    have hsub : P'.support.Sublist P.support := by rw [hP's, hsupp]; exact sublist_collapse
    obtain ⟨H, hle, hcr, P'', h1, h2, h3, h4, h5, hedge, hsub', hpref⟩ :=
      ih _ (hP's ▸ hlen hsupp (by simp)) (G ⊔ edge y s) P' rfl
      (hC.mono le_sup_left) hP' hind' hsep' htight'
      (hsubX le_sup_left hsub)
    exact ⟨H, le_sup_left.trans hle, fun h => hsafe (hcr h), P'', h1, h2, h3, h4, h5,
      edges_step hP's hboth hedge hpref, hsub'.trans hsub,
      prefix_step hsupp₀ ht hP's hsub hpref⟩

/-- **The loop of Algorithm 5.2** (Humeau and Pous, page 23), from an induced, tight `C`-path that
separates `A` from `B` and whose vertices are all on some side. Each turn adds the edge `y_j y_s` of
Lemma 5.4 and replaces `P` by `P y_j y_s P` (lines 5 to 8). The loop ends with a graph `H ⊇ G` in
which `C` is crossed only if it is crossed in `G` (each edge is safe), and a `C`-path of `H` from `a`
to `b` that separates `A` from `B` and all of whose vertices are on both sides. The path also stays
induced and tight. -/
theorem complete_loop [Finite V] (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ [])
    (hB : B ≠ []) (n : ℕ) (G : SimpleGraph V) (P : G.Walk a b) (hn : P.support.length = n)
    (hC : IsCycleList G C) (hP : IsTPath G C P)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (hsep : Separates G {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B})
    (htight : IsTight G C A B P.support)
    (hsided : ∀ v ∈ P.support, IsSided G {x | x ∈ C ∨ x ∈ P.support} A B v) :
    ∃ H : SimpleGraph V, G ≤ H ∧ (IsCrossed H C → IsCrossed G C) ∧
      ∃ P' : H.Walk a b, IsTPath H C P' ∧ OnBothSides H C A B P' ∧
        Separates H {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} ∧
        (∀ u ∈ P'.support, ∀ v ∈ P'.support, H.Adj u v → IsListEdge P'.support u v) ∧
        IsTight H C A B P'.support := by
  obtain ⟨H, hle, hcr, P', h1, h2, h3, h4, h5, -⟩ :=
    complete_loop_edges hrot hA hB n G P hn hC hP hind hsep htight hsided
  exact ⟨H, hle, hcr, P', h1, h2, h3, h4, h5⟩

end GraphMinor.HP25
