module

public import GraphMinor.HP25.Completion
public import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.CrossTools
import GraphMinor.HP25.Embedding
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Prop34

/-!
# Lemma 4.3, first case: two frame vertices that are not `C`-connected

Humeau and Pous, proof of Lemma 4.3 (page 13), case 1: "There are two vertices $x$ and $x'$ of $C$
which are not $C$-connected". The paper takes "$P'$ the longest portion of $C$ containing $x'$ whose
inner vertices are all not $C$-connected to $x$", with ends `w` and `w'`, and `P` the rest of `C`. It
proves that no inner vertex of `P` is `C`-connected to an inner vertex of `P'`
(`lemma_4_3_case_one_sep`): such a path `Q`, with a path `R` from `x` to an end of `P`, either meets
`R` (then an inner vertex of `P'` is `C`-connected to `x`) or forms a crossing with it. So
`{w, w'}` separates; "adding the edge $ww'$ cannot create a crossing", and by maximality `ww'` is an
edge. "Hence, $G$ is the edge composition of two graphs along $ww'$ ... these two graphs are
maximally crossless ... By induction hypothesis they are webs and, by Proposition 3.1, $G$ is a
web."

Here we differ from the paper: instead of showing that the two sides are maximally crossless, we
show that their frames are crossless (a crossing of a side is a crossing of `C`), take maximally
crossless supergraphs on the same vertex sets, apply the induction hypothesis to those, and conclude
with `IsMaxCrosslessOn.eq_sup_of_pieces` (Proposition 3.1, Proposition 3.2 and the maximality of
`G`).
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-- The edges of the path `w w'`. -/
theorem isListEdge_pair {w w' u v : V} (hu : u ∈ w :: ([] : List V) ++ [w'])
    (hv : v ∈ w :: ([] : List V) ++ [w']) (huv : u ≠ v) : IsListEdge (w :: [] ++ [w']) u v := by
  simp only [List.nil_append, List.cons_append, List.mem_cons,
    List.not_mem_nil, or_false] at hu hv
  refine ⟨(w, w'), by simp, ?_⟩
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact absurd rfl huv
  · rfl
  · exact Sym2.eq_swap
  · exact absurd rfl huv

/-- **Meeting or crossing.** Let `x` be `C`-connected to `w` and `u` to `v`, all four on `C`, with
`x, w` alternating with `u, v`. Since `C` is crossless the two paths meet, and then `x` is
`C`-connected to `v`. -/
theorem connected_of_alternate {C : List V} (hnc : ¬ IsCrossed G C) {x w u v : V} (hx : x ∈ C)
    (hw : w ∈ C) (hu : u ∈ C) (hv : v ∈ C) (hgw : IsConnectedAvoiding G {y | y ∈ C} x {w})
    (hq : IsConnectedAvoiding G {y | y ∈ C} u {v})
    (halt : Alternate C x w u v ∨ Alternate C x w v u) (hwu : w ≠ u) (hwv : w ≠ v) (hux : u ≠ x)
    (huw : u ≠ w) : IsConnectedAvoiding G {y | y ∈ C} x {v} := by
  obtain ⟨w₀, hw₀, p, hp, hpin⟩ := hgw
  rw [mem_singleton_iff] at hw₀
  subst hw₀
  obtain ⟨v₀, hv₀, q, hq, hqin⟩ := hq
  rw [mem_singleton_iff] at hv₀
  subst hv₀
  have hpX : ∀ y ∈ p.support, y ∈ {y | y ∈ C} → y = x ∨ y = w₀ := fun y hy hyC => by
    by_contra hne
    push Not at hne
    exact hpin y hy hne.1 hne.2 hyC
  have hqX : ∀ y ∈ q.support, y ∈ {y | y ∈ C} → y = u ∨ y = v₀ := fun y hy hyC => by
    by_contra hne
    push Not at hne
    exact hqin y hy hne.1 hne.2 hyC
  by_cases hmeet : ∃ c ∈ p.support, c ∈ q.support
  · obtain ⟨c, hcp, hcq⟩ := hmeet
    refine connected_of_meet hp hq hpX hqX hcp hcq (fun hcw => ?_) (fun hcu => ?_)
    · subst hcw
      rcases hqX c hcq hw with h | h
      · exact hwu h
      · exact hwv h
    · subst hcu
      rcases hpX c hcp hu with h | h
      · exact absurd h hux
      · exact absurd h huw
  · exfalso
    push Not at hmeet
    have hdisj : p.support.Disjoint q.support := fun _ h1 h2 => hmeet _ h1 h2
    have hpT : IsTPath G C p := ⟨hp, hx, hw, fun y hy h1 h2 =>
      ⟨hpin y hy h1 h2, hpin y hy h1 h2⟩⟩
    have hqT : IsTPath G C q := ⟨hq, hu, hv, fun y hy h1 h2 =>
      ⟨hqin y hy h1 h2, hqin y hy h1 h2⟩⟩
    rcases halt with halt | halt
    · exact hnc (isCrossed_of_alternate' halt p q hpT hqT hdisj)
    · exact hnc (isCrossed_of_alternate' halt p q.reverse hpT hqT.reverse
        (by rw [Walk.support_reverse]; exact fun _ h1 h2 => hdisj h1 (List.mem_reverse.mp h2)))

/-- **`{w, w'}` separates** (page 14): "none of the inner vertices $u$ and $v$, respectively of $P$
and $P'$, are $C$-connected." Here `C` is, up to rotation, `x R`; `w = R[a]` and `w' = R[b]` are
`C`-connected to `x`, the entries strictly between them are not; `P'` has inner vertices
`R[a+1], …, R[b-1]`, and the inner vertices of `P` are `R[b+1], …, x, …, R[a-1]`. -/
theorem lemma_4_3_case_one_sep {C : List V} (hnc : ¬ IsCrossed G C) (hnd : C.Nodup) {x : V}
    {R : List V} {k : ℕ} (hrot : C.rotate k = x :: R) {a b : ℕ} (hab : a < b) (hb : b < R.length)
    (hgw : IsConnectedAvoiding G {y | y ∈ C} x {R[a]})
    (hgw' : IsConnectedAvoiding G {y | y ∈ C} x {R[b]})
    (hbad : ∀ t (ht : t < R.length), a < t → t < b →
      ¬ IsConnectedAvoiding G {y | y ∈ C} x {R[t]})
    {u v : V} (hu : u ∈ R.drop (b + 1) ++ x :: R.take a) (hv : v ∈ (R.take b).drop (a + 1)) :
    ¬ IsConnectedAvoiding G {y | y ∈ C} u {v} := by
  intro hq
  have hnd' : (x :: R).Nodup := by rw [← hrot]; exact List.nodup_rotate.mpr hnd
  have hxR : x ∉ R := (List.nodup_cons.mp hnd').1
  have hRnd : R.Nodup := (List.nodup_cons.mp hnd').2
  have hmem : ∀ y, y ∈ x :: R → y ∈ C := fun y hy => by
    rw [← hrot] at hy; exact List.mem_rotate.mp hy
  have hRC : ∀ y ∈ R, y ∈ C := fun y hy => hmem y (List.mem_cons_of_mem _ hy)
  have hxC : x ∈ C := hmem x List.mem_cons_self
  -- `v = R[t]` with `a < t < b`
  obtain ⟨i, hi, hvi⟩ := List.mem_drop_iff_getElem.mp hv
  simp only [List.length_take, lt_min_iff] at hi
  rw [List.getElem_take] at hvi
  subst hvi
  have hi1 : a + 1 + i < b := by omega
  have hi2 : a + 1 + i < R.length := by omega
  replace hi : a + 1 + i < b ∧ a + 1 + i < R.length := ⟨hi1, hi2⟩
  have hvbad := hbad (a + 1 + i) hi.2 (by omega) hi.1
  have hsplit : ∀ c (hc : c < R.length), x :: R = x :: R.take c ++ R[c] :: R.drop (c + 1) := by
    intro c hc
    rw [← List.drop_eq_getElem_cons hc]
    simp
  have hne : ∀ {c d : ℕ} (hc : c < R.length) (hd : d < R.length), c ≠ d → R[c] ≠ R[d] :=
    fun hc hd hcd h => hcd ((hRnd.getElem_inj_iff).mp h)
  rcases List.mem_append.mp hu with hu | hu
  · -- `u` lies after `w'`: use the path from `x` to `w' = R[b]`
    obtain ⟨q, hqR, rfl, hqb⟩ := exists_idx_of_mem_drop hu
    refine hvbad (connected_of_alternate hnc hxC (hRC _ (List.getElem_mem _))
      (hRC _ (List.getElem_mem _)) (hRC _ (List.getElem_mem _)) hgw' hq
      (Or.inr ⟨k, R.take b, R.drop (b + 1), by rw [hrot, hsplit b hb],
        (getElem_mem_take_iff hRnd _ b).mpr hi.1, hu⟩)
      (hne hb hqR (by omega)) (hne hb hi.2 (by omega))
      (fun h => hxR (h ▸ List.getElem_mem _)) (hne hqR hb (by omega)))
  · rcases List.mem_cons.mp hu with rfl | hu
    · exact hvbad hq
    · -- `u` lies before `w`: use the path from `x` to `w = R[a]`
      obtain ⟨q, hqR, rfl, hqa⟩ := exists_idx_of_mem_take hu
      have ha : a < R.length := by omega
      refine hvbad (connected_of_alternate hnc hxC (hRC _ (List.getElem_mem _))
        (hRC _ (List.getElem_mem _)) (hRC _ (List.getElem_mem _)) hgw hq
        (Or.inl ⟨k, R.take a, R.drop (a + 1), by rw [hrot, hsplit a ha], hu,
          (getElem_mem_drop_iff hRnd _ (a + 1)).mpr (by omega)⟩)
        (hne ha hqR (by omega)) (hne ha hi.2 (by omega))
        (fun h => hxR (h ▸ List.getElem_mem _)) (hne hqR ha (by omega)))

/-- The first vertex of a cycle `x R` is adjacent to the first and to the last entry of `R`. -/
theorem IsCycleList.adj_first_last {x : V} {R : List V} (hC : IsCycleList G (x :: R))
    (hne : R ≠ []) :
    G.Adj x (R[0]'(List.length_pos_of_ne_nil hne)) ∧
      G.Adj (R[R.length - 1]'(by have := List.length_pos_of_ne_nil hne; omega)) x := by
  have hch : (x :: R ++ [x]).IsChain G.Adj := by
    have hz := hC.2.2
    rw [zip_rotate_one_cons] at hz
    exact isChain_iff_zip.mpr hz
  constructor
  · obtain ⟨r, R', rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.getElem_cons_zero]
    exact (List.isChain_cons_cons.mp (by simpa using hch)).1
  · rw [← List.getLast_eq_getElem hne]
    apply (List.isChain_append.mp hch).2.2
    · simp [List.getLast?_cons, List.getLast?_eq_some_getLast hne]
    · simp

/-- **Lemma 4.3, case 1** (pages 13–14). Let `G` be maximally `C`-crossless on the finite set `S`,
with `C` a cycle of `G` inside `S`, and assume Lemma 4.3 for smaller vertex sets. If two vertices
`x`, `x'` of `C` are not `C`-connected, then `G` is a web on `S` with frame `C`. -/
theorem lemma_4_3_case_one [Finite V] {S : Set V} {C : List V}
    (ih : ∀ (G' : SimpleGraph V) (S' : Set V) (C' : List V), S'.ncard < S.ncard →
      IsCycleList G' C' → (∀ v ∈ C', v ∈ S') → IsMaxCrosslessOn G' S' C' → IsWebOn G' S' C')
    (h : IsMaxCrosslessOn G S C) (hC : IsCycleList G C) (hCS : ∀ v ∈ C, v ∈ S)
    {x x' : V} (hx : x ∈ C) (hx' : x' ∈ C) (hxx : x ≠ x')
    (hnc : ¬ IsConnectedAvoiding G {v | v ∈ C} x {x'}) : IsWebOn G S C := by
  classical
  set X : Set V := {v | v ∈ C} with hX
  have hnd := hC.2.1
  -- rotate `C` to start at `x`
  obtain ⟨l₁, l₂, hCe⟩ := List.append_of_mem hx
  set R := l₂ ++ l₁ with hR
  have hrot0 : C.rotate l₁.length = x :: R := by
    rw [hCe]; exact (List.rotate_append_length_eq l₁ (x :: l₂)).trans (by simp [hR])
  have hndR : (x :: R).Nodup := by rw [← hrot0]; exact List.nodup_rotate.mpr hnd
  have hxR : x ∉ R := (List.nodup_cons.mp hndR).1
  have hRnd : R.Nodup := (List.nodup_cons.mp hndR).2
  have hmemR : ∀ v, v ∈ C ↔ v = x ∨ v ∈ R := fun v => by
    rw [← List.mem_rotate (n := l₁.length), hrot0, List.mem_cons]
  have hRlen : 2 ≤ R.length := by
    have h3 := hC.1
    have := congrArg List.length hrot0
    simp at this; omega
  -- the two neighbours of `x` on `C` are `C`-connected to `x`
  have hCx : IsCycleList G (x :: R) := by rw [← hrot0]; exact hC.rotate _
  have hRne : R ≠ [] := List.ne_nil_of_length_pos (by omega)
  obtain ⟨hadj0, hadjL⟩ := hCx.adj_first_last hRne
  have good_adj : ∀ v, G.Adj x v → IsConnectedAvoiding G X x {v} := fun v hv =>
    isConnectedAvoiding_of_walk (Walk.cons hv Walk.nil) fun y hy _ => by
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hy
      exact hy
  -- `x' = R[j]`
  have hx'R : x' ∈ R := ((hmemR x').mp hx').resolve_left (Ne.symm hxx)
  obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx'R
  have hgood0 := good_adj _ hadj0
  have hgoodL := good_adj _ hadjL.symm
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; exact absurd (hjx ▸ hgood0) hnc
    · exact h0
  have hjL : j < R.length - 1 := by
    by_contra hge
    have : j = R.length - 1 := by omega
    subst this
    exact hnc (hjx ▸ hgoodL)
  -- the longest stretch `R[a+1], …, R[b-1]` around `x'` of vertices not `C`-connected to `x`
  let P : ℕ → Prop := fun i => ∃ hi : i < R.length, IsConnectedAvoiding G X x {R[i]}
  set a := Nat.findGreatest P j with ha
  have haP : P a := Nat.findGreatest_spec (m := 0) (Nat.zero_le j) ⟨by omega, hgood0⟩
  have haj : a < j := by
    rcases Nat.lt_or_ge a j with h' | h'
    · exact h'
    · have : a = j := le_antisymm (Nat.findGreatest_le j) h'
      obtain ⟨_, hg⟩ := haP
      simp only [this, hjx] at hg
      exact absurd hg hnc
  have hgap₁ : ∀ t, a < t → t ≤ j → ¬ P t := fun t h1 h2 => Nat.findGreatest_is_greatest h1 h2
  have hex : ∃ i, j < i ∧ P i := ⟨R.length - 1, hjL, by omega, hgoodL⟩
  set b := Nat.find hex with hb
  obtain ⟨hjb, hbl, hbP⟩ := Nat.find_spec hex
  have hgap₂ : ∀ t < b, ¬ (j < t ∧ P t) := fun t ht => Nat.find_min hex ht
  have hbad : ∀ t (ht : t < R.length), a < t → t < b → ¬ IsConnectedAvoiding G X x {R[t]} := by
    intro t ht h1 h2 hg
    by_cases htj : t ≤ j
    · exact hgap₁ t h1 htj ⟨ht, hg⟩
    · exact hgap₂ t h2 ⟨by omega, ht, hg⟩
  obtain ⟨hal, haP⟩ := haP
  have hab : a < b := by omega
  set w := R[a] with hw
  set w' := R[b] with hw'
  set A := (R.take b).drop (a + 1) with hA
  set B := R.drop (b + 1) ++ x :: R.take a with hB
  have hrot : C.rotate (l₁.length + (a + 1)) = w :: A ++ w' :: B := by
    rw [← List.rotate_rotate, hrot0, List.rotate_eq_drop_append_take (by simp; omega)]
    simp only [List.drop_succ_cons, List.take_succ_cons]
    rw [List.drop_eq_getElem_cons hal]
    have e : R.drop (a + 1) = A ++ R[b] :: R.drop (b + 1) := by
      rw [hA, List.drop_take, ← List.drop_eq_getElem_cons hbl]
      conv_lhs => rw [← List.take_append_drop (b - (a + 1)) (List.drop (a + 1) R)]
      rw [List.drop_drop]
      congr 2
      omega
    rw [e, hB]
    simp only [List.cons_append, List.append_assoc]
    rfl
  set k := l₁.length + (a + 1) with hk
  have hnd' : (w :: A ++ w' :: B).Nodup := by rw [← hrot]; exact List.nodup_rotate.mpr hnd
  have hmem : ∀ v, v ∈ C ↔ v = w ∨ v ∈ A ∨ v = w' ∨ v ∈ B := fun v => by
    rw [← List.mem_rotate (n := k), hrot]
    simp
  have hwC : w ∈ C := (hmem w).mpr (Or.inl rfl)
  have hw'C : w' ∈ C := (hmem w').mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hAC : ∀ v ∈ A, v ∈ C := fun v hv => (hmem v).mpr (Or.inr (Or.inl hv))
  have hBC : ∀ v ∈ B, v ∈ C := fun v hv => (hmem v).mpr (Or.inr (Or.inr (Or.inr hv)))
  have hnd'' := hnd'
  rw [List.cons_append, List.nodup_cons, List.nodup_append, List.nodup_cons] at hnd''
  obtain ⟨hwAB, hAnd, ⟨hw'B, hBnd⟩, hAB⟩ := hnd''
  have hwA : w ∉ A := fun h' => hwAB (List.mem_append_left _ h')
  have hwB : w ∉ B := fun h' => hwAB (List.mem_append_right _ (List.mem_cons_of_mem _ h'))
  have hww' : w ≠ w' := fun h' => hwAB (List.mem_append_right _ (h' ▸ List.mem_cons_self))
  have hw'A : w' ∉ A := fun h' => hAB w' h' w' List.mem_cons_self rfl
  have hAB' : ∀ v ∈ A, v ∉ B := fun v hv hvB => hAB v hv v (List.mem_cons_of_mem _ hvB) rfl
  have hx'A : x' ∈ A := by
    rw [← hjx, hA]
    exact List.mem_drop_iff_getElem.mpr ⟨j - (a + 1), by simp; omega, by
      rw [List.getElem_take]; congr 1; omega⟩
  have hxB : x ∈ B := by simp [hB]
  have hAne : A ≠ [] := List.ne_nil_of_mem hx'A
  have hBne : B ≠ [] := List.ne_nil_of_mem hxB
  -- "none of the inner vertices $u$ and $v$, respectively of $P$ and $P'$, are $C$-connected"
  have sep : ∀ u ∈ B, ∀ v ∈ A, ¬ IsConnectedAvoiding G X u {v} := fun u hu v hv =>
    lemma_4_3_case_one_sep h.2.1 hnd hrot0 hab hbl haP hbP hbad hu hv
  -- "adding the edge $ww'$ cannot create a crossing ... this edge must belong to $G$"
  have hadj : G.Adj w w' := by
    by_contra hn
    rcases isCrossed_sup_edge_cases (h.2.2 w (hCS w hwC) w' (hCS w' hw'C) hww' hn) hwC hw'C
      hww' with hc | ⟨c, d, Rp, halt, hRp⟩
    · exact h.2.1 hc
    · obtain ⟨hcA, hdB⟩ := halt.mem_of_rotate hnd hrot
      exact sep d hdB c hcA hRp.isConnectedAvoiding.symm'
  -- the two sides
  set Z : Set V := {v | ∃ a' ∈ A, (restrict G (S \ {w, w'})).Reachable a' v} with hZ
  have hZS : ∀ v ∈ Z, v ∈ S ∧ v ≠ w ∧ v ≠ w' := by
    rintro v ⟨a', ha', ⟨W⟩⟩
    by_cases hv : v = a'
    · subst hv
      exact ⟨hCS v (hAC v ha'), fun h' => hwA (h' ▸ ha'), fun h' => hw'A (h' ▸ ha')⟩
    · have := mem_of_mem_support_restrict W W.end_mem_support hv
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or] at this
      exact this
  have hAZ : ∀ v ∈ A, v ∈ Z := fun v hv => ⟨v, hv, Reachable.refl _⟩
  have hBZ : ∀ v ∈ B, v ∉ Z := by
    rintro v hvB ⟨a', ha', ⟨W⟩⟩
    have hW : ∀ y ∈ (W.mapLe (restrict_le G _)).support, y ∈ X → y ∈ {v | v ∈ A} ∨
        y ∈ {v | v ∈ B} := by
      intro y hy hyX
      rw [support_mapLe] at hy
      have hyw : y ≠ w ∧ y ≠ w' := by
        by_cases hya : y = a'
        · subst hya; exact ⟨fun h' => hwA (h' ▸ ha'), fun h' => hw'A (h' ▸ ha')⟩
        · have := mem_of_mem_support_restrict W hy hya
          simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or] at this
          exact this.2
      rcases (hmem y).mp hyX with h' | h' | h' | h'
      · exact absurd h' hyw.1
      · exact Or.inl h'
      · exact absurd h' hyw.2
      · exact Or.inr h'
    obtain ⟨a'', ha'', b'', hb'', hcon⟩ := exists_connected_of_walk (X := X)
      (W.mapLe (restrict_le G _)) hvB hW a' ha' Walk.nil (fun y hy h1 => by
        simp only [Walk.support_nil, List.mem_singleton] at hy; exact absurd hy h1)
    exact sep b'' hb'' a'' ha'' hcon.symm'
  set S₁ : Set V := Z ∪ {w, w'} with hS₁
  set S₂ : Set V := S \ Z with hS₂
  have hwS : w ∈ S := hCS w hwC
  have hw'S : w' ∈ S := hCS w' hw'C
  have hU : S₁ ∪ S₂ = S := by
    ext v
    constructor
    · rintro ((hv | hv | hv) | hv)
      · exact (hZS v hv).1
      · exact hv ▸ hwS
      · rw [mem_singleton_iff] at hv; exact hv ▸ hw'S
      · exact hv.1
    · intro hv
      by_cases hvZ : v ∈ Z
      · exact Or.inl (Or.inl hvZ)
      · exact Or.inr ⟨hv, hvZ⟩
  have hI : S₁ ∩ S₂ = {v | v ∈ w :: ([] : List V) ++ [w']} := by
    ext v
    simp only [mem_inter_iff, mem_union, mem_insert_iff, mem_singleton_iff, mem_sdiff,
      List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil,
      or_false, mem_ofPred_eq, hS₁, hS₂]
    constructor
    · rintro ⟨(hvZ | hv), -, hvZ'⟩
      · exact absurd hvZ hvZ'
      · exact hv
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), hwS, fun h' => (hZS _ h').2.1 rfl⟩
      · exact ⟨Or.inr (Or.inr rfl), hw'S, fun h' => (hZS _ h').2.2 rfl⟩
  have hGedge : ∀ u v, G.Adj u v → (u ∈ S₁ ∧ v ∈ S₁) ∨ (u ∈ S₂ ∧ v ∈ S₂) := by
    intro u v huv
    have huS := h.1 huv
    have hvS := h.1 huv.symm
    have ext : ∀ {u v : V}, G.Adj u v → u ∈ Z → v ∈ S → v ∈ S₁ := by
      intro u v huv huZ hvS
      by_cases hvw : v = w
      · exact Or.inr (Or.inl hvw)
      · by_cases hvw' : v = w'
        · exact Or.inr (Or.inr hvw')
        · obtain ⟨a', ha', hr⟩ := huZ
          obtain ⟨huS', huw, huw'⟩ := hZS u ⟨a', ha', hr⟩
          refine Or.inl ⟨a', ha', hr.trans (Adj.reachable ⟨huv, ?_, ?_⟩)⟩
          · simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or]
            exact ⟨huS', huw, huw'⟩
          · simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or]
            exact ⟨hvS, hvw, hvw'⟩
    by_cases huZ : u ∈ Z
    · exact Or.inl ⟨Or.inl huZ, ext huv huZ hvS⟩
    · by_cases hvZ : v ∈ Z
      · exact Or.inl ⟨ext huv.symm hvZ huS, Or.inl hvZ⟩
      · exact Or.inr ⟨⟨huS, huZ⟩, ⟨hvS, hvZ⟩⟩
  have hS₁S : S₁ ⊆ S := fun v hv => hU ▸ Or.inl hv
  have hS₂S : S₂ ⊆ S := fun v hv => hU ▸ Or.inr hv
  have hxS₁ : x ∉ S₁ := by
    rintro ((hv | hv | hv))
    · exact hBZ x hxB hv
    · exact hwB (hv ▸ hxB)
    · rw [mem_singleton_iff] at hv; exact hw'B (hv ▸ hxB)
  have hxS : x ∈ S := hCS x hx
  have hlt₁ : S₁.ncard < S.ncard :=
    Set.ncard_lt_ncard ⟨hS₁S, fun h' => hxS₁ (h' hxS)⟩ (Set.toFinite S)
  have hx'S₂ : x' ∉ S₂ := fun h' => h'.2 (hAZ x' hx'A)
  have hlt₂ : S₂.ncard < S.ncard :=
    Set.ncard_lt_ncard ⟨hS₂S, fun h' => hx'S₂ (h' (hCS x' hx'))⟩ (Set.toFinite S)
  -- the frames `w A w'` and `w' B w` of the two sides
  have hCrot : IsCycleList G (w :: A ++ w' :: B) := by rw [← hrot]; exact hC.rotate _
  have hF₁ : IsCycleList G (w :: A ++ [w']) := hCrot.of_chord hadj hAne
  have hrot₂ : C.rotate (k + (A.length + 1)) = w' :: B ++ w :: A := by
    rw [← List.rotate_rotate, hrot, rotate_cons_append_cons']
  have hF₂ : IsCycleList G (w' :: B ++ [w]) := by
    have : IsCycleList G (w' :: B ++ w :: A) := by rw [← hrot₂]; exact hC.rotate _
    exact this.of_chord hadj.symm hBne
  have hF₁S : ∀ v ∈ w :: A ++ [w'], v ∈ S₁ := by
    intro v hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | hv | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (hAZ v hv)
    · exact Or.inr (Or.inr rfl)
  have hF₂S : ∀ v ∈ w' :: B ++ [w], v ∈ S₂ := by
    intro v hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | hv | rfl
    · exact ⟨hw'S, fun h' => (hZS _ h').2.2 rfl⟩
    · exact ⟨hCS v (hBC v hv), hBZ v hv⟩
    · exact ⟨hwS, fun h' => (hZS _ h').2.1 rfl⟩
  -- a crossing of a side is a crossing of `C`
  have hnc₁ : ¬ IsCrossed (restrict G S₁) (w :: A ++ [w']) := fun hc =>
    h.2.1 (hc.of_restrict_prefix (k := k) (T₂ := B) (by rw [hrot]; simp) fun v hv h' => by
      rcases h' with hvZ | hvw | hvw'
      · exact hBZ v hv hvZ
      · exact hwB (hvw ▸ hv)
      · rw [mem_singleton_iff] at hvw'; exact hw'B (hvw' ▸ hv))
  have hnc₂ : ¬ IsCrossed (restrict G S₂) (w' :: B ++ [w]) := fun hc =>
    h.2.1 (hc.of_restrict_prefix (k := k + (A.length + 1)) (T₂ := A) (by rw [hrot₂]; simp)
      fun v hv h' => h'.2 (hAZ v hv))
  -- maximally crossless supergraphs of the sides are webs, by induction
  have hsupp : ∀ S' : Set V, IsSupportedOn (restrict G S') S' := fun S' _ _ huv => huv.2.1
  obtain ⟨W₁, hle₁, hW₁⟩ := exists_maxCrosslessOn (hsupp S₁) hnc₁
  obtain ⟨W₂, hle₂, hW₂⟩ := exists_maxCrosslessOn (hsupp S₂) hnc₂
  have hweb₁ := ih W₁ S₁ _ hlt₁ ((hF₁.restrict hF₁S).mono hle₁) hF₁S hW₁
  have hweb₂ := ih W₂ S₂ _ hlt₂ ((hF₂.restrict hF₂S).mono hle₂) hF₂S hW₂
  have hind : ∀ W : SimpleGraph V, ∀ u ∈ w :: ([] : List V) ++ [w'],
      ∀ v ∈ w :: ([] : List V) ++ [w'], W.Adj u v → IsListEdge (w :: [] ++ [w']) u v :=
    fun W u hu v hv huv => isListEdge_pair hu hv (W.ne_of_adj huv)
  -- "by Proposition 3.1, $G$ is a web"
  exact (h.eq_sup_of_pieces (m := []) hrot hU hI hGedge
    (by rw [List.reverse_nil]; exact hweb₁) hweb₂ hle₁ hle₂ (hind W₁) (hind W₂)).2

end GraphMinor.HP25
