module

public import GraphMinor.Crossing.DefsHistory
import GraphMinor.Crossing.CutSec3
import GraphMinor.Crossing.CutSec2Fan

/-!
# Reverse replacement steps for a stored history

The history lift interface supplies a valid replacement and a crossing after it. The
statement of Lemma 1 also lists graph support and cycle-edge hypotheses, which its reverse
proof does not use. This file gives the reverse-search existence and arbitrary-search-path
splice steps with exactly the local hypotheses available in a history. The proof follows
Section 3 of the note and the proof of `lemma1Reverse_proved`: a boundary of size at most
three is used by at most one path, and a path through the recorded component replaces the
segment between its first and last boundary vertices.
-/

public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph Set Finset GraphMinor.Crossing

universe u

variable {V : Type u}

/-- If `L.IsChain R` and `L[i]? = some a` and `L[i + 1]? = some b`, then `R a b`. -/
private theorem isChain_rel_of_getElem? {R : V → V → Prop} :
    ∀ {L : List V} {i : ℕ} {a b : V},
      L.IsChain R → L[i]? = some a → L[i + 1]? = some b → R a b
  | [], _, _, _, _, h1, _ => by simp at h1
  | [_], 0, _, _, _, _, h2 => by simp at h2
  | [_], _ + 1, _, _, _, h1, _ => by simp at h1
  | x :: y :: rest, 0, a, b, hch, h1, h2 => by
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h1 h2
    subst a b
    exact List.IsChain.rel_head? hch rfl
  | _ :: y :: rest, i + 1, a, b, hch, h1, h2 => by
    simp only [List.getElem?_cons_succ] at h1 h2
    exact isChain_rel_of_getElem? hch.tail h1 h2

/-- If `L.IsChain r.newGraph.Adj` and `usesNewEdge r.graph L`, then `L` contains two distinct
vertices of `r.boundary`. -/
private theorem exists_two_mem_boundary_of_usesNewEdge {r : ReplRecord V} {L : List V}
    (hch : L.IsChain r.newGraph.Adj) (hnew : usesNewEdge r.graph L) :
    ∃ a b : V, a ∈ L ∧ b ∈ L ∧ a ∈ r.boundary ∧ b ∈ r.boundary ∧ a ≠ b := by
  rcases hnew with ⟨i, a, b, ha, hb, hnot_adj⟩
  have hadj_new : r.newGraph.Adj a b := isChain_rel_of_getElem? hch ha hb
  rcases hadj_new with ⟨hadj_old, -, -⟩ | ⟨ha_bd, hb_bd, hab⟩
  · exact False.elim (hnot_adj hadj_old)
  · exact ⟨a, b, List.mem_of_getElem? ha, List.mem_of_getElem? hb, ha_bd, hb_bd, hab⟩

/-- If `L.IsChain r.newGraph.Adj` and `¬ usesNewEdge r.graph L`, then `L.IsChain r.graph.Adj`. -/
private theorem isChain_of_not_usesNewEdge {G H : SimpleGraph V} :
    ∀ {L : List V}, L.IsChain H.Adj → ¬ usesNewEdge G L → L.IsChain G.Adj
  | [], _, _ => .nil
  | [a], _, _ => .singleton a
  | a :: b :: rest, hch, hnot => by
    have hab : G.Adj a b := by
      by_contra h
      exact hnot ⟨0, a, b, rfl, rfl, h⟩
    have hnot_tail : ¬ usesNewEdge G (b :: rest) := by
      rintro ⟨i, x, y, hx, hy, hxy⟩
      exact hnot ⟨i + 1, x, y, hx, hy, hxy⟩
    exact List.IsChain.cons_cons hab (isChain_of_not_usesNewEdge hch.tail hnot_tail)

/-- Every vertex of a chain in `G.Adj` of length at least `2` has a `G`-neighbor in the list. -/
private theorem exists_adj_of_mem_isChain {G : SimpleGraph V} :
    ∀ {L : List V}, 2 ≤ L.length → L.IsChain G.Adj → ∀ x ∈ L, ∃ y ∈ L, G.Adj x y
  | [], hlen, _ => by simp at hlen
  | [_], hlen, _ => by simp at hlen
  | a :: b :: rest, _, hch => by
    intro x hx
    have hab : G.Adj a b := List.IsChain.rel_head? hch rfl
    rcases List.mem_cons.mp hx with rfl | hx_tail
    · exact ⟨b, List.mem_cons_of_mem _ List.mem_cons_self, hab⟩
    · cases rest with
      | nil =>
        rcases List.mem_singleton.mp hx_tail with rfl
        exact ⟨a, List.mem_cons_self, hab.symm⟩
      | cons c rest' =>
        have hlen' : 2 ≤ (b :: c :: rest').length := by simp
        obtain ⟨y, hy, hadj⟩ := exists_adj_of_mem_isChain hlen' hch.tail x hx_tail
        exact ⟨y, List.mem_cons_of_mem _ hy, hadj⟩

/-- In a valid replacement, no vertex of a path list in `r.newGraph` of length `≥ 2` belongs to
`r.deleted`. -/
private theorem not_mem_deleted_of_mem_newGraph_chain {r : ReplRecord V} {D : List V}
    (hval : r.IsValid D) {L : List V} (hlen : 2 ≤ L.length) (hch : L.IsChain r.newGraph.Adj)
    {x : V} (hx : x ∈ L) :
    x ∉ r.deleted := by
  obtain ⟨y, _, hadj⟩ := exists_adj_of_mem_isChain hlen hch x hx
  rcases hadj with ⟨_, hx_not_del, _⟩ | ⟨hx_bd, _, _⟩
  · exact hx_not_del
  · exact (hval.2.2.2.1 hx_bd).2

private theorem exists_head?_of_ne_nil : ∀ {L : List V}, L ≠ [] → ∃ a, L.head? = some a
  | [], h => False.elim (h rfl)
  | a :: _, _ => ⟨a, rfl⟩

private theorem exists_snoc_of_ne_nil : ∀ {L : List V}, L ≠ [] → ∃ init last, L = init ++ [last]
  | [], h => False.elim (h rfl)
  | [a], _ => ⟨[], a, rfl⟩
  | a :: b :: rest, _ => by
    obtain ⟨init, last, heq⟩ := exists_snoc_of_ne_nil (List.cons_ne_nil b rest)
    exact ⟨a :: init, last, by simp [heq]⟩

private theorem exists_getLast?_of_ne_nil {L : List V} (h : L ≠ []) : ∃ a, L.getLast? = some a := by
  obtain ⟨init, last, rfl⟩ := exists_snoc_of_ne_nil h
  exact ⟨last, by simp⟩

private theorem head_dropWhile_false {p : V → Bool} :
    ∀ {L : List V} {a : V}, (L.dropWhile p).head? = some a → p a = false
  | [], _, h => by simp at h
  | x :: xs, a, h => by
    rw [List.dropWhile_cons] at h
    by_cases hpx : p x = true
    · simp only [hpx, ↓reduceIte] at h
      exact head_dropWhile_false h
    · simp only [hpx, Bool.false_eq_true, ↓reduceIte, List.head?_cons, Option.some.injEq] at h
      subst a
      exact Bool.eq_false_iff.mpr hpx

private theorem of_mem_takeWhile {p : V → Bool} :
    ∀ {L : List V} {a : V}, a ∈ L.takeWhile p → p a = true
  | [], _, h => by simp at h
  | x :: xs, a, h => by
    rw [List.takeWhile_cons] at h
    by_cases hpx : p x = true
    · simp only [hpx, ↓reduceIte, List.mem_cons] at h
      exact h.elim (fun ha => ha ▸ hpx) of_mem_takeWhile
    · simp [hpx] at h

/-- If `xs` contains an element where `p` is `false`, `takeWhile p (xs ++ ys) = takeWhile p xs`
and `dropWhile p (xs ++ ys) = dropWhile p xs ++ ys`. -/
private theorem takeWhile_dropWhile_append_of_exists_false {p : V → Bool} :
    ∀ {xs : List V} (ys : List V), (∃ x ∈ xs, p x = false) →
      (xs ++ ys).takeWhile p = xs.takeWhile p ∧
        (xs ++ ys).dropWhile p = xs.dropWhile p ++ ys
  | [], _, ⟨_, hx, _⟩ => by simp at hx
  | a :: xs, ys, ⟨x, hx, hpx⟩ => by
    simp only [List.cons_append, List.takeWhile_cons, List.dropWhile_cons]
    by_cases hpa : p a = true
    · simp only [hpa, ↓reduceIte]
      have hx_xs : x ∈ xs := by
        rcases List.mem_cons.mp hx with rfl | h
        · rw [hpa] at hpx; cases hpx
        · exact h
      obtain ⟨h1, h2⟩ := takeWhile_dropWhile_append_of_exists_false ys ⟨x, hx_xs, hpx⟩
      exact ⟨congrArg (a :: ·) h1, h2⟩
    · simp [hpa]

variable [DecidableEq V]

/-- Decomposition of a list `L` around its first and last vertices in `S`. -/
private theorem split_firstIn_lastIn {S : Finset V} {L : List V} {p q : V}
    (hp : firstIn S L = some p) (hq : lastIn S L = some q) :
    let pred := fun y => decide (y ∉ S)
    let A := L.takeWhile pred
    let C := (L.reverse.takeWhile pred).reverse
    ∃ M : List V,
      L = A ++ M ++ C ∧
      M.head? = some p ∧ M.getLast? = some q ∧
      p ∈ S ∧ q ∈ S ∧
      (∀ y ∈ A, y ∉ S) ∧ (∀ y ∈ C, y ∉ S) := by
  intro pred A C
  let B := L.dropWhile pred
  have hAB : A ++ B = L := List.takeWhile_append_dropWhile
  have hB_head : B.head? = some p := hp
  have hpB : p ∈ B := List.mem_of_head? hB_head
  have hpS : p ∈ S := by
    have hfalse : pred p = false := head_dropWhile_false hB_head
    simpa [pred] using hfalse
  have hp_rev : ∃ x ∈ B.reverse, pred x = false :=
    ⟨p, List.mem_reverse.mpr hpB, by simpa [pred] using hpS⟩
  have hL_rev : L.reverse = B.reverse ++ A.reverse := by
    rw [← hAB, List.reverse_append]
  obtain ⟨htake_rev, hdrop_rev⟩ :=
    takeWhile_dropWhile_append_of_exists_false A.reverse hp_rev
  let M := (B.reverse.dropWhile pred).reverse
  have hBM : B = M ++ C := by
    have h1 : B.reverse.takeWhile pred ++ B.reverse.dropWhile pred = B.reverse :=
      List.takeWhile_append_dropWhile
    have h2 := congrArg List.reverse h1
    rw [List.reverse_append, List.reverse_reverse] at h2
    dsimp [C, M]
    rw [hL_rev, htake_rev]
    exact h2.symm
  have hA_not_S : ∀ y ∈ A, y ∉ S := by
    intro y hy
    have h := of_mem_takeWhile hy
    simpa [pred] using h
  have hC_not_S : ∀ y ∈ C, y ∉ S := by
    intro y hy
    rw [List.mem_reverse] at hy
    have h := of_mem_takeWhile hy
    simpa [pred] using h
  have hM_ne : M ≠ [] := by
    intro hM
    rw [hM, List.nil_append] at hBM
    have hpC : p ∈ C := hBM ▸ hpB
    exact hC_not_S p hpC hpS
  have hM_head : M.head? = some p := by
    rw [← List.head?_append_of_ne_nil _ hM_ne, ← hBM, hB_head]
  have hrev_ne : B.reverse.dropWhile pred ≠ [] := by
    intro h; apply hM_ne; simp [M, h]
  have hrev_head : (B.reverse.dropWhile pred).head? = some q := by
    have hq' : (L.reverse.dropWhile pred).head? = some q := hq
    rwa [hL_rev, hdrop_rev, List.head?_append_of_ne_nil _ hrev_ne] at hq'
  have hM_last : M.getLast? = some q := by
    rw [← List.head?_reverse]
    simpa [M] using hrev_head
  have hqS : q ∈ S := by
    have hfalse : pred q = false := head_dropWhile_false hrev_head
    simpa [pred] using hfalse
  refine ⟨M, ?_, hM_head, hM_last, hpS, hqS, hA_not_S, hC_not_S⟩
  rw [List.append_assoc, ← hBM, hAB]

/-- If `L` contains an element of `S`, both `firstIn S L` and `lastIn S L` are `some`. -/
private theorem exists_firstIn_lastIn_of_mem {S : Finset V} {L : List V} {a : V}
    (haL : a ∈ L) (haS : a ∈ S) :
    ∃ p q : V, firstIn S L = some p ∧ lastIn S L = some q := by
  let pred := fun y => decide (y ∉ S)
  have hdrop_ne : L.dropWhile pred ≠ [] := by
    intro h
    have htake : L.takeWhile pred = L := by
      have := List.takeWhile_append_dropWhile (p := pred) (l := L)
      rwa [h, List.append_nil] at this
    have ha_take : a ∈ L.takeWhile pred := htake.symm ▸ haL
    have hpred := of_mem_takeWhile ha_take
    simp [pred, haS] at hpred
  have hdrop_rev_ne : L.reverse.dropWhile pred ≠ [] := by
    intro h
    have htake : L.reverse.takeWhile pred = L.reverse := by
      have := List.takeWhile_append_dropWhile (p := pred) (l := L.reverse)
      rwa [h, List.append_nil] at this
    have ha_take : a ∈ L.reverse.takeWhile pred := htake.symm ▸ (List.mem_reverse.mpr haL)
    have hpred := of_mem_takeWhile ha_take
    simp [pred, haS] at hpred
  obtain ⟨p, hp⟩ := exists_head?_of_ne_nil hdrop_ne
  obtain ⟨q, hq⟩ := exists_head?_of_ne_nil hdrop_rev_ne
  exact ⟨p, q, hp, hq⟩

omit [DecidableEq V] in
/-- Every walk `w : G.Walk a b` that is a path (`w.IsPath`) has `IsPathList G w.support` and
`HasEnds w.support a b`. -/
private theorem isPathList_support_of_isPath {G : SimpleGraph V} {a b : V} {w : G.Walk a b}
    (hw : w.IsPath) :
    IsPathList G w.support ∧ HasEnds w.support a b := by
  have hch : ∀ {u v : V} (q : G.Walk u v), q.support.IsChain G.Adj := by
    intro u v q
    induction q with
    | nil => exact List.isChain_singleton _
    | @cons u w v hadj rest ih =>
      rw [Walk.support_cons, List.isChain_cons]
      refine ⟨fun y hy => ?_, ih⟩
      have hy_eq : y = w := by
        cases rest <;> simp only [Walk.support_nil, Walk.support_cons, List.head?_cons,
          Option.mem_def, Option.some.injEq] at hy <;> exact hy.symm
      exact hy_eq ▸ hadj
  have hlast : ∀ {u v : V} (q : G.Walk u v), q.support.getLast? = some v := by
    intro u v q
    induction q with
    | nil => rfl
    | @cons u w v _ rest ih =>
      rw [Walk.support_cons, ← List.singleton_append,
        List.getLast?_append_of_ne_nil _ (Walk.support_ne_nil rest), ih]
  refine ⟨⟨Walk.support_ne_nil w, hw.support_nodup, hch w⟩, ?_, hlast w⟩
  cases w <;> rfl

/-- Existence of a search path `Y` in `r.rep ∪ {p, q}` when `usesNewEdge r.graph L₁`. -/
private theorem exists_replSearchPath {r : ReplRecord V} {D : List V} {L₁ : List V}
    (hval : r.IsValid D) (hch : L₁.IsChain r.newGraph.Adj) (hnew : usesNewEdge r.graph L₁) :
    ∃ Y, IsReplSearchPath r L₁ Y := by
  obtain ⟨a, _, haL₁, _, haS, _, _⟩ := exists_two_mem_boundary_of_usesNewEdge hch hnew
  obtain ⟨p, q, hp, hq⟩ := exists_firstIn_lastIn_of_mem haL₁ haS
  obtain ⟨_, _, _, _, hpS, hqS, _, _⟩ := split_firstIn_lastIn hp hq
  have hrep_comp : IsComponentIn r.graph r.deleted r.rep := hval.2.2.2.2.2
  have hrep_nbhd : nbhd r.graph r.rep = r.boundary := hval.2.2.2.2.1 r.rep hrep_comp
  have hp_nbhd : p ∈ nbhd r.graph r.rep := hrep_nbhd.symm ▸ hpS
  have hq_nbhd : q ∈ nbhd r.graph r.rep := hrep_nbhd.symm ▸ hqS
  rcases hp_nbhd.2 with ⟨ap, hap, hadj_ap⟩
  rcases hq_nbhd.2 with ⟨aq, haq, hadj_aq⟩
  obtain ⟨w_rep, hw_rep⟩ := hrep_comp.2.1.2 ap hap aq haq
  let U : Set V := r.rep ∪ {p, q}
  have hpU : p ∈ U := Or.inr (by simp)
  have hqU : q ∈ U := Or.inr (by simp)
  have hapU : ap ∈ U := Or.inl hap
  have haqU : aq ∈ U := Or.inl haq
  have hreach_U : ReachIn r.graph U p q := by
    have h1 : ReachIn r.graph U p ap := ReachIn.of_adj hadj_ap.symm hpU hapU
    have h2 : ReachIn r.graph U ap aq := ⟨w_rep, fun y hy => Or.inl (hw_rep y hy)⟩
    have h3 : ReachIn r.graph U aq q := ReachIn.of_adj hadj_aq haqU hqU
    exact (h1.trans h2).trans h3
  rcases hreach_U with ⟨w_U, hw_U⟩
  have hwalk_rest :
      ∀ {u v : V} (q₀ : r.graph.Walk u v),
        (∀ y ∈ q₀.support, y ∈ U) →
        ∃ q₁ : (HP25.restrict r.graph U).Walk u v, True := by
    intro u v q₀
    induction q₀ with
    | nil => intro _; exact ⟨.nil, trivial⟩
    | @cons u w v hadj rest ih =>
      intro hsupp
      have huU : u ∈ U := hsupp u (Walk.start_mem_support _)
      have hwU : w ∈ U := hsupp w (List.mem_cons_of_mem _ (Walk.start_mem_support _))
      obtain ⟨q₁, _⟩ := ih (fun y hy => hsupp y (List.mem_cons_of_mem _ hy))
      exact ⟨.cons ⟨hadj, huU, hwU⟩ q₁, trivial⟩
  obtain ⟨w_rest, _⟩ := hwalk_rest w_U hw_U
  let path_Y := w_rest.bypass
  obtain ⟨hpath_Y, hends_Y⟩ := isPathList_support_of_isPath w_rest.bypass_isPath
  exact ⟨path_Y.support, p, q, hp, hq, hpath_Y, hends_Y⟩

omit [DecidableEq V] in
/-- For any nodup list `L` of length at least `2` with `HasEnds L u v`, `y ∈ inner L` if and only if
`y ∈ L ∧ y ≠ u ∧ y ≠ v`. -/
private theorem mem_inner_iff_of_nodup {L : List V} {u v : V}
    (hnd : L.Nodup) (hlen : 2 ≤ L.length) (hends : HasEnds L u v) (y : V) :
    y ∈ inner L ↔ y ∈ L ∧ y ≠ u ∧ y ≠ v := by
  cases L with
  | nil => simp at hlen
  | cons a tail =>
    have htail_ne : tail ≠ [] := by
      intro h; simp [h] at hlen
    obtain ⟨mid, b, rfl⟩ := exists_snoc_of_ne_nil htail_ne
    have ha_eq : a = u := by
      have h1 := hends.1
      simp only [List.head?_cons, Option.some.injEq] at h1
      exact h1
    have hb_eq : b = v := by
      have h2 := hends.2
      rw [← List.singleton_append, List.getLast?_append_of_ne_nil _ (by simp)] at h2
      simpa using h2
    subst ha_eq hb_eq
    have hinner : inner (a :: (mid ++ [b])) = mid := by
      simp [GraphMinor.Crossing.inner]
    rw [hinner]
    have hnd_cons := List.nodup_cons.mp hnd
    have ha_not : a ∉ mid ++ [b] := hnd_cons.1
    have hnd_app := List.nodup_append.mp hnd_cons.2
    have hb_not : ∀ x ∈ mid, x ≠ b :=
      fun x hx => hnd_app.2.2 x hx b (List.mem_singleton.mpr rfl)
    constructor
    · intro hy
      refine ⟨List.mem_cons_of_mem _ (List.mem_append_left _ hy), ?_, hb_not y hy⟩
      rintro rfl
      exact ha_not (List.mem_append_left _ hy)
    · rintro ⟨hyL, hya, hyb⟩
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hyL
      rcases hyL with rfl | hy_mid | rfl
      · exact False.elim (hya rfl)
      · exact hy_mid
      · exact False.elim (hyb rfl)

omit [DecidableEq V] in
/-- Every step of `A ++ M` where `A` has no vertices in `r.boundary` and `(A ++ M).IsChain r.newGraph.Adj`
has `(A ++ [p]).IsChain r.graph.Adj` when `M.head? = some p`. -/
private theorem isChain_prefix_of_not_mem_boundary {r : ReplRecord V} :
    ∀ {A M : List V} {p : V},
      (A ++ M).IsChain r.newGraph.Adj →
      M.head? = some p →
      (∀ y ∈ A, y ∉ r.boundary) →
      (A ++ [p]).IsChain r.graph.Adj
  | [], M, p, _, _, _ => List.isChain_singleton p
  | [a], M, p, hch, hhead, hA => by
    cases M with
    | nil => simp at hhead
    | cons x rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst x
      simp only [List.singleton_append] at hch ⊢
      have hadj_new : r.newGraph.Adj a p := List.IsChain.rel_head? hch rfl
      have hadj_old : r.graph.Adj a p := by
        rcases hadj_new with ⟨h, -, -⟩ | ⟨ha_bd, -, -⟩
        · exact h
        · exact False.elim (hA a (List.mem_singleton.mpr rfl) ha_bd)
      exact List.isChain_pair.mpr hadj_old
  | a :: b :: rest, M, p, hch, hhead, hA => by
    simp only [List.cons_append] at hch ⊢
    have hadj_new : r.newGraph.Adj a b := List.IsChain.rel_head? hch rfl
    have hadj_old : r.graph.Adj a b := by
      rcases hadj_new with ⟨h, -, -⟩ | ⟨ha_bd, -, -⟩
      · exact h
      · exact False.elim (hA a List.mem_cons_self ha_bd)
    have ih := isChain_prefix_of_not_mem_boundary hch.tail hhead
      (fun y hy => hA y (List.mem_cons_of_mem _ hy))
    exact List.IsChain.cons_cons hadj_old ih

omit [DecidableEq V] in
/-- Symmetrically, if `(M ++ C).IsChain r.newGraph.Adj`, `M.getLast? = some q`, and `C` has no
vertices in `r.boundary`, then `(q :: C).IsChain r.graph.Adj`. -/
private theorem isChain_suffix_of_not_mem_boundary {r : ReplRecord V} {M C : List V} {q : V}
    (hch : (M ++ C).IsChain r.newGraph.Adj) (hlast : M.getLast? = some q)
    (hC : ∀ y ∈ C, y ∉ r.boundary) :
    (q :: C).IsChain r.graph.Adj := by
  have hrev_ch : (C.reverse ++ M.reverse).IsChain r.newGraph.Adj := by
    rw [← List.reverse_append, List.isChain_reverse]
    exact hch.imp fun _ _ h => h.symm
  have hrev_head : M.reverse.head? = some q := by
    rwa [List.head?_reverse]
  have hrev_C : ∀ y ∈ C.reverse, y ∉ r.boundary := by
    intro y hy; exact hC y (List.mem_reverse.mp hy)
  have h := isChain_prefix_of_not_mem_boundary hrev_ch hrev_head hrev_C
  have h' : (q :: C).IsChain (fun a b => r.graph.Adj b a) := by
    rw [← List.reverse_reverse (q :: C), List.isChain_reverse]
    simpa using h
  exact h'.imp fun _ _ hadj => hadj.symm

omit [DecidableEq V] in
/-- Joining `(L₁ ++ [p]).IsChain R` and `L₂.IsChain R` when `L₂.head? = some p`. -/
private theorem isChain_append_of_head? {R : V → V → Prop} :
    ∀ {L₁ L₂ : List V} {p : V},
      (L₁ ++ [p]).IsChain R → L₂.IsChain R → L₂.head? = some p → (L₁ ++ L₂).IsChain R
  | [], L₂, _, _, h2, _ => h2
  | [a], L₂, p, h1, h2, hhead => by
    cases L₂ with
    | nil => simp at hhead
    | cons x rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst x
      have hap : R a p := List.IsChain.rel_head? h1 rfl
      exact List.IsChain.cons_cons hap h2
  | a :: b :: rest, L₂, p, h1, h2, hhead => by
    simp only [List.cons_append] at h1 ⊢
    have hab : R a b := List.IsChain.rel_head? h1 rfl
    have htail : ((b :: rest) ++ [p]).IsChain R := h1.tail
    have ih : (b :: (rest ++ L₂)).IsChain R := isChain_append_of_head? htail h2 hhead
    exact List.IsChain.cons_cons hab ih

/-- Splicing a valid search path `Y` into `L₁` produces a valid `D`-path in `r.graph` with the same
ends and disjoint from `L₂`. -/
private theorem isCrossingPair_spliceBetween {r : ReplRecord V} {D L₁ L₂ Y : List V}
    (hval : r.IsValid D) (hcross : IsCrossingPair r.newGraph D L₁ L₂)
    (hnew : usesNewEdge r.graph L₁) (hY : IsReplSearchPath r L₁ Y) :
    IsCrossingPair r.graph D (spliceBetween r.boundary L₁ Y) L₂ := by
  have hnot_new₂ : ¬ usesNewEdge r.graph L₂ := by
    intro hnew₂
    obtain ⟨a₁, b₁, ha₁L, hb₁L, ha₁S, hb₁S, hab₁⟩ :=
      exists_two_mem_boundary_of_usesNewEdge hcross.1.1.2.2 hnew
    obtain ⟨a₂, b₂, ha₂L, hb₂L, ha₂S, hb₂S, hab₂⟩ :=
      exists_two_mem_boundary_of_usesNewEdge hcross.2.1.1.2.2 hnew₂
    have hdisj := List.disjoint_left.mp hcross.2.2.1
    have ha₁_ne_a₂ : a₁ ≠ a₂ := fun h => hdisj ha₁L (h ▸ ha₂L)
    have ha₁_ne_b₂ : a₁ ≠ b₂ := fun h => hdisj ha₁L (h ▸ hb₂L)
    have hb₁_ne_a₂ : b₁ ≠ a₂ := fun h => hdisj hb₁L (h ▸ ha₂L)
    have hb₁_ne_b₂ : b₁ ≠ b₂ := fun h => hdisj hb₁L (h ▸ hb₂L)
    let F : Finset V := {a₁, b₁, a₂, b₂}
    have hF_sub : F ⊆ r.boundary := by
      intro x hx
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hF_card : F.card = 4 := by
      simp [F, hab₁, hab₂, ha₁_ne_a₂, ha₁_ne_b₂, hb₁_ne_a₂, hb₁_ne_b₂]
    have hle := Finset.card_le_card hF_sub
    have hbd_le := hval.2.2.1
    omega
  have hL₂_dpath : IsDPathList r.graph D L₂ := by
    refine ⟨⟨hcross.2.1.1.1, hcross.2.1.1.2.1,
      isChain_of_not_usesNewEdge hcross.2.1.1.2.2 hnot_new₂⟩,
      hcross.2.1.2.1, hcross.2.1.2.2.1, hcross.2.1.2.2.2.1, hcross.2.1.2.2.2.2⟩
  rcases hY with ⟨p, q, hp, hq, hY_path, hY_ends⟩
  obtain ⟨M, hL₁_eq, hM_head, hM_last, hpS, hqS, hA_not_S, hC_not_S⟩ :=
    split_firstIn_lastIn hp hq
  let pred := fun y => decide (y ∉ r.boundary)
  let A := L₁.takeWhile pred
  let C := (L₁.reverse.takeWhile pred).reverse
  change L₁ = A ++ M ++ C at hL₁_eq
  have hsplice_eq : spliceBetween r.boundary L₁ Y = A ++ Y ++ C := rfl
  -- First, `p ≠ q` because `L₁` contains two distinct vertices of `r.boundary`, both in `M`.
  have hpq : p ≠ q := by
    obtain ⟨a₁, b₁, ha₁L, hb₁L, ha₁S, hb₁S, hab₁⟩ :=
      exists_two_mem_boundary_of_usesNewEdge hcross.1.1.2.2 hnew
    have ha₁M : a₁ ∈ M := by
      rw [hL₁_eq, List.mem_append, List.mem_append] at ha₁L
      rcases ha₁L with (ha₁A | ha₁M) | ha₁C
      · exact False.elim (hA_not_S a₁ ha₁A ha₁S)
      · exact ha₁M
      · exact False.elim (hC_not_S a₁ ha₁C ha₁S)
    have hb₁M : b₁ ∈ M := by
      rw [hL₁_eq, List.mem_append, List.mem_append] at hb₁L
      rcases hb₁L with (hb₁A | hb₁M) | hb₁C
      · exact False.elim (hA_not_S b₁ hb₁A hb₁S)
      · exact hb₁M
      · exact False.elim (hC_not_S b₁ hb₁C hb₁S)
    have hM_nd : M.Nodup := by
      have hnd := hcross.1.1.2.1
      rw [hL₁_eq] at hnd
      exact (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.1
    intro heq
    subst heq
    cases M with
    | nil => simp at hM_head
    | cons x rest =>
      simp only [List.head?_cons, Option.some.injEq] at hM_head
      subst x
      cases rest with
      | nil =>
        simp only [List.mem_singleton] at ha₁M hb₁M
        exact hab₁ (ha₁M.trans hb₁M.symm)
      | cons y rest' =>
        have hlast_mem : p ∈ y :: rest' :=
          List.mem_of_getLast? (by simpa using hM_last)
        exact (List.nodup_cons.mp hM_nd).1 hlast_mem
  -- Every vertex of `Y` is in `r.rep ∪ {p, q}`.
  have hY_mem : ∀ y ∈ Y, y ∈ r.rep ∪ {p, q} := by
    intro y hy
    have hlen_Y : 2 ≤ Y.length := by
      cases Y with
      | nil => exact False.elim (hY_path.1 rfl)
      | cons x rest =>
        cases rest with
        | nil =>
          have h1 := hY_ends.1
          have h2 := hY_ends.2
          simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at h1 h2
          exact False.elim (hpq (h1.symm.trans h2))
        | cons z rest' => simp
    obtain ⟨w, _, hadj⟩ := exists_adj_of_mem_isChain hlen_Y hY_path.2.2 y hy
    exact hadj.2.1
  -- Every vertex of `L₁` and `L₂` is outside `r.deleted`, while `r.rep ⊆ r.deleted`.
  have hrep_del : r.rep ⊆ r.deleted := hval.2.2.2.2.2.1
  have hL₁_not_del : ∀ y ∈ L₁, y ∉ r.deleted :=
    fun y hy => not_mem_deleted_of_mem_newGraph_chain hval hcross.1.2.1 hcross.1.1.2.2 hy
  have hL₂_not_del : ∀ y ∈ L₂, y ∉ r.deleted :=
    fun y hy => not_mem_deleted_of_mem_newGraph_chain hval hcross.2.1.2.1 hcross.2.1.1.2.2 hy
  have hpM : p ∈ M := List.mem_of_head? hM_head
  have hqM : q ∈ M := List.mem_of_getLast? hM_last
  have hpL₁ : p ∈ L₁ := by rw [hL₁_eq]; exact List.mem_append_left _ (List.mem_append_right _ hpM)
  have hqL₁ : q ∈ L₁ := by rw [hL₁_eq]; exact List.mem_append_left _ (List.mem_append_right _ hqM)
  -- `A ++ Y ++ C` is a chain in `r.graph.Adj`.
  have hL₁_ch : (A ++ M ++ C).IsChain r.newGraph.Adj := hL₁_eq ▸ hcross.1.1.2.2
  have hAM_ch : (A ++ M).IsChain r.newGraph.Adj := hL₁_ch.left_of_append
  have hMC_ch : (M ++ C).IsChain r.newGraph.Adj := by
    rw [List.append_assoc] at hL₁_ch
    exact hL₁_ch.right_of_append
  have hAp_ch : (A ++ [p]).IsChain r.graph.Adj :=
    isChain_prefix_of_not_mem_boundary hAM_ch hM_head hA_not_S
  have hqC_ch : (q :: C).IsChain r.graph.Adj :=
    isChain_suffix_of_not_mem_boundary hMC_ch hM_last hC_not_S
  have hY_ch : Y.IsChain r.graph.Adj := hY_path.2.2.imp fun _ _ h => h.1
  have hAY_ch : (A ++ Y).IsChain r.graph.Adj :=
    isChain_append_of_head? hAp_ch hY_ch hY_ends.1
  have hAYC_ch : (A ++ Y ++ C).IsChain r.graph.Adj := by
    have hY_ne : Y ≠ [] := hY_path.1
    obtain ⟨initY, lastY, hY_split⟩ := exists_snoc_of_ne_nil hY_ne
    have hlast_eq : lastY = q := by
      have h2 := hY_ends.2
      rw [hY_split, List.getLast?_append_of_ne_nil _ (by simp)] at h2
      simpa using h2
    subst lastY
    have hAY_split : A ++ Y = (A ++ initY) ++ [q] := by
      rw [hY_split, List.append_assoc]
    have hAY_ch' : ((A ++ initY) ++ [q]).IsChain r.graph.Adj := hAY_split ▸ hAY_ch
    have hres := isChain_append_of_head? hAY_ch' hqC_ch rfl
    have heq : A ++ initY ++ q :: C = A ++ Y ++ C := by simp [hY_split]
    exact heq ▸ hres
  -- `A ++ Y ++ C` is `Nodup`.
  have hL₁_nd : (A ++ M ++ C).Nodup := hL₁_eq ▸ hcross.1.1.2.1
  have hAM_nd : (A ++ M).Nodup := (List.nodup_append.mp hL₁_nd).1
  have hA_nd : A.Nodup := (List.nodup_append.mp hAM_nd).1
  have hC_nd : C.Nodup := (List.nodup_append.mp hL₁_nd).2.1
  have hAC_disj : A.Disjoint C :=
    fun y hyA hyC => (List.nodup_append.mp hL₁_nd).2.2 y (List.mem_append_left _ hyA) y hyC rfl
  have hAY_disj : A.Disjoint Y := by
    intro y hyA hyY
    rcases hY_mem y hyY with hy_rep | hy_pq
    · exact hL₁_not_del y (by rw [hL₁_eq]; exact List.mem_append_left _ (List.mem_append_left _ hyA))
        (hrep_del hy_rep)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_pq
      rcases hy_pq with hyp | hyq
      · exact hA_not_S p (hyp ▸ hyA) hpS
      · exact hA_not_S q (hyq ▸ hyA) hqS
  have hYC_disj : Y.Disjoint C := by
    intro y hyY hyC
    rcases hY_mem y hyY with hy_rep | hy_pq
    · exact hL₁_not_del y (by rw [hL₁_eq]; exact List.mem_append_right _ hyC)
        (hrep_del hy_rep)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_pq
      rcases hy_pq with hyp | hyq
      · exact hC_not_S p (hyp ▸ hyC) hpS
      · exact hC_not_S q (hyq ▸ hyC) hqS
  have hAY_nd : (A ++ Y).Nodup :=
    hA_nd.append hY_path.2.1 hAY_disj
  have hAYC_nd : (A ++ Y ++ C).Nodup := by
    refine hAY_nd.append hC_nd ?_
    intro y hyAY hyC
    rcases List.mem_append.mp hyAY with hyA | hyY
    · exact hAC_disj hyA hyC
    · exact hYC_disj hyY hyC
  -- `head?` and `getLast?` of `A ++ Y ++ C` match those of `L₁ = A ++ M ++ C`.
  have hM_ne : M ≠ [] := by intro h; simp [h] at hM_head
  have hY_ne : Y ≠ [] := hY_path.1
  have hhead_eq : (A ++ Y ++ C).head? = L₁.head? := by
    rw [hL₁_eq, List.append_assoc, List.append_assoc]
    by_cases hA_ne : A ≠ []
    · rw [List.head?_append_of_ne_nil _ hA_ne, List.head?_append_of_ne_nil _ hA_ne]
    · have hA_nil : A = [] := Classical.not_not.mp hA_ne
      rw [hA_nil]
      simp only [List.nil_append]
      rw [List.head?_append_of_ne_nil _ hY_ne, List.head?_append_of_ne_nil _ hM_ne,
        hY_ends.1, hM_head]
  have hlast_eq : (A ++ Y ++ C).getLast? = L₁.getLast? := by
    rw [hL₁_eq]
    by_cases hC_ne : C ≠ []
    · rw [List.getLast?_append_of_ne_nil _ hC_ne, List.getLast?_append_of_ne_nil _ hC_ne]
    · have hC_nil : C = [] := Classical.not_not.mp hC_ne
      rw [hC_nil]
      simp only [List.append_nil]
      rw [List.getLast?_append_of_ne_nil _ hY_ne, List.getLast?_append_of_ne_nil _ hM_ne,
        hY_ends.2, hM_last]
  -- Length of `A ++ Y ++ C` is at least 2.
  have hlen_Y : 2 ≤ Y.length := by
    cases Y with
    | nil => exact False.elim (hY_ne rfl)
    | cons x rest =>
      cases rest with
      | nil =>
        have h1 := hY_ends.1
        have h2 := hY_ends.2
        simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at h1 h2
        exact False.elim (hpq (h1.symm.trans h2))
      | cons z rest' => simp
  have hAYC_len : 2 ≤ (A ++ Y ++ C).length := by
    simp only [List.length_append]
    omega
  have hAYC_ne : A ++ Y ++ C ≠ [] := by
    intro h; simp [h] at hAYC_len
  -- Inner vertices of `A ++ Y ++ C` avoid `D`.
  have hinner_not_D : ∀ y ∈ inner (A ++ Y ++ C), y ∉ D := by
    intro y hy
    obtain ⟨u, hu⟩ := exists_head?_of_ne_nil hcross.1.1.1
    obtain ⟨v, hv⟩ := exists_getLast?_of_ne_nil hcross.1.1.1
    have hends_L₁ : HasEnds L₁ u v := ⟨hu, hv⟩
    have hends_AYC : HasEnds (A ++ Y ++ C) u v := ⟨hhead_eq.trans hu, hlast_eq.trans hv⟩
    obtain ⟨hy_AYC, hyu, hyv⟩ :=
      (mem_inner_iff_of_nodup hAYC_nd hAYC_len hends_AYC y).mp hy
    have hy_cases : y ∈ L₁ ∨ y ∈ r.deleted := by
      simp only [List.mem_append] at hy_AYC
      rcases hy_AYC with (hyA | hyY) | hyC
      · left; rw [hL₁_eq]; exact List.mem_append_left _ (List.mem_append_left _ hyA)
      · rcases hY_mem y hyY with hy_rep | hy_pq
        · right; exact hrep_del hy_rep
        · left
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_pq
          rcases hy_pq with rfl | rfl
          · exact hpL₁
          · exact hqL₁
      · left; rw [hL₁_eq]; exact List.mem_append_right _ hyC
    rcases hy_cases with hyL₁ | hy_del
    · have hy_inner_L₁ : y ∈ inner L₁ :=
        (mem_inner_iff_of_nodup hcross.1.1.2.1 hcross.1.2.1 hends_L₁ y).mpr ⟨hyL₁, hyu, hyv⟩
      exact hcross.1.2.2.2.2 y hy_inner_L₁
    · exact hval.2.1 y hy_del
  -- Disjointness from `L₂`.
  have hAYC_disj : (A ++ Y ++ C).Disjoint L₂ := by
    rw [List.disjoint_left]
    intro y hyAYC hyL₂
    simp only [List.mem_append] at hyAYC
    rcases hyAYC with (hyA | hyY) | hyC
    · exact List.disjoint_left.mp hcross.2.2.1
        (by rw [hL₁_eq]; exact List.mem_append_left _ (List.mem_append_left _ hyA)) hyL₂
    · rcases hY_mem y hyY with hy_rep | hy_pq
      · exact hL₂_not_del y hyL₂ (hrep_del hy_rep)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy_pq
        rcases hy_pq with rfl | rfl
        · exact List.disjoint_left.mp hcross.2.2.1 hpL₁ hyL₂
        · exact List.disjoint_left.mp hcross.2.2.1 hqL₁ hyL₂
    · exact List.disjoint_left.mp hcross.2.2.1
        (by rw [hL₁_eq]; exact List.mem_append_right _ hyC) hyL₂
  -- Assemble `IsCrossingPair`.
  rw [hsplice_eq]
  have hAYC_dpath : IsDPathList r.graph D (A ++ Y ++ C) := by
    refine ⟨⟨hAYC_ne, hAYC_nd, hAYC_ch⟩, hAYC_len, ?_, ?_, hinner_not_D⟩
    · intro a ha; exact hcross.1.2.2.1 a (hhead_eq ▸ ha)
    · intro b hb; exact hcross.1.2.2.2.1 b (hlast_eq ▸ hb)
  rcases hcross.2.2.2 with ⟨i, r_idx, j, s, hir, hrj, hjs, a, c, b, d, haD, hcD, hbD, hdD, hends⟩
  have hends_eq : ∀ u v : V, HasEndsUnordered (A ++ Y ++ C) u v ↔ HasEndsUnordered L₁ u v := by
    intro u v
    simp only [HasEndsUnordered, HasEnds, hhead_eq, hlast_eq]
  rw [← hends_eq a b, ← hends_eq c d] at hends
  exact ⟨hAYC_dpath, hL₂_dpath, hAYC_disj,
    i, r_idx, j, s, hir, hrj, hjs, a, c, b, d, haD, hcD, hbD, hdD, hends⟩

/-- First and last boundary visits belong to the recorded boundary. -/
theorem liftBoundaryEnds_mem {S : Finset V} {L : List V} {p q : V}
    (hp : firstIn S L = some p) (hq : lastIn S L = some q) : p ∈ S ∧ q ∈ S := by
  obtain ⟨_, _, _, _, hpS, hqS, _, _⟩ := split_firstIn_lastIn hp hq
  exact ⟨hpS, hqS⟩

/-- Lemma 1, reverse-search existence (Section 3): the recorded connected component
joins the first and last boundary vertices of the path that uses a new edge. -/
theorem liftReplacementSearch_exists {r : ReplRecord V} {D L : List V}
    (hvalid : r.IsValid D) (hchain : L.IsChain r.newGraph.Adj)
    (hnew : usesNewEdge r.graph L) : ∃ Y, IsReplSearchPath r L Y :=
  exists_replSearchPath hvalid hchain hnew

/-- Lemma 1, reverse splice (Section 3): any simple path found in the recorded component
between the prescribed boundary vertices gives the old crossing pair. -/
theorem liftReplacementSplice_crossing {r : ReplRecord V} {D L₁ L₂ Y : List V}
    (hvalid : r.IsValid D) (hcross : IsCrossingPair r.newGraph D L₁ L₂)
    (hnew : usesNewEdge r.graph L₁) (hY : IsReplSearchPath r L₁ Y) :
    IsCrossingPair r.graph D (spliceBetween r.boundary L₁ Y) L₂ :=
  isCrossingPair_spliceBetween hvalid hcross hnew hY

omit [DecidableEq V] in
/-- Lemma 1, retain case (Section 3): when neither path uses a new edge, both are old paths. -/
theorem liftReplacementRetain_crossing {r : ReplRecord V} {D L₁ L₂ : List V}
    (hcross : IsCrossingPair r.newGraph D L₁ L₂)
    (h₁ : ¬ usesNewEdge r.graph L₁) (h₂ : ¬ usesNewEdge r.graph L₂) :
    IsCrossingPair r.graph D L₁ L₂ :=
  ⟨⟨⟨hcross.1.1.1, hcross.1.1.2.1, isChain_of_not_usesNewEdge hcross.1.1.2.2 h₁⟩, hcross.1.2⟩,
    ⟨⟨hcross.2.1.1.1, hcross.2.1.1.2.1,
      isChain_of_not_usesNewEdge hcross.2.1.1.2.2 h₂⟩, hcross.2.1.2⟩, hcross.2.2⟩

end GraphMinor.Compute.Crossing
