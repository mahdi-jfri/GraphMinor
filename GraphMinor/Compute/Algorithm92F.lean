module

public import GraphMinor.Compute.Algorithm92Input

/-!
# Graph Minors XIII, (9.2): the subgraph `F` (`Algorithm92F.lean`)

Page 101 of Graph Minors XIII: "First, we determine $F$." The paper takes $F$ minimal such that
every $H_i$ is non-dividing in $H \cup F$, and uses minimality to bound the size of $F$. We build a
bounded `F` directly, one subwall at a time (`fBuild`). For each subwall `H_a` we are given an
`H`-path `P a` of `G` from the inside of `H_a` to a vertex of `H` outside `H_a` (it exists because
`H_a` is non-dividing). Then (`fStep`):

* if no inner vertex of `P a` lies on `F`, the path `P a` is added to `F`, and it is the `H`-path
  of `H_a`;
* otherwise let `z` be the first vertex of `P a` that lies on `F` and not on `H`. The part of
  `P a` up to `z` is added to `F`. The `H`-path of `H_a` follows `P a` up to `z` and then goes back
  along an earlier `H`-path (for some `H_b`) to its first vertex, which is inside `H_b`, hence
  outside `H_a`.

So `F` gets one path for each subwall. `isFSystem_fBuild` proves that the result satisfies
`IsFSystem`, when distinct subwalls are disjoint (which holds when `r ≥ 1`).
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

open WallOfHeight

variable {n h : ℕ} {G : MultiDigraph n}

/-- One step of the construction of `F`: the new path of `F` and the new `H`-path, from the
given `H`-path `P`, the paths `segs` of `F` so far and the `H`-paths `prs` so far. -/
def fStep (W : WallOfHeight h G) (P : List (Fin n)) (segs prs : List (List (Fin n))) :
    List (Fin n) × List (Fin n) :=
  match P.find? (fun y => decide (y ∈ segs.flatten ∧ y ∉ W.vertexFinset)) with
  | none => (P, P)
  | some z =>
    match prs.find? (fun Q => decide (z ∈ Q)) with
    | none => (P, P)
    | some pb => (P.take (P.idxOf z + 1), P.take (P.idxOf z + 1) ++ (pb.take (pb.idxOf z)).reverse)

/-- The construction of `F` for the subwalls in the list `as`: the paths of `F` and the `H`-paths,
one of each for every element of `as`, in the same order. -/
def fBuild {k : ℕ} (W : WallOfHeight h G) (P : Fin k → List (Fin n)) :
    List (Fin k) → List (List (Fin n)) × List (List (Fin n))
  | [] => ([], [])
  | a :: as =>
    ((fStep W (P a) (fBuild W P as).1 (fBuild W P as).2).1 :: (fBuild W P as).1,
      (fStep W (P a) (fBuild W P as).1 (fBuild W P as).2).2 :: (fBuild W P as).2)

/-- The ends of the paths of `F`. -/
def segEnds (segs : List (List (Fin n))) : List (Fin n) :=
  segs.flatMap (fun Q => Q.head?.toList ++ Q.getLast?.toList)

/-- An `H`-path for the subwall `W'`: from the inside of `W'` to a vertex of `W` outside `W'`. -/
def IsSubwallHPath {h' : ℕ} (W : WallOfHeight h G) (W' : WallOfHeight h' G) (Q : List (Fin n)) :
    Prop :=
  W.IsHPath Q ∧ (∀ y, Q.head? = some y → y ∈ W'.insideFinset) ∧
    (∀ y, Q.getLast? = some y → y ∈ W.vertexFinset \ W'.vertexFinset)

theorem take_idxOf_of_split {L A B : List (Fin n)} {z : Fin n} (h : L = A ++ z :: B) (hz : z ∉ A) :
    L.take (L.idxOf z) = A ∧ L.take (L.idxOf z + 1) = A ++ [z] := by
  have hidx : L.idxOf z = A.length := by rw [h, List.idxOf_append_of_notMem hz]; simp
  rw [hidx, h]
  refine ⟨List.take_left, ?_⟩
  rw [show A ++ z :: B = (A ++ [z]) ++ B by simp, show A.length + 1 = (A ++ [z]).length by simp,
    List.take_left]

theorem not_mem_of_nodup_split {L A B : List (Fin n)} {z : Fin n} (hL : L.Nodup)
    (h : L = A ++ z :: B) : z ∉ A ∧ z ∉ B := by
  subst h
  rw [List.nodup_append] at hL
  refine ⟨fun hz => hL.2.2 z hz z List.mem_cons_self rfl, fun hz => ?_⟩
  exact (List.nodup_cons.mp hL.2.1).1 hz

theorem mem_flatten_of_consec_edges {segs : List (List (Fin n))} {Q : List (Fin n)}
    (h2 : 2 ≤ Q.length) (hQ : ∀ y z, Consec Q y z → CEdge segs y z) {y : Fin n} (hy : y ∈ Q) :
    y ∈ segs.flatten := by
  obtain ⟨z, hz | hz⟩ := exists_consec_of_mem hy h2
  · obtain ⟨R, hR, hc | hc⟩ := hQ y z hz
    · exact List.mem_flatten.mpr ⟨R, hR, hc.mem_left⟩
    · exact List.mem_flatten.mpr ⟨R, hR, hc.mem_right⟩
  · obtain ⟨R, hR, hc | hc⟩ := hQ z y hz
    · exact List.mem_flatten.mpr ⟨R, hR, hc.mem_right⟩
    · exact List.mem_flatten.mpr ⟨R, hR, hc.mem_left⟩

theorem CEdge.mono {segs segs' : List (List (Fin n))} (hss : ∀ Q ∈ segs, Q ∈ segs') {y z : Fin n}
    (h : CEdge segs y z) : CEdge segs' y z := by
  obtain ⟨Q, hQ, hc⟩ := h
  exact ⟨Q, hss Q hQ, hc⟩

variable {k : ℕ} {hs : Fin k → ℕ} (W : WallOfHeight h G) (Wsub : ∀ a, WallOfHeight (hs a) G)

/-- The invariant of the construction, after the subwalls of the list `as`. -/
structure FInv (as : List (Fin k)) (segs prs : List (List (Fin n))) : Prop where
  len_prs : prs.length = as.length
  len_segs : segs.length = as.length
  seg_nodup : ∀ Q ∈ segs, Q.Nodup
  seg_walk : ∀ Q ∈ segs, IsSimpleWalkList G Q
  seg_inner : ∀ Q ∈ segs, ∀ y ∈ Q, y ∈ W.vertexFinset → Q.head? = some y ∨ Q.getLast? = some y
  seg_unique : ∀ Q ∈ segs, ∀ R ∈ segs, ∀ y ∈ Q, y ∈ R → Q = R ∨ y ∈ segEnds segs
  path : ∀ i (hi : i < as.length), IsSubwallHPath W (Wsub as[i]) (prs[i]'(len_prs ▸ hi)) ∧
    ∀ y z, Consec (prs[i]'(len_prs ▸ hi)) y z → CEdge segs y z
  cover : ∀ Q ∈ segs, ∀ y ∈ Q, ∃ Q' ∈ prs, y ∈ Q'

variable {W Wsub}

theorem FInv.nil : FInv W Wsub [] [] [] where
  len_prs := rfl
  len_segs := rfl
  seg_nodup := by simp
  seg_walk := by simp
  seg_inner := by simp
  seg_unique := by simp
  path := by simp
  cover := by simp

theorem segEnds_cons {Q : List (Fin n)} {segs : List (List (Fin n))} {y : Fin n} :
    y ∈ segEnds (Q :: segs) ↔ (Q.head? = some y ∨ Q.getLast? = some y) ∨ y ∈ segEnds segs := by
  simp [segEnds, or_assoc]

theorem consec_append {α : Type*} {Y : List α} {u v : α} : ∀ {X : List α},
    Consec (X ++ Y) u v →
      Consec X u v ∨ Consec Y u v ∨ (X.getLast? = some u ∧ Y.head? = some v)
  | [], h => Or.inr (Or.inl (by simpa using h))
  | x :: X', h => by
    obtain ⟨A, B, hAB⟩ := h
    cases A with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hAB
      obtain ⟨rfl, hAB⟩ := hAB
      cases X' with
      | nil =>
        right; right
        simp only [List.nil_append] at hAB
        exact ⟨rfl, by rw [hAB]; rfl⟩
      | cons x' X'' =>
        simp only [List.cons_append, List.cons.injEq] at hAB
        obtain ⟨rfl, -⟩ := hAB
        exact Or.inl ⟨[], X'', rfl⟩
    | cons w A =>
      simp only [List.cons_append, List.cons.injEq] at hAB
      rcases consec_append (X := X') ⟨A, B, hAB.2⟩ with h | h | ⟨h1, h2⟩
      · exact Or.inl (h.cons x)
      · exact Or.inr (Or.inl h)
      · right; right
        refine ⟨?_, h2⟩
        cases X' with
        | nil => simp at h1
        | cons y Y' => rw [getLast?_cons_of_ne_nil (List.cons_ne_nil _ _)]; exact h1

theorem isHPath_of {W : WallOfHeight h G} {L : List (Fin n)} (hne : L ≠ []) (h2 : 2 ≤ L.length)
    (hnd : L.Nodup) (hw : IsSimpleWalkList G L) (hh : L.head hne ∈ W.vertexFinset)
    (hl : L.getLast hne ∈ W.vertexFinset)
    (hin : ∀ v ∈ L, v ∈ W.vertexFinset → v = L.head hne ∨ v = L.getLast hne)
    (h3 : 3 ≤ L.length) : W.IsHPath L :=
  ⟨hne, h2, hnd, hw, hh, hl, (not_mem_drop_one_dropLast_iff hne h2 hnd _ hh hl).mpr hin,
    fun h => by omega⟩

/-- **One step keeps the invariant.** -/
theorem FInv.step (hdisj : ∀ a b, a ≠ b → Disjoint (Wsub a).vertexFinset (Wsub b).vertexFinset)
    {as : List (Fin k)} {segs prs : List (List (Fin n))} (hI : FInv W Wsub as segs prs)
    {a : Fin k} (ha : a ∉ as) {P : List (Fin n)} (hP : IsSubwallHPath W (Wsub a) P) :
    FInv W Wsub (a :: as) ((fStep W P segs prs).1 :: segs) ((fStep W P segs prs).2 :: prs) := by
  have hP' := hP
  obtain ⟨⟨hPne, hP2, hPnd, hPw, hPh, hPl, hPin, -⟩, hPhead, hPlast⟩ := hP'
  -- facts on `P`
  have hPV : ∀ y ∈ P, y ∈ W.vertexFinset → y = P.head hPne ∨ y = P.getLast hPne := by
    intro y hy hyW
    rcases mem_head_or_drop_one_dropLast_or_getLast hPne hy with h | h | h
    · exact Or.inl h
    · exact absurd hyW (hPin y h)
    · exact Or.inr h
  have hsa : P.head hPne ∈ (Wsub a).insideFinset := hPhead _ (List.head?_eq_some_head hPne)
  -- common facts for the new invariant
  have hlen := hI.len_prs
  have hlens := hI.len_segs
  unfold fStep
  split
  · -- no inner vertex of `P` is on `F`: add `P`
    rename_i hnone
    dsimp only
    rw [List.find?_eq_none] at hnone
    have hPF : ∀ y ∈ P, y ∈ segs.flatten → y ∈ W.vertexFinset := by
      intro y hy hyF
      by_contra hyW
      exact hnone y hy (by simp [hyF, hyW])
    refine ⟨by simp [hlen], by simp [hlens], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro Q hQ
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact hPnd
      · exact hI.seg_nodup Q hQ
    · intro Q hQ
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact hPw
      · exact hI.seg_walk Q hQ
    · intro Q hQ y hy hyW
      rcases List.mem_cons.mp hQ with rfl | hQ
      · rcases hPV y hy hyW with h | h
        · exact Or.inl (h ▸ List.head?_eq_some_head hPne)
        · exact Or.inr (h ▸ List.getLast?_eq_some_getLast hPne)
      · exact hI.seg_inner Q hQ y hy hyW
    · -- a vertex on `P` and on an older path is an end of `P`
      have hend : ∀ R ∈ segs, ∀ y ∈ P, y ∈ R → y ∈ segEnds (P :: segs) := by
        intro R hR y hyP hyR
        have hyW := hPF y hyP (List.mem_flatten.mpr ⟨R, hR, hyR⟩)
        rw [segEnds_cons]
        left
        rcases hPV y hyP hyW with h | h
        · exact Or.inl (h ▸ List.head?_eq_some_head hPne)
        · exact Or.inr (h ▸ List.getLast?_eq_some_getLast hPne)
      intro Q hQ R hR y hyQ hyR
      rcases List.mem_cons.mp hQ with hQP | hQs <;> rcases List.mem_cons.mp hR with hRP | hRs
      · exact Or.inl (hQP.trans hRP.symm)
      · exact Or.inr (hend R hRs y (hQP ▸ hyQ) hyR)
      · exact Or.inr (hend Q hQs y (hRP ▸ hyR) hyQ)
      · rcases hI.seg_unique Q hQs R hRs y hyQ hyR with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [segEnds_cons]; exact Or.inr h)
    · intro i hi
      cases i with
      | zero =>
        refine ⟨hP, ?_⟩
        · intro y z hyz
          exact ⟨P, List.mem_cons_self, Or.inl hyz⟩
      | succ i =>
        have hi' : i < as.length := by simpa using hi
        obtain ⟨h1, h2⟩ := hI.path i hi'
        refine ⟨by simpa using h1, fun y z hyz => ?_⟩
        exact CEdge.mono (fun Q hQ => List.mem_cons_of_mem _ hQ) (h2 y z (by simpa using hyz))
    · intro Q hQ y hy
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact ⟨Q, List.mem_cons_self, hy⟩
      · obtain ⟨Q', hQ', hyQ'⟩ := hI.cover Q hQ y hy
        exact ⟨Q', List.mem_cons_of_mem _ hQ', hyQ'⟩
  · rename_i z hz
    obtain ⟨hzp, l1, l2, hPsplit, hl1⟩ := List.find?_eq_some_iff_append.mp hz
    have hzF : z ∈ segs.flatten := (of_decide_eq_true hzp).1
    have hzW : z ∉ W.vertexFinset := (of_decide_eq_true hzp).2
    have hl1F : ∀ y ∈ l1, y ∈ segs.flatten → y ∈ W.vertexFinset := by
      intro y hy hyF
      by_contra hyW
      have := hl1 y hy
      simp [hyF, hyW] at this
    split
    · -- impossible: `z` is on an earlier `H`-path
      rename_i hnone
      exfalso
      obtain ⟨R, hR, hzR⟩ := List.mem_flatten.mp hzF
      obtain ⟨Q', hQ', hzQ'⟩ := hI.cover R hR z hzR
      rw [List.find?_eq_none] at hnone
      exact hnone Q' hQ' (by simpa using hzQ')
    · rename_i pb hpb
      have hpbmem : pb ∈ prs := List.mem_of_find?_eq_some hpb
      have hzpb : z ∈ pb := by simpa using List.find?_some hpb
      obtain ⟨j, hj, hjpb⟩ := List.mem_iff_getElem.mp hpbmem
      have hj' : j < as.length := hlen ▸ hj
      obtain ⟨hpbOK, hpbE⟩ := hI.path j hj'
      simp only [hjpb] at hpbOK hpbE
      have hab : a ≠ as[j] := fun h => ha (h ▸ List.getElem_mem hj')
      obtain ⟨⟨hpbne, hpb2, hpbnd, hpbw, hpbh, hpbl, hpbin, -⟩, hpbhead, -⟩ := hpbOK
      obtain ⟨A, B, hpbsplit⟩ := List.append_of_mem hzpb
      obtain ⟨hzA, -⟩ := not_mem_of_nodup_split hpbnd hpbsplit
      obtain ⟨hzl1, -⟩ := not_mem_of_nodup_split hPnd hPsplit
      rw [(take_idxOf_of_split hPsplit hzl1).2, (take_idxOf_of_split hpbsplit hzA).1]
      subst hPsplit
      subst hpbsplit
      dsimp only
      cases l1 with
      | nil => exact absurd (by simpa using hPh) hzW
      | cons sa l1' =>
      cases A with
      | nil => exact absurd (by simpa using hpbh) hzW
      | cons sb A' =>
      have hsa' : sa ∈ (Wsub a).insideFinset := hsa
      have hsb : sb ∈ (Wsub as[j]).insideFinset := hpbhead sb rfl
      have hsaV : sa ∈ (Wsub a).vertexFinset := (Finset.mem_sdiff.mp hsa').1
      have hsbV : sb ∈ (Wsub as[j]).vertexFinset := (Finset.mem_sdiff.mp hsb).1
      have hsbA : sb ∉ (Wsub a).vertexFinset :=
        Finset.disjoint_left.mp (hdisj _ _ (Ne.symm hab)) hsbV
      have hsbW : sb ∈ W.vertexFinset := hpbh
      have hl1W : ∀ y ∈ sa :: l1', y ∈ W.vertexFinset → y = sa := by
        intro y hy hyW
        by_contra hne
        have hy' : y ∈ l1' := (List.mem_cons.mp hy).resolve_left hne
        apply hPin y _ hyW
        simp [List.dropLast_append_of_ne_nil, hy']
      have hAW : ∀ y ∈ sb :: A', y ∈ W.vertexFinset → y = sb := by
        intro y hy hyW
        by_contra hne
        have hy' : y ∈ A' := (List.mem_cons.mp hy).resolve_left hne
        apply hpbin y _ hyW
        simp [List.dropLast_append_of_ne_nil, hy']
      have hAF : ∀ y ∈ sb :: A', y ∈ segs.flatten := fun y hy =>
        mem_flatten_of_consec_edges hpb2 hpbE (List.mem_append_left _ hy)
      have hl1F' : ∀ y ∈ sa :: l1', y ∈ segs.flatten → y = sa := fun y hy hyF =>
        hl1W y hy (hl1F y hy hyF)
      have hSnd : ((sa :: l1') ++ [z]).Nodup :=
        hPnd.sublist (List.IsPrefix.sublist ⟨l2, by simp⟩)
      have hSw : IsSimpleWalkList G ((sa :: l1') ++ [z]) :=
        isSimpleWalkList_infix hPw ⟨[], l2, by simp⟩
      have hpbz : ∀ v, (sb :: A').getLast? = some v → Consec ((sb :: A') ++ z :: B) v z := by
        intro v hv
        have hne : sb :: A' ≠ [] := List.cons_ne_nil _ _
        have hv' : (sb :: A').getLast hne = v :=
          Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hv)
        refine ⟨(sb :: A').dropLast, B, ?_⟩
        conv_lhs => rw [← List.dropLast_append_getLast hne]
        rw [hv']; simp
      have hArev : ∀ u v, Consec (sb :: A').reverse u v → Consec ((sb :: A') ++ z :: B) v u :=
        fun u v h => (consec_reverse.mp h).append_right _
      refine ⟨by simp [hlen], by simp [hlens], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro Q hQ
        rcases List.mem_cons.mp hQ with rfl | hQ
        · exact hSnd
        · exact hI.seg_nodup Q hQ
      · intro Q hQ
        rcases List.mem_cons.mp hQ with rfl | hQ
        · exact hSw
        · exact hI.seg_walk Q hQ
      · intro Q hQ y hy hyW
        rcases List.mem_cons.mp hQ with rfl | hQ
        · rw [List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | hyz
          · left; rw [hl1W y hy hyW]; rfl
          · exact absurd (hyz ▸ hyW) hzW
        · exact hI.seg_inner Q hQ y hy hyW
      · have hend : ∀ R ∈ segs, ∀ y ∈ (sa :: l1') ++ [z], y ∈ R →
            y ∈ segEnds (((sa :: l1') ++ [z]) :: segs) := by
          intro R hR y hyS hyR
          rw [segEnds_cons]
          left
          rw [List.mem_append, List.mem_singleton] at hyS
          rcases hyS with hy | hyz
          · rw [hl1F' y hy (List.mem_flatten.mpr ⟨R, hR, hyR⟩)]; left; rfl
          · right; rw [hyz]; exact List.getLast?_concat
        intro Q hQ R hR y hyQ hyR
        rcases List.mem_cons.mp hQ with hQP | hQs <;> rcases List.mem_cons.mp hR with hRP | hRs
        · exact Or.inl (hQP.trans hRP.symm)
        · exact Or.inr (hend R hRs y (hQP ▸ hyQ) hyR)
        · exact Or.inr (hend Q hQs y (hRP ▸ hyR) hyQ)
        · rcases hI.seg_unique Q hQs R hRs y hyQ hyR with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [segEnds_cons]; exact Or.inr h)
      · intro i hi
        cases i with
        | zero =>
          simp only [List.getElem_cons_zero]
          have hQne : (sa :: l1') ++ [z] ++ (sb :: A').reverse ≠ [] := by simp
          have hQl : ((sa :: l1') ++ [z] ++ (sb :: A').reverse).getLast hQne = sb :=
            Option.some.inj ((List.getLast?_eq_some_getLast hQne).symm.trans (by
              rw [List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_reverse]; rfl))
          have hQh : ((sa :: l1') ++ [z] ++ (sb :: A').reverse).head hQne = sa := rfl
          have hnd : ((sa :: l1') ++ [z] ++ (sb :: A').reverse).Nodup := by
            rw [List.nodup_append]
            refine ⟨hSnd, List.nodup_reverse.mpr
              (hpbnd.sublist (List.IsPrefix.sublist ⟨z :: B, rfl⟩)), ?_⟩
            intro y hy y' hy' hyy
            subst hyy
            rw [List.mem_reverse] at hy'
            rw [List.mem_append, List.mem_singleton] at hy
            rcases hy with hy | rfl
            · have h1 := hl1F' y hy (hAF y hy')
              have h2 := hAW y hy' (h1 ▸ hsaV |> fun _ => h1 ▸ (hPh : sa ∈ W.vertexFinset))
              exact hsbA (h2 ▸ h1 ▸ hsaV)
            · exact hzA hy'
          have hw : IsSimpleWalkList G ((sa :: l1') ++ [z] ++ (sb :: A').reverse) := by
            rw [isSimpleWalkList_iff_consec]
            intro u v huv
            rcases consec_append huv with h | h | ⟨h1, h2⟩
            · exact isSimpleWalkList_iff_consec.mp hSw u v h
            · exact (isSimpleWalkList_iff_consec.mp hpbw v u (hArev u v h)).symm
            · have hu : u = z := Option.some.inj (h1.symm.trans List.getLast?_concat)
              subst hu
              rw [List.head?_reverse] at h2
              exact (isSimpleWalkList_iff_consec.mp hpbw v u (hpbz v h2)).symm
          refine ⟨⟨isHPath_of hQne (by simp; omega) hnd hw (by rw [hQh]; exact hPh)
            (by rw [hQl]; exact hsbW) ?_ (by simp; omega), ?_, ?_⟩, ?_⟩
          · intro v hv hvW
            rw [hQh, hQl]
            rw [List.mem_append, List.mem_append, List.mem_singleton, List.mem_reverse] at hv
            rcases hv with (hv | rfl) | hv
            · exact Or.inl (hl1W v hv hvW)
            · exact absurd hvW hzW
            · exact Or.inr (hAW v hv hvW)
          · intro y hy
            have : y = sa := by simpa using hy.symm
            rw [this]; exact hsa'
          · intro y hy
            have : y = sb := by
              rw [List.getLast?_eq_some_getLast hQne, hQl] at hy
              exact (Option.some.inj hy).symm
            rw [this]; exact Finset.mem_sdiff.mpr ⟨hsbW, hsbA⟩
          · intro u v huv
            rcases consec_append huv with h | h | ⟨h1, h2⟩
            · exact ⟨_, List.mem_cons_self, Or.inl h⟩
            · exact CEdge.mono (fun Q hQ => List.mem_cons_of_mem _ hQ)
                (hpbE v u (hArev u v h)).symm
            · have hu : u = z := Option.some.inj (h1.symm.trans List.getLast?_concat)
              subst hu
              rw [List.head?_reverse] at h2
              exact CEdge.mono (fun Q hQ => List.mem_cons_of_mem _ hQ) (hpbE v u (hpbz v h2)).symm
        | succ i =>
          have hi' : i < as.length := by simpa using hi
          obtain ⟨h1, h2⟩ := hI.path i hi'
          refine ⟨by simpa using h1, fun y z hyz => ?_⟩
          exact CEdge.mono (fun Q hQ => List.mem_cons_of_mem _ hQ) (h2 y z (by simpa using hyz))
      · intro Q hQ y hy
        rcases List.mem_cons.mp hQ with rfl | hQ
        · exact ⟨_, List.mem_cons_self, List.mem_append_left _ hy⟩
        · obtain ⟨Q', hQ', hyQ'⟩ := hI.cover Q hQ y hy
          exact ⟨Q', List.mem_cons_of_mem _ hQ', hyQ'⟩

/-- **The construction keeps the invariant**, for every list of distinct subwalls. -/
theorem fInv_fBuild (hdisj : ∀ a b, a ≠ b → Disjoint (Wsub a).vertexFinset (Wsub b).vertexFinset)
    {P : Fin k → List (Fin n)} (hP : ∀ a, IsSubwallHPath W (Wsub a) (P a)) :
    ∀ as : List (Fin k), as.Nodup → FInv W Wsub as (fBuild W P as).1 (fBuild W P as).2
  | [], _ => FInv.nil
  | a :: as, hnd =>
    FInv.step hdisj (fInv_fBuild hdisj hP as (List.nodup_cons.mp hnd).2)
      (List.nodup_cons.mp hnd).1 (hP a)

/-! ### `F` for an input of (9.2) -/

variable {l m p r : ℕ}

/-- Distinct subwalls of an input with `r ≥ 1` are disjoint. -/
theorem disjoint_sub (x : Alg92Input l m p h k r) (hr : 1 ≤ r) (a b : Fin k)
    (hab : a ≠ b) : Disjoint (x.W_sub a).vertexFinset (x.W_sub b).vertexFinset := by
  rw [Finset.disjoint_left]
  intro u hua hub
  have := x.hdist a b hab u hua u hub
  simp [brickDist] at this
  omega

/-- The paths of `F` built from the `H`-paths `P`. -/
def fSegs (x : Alg92Input l m p h k r) (P : Fin k → List (Fin x.n)) : List (List (Fin x.n)) :=
  (fBuild x.W P (List.finRange k)).1

/-- The `H`-paths of the subwalls, built from the `H`-paths `P`. -/
def fHPaths (x : Alg92Input l m p h k r) (P : Fin k → List (Fin x.n)) (a : Fin k) :
    List (Fin x.n) :=
  (fBuild x.W P (List.finRange k)).2.getD a.1 []

theorem segEnds_subset_fNodes {x : Alg92Input l m p h k r} {segs : List (List (Fin x.n))}
    {y : Fin x.n} (hy : y ∈ segEnds segs) : y ∈ fNodes x segs := by
  unfold fNodes
  rw [Finset.mem_union, List.mem_toFinset]
  exact Or.inr hy

/-- **`F` satisfies the conditions of the search.** For an input with `r ≥ 1` and an `H`-path
`P a` for each subwall `H_a`, from its inside to a vertex of `H` outside it, the constructed `F`
satisfies `IsFSystem`. -/
theorem isFSystem_fSegs (x : Alg92Input l m p h k r) (hr : 1 ≤ r) {P : Fin k → List (Fin x.n)}
    (hP : ∀ a, IsSubwallHPath x.W (x.W_sub a) (P a)) :
    IsFSystem x (fSegs x P) (fHPaths x P) := by
  have hI := fInv_fBuild (disjoint_sub x hr) hP (List.finRange k) (List.nodup_finRange k)
  have hpa : ∀ a : Fin k, IsSubwallHPath x.W (x.W_sub a) (fHPaths x P a) ∧
      ∀ y z, Consec (fHPaths x P a) y z → CEdge (fSegs x P) y z := by
    intro a
    have ha : a.1 < (List.finRange k).length := by simp
    have h := hI.path a.1 ha
    have hga : (List.finRange k)[a.1]'ha = a := by simp
    have hgd : fHPaths x P a = (fBuild x.W P (List.finRange k)).2[a.1]'(hI.len_prs ▸ ha) := by
      unfold fHPaths
      rw [List.getD_eq_getElem]
    rw [hga] at h
    rw [hgd]
    exact h
  refine ⟨hI.seg_nodup, hI.seg_walk, ?_, ?_, fun a => (hpa a).1.1, fun a => (hpa a).1.2.1,
    fun a => (hpa a).1.2.2, fun a => (hpa a).2⟩
  · intro Q hQ y hy hyS hyW
    rcases hI.seg_inner Q hQ y hy hyW with h | h
    · exact hyS (mem_fNodes_of_head hQ h)
    · exact hyS (mem_fNodes_of_getLast hQ h)
  · intro Q hQ R hR y hyS hyQ hyR
    rcases hI.seg_unique Q hQ R hR y hyQ hyR with h | h
    · exact h
    · exact absurd (segEnds_subset_fNodes h) hyS

theorem length_fSegs (x : Alg92Input l m p h k r) (hr : 1 ≤ r) {P : Fin k → List (Fin x.n)}
    (hP : ∀ a, IsSubwallHPath x.W (x.W_sub a) (P a)) : (fSegs x P).length = k := by
  have hI := fInv_fBuild (disjoint_sub x hr) hP (List.finRange k) (List.nodup_finRange k)
  rw [fSegs, hI.len_segs, List.length_finRange]

end Alg92

end GraphMinor.Compute
