module

public import GraphMinor.HP25.Prop52Tools
import GraphMinor.HP25.WebPath
import GraphMinor.HP25.WebSplit
import GraphMinor.HP25.Prop23
import GraphMinor.HP25.Prop32
import GraphMinor.HP25.Prop34
import GraphMinor.HP25.Prop34Tools
import GraphMinor.HP25.Alternate
import GraphMinor.HP25.Completion
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Lemma43Case2

/-!
# Proposition 5.2: the sides are crossless when `C` is

Humeau and Pous, proof of Proposition 5.2 (page 17), second item: "Suppose $C$ is crossless in $G$
... This construction provides a web completion of both $G_1$ and $G_2$ proving that $P_1P$ and
$P_2P$ are crossless, respectively in $G_1$ and $G_2$."

We prove that `P₁ P` is crossless in `G₁` (`SplitSetting.crossless_side₁`). As in the paper, take a
web completion `W` of `G` (here a maximal crossless completion, a web by `lemma_4_3_on`). `P` is induced in `W` (`induced_of_crossless`), so its inner vertices are
rib vertices (`WebData.mem_rib_of_induced`: two neighbours of a clique vertex are adjacent), and `W`
is the web composition along `P` of two webs (`WebData.split`). The side of `A` contains `P` and what
`A` reaches in `G - P`. The paper then adds back the components of `G - P` that reach neither side.
We do not build a completion of `G₁`; instead we move a crossing of `P₁ P` in `G₁` into the web side
of `W`: a crossing path through such a component joins consecutive vertices of `P`
(`consecutive_of_outside`), so it can be replaced by the edge between them.

The side `G₂` follows by symmetry (`SplitSetting.symm`), and `prop_5_2` puts the two directions
together.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

namespace WebData

variable {S : Set V} {C : List V} {R : Set V} {tri : V → Set V}

/-- Two distinct neighbours of a clique vertex of a web are adjacent. -/
theorem adj_of_clique (W : WebData G S C R tri) {x u w : V} (hx : x ∈ S \ R) (hu : G.Adj x u)
    (hw : G.Adj x w) (huw : u ≠ w) : G.Adj u w := by
  obtain ⟨a, b, c, ⟨-, -, -, hab, hbc, hac⟩, htri⟩ := W.tri_spec x hx
  rcases (W.adj_iff x hx u).mp hu with hu' | ⟨huS, -, hut⟩ <;>
    rcases (W.adj_iff x hx w).mp hw with hw' | ⟨hwS, -, hwt⟩
  · rw [htri] at hu' hw'
    simp only [mem_insert_iff, mem_singleton_iff] at hu' hw'
    rcases hu' with rfl | rfl | rfl <;> rcases hw' with rfl | rfl | rfl
    all_goals first | exact absurd rfl huw | assumption | exact G.adj_symm ‹_›
  · exact ((W.adj_iff w hwS u).mpr (Or.inl (hwt ▸ hu'))).symm
  · exact (W.adj_iff u huS w).mpr (Or.inl (hut ▸ hw'))
  · exact (W.adj_iff u huS w).mpr (Or.inr ⟨hwS, huw.symm, hwt.trans hut.symm⟩)

/-- The inner vertices of an induced path of a web are rib vertices. -/
theorem mem_rib_of_induced (W : WebData G S C R tri) {l : List V} (hnd : l.Nodup)
    (hch : l.IsChain G.Adj) (hS : ∀ v ∈ l, v ∈ S)
    (hind : ∀ u ∈ l, ∀ v ∈ l, G.Adj u v → IsListEdge l u v) {t : ℕ} (h0 : 0 < t)
    (ht : t + 1 < l.length) : l[t] ∈ R := by
  classical
  by_contra hx
  have hadj : ∀ i (hi : i + 1 < l.length), G.Adj (l[i]'(by omega)) l[i + 1] :=
    fun i hi => List.isChain_iff_getElem.mp hch i hi
  have h1 := hadj (t - 1) (by omega)
  simp only [show t - 1 + 1 = t by omega] at h1
  have h2 := hadj t ht
  have hne : l[t - 1]'(by omega) ≠ l[t + 1] := fun e => by
    have := hnd.getElem_inj_iff.mp e
    omega
  have huw := W.adj_of_clique ⟨hS _ (List.getElem_mem _), hx⟩ h1.symm h2 hne
  have := (hind _ (List.getElem_mem _) _ (List.getElem_mem _) huw).idxOf hnd
  rw [hnd.idxOf_getElem, hnd.idxOf_getElem] at this
  omega

end WebData

/-- In `a A b B` with `A` and `B` not empty, `a` and `b` are not consecutive. -/
theorem not_isCycleEdge_of_rotate {C : List V} (hnd : C.Nodup) {a b : V} {A B : List V} {k : ℕ}
    (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ []) (hB : B ≠ []) :
    ¬ PlaneEmbedding.IsCycleEdge C a b := by
  classical
  rw [← isCycleEdge_rotate C k, hrot]
  have hnd' : (a :: A ++ b :: B).Nodup := hrot ▸ List.nodup_rotate.mpr hnd
  rw [isCycleEdge_iff_idxOf hnd']
  have ha : (a :: A ++ b :: B).idxOf a = 0 := by simp
  have hb : (a :: A ++ b :: B).idxOf b = A.length + 1 := by
    have e : (a :: A ++ b :: B)[A.length + 1]'(by simp) = b := by simp
    have := hnd'.idxOf_getElem (A.length + 1) (by simp)
    rwa [e] at this
  have hA' := List.length_pos_of_ne_nil hA
  have hB' := List.length_pos_of_ne_nil hB
  rw [ha, hb]
  simp only [List.cons_append, List.length_cons, List.length_append]
  rintro ⟨-, -, h | h⟩
  · rw [Nat.mod_eq_of_lt (by omega)] at h
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at h
    omega

/-- Consecutive entries of a chain are adjacent. -/
theorem IsListEdge.adj_of_isChain {l : List V} (hnd : l.Nodup) (hch : l.IsChain G.Adj) {u v : V}
    (h : IsListEdge l u v) : G.Adj u v := by
  classical
  have hu := h.mem_left
  have hv := h.mem_right
  have hadj : ∀ i (hi : i + 1 < l.length), G.Adj (l[i]'(by omega)) l[i + 1] :=
    fun i hi => List.isChain_iff_getElem.mp hch i hi
  have hiu := List.idxOf_lt_length_of_mem hu
  have hiv := List.idxOf_lt_length_of_mem hv
  rcases h.idxOf hnd with e | e
  · have := hadj (l.idxOf u) (by omega)
    simp only [e, List.getElem_idxOf] at this
    exact this
  · have := hadj (l.idxOf v) (by omega)
    simp only [e, List.getElem_idxOf] at this
    exact this.symm

namespace SplitSetting

variable {C : List V} {a b : V} {A B m : List V} {k : ℕ} {P : G.Walk a b}
  {G₁ G₂ : SimpleGraph V} {S₁ S₂ : Set V}

/-- **Proposition 5.2, side 1 of the converse** (page 17): if `C` is crossless in `G`, then `P₁ P` is crossless in `G₁`. -/
theorem crossless_side₁ [Finite V]
    (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) (hsides : OnBothSides G C A B P)
    (hnc : ¬ IsCrossed G C) : ¬ IsCrossed G₁ (a :: A ++ b :: m.reverse) := by
  classical
  -- a web completion `W` of `G`, in which `P` is induced
  obtain ⟨W, hle, hmax⟩ := exists_maxCrosslessOn (G := G) (S := univ) (C := C)
    (fun _ _ _ => trivial) hnc
  have hweb : IsWebOn W univ C :=
    lemma_4_3_on _ W univ C rfl (hs.cyc.mono hle) (fun _ _ => trivial) hmax
  have hindP := hs.induced_of_crossless hsides hle hmax.2.1
  have hind : ∀ u ∈ a :: m ++ [b], ∀ v ∈ a :: m ++ [b], W.Adj u v →
      IsListEdge (a :: m ++ [b]) u v := by
    rw [← hs.supp]; exact hindP
  obtain ⟨R, tri, WD⟩ := hweb.exists_webData
  have hPnd : (a :: m ++ [b]).Nodup := hs.supp ▸ hs.path.1.support_nodup
  have hPch : (a :: m ++ [b]).IsChain W.Adj :=
    hs.supp ▸ (P.isChain_adj_support.imp fun _ _ h => hle h)
  have hCR := WD.rib.2.1
  have haC : a ∈ C := hs.path.2.1
  have hbC : b ∈ C := hs.path.2.2.1
  -- `P` lies in the rib
  have hl : IsPathList W R (a :: m ++ [b]) := by
    refine ⟨hPnd, hPch, fun v hv => ?_⟩
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hv
    by_cases h0 : t = 0
    · subst h0; simpa using hCR a haC
    by_cases h1 : t + 1 = (a :: m ++ [b]).length
    · have e : (a :: m ++ [b])[t] = b := by
        simp only [List.length_append, List.length_cons, List.length_nil] at h1
        simp [show t = m.length + 1 by omega]
      rw [e]; exact hCR b hbC
    · exact WD.mem_rib_of_induced hPnd hPch (fun _ _ => trivial) hind (by omega) (by omega)
  have hab := not_isCycleEdge_of_rotate hs.cyc.2.1 hs.rot hs.neA hs.neB
  obtain ⟨a', b', m', A', B', k', S₁', S₂', hl', hrot', -, hU, hI, hno, -, hH, -⟩ :=
    WD.split hs.rot hab hl (fun v hv => hs.m_not_mem hv) hind
  -- the split is along the same path, with the same sides of `C`
  obtain ⟨rfl, h2⟩ := List.cons_eq_cons.mp hl'
  obtain ⟨rfl, h3⟩ := List.append_inj' h2 rfl
  obtain rfl := List.singleton_inj.mp h3
  have hXY := rotate_eq_of_head hs.cyc.2.1 hs.rot hrot'
  obtain ⟨rfl, -⟩ := split_unique hXY (by
    have := hs.nodup
    rw [List.cons_append, List.nodup_cons] at this
    exact this.2)
  have hPS : ∀ x ∈ P.support, x ∈ S₁' := fun x hx => by
    have : x ∈ S₁' ∩ S₂' := by rw [hI, ← hs.supp]; exact hx
    exact this.1
  -- what `A` reaches in `G - P` lies on the side of `A`
  have hstep : ∀ {x y : V}, x ∈ S₁' → x ∉ P.support → W.Adj x y → y ∈ S₁' := by
    intro x y hx hxP hxy
    have hy : y ∈ S₁' ∪ S₂' := by rw [hU]; trivial
    rcases hy with hy | hy
    · exact hy
    · rcases hno x hx y hy hxy with h' | h'
      · have : x ∈ S₁' ∩ S₂' := ⟨hx, h'⟩
        rw [hI, ← hs.supp] at this
        exact absurd this hxP
      · exact h'
  have hwalk : ∀ {x y : V} (q : (restrict G {w | w ∉ P.support}).Walk x y), x ∈ S₁' →
      x ∉ P.support → y ∈ S₁' := by
    intro x y q
    induction q with
    | nil => exact fun h _ => h
    | cons hxy q ih => exact fun hx hxP => ih (hstep hx hxP (hle hxy.1)) hxy.2.2
  have hreach : ∀ c ∈ A, ∀ x, (restrict G {w | w ∉ P.support}).Reachable c x → x ∈ S₁' := by
    rintro c hc x ⟨q⟩
    exact hwalk q (hH.frame_subset c (by simp [hc])) (hs.AB_not_mem (List.mem_append_left _ hc))
  have hC₁S : ∀ x ∈ a :: A ++ b :: m.reverse, x ∈ S₁' := fun x hx => hH.frame_subset x hx
  have hPC₁ : ∀ x ∈ P.support, x ∈ a :: A ++ b :: m.reverse := fun x hx => by
    rw [hs.supp] at hx
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hx
    rcases hx with h | h | h <;> simp [h]
  have hle₁ : G₁ ≤ G := hs.comp.1 ▸ le_sup_left
  -- each path of a crossing of `P₁ P` in `G₁` moves into the side of `A` in `W`
  have hmove : ∀ {u v : V} (Q : G₁.Walk u v), IsTPath G₁ (a :: A ++ b :: m.reverse) Q →
      ∃ Q' : (restrict W S₁').Walk u v, IsTPath (restrict W S₁') (a :: A ++ b :: m.reverse) Q' ∧
        ∀ x ∈ Q'.support, x ∈ Q.support := by
    intro u v Q hQ
    have hQW := IsTPath.mapLe' hQ (hle₁.trans hle)
    by_cases hall : ∀ x ∈ Q.support, x ∈ S₁'
    · -- all of `Q` is on the side of `A`
      have hE : ∀ e ∈ (Q.mapLe (hle₁.trans hle)).edges, e ∈ (restrict W S₁').edgeSet := by
        intro e he
        have hE := (Q.mapLe (hle₁.trans hle)).edges_subset_edgeSet he
        induction e using Sym2.ind with
        | _ x y =>
          have hx := (Q.mapLe (hle₁.trans hle)).fst_mem_support_of_mem_edges he
          have hy := (Q.mapLe (hle₁.trans hle)).snd_mem_support_of_mem_edges he
          rw [Walk.support_mapLe_eq_support] at hx hy
          exact ⟨hE, hall x hx, hall y hy⟩
      refine ⟨(Q.mapLe (hle₁.trans hle)).transfer _ hE, ⟨hQW.1.transfer _, hQW.2.1, hQW.2.2.1,
        by rw [Walk.support_transfer]; exact hQW.2.2.2⟩, fun x hx => ?_⟩
      rw [Walk.support_transfer, Walk.support_mapLe_eq_support] at hx
      exact hx
    · -- `Q` runs through a component reaching neither side: its ends are consecutive on `P`
      push Not at hall
      obtain ⟨x, hxQ, hxS⟩ := hall
      have hxu : x ≠ u := fun e => hxS (e ▸ hC₁S u hQ.2.1)
      have hxv : x ≠ v := fun e => hxS (e ▸ hC₁S v hQ.2.2.1)
      have huv : u ≠ v := by
        rintro rfl
        have h0 := Walk.isPath_iff_nil.mp hQ.1
        rw [← Walk.eq_nil_iff_nil] at h0
        subst h0
        simp at hxQ
        exact hxu hxQ
      have hinner : ∀ y ∈ Q.support, y ≠ u → y ≠ v → y ∉ P.support := fun y hy h1 h2 hyP =>
        (hQ.2.2.2 y hy h1 h2).1 (hPC₁ y hyP)
      obtain ⟨I, hI'⟩ := IsXZPath.exists_middle (G := G₁) (C := []) (P := Q.support)
        ⟨Q.isChain_adj_support, hQ.1.support_nodup, Walk.support_head? Q,
          Walk.support_getLast? Q, fun _ _ h => by simp at h⟩ (by
          rw [Walk.length_support]
          have : Q.length ≠ 0 := fun h0 => huv (Walk.eq_of_length_eq_zero h0)
          omega)
      have hQnd := hQ.1.support_nodup
      rw [hI'] at hQnd
      have hIin : ∀ y ∈ I, y ∈ Q.support ∧ y ≠ u ∧ y ≠ v := fun y hy => by
        refine ⟨by rw [hI']; simp [hy], fun e => ?_, fun e => ?_⟩
        · subst e
          rw [List.cons_append, List.nodup_cons] at hQnd
          exact hQnd.1 (List.mem_append_left _ hy)
        · subst e
          rw [List.cons_append, List.nodup_cons, List.nodup_append] at hQnd
          exact hQnd.2.2.2 y hy y (by simp) rfl
      have hch := Q.isChain_adj_support
      rw [hI'] at hch
      have hIch : I.IsChain G.Adj :=
        (hch.tail.left_of_append).imp fun _ _ h => hle₁ h
      have hIP : ∀ y ∈ I, y ∈ {w | w ∉ P.support} := fun y hy =>
        hinner y (hIin y hy).1 (hIin y hy).2.1 (hIin y hy).2.2
      have hxI : x ∈ I := by
        have := hxQ
        rw [hI'] at this
        simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
          or_false] at this
        rcases this with h | h | h
        · exact absurd h hxu
        · exact h
        · exact absurd h hxv
      have hIA : ∀ y ∈ I, ¬ ∃ c ∈ A, (restrict G {w | w ∉ P.support}).Reachable c y := by
        rintro y hy ⟨c, hc, hr⟩
        exact hxS (hreach c hc x (hr.trans (chain_reach hIch hIP y hy x hxI)))
      -- the ends of `Q` are on `P`
      have hend : ∀ {e y : V}, e ∈ a :: A ++ b :: m.reverse → y ∈ I → G.Adj e y →
          e ∈ P.support := by
        intro e y he hy hey
        by_contra heP
        have heA : e ∈ A := by
          simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_reverse] at he
          rcases he with rfl | h | rfl | h
          · exact absurd P.start_mem_support heP
          · exact h
          · exact absurd P.end_mem_support heP
          · exact absurd (by rw [hs.supp]; simp [h]) heP
        exact hIA y hy ⟨e, heA, Adj.reachable ⟨hey, heP, hIP y hy⟩⟩
      obtain ⟨y₀, I', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hxI)
      have huP : u ∈ P.support :=
        hend hQ.2.1 (by simp) (hle₁ (List.isChain_cons_cons.mp hch).1)
      have hrev := List.isChain_reverse.mpr (hch.imp fun _ _ h => h.symm)
      simp only [List.cons_append, List.reverse_cons, List.reverse_append, List.reverse_nil,
        List.nil_append] at hrev
      obtain ⟨y₁, I'', hy₁⟩ := List.exists_cons_of_ne_nil (show (I'.reverse ++ [y₀]) ≠ [] by simp)
      rw [hy₁] at hrev
      have hy₁I : y₁ ∈ y₀ :: I' := by
        have : y₁ ∈ I'.reverse ++ [y₀] := by rw [hy₁]; simp
        simpa [or_comm] using this
      have hvP : v ∈ P.support :=
        hend hQ.2.2.1 hy₁I (hle₁ (List.isChain_cons_cons.mp hrev).1)
      have hedge := hs.consecutive_of_outside hsides hnc Q hQ.1 huP hvP huv fun y hy h1 h2 => by
        have hyI : y ∈ y₀ :: I' := by
          have := hy
          rw [hI'] at this
          simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
            or_false] at this
          rcases this with h | h | h | h
          · exact absurd h h1
          · exact List.mem_cons.mpr (Or.inl h)
          · exact List.mem_cons_of_mem _ h
          · exact absurd h h2
        exact ⟨hIP y hyI, hIA y hyI⟩
      have hWadj : W.Adj u v :=
        hle (hedge.adj_of_isChain hs.path.1.support_nodup P.isChain_adj_support)
      refine ⟨Walk.cons (show (restrict W S₁').Adj u v from ⟨hWadj, hPS u huP, hPS v hvP⟩)
        Walk.nil, ⟨by simp [huv], hQ.2.1, hQ.2.2.1, fun y hy h1 h2 => ?_⟩, fun y hy => ?_⟩
      · simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hy
        rcases hy with rfl | rfl
        · exact absurd rfl h1
        · exact absurd rfl h2
      · simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hy
        rcases hy with rfl | rfl
        · exact Q.start_mem_support
        · exact Q.end_mem_support
  rintro ⟨u₁, v₁, u₂, v₂, Q, R, hidx, hQ, hR, hdisj⟩
  obtain ⟨Q', hQ', hQs⟩ := hmove Q hQ
  obtain ⟨R', hR', hRs⟩ := hmove R hR
  exact hH.not_isCrossed ⟨u₁, v₁, u₂, v₂, Q', R', hidx, hQ', hR',
    fun x hx1 hx2 => hdisj (hQs x hx1) (hRs x hx2)⟩

/-- The setting seen from the other side: swap `A` and `B`, and walk `P` backwards. -/
theorem symm (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) :
    SplitSetting G C b a B A m.reverse (k + (A.length + 1)) P.reverse G₂ G₁ S₂ S₁ := by
  have hsupp : ∀ x, x ∈ P.reverse.support ↔ x ∈ P.support := fun x => by
    rw [Walk.support_reverse, List.mem_reverse]
  have hset : {v | v ∈ P.reverse.support} = {v | v ∈ P.support} := by
    ext x; exact hsupp x
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hs.comp
  refine ⟨hs.cyc, ?_, hs.neB, hs.neA, hs.path.reverse, ?_, ?_, ?_, hs.chain₂, hs.sub₂, hs.chain₁,
    hs.sub₁⟩
  · rw [← List.rotate_rotate, hs.rot, rotate_cons_append_cons]
  · rw [Walk.support_reverse, hs.supp]; simp
  · intro u hu w hw q
    obtain ⟨v, hv, hvP⟩ := hs.sep w hw u hu q.reverse
    exact ⟨v, by rwa [Walk.support_reverse, List.mem_reverse] at hv, (hsupp v).mpr hvP⟩
  · refine ⟨by rw [h1, sup_comm], h3, h2, by rw [union_comm, h4],
      by rw [inter_comm, h5, hset], ?_, ?_⟩
    · rw [Walk.support_reverse]
      exact List.isChain_reverse.mpr (h7.imp fun _ _ h => h.symm)
    · rw [Walk.support_reverse]
      exact List.isChain_reverse.mpr (h6.imp fun _ _ h => h.symm)

theorem _root_.GraphMinor.HP25.OnBothSides.symm {C A B : List V} {a b : V} {P : G.Walk a b}
    (h : OnBothSides G C A B P) : OnBothSides G C B A P.reverse := by
  have hset : {u | u ∈ C ∨ u ∈ P.reverse.support} = {u | u ∈ C ∨ u ∈ P.support} := by
    ext x; simp [Walk.support_reverse]
  intro v hv
  rw [Walk.support_reverse, List.mem_reverse] at hv
  rw [hset]
  exact ⟨(h v hv).2, (h v hv).1⟩

/-- **Proposition 5.2, side 2 of the converse** (page 17): if `C` is crossless in `G`, then `P₂ P` is crossless in `G₂`. It is side 1 for the setting seen from the
other side (`SplitSetting.symm`). -/
theorem crossless_side₂ [Finite V]
    (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) (hsides : OnBothSides G C A B P)
    (hnc : ¬ IsCrossed G C) : ¬ IsCrossed G₂ (b :: B ++ a :: m) := by
  have := hs.symm.crossless_side₁ hsides.symm hnc
  rwa [List.reverse_reverse] at this

/-- **Proposition 5.2** (page 17): "If $P$ separates $\mathring P_1$ from $\mathring P_2$ and all
vertices of $P$ are on both $P$-sides, then $C$ is crossed in $G$ if and only if $P_1P$ is crossed
in $G_1$ or $P_2P$ is crossed in $G_2$, where $G_1$ and $G_2$ are the subgraphs obtained by
Proposition 5.1." Both directions use Theorem 1.3, through `lemma_4_3_on`. -/
theorem _root_.GraphMinor.HP25.prop_5_2 [Finite V]
    (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) (hsides : OnBothSides G C A B P) :
    IsCrossed G C ↔ IsCrossed G₁ (a :: A ++ b :: m.reverse) ∨ IsCrossed G₂ (b :: B ++ a :: m) := by
  refine ⟨hs.crossed_side hsides, fun h => ?_⟩
  by_contra hnc
  rcases h with h | h
  · exact hs.crossless_side₁ hsides hnc h
  · exact hs.crossless_side₂ hsides hnc h

end SplitSetting

end GraphMinor.HP25
