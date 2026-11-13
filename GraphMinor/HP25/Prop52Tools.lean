module

public import GraphMinor.HP25.Prop52
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Lemma43Reroute
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.CycleEdges
import GraphMinor.HP25.Lemma43Fan

/-!
# Proposition 5.2: crossings through the middle of `P`

Tools for the converse of Proposition 5.2 (Humeau and Pous, page 17). In the setting of
Proposition 5.1, let `z = P[i+1]` be an inner vertex of `P` on both `P`-sides. The paths from `z` to
`A` and to `B` make a path `Y` from `A` to `B` through `z` (`SplitSetting.side_list`). Any path `X`
from `P[i]` to `P[j]`, `i + 2 ≤ j`, that misses `Y` and `C` and meets `P` only at its ends then gives
a crossing of `C`: "The pair $(PxQyP,RS)$ is a crossing of $C$ in $G$" (`SplitSetting.cross_of_bypass`).

With `X` an edge, this says that `P` is induced in every crossless graph containing `G`
(`SplitSetting.induced_of_crossless`): "The same method works when $D$ is replaced with an edge
between non-consecutive vertices of $P$. In particular, $P$ is induced in $G$."
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

namespace SplitSetting

variable {C : List V} {a b : V} {A B m : List V} {k : ℕ} {P : G.Walk a b}
  {G₁ G₂ : SimpleGraph V} {S₁ S₂ : Set V}

/-- A vertex of `P` on `C` is an end of `P`. -/
theorem P_mem_C (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) {w : V} (hw : w ∈ P.support)
    (hwC : w ∈ C) : w = a ∨ w = b := by
  by_contra hne
  push Not at hne
  exact (hs.path.2.2.2 w hw hne.1 hne.2).1 hwC

/-- **The crossing through a bypass** (page 17). A chain `X` of `H` from `P[i]` to `P[j]`,
`i + 2 ≤ j`, meeting `P` only at its ends and `C` only on `P`, and a chain `Y` of `H` from `A` to
`B` meeting `C` only at its ends, `P` only at `P[i+1]`, and missing `X`, make `C` crossed in `H`. -/
theorem cross_of_bypass (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) {H : SimpleGraph V}
    (hPH : P.support.IsChain H.Adj) {i j : ℕ} (hij : i + 2 ≤ j) (hj : j < P.support.length)
    {X : List V} (hX : X.IsChain H.Adj) (hXnd : X.Nodup)
    (hXh : X.head? = some (P.support[i]'(by omega))) (hXl : X.getLast? = some P.support[j])
    (hXP : ∀ w ∈ X, w ∈ P.support → w = P.support[i]'(by omega) ∨ w = P.support[j])
    (hXC : ∀ w ∈ X, w ∈ C → w ∈ P.support) {cA cB : V} (hcA : cA ∈ A) (hcB : cB ∈ B)
    {Y : List V} (hY : Y.IsChain H.Adj) (hYh : Y.head? = some cA) (hYl : Y.getLast? = some cB)
    (hYC : ∀ w ∈ Y, w ∈ C → w = cA ∨ w = cB)
    (hYP : ∀ w ∈ Y, w ∈ P.support → w = P.support[i + 1]'(by omega))
    (hXY : ∀ w ∈ X, w ∉ Y) : IsCrossed H C := by
  have hnd := hs.path.1.support_nodup
  obtain ⟨hc, nd, hh, hl, hmem⟩ := splice hPH hnd (p₂ := i) (p₄ := j) (by omega) hj
    (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem _) hX hXnd hXh hXl hXP
  have haC : a ∈ C := hs.path.2.1
  have hbC : b ∈ C := hs.path.2.2.1
  obtain ⟨Q₁, hQ₁, hQ₁s⟩ := exists_tPath_of_chain (T := C) hc (hh.trans (Walk.support_head? P))
    (hl.trans (Walk.support_getLast? P)) haC hbC (fun w hw hwC => by
      rcases hmem w hw with hw | ⟨q, hq, rfl, -⟩
      · exact hs.P_mem_C (hXC w hw hwC) hwC
      · exact hs.P_mem_C (List.getElem_mem _) hwC)
  have hcAC : cA ∈ C := hs.mem_C.mpr (by simp [hcA])
  have hcBC : cB ∈ C := hs.mem_C.mpr (by simp [hcB])
  obtain ⟨Q₂, hQ₂, hQ₂s⟩ := exists_tPath_of_chain (T := C) hY hYh hYl hcAC hcBC hYC
  refine isCrossed_of_alternate' ⟨k, A, B, hs.rot, hcA, hcB⟩ Q₁ Q₂ hQ₁ hQ₂ fun u hu1 hu2 => ?_
  have hu1' := hQ₁s u hu1
  have hu2' := hQ₂s u hu2
  rcases hmem u hu1' with hu | ⟨q, hq, rfl, hq'⟩
  · exact hXY u hu hu2'
  · have := hnd.getElem_inj_iff.mp (hYP _ hu2' (List.getElem_mem _))
    omega

/-- The vertices of a path from a vertex `z` of `P`, other than `z`, are reached in `G - P` from its
end, when only `z` is on `P`. -/
theorem reach_of_path {z c : V} {R : G.Walk z c} (hR : R.IsPath)
    (hoff : ∀ x ∈ R.support, x ≠ z → x ∉ P.support) {x : V} (hx : x ∈ R.support) (hxz : x ≠ z) :
    (restrict G {w | w ∉ P.support}).Reachable c x := by
  classical
  have hz := start_notMem_support_dropUntil hR hx hxz
  have hsub : ∀ y ∈ (R.dropUntil x hx).support, y ∉ P.support := fun y hy =>
    hoff y ((R.support_dropUntil_subset_support hx) hy) fun e => hz (e ▸ hy)
  refine Reachable.symm ⟨(R.dropUntil x hx).transfer (restrict G {w | w ∉ P.support}) ?_⟩
  intro e he
  have hE := (R.dropUntil x hx).edges_subset_edgeSet he
  induction e using Sym2.ind with
  | _ u v =>
    exact ⟨hE, hsub u ((R.dropUntil x hx).fst_mem_support_of_mem_edges he),
      hsub v ((R.dropUntil x hx).snd_mem_support_of_mem_edges he)⟩

/-- **The path `R S` of page 17.** For an inner vertex `z = P[i+1]` on both sides, there is a chain
of `G` from some `cA ∈ A` to some `cB ∈ B` whose vertices other than `z` are reached in `G - P` from
`A` or from `B`, that meets `C` only at its ends and `P` only at `z`. -/
theorem side_list (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂)
    (hsides : OnBothSides G C A B P) {i : ℕ} (hi : i + 2 < P.support.length) :
    ∃ cA ∈ A, ∃ cB ∈ B, ∃ Y : List V, Y.IsChain G.Adj ∧ Y.head? = some cA ∧
      Y.getLast? = some cB ∧ (∀ w ∈ Y, w ∈ C → w = cA ∨ w = cB) ∧
      (∀ w ∈ Y, w ∈ P.support → w = P.support[i + 1]'(by omega)) ∧
      ∀ w ∈ Y, w ≠ P.support[i + 1]'(by omega) →
        (∃ u ∈ A, (restrict G {w | w ∉ P.support}).Reachable u w) ∨
        (∃ u ∈ B, (restrict G {w | w ∉ P.support}).Reachable u w) := by
  have hnd := hs.path.1.support_nodup
  set z := P.support[i + 1]'(by omega) with hzdef
  have hz : z ∈ P.support := List.getElem_mem _
  have hzC : z ∉ C := fun hzC => by
    rcases hs.P_mem_C hz hzC with e | e
    · have e' : P.support[0]'(by omega) = a := by
        have := Walk.support_head? P
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at this
        exact Option.some.inj this
      have := hnd.getElem_inj_iff.mp (e.trans e'.symm)
      omega
    · have e' : P.support[P.support.length - 1]'(by omega) = b := by
        have := Walk.support_getLast? P
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at this
        exact Option.some.inj this
      have := hnd.getElem_inj_iff.mp (e.trans e'.symm)
      omega
  obtain ⟨cA, hcA, R, hR, hRin⟩ := (hsides z hz).1
  obtain ⟨cB, hcB, S, hS, hSin⟩ := (hsides z hz).2
  have hcA' : cA ∈ A := hcA
  have hcB' : cB ∈ B := hcB
  have hcAP : cA ∉ P.support := hs.AB_not_mem (List.mem_append_left _ hcA')
  have hcBP : cB ∉ P.support := hs.AB_not_mem (List.mem_append_right _ hcB')
  have hRoff : ∀ x ∈ R.support, x ≠ z → x ∉ P.support := fun x hx hxz => by
    by_cases hxc : x = cA
    · exact hxc ▸ hcAP
    · exact fun h' => hRin x hx hxz hxc (Or.inr h')
  have hSoff : ∀ x ∈ S.support, x ≠ z → x ∉ P.support := fun x hx hxz => by
    by_cases hxc : x = cB
    · exact hxc ▸ hcBP
    · exact fun h' => hSin x hx hxz hxc (Or.inr h')
  have hmem : ∀ w ∈ (R.reverse.append S).support, w ∈ R.support ∨ w ∈ S.support := by
    intro w hw
    rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hw
    exact hw
  refine ⟨cA, hcA', cB, hcB', (R.reverse.append S).support, Walk.isChain_adj_support _,
    Walk.support_head? _, Walk.support_getLast? _, fun w hw hwC => ?_, fun w hw hwP => ?_,
    fun w hw hwz => ?_⟩
  · rcases hmem w hw with hw | hw
    · by_cases hwz : w = z
      · exact absurd (hwz ▸ hwC) hzC
      by_cases hwc : w = cA
      · exact Or.inl hwc
      · exact absurd (Or.inl hwC) (hRin w hw hwz hwc)
    · by_cases hwz : w = z
      · exact absurd (hwz ▸ hwC) hzC
      by_cases hwc : w = cB
      · exact Or.inr hwc
      · exact absurd (Or.inl hwC) (hSin w hw hwz hwc)
  · by_contra hwz
    rcases hmem w hw with hw | hw
    · exact hRoff w hw hwz hwP
    · exact hSoff w hw hwz hwP
  · rcases hmem w hw with hw | hw
    · exact Or.inl ⟨cA, hcA', reach_of_path hR hRoff hw hwz⟩
    · exact Or.inr ⟨cB, hcB', reach_of_path hS hSoff hw hwz⟩

/-- **`P` is induced in every crossless graph containing `G`** (page 17): "The same method works when
$D$ is replaced with an edge between non-consecutive vertices of $P$. In particular, $P$ is induced
in $G$." -/
theorem induced_of_crossless (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂)
    (hsides : OnBothSides G C A B P) {W : SimpleGraph V} (hle : G ≤ W) (hnc : ¬ IsCrossed W C) :
    ∀ u ∈ P.support, ∀ v ∈ P.support, W.Adj u v → IsListEdge P.support u v := by
  have hnd := hs.path.1.support_nodup
  have key : ∀ t t' (ht : t' < P.support.length) (_ : t + 2 ≤ t'),
      ¬ W.Adj (P.support[t]'(by omega)) P.support[t'] := by
    intro t t' ht htt hadj
    obtain ⟨cA, hcA, cB, hcB, Y, hY, hYh, hYl, hYC, hYP, -⟩ := hs.side_list hsides (i := t) (by omega)
    have hne : P.support[t]'(by omega) ≠ P.support[t'] := fun e => by
      have := hnd.getElem_inj_iff.mp e
      omega
    refine hnc (hs.cross_of_bypass (H := W) (P.isChain_adj_support.imp fun _ _ h => hle h) htt ht
      (X := [P.support[t]'(by omega), P.support[t']]) (by simp [hadj]) (by simp [hne]) rfl rfl
      (fun w hw _ => by simpa using hw) (fun w hw _ => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> exact List.getElem_mem _)
      hcA hcB (hY.imp fun _ _ h => hle h) hYh hYl hYC hYP fun w hw hwY => ?_)
    have e := hYP w hwY
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · have := hnd.getElem_inj_iff.mp (e (List.getElem_mem _))
      omega
    · have := hnd.getElem_inj_iff.mp (e (List.getElem_mem _))
      omega
  intro u hu v hv huv
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hu
  obtain ⟨t', ht', rfl⟩ := List.getElem_of_mem hv
  have hne : t ≠ t' := fun e => by subst e; exact W.ne_of_adj huv rfl
  rcases (show t' = t + 1 ∨ t = t' + 1 ∨ t + 2 ≤ t' ∨ t' + 2 ≤ t by omega)
    with rfl | rfl | h' | h'
  · exact isListEdge_getElem _ t ht'
  · exact (isListEdge_getElem _ t' ht).symm
  · exact absurd huv (key t t' ht' h')
  · exact absurd huv.symm (key t' t ht h')

/-- What `B` reaches in `G - P` lies in `S₂`. -/
theorem reachB_sub (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) {u w : V} (hu : u ∈ B)
    (h : (restrict G {w | w ∉ P.support}).Reachable u w) : w ∈ S₂ := by
  obtain ⟨W⟩ := h
  have step : ∀ {x y : V}, x ∈ S₂ → x ∉ P.support → G.Adj x y → y ∈ S₂ := by
    intro x y hx hxP hxy
    have : (G₁ ⊔ G₂).Adj x y := hs.comp.1 ▸ hxy
    rcases this with h' | h'
    · have : x ∈ S₁ ∩ S₂ := ⟨hs.comp.2.1 h', hx⟩
      rw [hs.comp.2.2.2.2.1] at this
      exact absurd this hxP
    · exact hs.comp.2.2.1 h'.symm
  have key : ∀ {x y : V} (q : (restrict G {w | w ∉ P.support}).Walk x y), x ∈ S₂ →
      x ∉ P.support → y ∈ S₂ := by
    intro x y q
    induction q with
    | nil => exact fun h _ => h
    | cons hxy q ih => exact fun hx hxP => ih (step hx hxP hxy.1) hxy.2.2
  exact key W (hs.sub₂ u (List.mem_append_left _ (List.mem_cons_of_mem _ hu)))
    (hs.AB_not_mem (List.mem_append_right _ hu))

/-- **Components outside both sides** (page 17): a path of `G₁` between two vertices of `P` whose inner
vertices are off `P` and not reached from `A` in `G - P` joins consecutive vertices of `P`:
"if that was not the case, then $D$ would induce an $x$-$y$ path $Q$ between non-consecutive
vertices of $P$ ... The pair $(PxQyP,RS)$ is a crossing of $C$ in $G$, a contradiction." -/
theorem consecutive_of_outside (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂)
    (hsides : OnBothSides G C A B P) (hnc : ¬ IsCrossed G C) {u v : V} (Q : G₁.Walk u v)
    (hQ : Q.IsPath) (hu : u ∈ P.support) (hv : v ∈ P.support) (huv : u ≠ v)
    (hin : ∀ x ∈ Q.support, x ≠ u → x ≠ v →
      x ∉ P.support ∧ ¬ ∃ c ∈ A, (restrict G {w | w ∉ P.support}).Reachable c x) :
    IsListEdge P.support u v := by
  have hnd := hs.path.1.support_nodup
  have hle : G₁ ≤ G := hs.comp.1 ▸ le_sup_left
  -- an inner vertex of `Q` lies in `S₁` but off `P`, so not in `S₂`
  have hS₁ : ∀ x ∈ Q.support, x ∈ S₁ := fun x hx => by
    rcases Walk.mem_support_iff_exists_getVert.mp hx with ⟨n, rfl, -⟩
    by_cases h0 : Q.getVert n = v
    · rw [h0]; exact hs.P_sub₁ hv
    · exact hs.comp.2.1 (Q.adj_getVert_succ (by
        by_contra hn
        push Not at hn
        exact h0 (Q.getVert_of_length_le hn)))
  have hS₂ : ∀ x ∈ Q.support, x ≠ u → x ≠ v → x ∉ S₂ := fun x hx h1 h2 hx2 => by
    have : x ∈ S₁ ∩ S₂ := ⟨hS₁ x hx, hx2⟩
    rw [hs.comp.2.2.2.2.1] at this
    exact (hin x hx h1 h2).1 this
  have key : ∀ {u v : V} (Q : G₁.Walk u v), Q.IsPath → ∀ t t' (ht : t' < P.support.length)
      (_ : t + 2 ≤ t'), u = P.support[t]'(by omega) → v = P.support[t'] →
      (∀ x ∈ Q.support, x ≠ u → x ≠ v → x ∉ P.support ∧ x ∉ S₂ ∧
        ¬ ∃ c ∈ A, (restrict G {w | w ∉ P.support}).Reachable c x) → False := by
    intro u v Q hQ t t' ht htt hu hv hin
    subst hu hv
    obtain ⟨cA, hcA, cB, hcB, Y, hY, hYh, hYl, hYC, hYP, hYr⟩ :=
      hs.side_list hsides (i := t) (by omega)
    have hne : ∀ {i} (hi : i < P.support.length), i ≠ t + 1 → P.support[i] ∉ Y := fun hi hit hY' =>
      hit (hnd.getElem_inj_iff.mp (hYP _ hY' (List.getElem_mem hi))).symm.symm
    refine hnc (hs.cross_of_bypass (H := G) P.isChain_adj_support htt ht
      (X := (Q.mapLe hle).support) (Walk.isChain_adj_support _)
      ((Walk.isPath_mapLe _).mpr hQ).support_nodup (Walk.support_head? _) (Walk.support_getLast? _)
      (fun w hw hwP => ?_) (fun w hw hwC => ?_) hcA hcB hY hYh hYl hYC hYP fun w hw hwY => ?_)
    · rw [Walk.support_mapLe_eq_support] at hw
      by_contra hne'
      push Not at hne'
      exact (hin w hw hne'.1 hne'.2).1 hwP
    · rw [Walk.support_mapLe_eq_support] at hw
      by_contra hwP
      have h1 : w ≠ P.support[t]'(by omega) := fun e => hwP (e ▸ List.getElem_mem _)
      have h2 : w ≠ P.support[t'] := fun e => hwP (e ▸ List.getElem_mem _)
      obtain ⟨-, hw2, hwA⟩ := hin w hw h1 h2
      rcases List.mem_cons.mp (List.mem_append.mp (List.mem_cons.mp
        (hs.mem_C.mp hwC) |>.resolve_left fun e => hwP (e ▸ P.start_mem_support)) |>.resolve_left
          fun h' => hwA ⟨w, h', Reachable.refl _⟩) with e | h'
      · exact hwP (e ▸ P.end_mem_support)
      · exact hw2 (hs.sub₂ w (List.mem_append_left _ (List.mem_cons_of_mem _ h')))
    · rw [Walk.support_mapLe_eq_support] at hw
      by_cases h1 : w = P.support[t]'(by omega)
      · exact hne _ (by omega) (h1 ▸ hwY)
      by_cases h2 : w = P.support[t']
      · exact hne _ (by omega) (h2 ▸ hwY)
      obtain ⟨hwP, hw2, hwA⟩ := hin w hw h1 h2
      rcases hYr w hwY (fun e => hwP (e ▸ List.getElem_mem _)) with h' | ⟨c, hc, hr⟩
      · exact hwA h'
      · exact hw2 (hs.reachB_sub hc hr)
  have hin' : ∀ x ∈ Q.support, x ≠ u → x ≠ v → x ∉ P.support ∧ x ∉ S₂ ∧
      ¬ ∃ c ∈ A, (restrict G {w | w ∉ P.support}).Reachable c x := fun x hx h1 h2 =>
    ⟨(hin x hx h1 h2).1, hS₂ x hx h1 h2, (hin x hx h1 h2).2⟩
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hu
  obtain ⟨t', ht', rfl⟩ := List.getElem_of_mem hv
  have hne : t ≠ t' := fun e => by subst e; exact huv rfl
  rcases (show t' = t + 1 ∨ t = t' + 1 ∨ t + 2 ≤ t' ∨ t' + 2 ≤ t by omega)
    with rfl | rfl | h' | h'
  · exact isListEdge_getElem _ t ht'
  · exact (isListEdge_getElem _ t' ht).symm
  · exact (key Q hQ t t' ht' h' rfl rfl hin').elim
  · refine (key Q.reverse hQ.reverse t' t ht h' rfl rfl fun x hx h1 h2 => ?_).elim
    rw [Walk.support_reverse, List.mem_reverse] at hx
    exact hin' x hx h2 h1

end SplitSetting

end GraphMinor.HP25
