module

public import GraphMinor.Crossing.Statements
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card

/-!
# Clean vertex degrees and positive trials (Section 10.2 of the note)

This file proves the two claims of Section 10.2 of `docs/crossing/crossing_extractor.tex`:
* `sec102Degree_proved` (`Sec102DegreeStatement`): in a clean instance `(K, D)`, every off-cycle
  vertex in `S` has degree at least four.
* `sec102_proved` (`Sec102Statement`): among any five vertices of `S` in a clean, crossed instance,
  at least one vertex `u` has a trial edge `uv` whose contraction preserves the existence of a
  crossing.
-/

public section

namespace GraphMinor.Crossing

open SimpleGraph Set

universe u

variable {V : Type u}

/-! ### Section 10.2: Off-cycle vertices have degree at least four -/

/-- **Off-cycle vertices of a clean instance have degree at least four** (Section 10.2):
"cleanliness implies that every vertex off the cycle has degree at least four." -/
theorem sec102Degree_proved : Sec102DegreeStatement := by
  intro V K S D hSfin hK _ hclean v hvS hvD
  classical
  have hNsub : K.neighborSet v ⊆ S := fun w hw => hK hw.symm
  have hNfin : (K.neighborSet v).Finite := hSfin.subset hNsub
  by_contra hlt
  rw [not_le] at hlt
  let N : Finset V := hNfin.toFinset
  let X : Finset (Option V) := N.image some
  have hXsub : (X : Set (Option V)) ⊆ apexVerts S \ {none} := by
    intro x hx
    simp only [X, Finset.coe_image, mem_image] at hx
    obtain ⟨w, hwN, rfl⟩ := hx
    have hwS : w ∈ S := hNsub (hNfin.mem_toFinset.mp hwN)
    exact ⟨Or.inr ⟨w, hwS, rfl⟩, by simp⟩
  have hXcard : X.card < 4 := by
    have h1 : X.card ≤ N.card := Finset.card_image_le
    have h2 : N.card = (K.neighborSet v).ncard := (Set.ncard_eq_toFinset_card _ hNfin).symm
    omega
  have hv_mem : some v ∈ apexVerts S \ (X : Set (Option V)) := by
    refine ⟨Or.inr ⟨v, hvS, rfl⟩, ?_⟩
    simp only [X, Finset.coe_image, mem_image, Option.some.injEq, exists_eq_right]
    exact fun hvN => K.loopless.irrefl v (hNfin.mem_toFinset.mp hvN)
  have hnone_mem : (none : Option V) ∈ apexVerts S \ (X : Set (Option V)) := by
    refine ⟨Or.inl rfl, ?_⟩
    simp [X]
  obtain ⟨_, hconn⟩ := hclean X hXsub hXcard
  obtain ⟨p, hp⟩ := hconn (some v) hv_mem none hnone_mem
  cases p with
  | @cons _ w _ hadj p' =>
    have hw_mem : w ∈ apexVerts S \ (X : Set (Option V)) :=
      hp w (List.mem_cons_of_mem _ (Walk.start_mem_support _))
    cases w with
    | none =>
      exact hvD hadj
    | some y =>
      have hyN : y ∈ N := hNfin.mem_toFinset.mpr hadj
      have hwyX : some y ∈ (X : Set (Option V)) :=
        Finset.mem_coe.mpr (Finset.mem_image_of_mem some hyN)
      exact hw_mem.2 hwyX

/-! ### Section 10.2: At least one trial is positive -/

private lemma exists_liftWalkNotMem {K : SimpleGraph V} {u : V} (v : V) {x y : V}
    (P : K.Walk x y) (hu : u ∉ P.support) :
    ∃ P' : (contractGraph K u v).Walk x y, P'.support = P.support := by
  induction P with
  | nil => exact ⟨Walk.nil, rfl⟩
  | @cons a b c hab P ih =>
    have hau : a ≠ u := fun h => hu (h ▸ Walk.start_mem_support _)
    have hbu : b ≠ u := fun h => hu (h ▸ List.mem_cons_of_mem _ (Walk.start_mem_support P))
    have hu' : u ∉ P.support := fun h => hu (List.mem_cons_of_mem _ h)
    obtain ⟨P', hP'⟩ := ih hu'
    have hab' : (contractGraph K u v).Adj a b := ⟨hab.ne, hau, hbu, Or.inl hab⟩
    refine ⟨Walk.cons hab' P', ?_⟩
    rw [Walk.support_cons, Walk.support_cons, hP']

private lemma exists_liftTPathNotMem {K : SimpleGraph V} {D D' : List V} {u : V} (v : V)
    {x y : V} (P : K.Walk x y) (hu : u ∉ P.support) (hP : HP25.IsTPath K D P)
    (hxD' : x ∈ D') (hyD' : y ∈ D') (hsub : ∀ z ∈ D', z ∈ D) :
    ∃ P' : (contractGraph K u v).Walk x y,
      HP25.IsTPath (contractGraph K u v) D' P' ∧ P'.support = P.support := by
  obtain ⟨P', hsupp⟩ := exists_liftWalkNotMem v P hu
  have hpath : P'.IsPath := Walk.IsPath.mk' (by rw [hsupp]; exact hP.1.support_nodup)
  refine ⟨P', ⟨hpath, hxD', hyD', ?_⟩, hsupp⟩
  intro z hz hzx hzy
  rw [hsupp] at hz
  have hzD : z ∉ D := (hP.2.2.2 z hz hzx hzy).1
  exact ⟨fun h => hzD (hsub z h), fun h => hzD (hsub z h)⟩

private lemma exists_contract_walk_of_mem_support {K : SimpleGraph V} {a b u : V}
    (Q : K.Walk a b) (hQ : Q.IsPath) (hu : u ∈ Q.support) (hua : u ≠ a) (hub : u ≠ b) :
    ∃ v, K.Adj u v ∧ ∃ Q' : (contractGraph K u v).Walk a b,
      Q'.IsPath ∧ ∀ y ∈ Q'.support, y ∈ Q.support := by
  induction Q with
  | nil =>
    simp only [Walk.support_nil, List.mem_singleton] at hu
    exact absurd hu hua
  | @cons a c b hac P ih =>
    rw [Walk.cons_isPath_iff] at hQ
    obtain ⟨hP, haP⟩ := hQ
    have huP : u ∈ P.support := by
      simp only [Walk.support_cons, List.mem_cons] at hu
      rcases hu with rfl | h
      · exact absurd rfl hua
      · exact h
    by_cases hcu : c = u
    · subst c
      cases P with
      | nil => exact absurd rfl hub
      | @cons _ w b huw P₂ =>
        rw [Walk.cons_isPath_iff] at hP
        obtain ⟨hP₂, huP₂⟩ := hP
        have haw : a ≠ w := by
          rintro rfl
          exact haP (List.mem_cons_of_mem _ (Walk.start_mem_support P₂))
        have hwu : w ≠ u := by
          rintro rfl
          exact huP₂ (Walk.start_mem_support P₂)
        have haw_c : (contractGraph K u a).Adj a w :=
          ⟨haw, Ne.symm hua, hwu, Or.inr (Or.inl ⟨rfl, huw⟩)⟩
        obtain ⟨P₂', hsupp₂⟩ := exists_liftWalkNotMem a P₂ huP₂
        have hP₂'_path : P₂'.IsPath := Walk.IsPath.mk' (by rw [hsupp₂]; exact hP₂.support_nodup)
        have haP₂' : a ∉ P₂'.support := by
          rw [hsupp₂]
          exact fun h => haP (List.mem_cons_of_mem _ h)
        refine ⟨a, hac.symm, Walk.cons haw_c P₂', ?_, ?_⟩
        · exact (Walk.cons_isPath_iff _ _).mpr ⟨hP₂'_path, haP₂'⟩
        · intro y hy
          simp only [Walk.support_cons, List.mem_cons] at hy ⊢
          rw [hsupp₂] at hy
          rcases hy with rfl | hy
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hy)
    · obtain ⟨v, huv, P', hP', hsub⟩ := ih hP huP (Ne.symm hcu) hub
      have hac_c : (contractGraph K u v).Adj a c := ⟨hac.ne, Ne.symm hua, hcu, Or.inl hac⟩
      have haP' : a ∉ P'.support := fun h => haP (hsub a h)
      refine ⟨v, huv, Walk.cons hac_c P', (Walk.cons_isPath_iff _ _).mpr ⟨hP', haP'⟩, ?_⟩
      intro y hy
      simp only [Walk.support_cons, List.mem_cons] at hy ⊢
      rcases hy with rfl | hy
      · exact Or.inl rfl
      · exact Or.inr (hsub y hy)

private def embIdx (k idx : ℕ) : ℕ :=
  if idx < k then idx else idx + 1

variable [DecidableEq V]

private lemma getElem?_embIdx_erase {D : List V} {u : V} (hu : u ∈ D) (idx : ℕ) :
    D[embIdx (D.idxOf u) idx]? = (D.erase u)[idx]? := by
  induction D generalizing idx with
  | nil => simp at hu
  | cons x rest ih =>
    by_cases hxu : x = u
    · subst x
      simp [embIdx]
    · have hu_rest : u ∈ rest := by
        rcases List.mem_cons.mp hu with rfl | h
        · exact absurd rfl hxu
        · exact h
      rw [List.idxOf_cons_ne _ hxu, List.erase_cons_tail (by simpa [beq_iff_eq] using hxu)]
      cases idx with
      | zero => simp [embIdx]
      | succ m =>
        have hemb : embIdx (rest.idxOf u + 1) (m + 1) = embIdx (rest.idxOf u) m + 1 := by
          unfold embIdx; split_ifs <;> omega
        rw [hemb, List.getElem?_cons_succ, List.getElem?_cons_succ, ih hu_rest m]

private lemma idxOf_eq_of_getElem?_eq_some {D : List V} (hnodup : D.Nodup) {i : ℕ} {x : V}
    (h : D[i]? = some x) : D.idxOf x = i := by
  induction D generalizing i with
  | nil => simp at h
  | cons a rest ih =>
    rw [List.nodup_cons] at hnodup
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst a
      exact List.idxOf_cons_self
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      have hax : a ≠ x := fun hax => hnodup.1 (hax ▸ List.mem_of_getElem? h)
      rw [List.idxOf_cons_ne _ hax, ih hnodup.2 h]

private def unembIdx (ku idx : ℕ) : ℕ :=
  if idx < ku then idx else idx - 1

private lemma unembIdx_strictMono {ku i j : ℕ} (hi : i ≠ ku) (hj : j ≠ ku) (hij : i < j) :
    unembIdx ku i < unembIdx ku j := by
  unfold unembIdx; split_ifs <;> omega

private lemma embIdx_unembIdx {ku idx : ℕ} (h : idx ≠ ku) :
    embIdx ku (unembIdx ku idx) = idx := by
  unfold embIdx unembIdx; split_ifs <;> omega

private lemma getElem?_erase_unembIdx {D : List V} {u x : V} (huD : u ∈ D) {idx : ℕ}
    (hx : D[idx]? = some x) (hxu : x ≠ u) :
    (D.erase u)[unembIdx (D.idxOf u) idx]? = some x := by
  have hidx_ne : idx ≠ D.idxOf u := by
    rintro rfl
    exact hxu (Option.some.inj (hx.symm.trans (List.getElem?_idxOf huD)))
  rw [← getElem?_embIdx_erase huD, embIdx_unembIdx hidx_ne, hx]

/-- **At least one trial is positive** (Section 10.2): "Fix any crossing of $D$. It has exactly
four ends. So at least one of the five chosen vertices, say $u$, is not one of these ends." -/
theorem sec102_proved : Sec102Statement := by
  intro V _ K S D U hSfin hK hD hclean hcross hUcard hUS
  obtain ⟨a, b, c, d, Q, R, ⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩, hQ, hR, hdisj⟩ := hcross
  let Ends : Finset V := {a, b, c, d}
  have hEnds_card : Ends.card ≤ 4 := by
    dsimp only [Ends]
    have h1 := Finset.card_insert_le a ({b, c, d} : Finset V)
    have h2 := Finset.card_insert_le b ({c, d} : Finset V)
    have h3 := Finset.card_insert_le c ({d} : Finset V)
    have h4 : ({d} : Finset V).card = 1 := Finset.card_singleton d
    omega
  have hex_u : ∃ u ∈ U, u ∉ Ends :=
    Finset.exists_mem_notMem_of_card_lt_card (by omega)
  obtain ⟨u, huU, huEnds⟩ := hex_u
  simp only [Ends, Finset.mem_insert, Finset.mem_singleton, not_or] at huEnds
  obtain ⟨hua, hub, huc, hud⟩ := huEnds
  have huS : u ∈ S := hUS huU
  by_cases huD : u ∈ D
  · -- Case 3: `u ∈ D`
    have huQ : u ∉ Q.support := fun h => (hQ.2.2.2 u h hua hub).1 huD
    have huR : u ∉ R.support := fun h => (hR.2.2.2 u h huc hud).1 huD
    have hDlen_ne : D.length ≠ 4 := by
      have haD : a ∈ D := List.mem_of_getElem? hi
      have hcD : c ∈ D := List.mem_of_getElem? hr
      have hbD : b ∈ D := List.mem_of_getElem? hj
      have hdD : d ∈ D := List.mem_of_getElem? hs
      have hac : a ≠ c := by
        intro h; subst h
        have := idxOf_eq_of_getElem?_eq_some hD.2.1 hi
        have := idxOf_eq_of_getElem?_eq_some hD.2.1 hr
        omega
      have hab : a ≠ b := by
        intro h; subst h
        have := idxOf_eq_of_getElem?_eq_some hD.2.1 hi
        have := idxOf_eq_of_getElem?_eq_some hD.2.1 hj
        omega
      have had : a ≠ d := by
        intro h; subst h
        have := idxOf_eq_of_getElem?_eq_some hD.2.1 hi
        have := idxOf_eq_of_getElem?_eq_some hD.2.1 hs
        omega
      have hcb : c ≠ b := by
        intro h; subst h
        have := idxOf_eq_of_getElem?_eq_some hD.2.1 hr
        have := idxOf_eq_of_getElem?_eq_some hD.2.1 hj
        omega
      have hcd : c ≠ d := by
        intro h; subst h
        have := idxOf_eq_of_getElem?_eq_some hD.2.1 hr
        have := idxOf_eq_of_getElem?_eq_some hD.2.1 hs
        omega
      have hbd : b ≠ d := by
        intro h; subst h
        have := idxOf_eq_of_getElem?_eq_some hD.2.1 hj
        have := idxOf_eq_of_getElem?_eq_some hD.2.1 hs
        omega
      let F5 : Finset V := {u, a, c, b, d}
      have hF5_sub : F5 ⊆ D.toFinset := by
        intro x hx
        simp only [F5, Finset.mem_insert, Finset.mem_singleton] at hx
        rw [List.mem_toFinset]
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
      have hF5_card : F5.card = 5 := by
        dsimp only [F5]
        rw [Finset.card_insert_of_notMem (by simp [hua, hub, huc, hud]),
          Finset.card_insert_of_notMem (by simp [hac, hab, had]),
          Finset.card_insert_of_notMem (by simp [hcb, hcd]),
          Finset.card_insert_of_notMem (by simp [hbd]),
          Finset.card_singleton]
      have hle : 5 ≤ D.length := by
        rw [← hF5_card, ← List.toFinset_card_of_nodup hD.2.1]
        exact Finset.card_le_card hF5_sub
      omega
    have hex_v : ∃ v, K.Adj u v ∧ IsCycleEdge D u v := by
      have hidx : D.idxOf u < (D.rotate 1).length := by
        rw [List.length_rotate]
        exact List.idxOf_lt_length_of_mem huD
      let v := (D.rotate 1)[D.idxOf u]'hidx
      have hv : (D.rotate 1)[D.idxOf u]? = some v := List.getElem?_eq_getElem hidx
      have hzip : (D.zip (D.rotate 1))[D.idxOf u]? = some (u, v) := by
        rw [List.getElem?_zip_eq_some]
        exact ⟨List.getElem?_idxOf huD, hv⟩
      have hp_mem : (u, v) ∈ D.zip (D.rotate 1) := List.mem_of_getElem? hzip
      exact ⟨v, hD.2.2 (u, v) hp_mem, ⟨(u, v), hp_mem, Or.inl rfl⟩⟩
    obtain ⟨v, huv, hce⟩ := hex_v
    refine ⟨u, huU, v, ⟨huv, Or.inr hce⟩, fun _ => hDlen_ne, ?_⟩
    unfold contractCycle
    simp only [huD, ↓reduceIte]
    have ha_er : a ∈ D.erase u := (List.mem_erase_of_ne (Ne.symm hua)).mpr hQ.2.1
    have hb_er : b ∈ D.erase u := (List.mem_erase_of_ne (Ne.symm hub)).mpr hQ.2.2.1
    have hc_er : c ∈ D.erase u := (List.mem_erase_of_ne (Ne.symm huc)).mpr hR.2.1
    have hd_er : d ∈ D.erase u := (List.mem_erase_of_ne (Ne.symm hud)).mpr hR.2.2.1
    obtain ⟨Q', hQ', hQ'supp⟩ :=
      exists_liftTPathNotMem v Q huQ hQ ha_er hb_er (fun _ hz => List.mem_of_mem_erase hz)
    obtain ⟨R', hR', hR'supp⟩ :=
      exists_liftTPathNotMem v R huR hR hc_er hd_er (fun _ hz => List.mem_of_mem_erase hz)
    have hdisj' : Q'.support.Disjoint R'.support := by
      rw [hQ'supp, hR'supp]
      exact hdisj
    let ku := D.idxOf u
    have hi_ne : i ≠ ku := by
      rintro rfl
      exact hua (Option.some.inj ((List.getElem?_idxOf huD).symm.trans hi))
    have hr_ne : r ≠ ku := by
      rintro rfl
      exact huc (Option.some.inj ((List.getElem?_idxOf huD).symm.trans hr))
    have hj_ne : j ≠ ku := by
      rintro rfl
      exact hub (Option.some.inj ((List.getElem?_idxOf huD).symm.trans hj))
    have hs_ne : s ≠ ku := by
      rintro rfl
      exact hud (Option.some.inj ((List.getElem?_idxOf huD).symm.trans hs))
    refine ⟨a, b, c, d, Q', R', ⟨unembIdx ku i, unembIdx ku r, unembIdx ku j, unembIdx ku s,
      unembIdx_strictMono hi_ne hr_ne hir, unembIdx_strictMono hr_ne hj_ne hrj,
      unembIdx_strictMono hj_ne hs_ne hjs,
      getElem?_erase_unembIdx huD hi (Ne.symm hua), getElem?_erase_unembIdx huD hr (Ne.symm huc),
      getElem?_erase_unembIdx huD hj (Ne.symm hub), getElem?_erase_unembIdx huD hs (Ne.symm hud)⟩,
      hQ', hR', hdisj'⟩
  · -- `u ∉ D`
    by_cases huQ : u ∈ Q.support
    · -- Case 2a: `u ∈ Q.support`
      have huR : u ∉ R.support := fun h => hdisj huQ h
      obtain ⟨v, huv, Q', hQ'_path, hQ'_sub⟩ :=
        exists_contract_walk_of_mem_support Q hQ.1 huQ hua hub
      refine ⟨u, huU, v, ⟨huv, Or.inl huD⟩, fun h => absurd h huD, ?_⟩
      unfold contractCycle
      simp only [huD, ↓reduceIte]
      obtain ⟨R', hR', hR'supp⟩ :=
        exists_liftTPathNotMem v R huR hR hR.2.1 hR.2.2.1 (fun _ hz => hz)
      have hQ' : HP25.IsTPath (contractGraph K u v) D Q' :=
        ⟨hQ'_path, hQ.2.1, hQ.2.2.1, fun z hz => hQ.2.2.2 z (hQ'_sub z hz)⟩
      have hdisj' : Q'.support.Disjoint R'.support := by
        rw [hR'supp]
        exact fun y hyQ' hyR => hdisj (hQ'_sub y hyQ') hyR
      exact ⟨a, b, c, d, Q', R', ⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩, hQ', hR', hdisj'⟩
    · by_cases huR : u ∈ R.support
      · -- Case 2b: `u ∈ R.support`
        obtain ⟨v, huv, R', hR'_path, hR'_sub⟩ :=
          exists_contract_walk_of_mem_support R hR.1 huR huc hud
        refine ⟨u, huU, v, ⟨huv, Or.inl huD⟩, fun h => absurd h huD, ?_⟩
        unfold contractCycle
        simp only [huD, ↓reduceIte]
        obtain ⟨Q', hQ', hQ'supp⟩ :=
          exists_liftTPathNotMem v Q huQ hQ hQ.2.1 hQ.2.2.1 (fun _ hz => hz)
        have hR' : HP25.IsTPath (contractGraph K u v) D R' :=
          ⟨hR'_path, hR.2.1, hR.2.2.1, fun z hz => hR.2.2.2 z (hR'_sub z hz)⟩
        have hdisj' : Q'.support.Disjoint R'.support := by
          rw [hQ'supp]
          exact fun y hyQ hyR' => hdisj hyQ (hR'_sub y hyR')
        exact ⟨a, b, c, d, Q', R', ⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩, hQ', hR', hdisj'⟩
      · -- Case 1: `u ∉ D`, `u ∉ Q.support`, `u ∉ R.support`
        have hdeg : 4 ≤ (K.neighborSet u).ncard :=
          sec102Degree_proved K S D hSfin hK hD hclean u huS huD
        have hne : (K.neighborSet u).Nonempty :=
          Set.nonempty_of_ncard_ne_zero (by omega)
        obtain ⟨v, huv⟩ := hne
        refine ⟨u, huU, v, ⟨huv, Or.inl huD⟩, fun h => absurd h huD, ?_⟩
        unfold contractCycle
        simp only [huD, ↓reduceIte]
        obtain ⟨Q', hQ', hQ'supp⟩ :=
          exists_liftTPathNotMem v Q huQ hQ hQ.2.1 hQ.2.2.1 (fun _ hz => hz)
        obtain ⟨R', hR', hR'supp⟩ :=
          exists_liftTPathNotMem v R huR hR hR.2.1 hR.2.2.1 (fun _ hz => hz)
        have hdisj' : Q'.support.Disjoint R'.support := by
          rw [hQ'supp, hR'supp]
          exact hdisj
        exact ⟨a, b, c, d, Q', R', ⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩, hQ', hR', hdisj'⟩

end GraphMinor.Crossing
