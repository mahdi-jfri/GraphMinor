module

public import GraphMinor.Crossing.Statements
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card

/-!
# Four BFS forests preserve all cuts of order at most three (Section 7.1 of the note)

This file proves the two claims of Section 7.1 of `docs/crossing/crossing_extractor.tex`:
* `lemma5_proved` (`Lemma5Statement`): Lemma 5 (strong certificate), showing that for `k`
  successive scan-first forests and every set `X` with `|X| < k`, the union of the forests minus
  `X` has the same connected components on `T \ X` as `G - X`.
* `sec71Count_proved` (`Sec71CountStatement`): on `n + 1` vertices, each scan-first forest has at
  most `n` edges, so the union of `k` forests has at most `k * n` edges.
-/

public section

namespace GraphMinor.Crossing

open SimpleGraph Set

universe u

variable {W : Type u}

/-! ### Basic properties of `ReachIn` and `scanForest` -/

private lemma reachIn_refl {G : SimpleGraph W} {T : Set W} {a : W} (ha : a ∈ T) :
    ReachIn G T a a :=
  ⟨Walk.nil, fun y hy => by simp only [Walk.support_nil, List.mem_singleton] at hy; exact hy ▸ ha⟩

private lemma reachIn_symm {G : SimpleGraph W} {T : Set W} {a b : W} (h : ReachIn G T a b) :
    ReachIn G T b a := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.reverse, fun y hy => hp y ?_⟩
  rw [Walk.support_reverse, List.mem_reverse] at hy
  exact hy

private lemma reachIn_trans {G : SimpleGraph W} {T : Set W} {a b c : W}
    (hab : ReachIn G T a b) (hbc : ReachIn G T b c) : ReachIn G T a c := by
  obtain ⟨p, hp⟩ := hab
  obtain ⟨q, hq⟩ := hbc
  refine ⟨p.append q, fun y hy => ?_⟩
  rw [Walk.support_append, List.mem_append] at hy
  rcases hy with hy | hy
  · exact hp y hy
  · exact hq y (List.tail_subset _ hy)

private lemma reachIn_of_adj {G : SimpleGraph W} {T : Set W} {a b : W}
    (ha : a ∈ T) (hb : b ∈ T) (hab : G.Adj a b) : ReachIn G T a b := by
  refine ⟨Walk.cons hab Walk.nil, fun y hy => ?_⟩
  simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl <;> assumption

private lemma reachIn_mono_graph {G G' : SimpleGraph W} {T : Set W} {a b : W}
    (hle : G ≤ G') (h : ReachIn G T a b) : ReachIn G' T a b := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.map (Hom.ofLE hle), fun y hy => hp y (by simpa using hy)⟩

variable [DecidableEq W]

private lemma scanForest_le (G : SimpleGraph W) (σ : List W) : scanForest G σ ≤ G := by
  intro a b h
  rcases h with h | h
  · exact h.1
  · exact h.1.symm

private lemma forestUnion_le {G : SimpleGraph W} {T : Set W} {Fs : List (SimpleGraph W)}
    (hFs : IsScanFirstSequence G T Fs) : forestUnion Fs ≤ G := by
  induction Fs generalizing G with
  | nil => exact bot_le
  | cons F Fs ih =>
    obtain ⟨⟨σ, _, rfl⟩, hFs'⟩ := hFs
    exact sup_le (scanForest_le G σ) (le_trans (ih hFs') sdiff_le)

/-! ### Scan parents, scan ancestors and scan roots -/

private lemma idxOf_eq_iff_of_mem {σ : List W} {a b : W} (ha : a ∈ σ) (hb : b ∈ σ) :
    σ.idxOf a = σ.idxOf b ↔ a = b := by
  constructor
  · intro h
    have ha' : σ[σ.idxOf a]? = some a := List.getElem?_idxOf ha
    have hb' : σ[σ.idxOf b]? = some b := List.getElem?_idxOf hb
    exact Option.some.inj (ha'.symm.trans (h ▸ hb'))
  · rintro rfl; rfl

private lemma idxOf_le_of_getElem?_eq_some {σ : List W} {i : ℕ} {a : W} (h : σ[i]? = some a) :
    σ.idxOf a ≤ i := by
  induction σ generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [List.idxOf_cons_self]
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      rw [List.idxOf_cons]
      split_ifs
      · exact Nat.zero_le _
      · exact Nat.succ_le_succ (ih h)

private lemma IsScanParent.unique {G : SimpleGraph W} {T : Set W} {σ : List W}
    (hG : HP25.IsSupportedOn G T) (hσ : IsScanOrder G T σ) {c p₁ p₂ : W}
    (h₁ : IsScanParent G σ c p₁) (h₂ : IsScanParent G σ c p₂) : p₁ = p₂ := by
  have hp₁ : p₁ ∈ σ := (hσ.2.1 p₁).mpr (hG h₁.1.symm)
  have hp₂ : p₂ ∈ σ := (hσ.2.1 p₂).mpr (hG h₂.1.symm)
  exact (idxOf_eq_iff_of_mem hp₁ hp₂).mp (le_antisymm (h₁.2.2 p₂ h₂.1) (h₂.2.2 p₁ h₁.1))

private lemma exists_isScanParent_of_adj_lt (G : SimpleGraph W) (σ : List W) {c y : W}
    (hcy : G.Adj c y) (hlt : σ.idxOf y < σ.idxOf c) : ∃ p, IsScanParent G σ c p := by
  classical
  have hex : ∃ i, ∃ z, σ.idxOf z = i ∧ G.Adj c z := ⟨σ.idxOf y, y, rfl, hcy⟩
  obtain ⟨p, hp_idx, hcp⟩ := Nat.find_spec hex
  refine ⟨p, hcp, ?_, ?_⟩
  · rw [hp_idx]
    exact lt_of_le_of_lt (Nat.find_min' hex ⟨y, rfl, hcy⟩) hlt
  · intro z hcz
    rw [hp_idx]
    exact Nat.find_min' hex ⟨z, rfl, hcz⟩

private abbrev ScanAncestor (G : SimpleGraph W) (σ : List W) : W → W → Prop :=
  Relation.ReflTransGen (fun p c => IsScanParent G σ c p)

private def IsScanRoot (G : SimpleGraph W) (T : Set W) (σ : List W) (r : W) : Prop :=
  r ∈ T ∧ ¬ ∃ p, IsScanParent G σ r p

private lemma scanAncestor_mem_and_reachIn {G : SimpleGraph W} {T : Set W} {σ : List W}
    (hG : HP25.IsSupportedOn G T) {r x : W} (hr : r ∈ T) (h : ScanAncestor G σ r x) :
    x ∈ T ∧ ReachIn (scanForest G σ) T r x ∧ σ.idxOf r ≤ σ.idxOf x := by
  induction h with
  | refl => exact ⟨hr, reachIn_refl hr, le_rfl⟩
  | @tail p c _ hpc ih =>
    have hcT : c ∈ T := hG hpc.1
    exact ⟨hcT, reachIn_trans ih.2.1 (reachIn_of_adj ih.1 hcT (Or.inr hpc)),
      le_trans ih.2.2 (le_of_lt hpc.2.1)⟩

private lemma exists_scanRoot (G : SimpleGraph W) (T : Set W) (σ : List W)
    (hG : HP25.IsSupportedOn G T) {x : W} (hx : x ∈ T) :
    ∃ r, IsScanRoot G T σ r ∧ ScanAncestor G σ r x := by
  suffices ∀ k x, x ∈ T → σ.idxOf x = k → ∃ r, IsScanRoot G T σ r ∧ ScanAncestor G σ r x from
    this (σ.idxOf x) x hx rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hx hkx
    by_cases hp : ∃ p, IsScanParent G σ x p
    · obtain ⟨p, hxp⟩ := hp
      have hpT : p ∈ T := hG hxp.1.symm
      have hlt : σ.idxOf p < k := hkx ▸ hxp.2.1
      obtain ⟨r, hr, hrp⟩ := ih (σ.idxOf p) hlt p hpT rfl
      exact ⟨r, hr, hrp.tail hxp⟩
    · exact ⟨x, ⟨hx, hp⟩, Relation.ReflTransGen.refl⟩

private lemma scanRoot_not_lt_of_reachIn {G : SimpleGraph W} {T : Set W} {σ : List W}
    (hσ : IsScanOrder G T σ) {r₁ r₂ : W} (hr₁ : r₁ ∈ T) (hr₂ : IsScanRoot G T σ r₂)
    (hreach : ReachIn G T r₁ r₂) : ¬ σ.idxOf r₁ < σ.idxOf r₂ := by
  intro hlt
  have h1 : r₁ ∈ σ := (hσ.2.1 r₁).mpr hr₁
  have h2 : r₂ ∈ σ := (hσ.2.1 r₂).mpr hr₂.1
  have hg1 : σ[σ.idxOf r₁]? = some r₁ := List.getElem?_idxOf h1
  have hg2 : σ[σ.idxOf r₂]? = some r₂ := List.getElem?_idxOf h2
  obtain ⟨i', hi', c, hgc, hcr₂⟩ := hσ.2.2 (σ.idxOf r₁) (σ.idxOf r₂) r₁ r₂ hlt hg1 hg2 hreach
  have hclt : σ.idxOf c < σ.idxOf r₂ := lt_of_le_of_lt (idxOf_le_of_getElem?_eq_some hgc) hi'
  exact hr₂.2 (exists_isScanParent_of_adj_lt G σ hcr₂.symm hclt)

private lemma scanRoot_unique_of_reachIn {G : SimpleGraph W} {T : Set W} {σ : List W}
    (hσ : IsScanOrder G T σ) {r₁ r₂ : W} (hr₁ : IsScanRoot G T σ r₁) (hr₂ : IsScanRoot G T σ r₂)
    (hreach : ReachIn G T r₁ r₂) : r₁ = r₂ := by
  have h1 : r₁ ∈ σ := (hσ.2.1 r₁).mpr hr₁.1
  have h2 : r₂ ∈ σ := (hσ.2.1 r₂).mpr hr₂.1
  apply (idxOf_eq_iff_of_mem h1 h2).mp
  exact le_antisymm
    (not_lt.mp (scanRoot_not_lt_of_reachIn hσ hr₂.1 hr₁ (reachIn_symm hreach)))
    (not_lt.mp (scanRoot_not_lt_of_reachIn hσ hr₁.1 hr₂ hreach))

private lemma scanAncestor_of_scanRoot_and_adj {G : SimpleGraph W} {T : Set W} {σ : List W}
    (hG : HP25.IsSupportedOn G T) (hσ : IsScanOrder G T σ) {r x y : W}
    (hr : IsScanRoot G T σ r) (hrx : ScanAncestor G σ r x) (hxy : G.Adj x y) :
    ScanAncestor G σ r y := by
  have hx := scanAncestor_mem_and_reachIn hG hr.1 hrx
  have hyT : y ∈ T := hG hxy.symm
  obtain ⟨ry, hry, hry_y⟩ := exists_scanRoot G T σ hG hyT
  have hy := scanAncestor_mem_and_reachIn hG hry.1 hry_y
  have hreach_r_ry : ReachIn G T r ry :=
    reachIn_trans (reachIn_mono_graph (scanForest_le G σ) hx.2.1)
      (reachIn_trans (reachIn_of_adj hx.1 hyT hxy)
        (reachIn_symm (reachIn_mono_graph (scanForest_le G σ) hy.2.1)))
  have heq : r = ry := scanRoot_unique_of_reachIn hσ hr hry hreach_r_ry
  exact heq ▸ hry_y

/-! ### Proof of Lemma 5 -/

private lemma exists_sep_ancestor_of_scanAncestor {G : SimpleGraph W} {T A B S : Set W}
    {σ : List W} (hG : HP25.IsSupportedOn G T)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, ¬ (scanForest G σ).Adj x y)
    (hT : T ⊆ A ∪ B ∪ S) (hdAB : Disjoint A B)
    {r y : W} (hr : r ∈ A) (hy : y ∈ B) (hry : ScanAncestor G σ r y) :
    ∃ u ∈ S, ∃ p, ScanAncestor G σ r u ∧ σ.idxOf u ≤ σ.idxOf p ∧ IsScanParent G σ y p := by
  induction hry with
  | refl => exact absurd hy (Disjoint.notMem_of_mem_left hdAB hr)
  | @tail p y h_rp h_py ih =>
    have hpT : p ∈ T := hG h_py.1.symm
    have hFpy : (scanForest G σ).Adj p y := Or.inr h_py
    rcases hT hpT with (hpA | hpB) | hpS
    · exact absurd hFpy (hAB p hpA y hy)
    · obtain ⟨u, huS, p', hru, hup', hp'p⟩ := ih hpB
      exact ⟨u, huS, p, hru, le_trans hup' (le_of_lt hp'p.2.1), h_py⟩
    · exact ⟨p, hpS, p, h_rp, le_rfl, h_py⟩

private lemma isScanParent_of_le_parent {G : SimpleGraph W} {σ : List W} {y p s : W}
    (hp : IsScanParent G σ y p) (hys : G.Adj y s) (hsp : σ.idxOf s ≤ σ.idxOf p) :
    IsScanParent G σ y s :=
  ⟨hys, lt_of_le_of_lt hsp hp.2.1, fun z hyz => le_trans hsp (hp.2.2 z hyz)⟩

private lemma scanForest_selects_sep_edges {G : SimpleGraph W} {T A B S : Set W} {σ : List W}
    (hG : HP25.IsSupportedOn G T) (hσ : IsScanOrder G T σ)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, ¬ (scanForest G σ).Adj x y)
    (hT : T ⊆ A ∪ B ∪ S) (hdAB : Disjoint A B) (hdBS : Disjoint B S)
    {r s : W} (hr : IsScanRoot G T σ r) (hrAS : r ∈ A ∨ r ∈ S)
    (hrs : ScanAncestor G σ r s)
    (hmin : ∀ u ∈ S, ScanAncestor G σ r u → σ.idxOf s ≤ σ.idxOf u)
    {y : W} (hy : y ∈ B) (hsy : G.Adj s y) :
    (scanForest G σ).Adj s y := by
  have hry : ScanAncestor G σ r y := scanAncestor_of_scanRoot_and_adj hG hσ hr hrs hsy
  rcases hrAS with hrA | hrS
  · obtain ⟨u, huS, p, hru, hup, hp⟩ :=
      exists_sep_ancestor_of_scanAncestor hG hAB hT hdAB hrA hy hry
    have hsp : σ.idxOf s ≤ σ.idxOf p := le_trans (hmin u huS hru) hup
    exact Or.inr (isScanParent_of_le_parent hp hsy.symm hsp)
  · rcases Relation.ReflTransGen.cases_tail hry with rfl | ⟨p, hrp, hp⟩
    · exact absurd hrS (Disjoint.notMem_of_mem_left hdBS hy)
    · have hr_le_p : σ.idxOf r ≤ σ.idxOf p := (scanAncestor_mem_and_reachIn hG hr.1 hrp).2.2
      have hsp : σ.idxOf s ≤ σ.idxOf p :=
        le_trans (hmin r hrS Relation.ReflTransGen.refl) hr_le_p
      exact Or.inr (isScanParent_of_le_parent hp hsy.symm hsp)

private lemma not_adj_of_scanFirstSequence {G : SimpleGraph W} {T : Set W}
    {Fs : List (SimpleGraph W)} (hG : HP25.IsSupportedOn G T) (hFs : IsScanFirstSequence G T Fs)
    {A B : Set W} {X : Finset W} (hcard : X.card < Fs.length)
    (hT : T ⊆ A ∪ B ∪ (X : Set W))
    (hdAB : Disjoint A B) (hdAX : Disjoint A (X : Set W)) (hdBX : Disjoint B (X : Set W))
    {a b : W} (ha : a ∈ A) (hb : b ∈ B)
    (hU : ∀ x ∈ A, ∀ y ∈ B, ¬ (forestUnion Fs).Adj x y) :
    ¬ G.Adj a b := by
  induction Fs generalizing G A B X with
  | nil => exact absurd hcard (Nat.not_lt_zero _)
  | cons F Fs ih =>
    intro hab
    obtain ⟨⟨σ, hσ, rfl⟩, hFs'⟩ := hFs
    have hFAB : ∀ x ∈ A, ∀ y ∈ B, ¬ (scanForest G σ).Adj x y :=
      fun x hx y hy h => hU x hx y hy (Or.inl h)
    have hU' : ∀ x ∈ A, ∀ y ∈ B, ¬ (forestUnion Fs).Adj x y :=
      fun x hx y hy h => hU x hx y hy (Or.inr h)
    have hFU_le : forestUnion Fs ≤ G \ scanForest G σ := forestUnion_le hFs'
    have hG' : HP25.IsSupportedOn (G \ scanForest G σ) T := fun _ _ h => hG h.1
    have hab' : (G \ scanForest G σ).Adj a b := ⟨hab, hFAB a ha b hb⟩
    have haT : a ∈ T := hG hab
    obtain ⟨r, hr, hra⟩ := exists_scanRoot G T σ hG haT
    have hrb : ScanAncestor G σ r b := scanAncestor_of_scanRoot_and_adj hG hσ hr hra hab
    have hex_u : ∃ u ∈ (X : Set W), ScanAncestor G σ r u := by
      rcases hT hr.1 with (hrA | hrB) | hrX
      · obtain ⟨u, huX, _, hru, _, _⟩ :=
          exists_sep_ancestor_of_scanAncestor hG hFAB hT hdAB hrA hb hrb
        exact ⟨u, huX, hru⟩
      · have hBA : ∀ x ∈ B, ∀ y ∈ A, ¬ (scanForest G σ).Adj x y :=
          fun x hx y hy h => hFAB y hy x hx h.symm
        have hT' : T ⊆ B ∪ A ∪ (X : Set W) := by
          intro z hz; rcases hT hz with (h | h) | h
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        obtain ⟨u, huX, _, hru, _, _⟩ :=
          exists_sep_ancestor_of_scanAncestor hG hBA hT' hdAB.symm hrB ha hra
        exact ⟨u, huX, hru⟩
      · exact ⟨r, hrX, Relation.ReflTransGen.refl⟩
    classical
    have hex : ∃ i, ∃ s ∈ (X : Set W), ScanAncestor G σ r s ∧ σ.idxOf s = i := by
      obtain ⟨u, huX, hru⟩ := hex_u
      exact ⟨σ.idxOf u, u, huX, hru, rfl⟩
    obtain ⟨s, hsX, hrs, hs_idx⟩ := Nat.find_spec hex
    have hmin : ∀ u ∈ (X : Set W), ScanAncestor G σ r u → σ.idxOf s ≤ σ.idxOf u := by
      intro u huX hru
      rw [hs_idx]
      exact Nat.find_min' hex ⟨u, huX, hru, rfl⟩
    have hcard' : (X.erase s).card < Fs.length := by
      have h1 : (X.erase s).card + 1 = X.card := Finset.card_erase_add_one hsX
      simp only [List.length_cons] at hcard
      omega
    have hrAX_or_B : (r ∈ A ∨ r ∈ (X : Set W)) ∨ r ∈ B := by
      rcases hT hr.1 with (hrA | hrB) | hrX
      · exact Or.inl (Or.inl hrA)
      · exact Or.inr hrB
      · exact Or.inl (Or.inr hrX)
    rcases hrAX_or_B with hrAX | hrB
    · refine ih hG' hFs' (A := insert s A) (B := B) (X := X.erase s) hcard' ?_ ?_ ?_ ?_
        (mem_insert_of_mem s ha) hb ?_ hab'
      · intro z hz
        rcases hT hz with (hzA | hzB) | hzX
        · exact Or.inl (Or.inl (mem_insert_of_mem s hzA))
        · exact Or.inl (Or.inr hzB)
        · by_cases hzs : z = s
          · exact Or.inl (Or.inl (hzs ▸ mem_insert s A))
          · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hzs, hzX⟩))
      · exact Set.disjoint_insert_left.mpr ⟨Disjoint.notMem_of_mem_right hdBX hsX, hdAB⟩
      · rw [Finset.coe_erase]
        exact Set.disjoint_insert_left.mpr ⟨fun h => h.2 rfl, hdAX.mono_right sdiff_subset⟩
      · rw [Finset.coe_erase]
        exact hdBX.mono_right sdiff_subset
      · intro x hx y hy hxy
        rcases mem_insert_iff.mp hx with rfl | hxA
        · have hGF : (G \ scanForest G σ).Adj x y := hFU_le hxy
          exact hGF.2 (scanForest_selects_sep_edges hG hσ hFAB hT hdAB hdBX hr
            hrAX hrs hmin hy hGF.1)
        · exact hU' x hxA y hy hxy
    · have hBA : ∀ x ∈ B, ∀ y ∈ A, ¬ (scanForest G σ).Adj x y :=
        fun x hx y hy h => hFAB y hy x hx h.symm
      have hT' : T ⊆ B ∪ A ∪ (X : Set W) := by
        intro z hz; rcases hT hz with (h | h) | h
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      refine ih hG' hFs' (A := A) (B := insert s B) (X := X.erase s) hcard' ?_ ?_ ?_ ?_
        ha (mem_insert_of_mem s hb) ?_ hab'
      · intro z hz
        rcases hT hz with (hzA | hzB) | hzX
        · exact Or.inl (Or.inl hzA)
        · exact Or.inl (Or.inr (mem_insert_of_mem s hzB))
        · by_cases hzs : z = s
          · exact Or.inl (Or.inr (hzs ▸ mem_insert s B))
          · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hzs, hzX⟩))
      · exact Set.disjoint_insert_right.mpr ⟨Disjoint.notMem_of_mem_right hdAX hsX, hdAB⟩
      · rw [Finset.coe_erase]
        exact hdAX.mono_right sdiff_subset
      · rw [Finset.coe_erase]
        exact Set.disjoint_insert_left.mpr ⟨fun h => h.2 rfl, hdBX.mono_right sdiff_subset⟩
      · intro x hx y hy hxy
        rcases mem_insert_iff.mp hy with rfl | hyB
        · have hGF : (G \ scanForest G σ).Adj y x := (hFU_le hxy).symm
          exact hGF.2 (scanForest_selects_sep_edges hG hσ hBA hT' hdAB.symm hdAX hr
            (Or.inl hrB) hrs hmin hx hGF.1)
        · exact hU' x hx y hyB hxy

/-- **Lemma 5: strong certificate** (Section 7.1): "Let $F$ be the union of $k$ successive BFS
forests of $J$, taken as above. For every set $S$ of vertices with $|S|<k$, the graphs $F-S$ and
$J-S$ have exactly the same components." -/
theorem lemma5_proved : Lemma5Statement := by
  intro W _ G T Fs hG hFs X hcard a ha b hb
  constructor
  · rintro ⟨p, hp⟩
    induction p with
    | nil => exact reachIn_refl ha
    | @cons a c b hac p ih =>
      have ha' : a ∈ T \ (X : Set W) := hp a (Walk.start_mem_support _)
      have hc' : c ∈ T \ (X : Set W) := hp c (List.mem_cons_of_mem _ (Walk.start_mem_support _))
      have hcb : ReachIn (forestUnion Fs) (T \ (X : Set W)) c b :=
        ih hc' hb (fun y hy => hp y (List.mem_cons_of_mem _ hy))
      have hac_reach : ReachIn (forestUnion Fs) (T \ (X : Set W)) a c := by
        by_contra hnot
        let A : Set W := {y ∈ T \ (X : Set W) | ReachIn (forestUnion Fs) (T \ (X : Set W)) a y}
        let B : Set W := {y ∈ T \ (X : Set W) | ¬ ReachIn (forestUnion Fs) (T \ (X : Set W)) a y}
        have hT : T ⊆ A ∪ B ∪ (X : Set W) := by
          intro z hz
          by_cases hzX : z ∈ (X : Set W)
          · exact Or.inr hzX
          · by_cases hr : ReachIn (forestUnion Fs) (T \ (X : Set W)) a z
            · exact Or.inl (Or.inl ⟨⟨hz, hzX⟩, hr⟩)
            · exact Or.inl (Or.inr ⟨⟨hz, hzX⟩, hr⟩)
        have hdAB : Disjoint A B := Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx.2)
        have hdAX : Disjoint A (X : Set W) := Set.disjoint_left.mpr (fun _ hx hzX => hx.1.2 hzX)
        have hdBX : Disjoint B (X : Set W) := Set.disjoint_left.mpr (fun _ hx hzX => hx.1.2 hzX)
        have haA : a ∈ A := ⟨ha', reachIn_refl ha'⟩
        have hcB : c ∈ B := ⟨hc', hnot⟩
        have hU : ∀ x ∈ A, ∀ y ∈ B, ¬ (forestUnion Fs).Adj x y := by
          intro x hx y hy hxy
          exact hy.2 (reachIn_trans hx.2 (reachIn_of_adj hx.1 hy.1 hxy))
        exact not_adj_of_scanFirstSequence hG hFs hcard hT hdAB hdAX hdBX haA hcB hU hac
      exact reachIn_trans hac_reach hcb
  · exact reachIn_mono_graph (forestUnion_le hFs)

/-! ### Edge count of the scan-first forest union (Section 7.1) -/

private noncomputable def parentEdge (G : SimpleGraph W) (σ : List W) (c : W) : Sym2 W :=
  letI := Classical.dec (∃ p, IsScanParent G σ c p)
  if h : ∃ p, IsScanParent G σ c p then s(c, Classical.choose h) else s(c, c)

private lemma mem_image_parentEdge_of_isScanParent {G : SimpleGraph W} {T : Set W}
    {r₀ : W} {σ' : List W} (hG : HP25.IsSupportedOn G T) (hσ : IsScanOrder G T (r₀ :: σ'))
    {c p : W} (hcp : IsScanParent G (r₀ :: σ') c p) :
    s(c, p) ∈ parentEdge G (r₀ :: σ') '' (T \ {r₀}) := by
  have hcT : c ∈ T := hG hcp.1
  have hcr₀ : c ≠ r₀ := by
    rintro rfl
    have hlt := hcp.2.1
    rw [List.idxOf_cons_self] at hlt
    exact Nat.not_lt_zero _ hlt
  refine ⟨c, ⟨hcT, hcr₀⟩, ?_⟩
  dsimp only [parentEdge]
  split_ifs with hex
  · rw [IsScanParent.unique hG hσ (Classical.choose_spec hex) hcp]
  · exact absurd ⟨p, hcp⟩ hex

private lemma scanForest_edgeSet_finite_and_ncard_le {G : SimpleGraph W} {T : Set W}
    {σ : List W} {n : ℕ} (hTfin : T.Finite) (hTcard : T.ncard = n + 1)
    (hG : HP25.IsSupportedOn G T) (hσ : IsScanOrder G T σ) :
    (scanForest G σ).edgeSet.Finite ∧ (scanForest G σ).edgeSet.ncard ≤ n := by
  cases σ with
  | nil =>
    have hTempty : T = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      (fun y hy => List.not_mem_nil ((hσ.2.1 y).mpr hy))
    rw [hTempty, Set.ncard_empty] at hTcard
    omega
  | cons r₀ σ' =>
    have hr₀T : r₀ ∈ T := (hσ.2.1 r₀).mp List.mem_cons_self
    have hsub : (scanForest G (r₀ :: σ')).edgeSet ⊆ parentEdge G (r₀ :: σ') '' (T \ {r₀}) := by
      intro e he
      induction e using Sym2.ind with
      | _ a b =>
        rcases he with hab | hba
        · exact mem_image_parentEdge_of_isScanParent hG hσ hab
        · rw [Sym2.eq_swap]
          exact mem_image_parentEdge_of_isScanParent hG hσ hba
    have hSfin : (T \ {r₀}).Finite := hTfin.sdiff
    have hIfin : (parentEdge G (r₀ :: σ') '' (T \ {r₀})).Finite := hSfin.image _
    have hEfin : (scanForest G (r₀ :: σ')).edgeSet.Finite := hIfin.subset hsub
    refine ⟨hEfin, ?_⟩
    have hle1 : (scanForest G (r₀ :: σ')).edgeSet.ncard ≤
        (parentEdge G (r₀ :: σ') '' (T \ {r₀})).ncard :=
      Set.ncard_le_ncard hsub hIfin
    have hle2 : (parentEdge G (r₀ :: σ') '' (T \ {r₀})).ncard ≤ (T \ {r₀}).ncard :=
      Set.ncard_image_le hSfin
    have hScard : (T \ {r₀}).ncard = n := by
      have h1 := Set.ncard_sdiff_singleton_of_mem hr₀T
      omega
    omega

private lemma forestUnion_edgeSet_finite_and_ncard_le {G : SimpleGraph W} {T : Set W}
    {Fs : List (SimpleGraph W)} {n : ℕ} (hTfin : T.Finite) (hTcard : T.ncard = n + 1)
    (hG : HP25.IsSupportedOn G T) (hFs : IsScanFirstSequence G T Fs) :
    (forestUnion Fs).edgeSet.Finite ∧ (forestUnion Fs).edgeSet.ncard ≤ Fs.length * n := by
  induction Fs generalizing G with
  | nil =>
    simp [forestUnion]
  | cons F Fs ih =>
    obtain ⟨⟨σ, hσ, rfl⟩, hFs'⟩ := hFs
    have hG' : HP25.IsSupportedOn (G \ scanForest G σ) T := fun _ _ h => hG h.1
    obtain ⟨hFfin, hFcard⟩ := scanForest_edgeSet_finite_and_ncard_le hTfin hTcard hG hσ
    obtain ⟨hUfin, hUcard⟩ := ih hG' hFs'
    simp only [forestUnion, edgeSet_sup, List.length_cons]
    refine ⟨hFfin.union hUfin, ?_⟩
    have hle := Set.ncard_union_le (scanForest G σ).edgeSet (forestUnion Fs).edgeSet
    have hmul : (Fs.length + 1) * n = n + Fs.length * n := by ring
    omega

/-- **The size of the certificate** (Section 7.1): "On $n+1$ vertices their union has at most $4n$
edges." -/
theorem sec71Count_proved : Sec71CountStatement := by
  intro W _ G T Fs n hTfin hTcard hG hFs
  exact (forestUnion_edgeSet_finite_and_ncard_le hTfin hTcard hG hFs).2

end GraphMinor.Crossing
