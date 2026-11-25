module

public import GraphMinor.Surface.CutSimilar

/-!
# Homeomorphisms of surfaces acting on cuffs

Given a presentation `f` of a connected surface `Y` by the normal word `ew a b c`, its `c` cuffs are
parametrized by `holeP a b c f i` (`i < c`). Using the side-tracking moves (`Trk`) of
`WordTrack.lean` and `presents_homeo`, we construct homeomorphisms acting on these cuffs:
- `exists_homeo_perm_cuffs`: for any two surfaces `Y, Y'` presented by `ew a b c` and any
  permutation `π` of `Fin c`, a homeomorphism `Y ≃ₜ Y'` mapping cuff `i` to cuff `π i` preserving
  their `holeP` parameterizations.
- `exists_homeo_reverse_all_cuffs`: for an orientable surface `b = 0`, a homeomorphism `Y ≃ₜ Y`
  reversing every cuff parameterization `u ↦ 1 - u`.
- `exists_homeo_flip_one_cuff` and `exists_homeo_flip_cuffs`: for a non-orientable surface
  `b = b' + 1`, a homeomorphism `Y ≃ₜ Y` reversing any chosen subset of cuffs while fixing all
  other cuffs pointwise.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Function

universe uu

/-! ### Flipping signs of labels while keeping presentations -/

/-- Flipping the signs of labels selected by `c` preserves `Presents (sW w) f` for the same map `f`. -/
theorem presents_flip {T : Type uu} [TopologicalSpace T] {w : List Letter} {f : ℕ × ℂ → T}
    (hf : Presents (sW w) f) (c : ℕ → Bool) : Presents (sW (w.map (flipL c))) f := by
  have hlen : ∀ i, (sW (w.map (flipL c)) i).length = (sW w i).length := fun i => by
    by_cases hi : i = 0
    · subst hi; simp [sW]
    · simp [sW, update_of_ne hi, nW]
  have hD : Dsk (sW (w.map (flipL c))) = Dsk (sW w) := by
    ext a
    have := hlen a.1
    simp only [Dsk, mem_ofPred_eq, ne_eq, ← List.length_eq_zero_iff, this]
  have hget : ∀ i p, (sW (w.map (flipL c)) i)[p]? = ((sW w i)[p]?).map (flipL c) := fun i p => by
    by_cases hi : i = 0
    · subst hi
      have e1 : ∀ v : List Letter, sW v 0 = v := fun v => by simp [sW]
      rw [e1, e1, List.getElem?_map]
    · have e1 : ∀ v : List Letter, sW v i = [] := fun v => by simp [sW, update_of_ne hi, nW]
      rw [e1, e1]; simp
  have hS : ∀ a b, Stp (sW w) a b → Stp (sW (w.map (flipL c))) a b := by
    rintro _ _ ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩
    by_cases hk : c k = true
    · refine ⟨i, j, p, q, k, !ε, !ε', 1 - t, by simp [hget, h1, flipL, hk], by simp [hget, h2, flipL, hk], h3,
        ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_, ?_⟩
      · rw [hlen, sdPt_not]
      · rw [hlen, sdPt_not]
    · exact ⟨i, j, p, q, k, ε, ε', t, by simp [hget, h1, flipL, hk], by simp [hget, h2, flipL, hk], h3, ht,
        by rw [hlen], by rw [hlen]⟩
  have hS' : ∀ a b, Stp (sW (w.map (flipL c))) a b → Stp (sW w) a b := by
    rintro _ _ ⟨i, j, p, q, k, ε, ε', t, h1, h2, h3, ht, rfl, rfl⟩
    rw [hget, Option.map_eq_some_iff] at h1 h2
    obtain ⟨⟨k₁, ε₁⟩, a1, a2⟩ := h1
    obtain ⟨⟨k₂, ε₂⟩, b1, b2⟩ := h2
    simp only [flipL, Prod.mk.injEq] at a2 b2
    obtain ⟨rfl, a3⟩ := a2
    obtain ⟨hk2, b3⟩ := b2
    subst hk2
    by_cases hk : c k₂ = true
    · have e1 : ε₁ = !ε := by rw [← a3]; cases ε₁ <;> simp [hk]
      have e2 : ε₂ = !ε' := by rw [← b3]; cases ε₂ <;> simp [hk]
      subst e1 e2
      refine ⟨i, j, p, q, k₂, !ε, !ε', 1 - t, a1, b1, h3, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_, ?_⟩
      · rw [hlen, sdPt_not]
      · rw [hlen, sdPt_not]
    · have hk' : c k₂ = false := Bool.eq_false_iff.mpr hk
      have e1 : ε₁ = ε := by rw [← a3]; cases ε₁ <;> simp [hk']
      have e2 : ε₂ = ε' := by rw [← b3]; cases ε₂ <;> simp [hk']
      subst e1 e2
      exact ⟨i, j, p, q, k₂, ε₁, ε₂, t, a1, b1, h3, ht, by rw [hlen], by rw [hlen]⟩
  have hP : ∀ a b, PRel (sW w) a b ↔ PRel (sW (w.map (flipL c))) a b := by
    intro a b
    constructor
    · intro h; induction h with
      | rel x y hs => exact .rel _ _ (hS _ _ hs)
      | refl _ => exact .refl _
      | symm _ _ _ ih => exact .symm _ _ ih
      | trans _ _ _ _ _ h1 h2 => exact .trans _ _ _ h1 h2
    · intro h; induction h with
      | rel x y hs => exact .rel _ _ (hS' _ _ hs)
      | refl _ => exact .refl _
      | symm _ _ _ ih => exact .symm _ _ ih
      | trans _ _ _ _ _ h1 h2 => exact .trans _ _ _ h1 h2
  refine ⟨hD.symm ▸ hf.1, hD.symm ▸ hf.2.1, fun a ha b hb => ?_⟩
  rw [hD] at ha hb
  exact (hf.2.2 a ha b hb).trans (hP a b)

/-- A presentation of `sW w` gives a presentation of `sW (w.map (flipL c))` with the same map `f`,
preserving every side whose label has `c k = false` and reversing every side with `c k = true`. -/
theorem sideVal_flip_same {T : Type*} {w : List Letter} {f : ℕ × ℂ → T} {c : ℕ → Bool} {k : ℕ}
    {ρ : ℝ → T} (h : SideVal (sW w) f k ρ) (hc : c k = false) :
    SideVal (sW (w.map (flipL c))) f k ρ := by
  obtain ⟨i, p, h1, h2⟩ := h
  obtain ⟨rfl, h3⟩ := sW_get h1
  refine ⟨0, p, ?_, fun u hu => ?_⟩
  · rw [sW_zero, List.getElem?_map, h3]; simp [flipL, hc]
  · rw [sW_zero, List.length_map]; exact h2 u hu

theorem sideVal_flip_rev {T : Type*} {w : List Letter} {f : ℕ × ℂ → T} {c : ℕ → Bool} {k : ℕ}
    {p : ℕ} {ρ : ℝ → T} (h1 : w[p]? = some (k, false))
    (h2 : ∀ u ∈ Icc (0 : ℝ) 1, f (0, sdPt w.length p false u) = ρ u) (hc : c k = true) :
    SideVal (sW (w.map (flipL c))) f k (fun u => ρ (1 - u)) := by
  refine ⟨0, p, ?_, fun u hu => ?_⟩
  · rw [sW_zero, List.getElem?_map, h1]; simp [flipL, hc]
  · rw [sW_zero, List.length_map, ← sdPt_not]
    simpa using h2 (1 - u) (rev_mem hu)

/-! ### Permuting cuffs of a model surface -/

/-- Bringing all holes in a list `M` to the front of `U ++ rW a b c R`, when `M` is a subset of `R`
with no duplicates. -/
theorem trk_front_list {a b c : ℕ} :
    ∀ (M : List ℕ) (U : List Letter) (R : List ℕ),
      M.Nodup → R.Nodup → (∀ m ∈ M, m ∈ R) → (∀ m' ∈ R, m' < c) →
      (∀ m ∈ M, NoLab U (tL a b m).1) →
      Trk.{uu} {k | ∃ m < c, k = (rL a b m).1}
        (sW (U ++ rW a b c R))
        (sW (hlW (2 * a + b) M.reverse ++ U ++ rW a b c (M.foldl List.erase R))) := by
  intro M
  induction M with
  | nil =>
    intro U R _ _ _ _ _
    simpa [hlW_nil] using Trk.refl.{uu} _ _
  | cons m M ih =>
    intro U R hMn hRn hMR hRc hU
    obtain ⟨hmM, hMn'⟩ := List.nodup_cons.mp hMn
    have hmR : m ∈ R := hMR m (by simp)
    have h1 := (trk_hole.{uu} (a := a) (b := b) (c := c) (U := U) hRn hmR hRc (hU m (by simp))).restrict
      (K' := {k | ∃ m' < c, k = (rL a b m').1}) (by
        rintro k ⟨m', -, rfl⟩
        exact .inl (by simp [rL, tL]; omega))
    have hRn' : (R.erase m).Nodup := hRn.erase m
    have hMR' : ∀ x ∈ M, x ∈ R.erase m := fun x hx =>
      (hRn.mem_erase_iff).mpr ⟨fun h => hmM (h ▸ hx), hMR x (by simp [hx])⟩
    have hRc' : ∀ x ∈ R.erase m, x < c := fun x hx => hRc x (List.mem_of_mem_erase hx)
    have hU' : ∀ x ∈ M, NoLab (hB a b m ++ U) (tL a b x).1 := fun x hx => by
      refine noLab_append.mpr ⟨?_, hU x (by simp [hx])⟩
      have hne : x ≠ m := fun h => hmM (h ▸ hx)
      intro l hl he
      simp only [hB, holB, tL, rL, linv, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl <;> simp only [tL] at he <;> omega
    have h2 := ih (hB a b m ++ U) (R.erase m) hMn' hRn' hMR' hRc' hU'
    have e1 : hlW (2 * a + b) (m :: M).reverse ++ U ++ rW a b c ((m :: M).foldl List.erase R) =
        hlW (2 * a + b) M.reverse ++ (hB a b m ++ U) ++ rW a b c (M.foldl List.erase (R.erase m)) := by
      simp [hlW_append, hlW_cons, hlW_nil, hB, tL, rL, add_assoc]
    rw [e1]
    exact h1.trans (by simpa [List.append_assoc] using h2)

/-- Erasing all elements of a permutation of `R` leaves the empty list. -/
private theorem foldl_erase_eq_nil_of_perm {M R : List ℕ} (h : M.Perm R) :
    M.foldl List.erase R = [] := by
  induction M generalizing R with
  | nil => exact (List.perm_nil.mp h.symm)
  | cons m M ih =>
    have hm : m ∈ R := h.subset (by simp)
    have h1 : (m :: M).Perm (m :: R.erase m) := h.trans (List.perm_cons_erase hm)
    exact ih ((List.perm_cons m).mp h1)

/-- Moving all `c` holes of `ew a b c` to the front in any permutation order `π`. -/
theorem trk_perm_front (a b c : ℕ) (π : Equiv.Perm (Fin c)) :
    Trk.{uu} {k | ∃ m < c, k = (rL a b m).1}
      (sW (ew a b c))
      (sW (hlW (2 * a + b) (List.ofFn fun i : Fin c => (π.symm i).1) ++ rW a b c [])) := by
  let L : List ℕ := List.ofFn fun i : Fin c => (π.symm i).1
  have hLlen : L.length = c := List.length_ofFn
  have hLnd : L.Nodup := by
    rw [List.nodup_ofFn]
    intro i j hij
    exact π.symm.injective (Fin.ext hij)
  have hLmem : ∀ m, m ∈ L ↔ m < c := by
    intro m
    simp only [L, List.mem_ofFn]
    constructor
    · rintro ⟨i, rfl⟩; exact (π.symm i).isLt
    · intro hm; exact ⟨π ⟨m, hm⟩, by simp⟩
  have hPerm : L.reverse.Perm (List.range' 0 c) := by
    refine (List.perm_ext_iff_of_nodup (List.nodup_reverse.mpr hLnd) List.nodup_range').mpr fun m => ?_
    simp [List.mem_reverse, hLmem, List.mem_range'_1]
  have h1 := trk_front_list.{uu} (a := a) (b := b) (c := c) L.reverse [] (List.range' 0 c)
    (List.nodup_reverse.mpr hLnd) List.nodup_range'
    (fun m hm => hPerm.subset hm) (fun m hm => by simpa [List.mem_range'_1] using hm)
    (fun _ _ => noLab_nil)
  rw [List.reverse_reverse, foldl_erase_eq_nil_of_perm hPerm] at h1
  rw [ew_eq_rW]
  simpa [L] using h1

/-- Permuting the cuffs of two surfaces presented by `ew a b c`, preserving each cuff's
`holeP` parameterization. -/
theorem exists_homeo_perm_cuffs {Y Y' : Type uu} [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace Y'] [T2Space Y'] {a b c : ℕ} {f : ℕ × ℂ → Y} {f' : ℕ × ℂ → Y'}
    (hf : Presents (sW (ew a b c)) f) (hf' : Presents (sW (ew a b c)) f')
    (π : Equiv.Perm (Fin c)) :
    ∃ h : Y ≃ₜ Y', ∀ (i : Fin c), ∀ u ∈ Icc (0 : ℝ) 1,
      h (holeP a b c f i.1 u) = holeP a b c f' (π i).1 u := by
  let L : List ℕ := List.ofFn fun i : Fin c => (π.symm i).1
  let L₀ : List ℕ := List.ofFn fun i : Fin c => i.1
  have hL₀ : L₀ = List.range' 0 c := by
    apply List.ext_getElem (by simp [L₀])
    intro n h1 h2; simp [L₀]
  obtain ⟨g₁, hg₁, hs₁⟩ := (trk_perm_front.{uu} a b c π).sideVal hf
  obtain ⟨g₂, hg₂, hs₂⟩ := (trk_perm_front.{uu} a b c (Equiv.refl _)).sideVal hf'
  have hW₂ : hlW (2 * a + b) (List.ofFn fun i : Fin c => ((Equiv.refl (Fin c)).symm i).1) =
      hlW (2 * a + b) (List.range' 0 c) := by
    rw [← hL₀]; rfl
  rw [hW₂] at hg₂ hs₂
  -- Define the label bijection sending hole `m` to hole `π m` and fixing all other labels.
  let r : ℕ → ℕ := fun k =>
    if h : 2 * a + b ≤ k ∧ k < 2 * a + b + 2 * c then
      let m := (k - (2 * a + b)) / 2
      let p := (k - (2 * a + b)) % 2
      2 * a + b + 2 * (π ⟨m, by omega⟩).1 + p
    else k
  have hr_inj : Function.Injective r := by
    intro k₁ k₂ he
    dsimp only [r] at he
    split_ifs at he with h1 h2 h2
    · have h1m : (k₁ - (2 * a + b)) / 2 < c := by omega
      have h2m : (k₂ - (2 * a + b)) / 2 < c := by omega
      have hp1 : (k₁ - (2 * a + b)) % 2 < 2 := Nat.mod_lt _ (by omega)
      have hp2 : (k₂ - (2 * a + b)) % 2 < 2 := Nat.mod_lt _ (by omega)
      have hpeq : (k₁ - (2 * a + b)) % 2 = (k₂ - (2 * a + b)) % 2 := by omega
      have hmeq : (π ⟨(k₁ - (2 * a + b)) / 2, h1m⟩).1 = (π ⟨(k₂ - (2 * a + b)) / 2, h2m⟩).1 := by omega
      have hfin : (⟨(k₁ - (2 * a + b)) / 2, h1m⟩ : Fin c) = ⟨(k₂ - (2 * a + b)) / 2, h2m⟩ :=
        π.injective (Fin.ext hmeq)
      have hdiv : (k₁ - (2 * a + b)) / 2 = (k₂ - (2 * a + b)) / 2 := congrArg Fin.val hfin
      omega
    · exfalso
      have := (π ⟨(k₁ - (2 * a + b)) / 2, by omega⟩).isLt
      have : (k₁ - (2 * a + b)) % 2 < 2 := Nat.mod_lt _ (by omega)
      omega
    · exfalso
      have := (π ⟨(k₂ - (2 * a + b)) / 2, by omega⟩).isLt
      have : (k₂ - (2 * a + b)) % 2 < 2 := Nat.mod_lt _ (by omega)
      omega
    · exact he
  have hr_fix : ∀ k, (k < 2 * a + b ∨ 2 * a + b + 2 * c ≤ k) → r k = k := by
    intro k hk; dsimp only [r]; rw [dite_eq_right (by omega)]
  have hr_tL : ∀ i : Fin c, r (2 * a + b + 2 * i.1) = 2 * a + b + 2 * (π i).1 := by
    intro i
    have hlt : 2 * a + b ≤ 2 * a + b + 2 * i.1 ∧ 2 * a + b + 2 * i.1 < 2 * a + b + 2 * c :=
      ⟨by omega, by have := i.isLt; omega⟩
    dsimp only [r]
    rw [dite_eq_left hlt]
    have e1 : (2 * a + b + 2 * i.1 - (2 * a + b)) / 2 = i.1 := by omega
    have e2 : (2 * a + b + 2 * i.1 - (2 * a + b)) % 2 = 0 := by omega
    simp only [e1, e2, add_zero]
  have hr_rL : ∀ i : Fin c, r (2 * a + b + 2 * i.1 + 1) = 2 * a + b + 2 * (π i).1 + 1 := by
    intro i
    have hlt : 2 * a + b ≤ 2 * a + b + 2 * i.1 + 1 ∧ 2 * a + b + 2 * i.1 + 1 < 2 * a + b + 2 * c :=
      ⟨by omega, by have := i.isLt; omega⟩
    dsimp only [r]
    rw [dite_eq_left hlt]
    have e1 : (2 * a + b + 2 * i.1 + 1 - (2 * a + b)) / 2 = i.1 := by omega
    have e2 : (2 * a + b + 2 * i.1 + 1 - (2 * a + b)) % 2 = 1 := by omega
    simp only [e1, e2]
  have hr_rW : (rW a b c []).map (fun l => (r l.1, l.2)) = rW a b c [] := by
    conv_rhs => rw [← List.map_id (rW a b c [])]
    refine List.map_congr_left fun l hl => ?_
    simp only [rW, hlW_nil, List.append_nil, List.mem_append] at hl
    have hfix : r l.1 = l.1 := by
      rcases hl with (hl | hl) | hl
      · exact hr_fix _ (.inl (by have := (hW_labels 0 a l hl).2; omega))
      · exact hr_fix _ (.inl (cW_labels (2 * a) b l hl).2)
      · simp only [eW, List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> exact hr_fix _ (.inr (by omega))
    exact Prod.ext hfix rfl
  have hr_hlW : (hlW (2 * a + b) L).map (fun l => (r l.1, l.2)) =
      hlW (2 * a + b) (List.range' 0 c) := by
    rw [← hL₀]
    simp only [hlW, L, L₀, List.map_flatMap]
    have hLmap : (List.ofFn fun i : Fin c => (π.symm i).1) = (List.finRange c).map (fun i : Fin c => (π.symm i).1) := by
      rw [List.ofFn_eq_map]
    have hL0map : (List.ofFn fun i : Fin c => i.1) = (List.finRange c).map (fun i : Fin c => i.1) := by
      rw [List.ofFn_eq_map]
    rw [hLmap, hL0map, List.flatMap_map, List.flatMap_map]
    refine List.flatMap_congr fun i _ => ?_
    simp only [holB, linv, List.map_cons, List.map_nil, hr_tL (π.symm i), hr_rL (π.symm i),
      Equiv.apply_symm_apply]
  have hg₁' : Presents (sW (hlW (2 * a + b) (List.range' 0 c) ++ rW a b c [])) g₁ := by
    have hrel := (presents_relab (r := r) (W := sW (hlW (2 * a + b) L ++ rW a b c []))
      (fun _ _ _ _ _ _ h => hr_inj h) g₁).mp hg₁
    rwa [relab_sW, List.map_append, hr_hlW, hr_rW] at hrel
  obtain ⟨h, hh⟩ := presents_homeo (finW_sW _) hg₁' hg₂
  refine ⟨h, fun i u hu => ?_⟩
  have hside1 := hs₁ (rL a b i.1).1 ⟨i.1, i.isLt, rfl⟩ _ (by rw [ew_eq_rW]; exact sideVal_hole hf i.isLt)
  have hside2 := hs₂ (rL a b (π i).1).1 ⟨(π i).1, (π i).isLt, rfl⟩ _ (by rw [ew_eq_rW]; exact sideVal_hole hf' (π i).isLt)
  obtain ⟨j₁, p₁, hp₁, hv₁⟩ := hside1
  obtain ⟨rfl, hp₁'⟩ := sW_get hp₁
  rw [sW_zero] at hv₁
  have hp₁_rel : (hlW (2 * a + b) (List.range' 0 c) ++ rW a b c [])[p₁]? =
      some ((rL a b (π i).1).1, true) := by
    rw [← hr_hlW, ← hr_rW, ← List.map_append, List.getElem?_map, hp₁']
    simp [rL, hr_rL i]
  have hcnt : cnt (hlW (2 * a + b) (List.range' 0 c) ++ rW a b c []) (rL a b (π i).1).1 = 1 := by
    rw [cnt_append]
    have hc2 : cnt (rW a b c []) (rL a b (π i).1).1 = 0 :=
      noLab_iff_cnt.mp (noLab_rW (by simp [rL]; omega) (by simp [rL]; have := (π i).isLt; omega) (by simp))
    have h1 : ∀ (K : List ℕ), K.Nodup → ∀ m ∈ K, cnt (hlW (2 * a + b) K) (rL a b m).1 = 1 := by
      intro K hK
      induction K with
      | nil => simp
      | cons x K ih =>
        intro m hm
        obtain ⟨hxK, hKn⟩ := List.nodup_cons.mp hK
        rw [hlW_cons, cnt_append]
        rcases List.mem_cons.mp hm with rfl | hm'
        · have hcK : cnt (hlW (2 * a + b) K) (rL a b m).1 = 0 :=
            noLab_iff_cnt.mp (noLab_hlW fun m' hm' => by
              have hne : m' ≠ m := fun he => hxK (he ▸ hm')
              simp [rL]; omega)
          rw [hcK, add_zero]
          simp [holB, linv, cnt_cons, cnt_nil, rL]
        · have hne : m ≠ x := fun he => hxK (he ▸ hm')
          have hcx : cnt (holB (2 * a + b + 2 * x, true) (2 * a + b + 2 * x + 1, true)) (rL a b m).1 = 0 := by
            simp only [holB, linv, cnt_cons, cnt_nil, rL]
            split_ifs <;> omega
          rw [hcx, zero_add]
          exact ih hKn m hm'
    rw [hc2, add_zero]
    exact h1 _ List.nodup_range' _ (List.mem_range'_1.mpr ⟨Nat.zero_le _, by simp⟩)
  have hv₂ := hside2.at_word hp₁_rel hcnt u hu
  have hlen_eq : (hlW (2 * a + b) (List.range' 0 c) ++ rW a b c []).length =
      (hlW (2 * a + b) L ++ rW a b c []).length := by
    calc (hlW (2 * a + b) (List.range' 0 c) ++ rW a b c []).length
        = ((hlW (2 * a + b) L ++ rW a b c []).map fun l => (r l.1, l.2)).length := by
            rw [List.map_append, hr_hlW, hr_rW]
      _ = (hlW (2 * a + b) L ++ rW a b c []).length := List.length_map _
  have hmem : (0, sdPt (hlW (2 * a + b) (List.range' 0 c) ++ rW a b c []).length p₁ true u) ∈
      Dsk (sW (hlW (2 * a + b) (List.range' 0 c) ++ rW a b c [])) := by
    refine ⟨?_, (norm_per _ _).le⟩
    intro he; simp only [sW_zero] at he; rw [he] at hp₁_rel; simp at hp₁_rel
  rw [← hv₁ u hu, ← hlen_eq, hh _ hmem, hv₂]

/-! ### Reversing all cuffs of an orientable surface -/

private theorem hW_rev_relab (a : ℕ) :
    let r : ℕ → ℕ := fun k => if k < 2 * a then (2 * (a - 1 - k / 2) + (1 - k % 2)) else k
    (winv (hW 0 a)).map (fun l => (r l.1, l.2)) = hW 0 a := by
  intro r
  have hrev : ∀ n s, winv (hW s n) = ((List.range' 0 n).reverse).flatMap fun j =>
      hndB (s + 2 * j + 1, true) (s + 2 * j, true) := by
    intro n
    induction n with
    | zero => intro s; simp [hW, winv]
    | succ n ih =>
      intro s
      have he : hW s (n + 1) = hndB (s, true) (s + 1, true) ++ hW (s + 2) n := rfl
      rw [he, winv_append, ih (s + 2), winv_hndB, List.range'_succ, List.reverse_cons,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      congr 1
      rw [List.range'_eq_map_range, List.range'_eq_map_range, ← List.map_reverse, ← List.map_reverse,
        List.flatMap_map, List.flatMap_map]
      refine List.flatMap_congr fun j _ => ?_
      have e1 : s + 2 + 2 * j = s + 2 * (1 + j) := by omega
      simp [e1]
  have hfw : ∀ n s, hW s n = (List.range' 0 n).flatMap fun j =>
      hndB (s + 2 * j, true) (s + 2 * j + 1, true) := by
    intro n
    induction n with
    | zero => intro s; simp [hW]
    | succ n ih =>
      intro s
      have he : hW s (n + 1) = hndB (s, true) (s + 1, true) ++ hW (s + 2) n := rfl
      rw [he, ih (s + 2), List.range'_succ, List.flatMap_cons]
      congr 1
      rw [List.range'_eq_map_range, List.range'_eq_map_range, List.flatMap_map, List.flatMap_map]
      refine List.flatMap_congr fun j _ => ?_
      have e1 : s + 2 + 2 * j = s + 2 * (1 + j) := by omega
      simp [e1]
  rw [hrev a 0, hfw a 0, List.map_flatMap]
  have hrange : (List.range' 0 a).reverse = (List.range' 0 a).map (fun j => a - 1 - j) := by
    apply List.ext_getElem (by simp)
    intro n h1 h2
    simp only [List.getElem_reverse, List.length_range', List.getElem_range', zero_add,
      List.getElem_map]
    omega
  rw [hrange, List.flatMap_map]
  refine List.flatMap_congr fun j hj => ?_
  have hja : j < a := by simpa [List.mem_range'_1] using hj
  have h1 : 2 * (a - 1 - j) + 1 < 2 * a := by omega
  have h2 : 2 * (a - 1 - j) < 2 * a := by omega
  have hr1 : r (2 * (a - 1 - j) + 1) = 2 * j := by
    dsimp only [r]; rw [ite_eq_left h1]; omega
  have hr2 : r (2 * (a - 1 - j)) = 2 * j + 1 := by
    dsimp only [r]; rw [ite_eq_left h2]; omega
  simp only [hndB, linv, zero_add, List.map_cons, List.map_nil, hr1, hr2]

/-- On an orientable surface presented by `ew a 0 c`, there is a homeomorphism reversing all
cuff parameterizations `u ↦ 1 - u` simultaneously. -/
theorem exists_homeo_reverse_all_cuffs {Y : Type uu} [TopologicalSpace Y] [T2Space Y]
    {a c : ℕ} {f : ℕ × ℂ → Y} (hf : Presents (sW (ew a 0 c)) f) :
    ∃ h : Y ≃ₜ Y, ∀ i < c, ∀ u ∈ Icc (0 : ℝ) 1,
      h (holeP a 0 c f i u) = holeP a 0 c f i (1 - u) := by
  -- Reverse the polygon via complex conjugation.
  let f₁ : ℕ × ℂ → Y := f ∘ (fun a => if a.1 = 0 then (0, (starRingEnd ℂ) a.2) else a)
  have hf₁ : Presents (sW (winv (ew a 0 c))) f₁ := hf.of_map isPolyMap_rev
  -- Flip the sign of all free hole labels `(rL a 0 i).1`.
  let flipC : ℕ → Bool := fun k => decide (∃ i < c, k = (rL a 0 i).1)
  have hf₂ : Presents (sW ((winv (ew a 0 c)).map (flipL flipC))) f₁ := presents_flip hf₁ flipC
  -- Compute `(winv (ew a 0 c)).map (flipL flipC)`.
  have hew : ew a 0 c = hW 0 a ++ hlW (2 * a) (List.range' 0 c) ++ eW a 0 c := by
    rw [ew_eq_rW]; simp [rW, cW]
  have hwinv_eW : winv (eW a 0 c) = eW a 0 c := by simp [eW, winv, linv]
  have hflip_eW : (eW a 0 c).map (flipL flipC) = eW a 0 c := by
    conv_rhs => rw [← List.map_id (eW a 0 c)]
    refine List.map_congr_left fun l hl => ?_
    have hfalse : flipC l.1 = false := by
      simp only [flipC, decide_eq_false_iff_not, not_exists, not_and]
      intro i hi he
      simp only [eW, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp only [rL] at he <;> omega
    simp [flipL, hfalse]
  have hflip_hW : (winv (hW 0 a)).map (flipL flipC) = winv (hW 0 a) := by
    conv_rhs => rw [← List.map_id (winv (hW 0 a))]
    refine List.map_congr_left fun l hl => ?_
    have hlt : l.1 < 2 * a := by
      simp only [winv, List.mem_map, List.mem_reverse] at hl
      obtain ⟨m, hm, rfl⟩ := hl
      have := (hW_labels 0 a m hm).2; simp only [linv]; omega
    have hfalse : flipC l.1 = false := by
      simp only [flipC, decide_eq_false_iff_not, not_exists, not_and]
      intro i _ he; simp only [rL] at he; omega
    simp [flipL, hfalse]
  have hwinv_hlW : ∀ L : List ℕ, (∀ m ∈ L, m < c) →
      (winv (hlW (2 * a) L)).map (flipL flipC) = hlW (2 * a) L.reverse := by
    intro L
    induction L with
    | nil => intro _; simp [hlW_nil, winv]
    | cons m L ih =>
      intro hLc
      have hm : m < c := hLc m (by simp)
      rw [hlW_cons, winv_append, List.map_append, ih (fun x hx => hLc x (by simp [hx])),
        List.reverse_cons, hlW_append, hlW_cons, hlW_nil, List.append_nil, winv_holB]
      congr 1
      have h1 : flipC (2 * a + 2 * m) = false := by
        simp only [flipC, decide_eq_false_iff_not, not_exists, not_and]
        intro i _ he; simp only [rL] at he; omega
      have h2 : flipC (2 * a + 2 * m + 1) = true := by
        simp only [flipC, decide_eq_true_eq]
        exact ⟨m, hm, by simp [rL]⟩
      simp [holB, linv, flipL, h1, h2]
  have hw_eq : (winv (ew a 0 c)).map (flipL flipC) =
      eW a 0 c ++ hlW (2 * a) (List.range' 0 c).reverse ++ winv (hW 0 a) := by
    rw [hew, winv_append, winv_append, hwinv_eW, List.map_append, List.map_append,
      hflip_eW, hflip_hW, hwinv_hlW _ (fun m hm => by simpa [List.mem_range'_1] using hm)]
    simp [List.append_assoc]
  rw [hw_eq] at hf₂
  -- Track each free hole side `(rL a 0 i).1` in `hf₂`: its image is `u ↦ holeP a 0 c f i (1 - u)`.
  have hside_rev : ∀ i < c,
      SideVal (sW (eW a 0 c ++ hlW (2 * a) (List.range' 0 c).reverse ++ winv (hW 0 a))) f₁
        (rL a 0 i).1 (fun u => holeP a 0 c f i (1 - u)) := by
    intro i hi
    have hs0 := sideVal_hole hf hi
    rw [← ew_eq_rW] at hs0
    obtain ⟨j, p, hp, hv⟩ := hs0
    obtain ⟨rfl, hp'⟩ := sW_get hp
    rw [sW_zero] at hv
    have hp_lt : p < (ew a 0 c).length := (List.getElem?_eq_some_iff.mp hp').1
    set q := (ew a 0 c).length - 1 - p with hq
    have hq_lt : q < (ew a 0 c).length := by omega
    have hq_get : (winv (ew a 0 c))[q]? = some ((rL a 0 i).1, false) := by
      rw [winv, List.getElem?_map, List.getElem?_reverse hq_lt]
      have e : (ew a 0 c).length - 1 - q = p := by omega
      rw [e, hp']; rfl
    have hq_val : ∀ u ∈ Icc (0 : ℝ) 1, f₁ (0, sdPt (winv (ew a 0 c)).length q false u) =
        holeP a 0 c f i u := by
      intro u hu
      dsimp only [f₁]
      simp only [Function.comp_apply, ite_true, winv, List.length_map, List.length_reverse]
      rw [conj_sdPt hq_lt, Bool.not_false]
      have e : (ew a 0 c).length - 1 - q = p := by omega
      rw [e, hv u hu]
    have hfl := sideVal_flip_rev (c := flipC) hq_get hq_val (by simp only [flipC, decide_eq_true_eq]; exact ⟨i, hi, rfl⟩)
    rwa [hw_eq] at hfl
  -- Relabel the handles of `winv (hW 0 a)` back to `hW 0 a` (fixing all hole and `eW` labels).
  let r : ℕ → ℕ := fun k => if k < 2 * a then (2 * (a - 1 - k / 2) + (1 - k % 2)) else k
  have hr_inj : Function.Injective r := by
    intro k₁ k₂ he
    dsimp only [r] at he
    split_ifs at he with h1 h2 h2
    · omega
    · omega
    · omega
    · exact he
  have hr_fix : ∀ k, 2 * a ≤ k → r k = k := fun k hk => by dsimp only [r]; rw [ite_eq_right (by omega)]
  have hr_eW : (eW a 0 c).map (fun l => (r l.1, l.2)) = eW a 0 c := by
    conv_rhs => rw [← List.map_id (eW a 0 c)]
    refine List.map_congr_left fun l hl => ?_
    simp only [eW, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> exact Prod.ext (hr_fix _ (by omega)) rfl
  have hr_hlW : (hlW (2 * a) (List.range' 0 c).reverse).map (fun l => (r l.1, l.2)) =
      hlW (2 * a) (List.range' 0 c).reverse := by
    conv_rhs => rw [← List.map_id (hlW (2 * a) (List.range' 0 c).reverse)]
    refine List.map_congr_left fun l hl => ?_
    obtain ⟨m, -, hm⟩ := hlW_labels l hl
    exact Prod.ext (hr_fix _ (by omega)) rfl
  have hf₃ : Presents (sW (eW a 0 c ++ hlW (2 * a) (List.range' 0 c).reverse ++ hW 0 a)) f₁ := by
    have hrel := (presents_relab (r := r) (W := sW (eW a 0 c ++ hlW (2 * a) (List.range' 0 c).reverse ++ winv (hW 0 a)))
      (fun _ _ _ _ _ _ h => hr_inj h) f₁).mp hf₂
    rwa [relab_sW, List.map_append, List.map_append, hr_eW, hr_hlW, hW_rev_relab a] at hrel
  have hside₃ : ∀ i < c,
      SideVal (sW (eW a 0 c ++ hlW (2 * a) (List.range' 0 c).reverse ++ hW 0 a)) f₁
        (rL a 0 i).1 (fun u => holeP a 0 c f i (1 - u)) := by
    intro i hi
    obtain ⟨j, p, hp, hv⟩ := hside_rev i hi
    obtain ⟨rfl, hp'⟩ := sW_get hp
    rw [sW_zero] at hv
    refine ⟨0, p, ?_, fun u hu => ?_⟩
    · rw [sW_zero, ← hr_eW, ← hr_hlW, ← hW_rev_relab a, ← List.map_append, ← List.map_append,
        List.getElem?_map, hp']
      simp [hr_fix (rL a 0 i).1 (by simp [rL]; omega)]
    · rw [sW_zero]
      have hlen : (eW a 0 c ++ hlW (2 * a) (List.range' 0 c).reverse ++ hW 0 a).length =
          (eW a 0 c ++ hlW (2 * a) (List.range' 0 c).reverse ++ winv (hW 0 a)).length := by
        simp [winv]
      rw [hlen]
      exact hv u hu
  -- Rotate `eW a 0 c` to the end: `hlW (2*a) (range' 0 c).reverse ++ hW 0 a ++ eW a 0 c`,
  -- which is `hlW (2*a) (range' 0 c).reverse ++ rW a 0 c []`.
  have hrot := trk_rot_sW.{uu} (w := eW a 0 c ++ hlW (2 * a) (List.range' 0 c).reverse ++ hW 0 a)
    (eW a 0 c) (hlW (2 * a) (List.range' 0 c).reverse ++ hW 0 a)
    (by simp [List.append_assoc]) rfl
  obtain ⟨g₁, hg₁, htr₁⟩ := hrot.sideVal hf₃
  have hrew : (hlW (2 * a) (List.range' 0 c).reverse ++ hW 0 a) ++ eW a 0 c =
      hlW (2 * a) (List.range' 0 c).reverse ++ rW a 0 c [] := by simp [rW, cW, hlW_nil, List.append_assoc]
  rw [hrew] at hg₁ htr₁
  -- Compare with `trk_perm_front` for the reversing permutation `i ↦ c - 1 - i` on `f`!
  let revPerm : Equiv.Perm (Fin c) :=
    { toFun := fun i => ⟨c - 1 - i.1, by omega⟩
      invFun := fun i => ⟨c - 1 - i.1, by omega⟩
      left_inv := fun i => Fin.ext (by dsimp; omega)
      right_inv := fun i => Fin.ext (by dsimp; omega) }
  have hLrev : (List.ofFn fun i : Fin c => (revPerm.symm i).1) = (List.range' 0 c).reverse := by
    apply List.ext_getElem (by simp)
    intro n h1 h2
    simp only [List.getElem_ofFn, List.getElem_reverse, List.length_range', List.getElem_range',
      zero_add, revPerm, Equiv.symm_mk, Equiv.coe_fn_mk]
    omega
  obtain ⟨g₂, hg₂, htr₂⟩ := (trk_perm_front.{uu} a 0 c revPerm).sideVal hf
  simp only [add_zero] at hg₂ htr₂
  rw [hLrev] at hg₂ htr₂
  obtain ⟨h, hh⟩ := presents_homeo (finW_sW _) hg₂ hg₁
  refine ⟨h, fun i hi u hu => ?_⟩
  have h2 := htr₂ (rL a 0 i).1 ⟨i, hi, rfl⟩ _ (by rw [ew_eq_rW]; exact sideVal_hole hf hi)
  have h1 := htr₁ (rL a 0 i).1 (mem_univ _) _ (hside₃ i hi)
  obtain ⟨j, p, hp, hv₂⟩ := h2
  obtain ⟨rfl, hp'⟩ := sW_get hp
  rw [sW_zero] at hv₂
  have hcnt : cnt (hlW (2 * a) (List.range' 0 c).reverse ++ rW a 0 c []) (rL a 0 i).1 = 1 := by
    rw [cnt_append]
    have hc2 : cnt (rW a 0 c []) (rL a 0 i).1 = 0 :=
      noLab_iff_cnt.mp (noLab_rW (by simp [rL]; omega) (by simp [rL]; omega) (by simp))
    have h1' : ∀ (K : List ℕ), K.Nodup → ∀ m ∈ K, cnt (hlW (2 * a) K) (rL a 0 m).1 = 1 := by
      intro K hK
      induction K with
      | nil => simp
      | cons x K ih =>
        intro m hm
        obtain ⟨hxK, hKn⟩ := List.nodup_cons.mp hK
        rw [hlW_cons, cnt_append]
        rcases List.mem_cons.mp hm with rfl | hm'
        · have hcK : cnt (hlW (2 * a) K) (rL a 0 m).1 = 0 :=
            noLab_iff_cnt.mp (noLab_hlW fun m' hm' => by
              have hne : m' ≠ m := fun he => hxK (he ▸ hm')
              simp [rL]; omega)
          rw [hcK, add_zero]; simp [holB, linv, cnt_cons, cnt_nil, rL]
        · have hne : m ≠ x := fun he => hxK (he ▸ hm')
          have hcx : cnt (holB (2 * a + 2 * x, true) (2 * a + 2 * x + 1, true)) (rL a 0 m).1 = 0 := by
            simp only [holB, linv, cnt_cons, cnt_nil, rL]; split_ifs <;> omega
          rw [hcx, zero_add]; exact ih hKn m hm'
    rw [hc2, add_zero]
    exact h1' _ (List.nodup_reverse.mpr List.nodup_range') _
      (List.mem_reverse.mpr (List.mem_range'_1.mpr ⟨Nat.zero_le _, by simpa using hi⟩))
  have hv₁ := h1.at_word hp' hcnt u hu
  have hmem : (0, sdPt (hlW (2 * a) (List.range' 0 c).reverse ++ rW a 0 c []).length p true u) ∈
      Dsk (sW (hlW (2 * a) (List.range' 0 c).reverse ++ rW a 0 c [])) := by
    refine ⟨?_, (norm_per _ _).le⟩
    intro he; simp only [sW_zero] at he; rw [he] at hp'; simp at hp'
  rw [← hv₂ u hu, hh _ hmem, hv₁]

/-! ### Reversing a single cuff on a non-orientable surface -/

/-- Reversing the left word of `dW a c`: sides of `c` are completely unchanged, while sides of `a`
flip sign with the same parameter `t`. -/
private theorem presents_dW_rev_left {T : Type uu} [TopologicalSpace T] {a c : List Letter}
    {f : ℕ × ℂ → T} (hf : Presents (dW a c) f) :
    ∃ f' : ℕ × ℂ → T, Presents (dW (winv a) c) f' ∧
      (∀ p k ε, c[p]? = some (k, ε) → ∀ t ∈ Icc (0 : ℝ) 1,
        f' (1, sdPt c.length p ε t) = f (1, sdPt c.length p ε t)) ∧
      (∀ p k ε, a[p]? = some (k, ε) → ∃ p', (winv a)[p']? = some (k, !ε) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, f' (0, sdPt (winv a).length p' (!ε) t) = f (0, sdPt a.length p ε t)) := by
  have hrev : IsPolyMap (dW a c) (dW (winv a) c)
      (fun x => if x.1 = 0 then (0, (starRingEnd ℂ) x.2) else x) := by
    rw [dW_comm, dW_comm]
    exact isPolyMap_rev (W := update nW 1 c) (i := 0) (w := a)
  refine ⟨_, hf.of_map hrev, ?_, ?_⟩
  · intro p k ε _ t _
    simp [Function.comp_apply]
  · intro p k ε h
    have hp : p < a.length := (List.getElem?_eq_some_iff.mp h).1
    refine ⟨a.length - 1 - p, ?_, fun t _ => ?_⟩
    · rw [winv, List.getElem?_map, List.getElem?_reverse (by omega)]
      have e : a.length - 1 - (a.length - 1 - p) = p := by omega
      rw [e, h]; rfl
    · simp only [Function.comp_apply, ite_true, winv, List.length_map, List.length_reverse]
      rw [conj_sdPt (by omega), Bool.not_not]
      have e : a.length - 1 - (a.length - 1 - p) = p := by omega
      rw [e]

/-- Side-tracking version of `ruleB` with `u₁ = []`, `v₂ = []`:
`x :: u₂ ++ v₁ ++ [x]` transforms to `u₂ ++ x :: winv v₁ ++ [x]`, keeping all sides in `u₂`
unchanged and reversing the signs of all sides in `v₁` with the same parameter `t`. -/
theorem presents_ruleB_flip {T : Type uu} [TopologicalSpace T] [T2Space T]
    {x : Letter} {u₂ v₁ : List Letter} (h2 : NoLab u₂ x.1) (h3 : NoLab v₁ x.1)
    {f : ℕ × ℂ → T} (hf : Presents (sW (x :: (u₂ ++ v₁ ++ [x]))) f) :
    ∃ f' : ℕ × ℂ → T, Presents (sW (u₂ ++ x :: (winv v₁ ++ [x]))) f' ∧
      (∀ k, k ≠ x.1 → NoLab v₁ k → ∀ p ε, (x :: (u₂ ++ v₁ ++ [x]))[p]? = some (k, ε) →
        ∃ p', (u₂ ++ x :: (winv v₁ ++ [x]))[p']? = some (k, ε) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, f' (0, sdPt (u₂ ++ x :: (winv v₁ ++ [x])).length p' ε t) =
          f (0, sdPt (x :: (u₂ ++ v₁ ++ [x])).length p ε t)) ∧
      (∀ k, k ≠ x.1 → NoLab u₂ k → ∀ p ε, (x :: (u₂ ++ v₁ ++ [x]))[p]? = some (k, ε) →
        ∃ p', (u₂ ++ x :: (winv v₁ ++ [x]))[p']? = some (k, !ε) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, f' (0, sdPt (u₂ ++ x :: (winv v₁ ++ [x])).length p' (!ε) t) =
          f (0, sdPt (x :: (u₂ ++ v₁ ++ [x])).length p ε t)) := by
  set X := x :: (u₂ ++ v₁ ++ [x]) with hX
  obtain ⟨y, -, hy⟩ := exists_fresh X
  have hy' : y ≠ x.1 := fun he => hy x (by simp [hX]) he.symm
  have e : X = (x :: u₂) ++ (v₁ ++ [x]) := by simp [hX]
  have hA : NoLab (x :: u₂) y ∧ NoLab (v₁ ++ [x]) y := by rw [e] at hy; exact noLab_append.mp hy
  -- Step 1: cut `X` into `dW ((y, !x.2) :: (v₁ ++ [x])) ((y, x.2) :: (x :: u₂))`.
  have hcut := trk_cut_sW.{uu} (y := y) (u := v₁ ++ [x]) (v := x :: u₂) (!x.2) (by simp) (by simp)
    (by rw [← e]; exact hy)
  rw [← e] at hcut
  simp only [Bool.not_not] at hcut
  obtain ⟨f₁, hf₁, htr1⟩ := hcut T f hf
  -- Step 2: reverse slot 0 of `dW`.
  obtain ⟨f₂, hf₂, htr2_right, htr2_left⟩ := presents_dW_rev_left hf₁
  have e0 : winv ((y, !x.2) :: (v₁ ++ [x])) = linv x :: (winv v₁ ++ [(y, x.2)]) := by
    simp [winv, linv]
  rw [e0] at hf₂ htr2_left
  -- Step 3: rotate slot 1 of `dW`: `(y, x.2) :: (x :: u₂) ↦ x :: (u₂ ++ [(y, x.2)])`.
  have hrot := trk_dW_right.{uu} [(y, x.2)] (x :: u₂) (linv x :: (winv v₁ ++ [(y, x.2)]))
  have er1 : [(y, x.2)] ++ (x :: u₂) = (y, x.2) :: (x :: u₂) := rfl
  have er2 : (x :: u₂) ++ [(y, x.2)] = x :: (u₂ ++ [(y, x.2)]) := by simp
  rw [er1, er2] at hrot
  obtain ⟨f₃, hf₃, htr3⟩ := hrot T f₂ hf₂
  -- Step 4: glue along `x`.
  set U := winv v₁ ++ [(y, x.2)] with hU
  set V := u₂ ++ [(y, x.2)] with hV
  have hx1 : NoLab U x.1 := noLab_append.mpr ⟨noLab_winv.mpr h3, noLab_cons.mpr ⟨hy', noLab_nil⟩⟩
  have hx2 : NoLab V x.1 := noLab_append.mpr ⟨h2, noLab_cons.mpr ⟨hy', noLab_nil⟩⟩
  have hc : NoLab (V ++ U) x.1 := noLab_append.mpr ⟨hx2, hx1⟩
  have hgl := trk_glue_sW.{uu} (y := x.1) (u := U) (v := V) (!x.2) (by simp [hU]) (by simp [hV]) hc
  have eg1 : ((x.1, !x.2) : Letter) = linv x := rfl
  have eg2 : ((x.1, !!x.2) : Letter) = x := by simp
  rw [eg1, eg2] at hgl
  obtain ⟨f₄, hf₄, htr4⟩ := hgl T f₃ hf₃
  -- Step 5: rename `y ↦ x.1`.
  have hren := trk_relab.{uu} (r := fun n => if n = y then x.1 else n) (W := sW (V ++ U))
    (K := {k | k ≠ y}) (fun k hk => ite_eq_right hk) (relab_rename_inj hc)
  have hm : ∀ {a : List Letter}, NoLab a y → (a.map fun l => (if l.1 = y then x.1 else l.1, l.2)) = a :=
    fun h => map_rename_of_noLab h
  have hu₂y : NoLab u₂ y := (noLab_cons.mp hA.1).2
  have hv₁y : NoLab v₁ y := (noLab_append.mp hA.2).1
  have efinal : ((V ++ U).map fun l => (if l.1 = y then x.1 else l.1, l.2)) =
      u₂ ++ x :: (winv v₁ ++ [x]) := by
    simp only [hU, hV, List.map_append, List.map_cons, hm hu₂y, hm (noLab_winv.mpr hv₁y),
      ite_true, List.append_assoc, List.cons_append]
    simp [List.map_nil]
  rw [relab_sW, efinal] at hren
  obtain ⟨f₅, hf₅, htr5⟩ := hren T f₄ hf₄
  refine ⟨f₅, hf₅, ?_, ?_⟩
  · -- Labels in `u₂` (not in `v₁`, not `x.1`): come from slot 1 in `f₁`, unchanged by `rev_left`!
    intro k hkx hkv p ε hp
    have hky : k ≠ y := fun he => hy (k, ε) (List.mem_of_getElem? hp) he
    obtain ⟨i₁, p₁, hp₁, hv₁⟩ := htr1 k (mem_univ _) 0 p ε (by rwa [sW_zero])
    have hi₁ : i₁ = 1 := by
      rcases dW_cases ((y, !x.2) :: (v₁ ++ [x])) ((y, x.2) :: (x :: u₂)) i₁ with ⟨rfl, h⟩ | ⟨rfl, _⟩ | h
      · exfalso
        rw [h] at hp₁
        have hmem := List.mem_of_getElem? hp₁
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hmem
        rcases hmem with hmem | hmem | hmem
        · exact hky (congrArg Prod.fst hmem)
        · exact hkv (k, ε) hmem rfl
        · exact hkx (congrArg Prod.fst hmem)
      · rfl
      · exfalso; rw [h] at hp₁; simp at hp₁
    subst hi₁
    have hp₁' : ((y, x.2) :: (x :: u₂))[p₁]? = some (k, ε) := by simpa [dW] using hp₁
    have hv₂ : ∀ t ∈ Icc (0 : ℝ) 1,
        f₂ (1, sdPt ((y, x.2) :: (x :: u₂)).length p₁ ε t) = f (0, sdPt X.length p ε t) := by
      intro t ht
      rw [htr2_right p₁ k ε hp₁' t ht]
      simpa [dW, sW_zero] using hv₁ t ht
    obtain ⟨i₃, p₃, hp₃, hv₃⟩ := htr3 k (mem_univ _) 1 p₁ ε (by simpa [dW] using hp₁')
    obtain ⟨i₄, p₄, hp₄, hv₄⟩ := htr4 k hkx i₃ p₃ ε hp₃
    obtain ⟨i₅, p₅, hp₅, hv₅⟩ := htr5 k hky i₄ p₄ ε hp₄
    obtain ⟨rfl, hp₅'⟩ := sW_get hp₅
    refine ⟨p₅, hp₅', fun t ht => ?_⟩
    have e := (hv₅ t ht).trans ((hv₄ t ht).trans (hv₃ t ht))
    rw [sW_zero] at e
    simpa [dW] using e.trans (hv₂ t ht)
  · -- Labels in `v₁` (not in `u₂`, not `x.1`): come from slot 0 in `f₁`, reversed by `rev_left`!
    intro k hkx hku p ε hp
    have hky : k ≠ y := fun he => hy (k, ε) (List.mem_of_getElem? hp) he
    obtain ⟨i₁, p₁, hp₁, hv₁⟩ := htr1 k (mem_univ _) 0 p ε (by rwa [sW_zero])
    have hi₁ : i₁ = 0 := by
      rcases dW_cases ((y, !x.2) :: (v₁ ++ [x])) ((y, x.2) :: (x :: u₂)) i₁ with ⟨rfl, _⟩ | ⟨rfl, h⟩ | h
      · rfl
      · exfalso
        rw [h] at hp₁
        have hmem := List.mem_of_getElem? hp₁
        simp only [List.mem_cons] at hmem
        rcases hmem with hmem | hmem | hmem
        · exact hky (congrArg Prod.fst hmem)
        · exact hkx (congrArg Prod.fst hmem)
        · exact hku (k, ε) hmem rfl
      · exfalso; rw [h] at hp₁; simp at hp₁
    subst hi₁
    have hp₁' : ((y, !x.2) :: (v₁ ++ [x]))[p₁]? = some (k, ε) := by simpa [dW, sW] using hp₁
    obtain ⟨p₂, hp₂, hv₂⟩ := htr2_left p₁ k ε hp₁'
    obtain ⟨i₃, p₃, hp₃, hv₃⟩ := htr3 k (mem_univ _) 0 p₂ (!ε) (by simpa [dW, sW] using hp₂)
    obtain ⟨i₄, p₄, hp₄, hv₄⟩ := htr4 k hkx i₃ p₃ (!ε) hp₃
    obtain ⟨i₅, p₅, hp₅, hv₅⟩ := htr5 k hky i₄ p₄ (!ε) hp₄
    obtain ⟨rfl, hp₅'⟩ := sW_get hp₅
    refine ⟨p₅, hp₅', fun t ht => ?_⟩
    have e := (hv₅ t ht).trans ((hv₄ t ht).trans (hv₃ t ht))
    rw [sW_zero] at e
    have h2' := hv₂ t ht
    have h1' := hv₁ t ht
    simp only [dW, sW, update_self, update_of_ne (by decide : (0 : ℕ) ≠ 1)] at e h1'
    exact e.trans (h2'.trans h1')

/-- On a non-orientable surface presented by `ew a (b + 1) c`, there is a homeomorphism reversing
a chosen cuff `i₀ < c` while fixing every other cuff pointwise. -/
theorem exists_homeo_flip_one_cuff {Y : Type uu} [TopologicalSpace Y] [T2Space Y]
    {a b c : ℕ} {f : ℕ × ℂ → Y} (hf : Presents (sW (ew a (b + 1) c)) f) {i₀ : ℕ} (hi₀ : i₀ < c) :
    ∃ h : Y ≃ₜ Y,
      (∀ u ∈ Icc (0 : ℝ) 1, h (holeP a (b + 1) c f i₀ u) = holeP a (b + 1) c f i₀ (1 - u)) ∧
      (∀ i < c, i ≠ i₀ → ∀ u ∈ Icc (0 : ℝ) 1, h (holeP a (b + 1) c f i u) = holeP a (b + 1) c f i u) := by
  let b' := b + 1
  have hL : (List.range' 0 c).Nodup := List.nodup_range'
  have hm : i₀ ∈ List.range' 0 c := by simpa using hi₀
  have hmc : ∀ m' ∈ List.range' 0 c, m' < c := fun m' h => by simpa using h
  -- Bring hole `i₀` to the front of `ew a b' c`.
  have ht0 := trk_hole.{uu} (a := a) (b := b') (c := c) (U := []) hL hm hmc noLab_nil
  simp only [List.nil_append] at ht0
  have hf_rW : Presents (sW (rW a b' c (List.range' 0 c))) f := ew_eq_rW a b' c ▸ hf
  obtain ⟨g₀, hg₀, htr₀⟩ := ht0.sideVal hf_rW
  -- Unpack the first crosscap `x = (2*a, true)`.
  let x : Letter := (2 * a, true)
  let H₀ : List Letter := hB a b' i₀
  let L₁ : List ℕ := (List.range' 0 c).erase i₀
  let Tail : List Letter := cW (2 * a + 1) b ++ hlW (2 * a + b') L₁ ++ eW a b' c
  let Rest : List Letter := Tail ++ hW 0 a
  -- Step 0: slide `H₀` past `hW 0 a` so `H₀` sits right before `[x, x]`.
  have ht_H₀_r : NoLab [rL a b' i₀] (tL a b' i₀).1 := noLab_cons.mpr ⟨by simp [tL, rL], noLab_nil⟩
  have ht_hW : NoLab (hW 0 a) (tL a b' i₀).1 := fun l hl he => by
    have := (hW_labels 0 a l hl).2; simp only [tL] at he; omega
  have ht_xTail : NoLab ([x, x] ++ Tail) (tL a b' i₀).1 := by
    refine noLab_append.mpr ⟨fun l hl he => ?_, noLab_append.mpr ⟨noLab_append.mpr ⟨?_, ?_⟩, ?_⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp only [x, tL] at he <;> omega
    · intro l hl he; have := (cW_labels (2 * a + 1) b l hl).2; simp only [tL, b'] at he; omega
    · exact noLab_hlW fun m hm => by
        have hne : m ≠ i₀ := ((hL.mem_erase_iff).mp hm).1
        simp only [tL]; omega
    · intro l hl he
      simp only [eW, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp only [tL] at he <;> omega
  -- Rotate `H₀` to the end, then use `trk_slide_hole` to swap `hW 0 a` and `[x, x] ++ Tail`?
  -- Even simpler: `trk_rot` turns `H₀ ++ hW 0 a ++ [x, x] ++ Tail` into
  -- `(hW 0 a) ++ ([x, x] ++ Tail) ++ H₀`, then `trk_slide_hole` swaps `hW 0 a` and `[x, x] ++ Tail`
  -- to `([x, x] ++ Tail) ++ (hW 0 a) ++ H₀ = [x] ++ (x :: Tail ++ hW 0 a ++ H₀)`,
  -- then `trk_rot` puts the first `[x]` at the end: `x :: (Tail ++ hW 0 a) ++ H₀ ++ [x]`!
  have hrot0a := trk_rot_sW.{uu} (w := hB a b' i₀ ++ rW a b' c L₁)
    H₀ (hW 0 a ++ ([x, x] ++ Tail))
    (by simp only [H₀, Tail, rW, cW, x, b', List.append_assoc, List.cons_append, List.nil_append]) rfl
  obtain ⟨g0a, hg0a, htr0a⟩ := hrot0a Y g₀ hg₀
  have hsl0 := trk_slide_hole.{uu} (tL a b' i₀) ht_H₀_r ht_hW ht_xTail
  have hsl0_in : hW 0 a ++ ([x, x] ++ Tail) ++ [tL a b' i₀, rL a b' i₀] ++ [linv (tL a b' i₀)] =
      hW 0 a ++ ([x, x] ++ Tail) ++ H₀ := by
    simp [H₀, hB, holB, List.append_assoc]
  have hsl0_out : [x, x] ++ Tail ++ hW 0 a ++ [tL a b' i₀, rL a b' i₀] ++ [linv (tL a b' i₀)] =
      [x] ++ (x :: (Rest ++ H₀)) := by
    simp [H₀, hB, holB, Rest, List.append_assoc]
  rw [hsl0_in, hsl0_out] at hsl0
  obtain ⟨g0b, hg0b, htr0b⟩ := hsl0 Y g0a hg0a
  -- Step 1: rotate `[x]` to the end: `x :: (Rest ++ H₀ ++ [x])`.
  have hrot1 := trk_rot_sW.{uu} (w' := x :: (Rest ++ H₀ ++ [x])) [x] (x :: (Rest ++ H₀)) rfl (by simp [List.append_assoc])
  obtain ⟨g₁, hg₁, htr₁⟩ := hrot1 Y g0b hg0b
  -- Check label disjointness for `presents_ruleB_flip`.
  have hx_H₀ : NoLab H₀ x.1 := by
    intro l hl he
    simp only [H₀, hB, holB, tL, rL, linv, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> simp only [x] at he <;> omega
  have hx_Rest : NoLab Rest x.1 := by
    refine noLab_append.mpr ⟨noLab_append.mpr ⟨noLab_append.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro l hl he; have := (cW_labels (2 * a + 1) b l hl).1; simp only [x] at he; omega
    · exact noLab_hlW fun m _ => by simp only [x, b']; omega
    · intro l hl he
      simp only [eW, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp only [x, b'] at he <;> omega
    · intro l hl he; have := (hW_labels 0 a l hl).2; simp only [x] at he; omega
  -- Step 2: apply `presents_ruleB_flip`!
  obtain ⟨g₂, hg₂, hkeep, hflip⟩ := presents_ruleB_flip hx_Rest hx_H₀ hg₁
  -- Step 3: slide `winv H₀ = [tL, linv rL, linv tL]` to the front using `trk_hole_front`!
  have hwinv_H₀ : winv H₀ = tL a b' i₀ :: [linv (rL a b' i₀)] ++ [linv (tL a b' i₀)] := by
    simp [H₀, hB, holB, winv, linv]
  have ht_r : NoLab [linv (rL a b' i₀)] (tL a b' i₀).1 :=
    noLab_cons.mpr ⟨by simp [tL, rL, linv], noLab_nil⟩
  have ht_Rest : NoLab (Rest ++ [x]) (tL a b' i₀).1 := by
    refine noLab_append.mpr ⟨noLab_append.mpr ⟨noLab_append.mpr ⟨noLab_append.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro l hl he; have := (cW_labels (2 * a + 1) b l hl).2; simp only [tL, b'] at he; omega
    · exact noLab_hlW fun m hm => by
        have hne : m ≠ i₀ := ((hL.mem_erase_iff).mp hm).1
        simp only [tL]; omega
    · intro l hl he
      simp only [eW, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp only [tL] at he <;> omega
    · intro l hl he; have := (hW_labels 0 a l hl).2; simp only [tL] at he; omega
    · intro l hl he; simp only [List.mem_singleton] at hl; rw [hl] at he; simp only [x, tL] at he; omega
  have ht_x : NoLab [x] (tL a b' i₀).1 := noLab_cons.mpr ⟨by simp [x, tL, b']; omega, noLab_nil⟩
  have hfr := trk_hole_front.{uu} (tL a b' i₀) ht_r ht_Rest ht_x
  have hfr_in : (Rest ++ [x]) ++ (tL a b' i₀ :: [linv (rL a b' i₀)] ++ [linv (tL a b' i₀)]) ++ [x] =
      Rest ++ x :: (winv H₀ ++ [x]) := by rw [hwinv_H₀]; simp [List.append_assoc]
  have hfr_out : tL a b' i₀ :: [linv (rL a b' i₀)] ++ linv (tL a b' i₀) :: ((Rest ++ [x]) ++ [x]) =
      winv H₀ ++ Tail ++ (hW 0 a ++ [x, x]) := by rw [hwinv_H₀]; simp [Rest, List.append_assoc]
  rw [hfr_in, hfr_out] at hfr
  obtain ⟨g₃, hg₃, htr₃⟩ := hfr Y g₂ hg₂
  -- Step 4: rotate `winv H₀ ++ Tail ++ (hW 0 a ++ [x, x])` so `hW 0 a ++ [x, x]` goes right after `winv H₀`!
  -- Actually `trk_hole_front` puts `winv H₀` at the front of `Rest ++ [x, x]`, and we want
  -- `winv H₀ ++ hW 0 a ++ [x, x] ++ Tail`! Just use `trk_slide_hole` on `winv H₀`?
  -- Wait: rotate `(winv H₀ ++ Tail)` and `(hW 0 a ++ [x, x])` -> `(hW 0 a ++ [x, x]) ++ winv H₀ ++ Tail`,
  -- then `trk_hole_front` brings `winv H₀` back to the front of `(hW 0 a ++ [x, x]) ++ Tail`!
  have hrot2 := trk_rot_sW.{uu} (winv H₀ ++ Tail) (hW 0 a ++ [x, x]) rfl rfl
  obtain ⟨g₄, hg₄, htr₄⟩ := hrot2 Y g₃ hg₃
  have ht_hx : NoLab (hW 0 a ++ [x, x]) (tL a b' i₀).1 := by
    refine noLab_append.mpr ⟨fun l hl he => ?_, fun l hl he => ?_⟩
    · have := (hW_labels 0 a l hl).2; simp only [tL] at he; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> simp only [x, tL] at he <;> omega
  have ht_Tail : NoLab Tail (tL a b' i₀).1 := (noLab_append.mp (noLab_append.mp ht_Rest).1).1
  have hfr2 := trk_hole_front.{uu} (tL a b' i₀) ht_r ht_hx ht_Tail
  have hfr2_in : (hW 0 a ++ [x, x]) ++ (tL a b' i₀ :: [linv (rL a b' i₀)] ++ [linv (tL a b' i₀)]) ++ Tail =
      (hW 0 a ++ [x, x]) ++ (winv H₀ ++ Tail) := by rw [hwinv_H₀]; simp [List.append_assoc]
  have hfr2_out : tL a b' i₀ :: [linv (rL a b' i₀)] ++ linv (tL a b' i₀) :: ((hW 0 a ++ [x, x]) ++ Tail) =
      winv H₀ ++ rW a b' c L₁ := by
    rw [hwinv_H₀]; simp only [rW, cW, Tail, x, b', List.append_assoc, List.cons_append, List.nil_append]
  rw [hfr2_in, hfr2_out] at hfr2
  obtain ⟨g₅, hg₅, htr₅⟩ := hfr2 Y g₄ hg₄
  -- Step 5: flip the single label `(rL a b' i₀).1`!
  let fl := flipAt (rL a b' i₀).1
  have hg₆ : Presents (sW ((winv H₀ ++ rW a b' c L₁).map (flipL fl))) g₅ := presents_flip hg₅ fl
  have hfl_rW : (rW a b' c L₁).map (flipL fl) = rW a b' c L₁ :=
    map_flipAt_of_noLab (noLab_rW (by simp [rL]; omega) (by simp [rL]; omega) fun m hm => by
      have hne : m ≠ i₀ := ((hL.mem_erase_iff).mp hm).1
      simp only [rL]; omega)
  have hfl_H₀ : (winv H₀).map (flipL fl) = H₀ := by
    have hne1 : (tL a b' i₀).1 ≠ (rL a b' i₀).1 := by simp [tL, rL]
    rw [hwinv_H₀]
    simp [H₀, hB, holB, linv, flipL, fl, flipAt, hne1]
  rw [List.map_append, hfl_H₀, hfl_rW] at hg₆
  -- Now both `g₀` and `g₅` present `sW (hB a b' i₀ ++ rW a b' c L₁)`!
  obtain ⟨h, hh⟩ := presents_homeo (finW_sW _) hg₀ hg₆
  -- Helper: count of `(rL a b' m).1` in `hB a b' i₀ ++ rW a b' c L₁` is 1 for every `m < c`.
  have hcnt : ∀ m < c, cnt (hB a b' i₀ ++ rW a b' c L₁) (rL a b' m).1 = 1 := by
    intro m hm'
    rw [cnt_append]
    by_cases hmi : m = i₀
    · subst hmi
      have hc2 : cnt (rW a b' c L₁) (rL a b' m).1 = 0 :=
        noLab_iff_cnt.mp (noLab_rW (by simp [rL]; omega) (by simp [rL]; omega) fun x hx => by
          have hne : x ≠ m := ((hL.mem_erase_iff).mp hx).1
          simp [rL]; omega)
      rw [hc2, add_zero]; simp [hB, holB, linv, cnt_cons, cnt_nil, tL, rL]
    · have hc1 : cnt (hB a b' i₀) (rL a b' m).1 = 0 := by
        simp only [hB, holB, linv, cnt_cons, cnt_nil, tL, rL]; split_ifs <;> omega
      rw [hc1, zero_add]
      have hc_hlW : ∀ (K : List ℕ), K.Nodup → ∀ n ∈ K, cnt (hlW (2 * a + b') K) (rL a b' n).1 = 1 := by
        intro K hK
        induction K with
        | nil => simp
        | cons y K ih =>
          intro n hn
          obtain ⟨hyK, hKn⟩ := List.nodup_cons.mp hK
          rw [hlW_cons, cnt_append]
          rcases List.mem_cons.mp hn with rfl | hn'
          · have : cnt (hlW (2 * a + b') K) (rL a b' n).1 = 0 :=
              noLab_iff_cnt.mp (noLab_hlW fun z hz => by
                have hne : z ≠ n := fun he => hyK (he ▸ hz)
                simp [rL]; omega)
            rw [this, add_zero]; simp [holB, linv, cnt_cons, cnt_nil, rL]
          · have hne : n ≠ y := fun he => hyK (he ▸ hn')
            have : cnt (holB (2 * a + b' + 2 * y, true) (2 * a + b' + 2 * y + 1, true)) (rL a b' n).1 = 0 := by
              simp only [holB, linv, cnt_cons, cnt_nil, rL]; split_ifs <;> omega
            rw [this, zero_add]; exact ih hKn n hn'
      simp only [rW, cnt_append]
      have h1 : cnt (hW 0 a) (rL a b' m).1 = 0 := noLab_iff_cnt.mp fun l hl he => by
        have := (hW_labels 0 a l hl).2; simp only [rL] at he; omega
      have h2 : cnt (cW (2 * a) b') (rL a b' m).1 = 0 := noLab_iff_cnt.mp fun l hl he => by
        have := (cW_labels (2 * a) b' l hl).2; simp only [rL] at he; omega
      have h3 : cnt (eW a b' c) (rL a b' m).1 = 0 := noLab_iff_cnt.mp fun l hl he => by
        simp only [eW, List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> simp only [rL] at he <;> omega
      rw [h1, h2, h3, zero_add, zero_add, add_zero]
      exact hc_hlW L₁ (hL.erase _) m ((hL.mem_erase_iff).mpr ⟨hmi, by simpa using hm'⟩)
  refine ⟨h, ?_, ?_⟩
  · -- Cuff `i₀`: reversed!
    intro u hu
    have hs0 := htr₀ (rL a b' i₀).1 (by simp [rL, tL]) _ (sideVal_hole hf hi₀)
    obtain ⟨j0, p0, hp0, hv0⟩ := hs0
    obtain ⟨rfl, hp0'⟩ := sW_get hp0
    rw [sW_zero] at hv0
    obtain ⟨j0a, p0a, hp0a, hv0a⟩ := htr0a (rL a b' i₀).1 (mem_univ _) 0 p0 true hp0
    obtain ⟨j0b, p0b, hp0b, hv0b⟩ := htr0b (rL a b' i₀).1 (by simp [rL, tL]) j0a p0a true hp0a
    obtain ⟨j1, p1, hp1, hv1⟩ := htr₁ (rL a b' i₀).1 (mem_univ _) j0b p0b true hp0b
    obtain ⟨rfl, hp1'⟩ := sW_get hp1
    rw [sW_zero] at hv1
    have hno_Rest : NoLab Rest (rL a b' i₀).1 := by
      refine noLab_append.mpr ⟨noLab_append.mpr ⟨noLab_append.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
      · intro l hl he; have := (cW_labels (2 * a + 1) b l hl).2; simp only [rL, b'] at he; omega
      · exact noLab_hlW fun m hm => by
          have hne : m ≠ i₀ := ((hL.mem_erase_iff).mp hm).1
          simp only [rL]; omega
      · intro l hl he
        simp only [eW, List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> simp only [rL] at he <;> omega
      · intro l hl he; have := (hW_labels 0 a l hl).2; simp only [rL] at he; omega
    obtain ⟨p2, hp2, hv2⟩ := hflip (rL a b' i₀).1 (by simp [x, rL]; omega) hno_Rest p1 true hp1'
    obtain ⟨j3, p3, hp3, hv3⟩ := htr₃ (rL a b' i₀).1 (by simp [rL, tL]) 0 p2 false (by rwa [sW_zero])
    obtain ⟨j4, p4, hp4, hv4⟩ := htr₄ (rL a b' i₀).1 (mem_univ _) j3 p3 false hp3
    obtain ⟨j5, p5, hp5, hv5⟩ := htr₅ (rL a b' i₀).1 (by simp [rL, tL]) j4 p4 false hp4
    obtain ⟨rfl, hp5'⟩ := sW_get hp5
    rw [sW_zero] at hv5
    have hval5 : ∀ v ∈ Icc (0 : ℝ) 1,
        g₅ (0, sdPt (winv H₀ ++ rW a b' c L₁).length p5 false v) = holeP a b' c f i₀ v := by
      intro v hv
      have e := (hv5 v hv).trans ((hv4 v hv).trans (hv3 v hv))
      have e0 := (hv1 v hv).trans ((hv0b v hv).trans (hv0a v hv))
      rw [sW_zero] at e e0
      exact e.trans ((hv2 v hv).trans (e0.trans (hv0 v hv)))
    have hside6 := sideVal_flip_rev (c := fl) hp5' hval5 (by simp [fl, flipAt])
    rw [List.map_append, hfl_H₀, hfl_rW] at hside6
    have hv6 := hside6.at_word hp0' (hcnt i₀ hi₀) u hu
    have hmem : (0, sdPt (hB a b' i₀ ++ rW a b' c L₁).length p0 true u) ∈
        Dsk (sW (hB a b' i₀ ++ rW a b' c L₁)) := by
      refine ⟨?_, (norm_per _ _).le⟩
      intro he; simp only [sW_zero] at he; rw [he] at hp0'; simp at hp0'
    dsimp only [H₀, L₁, b'] at hv6 hmem ⊢
    exact (congrArg h (hv0 u hu).symm).trans ((hh _ hmem).trans hv6)
  · -- Cuff `i ≠ i₀`: fixed pointwise!
    intro i hi hne u hu
    have hs0 := htr₀ (rL a b' i).1 (by simp [rL, tL]; omega) _ (sideVal_hole hf hi)
    obtain ⟨j0, p0, hp0, hv0⟩ := hs0
    obtain ⟨rfl, hp0'⟩ := sW_get hp0
    rw [sW_zero] at hv0
    obtain ⟨j0a, p0a, hp0a, hv0a⟩ := htr0a (rL a b' i).1 (mem_univ _) 0 p0 true hp0
    obtain ⟨j0b, p0b, hp0b, hv0b⟩ := htr0b (rL a b' i).1 (by simp [rL, tL]; omega) j0a p0a true hp0a
    obtain ⟨j1, p1, hp1, hv1⟩ := htr₁ (rL a b' i).1 (mem_univ _) j0b p0b true hp0b
    obtain ⟨rfl, hp1'⟩ := sW_get hp1
    rw [sW_zero] at hv1
    have hno_H₀ : NoLab H₀ (rL a b' i).1 := by
      intro l hl he
      simp only [H₀, hB, holB, tL, rL, linv, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl <;> simp only [rL] at he <;> omega
    obtain ⟨p2, hp2, hv2⟩ := hkeep (rL a b' i).1 (by simp [x, rL]; omega) hno_H₀ p1 true hp1'
    obtain ⟨j3, p3, hp3, hv3⟩ := htr₃ (rL a b' i).1 (by simp [rL, tL]; omega) 0 p2 true (by rwa [sW_zero])
    obtain ⟨j4, p4, hp4, hv4⟩ := htr₄ (rL a b' i).1 (mem_univ _) j3 p3 true hp3
    obtain ⟨j5, p5, hp5, hv5⟩ := htr₅ (rL a b' i).1 (by simp [rL, tL]; omega) j4 p4 true hp4
    obtain ⟨rfl, hp5'⟩ := sW_get hp5
    rw [sW_zero] at hv5
    have hside5 : SideVal (sW (winv H₀ ++ rW a b' c L₁)) g₅ (rL a b' i).1 (holeP a b' c f i) := by
      refine ⟨0, p5, by rwa [sW_zero], fun v hv => ?_⟩
      rw [sW_zero]
      have e := (hv5 v hv).trans ((hv4 v hv).trans (hv3 v hv))
      have e0 := (hv1 v hv).trans ((hv0b v hv).trans (hv0a v hv))
      rw [sW_zero] at e e0
      exact e.trans ((hv2 v hv).trans (e0.trans (hv0 v hv)))
    have hside6 := sideVal_flip_same (c := fl) hside5 (by simp [fl, flipAt, rL, hne])
    rw [List.map_append, hfl_H₀, hfl_rW] at hside6
    have hv6 := hside6.at_word hp0' (hcnt i hi) u hu
    have hmem : (0, sdPt (hB a b' i₀ ++ rW a b' c L₁).length p0 true u) ∈
        Dsk (sW (hB a b' i₀ ++ rW a b' c L₁)) := by
      refine ⟨?_, (norm_per _ _).le⟩
      intro he; simp only [sW_zero] at he; rw [he] at hp0'; simp at hp0'
    dsimp only [H₀, L₁, b'] at hv6 hmem ⊢
    exact (congrArg h (hv0 u hu).symm).trans ((hh _ hmem).trans hv6)

/-- On a non-orientable surface presented by `ew a (b + 1) c`, there is a homeomorphism reversing
any prescribed subset of cuffs while fixing all other cuffs pointwise. -/
theorem exists_homeo_flip_cuffs {Y : Type uu} [TopologicalSpace Y] [T2Space Y]
    {a b c : ℕ} {f : ℕ × ℂ → Y} (hf : Presents (sW (ew a (b + 1) c)) f) (flip : Fin c → Bool) :
    ∃ h : Y ≃ₜ Y, ∀ i : Fin c, ∀ u ∈ Icc (0 : ℝ) 1,
      h (holeP a (b + 1) c f i.1 u) =
        holeP a (b + 1) c f i.1 (if flip i then 1 - u else u) := by
  classical
  have key : ∀ S : Finset (Fin c), ∃ h : Y ≃ₜ Y, ∀ i : Fin c, ∀ u ∈ Icc (0 : ℝ) 1,
      h (holeP a (b + 1) c f i.1 u) =
        holeP a (b + 1) c f i.1 (if i ∈ S then 1 - u else u) := by
    intro S
    induction S using Finset.induction with
    | empty =>
      exact ⟨Homeomorph.refl Y, fun _ _ _ => by simp⟩
    | @insert i₀ S hi₀ ih =>
      obtain ⟨h₁, hh₁⟩ := ih
      obtain ⟨h₀, hh₀_rev, hh₀_fix⟩ := exists_homeo_flip_one_cuff hf i₀.isLt
      refine ⟨h₁.trans h₀, fun i u hu => ?_⟩
      simp only [Homeomorph.trans_apply]
      rw [hh₁ i u hu]
      by_cases hi : i = i₀
      · subst hi
        simp only [hi₀, ↓reduceIte, Finset.mem_insert_self]
        exact hh₀_rev u hu
      · have hne : i.1 ≠ i₀.1 := fun h => hi (Fin.ext h)
        simp only [Finset.mem_insert, hi, false_or]
        by_cases hS : i ∈ S
        · simp only [hS, ↓reduceIte]
          exact hh₀_fix i.1 i.isLt hne (1 - u) (rev_mem hu)
        · simp only [hS, ↓reduceIte]
          exact hh₀_fix i.1 i.isLt hne u hu
  obtain ⟨h, hh⟩ := key (Finset.univ.filter fun i : Fin c => flip i = true)
  refine ⟨h, fun i u hu => ?_⟩
  have := hh i u hu
  simpa using this

end GraphMinor.Surface
