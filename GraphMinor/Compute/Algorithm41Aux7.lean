module

public import GraphMinor.Compute.Algorithm41Aux6

/-!
# Table Combination Step for GM XIII Algorithm (4.1)

This file implements and verifies the constant-time Word RAM table-combination step
(`combineStepProg`, `combineStepProg_exec`, `combineStepProg_exec_table`) for the bottom-up dynamic
program of Algorithm (4.1) from Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths
Problem*, Section 4, pages 75–76:

1. **Canonical boundary-mask decoding (`canonMaskCardU`, `canonMaskSubA`, `canonMaskSubB`,
   `canonMaskSubZ`) and canonical combination recipes (`combineRecipesOfTabs`,
   `canonCombineRecipes`):**
   Recovers the canonical subset masks of `ZA, ZB, Z' ⊆ ZA ∪ ZB` from `mcode = encBoundaryMask ZA ZB Z'`
   and proves that `combineRecipesOfTabs` agrees with `rawCombineTables` and `combinePieceTables`.
2. **Arena fold-step and slot-fill gadgets (`combineFoldStepCmd`, `tabsSlotProg`,
   `tabsCombineBodyProg`, `copyFixedArrMinProg`):**
   For each slot `pos < S_tab δ ξ ω`, folds `2 * V_max δ ξ ω` union nodes into `ArenaV` and `ArenaE`
   to form the vertex and edge subsets of the combined model entry and copies the combined edge map.
3. **Full combination step (`combineStepProg`, `combineStepProg_exec`,
   `combineStepProg_exec_table`):**
   Chains `mergeBoundaryProg`, the 3-level `branchOnBound` lookup on `(r_tidA, r_tidB, r_13)`, and
   array copy-back from `a_out_*` to `a_acc_*`, proving that `bufA` holds a `ValidPieceBuffer` for
   `(combinePieceTables ... T_A T_B).toRawList`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Canonical Boundary Mask Decoding and Canonical Combine Recipes -/

theorem card_finPrefix {N m : ℕ} (hm : m ≤ N) :
    (finPrefix N m).card = m := by
  induction m with
  | zero => simp [finPrefix_zero]
  | succ m ih =>
    have hm_lt : m < N := by omega
    rw [finPrefix_succ hm_lt, Finset.card_insert_of_notMem, ih (by omega)]
    simp [finPrefix]

/-- Decoded union boundary cardinality `|ZA ∪ ZB|` from `mcode`: the number of indices
`k < Q_max ξ ω` whose base-8 digit has bit 0 or bit 1 set. -/
def canonMaskCardU (ξ ω mcode : ℕ) : ℕ :=
  (Finset.univ.filter (fun k : Fin (Q_max ξ ω) =>
    mcodeDigit mcode k.1 % 2 = 1 ∨ (mcodeDigit mcode k.1 / 2) % 2 = 1)).card

/-- Decoded subset of `Fin (canonMaskCardU ξ ω mcode)` corresponding to `ZA`. -/
def canonMaskSubA (ξ ω mcode : ℕ) : Finset (Fin (canonMaskCardU ξ ω mcode)) :=
  Finset.univ.filter (fun k : Fin (canonMaskCardU ξ ω mcode) =>
    mcodeDigit mcode k.1 % 2 = 1)

/-- Decoded subset of `Fin (canonMaskCardU ξ ω mcode)` corresponding to `ZB`. -/
def canonMaskSubB (ξ ω mcode : ℕ) : Finset (Fin (canonMaskCardU ξ ω mcode)) :=
  Finset.univ.filter (fun k : Fin (canonMaskCardU ξ ω mcode) =>
    (mcodeDigit mcode k.1 / 2) % 2 = 1)

/-- Decoded subset of `Fin (canonMaskCardU ξ ω mcode)` corresponding to `Z'`. -/
def canonMaskSubZ (ξ ω mcode : ℕ) : Finset (Fin (canonMaskCardU ξ ω mcode)) :=
  Finset.univ.filter (fun k : Fin (canonMaskCardU ξ ω mcode) =>
    (mcodeDigit mcode k.1 / 4) % 2 = 1)

theorem canonMaskCardU_le_Q_max (ξ ω mcode : ℕ) :
    canonMaskCardU ξ ω mcode ≤ Q_max ξ ω := by
  unfold canonMaskCardU
  calc (Finset.univ.filter _).card
      ≤ (Finset.univ : Finset (Fin (Q_max ξ ω))).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = Q_max ξ ω := Finset.card_fin _

theorem card_canonMaskSubZ_le_Q_max (ξ ω mcode : ℕ) :
    (canonMaskSubZ ξ ω mcode).card ≤ Q_max ξ ω := by
  calc (canonMaskSubZ ξ ω mcode).card
      ≤ (Finset.univ : Finset (Fin (canonMaskCardU ξ ω mcode))).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = canonMaskCardU ξ ω mcode := Finset.card_fin _
    _ ≤ Q_max ξ ω := canonMaskCardU_le_Q_max ξ ω mcode

theorem mcodeDigit_encBoundaryMask_of_lt {n : ℕ} (ZA ZB Z' : Finset (Fin n))
    {k : ℕ} (hk : k < (ZA ∪ ZB).card) :
    mcodeDigit (encBoundaryMask ZA ZB Z') k = boundaryMaskDigit ZA ZB Z' ⟨k, hk⟩ := by
  unfold encBoundaryMask
  let ds := (List.finRange (ZA ∪ ZB).card).map (boundaryMaskDigit ZA ZB Z')
  have hds : ∀ d ∈ ds, d < 8 := by
    intro d hd
    rcases List.mem_map.mp hd with ⟨idx, _, rfl⟩
    exact (boundaryMaskDigit_pos_and_lt ZA ZB Z' idx).2
  rw [mcodeDigit_packBase ds hds k]
  have hk_len : k < ds.length := by simp [ds, hk]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_len, Option.getD_some]
  simp [ds]

theorem mcodeDigit_encBoundaryMask_of_ge {n : ℕ} (ZA ZB Z' : Finset (Fin n))
    {k : ℕ} (hk : (ZA ∪ ZB).card ≤ k) :
    mcodeDigit (encBoundaryMask ZA ZB Z') k = 0 := by
  unfold encBoundaryMask
  let ds := (List.finRange (ZA ∪ ZB).card).map (boundaryMaskDigit ZA ZB Z')
  have hds : ∀ d ∈ ds, d < 8 := by
    intro d hd
    rcases List.mem_map.mp hd with ⟨idx, _, rfl⟩
    exact (boundaryMaskDigit_pos_and_lt ZA ZB Z' idx).2
  rw [mcodeDigit_packBase ds hds k]
  have hk_len : ds.length ≤ k := by simp [ds, hk]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk_len, Option.getD_none]

theorem boundaryMaskDigit_bits {n : ℕ} (ZA ZB Z' : Finset (Fin n))
    (k : Fin (ZA ∪ ZB).card) :
    (boundaryMaskDigit ZA ZB Z' k % 2 = 1 ↔ finsetRootFn (ZA ∪ ZB) k ∈ ZA) ∧
    ((boundaryMaskDigit ZA ZB Z' k / 2) % 2 = 1 ↔ finsetRootFn (ZA ∪ ZB) k ∈ ZB) ∧
    ((boundaryMaskDigit ZA ZB Z' k / 4) % 2 = 1 ↔ finsetRootFn (ZA ∪ ZB) k ∈ Z') := by
  unfold boundaryMaskDigit
  dsimp only
  by_cases hA : finsetRootFn (ZA ∪ ZB) k ∈ ZA <;>
    by_cases hB : finsetRootFn (ZA ∪ ZB) k ∈ ZB <;>
    by_cases hZ : finsetRootFn (ZA ∪ ZB) k ∈ Z' <;>
    simp [hA, hB, hZ]

theorem canonMaskCardU_encBoundaryMask {n ξ ω : ℕ} (ZA ZB Z' : Finset (Fin n))
    (hq : (ZA ∪ ZB).card ≤ Q_max ξ ω) :
    canonMaskCardU ξ ω (encBoundaryMask ZA ZB Z') = (ZA ∪ ZB).card := by
  unfold canonMaskCardU
  have hfilt :
      Finset.univ.filter (fun k : Fin (Q_max ξ ω) =>
        mcodeDigit (encBoundaryMask ZA ZB Z') k.1 % 2 = 1 ∨
        (mcodeDigit (encBoundaryMask ZA ZB Z') k.1 / 2) % 2 = 1) =
      finPrefix (Q_max ξ ω) (ZA ∪ ZB).card := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, finPrefix]
    by_cases hk : k.1 < (ZA ∪ ZB).card
    · rw [mcodeDigit_encBoundaryMask_of_lt ZA ZB Z' hk]
      rcases boundaryMaskDigit_bits ZA ZB Z' ⟨k.1, hk⟩ with ⟨hA, hB, _⟩
      rw [hA, hB]
      simp [hk, Finset.mem_union.mp (finsetRootFn_mem (ZA ∪ ZB) ⟨k.1, hk⟩)]
    · rw [mcodeDigit_encBoundaryMask_of_ge ZA ZB Z' (not_lt.mp hk)]
      simp [hk]
  rw [hfilt, card_finPrefix hq]

theorem mem_canonMaskSub_encBoundaryMask {n ξ ω : ℕ} (ZA ZB Z' : Finset (Fin n))
    (hq : (ZA ∪ ZB).card ≤ Q_max ξ ω) :
    let mcode := encBoundaryMask ZA ZB Z'
    let hU := canonMaskCardU_encBoundaryMask ZA ZB Z' hq
    (∀ k : Fin (canonMaskCardU ξ ω mcode),
      k ∈ canonMaskSubA ξ ω mcode ↔
        (⟨k.1, hU ▸ k.2⟩ : Fin (ZA ∪ ZB).card) ∈ subMaskFinset (ZA ∪ ZB) ZA) ∧
    (∀ k : Fin (canonMaskCardU ξ ω mcode),
      k ∈ canonMaskSubB ξ ω mcode ↔
        (⟨k.1, hU ▸ k.2⟩ : Fin (ZA ∪ ZB).card) ∈ subMaskFinset (ZA ∪ ZB) ZB) ∧
    (∀ k : Fin (canonMaskCardU ξ ω mcode),
      k ∈ canonMaskSubZ ξ ω mcode ↔
        (⟨k.1, hU ▸ k.2⟩ : Fin (ZA ∪ ZB).card) ∈ subMaskFinset (ZA ∪ ZB) Z') := by
  intro mcode hU
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_⟩ <;> {
    have hk : k.1 < (ZA ∪ ZB).card := hU ▸ k.2
    simp only [canonMaskSubA, canonMaskSubB, canonMaskSubZ, subMaskFinset,
      Finset.mem_filter, Finset.mem_univ, true_and, mcode,
      mcodeDigit_encBoundaryMask_of_lt ZA ZB Z' hk]
    rcases boundaryMaskDigit_bits ZA ZB Z' ⟨k.1, hk⟩ with ⟨hA, hB, hZ⟩
    first | exact hA | exact hB | exact hZ
  }

/-- Congruence principle for any function `F` returning a non-dependent type `α` from two abstract
tables and three index subsets `S_A, S_B, S_Z ⊆ Fin q_U`. -/
theorem tabsFn_congr {α : Type*}
    (F : AbstractTable → AbstractTable → ∀ (q_U : ℕ),
      Finset (Fin q_U) → Finset (Fin q_U) → Finset (Fin q_U) → α)
    {tab_A₁ tab_A₂ tab_B₁ tab_B₂ : AbstractTable}
    {q_U₁ q_U₂ : ℕ}
    {S_A₁ : Finset (Fin q_U₁)} {S_A₂ : Finset (Fin q_U₂)}
    {S_B₁ : Finset (Fin q_U₁)} {S_B₂ : Finset (Fin q_U₂)}
    {S_Z₁ : Finset (Fin q_U₁)} {S_Z₂ : Finset (Fin q_U₂)}
    (htA : tab_A₁ = tab_A₂) (htB : tab_B₁ = tab_B₂) (hq : q_U₁ = q_U₂)
    (hSA : ∀ k : Fin q_U₁, k ∈ S_A₁ ↔ (⟨k.1, hq ▸ k.2⟩ : Fin q_U₂) ∈ S_A₂)
    (hSB : ∀ k : Fin q_U₁, k ∈ S_B₁ ↔ (⟨k.1, hq ▸ k.2⟩ : Fin q_U₂) ∈ S_B₂)
    (hSZ : ∀ k : Fin q_U₁, k ∈ S_Z₁ ↔ (⟨k.1, hq ▸ k.2⟩ : Fin q_U₂) ∈ S_Z₂) :
    F tab_A₁ tab_B₁ q_U₁ S_A₁ S_B₁ S_Z₁ = F tab_A₂ tab_B₂ q_U₂ S_A₂ S_B₂ S_Z₂ := by
  subst htA htB hq
  have hA : S_A₁ = S_A₂ := Finset.ext hSA
  have hB : S_B₁ = S_B₂ := Finset.ext hSB
  have hZ : S_Z₁ = S_Z₂ := Finset.ext hSZ
  subst hA hB hZ
  rfl

/-- Purely combinatorial recipe list from `(tab_A, tab_B, q_U, S_A, S_B, S_Z)`. -/
def combineRecipesOfTabs (δ : ℕ) (tab_A tab_B : AbstractTable) (q_U : ℕ)
    (S_A S_B S_Z : Finset (Fin q_U)) :
    List (CombineEntryRecipe tab_A.2 tab_B.2 S_Z.card) :=
  if h : S_A.card = tab_A.1 ∧ S_B.card = tab_B.1 ∧ ∀ k : Fin q_U, k ∈ S_A ∪ S_B then
    let α_A : Fin tab_A.1 → Fin q_U := fun i => finsetRootFn S_A ⟨i.1, h.1.symm ▸ i.2⟩
    let α_B : Fin tab_B.1 → Fin q_U := fun j => finsetRootFn S_B ⟨j.1, h.2.1.symm ▸ j.2⟩
    let β : Fin S_Z.card → Fin q_U := finsetRootFn S_Z
    have hcov : ∀ k : Fin q_U, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k) := by
      intro k
      rcases Finset.mem_union.mp (h.2.2 k) with hkA | hkB
      · rcases exists_finsetRootFn_eq hkA with ⟨i₀, hi₀⟩
        exact Or.inl ⟨⟨i₀.1, h.1 ▸ i₀.2⟩, hi₀⟩
      · rcases exists_finsetRootFn_eq hkB with ⟨j₀, hj₀⟩
        exact Or.inr ⟨⟨j₀.1, h.2.1 ▸ j₀.2⟩, hj₀⟩
    abstractCombineRecipes δ α_A α_B hcov β tab_A.2 tab_B.2
  else
    []

theorem dedupByIso_sub {q : ℕ} {α : Type*} (projH : α → ComputeRootedDigraph q) :
    ∀ (xs : List α) {x : α}, x ∈ dedupByIso projH xs → x ∈ xs
  | [], _, hx => by contradiction
  | a :: xs, x, hx => by
    unfold dedupByIso at hx
    split_ifs at hx with h
    · exact List.mem_cons_of_mem a (dedupByIso_sub projH xs hx)
    · rcases List.mem_cons.mp hx with rfl | hmem
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (dedupByIso_sub projH xs hmem)

theorem dedupByIso_pairwise {q : ℕ} {α : Type*} (projH : α → ComputeRootedDigraph q) :
    ∀ (xs : List α),
      ((dedupByIso projH xs).map (fun x => encRootedDigraph (projH x))).Pairwise
        (fun c₁ c₂ => ¬ IsIsoRootedDigraphCode q c₁ c₂)
  | [] => List.Pairwise.nil
  | x :: xs => by
    unfold dedupByIso
    split_ifs with h
    · exact dedupByIso_pairwise projH xs
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨fun c' hc' hiso => h ?_, dedupByIso_pairwise projH xs⟩
      rcases List.mem_map.mp hc' with ⟨x', hx', rfl⟩
      rw [isIsoRootedDigraphCode_enc_iff] at hiso
      rw [List.any_eq_true]
      exact ⟨x', hx', decide_eq_true hiso⟩

theorem length_dedupByIso_le_allDetailLeCodes {q δ : ℕ} {α : Type*}
    (projH : α → ComputeRootedDigraph q) (xs : List α)
    (hdet : ∀ x ∈ dedupByIso projH xs, (projH x).HasDetailLe δ) :
    (dedupByIso projH xs).length ≤ (allDetailLeCodes q δ).length := by
  let F : FolioSetRep q δ :=
    { codes := (dedupByIso projH xs).map (fun x => encRootedDigraph (projH x))
      all_detail := fun c hc => by
        rcases List.mem_map.mp hc with ⟨x, hx, rfl⟩
        exact isDetailLeCode_encRootedDigraph (hdet x hx)
      pairwise_nonIso := dedupByIso_pairwise projH xs }
  simpa [F] using length_codes_le_allDetailLeCodes F

theorem hasDetailLe_of_mem_abstractCombineRecipes {q q_A q_B q' δ : ℕ}
    (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (β : Fin q' → Fin q)
    (Hs_A : List (ComputeRootedDigraph q_A))
    (Hs_B : List (ComputeRootedDigraph q_B))
    {r : CombineEntryRecipe Hs_A Hs_B q'}
    (hr : r ∈ abstractCombineRecipes δ α_A α_B hcov β Hs_A Hs_B) :
    r.H.HasDetailLe δ := by
  unfold abstractCombineRecipes at hr
  have hmem := dedupByIso_sub (fun x : CombineEntryRecipe Hs_A Hs_B q' => x.H) _ hr
  rw [List.mem_flatMap] at hmem
  rcases hmem with ⟨idx_A, _, hmemB⟩
  rw [List.mem_flatMap] at hmemB
  rcases hmemB with ⟨idx_B, _, hmemP⟩
  unfold abstractCombineEntryPair abstractCombineEntryPairAux at hmemP
  dsimp only at hmemP
  rw [List.mem_filterMap] at hmemP
  rcases hmemP with ⟨U, _, hopt⟩
  split_ifs at hopt with hU hdet
  rw [← Option.some.inj hopt]
  exact hdet

theorem length_abstractCombineRecipes_le {q q_A q_B q' δ : ℕ}
    (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (β : Fin q' → Fin q)
    (Hs_A : List (ComputeRootedDigraph q_A))
    (Hs_B : List (ComputeRootedDigraph q_B)) :
    (abstractCombineRecipes δ α_A α_B hcov β Hs_A Hs_B).length ≤
      (allDetailLeCodes q' δ).length := by
  have hdet := fun (r : CombineEntryRecipe Hs_A Hs_B q')
    (hr : r ∈ abstractCombineRecipes δ α_A α_B hcov β Hs_A Hs_B) =>
    hasDetailLe_of_mem_abstractCombineRecipes α_A α_B hcov β Hs_A Hs_B hr
  unfold abstractCombineRecipes at hdet ⊢
  exact length_dedupByIso_le_allDetailLeCodes
    (fun x : CombineEntryRecipe Hs_A Hs_B q' => x.H) _ hdet

theorem hasDetailLe_of_mem_combineRecipesOfTabs {δ : ℕ}
    (tab_A tab_B : AbstractTable) (q_U : ℕ) (S_A S_B S_Z : Finset (Fin q_U))
    {r : CombineEntryRecipe tab_A.2 tab_B.2 S_Z.card}
    (hr : r ∈ combineRecipesOfTabs δ tab_A tab_B q_U S_A S_B S_Z) :
    r.H.HasDetailLe δ := by
  unfold combineRecipesOfTabs at hr
  split_ifs at hr with h
  · exact hasDetailLe_of_mem_abstractCombineRecipes _ _ _ _ _ _ hr
  · simp at hr

theorem length_combineRecipesOfTabs_le {δ : ℕ}
    (tab_A tab_B : AbstractTable) (q_U : ℕ) (S_A S_B S_Z : Finset (Fin q_U)) :
    (combineRecipesOfTabs δ tab_A tab_B q_U S_A S_B S_Z).length ≤
      (allDetailLeCodes S_Z.card δ).length := by
  unfold combineRecipesOfTabs
  split_ifs with h
  · exact length_abstractCombineRecipes_le _ _ _ _ _ _
  · simp

theorem rawCombineTables_cast_q' {q q_A q_B q₁' q₂' δ : ℕ} {G : ComputeDigraph}
    (α_A₁ α_A₂ : Fin q_A → Fin q) (hA : α_A₁ = α_A₂)
    (α_B₁ α_B₂ : Fin q_B → Fin q) (hB : α_B₁ = α_B₂)
    (hcov₁ : ∀ k : Fin q, (∃ i_A, α_A₁ i_A = k) ∨ (∃ i_B, α_B₁ i_B = k))
    (hcov₂ : ∀ k : Fin q, (∃ i_A, α_A₂ i_A = k) ∨ (∃ i_B, α_B₂ i_B = k))
    (hq' : q₁' = q₂')
    (β₁ : Fin q₁' → Fin q) (β₂ : Fin q₂' → Fin q)
    (hβ : ∀ i : Fin q₂', β₁ ⟨i.1, hq'.symm ▸ i.2⟩ = β₂ i)
    (es_A : List (RawCertEntry G q_A)) (es_B : List (RawCertEntry G q_B)) :
    hq' ▸ rawCombineTables δ α_A₁ α_B₁ hcov₁ β₁ es_A es_B =
      rawCombineTables δ α_A₂ α_B₂ hcov₂ β₂ es_A es_B := by
  subst hq' hA hB
  have hβ_eq : β₁ = β₂ := funext hβ
  subst hβ_eq
  rfl

/-- Evaluating `combineRecipesOfTabs` on `(⟨ZA.card, es_A.map (·.H)⟩, ⟨ZB.card, es_B.map (·.H)⟩,
(ZA ∪ ZB).card, subMaskFinset (ZA ∪ ZB) ZA, subMaskFinset (ZA ∪ ZB) ZB,
subMaskFinset (ZA ∪ ZB) Z')` produces `rawCombineTables` along `finsetSubIdx`. -/
theorem map_eval_combineRecipesOfTabs_subMask {δ : ℕ} {G : ComputeDigraph}
    {ZA ZB Z' : Finset (Fin G.numVerts)} (hZ' : Z' ⊆ ZA ∪ ZB)
    (es_A : List (RawCertEntry G ZA.card))
    (es_B : List (RawCertEntry G ZB.card)) :
    let U := ZA ∪ ZB
    let S_A := subMaskFinset U ZA
    let S_B := subMaskFinset U ZB
    let S_Z := subMaskFinset U Z'
    let tab_A : AbstractTable := ⟨ZA.card, es_A.map (·.H)⟩
    let tab_B : AbstractTable := ⟨ZB.card, es_B.map (·.H)⟩
    let rs := combineRecipesOfTabs δ tab_A tab_B U.card S_A S_B S_Z
    let hSZ : S_Z.card = Z'.card := card_subMaskFinset hZ'
    let α_A := finsetSubIdx (Finset.subset_union_left : ZA ⊆ ZA ∪ ZB)
    let α_B := finsetSubIdx (Finset.subset_union_right : ZB ⊆ ZA ∪ ZB)
    let β := finsetSubIdx hZ'
    have hcov : ∀ k : Fin (ZA ∪ ZB).card, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k) := by
      intro k
      rcases Finset.mem_union.mp (finsetRootFn_mem (ZA ∪ ZB) k) with hkA | hkB
      · rcases exists_finsetRootFn_eq hkA with ⟨i_A, hi_A⟩
        exact Or.inl ⟨i_A, finsetRootFn_injective (ZA ∪ ZB) (by simpa [α_A] using hi_A)⟩
      · rcases exists_finsetRootFn_eq hkB with ⟨i_B, hi_B⟩
        exact Or.inr ⟨i_B, finsetRootFn_injective (ZA ∪ ZB) (by simpa [α_B] using hi_B)⟩
    hSZ ▸ (rs.map (fun r => r.eval es_A es_B rfl rfl)) =
      rawCombineTables δ α_A α_B hcov β es_A es_B := by
  intro U S_A S_B S_Z tab_A tab_B rs hSZ α_A α_B β hcov
  have hcond : S_A.card = tab_A.1 ∧ S_B.card = tab_B.1 ∧ ∀ k : Fin U.card, k ∈ S_A ∪ S_B := by
    refine ⟨card_subMaskFinset Finset.subset_union_left,
      card_subMaskFinset Finset.subset_union_right, fun k => ?_⟩
    rw [Finset.mem_union]
    simp only [S_A, S_B, subMaskFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.mem_union.mp (finsetRootFn_mem U k)
  have hrs_eq : rs = abstractCombineRecipes δ
      (fun i => finsetRootFn S_A ⟨i.1, hcond.1.symm ▸ i.2⟩)
      (fun j => finsetRootFn S_B ⟨j.1, hcond.2.1.symm ▸ j.2⟩)
      (by
        intro k
        rcases Finset.mem_union.mp (hcond.2.2 k) with hkA | hkB
        · rcases exists_finsetRootFn_eq hkA with ⟨i₀, hi₀⟩
          exact Or.inl ⟨⟨i₀.1, hcond.1 ▸ i₀.2⟩, hi₀⟩
        · rcases exists_finsetRootFn_eq hkB with ⟨j₀, hj₀⟩
          exact Or.inr ⟨⟨j₀.1, hcond.2.1 ▸ j₀.2⟩, hj₀⟩)
      (finsetRootFn S_Z) tab_A.2 tab_B.2 := by
    dsimp only [rs, combineRecipesOfTabs]
    split_ifs
    rfl
  rw [hrs_eq, map_eval_abstractCombineRecipes]
  refine rawCombineTables_cast_q' _ α_A ?_ _ α_B ?_ _ hcov hSZ (finsetRootFn S_Z) β ?_ es_A es_B
  · funext i
    exact (finsetSubIdx_eq_finsetRootFn_subMaskFinset Finset.subset_union_left i).symm
  · funext j
    exact (finsetSubIdx_eq_finsetRootFn_subMaskFinset Finset.subset_union_right j).symm
  · intro l
    exact (finsetSubIdx_eq_finsetRootFn_subMaskFinset hZ' l).symm

/-! ### Section 2: Word RAM Fold-Step, Slot-Fill, and Array-Copy Gadgets -/

theorem eval_readMin_of_getD {w : ℕ} {s : State} {a : Arr} {e_idx e_cap : Expr} {idx cap : ℕ}
    (hidx : e_idx.eval w s = some idx) (hcap : e_cap.eval w s = some cap)
    (hlen : idx < (s.arrs a).length) :
    (Expr.readMin a e_idx e_cap).eval w s = some (Nat.min ((s.arrs a).getD idx 0) cap) := by
  have hcap_w : cap < 2 ^ w := Expr.eval_lt hcap
  have hmin_w : Nat.min ((s.arrs a)[idx]'hlen) cap < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.min_le_right _ _) hcap_w
  have hget : (s.arrs a)[idx]'hlen = (s.arrs a).getD idx 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
  simp only [Expr.eval, hidx, hcap, hlen, ↓reduceDIte]
  rw [checkWord_of_lt hmin_w, hget]

theorem eval_readMin_eq_of_le {w : ℕ} {s : State} {a : Arr} {e_idx e_cap : Expr} {idx cap val : ℕ}
    (hidx : e_idx.eval w s = some idx) (hcap : e_cap.eval w s = some cap)
    (hlen : idx < (s.arrs a).length) (hget : (s.arrs a).getD idx 0 = val) (hle : val ≤ cap) :
    (Expr.readMin a e_idx e_cap).eval w s = some val := by
  rw [eval_readMin_of_getD hidx hcap hlen, hget]
  simp [hle]

/-- Copy `K` words from `a_src[0..K)` to `a_dst[0..K)` capped at `s.regs r_cap`. -/
def copyFixedArrMinProg (K : ℕ) (a_src a_dst : Arr) (r_cap : Reg) : Cmd :=
  seqRange K (fun i =>
    .write a_dst (.const i) (.readMin a_src (.const i) (.reg r_cap)))

theorem copyFixedArrMinProg_exec {w K cap : ℕ} {a_src a_dst : Arr} {r_cap : Reg} {s₀ : State}
    (hne : a_src ≠ a_dst) (hK_w : K < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (hrcap : s₀.regs r_cap = cap)
    (hsrc_len : (s₀.arrs a_src).length = K)
    (hdst_len : (s₀.arrs a_dst).length = K) :
    ∃ s' t,
      Exec w (copyFixedArrMinProg K a_src a_dst r_cap) s₀ s' t ∧
      t ≤ 1 + 6 * K ∧
      (s'.arrs a_dst).length = K ∧
      (∀ i < K, (s'.arrs a_dst).getD i 0 = Nat.min ((s₀.arrs a_src).getD i 0) cap) ∧
      (∀ a ≠ a_dst, s'.arrs a = s₀.arrs a) ∧
      (∀ r, s'.regs r = s₀.regs r) := by
  let P : ℕ → State → Prop := fun k s =>
    (s.arrs a_dst).length = K ∧
    (∀ i < k, (s.arrs a_dst).getD i 0 = Nat.min ((s₀.arrs a_src).getD i 0) cap) ∧
    (∀ a ≠ a_dst, s.arrs a = s₀.arrs a) ∧
    (∀ r, s.regs r = s₀.regs r)
  have h0 : P 0 s₀ := ⟨hdst_len, fun _ h => by omega, fun _ _ => rfl, fun _ => rfl⟩
  rcases Exec.seqRange (w := w) (K := K) (c := 6) P h0 (fun k hk s hs => by
    rcases hs with ⟨hlen_d, hprev, harr, hreg⟩
    have hk_w : k < 2 ^ w := by omega
    have hsrc_s : s.arrs a_src = s₀.arrs a_src := harr a_src hne
    have hk_src : k < (s.arrs a_src).length := by rw [hsrc_s, hsrc_len]; exact hk
    have hk_dst : k < (s.arrs a_dst).length := by rw [hlen_d]; exact hk
    have hidx_eval : (Expr.const k).eval w s = some k := by simp [Expr.eval, checkWord, hk_w]
    have hcap_eval : (Expr.reg r_cap).eval w s = some cap := by
      simp [Expr.eval, checkWord, hreg r_cap, hrcap, hcap_w]
    have hread_eval := eval_readMin_of_getD hidx_eval hcap_eval hk_src
    rw [hsrc_s] at hread_eval
    let val := Nat.min ((s₀.arrs a_src).getD k 0) cap
    let s₁ := s.writeArr a_dst k val
    have hex_w : Exec w (.write a_dst (.const k) (.readMin a_src (.const k) (.reg r_cap))) s s₁ 6 :=
      .write hidx_eval hread_eval hk_dst
    refine ⟨s₁, 6, hex_w, le_refl 6, by simp [s₁, hlen_d], fun i hi => ?_,
      fun a ha => by simp [s₁, State.writeArr_arrs_ne _ _ _ ha, harr a ha],
      fun r => by simp [s₁, hreg r]⟩
    by_cases hik : i = k
    · subst hik
      simp only [s₁, State.writeArr_arrs_self]
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hk_dst, Option.getD_some]
    · simp only [s₁, State.writeArr_arrs_self]
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hik),
          ← List.getD_eq_getElem?_getD]
      exact hprev i (by omega)) with
    ⟨s', t, hex, ht, hP⟩
  exact ⟨s', t, hex, ht, hP.1, hP.2.1, hP.2.2.1, hP.2.2.2⟩

/-- Single union-fold step pushing `(kd = 2, v1 = r_10, v2 = e_vv)` into `ArenaV` and
`(kd = 2, v1 = r_11, v2 = e_ve)` into `ArenaE`, updating `r_10` and `r_11` to the new node indices. -/
def combineFoldStepCmd (e_vv e_ve : Expr) : Cmd :=
  .seq (.assign 14 e_vv)
  (.seq (.assign 15 e_ve)
  (.seq (.assign 16 (.reg r_kv))
  (.seq (.assign 17 (.reg r_ke))
  (.seq (pushArenaNodeProg a_vkd a_vv1 a_vv2 r_kv (.const 2) (.reg 10) (.reg 14))
  (.seq (pushArenaNodeProg a_ekd a_ev1 a_ev2 r_ke (.const 2) (.reg 11) (.reg 15))
  (.seq (.assign 10 (.reg 16))
        (.assign 11 (.reg 17))))))))

theorem combineFoldStepCmd_exec {w n m kv ke p_vv p_ve q_vv q_ve : ℕ}
    {SV_acc SV_add : Finset (Fin n)} {SE_acc SE_add : Finset (Fin m)}
    {e_vv e_ve : Expr} {s : State}
    (hw2 : 2 < 2 ^ w) (hkv1_w : kv + 1 < 2 ^ w) (hke1_w : ke + 1 < 2 ^ w)
    (hwfV : ArenaWF n kv (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2))
    (hwfE : ArenaWF m ke (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2))
    (hkv_cap : kv + 1 ≤ (s.arrs a_vkd).length)
    (hke_cap : ke + 1 ≤ (s.arrs a_ekd).length)
    (hr_kv : s.regs r_kv = kv) (hr_ke : s.regs r_ke = ke)
    (hr10 : s.regs 10 = p_vv) (hr11 : s.regs 11 = p_ve)
    (hp_vv : p_vv < kv) (hp_ve : p_ve < ke)
    (hev_accV : evalArena n (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p_vv = SV_acc)
    (hev_accE : evalArena m (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p_ve = SE_acc)
    (he_vv : e_vv.eval w s = some q_vv) (hcost_vv : e_vv.cost ≤ 2)
    (hq_vv : q_vv < kv)
    (hev_addV : evalArena n (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) q_vv = SV_add)
    (he_ve : e_ve.eval w (s.setReg 14 q_vv) = some q_ve) (hcost_ve : e_ve.cost ≤ 2)
    (hq_ve : q_ve < ke)
    (hev_addE : evalArena m (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) q_ve = SE_add) :
    ∃ s' t,
      Exec w (combineFoldStepCmd e_vv e_ve) s s' t ∧
      t ≤ 45 ∧
      s'.regs r_kv = kv + 1 ∧ s'.regs r_ke = ke + 1 ∧
      s'.regs 10 = kv ∧ s'.regs 11 = ke ∧
      ArenaWF n (kv + 1) (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) ∧
      ArenaWF m (ke + 1) (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) ∧
      (s'.arrs a_vkd).length = (s.arrs a_vkd).length ∧
      (s'.arrs a_ekd).length = (s.arrs a_ekd).length ∧
      (∀ p < kv,
        evalArena n (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
          evalArena n (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p) ∧
      (∀ p < ke,
        evalArena m (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
          evalArena m (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p) ∧
      evalArena n (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) kv = SV_acc ∪ SV_add ∧
      evalArena m (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) ke = SE_acc ∪ SE_add ∧
      (∀ r < 10, r ≠ r_kv → r ≠ r_ke → s'.regs r = s.regs r) ∧
      (∀ a, a ≠ a_vkd → a ≠ a_vv1 → a ≠ a_vv2 → a ≠ a_ekd → a ≠ a_ev1 → a ≠ a_ev2 →
        s'.arrs a = s.arrs a) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hkv_w : kv < 2 ^ w := by omega
  have hke_w : ke < 2 ^ w := by omega
  have hp_vv_w : p_vv < 2 ^ w := by omega
  have hp_ve_w : p_ve < 2 ^ w := by omega
  have hq_vv_w : q_vv < 2 ^ w := by omega
  have hq_ve_w : q_ve < 2 ^ w := by omega
  have hkv_pos : 0 < kv := hwfV.1
  have hke_pos : 0 < ke := hwfE.1
  let s₁ := s.setReg 14 q_vv
  have hex₁ : Exec w (.assign 14 e_vv) s s₁ (e_vv.cost + 1) := .assign he_vv
  let s₂ := s₁.setReg 15 q_ve
  have hex₂ : Exec w (.assign 15 e_ve) s₁ s₂ (e_ve.cost + 1) := .assign he_ve
  let s₃ := s₂.setReg 16 kv
  have hex₃ : Exec w (.assign 16 (.reg r_kv)) s₂ s₃ 2 :=
    .assign (by simp [s₂, s₁, Expr.eval, checkWord, hr_kv, hkv_w])
  let s₄ := s₃.setReg 17 ke
  have hex₄ : Exec w (.assign 17 (.reg r_ke)) s₃ s₄ 2 :=
    .assign (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hr_ke, hke_w])
  let s₅ := (((s₄.writeArr a_vkd kv 2).writeArr a_vv1 kv p_vv).writeArr a_vv2 kv q_vv).setReg r_kv (kv + 1)
  rcases pushArenaNodeProg_exec (w := w) (a_kd := a_vkd) (a_v1 := a_vv1) (a_v2 := a_vv2)
      (r_k := r_kv) (e_kd := .const 2) (e_v1 := .reg 10) (e_v2 := .reg 14)
      (s := s₄) (K := kv) (kd := 2) (v1 := p_vv) (v2 := q_vv)
      (by decide) (by decide) (by decide) hw1 hkv1_w
      (by simp [s₄, s₃, s₂, s₁, hr_kv])
      (by simp [s₄, s₃, s₂, s₁]; omega)
      (by simp [s₄, s₃, s₂, s₁, hwfV.2.2.1]; omega)
      (by simp [s₄, s₃, s₂, s₁, hwfV.2.2.2.1]; omega)
      (by simp [Expr.eval, checkWord, hw2])
      (by simp [s₄, s₃, s₂, s₁, Expr.eval, checkWord, hr10, hp_vv_w])
      (by simp [s₄, s₃, s₂, s₁, Expr.eval, checkWord, hq_vv_w]) with
    ⟨t₅, ht₅, hex₅⟩
  let s₆ := (((s₅.writeArr a_ekd ke 2).writeArr a_ev1 ke p_ve).writeArr a_ev2 ke q_ve).setReg r_ke (ke + 1)
  rcases pushArenaNodeProg_exec (w := w) (a_kd := a_ekd) (a_v1 := a_ev1) (a_v2 := a_ev2)
      (r_k := r_ke) (e_kd := .const 2) (e_v1 := .reg 11) (e_v2 := .reg 15)
      (s := s₅) (K := ke) (kd := 2) (v1 := p_ve) (v2 := q_ve)
      (by decide) (by decide) (by decide) hw1 hke1_w
      (by simp [s₅, s₄, s₃, s₂, s₁, hr_ke])
      (by simp [s₅, s₄, s₃, s₂, s₁]; omega)
      (by simp [s₅, s₄, s₃, s₂, s₁, hwfE.2.2.1]; omega)
      (by simp [s₅, s₄, s₃, s₂, s₁, hwfE.2.2.2.1]; omega)
      (by simp [Expr.eval, checkWord, hw2])
      (by simp [s₅, s₄, s₃, s₂, s₁, Expr.eval, checkWord, hr11, hp_ve_w])
      (by simp [s₅, s₄, s₃, s₂, s₁, Expr.eval, checkWord, hq_ve_w]) with
    ⟨t₆, ht₆, hex₆⟩
  let s₇ := s₆.setReg 10 kv
  have hex₇ : Exec w (.assign 10 (.reg 16)) s₆ s₇ 2 :=
    .assign (by simp [s₆, s₅, s₄, s₃, s₂, s₁, Expr.eval, checkWord, hkv_w])
  let s' := s₇.setReg 11 ke
  have hex₈ : Exec w (.assign 11 (.reg 17)) s₇ s' 2 :=
    .assign (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, Expr.eval, checkWord, hke_w])
  have hs'_vkd : s'.arrs a_vkd = (s.arrs a_vkd).set kv 2 := by
    simp [s', s₇, s₆, s₅, s₄, s₃, s₂, s₁]
  have hs'_vv1 : s'.arrs a_vv1 = (s.arrs a_vv1).set kv p_vv := by
    simp [s', s₇, s₆, s₅, s₄, s₃, s₂, s₁]
  have hs'_vv2 : s'.arrs a_vv2 = (s.arrs a_vv2).set kv q_vv := by
    simp [s', s₇, s₆, s₅, s₄, s₃, s₂, s₁]
  have hs'_ekd : s'.arrs a_ekd = (s.arrs a_ekd).set ke 2 := by
    simp [s', s₇, s₆, s₅, s₄, s₃, s₂, s₁]
  have hs'_ev1 : s'.arrs a_ev1 = (s.arrs a_ev1).set ke p_ve := by
    simp [s', s₇, s₆, s₅, s₄, s₃, s₂, s₁]
  have hs'_ev2 : s'.arrs a_ev2 = (s.arrs a_ev2).set ke q_ve := by
    simp [s', s₇, s₆, s₅, s₄, s₃, s₂, s₁]
  have hwfV' : ArenaWF n (kv + 1) (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) := by
    rw [hs'_vkd, hs'_vv1, hs'_vv2]
    exact arenaWF_step_union hwfV (by omega) hp_vv hq_vv
  have hwfE' : ArenaWF m (ke + 1) (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) := by
    rw [hs'_ekd, hs'_ev1, hs'_ev2]
    exact arenaWF_step_union hwfE (by omega) hp_ve hq_ve
  dsimp [Expr.cost] at ht₅ ht₆
  refine ⟨s', (e_vv.cost + 1) + ((e_ve.cost + 1) + (2 + (2 + (t₅ + (t₆ + (2 + 2)))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈)))))),
    by omega,
    by simp [s', s₇, s₆, s₅, s₄, s₃, s₂, s₁],
    by simp [s', s₇, s₆, s₅, s₄, s₃, s₂, s₁],
    by simp [s', s₇], by simp [s'], hwfV', hwfE',
    by simp [hs'_vkd], by simp [hs'_ekd],
    fun p hp => by
      rw [hs'_vkd, hs'_vv1, hs'_vv2]
      exact evalArena_set_gt n _ _ _ kv 2 p_vv q_vv p hp,
    fun p hp => by
      rw [hs'_ekd, hs'_ev1, hs'_ev2]
      exact evalArena_set_gt m _ _ _ ke 2 p_ve q_ve p hp,
    by rw [hs'_vkd, hs'_vv1, hs'_vv2,
           evalArena_set_union hkv_pos _ _ _ (by omega) (by rw [hwfV.2.2.1]; omega)
             (by rw [hwfV.2.2.2.1]; omega) hp_vv hq_vv,
           hev_accV, hev_addV],
    by rw [hs'_ekd, hs'_ev1, hs'_ev2,
           evalArena_set_union hke_pos _ _ _ (by omega) (by rw [hwfE.2.2.1]; omega)
             (by rw [hwfE.2.2.2.1]; omega) hp_ve hq_ve,
           hev_accE, hev_addE],
    fun r hr h1 h2 => by
      simp [s', s₇, s₆, s₅, s₄, s₃, s₂, s₁, h1, h2,
        Nat.ne_of_lt (Nat.lt_of_lt_of_le hr (by decide : 10 ≤ 10)),
        Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 11)),
        Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 14)),
        Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 15)),
        Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 16)),
        Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 17))],
    fun a ha1 ha2 ha3 ha4 ha5 ha6 => by
      simp [s', s₇, s₆, s₅, s₄, s₃, s₂, s₁, ha1, ha2, ha3, ha4, ha5, ha6]⟩

/-- Stepwise subset contribution at index `u` for a parent digraph of `numV` vertices. -/
def stepSubFinset {α : Type*} (numV : ℕ) (f : Fin numV → Finset α)
    (owner : ℕ → ℕ) (v u : ℕ) : Finset α :=
  if h : u < numV ∧ owner u = v + 1 then
    f ⟨u, h.1⟩
  else
    ∅

theorem biUnion_range_stepSubFinset {α : Type*} [DecidableEq α]
    (numV : ℕ) (f : Fin numV → Finset α) (owner : ℕ → ℕ) (v K : ℕ) (hV : numV ≤ K) :
    (Finset.range K).biUnion (stepSubFinset numV f owner v) =
      (Finset.univ.filter (fun u : Fin numV => owner u.1 = v + 1)).biUnion f := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and,
    stepSubFinset]
  constructor
  · rintro ⟨u, _, hu⟩
    split_ifs at hu with h
    · exact ⟨⟨u, h.1⟩, h.2, hu⟩
    · simp at hu
  · rintro ⟨u, hown, hx⟩
    refine ⟨u.1, Nat.lt_of_lt_of_le u.2 hV, ?_⟩
    have h : u.1 < numV ∧ owner u.1 = v + 1 := ⟨u.2, hown⟩
    simp [h, hx]

/-- New `tid` produced by combining `(tab_A, tab_B, q_U, S_A, S_B, S_Z)`. -/
def tabsNewTid (δ ξ ω : ℕ) (tab_A tab_B : AbstractTable) (q_U : ℕ)
    (S_A S_B S_Z : Finset (Fin q_U)) : ℕ :=
  encAbstractTable δ ξ ω
    ⟨S_Z.card, (combineRecipesOfTabs δ tab_A tab_B q_U S_A S_B S_Z).map (·.H)⟩

/-- Optional source slot in `bufA` merged at step `u_A < V_max δ ξ ω` of slot `pos`. -/
def tabsSlotStepA (δ ξ ω : ℕ) (tab_A tab_B : AbstractTable) (q_U : ℕ)
    (S_A S_B S_Z : Finset (Fin q_U)) (pos u_A : ℕ) : Option ℕ :=
  let rs := combineRecipesOfTabs δ tab_A tab_B q_U S_A S_B S_Z
  let idx := pos / V_max δ ξ ω
  let v := pos % V_max δ ξ ω
  if h : idx < rs.length then
    let r := rs[idx]
    if v < r.H.digraph.numVerts ∧ u_A < tab_A.2[r.idx_A.1].digraph.numVerts ∧
       r.owner_A u_A = v + 1 then
      some (r.idx_A.1 * V_max δ ξ ω + u_A)
    else
      none
  else
    none

/-- Optional source slot in `bufB` merged at step `u_B < V_max δ ξ ω` of slot `pos`. -/
def tabsSlotStepB (δ ξ ω : ℕ) (tab_A tab_B : AbstractTable) (q_U : ℕ)
    (S_A S_B S_Z : Finset (Fin q_U)) (pos u_B : ℕ) : Option ℕ :=
  let rs := combineRecipesOfTabs δ tab_A tab_B q_U S_A S_B S_Z
  let idx := pos / V_max δ ξ ω
  let v := pos % V_max δ ξ ω
  if h : idx < rs.length then
    let r := rs[idx]
    if v < r.H.digraph.numVerts ∧ u_B < tab_B.2[r.idx_B.1].digraph.numVerts ∧
       r.owner_B u_B = v + 1 then
      some (r.idx_B.1 * V_max δ ξ ω + u_B)
    else
      none
  else
    none

/-- Edge-map expression for slot `pos`: reads from `a_acc_em` or `a_rhs_em`, or returns `0`. -/
def tabsSlotEMExpr (δ ξ ω : ℕ) (tab_A tab_B : AbstractTable) (q_U : ℕ)
    (S_A S_B S_Z : Finset (Fin q_U)) (pos : ℕ) : Expr :=
  let rs := combineRecipesOfTabs δ tab_A tab_B q_U S_A S_B S_Z
  let idx := pos / V_max δ ξ ω
  let d := pos % V_max δ ξ ω
  if h : idx < rs.length then
    let r := rs[idx]
    if d < r.H.digraph.numEdges then
      let m_A := tab_A.2[r.idx_A.1].digraph.numEdges
      if d < m_A then
        .read a_acc_em (.const (r.idx_A.1 * V_max δ ξ ω + d))
      else
        .read a_rhs_em (.const (r.idx_B.1 * V_max δ ξ ω + (d - m_A)))
    else
      .const 0
  else
    .const 0

/-- Fold command for step `u_A < V_max δ ξ ω` from `bufA` at slot `pos`. -/
def tabsFoldACmd (δ ξ ω : ℕ) (tab_A tab_B : AbstractTable) (q_U : ℕ)
    (S_A S_B S_Z : Finset (Fin q_U)) (pos u_A : ℕ) : Cmd :=
  match tabsSlotStepA δ ξ ω tab_A tab_B q_U S_A S_B S_Z pos u_A with
  | some src => combineFoldStepCmd (.read a_acc_vv (.const src)) (.read a_acc_ve (.const src))
  | none     => combineFoldStepCmd (.const 0) (.const 0)

/-- Fold command for step `u_B < V_max δ ξ ω` from `bufB` at slot `pos`. -/
def tabsFoldBCmd (δ ξ ω : ℕ) (tab_A tab_B : AbstractTable) (q_U : ℕ)
    (S_A S_B S_Z : Finset (Fin q_U)) (pos u_B : ℕ) : Cmd :=
  match tabsSlotStepB δ ξ ω tab_A tab_B q_U S_A S_B S_Z pos u_B with
  | some src => combineFoldStepCmd (.read a_rhs_vv (.const src)) (.read a_rhs_ve (.const src))
  | none     => combineFoldStepCmd (.const 0) (.const 0)

/-- Word RAM command computing slot `pos < S_tab δ ξ ω` of `(a_out_vv, a_out_ve, a_out_em)`. -/
def tabsSlotProg (δ ξ ω : ℕ) (tab_A tab_B : AbstractTable) (q_U : ℕ)
    (S_A S_B S_Z : Finset (Fin q_U)) (pos : ℕ) : Cmd :=
  .seq (.assign 10 (.const 0))
  (.seq (.assign 11 (.const 0))
  (.seq (seqRange (V_max δ ξ ω) (tabsFoldACmd δ ξ ω tab_A tab_B q_U S_A S_B S_Z pos))
  (.seq (seqRange (V_max δ ξ ω) (tabsFoldBCmd δ ξ ω tab_A tab_B q_U S_A S_B S_Z pos))
  (.seq (.write a_out_vv (.const pos) (.reg 10))
  (.seq (.write a_out_ve (.const pos) (.reg 11))
        (.write a_out_em (.const pos)
          (tabsSlotEMExpr δ ξ ω tab_A tab_B q_U S_A S_B S_Z pos)))))))

/-- Word RAM body for a fixed combination configuration `(tab_A, tab_B, q_U, S_A, S_B, S_Z)`. -/
def tabsCombineBodyProg (δ ξ ω : ℕ) (tab_A tab_B : AbstractTable) (q_U : ℕ)
    (S_A S_B S_Z : Finset (Fin q_U)) : Cmd :=
  .seq (.assign r_tidA (.const (tabsNewTid δ ξ ω tab_A tab_B q_U S_A S_B S_Z)))
       (seqRange (S_tab δ ξ ω) (tabsSlotProg δ ξ ω tab_A tab_B q_U S_A S_B S_Z))

/-- Canonical combination body indexed by integer codes `(tid_A, tid_B, mcode)`. -/
def canonCombineBodyProg (δ ξ ω tid_A tid_B mcode : ℕ) : Cmd :=
  tabsCombineBodyProg δ ξ ω
    (decAbstractTable δ ξ ω tid_A)
    (decAbstractTable δ ξ ω tid_B)
    (canonMaskCardU ξ ω mcode)
    (canonMaskSubA ξ ω mcode)
    (canonMaskSubB ξ ω mcode)
    (canonMaskSubZ ξ ω mcode)

/-- Three-level `branchOnBound` dispatch on `r_tidA < T_max δ ξ ω`, `r_tidB < T_max δ ξ ω`, and
`r_13 < M_max ξ ω`. -/
def combineDispatchProg (δ ξ ω : ℕ) : Cmd :=
  branchOnBound (T_max δ ξ ω) r_tidA (fun tid_A =>
    branchOnBound (T_max δ ξ ω) r_tidB (fun tid_B =>
      branchOnBound (M_max ξ ω) 13 (fun mcode =>
        canonCombineBodyProg δ ξ ω tid_A tid_B mcode)))

/-- Copy `(a_out_zV, a_out_zI, a_out_vv, a_out_ve, a_out_em)` into `bufA`. -/
def copyOutToAccProg (δ ξ ω : ℕ) : Cmd :=
  .seq (copyFixedArrMinProg (Q_max ξ ω) a_out_zV a_acc_zV 0)
  (.seq (copyFixedArrMinProg (Q_max ξ ω) a_out_zI a_acc_zI 1)
  (.seq (copyFixedArrMinProg (S_tab δ ξ ω) a_out_vv a_acc_vv r_kv)
  (.seq (copyFixedArrMinProg (S_tab δ ξ ω) a_out_ve a_acc_ve r_ke)
        (copyFixedArrMinProg (S_tab δ ξ ω) a_out_em a_acc_em 1))))

/-- Complete constant-time Word RAM combination step combining `bufA` and `bufB` into `bufA`. -/
def combineStepProg (δ ξ ω : ℕ) : Cmd :=
  .seq mergeBoundaryProg
  (.seq (.assign r_qA (.reg 12))
  (.seq (combineDispatchProg δ ξ ω)
        (copyOutToAccProg δ ξ ω)))

/-- Number of arena nodes pushed per `combineStepProg` execution. -/
def K_comb (δ ξ ω : ℕ) : ℕ :=
  2 * V_max δ ξ ω * S_tab δ ξ ω

/-! ### Section 3: Execution and Correctness of `combineStepProg` -/

/-- Stepwise vertex subset contribution from `es_A` at `(pos, u_A)`. -/
def slotVertSetA {δ ξ ω q_U : ℕ} {G : ComputeDigraph}
    {ZA ZB : Finset (Fin G.numVerts)}
    (es_A : List (RawCertEntry G ZA.card))
    (es_B : List (RawCertEntry G ZB.card))
    (S_A S_B S_Z : Finset (Fin q_U)) (pos u_A : ℕ) : Finset (Fin G.numVerts) :=
  let tab_A : AbstractTable := ⟨ZA.card, es_A.map RawCertEntry.H⟩
  let tab_B : AbstractTable := ⟨ZB.card, es_B.map RawCertEntry.H⟩
  let rs := combineRecipesOfTabs δ tab_A tab_B q_U S_A S_B S_Z
  let idx := pos / V_max δ ξ ω
  let v := pos % V_max δ ξ ω
  if h : idx < rs.length then
    let r := rs[idx]
    have hiA : r.idx_A.1 < es_A.length := by simpa [tab_A] using r.idx_A.2
    if v < r.H.digraph.numVerts then
      stepSubFinset es_A[r.idx_A.1].H.digraph.numVerts es_A[r.idx_A.1].vertVerts r.owner_A v u_A
    else ∅
  else ∅

/-- Stepwise edge subset contribution from `es_A` at `(pos, u_A)`. -/
def slotEdgeSetA {δ ξ ω q_U : ℕ} {G : ComputeDigraph}
    {ZA ZB : Finset (Fin G.numVerts)}
    (es_A : List (RawCertEntry G ZA.card))
    (es_B : List (RawCertEntry G ZB.card))
    (S_A S_B S_Z : Finset (Fin q_U)) (pos u_A : ℕ) : Finset (Fin G.numEdges) :=
  let tab_A : AbstractTable := ⟨ZA.card, es_A.map RawCertEntry.H⟩
  let tab_B : AbstractTable := ⟨ZB.card, es_B.map RawCertEntry.H⟩
  let rs := combineRecipesOfTabs δ tab_A tab_B q_U S_A S_B S_Z
  let idx := pos / V_max δ ξ ω
  let v := pos % V_max δ ξ ω
  if h : idx < rs.length then
    let r := rs[idx]
    have hiA : r.idx_A.1 < es_A.length := by simpa [tab_A] using r.idx_A.2
    if v < r.H.digraph.numVerts then
      stepSubFinset es_A[r.idx_A.1].H.digraph.numVerts es_A[r.idx_A.1].vertEdges r.owner_A v u_A
    else ∅
  else ∅

/-- Stepwise vertex subset contribution from `es_B` at `(pos, u_B)`. -/
def slotVertSetB {δ ξ ω q_U : ℕ} {G : ComputeDigraph}
    {ZA ZB : Finset (Fin G.numVerts)}
    (es_A : List (RawCertEntry G ZA.card))
    (es_B : List (RawCertEntry G ZB.card))
    (S_A S_B S_Z : Finset (Fin q_U)) (pos u_B : ℕ) : Finset (Fin G.numVerts) :=
  let tab_A : AbstractTable := ⟨ZA.card, es_A.map RawCertEntry.H⟩
  let tab_B : AbstractTable := ⟨ZB.card, es_B.map RawCertEntry.H⟩
  let rs := combineRecipesOfTabs δ tab_A tab_B q_U S_A S_B S_Z
  let idx := pos / V_max δ ξ ω
  let v := pos % V_max δ ξ ω
  if h : idx < rs.length then
    let r := rs[idx]
    have hiB : r.idx_B.1 < es_B.length := by simpa [tab_B] using r.idx_B.2
    if v < r.H.digraph.numVerts then
      stepSubFinset es_B[r.idx_B.1].H.digraph.numVerts es_B[r.idx_B.1].vertVerts r.owner_B v u_B
    else ∅
  else ∅

/-- Stepwise edge subset contribution from `es_B` at `(pos, u_B)`. -/
def slotEdgeSetB {δ ξ ω q_U : ℕ} {G : ComputeDigraph}
    {ZA ZB : Finset (Fin G.numVerts)}
    (es_A : List (RawCertEntry G ZA.card))
    (es_B : List (RawCertEntry G ZB.card))
    (S_A S_B S_Z : Finset (Fin q_U)) (pos u_B : ℕ) : Finset (Fin G.numEdges) :=
  let tab_A : AbstractTable := ⟨ZA.card, es_A.map RawCertEntry.H⟩
  let tab_B : AbstractTable := ⟨ZB.card, es_B.map RawCertEntry.H⟩
  let rs := combineRecipesOfTabs δ tab_A tab_B q_U S_A S_B S_Z
  let idx := pos / V_max δ ξ ω
  let v := pos % V_max δ ξ ω
  if h : idx < rs.length then
    let r := rs[idx]
    have hiB : r.idx_B.1 < es_B.length := by simpa [tab_B] using r.idx_B.2
    if v < r.H.digraph.numVerts then
      stepSubFinset es_B[r.idx_B.1].H.digraph.numVerts es_B[r.idx_B.1].vertEdges r.owner_B v u_B
    else ∅
  else ∅

/-- Target vertex subset for slot `pos`. -/
def slotTargetVV {δ ξ ω q_U : ℕ} {G : ComputeDigraph}
    {ZA ZB : Finset (Fin G.numVerts)}
    (es_A : List (RawCertEntry G ZA.card))
    (es_B : List (RawCertEntry G ZB.card))
    (S_A S_B S_Z : Finset (Fin q_U)) (pos : ℕ) : Finset (Fin G.numVerts) :=
  (Finset.range (V_max δ ξ ω)).biUnion (slotVertSetA (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos) ∪
  (Finset.range (V_max δ ξ ω)).biUnion (slotVertSetB (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos)

/-- Target edge subset for slot `pos`. -/
def slotTargetVE {δ ξ ω q_U : ℕ} {G : ComputeDigraph}
    {ZA ZB : Finset (Fin G.numVerts)}
    (es_A : List (RawCertEntry G ZA.card))
    (es_B : List (RawCertEntry G ZB.card))
    (S_A S_B S_Z : Finset (Fin q_U)) (pos : ℕ) : Finset (Fin G.numEdges) :=
  (Finset.range (V_max δ ξ ω)).biUnion (slotEdgeSetA (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos) ∪
  (Finset.range (V_max δ ξ ω)).biUnion (slotEdgeSetB (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos)

/-- Target edge-map value for slot `pos`. -/
def slotTargetEM {δ ξ ω q_U : ℕ} {G : ComputeDigraph}
    {ZA ZB : Finset (Fin G.numVerts)}
    (es_A : List (RawCertEntry G ZA.card))
    (es_B : List (RawCertEntry G ZB.card))
    (S_A S_B S_Z : Finset (Fin q_U)) (pos : ℕ) : ℕ :=
  let tab_A : AbstractTable := ⟨ZA.card, es_A.map RawCertEntry.H⟩
  let tab_B : AbstractTable := ⟨ZB.card, es_B.map RawCertEntry.H⟩
  let rs := combineRecipesOfTabs δ tab_A tab_B q_U S_A S_B S_Z
  let idx := pos / V_max δ ξ ω
  let d := pos % V_max δ ξ ω
  if h : idx < rs.length then
    let r := rs[idx]
    if hd : d < r.H.digraph.numEdges then
      ((r.eval es_A es_B rfl rfl).edgeMap ⟨d, hd⟩).1
    else 0
  else 0

theorem slotTargetVV_eq_eval {δ ξ ω q_U : ℕ} {G : ComputeDigraph}
    {ZA ZB : Finset (Fin G.numVerts)}
    (es_A : List (RawCertEntry G ZA.card))
    (es_B : List (RawCertEntry G ZB.card))
    (hqA : ZA.card ≤ Q_max ξ ω) (hqB : ZB.card ≤ Q_max ξ ω)
    (hdetA : ∀ e ∈ es_A, e.H.HasDetailLe δ)
    (hdetB : ∀ e ∈ es_B, e.H.HasDetailLe δ)
    (S_A S_B S_Z : Finset (Fin q_U)) (pos : ℕ)
    {idx : ℕ} (hdiv : pos / V_max δ ξ ω = idx)
    (hidx : idx < (combineRecipesOfTabs δ ⟨ZA.card, es_A.map RawCertEntry.H⟩ ⟨ZB.card, es_B.map RawCertEntry.H⟩ q_U S_A S_B S_Z).length)
    {v : Fin (combineRecipesOfTabs δ ⟨ZA.card, es_A.map RawCertEntry.H⟩ ⟨ZB.card, es_B.map RawCertEntry.H⟩ q_U S_A S_B S_Z)[idx].H.digraph.numVerts}
    (hmod : pos % V_max δ ξ ω = v.1) :
    slotTargetVV (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos =
      ((combineRecipesOfTabs δ ⟨ZA.card, es_A.map RawCertEntry.H⟩ ⟨ZB.card, es_B.map RawCertEntry.H⟩ q_U S_A S_B S_Z)[idx].eval
        es_A es_B rfl rfl).vertVerts ⟨v.1, v.2⟩ := by
  subst hdiv
  let tab_A : AbstractTable := ⟨ZA.card, es_A.map RawCertEntry.H⟩
  let tab_B : AbstractTable := ⟨ZB.card, es_B.map RawCertEntry.H⟩
  let rs := combineRecipesOfTabs δ tab_A tab_B q_U S_A S_B S_Z
  let r := rs[pos / V_max δ ξ ω]'hidx
  have hiA : r.idx_A.1 < es_A.length := by simpa [tab_A] using r.idx_A.2
  have hiB : r.idx_B.1 < es_B.length := by simpa [tab_B] using r.idx_B.2
  have hVA : es_A[r.idx_A.1].H.digraph.numVerts ≤ V_max δ ξ ω :=
    le_of_lt (numVerts_lt_V_max hqA (hdetA _ (List.getElem_mem hiA)))
  have hVB : es_B[r.idx_B.1].H.digraph.numVerts ≤ V_max δ ξ ω :=
    le_of_lt (numVerts_lt_V_max hqB (hdetB _ (List.getElem_mem hiB)))
  have hstepA : ∀ u_A, slotVertSetA (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos u_A =
      stepSubFinset es_A[r.idx_A.1].H.digraph.numVerts es_A[r.idx_A.1].vertVerts r.owner_A v.1 u_A := by
    intro u_A
    unfold slotVertSetA
    dsimp only
    simp only [hmod, hidx, ↓reduceDIte, v.2, ↓reduceIte]
    rfl
  have hstepB : ∀ u_B, slotVertSetB (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos u_B =
      stepSubFinset es_B[r.idx_B.1].H.digraph.numVerts es_B[r.idx_B.1].vertVerts r.owner_B v.1 u_B := by
    intro u_B
    unfold slotVertSetB
    dsimp only
    simp only [hmod, hidx, ↓reduceDIte, v.2, ↓reduceIte]
    rfl
  unfold slotTargetVV CombineEntryRecipe.eval
  dsimp only
  rw [Finset.biUnion_congr rfl (fun u _ => hstepA u),
      Finset.biUnion_congr rfl (fun u _ => hstepB u),
      biUnion_range_stepSubFinset _ _ _ _ _ hVA,
      biUnion_range_stepSubFinset _ _ _ _ _ hVB]

theorem slotTargetVE_eq_eval {δ ξ ω q_U : ℕ} {G : ComputeDigraph}
    {ZA ZB : Finset (Fin G.numVerts)}
    (es_A : List (RawCertEntry G ZA.card))
    (es_B : List (RawCertEntry G ZB.card))
    (hqA : ZA.card ≤ Q_max ξ ω) (hqB : ZB.card ≤ Q_max ξ ω)
    (hdetA : ∀ e ∈ es_A, e.H.HasDetailLe δ)
    (hdetB : ∀ e ∈ es_B, e.H.HasDetailLe δ)
    (S_A S_B S_Z : Finset (Fin q_U)) (pos : ℕ)
    {idx : ℕ} (hdiv : pos / V_max δ ξ ω = idx)
    (hidx : idx < (combineRecipesOfTabs δ ⟨ZA.card, es_A.map RawCertEntry.H⟩ ⟨ZB.card, es_B.map RawCertEntry.H⟩ q_U S_A S_B S_Z).length)
    {v : Fin (combineRecipesOfTabs δ ⟨ZA.card, es_A.map RawCertEntry.H⟩ ⟨ZB.card, es_B.map RawCertEntry.H⟩ q_U S_A S_B S_Z)[idx].H.digraph.numVerts}
    (hmod : pos % V_max δ ξ ω = v.1) :
    slotTargetVE (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos =
      ((combineRecipesOfTabs δ ⟨ZA.card, es_A.map RawCertEntry.H⟩ ⟨ZB.card, es_B.map RawCertEntry.H⟩ q_U S_A S_B S_Z)[idx].eval
        es_A es_B rfl rfl).vertEdges ⟨v.1, v.2⟩ := by
  subst hdiv
  let tab_A : AbstractTable := ⟨ZA.card, es_A.map RawCertEntry.H⟩
  let tab_B : AbstractTable := ⟨ZB.card, es_B.map RawCertEntry.H⟩
  let rs := combineRecipesOfTabs δ tab_A tab_B q_U S_A S_B S_Z
  let r := rs[pos / V_max δ ξ ω]'hidx
  have hiA : r.idx_A.1 < es_A.length := by simpa [tab_A] using r.idx_A.2
  have hiB : r.idx_B.1 < es_B.length := by simpa [tab_B] using r.idx_B.2
  have hVA : es_A[r.idx_A.1].H.digraph.numVerts ≤ V_max δ ξ ω :=
    le_of_lt (numVerts_lt_V_max hqA (hdetA _ (List.getElem_mem hiA)))
  have hVB : es_B[r.idx_B.1].H.digraph.numVerts ≤ V_max δ ξ ω :=
    le_of_lt (numVerts_lt_V_max hqB (hdetB _ (List.getElem_mem hiB)))
  have hstepA : ∀ u_A, slotEdgeSetA (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos u_A =
      stepSubFinset es_A[r.idx_A.1].H.digraph.numVerts es_A[r.idx_A.1].vertEdges r.owner_A v.1 u_A := by
    intro u_A
    unfold slotEdgeSetA
    dsimp only
    simp only [hmod, hidx, ↓reduceDIte, v.2, ↓reduceIte]
    rfl
  have hstepB : ∀ u_B, slotEdgeSetB (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos u_B =
      stepSubFinset es_B[r.idx_B.1].H.digraph.numVerts es_B[r.idx_B.1].vertEdges r.owner_B v.1 u_B := by
    intro u_B
    unfold slotEdgeSetB
    dsimp only
    simp only [hmod, hidx, ↓reduceDIte, v.2, ↓reduceIte]
    rfl
  unfold slotTargetVE CombineEntryRecipe.eval
  dsimp only
  rw [Finset.biUnion_congr rfl (fun u _ => hstepA u),
      Finset.biUnion_congr rfl (fun u _ => hstepB u),
      biUnion_range_stepSubFinset _ _ _ _ _ hVA,
      biUnion_range_stepSubFinset _ _ _ _ _ hVB]

theorem slotTargetEM_eq_eval {δ ξ ω q_U : ℕ} {G : ComputeDigraph}
    {ZA ZB : Finset (Fin G.numVerts)}
    (es_A : List (RawCertEntry G ZA.card))
    (es_B : List (RawCertEntry G ZB.card))
    (S_A S_B S_Z : Finset (Fin q_U)) (pos : ℕ)
    {idx : ℕ} (hdiv : pos / V_max δ ξ ω = idx)
    (hidx : idx < (combineRecipesOfTabs δ ⟨ZA.card, es_A.map RawCertEntry.H⟩ ⟨ZB.card, es_B.map RawCertEntry.H⟩ q_U S_A S_B S_Z).length)
    {d : Fin (combineRecipesOfTabs δ ⟨ZA.card, es_A.map RawCertEntry.H⟩ ⟨ZB.card, es_B.map RawCertEntry.H⟩ q_U S_A S_B S_Z)[idx].H.digraph.numEdges}
    (hmod : pos % V_max δ ξ ω = d.1) :
    slotTargetEM (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos =
      (((combineRecipesOfTabs δ ⟨ZA.card, es_A.map RawCertEntry.H⟩ ⟨ZB.card, es_B.map RawCertEntry.H⟩ q_U S_A S_B S_Z)[idx].eval
        es_A es_B rfl rfl).edgeMap ⟨d.1, d.2⟩).1 := by
  subst hdiv
  unfold slotTargetEM
  dsimp only
  simp only [hmod, hidx, ↓reduceDIte, d.2]

private theorem eval_read_const_of_getD {w : ℕ} {s : State} {a : Arr} {idx val : ℕ}
    (hidx_w : idx < 2 ^ w) (hval_w : val < 2 ^ w)
    (hlen : idx < (s.arrs a).length) (hget : (s.arrs a).getD idx 0 = val) :
    (Expr.read a (.const idx)).eval w s = some val := by
  have hget' : (s.arrs a)[idx]'hlen = val := by
    rw [← hget, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
  simp [Expr.eval, checkWord, hidx_w, hlen, hget', hval_w]

theorem tabsFoldACmd_exec {w δ ξ ω q_U kv₀ ke₀ kv ke p_vv p_ve pos u_A : ℕ}
    {G : ComputeDigraph} {ZA ZB : Finset (Fin G.numVerts)}
    {EA _EB : Finset (Fin G.numEdges)}
    {es_A : List (RawCertEntry G ZA.card)}
    {es_B : List (RawCertEntry G ZB.card)}
    {S_A S_B S_Z : Finset (Fin q_U)}
    {SV_acc : Finset (Fin G.numVerts)} {SE_acc : Finset (Fin G.numEdges)}
    {s₀ s : State}
    (hbufA : ValidPieceBuffer δ ξ ω G ZA EA es_A bufA s₀)
    (hw2 : 2 < 2 ^ w) (hS_w : S_tab δ ξ ω < 2 ^ w)
    (hkv1_w : kv + 1 < 2 ^ w) (hke1_w : ke + 1 < 2 ^ w)
    (hkv0_le : kv₀ ≤ kv) (hke0_le : ke₀ ≤ ke)
    (hr_kv0 : s₀.regs r_kv = kv₀) (hr_ke0 : s₀.regs r_ke = ke₀)
    (hwfV : ArenaWF G.numVerts kv (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2))
    (hwfE : ArenaWF G.numEdges ke (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2))
    (hkv_cap : kv + 1 ≤ (s.arrs a_vkd).length)
    (hke_cap : ke + 1 ≤ (s.arrs a_ekd).length)
    (hevalV0 : ∀ p < kv₀,
      evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p =
        evalArena G.numVerts (s₀.arrs a_vkd) (s₀.arrs a_vv1) (s₀.arrs a_vv2) p)
    (hevalE0 : ∀ p < ke₀,
      evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p =
        evalArena G.numEdges (s₀.arrs a_ekd) (s₀.arrs a_ev1) (s₀.arrs a_ev2) p)
    (hacc_vv : s.arrs a_acc_vv = s₀.arrs a_acc_vv)
    (hacc_ve : s.arrs a_acc_ve = s₀.arrs a_acc_ve)
    (hr_kv : s.regs r_kv = kv) (hr_ke : s.regs r_ke = ke)
    (hr10 : s.regs 10 = p_vv) (hr11 : s.regs 11 = p_ve)
    (hp_vv : p_vv < kv) (hp_ve : p_ve < ke)
    (hev_accV : evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p_vv = SV_acc)
    (hev_accE : evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p_ve = SE_acc)
    (hu_A : u_A < V_max δ ξ ω) :
    let tab_A : AbstractTable := ⟨ZA.card, es_A.map RawCertEntry.H⟩
    let tab_B : AbstractTable := ⟨ZB.card, es_B.map RawCertEntry.H⟩
    ∃ s' t,
      Exec w (tabsFoldACmd δ ξ ω tab_A tab_B q_U S_A S_B S_Z pos u_A) s s' t ∧
      t ≤ 45 ∧
      s'.regs r_kv = kv + 1 ∧ s'.regs r_ke = ke + 1 ∧
      s'.regs 10 = kv ∧ s'.regs 11 = ke ∧
      ArenaWF G.numVerts (kv + 1) (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) ∧
      ArenaWF G.numEdges (ke + 1) (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) ∧
      (s'.arrs a_vkd).length = (s.arrs a_vkd).length ∧
      (s'.arrs a_ekd).length = (s.arrs a_ekd).length ∧
      (∀ p < kv,
        evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
          evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p) ∧
      (∀ p < ke,
        evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
          evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p) ∧
      evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) kv =
        SV_acc ∪ slotVertSetA (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos u_A ∧
      evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) ke =
        SE_acc ∪ slotEdgeSetA (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos u_A ∧
      (∀ r < 10, r ≠ r_kv → r ≠ r_ke → s'.regs r = s.regs r) ∧
      (∀ a, a ≠ a_vkd → a ≠ a_vv1 → a ≠ a_vv2 → a ≠ a_ekd → a ≠ a_ev1 → a ≠ a_ev2 →
        s'.arrs a = s.arrs a) := by
  intro tab_A tab_B
  have h0_w : 0 < 2 ^ w := by omega
  let rs := combineRecipesOfTabs δ tab_A tab_B q_U S_A S_B S_Z
  let idx := pos / V_max δ ξ ω
  let v := pos % V_max δ ξ ω
  unfold tabsFoldACmd tabsSlotStepA slotVertSetA slotEdgeSetA stepSubFinset
  dsimp only [tab_A, tab_B]
  by_cases hidx : idx < rs.length
  · have hidx' : pos / V_max δ ξ ω < (combineRecipesOfTabs δ ⟨ZA.card, es_A.map RawCertEntry.H⟩ ⟨ZB.card, es_B.map RawCertEntry.H⟩ q_U S_A S_B S_Z).length := hidx
    simp only [hidx', ↓reduceDIte]
    let r := rs[idx]'hidx
    have hiA : r.idx_A.1 < es_A.length := by simpa [tab_A] using r.idx_A.2
    have hgetA : (es_A.map RawCertEntry.H)[r.idx_A.1] = es_A[r.idx_A.1].H := List.getElem_map _
    by_cases hcond : v < r.H.digraph.numVerts ∧
        u_A < (es_A.map RawCertEntry.H)[r.idx_A.1].digraph.numVerts ∧ r.owner_A u_A = v + 1
    · rcases hcond with ⟨hv, huA_lt, hown⟩
      have huA_lt' : u_A < es_A[r.idx_A.1].H.digraph.numVerts := hgetA ▸ huA_lt
      have hcond' : v < r.H.digraph.numVerts ∧
          u_A < (es_A.map RawCertEntry.H)[r.idx_A.1].digraph.numVerts ∧ r.owner_A u_A = v + 1 := ⟨hv, huA_lt, hown⟩
      have hsub : u_A < es_A[r.idx_A.1].H.digraph.numVerts ∧ r.owner_A u_A = v + 1 := ⟨huA_lt', hown⟩
      dsimp only [r, rs, idx, v, tab_A, tab_B] at hcond' hv hsub
      simp only [hcond', hsub, ↓reduceIte]
      let src := r.idx_A.1 * V_max δ ξ ω + u_A
      have hiA_C : r.idx_A.1 < C_max δ ξ ω :=
        Nat.lt_of_lt_of_le hiA (Nat.le_trans hbufA.hlen_le
          (Nat.le_of_lt (length_allDetailLeCodes_lt_C_max δ ξ ω hbufA.hq_le)))
      have hsrc_S : src < S_tab δ ξ ω := by
        unfold S_tab; have := Nat.mul_le_mul_right (V_max δ ξ ω) hiA_C
        rw [Nat.succ_mul] at this; omega
      have hsrc_w : src < 2 ^ w := by omega
      rcases (hbufA.hentries ⟨r.idx_A.1, hiA⟩).1 ⟨u_A, huA_lt'⟩ with
        ⟨hq_vv0, hev_vv0, hq_ve0, hev_ve0⟩
      dsimp [bufA] at hq_vv0 hev_vv0 hq_ve0 hev_ve0
      rw [hr_kv0] at hq_vv0; rw [hr_ke0] at hq_ve0
      let q_vv := (s₀.arrs a_acc_vv).getD src 0
      let q_ve := (s₀.arrs a_acc_ve).getD src 0
      have hq_vv_kv : q_vv < kv := Nat.lt_of_lt_of_le hq_vv0 hkv0_le
      have hq_ve_ke : q_ve < ke := Nat.lt_of_lt_of_le hq_ve0 hke0_le
      have hvv_len : (s₀.arrs a_acc_vv).length = S_tab δ ξ ω := hbufA.hvv_len
      have hve_len : (s₀.arrs a_acc_ve).length = S_tab δ ξ ω := hbufA.hve_len
      have he_vv : (Expr.read a_acc_vv (.const src)).eval w s = some q_vv :=
        eval_read_const_of_getD hsrc_w (by omega) (by rw [hacc_vv, hvv_len]; exact hsrc_S)
          (by rw [hacc_vv])
      have he_ve : (Expr.read a_acc_ve (.const src)).eval w (s.setReg 14 q_vv) = some q_ve :=
        eval_read_const_of_getD hsrc_w (by omega)
          (by simp [hacc_ve, hve_len, hsrc_S]) (by simp [hacc_ve, q_ve])
      exact combineFoldStepCmd_exec hw2 hkv1_w hke1_w hwfV hwfE hkv_cap hke_cap hr_kv hr_ke
        hr10 hr11 hp_vv hp_ve hev_accV hev_accE he_vv (le_refl 2) hq_vv_kv
        ((hevalV0 q_vv hq_vv0).trans hev_vv0) he_ve (le_refl 2) hq_ve_ke
        ((hevalE0 q_ve hq_ve0).trans hev_ve0)
    · have hcond' := hcond
      dsimp only [r, rs, idx, v, tab_A, tab_B] at hcond'
      simp only [hcond', ↓reduceIte]
      have hnot : ¬(v < r.H.digraph.numVerts ∧
          (u_A < es_A[r.idx_A.1].H.digraph.numVerts ∧ r.owner_A u_A = v + 1)) := by
        rintro ⟨hv, huA', hown⟩
        exact hcond ⟨hv, hgetA.symm ▸ huA', hown⟩
      have hempV : (if v < r.H.digraph.numVerts then
          if h : u_A < es_A[r.idx_A.1].H.digraph.numVerts ∧ r.owner_A u_A = v + 1 then
            es_A[r.idx_A.1].vertVerts ⟨u_A, h.1⟩ else ∅ else ∅) = ∅ := by
        split_ifs with hv h <;> [exact False.elim (hnot ⟨hv, h⟩); rfl; rfl]
      have hempE : (if v < r.H.digraph.numVerts then
          if h : u_A < es_A[r.idx_A.1].H.digraph.numVerts ∧ r.owner_A u_A = v + 1 then
            es_A[r.idx_A.1].vertEdges ⟨u_A, h.1⟩ else ∅ else ∅) = ∅ := by
        split_ifs with hv h <;> [exact False.elim (hnot ⟨hv, h⟩); rfl; rfl]
      dsimp only [r, rs, idx, v, tab_A, tab_B] at hempV hempE
      rw [hempV, hempE]
      exact combineFoldStepCmd_exec hw2 hkv1_w hke1_w hwfV hwfE hkv_cap hke_cap hr_kv hr_ke
        hr10 hr11 hp_vv hp_ve hev_accV hev_accE
        (by simp [Expr.eval, checkWord, h0_w]) (Nat.le_succ 1) hwfV.1 (evalArena_zero _ _ _ _)
        (by simp [Expr.eval, checkWord, h0_w]) (Nat.le_succ 1) hwfE.1 (evalArena_zero _ _ _ _)
  · dsimp only [rs, idx, tab_A, tab_B] at hidx
    simp only [hidx, ↓reduceDIte]
    exact combineFoldStepCmd_exec hw2 hkv1_w hke1_w hwfV hwfE hkv_cap hke_cap hr_kv hr_ke
      hr10 hr11 hp_vv hp_ve hev_accV hev_accE
      (by simp [Expr.eval, checkWord, h0_w]) (Nat.le_succ 1) hwfV.1 (evalArena_zero _ _ _ _)
      (by simp [Expr.eval, checkWord, h0_w]) (Nat.le_succ 1) hwfE.1 (evalArena_zero _ _ _ _)

theorem tabsFoldBCmd_exec {w δ ξ ω q_U kv₀ ke₀ kv ke p_vv p_ve pos u_B : ℕ}
    {G : ComputeDigraph} {ZA ZB : Finset (Fin G.numVerts)}
    {_EA EB : Finset (Fin G.numEdges)}
    {es_A : List (RawCertEntry G ZA.card)}
    {es_B : List (RawCertEntry G ZB.card)}
    {S_A S_B S_Z : Finset (Fin q_U)}
    {SV_acc : Finset (Fin G.numVerts)} {SE_acc : Finset (Fin G.numEdges)}
    {s₀ s : State}
    (hbufB : ValidPieceBuffer δ ξ ω G ZB EB es_B bufB s₀)
    (hw2 : 2 < 2 ^ w) (hS_w : S_tab δ ξ ω < 2 ^ w)
    (hkv1_w : kv + 1 < 2 ^ w) (hke1_w : ke + 1 < 2 ^ w)
    (hkv0_le : kv₀ ≤ kv) (hke0_le : ke₀ ≤ ke)
    (hr_kv0 : s₀.regs r_kv = kv₀) (hr_ke0 : s₀.regs r_ke = ke₀)
    (hwfV : ArenaWF G.numVerts kv (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2))
    (hwfE : ArenaWF G.numEdges ke (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2))
    (hkv_cap : kv + 1 ≤ (s.arrs a_vkd).length)
    (hke_cap : ke + 1 ≤ (s.arrs a_ekd).length)
    (hevalV0 : ∀ p < kv₀,
      evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p =
        evalArena G.numVerts (s₀.arrs a_vkd) (s₀.arrs a_vv1) (s₀.arrs a_vv2) p)
    (hevalE0 : ∀ p < ke₀,
      evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p =
        evalArena G.numEdges (s₀.arrs a_ekd) (s₀.arrs a_ev1) (s₀.arrs a_ev2) p)
    (hrhs_vv : s.arrs a_rhs_vv = s₀.arrs a_rhs_vv)
    (hrhs_ve : s.arrs a_rhs_ve = s₀.arrs a_rhs_ve)
    (hr_kv : s.regs r_kv = kv) (hr_ke : s.regs r_ke = ke)
    (hr10 : s.regs 10 = p_vv) (hr11 : s.regs 11 = p_ve)
    (hp_vv : p_vv < kv) (hp_ve : p_ve < ke)
    (hev_accV : evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p_vv = SV_acc)
    (hev_accE : evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p_ve = SE_acc)
    (hu_B : u_B < V_max δ ξ ω) :
    let tab_A : AbstractTable := ⟨ZA.card, es_A.map RawCertEntry.H⟩
    let tab_B : AbstractTable := ⟨ZB.card, es_B.map RawCertEntry.H⟩
    ∃ s' t,
      Exec w (tabsFoldBCmd δ ξ ω tab_A tab_B q_U S_A S_B S_Z pos u_B) s s' t ∧
      t ≤ 45 ∧
      s'.regs r_kv = kv + 1 ∧ s'.regs r_ke = ke + 1 ∧
      s'.regs 10 = kv ∧ s'.regs 11 = ke ∧
      ArenaWF G.numVerts (kv + 1) (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) ∧
      ArenaWF G.numEdges (ke + 1) (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) ∧
      (s'.arrs a_vkd).length = (s.arrs a_vkd).length ∧
      (s'.arrs a_ekd).length = (s.arrs a_ekd).length ∧
      (∀ p < kv,
        evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
          evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p) ∧
      (∀ p < ke,
        evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
          evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p) ∧
      evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) kv =
        SV_acc ∪ slotVertSetB (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos u_B ∧
      evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) ke =
        SE_acc ∪ slotEdgeSetB (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos u_B ∧
      (∀ r < 10, r ≠ r_kv → r ≠ r_ke → s'.regs r = s.regs r) ∧
      (∀ a, a ≠ a_vkd → a ≠ a_vv1 → a ≠ a_vv2 → a ≠ a_ekd → a ≠ a_ev1 → a ≠ a_ev2 →
        s'.arrs a = s.arrs a) := by
  intro tab_A tab_B
  have h0_w : 0 < 2 ^ w := by omega
  let rs := combineRecipesOfTabs δ tab_A tab_B q_U S_A S_B S_Z
  let idx := pos / V_max δ ξ ω
  let v := pos % V_max δ ξ ω
  unfold tabsFoldBCmd tabsSlotStepB slotVertSetB slotEdgeSetB stepSubFinset
  dsimp only [tab_A, tab_B]
  by_cases hidx : idx < rs.length
  · have hidx' : pos / V_max δ ξ ω < (combineRecipesOfTabs δ ⟨ZA.card, es_A.map RawCertEntry.H⟩ ⟨ZB.card, es_B.map RawCertEntry.H⟩ q_U S_A S_B S_Z).length := hidx
    simp only [hidx', ↓reduceDIte]
    let r := rs[idx]'hidx
    have hiB : r.idx_B.1 < es_B.length := by simpa [tab_B] using r.idx_B.2
    have hgetB : (es_B.map RawCertEntry.H)[r.idx_B.1] = es_B[r.idx_B.1].H := List.getElem_map _
    by_cases hcond : v < r.H.digraph.numVerts ∧
        u_B < (es_B.map RawCertEntry.H)[r.idx_B.1].digraph.numVerts ∧ r.owner_B u_B = v + 1
    · rcases hcond with ⟨hv, huB_lt, hown⟩
      have huB_lt' : u_B < es_B[r.idx_B.1].H.digraph.numVerts := hgetB ▸ huB_lt
      have hcond' : v < r.H.digraph.numVerts ∧
          u_B < (es_B.map RawCertEntry.H)[r.idx_B.1].digraph.numVerts ∧ r.owner_B u_B = v + 1 := ⟨hv, huB_lt, hown⟩
      have hsub : u_B < es_B[r.idx_B.1].H.digraph.numVerts ∧ r.owner_B u_B = v + 1 := ⟨huB_lt', hown⟩
      dsimp only [r, rs, idx, v, tab_A, tab_B] at hcond' hv hsub
      simp only [hcond', hsub, ↓reduceIte]
      let src := r.idx_B.1 * V_max δ ξ ω + u_B
      have hiB_C : r.idx_B.1 < C_max δ ξ ω :=
        Nat.lt_of_lt_of_le hiB (Nat.le_trans hbufB.hlen_le
          (Nat.le_of_lt (length_allDetailLeCodes_lt_C_max δ ξ ω hbufB.hq_le)))
      have hsrc_S : src < S_tab δ ξ ω := by
        unfold S_tab; have := Nat.mul_le_mul_right (V_max δ ξ ω) hiB_C
        rw [Nat.succ_mul] at this; omega
      have hsrc_w : src < 2 ^ w := by omega
      rcases (hbufB.hentries ⟨r.idx_B.1, hiB⟩).1 ⟨u_B, huB_lt'⟩ with
        ⟨hq_vv0, hev_vv0, hq_ve0, hev_ve0⟩
      dsimp [bufB] at hq_vv0 hev_vv0 hq_ve0 hev_ve0
      rw [hr_kv0] at hq_vv0; rw [hr_ke0] at hq_ve0
      let q_vv := (s₀.arrs a_rhs_vv).getD src 0
      let q_ve := (s₀.arrs a_rhs_ve).getD src 0
      have hq_vv_kv : q_vv < kv := Nat.lt_of_lt_of_le hq_vv0 hkv0_le
      have hq_ve_ke : q_ve < ke := Nat.lt_of_lt_of_le hq_ve0 hke0_le
      have hvv_len : (s₀.arrs a_rhs_vv).length = S_tab δ ξ ω := hbufB.hvv_len
      have hve_len : (s₀.arrs a_rhs_ve).length = S_tab δ ξ ω := hbufB.hve_len
      have he_vv : (Expr.read a_rhs_vv (.const src)).eval w s = some q_vv :=
        eval_read_const_of_getD hsrc_w (by omega) (by rw [hrhs_vv, hvv_len]; exact hsrc_S)
          (by rw [hrhs_vv])
      have he_ve : (Expr.read a_rhs_ve (.const src)).eval w (s.setReg 14 q_vv) = some q_ve :=
        eval_read_const_of_getD hsrc_w (by omega)
          (by simp [hrhs_ve, hve_len, hsrc_S]) (by simp [hrhs_ve, q_ve])
      exact combineFoldStepCmd_exec hw2 hkv1_w hke1_w hwfV hwfE hkv_cap hke_cap hr_kv hr_ke
        hr10 hr11 hp_vv hp_ve hev_accV hev_accE he_vv (le_refl 2) hq_vv_kv
        ((hevalV0 q_vv hq_vv0).trans hev_vv0) he_ve (le_refl 2) hq_ve_ke
        ((hevalE0 q_ve hq_ve0).trans hev_ve0)
    · have hcond' := hcond
      dsimp only [r, rs, idx, v, tab_A, tab_B] at hcond'
      simp only [hcond', ↓reduceIte]
      have hnot : ¬(v < r.H.digraph.numVerts ∧
          (u_B < es_B[r.idx_B.1].H.digraph.numVerts ∧ r.owner_B u_B = v + 1)) := by
        rintro ⟨hv, huB', hown⟩
        exact hcond ⟨hv, hgetB.symm ▸ huB', hown⟩
      have hempV : (if v < r.H.digraph.numVerts then
          if h : u_B < es_B[r.idx_B.1].H.digraph.numVerts ∧ r.owner_B u_B = v + 1 then
            es_B[r.idx_B.1].vertVerts ⟨u_B, h.1⟩ else ∅ else ∅) = ∅ := by
        split_ifs with hv h <;> [exact False.elim (hnot ⟨hv, h⟩); rfl; rfl]
      have hempE : (if v < r.H.digraph.numVerts then
          if h : u_B < es_B[r.idx_B.1].H.digraph.numVerts ∧ r.owner_B u_B = v + 1 then
            es_B[r.idx_B.1].vertEdges ⟨u_B, h.1⟩ else ∅ else ∅) = ∅ := by
        split_ifs with hv h <;> [exact False.elim (hnot ⟨hv, h⟩); rfl; rfl]
      dsimp only [r, rs, idx, v, tab_A, tab_B] at hempV hempE
      rw [hempV, hempE]
      exact combineFoldStepCmd_exec hw2 hkv1_w hke1_w hwfV hwfE hkv_cap hke_cap hr_kv hr_ke
        hr10 hr11 hp_vv hp_ve hev_accV hev_accE
        (by simp [Expr.eval, checkWord, h0_w]) (Nat.le_succ 1) hwfV.1 (evalArena_zero _ _ _ _)
        (by simp [Expr.eval, checkWord, h0_w]) (Nat.le_succ 1) hwfE.1 (evalArena_zero _ _ _ _)
  · dsimp only [rs, idx, tab_A, tab_B] at hidx
    simp only [hidx, ↓reduceDIte]
    exact combineFoldStepCmd_exec hw2 hkv1_w hke1_w hwfV hwfE hkv_cap hke_cap hr_kv hr_ke
      hr10 hr11 hp_vv hp_ve hev_accV hev_accE
      (by simp [Expr.eval, checkWord, h0_w]) (Nat.le_succ 1) hwfV.1 (evalArena_zero _ _ _ _)
      (by simp [Expr.eval, checkWord, h0_w]) (Nat.le_succ 1) hwfE.1 (evalArena_zero _ _ _ _)

theorem eval_tabsSlotEMExpr {w δ ξ ω q_U pos : ℕ} {G : ComputeDigraph}
    {ZA ZB : Finset (Fin G.numVerts)}
    {EA EB : Finset (Fin G.numEdges)}
    {es_A : List (RawCertEntry G ZA.card)}
    {es_B : List (RawCertEntry G ZB.card)}
    {S_A S_B S_Z : Finset (Fin q_U)} {s₀ s : State}
    (hbufA : ValidPieceBuffer δ ξ ω G ZA EA es_A bufA s₀)
    (hbufB : ValidPieceBuffer δ ξ ω G ZB EB es_B bufB s₀)
    (h0_w : 0 < 2 ^ w) (hm_w : G.numEdges < 2 ^ w) (hS_w : S_tab δ ξ ω < 2 ^ w)
    (hacc_em : s.arrs a_acc_em = s₀.arrs a_acc_em)
    (hrhs_em : s.arrs a_rhs_em = s₀.arrs a_rhs_em) :
    let tab_A : AbstractTable := ⟨ZA.card, es_A.map RawCertEntry.H⟩
    let tab_B : AbstractTable := ⟨ZB.card, es_B.map RawCertEntry.H⟩
    let e_em := tabsSlotEMExpr δ ξ ω tab_A tab_B q_U S_A S_B S_Z pos
    let val := slotTargetEM (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos
    e_em.eval w s = some val ∧ e_em.cost ≤ 2 ∧ val ≤ G.numEdges := by
  intro tab_A tab_B e_em val
  let rs := combineRecipesOfTabs δ tab_A tab_B q_U S_A S_B S_Z
  let idx := pos / V_max δ ξ ω
  let d := pos % V_max δ ξ ω
  dsimp only [e_em, val]
  unfold tabsSlotEMExpr slotTargetEM
  dsimp only [tab_A, tab_B]
  by_cases hidx : idx < rs.length
  · have hidx' : pos / V_max δ ξ ω < (combineRecipesOfTabs δ ⟨ZA.card, es_A.map RawCertEntry.H⟩ ⟨ZB.card, es_B.map RawCertEntry.H⟩ q_U S_A S_B S_Z).length := hidx
    simp only [hidx', ↓reduceDIte]
    let r := rs[idx]'hidx
    have hr_mem : r ∈ rs := List.getElem_mem hidx
    have hiA : r.idx_A.1 < es_A.length := by simpa [tab_A] using r.idx_A.2
    have hiB : r.idx_B.1 < es_B.length := by simpa [tab_B] using r.idx_B.2
    have hgetA : (es_A.map RawCertEntry.H)[r.idx_A.1] = es_A[r.idx_A.1].H := List.getElem_map _
    have hgetB : (es_B.map RawCertEntry.H)[r.idx_B.1] = es_B[r.idx_B.1].H := List.getElem_map _
    have hdetA : es_A[r.idx_A.1].H.HasDetailLe δ := hbufA.hdet _ (List.getElem_mem hiA)
    have hdetB : es_B[r.idx_B.1].H.HasDetailLe δ := hbufB.hdet _ (List.getElem_mem hiB)
    by_cases hd : d < r.H.digraph.numEdges
    · have hd' := hd
      dsimp only [r, rs, idx, d, tab_A, tab_B] at hd'
      simp only [hd', ↓reduceIte, ↓reduceDIte]
      unfold CombineEntryRecipe.eval
      dsimp only
      have hm_A_eq : (es_A.map RawCertEntry.H)[r.idx_A.1].digraph.numEdges = es_A[r.idx_A.1].H.digraph.numEdges :=
        congrArg (fun X => X.digraph.numEdges) hgetA
      by_cases hd_A : d < (es_A.map RawCertEntry.H)[r.idx_A.1].digraph.numEdges
      · have hd_A' : d < es_A[r.idx_A.1].H.digraph.numEdges := hm_A_eq ▸ hd_A
        have hd_A0 := hd_A
        have hd_A1 := hd_A'
        dsimp only [r, rs, idx, d, tab_A, tab_B] at hd_A0 hd_A1
        simp only [hd_A0, hd_A1, ↓reduceIte, ↓reduceDIte]
        let src := r.idx_A.1 * V_max δ ξ ω + d
        have hiA_C : r.idx_A.1 < C_max δ ξ ω :=
          Nat.lt_of_lt_of_le hiA (Nat.le_trans hbufA.hlen_le
            (Nat.le_of_lt (length_allDetailLeCodes_lt_C_max δ ξ ω hbufA.hq_le)))
        have hd_V : d < V_max δ ξ ω := Nat.lt_trans hd_A' (numEdges_lt_V_max hdetA)
        have hsrc_S : src < S_tab δ ξ ω := by
          unfold S_tab; have := Nat.mul_le_mul_right (V_max δ ξ ω) hiA_C
          rw [Nat.succ_mul] at this; omega
        have hem_get := (hbufA.hentries ⟨r.idx_A.1, hiA⟩).2 ⟨d, hd_A'⟩
        dsimp [bufA] at hem_get
        have he_lt := (es_A[r.idx_A.1].edgeMap ⟨d, hd_A'⟩).2
        have hem_lenA : (s₀.arrs a_acc_em).length = S_tab δ ξ ω := hbufA.hem_len
        refine ⟨eval_read_const_of_getD (Nat.lt_trans hsrc_S hS_w) (Nat.lt_trans he_lt hm_w)
          (by rw [hacc_em, hem_lenA]; exact hsrc_S) (by rw [hacc_em]; exact hem_get),
          le_refl 2, le_of_lt he_lt⟩
      · have hd_A' : ¬(d < es_A[r.idx_A.1].H.digraph.numEdges) := hm_A_eq ▸ hd_A
        have hd_A0 := hd_A
        have hd_A1 := hd_A'
        dsimp only [r, rs, idx, d, tab_A, tab_B] at hd_A0 hd_A1
        simp only [hd_A0, hd_A1, ↓reduceIte, ↓reduceDIte]
        let d_B := d - es_A[r.idx_A.1].H.digraph.numEdges
        have hd_B_eq : d - (es_A.map RawCertEntry.H)[r.idx_A.1].digraph.numEdges = d_B := by rw [hm_A_eq]
        dsimp only [r, rs, idx, d, tab_A, tab_B] at hd_B_eq
        rw [hd_B_eq]
        have hd_B_lt : d_B < es_B[r.idx_B.1].H.digraph.numEdges := by
          have hsum := r.h_edges
          rw [hgetA, hgetB] at hsum
          omega
        let src := r.idx_B.1 * V_max δ ξ ω + d_B
        have hiB_C : r.idx_B.1 < C_max δ ξ ω :=
          Nat.lt_of_lt_of_le hiB (Nat.le_trans hbufB.hlen_le
            (Nat.le_of_lt (length_allDetailLeCodes_lt_C_max δ ξ ω hbufB.hq_le)))
        have hdB_V : d_B < V_max δ ξ ω := Nat.lt_trans hd_B_lt (numEdges_lt_V_max hdetB)
        have hsrc_S : src < S_tab δ ξ ω := by
          unfold S_tab; have := Nat.mul_le_mul_right (V_max δ ξ ω) hiB_C
          rw [Nat.succ_mul] at this; omega
        have hem_get := (hbufB.hentries ⟨r.idx_B.1, hiB⟩).2 ⟨d_B, hd_B_lt⟩
        dsimp [bufB] at hem_get
        have he_lt := (es_B[r.idx_B.1].edgeMap ⟨d_B, hd_B_lt⟩).2
        have hem_lenB : (s₀.arrs a_rhs_em).length = S_tab δ ξ ω := hbufB.hem_len
        refine ⟨eval_read_const_of_getD (Nat.lt_trans hsrc_S hS_w) (Nat.lt_trans he_lt hm_w)
          (by rw [hrhs_em, hem_lenB]; exact hsrc_S) (by rw [hrhs_em]; exact hem_get),
          le_refl 2, le_of_lt he_lt⟩
    · dsimp only [r, rs, idx, d, tab_A, tab_B] at hd
      simp only [hd, ↓reduceIte, ↓reduceDIte]
      exact ⟨by simp [Expr.eval, checkWord, h0_w], Nat.le_succ 1, Nat.zero_le _⟩
  · dsimp only [rs, idx, tab_A, tab_B] at hidx
    simp only [hidx, ↓reduceDIte]
    exact ⟨by simp [Expr.eval, checkWord, h0_w], Nat.le_succ 1, Nat.zero_le _⟩

end GraphMinor.Compute
