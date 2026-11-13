module

public import GraphMinor.Compute.Algorithm41Aux1

/-!
# Finite Lookup Tables and Abstract Folio Operations for GM XIII (4.1)

This file builds the finite lookup tables used by the Word RAM implementation of Algorithm (4.1)
of Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem* (pages 75–76), and
proves that they agree with the specification operations `baseCertFolioTable` and
`combinePieceTables`:

1. Base-`B` digit packing (`packBase`, `unpackBase`), Word RAM bounded table-lookup branching
   (`branchOnBound`, `Exec.branchOnBound`), and `bitSetList` update lemmas (`bitSetList_empty41`,
   `bitSetList_set_one`).
2. Canonical index-subset representation (`subMaskFinset`) proving that `finsetSubIdx` depends
   only on the membership mask of a subset `U ⊆ W` inside `Fin W.card`.
3. Purely combinatorial combination recipes (`CombineEntryRecipe`, `abstractCombineRecipes`) that
   compute the combined folio and parent-model pointers from two abstract folio tables and a 3-bit
   boundary mask, together with the proof (`combinePieceTables_toSigmaRaw_eq`) that evaluating
   these recipes produces `(combinePieceTables ... T_A T_B).toSigmaRaw`.
4. Purely combinatorial base tables (`locDigraph`, `locRootSet`, `abstractBaseTable`) on local
   configurations of `≤ 2` vertices and `≤ 1` edge, together with the proof
   (`baseCertFolioTable_toSigmaRaw_eq`) that transporting the local table along `finsetRootFn VA`
   and `finsetRootFn EA` produces `(baseCertFolioTable G VA EA (finsetRootFn ZA) δ).toSigmaRaw`.
5. Bounded integer encoding (`encAbstractTable`, `decAbstractTable`) of abstract folio tables of
   detail `≤ δ` and root size `≤ Q_max ξ ω = 2 + 4 * (ω + ξ)`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Base-`B` Packing, `branchOnBound`, and `bitSetList` Update Lemmas -/

/-- Pack a list of digits `< B` into a single natural number in base `B` (least significant digit
first). -/
def packBase (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + B * packBase B ds

/-- Unpack `k` base-`B` digits from a natural number `x`. -/
def unpackBase (B : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, x => (x % B) :: unpackBase B k (x / B)

@[simp]
theorem length_unpackBase (B k x : ℕ) : (unpackBase B k x).length = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [unpackBase, ih]

theorem packBase_lt {B : ℕ} (hB : 0 < B) :
    ∀ (ds : List ℕ), (∀ d ∈ ds, d < B) → packBase B ds < B ^ ds.length
  | [], _ => by simp [packBase]
  | d :: ds, h => by
    have hd : d < B := h d List.mem_cons_self
    have hds : packBase B ds < B ^ ds.length :=
      packBase_lt hB ds (fun x hx => h x (List.mem_cons_of_mem d hx))
    simp only [packBase, List.length_cons, Nat.pow_succ']
    have hmul : B * (packBase B ds + 1) ≤ B * B ^ ds.length :=
      Nat.mul_le_mul_left B hds
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega

theorem unpackBase_packBase {B : ℕ} :
    ∀ (ds : List ℕ), (∀ d ∈ ds, d < B) → unpackBase B ds.length (packBase B ds) = ds
  | [], _ => rfl
  | d :: ds, h => by
    have hd : d < B := h d List.mem_cons_self
    have hB : 0 < B := by omega
    simp only [List.length_cons, packBase, unpackBase]
    have hmod : (d + B * packBase B ds) % B = d := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
    have hdiv : (d + B * packBase B ds) / B = packBase B ds := by
      rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hd, Nat.zero_add]
    rw [hmod, hdiv, unpackBase_packBase ds (fun x hx => h x (List.mem_cons_of_mem d hx))]

/-- Cascade of `if r_in == k then body k else ...` for `k ∈ [0, K)`, implementing constant-time
finite table lookup in the Word RAM language. -/
def branchOnBound : ℕ → Reg → (ℕ → Cmd) → Cmd
  | 0, _, _ => .skip
  | k + 1, r_in, body =>
    .ite (.op .eq (.reg r_in) (.const k)) (body k) (branchOnBound k r_in body)

theorem Exec.branchOnBound {w K : ℕ} {r_in : Reg} {body : ℕ → Cmd}
    {s s' : State} {x t : ℕ}
    (hw : 0 < w) (hK : K < 2 ^ w) (hr : s.regs r_in = x) (hx : x < K)
    (hbody : Exec w (body x) s s' t) :
    ∃ t' ≤ 3 * K + t, Exec w (branchOnBound K r_in body) s s' t' := by
  induction K with
  | zero => omega
  | succ k ih =>
    have h1_lt : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
    have h0_lt : 0 < 2 ^ w := by omega
    have hx_lt_w : x < 2 ^ w := by omega
    have hk_lt_w : k < 2 ^ w := by omega
    by_cases hxk : x = k
    · subst hxk
      have hcond : (Expr.op .eq (.reg r_in) (.const x)).eval w s = some 1 := by
        simp [Expr.eval, hr, BinOp.eval, BinOp.raw, checkWord_of_lt hx_lt_w,
          checkWord_of_lt h1_lt]
      refine ⟨3 + t, by omega, Exec.ite_true hcond (by omega) hbody⟩
    · have hx_lt_k : x < k := by omega
      have hcond : (Expr.op .eq (.reg r_in) (.const k)).eval w s = some 0 := by
        simp [Expr.eval, hr, hxk, BinOp.eval, BinOp.raw, checkWord_of_lt hx_lt_w,
          checkWord_of_lt hk_lt_w, checkWord_of_lt h0_lt]
      rcases ih (by omega) hx_lt_k with ⟨t₀, ht₀, hexec₀⟩
      refine ⟨3 + t₀, by omega, Exec.ite_false hcond hexec₀⟩

@[simp]
theorem bitSetList_empty41 (n : ℕ) :
    bitSetList (∅ : Finset (Fin n)) = List.replicate n 0 := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [bitSetList]

theorem bitSetList_set_one {n : ℕ} (S : Finset (Fin n)) (u : Fin n) :
    (bitSetList S).set u.1 1 = bitSetList (insert u S) := by
  have h1 : IsBitSet S 0 ((initState []).setArr 0 (bitSetList S)) :=
    IsBitSet.of_bitSetList S 0 _ (by simp)
  have h2 := h1.write_one u
  simpa [State.writeArr] using h2.arr_eq_bitSetList

/-! ### Section 2: Canonical Index Subsets (`subMaskFinset`) and `finsetSubIdx` -/

theorem finsetToFinList_eq_map_finsetRootFn {n : ℕ} (W : Finset (Fin n)) :
    finsetToFinList W = (List.finRange W.card).map (finsetRootFn W) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [finsetRootFn, finsetEnumEquiv]

@[simp]
theorem finsetToFinList_univ (n : ℕ) :
    finsetToFinList (Finset.univ : Finset (Fin n)) = List.finRange n := by
  simp [finsetToFinList]

@[simp]
theorem finsetRootFn_univ (n : ℕ) (i : Fin (Finset.univ : Finset (Fin n)).card) :
    finsetRootFn (Finset.univ : Finset (Fin n)) i = ⟨i.1, by simpa using i.2⟩ := by
  ext
  simp [finsetRootFn, finsetEnumEquiv]
  rfl

/-- For `U ⊆ W : Finset (Fin n)`, the subset of indices in `Fin W.card` whose elements lie in `U`. -/
def subMaskFinset {n : ℕ} (W U : Finset (Fin n)) : Finset (Fin W.card) :=
  Finset.univ.filter (fun k : Fin W.card => finsetRootFn W k ∈ U)

theorem finsetToFinList_sub_eq_map {n : ℕ} {W U : Finset (Fin n)} (hUW : U ⊆ W) :
    finsetToFinList U = (finsetToFinList (subMaskFinset W U)).map (finsetRootFn W) := by
  have h1 : (finsetToFinList W).filter (· ∈ U) = finsetToFinList U := by
    simp only [finsetToFinList, List.filter_filter]
    congr 1
    funext x
    by_cases hx : x ∈ U
    · simp [hx, hUW hx]
    · simp [hx]
  have h2 : (finsetToFinList W).filter (· ∈ U) =
      (finsetToFinList (subMaskFinset W U)).map (finsetRootFn W) := by
    rw [finsetToFinList_eq_map_finsetRootFn W, List.filter_map]
    congr 1
    simp only [finsetToFinList, subMaskFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  exact h1.symm.trans h2

theorem card_subMaskFinset {n : ℕ} {W U : Finset (Fin n)} (hUW : U ⊆ W) :
    (subMaskFinset W U).card = U.card := by
  have h := congrArg List.length (finsetToFinList_sub_eq_map hUW)
  simpa using h.symm

theorem finsetSubIdx_eq_finsetRootFn_subMaskFinset {n : ℕ} {W U : Finset (Fin n)}
    (hUW : U ⊆ W) (i : Fin U.card) :
    finsetSubIdx hUW i =
      finsetRootFn (subMaskFinset W U) ⟨i.1, (card_subMaskFinset hUW).symm ▸ i.2⟩ := by
  apply finsetRootFn_injective W
  rw [finsetRootFn_finsetSubIdx_apply]
  have h := finsetToFinList_sub_eq_map hUW
  have hi_U : i.1 < (finsetToFinList U).length := by simp [i.2]
  have hget := List.getElem_of_eq h hi_U
  simpa [finsetRootFn, finsetEnumEquiv] using hget

theorem finsetRootFn_sub_apply {n : ℕ} {W U : Finset (Fin n)}
    (hUW : U ⊆ W) (i : Fin U.card) :
    finsetRootFn U i =
      finsetRootFn W (finsetRootFn (subMaskFinset W U) ⟨i.1, (card_subMaskFinset hUW).symm ▸ i.2⟩) := by
  rw [← finsetSubIdx_eq_finsetRootFn_subMaskFinset hUW i, finsetRootFn_finsetSubIdx_apply]

/-! ### Section 3: Type-Erased Folio Tables (`toSigmaRaw`) and Abstract Combine Recipes -/

/-- Type-erased representation `⟨q, T.toRawList⟩` of a `CertFolioTable G VA EA r δ`, whose type
`Σ q, List (RawCertEntry G q)` is completely independent of `VA`, `EA`, and `r`. -/
def CertFolioTable.toSigmaRaw {q : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {δ : ℕ}
    (T : CertFolioTable G VA EA r δ) : Σ q', List (RawCertEntry G q') :=
  ⟨q, T.toRawList⟩

@[simp]
theorem CertFolioTable.toSigmaRaw_castSets {G : ComputeDigraph}
    {VA₁ VA₂ : Finset (Fin G.numVerts)} {EA₁ EA₂ : Finset (Fin G.numEdges)}
    {Z₁ Z₂ : Finset (Fin G.numVerts)} {δ : ℕ}
    (hV : VA₁ = VA₂) (hE : EA₁ = EA₂) (hZ : Z₁ = Z₂)
    (T : CertFolioTable G VA₁ EA₁ (finsetRootFn Z₁) δ) :
    (T.castSets hV hE hZ).toSigmaRaw = T.toSigmaRaw := by
  subst hV hE hZ
  rfl

@[simp]
theorem CertFolioTable.toRawList_rec_r {q : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r₁ r₂ : Fin q → Fin G.numVerts} {δ : ℕ}
    (hr : r₁ = r₂) (T : CertFolioTable G VA EA r₁ δ) :
    (hr ▸ T).toRawList = T.toRawList := by
  subst hr
  rfl

/-- Encode the `FolioSetRep` part of `s : Σ q, List (RawCertEntry G q)`. -/
def encSigmaRawFolio {G : ComputeDigraph} (s : Σ q, List (RawCertEntry G q)) : List ℕ :=
  let codes := s.2.map (fun e => encRootedDigraph e.H)
  codes.length :: codes.flatMap (fun c => c.length :: c)

/-- Encode the models part of `s : Σ q, List (RawCertEntry G q)`. -/
def encSigmaRawModels {G : ComputeDigraph} (s : Σ q, List (RawCertEntry G q)) : List ℕ :=
  encRawCertModels s.2

theorem encSigmaRawFolio_toSigmaRaw {q : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {δ : ℕ}
    (T : CertFolioTable G VA EA r δ) :
    encSigmaRawFolio T.toSigmaRaw = encFolioSetRep T.toFolioSetRep := by
  simp [encSigmaRawFolio, CertFolioTable.toSigmaRaw, CertFolioTable.toRawList,
    encFolioSetRep, CertFolioTable.toFolioSetRep, Function.comp_def, CertFolioEntry.toRaw]

theorem encSigmaRawModels_toSigmaRaw {q : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {δ : ℕ}
    (T : CertFolioTable G VA EA r δ) :
    encSigmaRawModels T.toSigmaRaw = encRawCertModels T.toRawList :=
  rfl

/-- Generic deduplication of a list by rooted digraph isomorphism along `projH : α → ComputeRootedDigraph q`. -/
def dedupByIso {q : ℕ} {α : Type*} (projH : α → ComputeRootedDigraph q) : List α → List α
  | [] => []
  | x :: xs =>
    if (dedupByIso projH xs).any (fun x' => decide (IsRootedDigraphIso (projH x) (projH x'))) then
      dedupByIso projH xs
    else
      x :: dedupByIso projH xs

theorem dedupCertEntries_eq_dedupByIso {q : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts} {δ : ℕ}
    (es : List (CertFolioEntry G VA EA r δ)) :
    dedupCertEntries es = dedupByIso (·.H) es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    unfold dedupCertEntries dedupByIso
    rw [ih]

theorem dedupByIso_map {q : ℕ} {α β : Type*}
    (projα : α → ComputeRootedDigraph q) (projβ : β → ComputeRootedDigraph q)
    (f : α → β) (hf : ∀ x, projβ (f x) = projα x) :
    ∀ (xs : List α), (dedupByIso projα xs).map f = dedupByIso projβ (xs.map f)
  | [] => rfl
  | x :: xs => by
    simp only [dedupByIso, List.map_cons, ← dedupByIso_map projα projβ f hf xs,
      List.any_map, Function.comp_def, hf]
    split_ifs <;> simp

/-- Glue two `RawCertEntry`s along `(α_A, α_B, hcov)` (type-erased counterpart of
`PieceRootedModel.glue`). -/
def rawGlue {q q_A q_B : ℕ} {G : ComputeDigraph}
    (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (raw_A : RawCertEntry G q_A) (raw_B : RawCertEntry G q_B) :
    RawCertEntry G q where
  H := glueRootedDigraphs α_A α_B hcov raw_A.H raw_B.H
  vertVerts c :=
    (Finset.univ.filter (fun x : Fin raw_A.H.digraph.numVerts ⊕ Fin raw_B.H.digraph.numVerts =>
      glueClassIdx α_A α_B raw_A.H raw_B.H x = c)).biUnion
      (fun x => match x with | Sum.inl u_A => raw_A.vertVerts u_A | Sum.inr u_B => raw_B.vertVerts u_B)
  vertEdges c :=
    (Finset.univ.filter (fun x : Fin raw_A.H.digraph.numVerts ⊕ Fin raw_B.H.digraph.numVerts =>
      glueClassIdx α_A α_B raw_A.H raw_B.H x = c)).biUnion
      (fun x => match x with | Sum.inl u_A => raw_A.vertEdges u_A | Sum.inr u_B => raw_B.vertEdges u_B)
  edgeMap e :=
    match finSumFinEquiv.symm e with
    | Sum.inl e_A => raw_A.edgeMap e_A
    | Sum.inr e_B => raw_B.edgeMap e_B

/-- Restrict a `RawCertEntry G q` along `β : Fin q' → Fin q` and `U ⊆ V(H)` (type-erased
counterpart of `PieceRootedModel.restrict`). -/
def rawRestrict {q q' : ℕ} {G : ComputeDigraph}
    (raw : RawCertEntry G q) (β : Fin q' → Fin q)
    (U : Finset (Fin raw.H.digraph.numVerts))
    (hU : IsValidRootedSubverts raw.H β U) :
    RawCertEntry G q' where
  H := restrictRootedDigraph raw.H β U hU
  vertVerts v := raw.vertVerts ((finsetEnumEquiv U v).1)
  vertEdges v := raw.vertEdges ((finsetEnumEquiv U v).1)
  edgeMap e := raw.edgeMap e

/-- Type-erased counterpart of `combineEntryPair`. -/
def rawCombineEntryPair {q q_A q_B q' : ℕ} {G : ComputeDigraph}
    (δ : ℕ) (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (β : Fin q' → Fin q)
    (raw_A : RawCertEntry G q_A) (raw_B : RawCertEntry G q_B) :
    List (RawCertEntry G q') :=
  let raw_AB := rawGlue α_A α_B hcov raw_A raw_B
  (finsetSubsets (Finset.univ : Finset (Fin raw_AB.H.digraph.numVerts))).filterMap (fun U =>
    if hU : IsValidRootedSubverts raw_AB.H β U then
      let raw' := rawRestrict raw_AB β U hU
      if raw'.H.HasDetailLe δ then
        some raw'
      else
        none
    else
      none)

/-- Type-erased counterpart of `combineCertFolioTable`. -/
def rawCombineTables {q q_A q_B q' : ℕ} {G : ComputeDigraph}
    (δ : ℕ) (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (β : Fin q' → Fin q)
    (es_A : List (RawCertEntry G q_A)) (es_B : List (RawCertEntry G q_B)) :
    List (RawCertEntry G q') :=
  dedupByIso (·.H) (es_A.flatMap (fun raw_A =>
    es_B.flatMap (fun raw_B =>
      rawCombineEntryPair δ α_A α_B hcov β raw_A raw_B)))

theorem map_toRaw_combineEntryPair {q q_A q_B q' δ : ℕ} {G : ComputeDigraph}
    {VA VB : Finset (Fin G.numVerts)} {EA EB : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts}
    {α_A : Fin q_A → Fin q} {α_B : Fin q_B → Fin q}
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (hE_disj : Disjoint EA EB)
    (hsep_inter : ∀ w ∈ VA ∩ VB, ∃ (i_A : Fin q_A) (i_B : Fin q_B),
      α_A i_A = α_B i_B ∧ r (α_A i_A) = w)
    (β : Fin q' → Fin q)
    (e_A : CertFolioEntry G VA EA (r ∘ α_A) δ)
    (e_B : CertFolioEntry G VB EB (r ∘ α_B) δ) :
    (combineEntryPair hcov hE_disj hsep_inter β e_A e_B).map CertFolioEntry.toRaw =
      rawCombineEntryPair δ α_A α_B hcov β e_A.toRaw e_B.toRaw := by
  unfold combineEntryPair rawCombineEntryPair
  dsimp only
  rw [List.map_filterMap]
  congr 1
  funext U
  dsimp only [rawGlue, rawRestrict, CertFolioEntry.toRaw, Function.comp_def]
  by_cases hU : IsValidRootedSubverts (glueRootedDigraphs α_A α_B hcov e_A.H e_B.H) β U
  · by_cases hdet : (restrictRootedDigraph (glueRootedDigraphs α_A α_B hcov e_A.H e_B.H) β U hU).HasDetailLe δ
    · simp only [hU, hdet, ↓reduceDIte, ↓reduceIte, Option.map_some]
      congr 1
      unfold CertFolioEntry.toRaw PieceRootedModel.restrict PieceRootedModel.glue
      dsimp only
      congr 1
      · funext v
        refine Finset.biUnion_congr rfl fun x _ => ?_
        rcases x with u_A | u_B <;> rfl
      · funext v
        refine Finset.biUnion_congr rfl fun x _ => ?_
        rcases x with u_A | u_B <;> rfl
      · funext e
        rcases finSumFinEquiv.symm e with e_A₁ | e_B₁ <;> rfl
    · simp only [hU, hdet, ↓reduceDIte, ↓reduceIte, Option.map_none]
  · simp only [hU, ↓reduceDIte, Option.map_none]

theorem toRawList_combineCertFolioTable {q q_A q_B q' δ : ℕ} {G : ComputeDigraph}
    {VA VB : Finset (Fin G.numVerts)} {EA EB : Finset (Fin G.numEdges)}
    {r : Fin q → Fin G.numVerts}
    {α_A : Fin q_A → Fin q} {α_B : Fin q_B → Fin q}
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (hE_disj : Disjoint EA EB)
    (hEA : ∀ e ∈ EA, G.head e ∈ VA ∧ G.tail e ∈ VA)
    (hEB : ∀ e ∈ EB, G.head e ∈ VB ∧ G.tail e ∈ VB)
    (hrA : ∀ i_A : Fin q_A, r (α_A i_A) ∈ VA)
    (hrB : ∀ i_B : Fin q_B, r (α_B i_B) ∈ VB)
    (hsep : ∀ x ∈ VA, x ∈ VB → ∃ i_A i_B, α_A i_A = α_B i_B ∧ r (α_A i_A) = x)
    (β : Fin q' → Fin q)
    (T_A : CertFolioTable G VA EA (r ∘ α_A) δ)
    (T_B : CertFolioTable G VB EB (r ∘ α_B) δ) :
    (combineCertFolioTable hcov hE_disj hEA hEB hrA hrB hsep β T_A T_B).toRawList =
      rawCombineTables δ α_A α_B hcov β T_A.toRawList T_B.toRawList := by
  unfold CertFolioTable.toRawList combineCertFolioTable rawCombineTables
  dsimp only
  rw [dedupCertEntries_eq_dedupByIso,
      dedupByIso_map (·.H) (·.H) CertFolioEntry.toRaw (fun _ => rfl)]
  congr 1
  rw [List.map_flatMap, List.flatMap_map]
  congr 1
  funext e_A
  rw [List.map_flatMap, List.flatMap_map]
  congr 1
  funext e_B
  exact map_toRaw_combineEntryPair hcov hE_disj _ β e_A e_B

theorem toRawList_combinePieceTables {G : ComputeDigraph}
    {VA VB ZA ZB Z' : Finset (Fin G.numVerts)}
    {EA EB : Finset (Fin G.numEdges)} {δ : ℕ}
    (hZA : ZA ⊆ VA) (hZB : ZB ⊆ VB) (hZ' : Z' ⊆ ZA ∪ ZB)
    (hE_disj : Disjoint EA EB)
    (hEA : ∀ e ∈ EA, G.head e ∈ VA ∧ G.tail e ∈ VA)
    (hEB : ∀ e ∈ EB, G.head e ∈ VB ∧ G.tail e ∈ VB)
    (hinter : VA ∩ VB ⊆ ZA ∩ ZB)
    (T_A : CertFolioTable G VA EA (finsetRootFn ZA) δ)
    (T_B : CertFolioTable G VB EB (finsetRootFn ZB) δ) :
    (combinePieceTables hZA hZB hZ' hE_disj hEA hEB hinter T_A T_B).toRawList =
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
      rawCombineTables δ α_A α_B hcov β T_A.toRawList T_B.toRawList := by
  unfold combinePieceTables
  dsimp only
  rw [CertFolioTable.toRawList_rec_r, toRawList_combineCertFolioTable,
      CertFolioTable.toRawList_rec_r, CertFolioTable.toRawList_rec_r]

/-- Abstract recipe for constructing one combined `RawCertEntry G q'` from `es_A[idx_A]` and
`es_B[idx_B]`. This structure depends only on the abstract lists of rooted digraphs `Hs_A` and
`Hs_B`, not on `G` or the piece subgraphs. -/
structure CombineEntryRecipe {q_A q_B : ℕ}
    (Hs_A : List (ComputeRootedDigraph q_A))
    (Hs_B : List (ComputeRootedDigraph q_B))
    (q' : ℕ) where
  /-- Resulting `q'`-rooted digraph `H'`. -/
  H : ComputeRootedDigraph q'
  /-- Index of the left parent entry in `Hs_A`. -/
  idx_A : Fin Hs_A.length
  /-- Index of the right parent entry in `Hs_B`. -/
  idx_B : Fin Hs_B.length
  /-- Number of edges of `H` equals the sum of the edge counts of the two parent entries. -/
  h_edges : H.digraph.numEdges =
    Hs_A[idx_A.1].digraph.numEdges + Hs_B[idx_B.1].digraph.numEdges
  /-- For each vertex `u_A` of `Hs_A[idx_A]`, `owner_A u_A = v + 1` if `u_A` is merged into
  vertex `v : Fin H.digraph.numVerts`, or `0` if `u_A` is dropped. -/
  owner_A : ℕ → ℕ
  /-- For each vertex `u_B` of `Hs_B[idx_B]`, `owner_B u_B = v + 1` if `u_B` is merged into
  vertex `v : Fin H.digraph.numVerts`, or `0` if `u_B` is dropped. -/
  owner_B : ℕ → ℕ

/-- Evaluate a `CombineEntryRecipe` on concrete lists `es_A` and `es_B` whose `.H` projections match
`Hs_A` and `Hs_B`. -/
def CombineEntryRecipe.eval {q_A q_B q' : ℕ} {G : ComputeDigraph}
    {Hs_A : List (ComputeRootedDigraph q_A)}
    {Hs_B : List (ComputeRootedDigraph q_B)}
    (r : CombineEntryRecipe Hs_A Hs_B q')
    (es_A : List (RawCertEntry G q_A))
    (es_B : List (RawCertEntry G q_B))
    (hes_A : es_A.map (·.H) = Hs_A)
    (hes_B : es_B.map (·.H) = Hs_B) :
    RawCertEntry G q' :=
  have hlen_A : es_A.length = Hs_A.length := by rw [← hes_A, List.length_map]
  have hlen_B : es_B.length = Hs_B.length := by rw [← hes_B, List.length_map]
  let raw_A := es_A[r.idx_A.1]'(by rw [hlen_A]; exact r.idx_A.2)
  let raw_B := es_B[r.idx_B.1]'(by rw [hlen_B]; exact r.idx_B.2)
  have hm_A : raw_A.H.digraph.numEdges = Hs_A[r.idx_A.1].digraph.numEdges := by
    have h := List.getElem_of_eq hes_A.symm r.idx_A.2
    rw [List.getElem_map] at h
    exact congrArg (fun X => X.digraph.numEdges) h.symm
  have hm_B : raw_B.H.digraph.numEdges = Hs_B[r.idx_B.1].digraph.numEdges := by
    have h := List.getElem_of_eq hes_B.symm r.idx_B.2
    rw [List.getElem_map] at h
    exact congrArg (fun X => X.digraph.numEdges) h.symm
  { H := r.H
    vertVerts := fun v =>
      (Finset.univ.filter (fun u_A : Fin raw_A.H.digraph.numVerts =>
        r.owner_A u_A.1 = v.1 + 1)).biUnion raw_A.vertVerts ∪
      (Finset.univ.filter (fun u_B : Fin raw_B.H.digraph.numVerts =>
        r.owner_B u_B.1 = v.1 + 1)).biUnion raw_B.vertVerts
    vertEdges := fun v =>
      (Finset.univ.filter (fun u_A : Fin raw_A.H.digraph.numVerts =>
        r.owner_A u_A.1 = v.1 + 1)).biUnion raw_A.vertEdges ∪
      (Finset.univ.filter (fun u_B : Fin raw_B.H.digraph.numVerts =>
        r.owner_B u_B.1 = v.1 + 1)).biUnion raw_B.vertEdges
    edgeMap := fun e =>
      if h : e.1 < raw_A.H.digraph.numEdges then
        raw_A.edgeMap ⟨e.1, h⟩
      else
        raw_B.edgeMap ⟨e.1 - raw_A.H.digraph.numEdges, by
          have he := e.2
          have hsum := r.h_edges
          omega⟩ }

/-- Build a single `CombineEntryRecipe` for `(idx_A, idx_B, U, hU)`. -/
def mkCombineRecipe {q q_A q_B q' : ℕ}
    (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (β : Fin q' → Fin q)
    (Hs_A : List (ComputeRootedDigraph q_A))
    (Hs_B : List (ComputeRootedDigraph q_B))
    (idx_A : Fin Hs_A.length) (idx_B : Fin Hs_B.length)
    (H_A : ComputeRootedDigraph q_A) (H_B : ComputeRootedDigraph q_B)
    (hA : H_A = Hs_A[idx_A.1]) (hB : H_B = Hs_B[idx_B.1])
    (U : Finset (Fin (glueRootedDigraphs α_A α_B hcov H_A H_B).digraph.numVerts))
    (hU : IsValidRootedSubverts (glueRootedDigraphs α_A α_B hcov H_A H_B) β U) :
    CombineEntryRecipe Hs_A Hs_B q' :=
  let H_AB := glueRootedDigraphs α_A α_B hcov H_A H_B
  { H := restrictRootedDigraph H_AB β U hU
    idx_A := idx_A
    idx_B := idx_B
    h_edges := by
      change H_A.digraph.numEdges + H_B.digraph.numEdges =
        Hs_A[idx_A.1].digraph.numEdges + Hs_B[idx_B.1].digraph.numEdges
      rw [hA, hB]
    owner_A := fun u_A =>
      if hu : u_A < H_A.digraph.numVerts then
        let c := glueClassIdx α_A α_B H_A H_B (Sum.inl ⟨u_A, hu⟩)
        if hc : c ∈ U then ((finsetEnumEquiv U).symm ⟨c, hc⟩).1 + 1 else 0
      else 0
    owner_B := fun u_B =>
      if hu : u_B < H_B.digraph.numVerts then
        let c := glueClassIdx α_A α_B H_A H_B (Sum.inr ⟨u_B, hu⟩)
        if hc : c ∈ U then ((finsetEnumEquiv U).symm ⟨c, hc⟩).1 + 1 else 0
      else 0 }

/-- Abstract candidate recipes generated from `(idx_A, idx_B)` with explicit digraphs `H_A, H_B`. -/
def abstractCombineEntryPairAux {q q_A q_B q' : ℕ}
    (δ : ℕ) (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (β : Fin q' → Fin q)
    (Hs_A : List (ComputeRootedDigraph q_A))
    (Hs_B : List (ComputeRootedDigraph q_B))
    (idx_A : Fin Hs_A.length) (idx_B : Fin Hs_B.length)
    (H_A : ComputeRootedDigraph q_A) (H_B : ComputeRootedDigraph q_B)
    (hA : H_A = Hs_A[idx_A.1]) (hB : H_B = Hs_B[idx_B.1]) :
    List (CombineEntryRecipe Hs_A Hs_B q') :=
  let H_AB := glueRootedDigraphs α_A α_B hcov H_A H_B
  (finsetSubsets (Finset.univ : Finset (Fin H_AB.digraph.numVerts))).filterMap (fun U =>
    if hU : IsValidRootedSubverts H_AB β U then
      let r := mkCombineRecipe α_A α_B hcov β Hs_A Hs_B idx_A idx_B H_A H_B hA hB U hU
      if r.H.HasDetailLe δ then
        some r
      else
        none
    else
      none)

/-- Abstract candidate recipes generated from `(idx_A, idx_B)`. -/
def abstractCombineEntryPair {q q_A q_B q' : ℕ}
    (δ : ℕ) (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (β : Fin q' → Fin q)
    (Hs_A : List (ComputeRootedDigraph q_A))
    (Hs_B : List (ComputeRootedDigraph q_B))
    (idx_A : Fin Hs_A.length) (idx_B : Fin Hs_B.length) :
    List (CombineEntryRecipe Hs_A Hs_B q') :=
  abstractCombineEntryPairAux δ α_A α_B hcov β Hs_A Hs_B idx_A idx_B
    Hs_A[idx_A.1] Hs_B[idx_B.1] rfl rfl

/-- Purely combinatorial table-combination function on `(Hs_A, Hs_B)` (Steps (2) and (3) of
GM XIII (4.1), page 76). -/
def abstractCombineRecipes {q q_A q_B q' : ℕ}
    (δ : ℕ) (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (β : Fin q' → Fin q)
    (Hs_A : List (ComputeRootedDigraph q_A))
    (Hs_B : List (ComputeRootedDigraph q_B)) :
    List (CombineEntryRecipe Hs_A Hs_B q') :=
  dedupByIso (·.H) ((List.finRange Hs_A.length).flatMap (fun idx_A =>
    (List.finRange Hs_B.length).flatMap (fun idx_B =>
      abstractCombineEntryPair δ α_A α_B hcov β Hs_A Hs_B idx_A idx_B)))

private theorem filter_sum_biUnion_eq {α β γ : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (P : α ⊕ β → Prop) [DecidablePred P] (f : α ⊕ β → Finset γ) :
    (Finset.univ.filter P).biUnion f =
      (Finset.univ.filter (fun a => P (Sum.inl a))).biUnion (fun a => f (Sum.inl a)) ∪
      (Finset.univ.filter (fun b => P (Sum.inr b))).biUnion (fun b => f (Sum.inr b)) := by
  ext z
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨a | b, hp, hz⟩
    · exact Or.inl ⟨a, hp, hz⟩
    · exact Or.inr ⟨b, hp, hz⟩
  · rintro (⟨a, hp, hz⟩ | ⟨b, hp, hz⟩)
    · exact ⟨Sum.inl a, hp, hz⟩
    · exact ⟨Sum.inr b, hp, hz⟩

private theorem owner_eq_succ_iff {k : ℕ} (U : Finset (Fin k)) (c : Fin k) (v : Fin U.card) :
    (if hc : c ∈ U then ((finsetEnumEquiv U).symm ⟨c, hc⟩).1 + 1 else 0) = v.1 + 1 ↔
      c = (finsetEnumEquiv U v).1 := by
  split_ifs with hc
  · simp only [Nat.add_right_cancel_iff, Fin.ext_iff.symm]
    rw [Equiv.symm_apply_eq, Subtype.ext_iff]
  · simp only [false_iff]
    intro heq
    exact hc (heq ▸ (finsetEnumEquiv U v).2)

private theorem RawCertEntry.mk_eq {q : ℕ} {G : ComputeDigraph} (H : ComputeRootedDigraph q)
    {vv₁ vv₂ : Fin H.digraph.numVerts → Finset (Fin G.numVerts)}
    {ve₁ ve₂ : Fin H.digraph.numVerts → Finset (Fin G.numEdges)}
    {em₁ em₂ : Fin H.digraph.numEdges → Fin G.numEdges}
    (hvv : vv₁ = vv₂) (hve : ve₁ = ve₂) (hem : em₁ = em₂) :
    ({ H := H, vertVerts := vv₁, vertEdges := ve₁, edgeMap := em₁ } : RawCertEntry G q) =
    { H := H, vertVerts := vv₂, vertEdges := ve₂, edgeMap := em₂ } := by
  subst hvv hve hem
  rfl

theorem eval_mkCombineRecipe {q q_A q_B q' : ℕ} {G : ComputeDigraph}
    (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (β : Fin q' → Fin q)
    (es_A : List (RawCertEntry G q_A))
    (es_B : List (RawCertEntry G q_B))
    (idx_A : Fin (es_A.map (·.H)).length) (idx_B : Fin (es_B.map (·.H)).length)
    (hA : (es_A[idx_A.1]'(by simpa using idx_A.2)).H = (es_A.map (·.H))[idx_A.1])
    (hB : (es_B[idx_B.1]'(by simpa using idx_B.2)).H = (es_B.map (·.H))[idx_B.1])
    (U : Finset (Fin (glueRootedDigraphs α_A α_B hcov
      (es_A[idx_A.1]'(by simpa using idx_A.2)).H
      (es_B[idx_B.1]'(by simpa using idx_B.2)).H).digraph.numVerts))
    (hU : IsValidRootedSubverts (glueRootedDigraphs α_A α_B hcov
      (es_A[idx_A.1]'(by simpa using idx_A.2)).H
      (es_B[idx_B.1]'(by simpa using idx_B.2)).H) β U) :
    (mkCombineRecipe α_A α_B hcov β (es_A.map (·.H)) (es_B.map (·.H)) idx_A idx_B
      (es_A[idx_A.1]'(by simpa using idx_A.2)).H
      (es_B[idx_B.1]'(by simpa using idx_B.2)).H hA hB U hU).eval
        es_A es_B rfl rfl =
      rawRestrict (rawGlue α_A α_B hcov
        (es_A[idx_A.1]'(by simpa using idx_A.2))
        (es_B[idx_B.1]'(by simpa using idx_B.2))) β U hU := by
  unfold CombineEntryRecipe.eval mkCombineRecipe rawRestrict rawGlue
  dsimp only
  apply RawCertEntry.mk_eq
  · funext v
    rw [filter_sum_biUnion_eq]
    congr 1
    · refine Finset.biUnion_congr ?_ (fun _ _ => rfl)
      ext u_A
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, u_A.2, ↓reduceDIte]
      exact owner_eq_succ_iff U _ v
    · refine Finset.biUnion_congr ?_ (fun _ _ => rfl)
      ext u_B
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, u_B.2, ↓reduceDIte]
      exact owner_eq_succ_iff U _ v
  · funext v
    rw [filter_sum_biUnion_eq]
    congr 1
    · refine Finset.biUnion_congr ?_ (fun _ _ => rfl)
      ext u_A
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, u_A.2, ↓reduceDIte]
      exact owner_eq_succ_iff U _ v
    · refine Finset.biUnion_congr ?_ (fun _ _ => rfl)
      ext u_B
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, u_B.2, ↓reduceDIte]
      exact owner_eq_succ_iff U _ v
  · funext e
    cases h : finSumFinEquiv.symm e with
    | inl e_A =>
      have he : e = finSumFinEquiv (Sum.inl e_A) := ((Equiv.eq_symm_apply finSumFinEquiv).mp h.symm).symm
      subst he
      simp [e_A.2]
    | inr e_B =>
      have he : e = finSumFinEquiv (Sum.inr e_B) := ((Equiv.eq_symm_apply finSumFinEquiv).mp h.symm).symm
      subst he
      have hnot : ¬ ((es_A[idx_A.1].H.digraph.numEdges + e_B.1) < es_A[idx_A.1].H.digraph.numEdges) := by
        omega
      simp [hnot]

private theorem abstractCombineEntryPairAux_congr {q q_A q_B q' : ℕ}
    (δ : ℕ) (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (β : Fin q' → Fin q)
    (Hs_A : List (ComputeRootedDigraph q_A))
    (Hs_B : List (ComputeRootedDigraph q_B))
    (idx_A : Fin Hs_A.length) (idx_B : Fin Hs_B.length)
    (H_A : ComputeRootedDigraph q_A) (H_B : ComputeRootedDigraph q_B)
    (hA : H_A = Hs_A[idx_A.1]) (hB : H_B = Hs_B[idx_B.1]) :
    abstractCombineEntryPair δ α_A α_B hcov β Hs_A Hs_B idx_A idx_B =
      abstractCombineEntryPairAux δ α_A α_B hcov β Hs_A Hs_B idx_A idx_B H_A H_B hA hB := by
  subst hA hB
  rfl

private theorem flatMap_finRange_getElem {α β : Type*} (L : List α) (f : α → List β) :
    (List.finRange L.length).flatMap (fun i => f L[i.1]) = L.flatMap f := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change (List.finRange (L.length + 1)).flatMap (fun i => f (a :: L)[i.1]) = (a :: L).flatMap f
    rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map]
    simp only [Fin.val_zero, List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ]
    rw [ih, List.flatMap_cons]

private theorem flatMap_finRange_cast {γ : Type*} {k₁ k₂ : ℕ} (hk : k₁ = k₂)
    (F : Fin k₁ → List γ) :
    (List.finRange k₁).flatMap F =
      (List.finRange k₂).flatMap (fun i => F ⟨i.1, hk ▸ i.2⟩) := by
  subst hk
  rfl

theorem map_eval_abstractCombineRecipes {q q_A q_B q' : ℕ} {G : ComputeDigraph}
    (δ : ℕ) (α_A : Fin q_A → Fin q) (α_B : Fin q_B → Fin q)
    (hcov : ∀ k : Fin q, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k))
    (β : Fin q' → Fin q)
    {Hs_A : List (ComputeRootedDigraph q_A)}
    {Hs_B : List (ComputeRootedDigraph q_B)}
    (es_A : List (RawCertEntry G q_A))
    (es_B : List (RawCertEntry G q_B))
    (hes_A : es_A.map (·.H) = Hs_A)
    (hes_B : es_B.map (·.H) = Hs_B) :
    (abstractCombineRecipes δ α_A α_B hcov β Hs_A Hs_B).map
        (fun r => r.eval es_A es_B hes_A hes_B) =
      rawCombineTables δ α_A α_B hcov β es_A es_B := by
  subst hes_A hes_B
  unfold abstractCombineRecipes rawCombineTables
  rw [dedupByIso_map
    (fun x : CombineEntryRecipe (es_A.map (·.H)) (es_B.map (·.H)) q' => x.H)
    (fun x : RawCertEntry G q' => x.H)
    (fun r => r.eval es_A es_B rfl rfl) (fun _ => rfl)]
  congr 1
  have hlenA : (es_A.map (·.H)).length = es_A.length := List.length_map _
  have hlenB : (es_B.map (·.H)).length = es_B.length := List.length_map _
  rw [List.map_flatMap, flatMap_finRange_cast hlenA]
  have hinner : ∀ idx_A : Fin es_A.length,
      List.map (fun r => r.eval es_A es_B rfl rfl)
        ((List.finRange (es_B.map (·.H)).length).flatMap (fun idx_B =>
          abstractCombineEntryPair δ α_A α_B hcov β
            (es_A.map (·.H)) (es_B.map (·.H))
            ⟨idx_A.1, hlenA.symm ▸ idx_A.2⟩ idx_B)) =
      es_B.flatMap (fun raw_B => rawCombineEntryPair δ α_A α_B hcov β es_A[idx_A.1] raw_B) := by
    intro idx_A
    rw [List.map_flatMap, flatMap_finRange_cast hlenB]
    have hpair : ∀ idx_B : Fin es_B.length,
        List.map (fun r => r.eval es_A es_B rfl rfl)
          (abstractCombineEntryPair δ α_A α_B hcov β
            (es_A.map (·.H)) (es_B.map (·.H))
            ⟨idx_A.1, hlenA.symm ▸ idx_A.2⟩
            ⟨idx_B.1, hlenB.symm ▸ idx_B.2⟩) =
        rawCombineEntryPair δ α_A α_B hcov β es_A[idx_A.1] es_B[idx_B.1] := by
      intro idx_B
      let idx_A' : Fin (es_A.map (·.H)).length := ⟨idx_A.1, hlenA.symm ▸ idx_A.2⟩
      let idx_B' : Fin (es_B.map (·.H)).length := ⟨idx_B.1, hlenB.symm ▸ idx_B.2⟩
      have hA : es_A[idx_A.1].H = (es_A.map (·.H))[idx_A'.1] := by simp [idx_A']
      have hB : es_B[idx_B.1].H = (es_B.map (·.H))[idx_B'.1] := by simp [idx_B']
      rw [abstractCombineEntryPairAux_congr δ α_A α_B hcov β (es_A.map (·.H)) (es_B.map (·.H))
        idx_A' idx_B' es_A[idx_A.1].H es_B[idx_B.1].H hA hB]
      unfold abstractCombineEntryPairAux rawCombineEntryPair
      dsimp only
      rw [List.map_filterMap]
      dsimp only [Function.comp_def, mkCombineRecipe, rawGlue, rawRestrict]
      congr 1
      funext U
      by_cases hU : IsValidRootedSubverts (glueRootedDigraphs α_A α_B hcov es_A[idx_A.1].H es_B[idx_B.1].H) β U
      · by_cases hdet : (restrictRootedDigraph (glueRootedDigraphs α_A α_B hcov es_A[idx_A.1].H es_B[idx_B.1].H) β U hU).HasDetailLe δ
        · simp only [hU, hdet, ↓reduceDIte, ↓reduceIte, Option.map_some]
          exact congrArg some (eval_mkCombineRecipe α_A α_B hcov β es_A es_B
            idx_A' idx_B' hA hB U hU)
        · simp only [hU, hdet, ↓reduceDIte, ↓reduceIte, Option.map_none]
      · simp only [hU, ↓reduceDIte, Option.map_none]
    exact (List.flatMap_congr fun idx_B _ => hpair idx_B).trans
      (flatMap_finRange_getElem es_B (fun raw_B => rawCombineEntryPair δ α_A α_B hcov β es_A[idx_A.1] raw_B))
  exact (List.flatMap_congr fun idx_A _ => hinner idx_A).trans
    (flatMap_finRange_getElem es_A (fun raw_A =>
      es_B.flatMap (fun raw_B => rawCombineEntryPair δ α_A α_B hcov β raw_A raw_B)))

/-! ### Section 4: Local Base Configurations and `baseCertFolioTable` Equivalence -/

/-- Transport a `RawCertEntry G_loc q` along vertex and edge maps `fV` and `fE`. -/
def RawCertEntry.mapEmb {G_loc G : ComputeDigraph} {q : ℕ}
    (fV : Fin G_loc.numVerts → Fin G.numVerts)
    (fE : Fin G_loc.numEdges → Fin G.numEdges)
    (e : RawCertEntry G_loc q) : RawCertEntry G q where
  H := e.H
  vertVerts u := (e.vertVerts u).image fV
  vertEdges u := (e.vertEdges u).image fE
  edgeMap d := fE (e.edgeMap d)

/-- Transport a `DigraphSubgraph G_loc` along `fV` and `fE` respecting `head` and `tail`. -/
def DigraphSubgraph.mapEmb {G_loc G : ComputeDigraph}
    (fV : Fin G_loc.numVerts → Fin G.numVerts)
    (fE : Fin G_loc.numEdges → Fin G.numEdges)
    (h_head : ∀ e, fV (G_loc.head e) = G.head (fE e))
    (h_tail : ∀ e, fV (G_loc.tail e) = G.tail (fE e))
    (S : DigraphSubgraph G_loc) : DigraphSubgraph G where
  verts := S.verts.image fV
  edges := S.edges.image fE
  head_mem {_} he := by
    rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
    rw [← h_head e₀]
    exact Finset.mem_image_of_mem fV (S.head_mem he₀)
  tail_mem {_} he := by
    rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
    rw [← h_tail e₀]
    exact Finset.mem_image_of_mem fV (S.tail_mem he₀)

private theorem toFinset_map_eq_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (L : List α) :
    (L.map f).toFinset = L.toFinset.image f := by
  ext y
  simp

theorem finsetSubsets_eq_map_image {k : ℕ} (S : Finset (Fin k)) :
    finsetSubsets S =
      (finsetSubsets (Finset.univ : Finset (Fin S.card))).map (Finset.image (finsetRootFn S)) := by
  unfold finsetSubsets
  rw [finsetToFinList_eq_map_finsetRootFn S, finsetToFinList_univ,
      List.sublists_map, List.map_map, List.map_map]
  congr 1
  funext L
  exact toFinset_map_eq_image (finsetRootFn S) L

private theorem mem_image_of_injective {α β : Type*} [DecidableEq β]
    (s : Finset α) {f : α → β} (hf : Function.Injective f) {a : α} :
    f a ∈ s.image f ↔ a ∈ s :=
  ⟨fun h => by rcases Finset.mem_image.mp h with ⟨b, hb, hab⟩; exact hf hab ▸ hb,
   Finset.mem_image_of_mem f⟩

private theorem mapEmb_adj_iff {G_loc G : ComputeDigraph}
    {fV : Fin G_loc.numVerts → Fin G.numVerts} (hfV : Function.Injective fV)
    {fE : Fin G_loc.numEdges → Fin G.numEdges}
    (h_head : ∀ e, fV (G_loc.head e) = G.head (fE e))
    (h_tail : ∀ e, fV (G_loc.tail e) = G.tail (fE e))
    (S : DigraphSubgraph G_loc) (u v : Fin G_loc.numVerts) :
    (S.mapEmb fV fE h_head h_tail).underlyingSimpleGraph.Adj (fV u) (fV v) ↔
      S.underlyingSimpleGraph.Adj u v := by
  unfold DigraphSubgraph.underlyingSimpleGraph DigraphSubgraph.mapEmb
  dsimp only
  rw [hfV.ne_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨_, he, h⟩
    rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
    rw [← h_head e₀, ← h_tail e₀, hfV.eq_iff, hfV.eq_iff, hfV.eq_iff, hfV.eq_iff] at h
    exact ⟨e₀, he₀, h⟩
  · rintro ⟨e₀, he₀, h⟩
    refine ⟨fE e₀, Finset.mem_image_of_mem fE he₀, ?_⟩
    rw [← h_head e₀, ← h_tail e₀, hfV.eq_iff, hfV.eq_iff, hfV.eq_iff, hfV.eq_iff]
    exact h

private theorem mapEmb_adj_mem_verts {G_loc G : ComputeDigraph}
    {fV : Fin G_loc.numVerts → Fin G.numVerts}
    {fE : Fin G_loc.numEdges → Fin G.numEdges}
    (h_head : ∀ e, fV (G_loc.head e) = G.head (fE e))
    (h_tail : ∀ e, fV (G_loc.tail e) = G.tail (fE e))
    (S : DigraphSubgraph G_loc) {x y : Fin G.numVerts}
    (hadj : (S.mapEmb fV fE h_head h_tail).underlyingSimpleGraph.Adj x y) :
    y ∈ (S.mapEmb fV fE h_head h_tail).verts := by
  rcases hadj with ⟨_, e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact (S.mapEmb fV fE h_head h_tail).tail_mem he
  · exact (S.mapEmb fV fE h_head h_tail).head_mem he

private theorem mapEmb_reachable_iff {G_loc G : ComputeDigraph}
    {fV : Fin G_loc.numVerts → Fin G.numVerts} (hfV : Function.Injective fV)
    {fE : Fin G_loc.numEdges → Fin G.numEdges}
    (h_head : ∀ e, fV (G_loc.head e) = G.head (fE e))
    (h_tail : ∀ e, fV (G_loc.tail e) = G.tail (fE e))
    (S : DigraphSubgraph G_loc) (u v : Fin G_loc.numVerts) :
    (S.mapEmb fV fE h_head h_tail).underlyingSimpleGraph.Reachable (fV u) (fV v) ↔
      S.underlyingSimpleGraph.Reachable u v := by
  constructor
  · rintro ⟨w⟩
    generalize hx : fV u = x at w
    generalize hy : fV v = y at w
    induction w generalizing u v with
    | nil =>
      have huv : u = v := hfV (hx.trans hy.symm)
      subst huv
      exact SimpleGraph.Reachable.refl u
    | @cons a b c hadj tail ih =>
      subst hx hy
      have hb_mem : b ∈ S.verts.image fV := mapEmb_adj_mem_verts h_head h_tail S hadj
      rcases Finset.mem_image.mp hb_mem with ⟨u', _, rfl⟩
      have hadj_loc : S.underlyingSimpleGraph.Adj u u' :=
        (mapEmb_adj_iff hfV h_head h_tail S u u').mp hadj
      exact hadj_loc.reachable.trans (ih u' v rfl rfl)
  · rintro ⟨w⟩
    induction w with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b c hadj tail ih =>
      have hadj' : (S.mapEmb fV fE h_head h_tail).underlyingSimpleGraph.Adj (fV a) (fV b) :=
        (mapEmb_adj_iff hfV h_head h_tail S a b).mpr hadj
      exact hadj'.reachable.trans ih

theorem mapEmb_isNonNullConnected_iff {G_loc G : ComputeDigraph}
    {fV : Fin G_loc.numVerts → Fin G.numVerts} (hfV : Function.Injective fV)
    {fE : Fin G_loc.numEdges → Fin G.numEdges}
    (h_head : ∀ e, fV (G_loc.head e) = G.head (fE e))
    (h_tail : ∀ e, fV (G_loc.tail e) = G.tail (fE e))
    (S : DigraphSubgraph G_loc) :
    (S.mapEmb fV fE h_head h_tail).IsNonNullConnected ↔ S.IsNonNullConnected := by
  unfold DigraphSubgraph.IsNonNullConnected
  have hne : (S.mapEmb fV fE h_head h_tail).verts.Nonempty ↔ S.verts.Nonempty :=
    Finset.image_nonempty
  refine and_congr hne ⟨fun h u hu v hv => ?_, fun h x hx y hy => ?_⟩
  · exact (mapEmb_reachable_iff hfV h_head h_tail S u v).mp
      (h (fV u) (Finset.mem_image_of_mem fV hu) (fV v) (Finset.mem_image_of_mem fV hv))
  · rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨v, hv, rfl⟩
    exact (mapEmb_reachable_iff hfV h_head h_tail S u v).mpr (h u hu v hv)

/-- Standard local digraph induced on `(Fin VA.card, Fin EA.card)` by a piece `(VA, EA)` whose
edges have endpoints in `VA`. -/
abbrev pieceLocDigraph (G : ComputeDigraph)
    (VA : Finset (Fin G.numVerts)) (EA : Finset (Fin G.numEdges))
    (hEA : ∀ e ∈ EA, G.head e ∈ VA ∧ G.tail e ∈ VA) : ComputeDigraph where
  numVerts := VA.card
  numEdges := EA.card
  head e := (finsetEnumEquiv VA).symm ⟨G.head (finsetRootFn EA e),
    (hEA (finsetRootFn EA e) (finsetRootFn_mem EA e)).1⟩
  tail e := (finsetEnumEquiv VA).symm ⟨G.tail (finsetRootFn EA e),
    (hEA (finsetRootFn EA e) (finsetRootFn_mem EA e)).2⟩

theorem pieceLocDigraph_head_eq (G : ComputeDigraph)
    (VA : Finset (Fin G.numVerts)) (EA : Finset (Fin G.numEdges))
    (hEA : ∀ e ∈ EA, G.head e ∈ VA ∧ G.tail e ∈ VA) (e : Fin EA.card) :
    finsetRootFn VA ((pieceLocDigraph G VA EA hEA).head e) = G.head (finsetRootFn EA e) := by
  dsimp [pieceLocDigraph, finsetRootFn]
  exact congrArg Subtype.val ((finsetEnumEquiv VA).apply_symm_apply _)

theorem pieceLocDigraph_tail_eq (G : ComputeDigraph)
    (VA : Finset (Fin G.numVerts)) (EA : Finset (Fin G.numEdges))
    (hEA : ∀ e ∈ EA, G.head e ∈ VA ∧ G.tail e ∈ VA) (e : Fin EA.card) :
    finsetRootFn VA ((pieceLocDigraph G VA EA hEA).tail e) = G.tail (finsetRootFn EA e) := by
  dsimp [pieceLocDigraph, finsetRootFn]
  exact congrArg Subtype.val ((finsetEnumEquiv VA).apply_symm_apply _)

theorem pieceSubgraphs_eq_map_loc (G : ComputeDigraph)
    (VA : Finset (Fin G.numVerts)) (EA : Finset (Fin G.numEdges))
    (hEA : ∀ e ∈ EA, G.head e ∈ VA ∧ G.tail e ∈ VA) :
    pieceSubgraphs G VA EA =
      (pieceSubgraphs (pieceLocDigraph G VA EA hEA) Finset.univ Finset.univ).map
        (DigraphSubgraph.mapEmb (finsetRootFn VA) (finsetRootFn EA)
          (pieceLocDigraph_head_eq G VA EA hEA)
          (pieceLocDigraph_tail_eq G VA EA hEA)) := by
  let G_loc := pieceLocDigraph G VA EA hEA
  let fV := finsetRootFn VA
  let fE := finsetRootFn EA
  have hfV : Function.Injective fV := finsetRootFn_injective VA
  have hfE : Function.Injective fE := finsetRootFn_injective EA
  have hhead := pieceLocDigraph_head_eq G VA EA hEA
  have htail := pieceLocDigraph_tail_eq G VA EA hEA
  unfold pieceSubgraphs
  rw [finsetSubsets_eq_map_image VA, finsetSubsets_eq_map_image EA,
      List.flatMap_map, List.map_flatMap]
  congr 1
  funext V_loc
  rw [List.filterMap_map, List.map_filterMap]
  congr 1
  funext E_loc
  have hends_iff :
      (∀ e ∈ E_loc.image fE, G.head e ∈ V_loc.image fV ∧ G.tail e ∈ V_loc.image fV) ↔
      (∀ e₀ ∈ E_loc, G_loc.head e₀ ∈ V_loc ∧ G_loc.tail e₀ ∈ V_loc) := by
    constructor
    · intro h e₀ he₀
      rcases h (fE e₀) (Finset.mem_image_of_mem fE he₀) with ⟨hh, ht⟩
      rw [← hhead e₀, mem_image_of_injective V_loc hfV] at hh
      rw [← htail e₀, mem_image_of_injective V_loc hfV] at ht
      exact ⟨hh, ht⟩
    · intro h e he
      rcases Finset.mem_image.mp he with ⟨e₀, he₀, rfl⟩
      rcases h e₀ he₀ with ⟨hh, ht⟩
      rw [← hhead e₀, ← htail e₀]
      exact ⟨Finset.mem_image_of_mem fV hh, Finset.mem_image_of_mem fV ht⟩
  by_cases hends_loc : ∀ e₀ ∈ E_loc, G_loc.head e₀ ∈ V_loc ∧ G_loc.tail e₀ ∈ V_loc
  · have hends : ∀ e ∈ E_loc.image fE, G.head e ∈ V_loc.image fV ∧ G.tail e ∈ V_loc.image fV :=
      hends_iff.mpr hends_loc
    dsimp only [Function.comp_def]
    rw [dite_eq_left_of_eq_true (eq_true hends), dite_eq_left_of_eq_true (eq_true hends_loc)]
    have hmk_eq :
        mkPieceSubgraph (V_loc.image fV) (E_loc.image fE) hends =
          (mkPieceSubgraph (G := G_loc) V_loc E_loc hends_loc).mapEmb fV fE hhead htail := rfl
    rw [hmk_eq]
    by_cases hconn : (mkPieceSubgraph (G := G_loc) V_loc E_loc hends_loc).IsNonNullConnected
    · have hconn' := (mapEmb_isNonNullConnected_iff hfV hhead htail _).mpr hconn
      simp only [fV, fE, hconn', hconn, ↓reduceIte, Option.map_some]
    · have hconn' : ¬ ((mkPieceSubgraph (G := G_loc) V_loc E_loc hends_loc).mapEmb fV fE hhead htail).IsNonNullConnected :=
        fun h => hconn ((mapEmb_isNonNullConnected_iff hfV hhead htail _).mp h)
      simp only [fV, fE, hconn', hconn, ↓reduceIte, Option.map_none]
  · have hends : ¬ (∀ e ∈ E_loc.image fE, G.head e ∈ V_loc.image fV ∧ G.tail e ∈ V_loc.image fV) :=
      fun h => hends_loc (hends_iff.mp h)
    dsimp only [Function.comp_def]
    rw [dite_eq_right_of_eq_false (eq_false hends),
        dite_eq_right_of_eq_false (eq_false hends_loc), Option.map_none]

private theorem allFinMaps_map {α β : Type*} (f : α → β) :
    ∀ (m : ℕ) (elems : List α),
      allFinMaps m (elems.map f) = (allFinMaps m elems).map (fun g => f ∘ g)
  | 0, _ => by
    simp only [allFinMaps, List.map_cons, List.map_nil]
    congr 1
    funext i
    exact i.elim0
  | m + 1, elems => by
    simp only [allFinMaps, List.flatMap_map, allFinMaps_map f m elems, List.map_flatMap,
      List.map_map]
    congr 1
    funext a
    congr 1
    funext g
    funext i
    refine Fin.cases rfl (fun j => rfl) i

private theorem flatMap_filterMap_map {α₁ α₂ β γ : Type*}
    (L₁ : List α₁) (L₂ : List α₂) (f : α₁ → α₂ → Option β) (g : β → γ) :
    (L₁.flatMap (fun a₁ => L₂.filterMap (fun a₂ => (f a₁ a₂).map g))).head? =
      ((L₁.flatMap (fun a₁ => L₂.filterMap (fun a₂ => f a₁ a₂))).head?).map g := by
  have h : L₁.flatMap (fun a₁ => L₂.filterMap (fun a₂ => (f a₁ a₂).map g)) =
      (L₁.flatMap (fun a₁ => L₂.filterMap (fun a₂ => f a₁ a₂))).map g := by
    rw [List.map_flatMap]
    congr 1
    funext a₁
    rw [List.map_filterMap]
  rw [h, List.head?_map]

theorem findPieceRootedModel_loc_eq {q : ℕ} (G : ComputeDigraph)
    (VA : Finset (Fin G.numVerts)) (EA : Finset (Fin G.numEdges))
    (hEA : ∀ e ∈ EA, G.head e ∈ VA ∧ G.tail e ∈ VA)
    (r_loc : Fin q → Fin VA.card)
    (H : ComputeRootedDigraph q) :
    let G_loc := pieceLocDigraph G VA EA hEA
    (findPieceRootedModel G VA EA (finsetRootFn VA ∘ r_loc) H).map
        (fun M => ({ H := H, vertVerts := fun u => (M.vertMap u).verts,
                     vertEdges := fun u => (M.vertMap u).edges,
                     edgeMap := M.edgeMap } : RawCertEntry G q)) =
      ((findPieceRootedModel G_loc Finset.univ Finset.univ r_loc H).map
        (fun M_loc => ({ H := H, vertVerts := fun u => (M_loc.vertMap u).verts,
                         vertEdges := fun u => (M_loc.vertMap u).edges,
                         edgeMap := M_loc.edgeMap } : RawCertEntry G_loc q))).map
        (RawCertEntry.mapEmb (finsetRootFn VA) (finsetRootFn EA)) := by
  let G_loc := pieceLocDigraph G VA EA hEA
  let fV := finsetRootFn VA
  let fE := finsetRootFn EA
  have hfV : Function.Injective fV := finsetRootFn_injective VA
  have hfE : Function.Injective fE := finsetRootFn_injective EA
  have hhead := pieceLocDigraph_head_eq G VA EA hEA
  have htail := pieceLocDigraph_tail_eq G VA EA hEA
  let toRawG : PieceRootedModel G VA EA (fV ∘ r_loc) H → RawCertEntry G q :=
    fun M => { H := H, vertVerts := fun u => (M.vertMap u).verts,
               vertEdges := fun u => (M.vertMap u).edges, edgeMap := M.edgeMap }
  let toRawLoc : PieceRootedModel G_loc Finset.univ Finset.univ r_loc H → RawCertEntry G_loc q :=
    fun M => { H := H, vertVerts := fun u => (M.vertMap u).verts,
               vertEdges := fun u => (M.vertMap u).edges, edgeMap := M.edgeMap }
  change (findPieceRootedModel G VA EA (fV ∘ r_loc) H).map toRawG =
    ((findPieceRootedModel G_loc Finset.univ Finset.univ r_loc H).map toRawLoc).map
      (RawCertEntry.mapEmb fV fE)
  rw [Option.map_map]
  unfold findPieceRootedModel
  dsimp only
  rw [pieceSubgraphs_eq_map_loc G VA EA hEA,
      finsetToFinList_eq_map_finsetRootFn EA,
      ← finsetToFinList_univ EA.card,
      allFinMaps_map, allFinMaps_map]
  simp only [List.flatMap_map, List.filterMap_map]
  rw [← flatMap_filterMap_map, ← flatMap_filterMap_map]
  congr 1
  congr 1
  funext vm_loc
  congr 1
  funext em_loc
  dsimp only [Function.comp_def]
  unfold buildPieceRootedModel?
  have hconn_iff :
      (∀ v, ((vm_loc v).mapEmb fV fE hhead htail).IsNonNullConnected) ↔
      (∀ v, (vm_loc v).IsNonNullConnected) :=
    forall_congr' fun v => mapEmb_isNonNullConnected_iff hfV hhead htail (vm_loc v)
  have hdisj_iff :
      (∀ u v, u ≠ v → Disjoint ((vm_loc u).mapEmb fV fE hhead htail).verts
        ((vm_loc v).mapEmb fV fE hhead htail).verts) ↔
      (∀ u v, u ≠ v → Disjoint (vm_loc u).verts (vm_loc v).verts) :=
    forall_congr' fun u => forall_congr' fun v => imp_congr_right fun _ =>
      Finset.disjoint_image hfV
  have hinj_iff :
      Function.Injective (fun e => fE (em_loc e)) ↔ Function.Injective em_loc :=
    hfE.of_comp_iff em_loc
  have hnotMem_iff :
      (∀ v e, fE (em_loc e) ∉ ((vm_loc v).mapEmb fV fE hhead htail).edges) ↔
      (∀ v e, em_loc e ∉ (vm_loc v).edges) :=
    forall_congr' fun v => forall_congr' fun e =>
      not_congr (mem_image_of_injective (vm_loc v).edges hfE)
  have hhead_iff :
      (∀ e, G.head (fE (em_loc e)) ∈ ((vm_loc (H.digraph.head e)).mapEmb fV fE hhead htail).verts) ↔
      (∀ e, G_loc.head (em_loc e) ∈ (vm_loc (H.digraph.head e)).verts) := by
    refine forall_congr' fun e => ?_
    rw [← hhead (em_loc e)]
    exact mem_image_of_injective _ hfV
  have htail_iff :
      (∀ e, G.tail (fE (em_loc e)) ∈ ((vm_loc (H.digraph.tail e)).mapEmb fV fE hhead htail).verts) ↔
      (∀ e, G_loc.tail (em_loc e) ∈ (vm_loc (H.digraph.tail e)).verts) := by
    refine forall_congr' fun e => ?_
    rw [← htail (em_loc e)]
    exact mem_image_of_injective _ hfV
  have hroot_iff :
      (∀ i, fV (r_loc i) ∈ ((vm_loc (H.roots i)).mapEmb fV fE hhead htail).verts) ↔
      (∀ i, r_loc i ∈ (vm_loc (H.roots i)).verts) :=
    forall_congr' fun i => mem_image_of_injective _ hfV
  have hvsub_true : ∀ v, ((vm_loc v).mapEmb fV fE hhead htail).verts ⊆ VA := by
    intro v x hx
    rcases Finset.mem_image.mp hx with ⟨u, _, rfl⟩
    exact finsetRootFn_mem VA u
  have hvsub_loc : ∀ v, (vm_loc v).verts ⊆ Finset.univ := fun v => Finset.subset_univ _
  have hesub_true : ∀ v, ((vm_loc v).mapEmb fV fE hhead htail).edges ⊆ EA := by
    intro v e he
    rcases Finset.mem_image.mp he with ⟨e₀, _, rfl⟩
    exact finsetRootFn_mem EA e₀
  have hesub_loc : ∀ v, (vm_loc v).edges ⊆ Finset.univ := fun v => Finset.subset_univ _
  have hemem_true : ∀ e, fE (em_loc e) ∈ EA := fun e => finsetRootFn_mem EA (em_loc e)
  have hemem_loc : ∀ e, em_loc e ∈ (Finset.univ : Finset (Fin G_loc.numEdges)) :=
    fun e => Finset.mem_univ _
  by_cases h1 : ∀ v, (vm_loc v).IsNonNullConnected
  · have h1' := hconn_iff.mpr h1
    rw [dite_eq_left_of_eq_true (eq_true h1'), dite_eq_left_of_eq_true (eq_true h1)]
    by_cases h2 : ∀ u v, u ≠ v → Disjoint (vm_loc u).verts (vm_loc v).verts
    · have h2' := hdisj_iff.mpr h2
      rw [dite_eq_left_of_eq_true (eq_true h2'), dite_eq_left_of_eq_true (eq_true h2)]
      by_cases h3 : Function.Injective em_loc
      · have h3' := hinj_iff.mpr h3
        rw [dite_eq_left_of_eq_true (eq_true h3'), dite_eq_left_of_eq_true (eq_true h3)]
        by_cases h4 : ∀ v e, em_loc e ∉ (vm_loc v).edges
        · have h4' := hnotMem_iff.mpr h4
          rw [dite_eq_left_of_eq_true (eq_true h4'), dite_eq_left_of_eq_true (eq_true h4)]
          by_cases h5 : ∀ e, G_loc.head (em_loc e) ∈ (vm_loc (H.digraph.head e)).verts
          · have h5' := hhead_iff.mpr h5
            rw [dite_eq_left_of_eq_true (eq_true h5'), dite_eq_left_of_eq_true (eq_true h5)]
            by_cases h6 : ∀ e, G_loc.tail (em_loc e) ∈ (vm_loc (H.digraph.tail e)).verts
            · have h6' := htail_iff.mpr h6
              rw [dite_eq_left_of_eq_true (eq_true h6'), dite_eq_left_of_eq_true (eq_true h6)]
              by_cases h7 : ∀ i, r_loc i ∈ (vm_loc (H.roots i)).verts
              · have h7' := hroot_iff.mpr h7
                rw [dite_eq_left_of_eq_true (eq_true h7'), dite_eq_left_of_eq_true (eq_true h7),
                    dite_eq_left_of_eq_true (eq_true hvsub_true), dite_eq_left_of_eq_true (eq_true hvsub_loc),
                    dite_eq_left_of_eq_true (eq_true hesub_true), dite_eq_left_of_eq_true (eq_true hesub_loc),
                    dite_eq_left_of_eq_true (eq_true hemem_true), dite_eq_left_of_eq_true (eq_true hemem_loc)]
                rfl
              · have h7' := fun h => h7 (hroot_iff.mp h)
                rw [dite_eq_right_of_eq_false (eq_false h7'), dite_eq_right_of_eq_false (eq_false h7), Option.map_none, Option.map_none]
            · have h6' := fun h => h6 (htail_iff.mp h)
              rw [dite_eq_right_of_eq_false (eq_false h6'), dite_eq_right_of_eq_false (eq_false h6), Option.map_none, Option.map_none]
          · have h5' := fun h => h5 (hhead_iff.mp h)
            rw [dite_eq_right_of_eq_false (eq_false h5'), dite_eq_right_of_eq_false (eq_false h5), Option.map_none, Option.map_none]
        · have h4' := fun h => h4 (hnotMem_iff.mp h)
          rw [dite_eq_right_of_eq_false (eq_false h4'), dite_eq_right_of_eq_false (eq_false h4), Option.map_none, Option.map_none]
      · have h3' := fun h => h3 (hinj_iff.mp h)
        rw [dite_eq_right_of_eq_false (eq_false h3'), dite_eq_right_of_eq_false (eq_false h3), Option.map_none, Option.map_none]
    · have h2' := fun h => h2 (hdisj_iff.mp h)
      rw [dite_eq_right_of_eq_false (eq_false h2'), dite_eq_right_of_eq_false (eq_false h2), Option.map_none, Option.map_none]
  · have h1' := fun h => h1 (hconn_iff.mp h)
    rw [dite_eq_right_of_eq_false (eq_false h1'), dite_eq_right_of_eq_false (eq_false h1), Option.map_none, Option.map_none]

theorem toRawList_baseCertFolioTable_loc {q δ : ℕ} (G : ComputeDigraph)
    (VA : Finset (Fin G.numVerts)) (EA : Finset (Fin G.numEdges))
    (hEA : ∀ e ∈ EA, G.head e ∈ VA ∧ G.tail e ∈ VA)
    (r_loc : Fin q → Fin VA.card) :
    (baseCertFolioTable G VA EA (finsetRootFn VA ∘ r_loc) δ).toRawList =
      (baseCertFolioTable (pieceLocDigraph G VA EA hEA) Finset.univ Finset.univ r_loc δ).toRawList.map
        (RawCertEntry.mapEmb (finsetRootFn VA) (finsetRootFn EA)) := by
  let G_loc := pieceLocDigraph G VA EA hEA
  unfold CertFolioTable.toRawList baseCertFolioTable
  dsimp only
  rw [dedupCertEntries_eq_dedupByIso, dedupCertEntries_eq_dedupByIso,
      dedupByIso_map (·.H) (·.H) CertFolioEntry.toRaw (fun _ => rfl),
      dedupByIso_map (·.H) (·.H) CertFolioEntry.toRaw (fun _ => rfl),
      dedupByIso_map (fun x : RawCertEntry G_loc q => x.H) (fun x : RawCertEntry G q => x.H)
        (RawCertEntry.mapEmb (finsetRootFn VA) (finsetRootFn EA)) (fun _ => rfl)]
  congr 1
  rw [List.map_filterMap, List.map_filterMap, List.map_filterMap]
  congr 1
  funext c
  cases decRootedDigraph q c with
  | none => rfl
  | some H =>
    dsimp only [Function.comp_apply]
    split_ifs with hdet
    · have hfind := findPieceRootedModel_loc_eq G VA EA hEA r_loc H
      dsimp only at hfind
      cases h1 : findPieceRootedModel G VA EA (finsetRootFn VA ∘ r_loc) H <;>
        cases h2 : findPieceRootedModel (pieceLocDigraph G VA EA hEA) Finset.univ Finset.univ r_loc H <;>
        simp only [h1, h2, Option.map_none, Option.map_some, reduceCtorEq] at hfind ⊢
      exact hfind
    · rfl

private theorem sigma_base_cast_q {q₁ q₂ δ : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {hEA : ∀ e ∈ EA, G.head e ∈ VA ∧ G.tail e ∈ VA}
    (hq : q₁ = q₂) (r₁ : Fin q₁ → Fin VA.card) (r₂ : Fin q₂ → Fin VA.card)
    (hr : ∀ i : Fin q₁, r₁ i = r₂ ⟨i.1, hq ▸ i.2⟩) :
    (⟨q₁, (baseCertFolioTable (pieceLocDigraph G VA EA hEA) Finset.univ Finset.univ r₁ δ).toRawList.map
        (RawCertEntry.mapEmb (finsetRootFn VA) (finsetRootFn EA))⟩ : Σ q, List (RawCertEntry G q)) =
    ⟨q₂, (baseCertFolioTable (pieceLocDigraph G VA EA hEA) Finset.univ Finset.univ r₂ δ).toRawList.map
        (RawCertEntry.mapEmb (finsetRootFn VA) (finsetRootFn EA))⟩ := by
  subst hq
  have hfn : r₁ = r₂ := funext hr
  subst hfn
  rfl

theorem toSigmaRaw_baseCertFolioTable {δ : ℕ} (G : ComputeDigraph)
    (VA : Finset (Fin G.numVerts)) (EA : Finset (Fin G.numEdges))
    (ZA : Finset (Fin G.numVerts)) (hZA : ZA ⊆ VA)
    (hEA : ∀ e ∈ EA, G.head e ∈ VA ∧ G.tail e ∈ VA) :
    (baseCertFolioTable G VA EA (finsetRootFn ZA) δ).toSigmaRaw =
      let G_loc := pieceLocDigraph G VA EA hEA
      let Z_loc := subMaskFinset VA ZA
      ⟨Z_loc.card,
        (baseCertFolioTable G_loc Finset.univ Finset.univ (finsetRootFn Z_loc) δ).toRawList.map
          (RawCertEntry.mapEmb (finsetRootFn VA) (finsetRootFn EA))⟩ := by
  have h_r : finsetRootFn ZA = finsetRootFn VA ∘ finsetSubIdx hZA :=
    (finsetRootFn_comp_finsetSubIdx hZA).symm
  unfold CertFolioTable.toSigmaRaw
  rw [h_r, toRawList_baseCertFolioTable_loc G VA EA hEA (finsetSubIdx hZA)]
  exact sigma_base_cast_q (card_subMaskFinset hZA).symm
    (finsetSubIdx hZA) (finsetRootFn (subMaskFinset VA ZA))
    (finsetSubIdx_eq_finsetRootFn_subMaskFinset hZA)

/-! ### Section 5: Intermediate `pieceZ` Bound `Q_max` and Bounded Encoding of Abstract Folio Tables -/

/-- Universal upper bound `2 + 4 * (ω + ξ)` on the size of every boundary root set `ZA` and every
union `ZA ∪ ZB` occurring during `computeFolioDP` on a branch-decomposition of width `≤ ω` with
`|Z| ≤ ξ`. -/
def Q_max (ξ ω : ℕ) : ℕ := 2 + 4 * (ω + ξ)

theorem card_pieceZ_dpAccEB_le_children {t ω ξ : ℕ} {G : ComputeDigraph}
    {Z : Finset (Fin G.numVerts)} (hZ : Z.card ≤ ξ) (ht : 0 < t)
    {p : ℕ → ℕ} (hp : ∀ z, 0 < z → z < t → p z < z)
    {τ : Fin G.numEdges → Fin t}
    (hbd : IsDigraphBranchDecompOfWidthLe ω G (parentTree t p) τ)
    (x : ℕ) :
    ∀ k : ℕ, x + 1 ≤ k → k ≤ t →
      (pieceZ G Z (dpAccEB G p τ x k)).card ≤
        2 + ((childrenFinset t p x).filter (fun c => c.1 < k)).card * (ω + ξ) := by
  intro k hk_ge hk_le
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hkx : k = x
    · subst hkx
      rw [dpAccEB_self]
      have hemp : (childrenFinset t p k).filter (fun c => c.1 < k + 1) = ∅ := by
        ext c
        simp only [Finset.mem_filter, childrenFinset, Finset.notMem_empty, iff_false]
        omega
      rw [hemp, Finset.card_empty, Nat.zero_mul, Nat.add_zero]
      exact (card_pieceZ_le_two_of_card_le_one G Z (card_leafEdges_le_one hbd k)).2
    · have hk_ge' : x + 1 ≤ k := by omega
      have hk_lt_t : k < t := by omega
      have hxk : x < k := by omega
      have h_ih := ih hk_ge' (by omega)
      by_cases hpk : p k = x
      · rw [dpAccEB_step_eq G p τ hk_lt_t hxk hpk]
        have hsub := pieceZ_union_subset Z (dpAccEB G p τ x k) (dpEB G p τ k)
        have hcard_u :
            (pieceZ G Z (dpAccEB G p τ x k ∪ dpEB G p τ k)).card ≤
              (pieceZ G Z (dpAccEB G p τ x k)).card + (pieceZ G Z (dpEB G p τ k)).card :=
          (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have hk_pos : 0 < k := by omega
        have hcard_k := card_pieceZ_dpEB_le hZ ht hp hbd (x := ⟨k, hk_lt_t⟩) hk_pos
        dsimp only at hcard_k
        have hchild_ins :
            (childrenFinset t p x).filter (fun c => c.1 < k + 1) =
              insert ⟨k, hk_lt_t⟩ ((childrenFinset t p x).filter (fun c => c.1 < k)) := by
          ext c
          simp only [Finset.mem_filter, childrenFinset, Finset.mem_insert, Finset.mem_univ,
            true_and, Fin.ext_iff]
          constructor
          · rintro ⟨⟨hxc, hpc⟩, hck1⟩
            by_cases hck : c.1 = k
            · exact Or.inl hck
            · exact Or.inr ⟨⟨hxc, hpc⟩, by omega⟩
          · rintro (hck | ⟨⟨hxc, hpc⟩, hck⟩)
            · rw [hck]
              exact ⟨⟨hxk, hpk⟩, Nat.lt_succ_self k⟩
            · exact ⟨⟨hxc, hpc⟩, by omega⟩
        have hnotMem : (⟨k, hk_lt_t⟩ : Fin t) ∉ (childrenFinset t p x).filter (fun c => c.1 < k) := by
          simp
        rw [hchild_ins, Finset.card_insert_of_notMem hnotMem, Nat.add_mul, Nat.one_mul]
        omega
      · rw [dpAccEB_step_ne G p τ hpk]
        have hchild_eq :
            (childrenFinset t p x).filter (fun c => c.1 < k + 1) =
              (childrenFinset t p x).filter (fun c => c.1 < k) := by
          ext c
          simp only [Finset.mem_filter, childrenFinset, Finset.mem_univ, true_and]
          refine and_congr_right fun ⟨_, hpc⟩ => ⟨fun hck1 => ?_, fun hck => by omega⟩
          have hck_ne : c.1 ≠ k := fun h => hpk (h ▸ hpc)
          omega
        rw [hchild_eq]
        exact h_ih

theorem card_pieceZ_dpAccEB_le_Q_max {t ω ξ : ℕ} {G : ComputeDigraph}
    {Z : Finset (Fin G.numVerts)} (hZ : Z.card ≤ ξ) (ht : 0 < t)
    {p : ℕ → ℕ} (hp : ∀ z, 0 < z → z < t → p z < z)
    {τ : Fin G.numEdges → Fin t}
    (hbd : IsDigraphBranchDecompOfWidthLe ω G (parentTree t p) τ)
    {x k : ℕ} (hx_lt : x < t) (hk_ge : x + 1 ≤ k) (hk_le : k ≤ t) :
    (pieceZ G Z (dpAccEB G p τ x k)).card ≤ 2 + 3 * (ω + ξ) ∧
    (pieceZ G Z (dpAccEB G p τ x k)).card ≤ Q_max ξ ω := by
  have h1 := card_pieceZ_dpAccEB_le_children hZ ht hp hbd x k hk_ge hk_le
  have hsub : (childrenFinset t p x).filter (fun c => c.1 < k) ⊆ childrenFinset t p x :=
    Finset.filter_subset _ _
  have hc3 : ((childrenFinset t p x).filter (fun c => c.1 < k)).card ≤ 3 :=
    (Finset.card_le_card hsub).trans (card_childrenFinset_le_three hp hbd ⟨x, hx_lt⟩)
  have hmul : ((childrenFinset t p x).filter (fun c => c.1 < k)).card * (ω + ξ) ≤ 3 * (ω + ξ) :=
    Nat.mul_le_mul_right (ω + ξ) hc3
  unfold Q_max
  omega

/-- Abstract folio table: a root count `q` together with a list of `q`-rooted digraphs. -/
abbrev AbstractTable := Σ q : ℕ, List (ComputeRootedDigraph q)

/-- Project `s : Σ q, List (RawCertEntry G q)` to its `AbstractTable`. -/
def sigmaRawToAbstract {G : ComputeDigraph} (s : Σ q, List (RawCertEntry G q)) : AbstractTable :=
  ⟨s.1, s.2.map (·.H)⟩

/-- Strict upper bound on `(allDetailLeCodes q δ).length` across all `q ≤ Q_max ξ ω`. -/
def C_max (δ ξ ω : ℕ) : ℕ :=
  ((List.range (Q_max ξ ω + 1)).map (fun q => (allDetailLeCodes q δ).length)).foldl Nat.max 0 + 1

/-- Base `B` used for digit-packing an `AbstractTable`. -/
def B_tab (δ ξ ω : ℕ) : ℕ :=
  Nat.max (Q_max ξ ω + 1) (C_max δ ξ ω)

/-- Strict upper bound on `encAbstractTable δ ξ ω a`. -/
def T_max (δ ξ ω : ℕ) : ℕ :=
  (B_tab δ ξ ω) ^ (2 + C_max δ ξ ω)

private theorem foldl_max_init_le : ∀ (L : List ℕ) (init : ℕ), init ≤ L.foldl Nat.max init
  | [], init => le_refl init
  | a :: L, init => le_trans (Nat.le_max_left init a) (foldl_max_init_le L (Nat.max init a))

private theorem foldl_max_ge : ∀ (L : List ℕ) (init : ℕ) (x : ℕ), x ∈ L → x ≤ L.foldl Nat.max init
  | [], _, _, h => by contradiction
  | a :: L, init, x, hx => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact le_trans (Nat.le_max_right init x) (foldl_max_init_le L (Nat.max init x))
    · exact foldl_max_ge L (Nat.max init a) x hmem

theorem length_allDetailLeCodes_lt_C_max (δ ξ ω : ℕ) {q : ℕ} (hq : q ≤ Q_max ξ ω) :
    (allDetailLeCodes q δ).length < C_max δ ξ ω := by
  unfold C_max
  have hmem : (allDetailLeCodes q δ).length ∈
      (List.range (Q_max ξ ω + 1)).map (fun q => (allDetailLeCodes q δ).length) := by
    rw [List.mem_map]
    exact ⟨q, List.mem_range.mpr (by omega), rfl⟩
  have hle := foldl_max_ge _ 0 _ hmem
  omega

/-- Encode an `AbstractTable` into a single natural number `< T_max δ ξ ω`. -/
def encAbstractTable (δ ξ ω : ℕ) (a : AbstractTable) : ℕ :=
  let q := a.1
  let Hs := a.2
  let codes := allDetailLeCodes q δ
  let digits : List ℕ :=
    q :: Hs.length :: (List.range (C_max δ ξ ω)).map (fun i =>
      if hi : i < Hs.length then
        codes.idxOf (encRootedDigraph Hs[i])
      else 0)
  packBase (B_tab δ ξ ω) digits

/-- Decode a natural number `tid` back into an `AbstractTable`. -/
def decAbstractTable (δ ξ ω : ℕ) (tid : ℕ) : AbstractTable :=
  let digits := unpackBase (B_tab δ ξ ω) (2 + C_max δ ξ ω) tid
  let q := digits.getD 0 0
  let len := digits.getD 1 0
  let codes := allDetailLeCodes q δ
  let Hs := (List.range len).map (fun i =>
    let idx := digits.getD (2 + i) 0
    let c := codes.getD idx []
    (decRootedDigraph q c).getD (defaultRootedDigraph q))
  ⟨q, Hs⟩

theorem encAbstractTable_lt (δ ξ ω : ℕ) (a : AbstractTable)
    (hq : a.1 ≤ Q_max ξ ω) (hlen : a.2.length ≤ (allDetailLeCodes a.1 δ).length) :
    encAbstractTable δ ξ ω a < T_max δ ξ ω := by
  rcases a with ⟨q, Hs⟩
  dsimp at hq hlen
  have hC : (allDetailLeCodes q δ).length < C_max δ ξ ω :=
    length_allDetailLeCodes_lt_C_max δ ξ ω hq
  have hB_q : Q_max ξ ω + 1 ≤ B_tab δ ξ ω := Nat.le_max_left _ _
  have hB_C : C_max δ ξ ω ≤ B_tab δ ξ ω := Nat.le_max_right _ _
  have hB_pos : 0 < B_tab δ ξ ω := by omega
  unfold encAbstractTable T_max
  dsimp only
  let digits : List ℕ :=
    q :: Hs.length :: (List.range (C_max δ ξ ω)).map (fun i =>
      if hi : i < Hs.length then (allDetailLeCodes q δ).idxOf (encRootedDigraph Hs[i]) else 0)
  have hdigits_len : digits.length = 2 + C_max δ ξ ω := by
    simp [digits]; omega
  rw [← hdigits_len]
  refine packBase_lt hB_pos digits (fun d hd => ?_)
  simp only [digits, List.mem_cons, List.mem_map, List.mem_range] at hd
  rcases hd with rfl | rfl | ⟨i, _, rfl⟩
  · omega
  · omega
  · split_ifs with hi
    · have hle_idx : (allDetailLeCodes q δ).idxOf (encRootedDigraph Hs[i]) ≤
          (allDetailLeCodes q δ).length := List.idxOf_le_length
      omega
    · omega

theorem decAbstractTable_encAbstractTable (δ ξ ω : ℕ) (a : AbstractTable)
    (hq : a.1 ≤ Q_max ξ ω)
    (hlen : a.2.length ≤ (allDetailLeCodes a.1 δ).length)
    (hdet : ∀ H ∈ a.2, H.HasDetailLe δ) :
    decAbstractTable δ ξ ω (encAbstractTable δ ξ ω a) = a := by
  rcases a with ⟨q, Hs⟩
  dsimp at hq hlen hdet
  have hC : (allDetailLeCodes q δ).length < C_max δ ξ ω :=
    length_allDetailLeCodes_lt_C_max δ ξ ω hq
  have hB_q : Q_max ξ ω + 1 ≤ B_tab δ ξ ω := Nat.le_max_left _ _
  have hB_C : C_max δ ξ ω ≤ B_tab δ ξ ω := Nat.le_max_right _ _
  let tailDigits : List ℕ :=
    (List.range (C_max δ ξ ω)).map (fun i =>
      if hi : i < Hs.length then (allDetailLeCodes q δ).idxOf (encRootedDigraph Hs[i]) else 0)
  let digits : List ℕ := q :: Hs.length :: tailDigits
  have hdigits_len : digits.length = 2 + C_max δ ξ ω := by
    simp [digits, tailDigits]; omega
  have hdigits_lt : ∀ d ∈ digits, d < B_tab δ ξ ω := by
    intro d hd
    simp only [digits, tailDigits, List.mem_cons, List.mem_map, List.mem_range] at hd
    rcases hd with rfl | rfl | ⟨i, _, rfl⟩
    · omega
    · omega
    · split_ifs with hi
      · have hle_idx : (allDetailLeCodes q δ).idxOf (encRootedDigraph Hs[i]) ≤
            (allDetailLeCodes q δ).length := List.idxOf_le_length
        omega
      · omega
  have hunpack : unpackBase (B_tab δ ξ ω) (2 + C_max δ ξ ω) (packBase (B_tab δ ξ ω) digits) = digits := by
    rw [← hdigits_len]
    exact unpackBase_packBase digits hdigits_lt
  unfold decAbstractTable encAbstractTable
  change (let u := unpackBase (B_tab δ ξ ω) (2 + C_max δ ξ ω) (packBase (B_tab δ ξ ω) digits)
    let q' := u.getD 0 0
    let len' := u.getD 1 0
    (⟨q', (List.range len').map (fun i =>
      let idx := u.getD (2 + i) 0
      let c := (allDetailLeCodes q' δ).getD idx []
      (decRootedDigraph q' c).getD (defaultRootedDigraph q'))⟩ : AbstractTable)) = ⟨q, Hs⟩
  rw [hunpack]
  have hget0 : digits.getD 0 0 = q := rfl
  have hget1 : digits.getD 1 0 = Hs.length := rfl
  dsimp only
  change (⟨q, (List.range Hs.length).map (fun i =>
    let idx := digits.getD (2 + i) 0
    let c := (allDetailLeCodes q δ).getD idx []
    (decRootedDigraph q c).getD (defaultRootedDigraph q))⟩ : AbstractTable) = ⟨q, Hs⟩
  congr 1
  refine List.ext_getElem (by simp) fun i hi1 hi2 => ?_
  simp only [List.getElem_map, List.getElem_range]
  have hi_C : i < C_max δ ξ ω := by omega
  have h2i : 2 + i = i + 1 + 1 := by omega
  have htail_len : i < tailDigits.length := by simp [tailDigits, hi_C]
  have hget_i : digits.getD (2 + i) 0 =
      (allDetailLeCodes q δ).idxOf (encRootedDigraph (Hs[i]'hi2)) := by
    rw [h2i]
    change tailDigits.getD i 0 = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htail_len, Option.getD_some]
    simp [tailDigits, hi2]
  rw [hget_i]
  have hmem_code : encRootedDigraph (Hs[i]'hi2) ∈ allDetailLeCodes q δ := by
    rw [mem_allDetailLeCodes_iff]
    exact isDetailLeCode_encRootedDigraph (hdet (Hs[i]'hi2) (List.getElem_mem hi2))
  have hidx_lt :
      (allDetailLeCodes q δ).idxOf (encRootedDigraph (Hs[i]'hi2)) < (allDetailLeCodes q δ).length :=
    List.idxOf_lt_length_of_mem hmem_code
  have hcode_eq : (allDetailLeCodes q δ).getD
      ((allDetailLeCodes q δ).idxOf (encRootedDigraph (Hs[i]'hi2))) [] =
      encRootedDigraph (Hs[i]'hi2) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx_lt, Option.getD_some]
    exact List.getElem_idxOf hidx_lt
  rw [hcode_eq, decRootedDigraph_encRootedDigraph]
  rfl

end GraphMinor.Compute
