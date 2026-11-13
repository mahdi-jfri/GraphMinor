module

public import GraphMinor.Compute.Algorithm41
public import GraphMinor.Compute.Join41
public import GraphMinor.Compute.Join441
public import GraphMinor.Compute.Specs105

/-!
# Core (4.1) Claim (`Claim41`), Input Conversions, and Adapter 1 (`Alg105.Alg41RawSpec`)

This file defines:
1. `Alg41CoreInput`, `alg41CoreSize`, `encAlg41CoreIn`, `RawCertEntry`, `CertFolioTable.toRawList`,
   `encRawCertEntry`, `encRawCertModels`, and `Claim41` (the core statement of GM XIII Algorithm
   (4.1), proved as `claim41_proved` in `Join13.lean`).
2. General and specialized conversions from `Alg41CodeInput ξ ω` (on `x.G.toComputeDigraph`) and
   `(G : MultiDigraph n, bdCode)` (on `G.toMultiComputeDigraph`) into `Alg41CoreInput ξ ω`.
3. `scanFolioPrefixLoop` and **Adapter 1** (`alg41RawSpec_of_claim41`), proving
   `Alg105.Alg41RawSpec p ξ δ B` from `Claim41`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Tree Bounds and `Claim41` -/

theorem card_pieceZ_dpAccEB_le_three_mul {t ω ξ : ℕ} {G : ComputeDigraph}
    {Z : Finset (Fin G.numVerts)} (hZ : Z.card ≤ ξ) (ht : 0 < t)
    {p : ℕ → ℕ} (hp : ∀ z, 0 < z → z < t → p z < z)
    {τ : Fin G.numEdges → Fin t}
    (hbd : IsDigraphBranchDecompOfWidthLe ω G (parentTree t p) τ)
    {x k : ℕ} (hx_lt : x < t) (hk_ge : x + 1 ≤ k) (hk_le : k ≤ t) :
    (pieceZ G Z (dpAccEB G p τ x k)).card ≤ 2 + 3 * (ω + ξ) := by
  have h1 := card_pieceZ_dpAccEB_le_children hZ ht hp hbd x k hk_ge hk_le
  have hsub : (childrenFinset t p x).filter (fun c => c.1 < k) ⊆ childrenFinset t p x :=
    Finset.filter_subset _ _
  have hc3 : ((childrenFinset t p x).filter (fun c => c.1 < k)).card ≤ 3 :=
    (Finset.card_le_card hsub).trans (card_childrenFinset_le_three hp hbd ⟨x, hx_lt⟩)
  have hmul : ((childrenFinset t p x).filter (fun c => c.1 < k)).card * (ω + ξ) ≤ 3 * (ω + ξ) :=
    Nat.mul_le_mul_right (ω + ξ) hc3
  omega

/-- **The core claim of Algorithm (4.1):**
For every fixed `δ, ξ, ω : ℕ`, there is a Word RAM program `P` that runs in `O(ε)` time on any
`x : Alg41CoreInput ξ ω` (`s₀.arrs inArr = encAlg41CoreIn x`) and writes the `δ`-folio of `x.G`
relative to `x.Z` (`encFolioSetRep T.toFolioSetRep`) followed by the serialized models
(`encRawCertModels T.toRawList`) to `outArr`, where `T = computeFolioDP x.G x.Z δ x.ht x.p x.hp x.τ`. -/
def Claim41 : Prop :=
  ∀ δ ξ ω : ℕ, ∃ P : Cmd,
    ComputesArrRelInTime (alg41CoreSize (ξ := ξ) (ω := ω))
      (encAlg41CoreIn (ξ := ξ) (ω := ω))
      (fun x out =>
        let T := computeFolioDP x.G x.Z δ x.ht x.p x.hp x.τ
        out = encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList)
      P (fun ε => ε)

/-! ### Section 2: Constructing `Alg41CoreInput` from `Alg41CodeInput` and `(G, bdCode)` -/

/-- General constructor for `Alg41CoreInput ξ ω` from either the small-graph convention
(`G.numEdges ≤ 1 ∧ t = 1`) or a valid branch-decomposition
`IsDigraphBranchDecompOfWidthLe ω G (parentTree t p) τ`. -/
def Alg41CoreInput.ofBranchDecompOrSmall {ξ ω : ℕ}
    (G : ComputeDigraph) (Z : Finset (Fin G.numVerts)) (hZ : Z.card ≤ ξ)
    (t : ℕ) (ht : 0 < t) (ht_le : t ≤ 2 * G.numEdges + 1)
    (p : ℕ → ℕ) (hp0 : p 0 = 0) (hp : ∀ z, 0 < z → z < t → p z < z)
    (τ : Fin G.numEdges → Fin t)
    (hcases : (G.numEdges ≤ 1 ∧ t = 1) ∨
      IsDigraphBranchDecompOfWidthLe ω G (parentTree t p) τ) :
    Alg41CoreInput ξ ω where
  G := G
  Z := Z
  hZ := hZ
  t := t
  ht := ht
  ht_le := ht_le
  p := p
  hp0 := hp0
  hp := hp
  τ := τ
  hch := fun node => by
    rcases hcases with ⟨_, ht1⟩ | hbd
    · have hemp : childrenFinset t p node.1 = ∅ := by
        ext c
        simp only [childrenFinset, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false]
        have := c.2
        omega
      rw [hemp]
      simp
    · exact card_childrenFinset_le_three hp hbd node
  hleaf := fun node => by
    rcases hcases with ⟨hm1, _⟩ | hbd
    · calc (Finset.univ.filter (fun e : Fin G.numEdges => (τ e).1 = node)).card
        _ ≤ (Finset.univ : Finset (Fin G.numEdges)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = G.numEdges := by simp
        _ ≤ 1 := hm1
    · exact card_leafEdges_le_one hbd node
  hQ_acc := fun node hnode k hk_ge hk_le => by
    rcases hcases with ⟨hm1, _⟩ | hbd
    · have hcardE : (dpAccEB G p τ node k).card ≤ 1 := by
        calc (dpAccEB G p τ node k).card
          _ ≤ (Finset.univ : Finset (Fin G.numEdges)).card :=
              Finset.card_le_card (Finset.subset_univ _)
          _ = G.numEdges := by simp
          _ ≤ 1 := hm1
      have h2 := (card_pieceZ_le_two_of_card_le_one G Z hcardE).2
      omega
    · exact card_pieceZ_dpAccEB_le_three_mul hZ ht hp hbd hnode hk_ge hk_le
  hQ_child := fun c hc_pos hc_lt => by
    rcases hcases with ⟨_, ht1⟩ | hbd
    · omega
    · exact card_pieceZ_dpEB_le hZ ht hp hbd (x := ⟨c, hc_lt⟩) hc_pos

/-- Normalized parent map `ℕ → ℕ` for `x : Alg41CodeInput ξ ω`. -/
def normParentCodeFn {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) (z : ℕ) : ℕ :=
  if z = 0 then 0 else pCode x z

theorem normParentCodeFn_zero {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) :
    normParentCodeFn x 0 = 0 := rfl

theorem normParentCodeFn_lt {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) :
    ∀ z, 0 < z → z < tCode x → normParentCodeFn x z < z := by
  intro z hz_pos hz_lt
  unfold normParentCodeFn
  rw [ite_eq_right (by omega)]
  exact hpCode x z hz_pos hz_lt

theorem parentTree_normParentCodeFn_eq_bdTree {ξ ω : ℕ} (x : Alg41CodeInput ξ ω)
    (_ht : 0 < bdNumTreeVerts x.bdCode)
    (hpar : ∀ z, 0 < z → z < bdNumTreeVerts x.bdCode → bdParent x.bdCode z < z) :
    parentTree (bdNumTreeVerts x.bdCode) (normParentCodeFn x) = bdTree x.bdCode := by
  ext u v
  simp only [parentTree, bdTree]
  refine and_congr_right fun _ => or_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · rintro ⟨hlt, hpu⟩
    refine ⟨hlt, ?_⟩
    have hlt_p := hpar u.1 hlt u.2
    unfold normParentCodeFn pCode at hpu
    rw [ite_eq_right (by omega), ite_eq_left hlt_p] at hpu
    exact hpu
  · rintro ⟨hlt, hpu⟩
    refine ⟨hlt, ?_⟩
    have hlt_p := hpar u.1 hlt u.2
    unfold normParentCodeFn pCode
    rw [ite_eq_right (by omega), ite_eq_left hlt_p]
    exact hpu
  · rintro ⟨hlt, hpv⟩
    refine ⟨hlt, ?_⟩
    have hlt_p := hpar v.1 hlt v.2
    unfold normParentCodeFn pCode at hpv
    rw [ite_eq_right (by omega), ite_eq_left hlt_p] at hpv
    exact hpv
  · rintro ⟨hlt, hpv⟩
    refine ⟨hlt, ?_⟩
    have hlt_p := hpar v.1 hlt v.2
    unfold normParentCodeFn pCode
    rw [ite_eq_right (by omega), ite_eq_left hlt_p]
    exact hpv

theorem isDigraphBranchDecompOfWidthLe_of_eq {t ω : ℕ} {G : ComputeDigraph}
    {T₁ T₂ : SimpleGraph (Fin t)} [DecidableRel T₁.Adj] [DecidableRel T₂.Adj]
    (hT : T₁ = T₂) {τ : Fin G.numEdges → Fin t}
    (h : IsDigraphBranchDecompOfWidthLe ω G T₁ τ) :
    IsDigraphBranchDecompOfWidthLe ω G T₂ τ := by
  subst hT
  convert h

theorem isDigraphBranchDecompOfWidthLe_cast_t {t₁ t₂ ω : ℕ} {G : ComputeDigraph}
    (ht : t₁ = t₂) (p : ℕ → ℕ)
    (τ₁ : Fin G.numEdges → Fin t₁) (τ₂ : Fin G.numEdges → Fin t₂)
    (hτ : ∀ e, (τ₁ e).1 = (τ₂ e).1)
    (h : IsDigraphBranchDecompOfWidthLe ω G (parentTree t₁ p) τ₁) :
    IsDigraphBranchDecompOfWidthLe ω G (parentTree t₂ p) τ₂ := by
  subst ht
  have hτ_eq : τ₁ = τ₂ := funext fun e => Fin.ext (hτ e)
  subst hτ_eq
  exact h

/-- Convert `x : Alg41CodeInput ξ ω` directly into `Alg41CoreInput ξ ω` on `x.G.toComputeDigraph`. -/
noncomputable def Alg41CodeInput.toCoreInput {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) :
    Alg41CoreInput ξ ω :=
  Alg41CoreInput.ofBranchDecompOrSmall
    x.G.toComputeDigraph x.Z x.hZ
    (tCode x) (htCode x)
    (by rw [x.G.toComputeDigraph_numEdges, x.G.length_directedEdgesList]; exact tCode_le x)
    (normParentCodeFn x) (normParentCodeFn_zero x) (normParentCodeFn_lt x)
    (tauCode x)
    (by
      rcases x.hbd.2.2.2 with ⟨hm1, ht0, _⟩ | ⟨_, ht_pos, _, hpar, _, hbd_multi⟩
      · left
        refine ⟨?_, ?_⟩
        · rw [x.G.toComputeDigraph_numEdges, x.G.length_directedEdgesList]
          exact hm1
        · simp [tCode, ht0]
      · right
        have htc : bdNumTreeVerts x.bdCode = tCode x := by simp [tCode, ht_pos]
        have hbd_bdTree :
            IsDigraphBranchDecompOfWidthLe ω x.G.toComputeDigraph
              (bdTree x.bdCode)
              (bdTau x.G x.bdCode ht_pos ∘ x.G.computeToMultiEdgeEquiv) :=
          (isDigraphBranchDecompOfWidthLe_toComputeDigraph_iff_isMultiBranchDecompOfWidthLe
            ω x.G (bdTree x.bdCode) (bdTau x.G x.bdCode ht_pos)).mpr hbd_multi
        have hbd_par :
            IsDigraphBranchDecompOfWidthLe ω x.G.toComputeDigraph
              (parentTree (bdNumTreeVerts x.bdCode) (normParentCodeFn x))
              (bdTau x.G x.bdCode ht_pos ∘ x.G.computeToMultiEdgeEquiv) :=
          isDigraphBranchDecompOfWidthLe_of_eq
            (parentTree_normParentCodeFn_eq_bdTree x ht_pos hpar).symm hbd_bdTree
        exact isDigraphBranchDecompOfWidthLe_cast_t htc (normParentCodeFn x)
          (bdTau x.G x.bdCode ht_pos ∘ x.G.computeToMultiEdgeEquiv) (tauCode x)
          (fun e => by simp [tauCode, ht_pos]) hbd_par)

@[simp]
theorem Alg41CodeInput.alg41CoreSize_toCoreInput {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) :
    alg41CoreSize x.toCoreInput = alg41CodeSize x := by
  unfold alg41CoreSize alg41CodeSize Alg41CodeInput.toCoreInput
    Alg41CoreInput.ofBranchDecompOrSmall
  dsimp only
  rw [x.G.length_directedEdgesList]

@[simp]
theorem Alg41CodeInput.encAlg41CoreIn_toCoreInput {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) :
    encAlg41CoreIn x.toCoreInput = encAlg41CodeIn x := by
  rfl

/-! ### Section 3: Prefix-Truncation Gadget and Adapter 1 (`Claim41 → Alg105.Alg41RawSpec`) -/

/-- Loop body of `scanFolioPrefixLoop`: reads `r_len := a_src[r_pos]` and advances
`r_pos := (r_pos + 1) + r_len`. -/
def scanFolioPrefixBody (a_src : Arr) (r_pos r_len : Reg) : Cmd :=
  .seq (.assign r_len (.read a_src (.reg r_pos)))
    (.assign r_pos (.op .add (.op .add (.reg r_pos) (.const 1)) (.reg r_len)))

theorem scanFolioPrefixLoop_exec {w : ℕ} (a_src : Arr) (r_i r_k r_pos r_len : Reg)
    (hne_ik : r_i ≠ r_k) (hne_ip : r_i ≠ r_pos) (hne_il : r_i ≠ r_len)
    (hne_kp : r_k ≠ r_pos) (hne_kl : r_k ≠ r_len) (hne_pl : r_pos ≠ r_len)
    (hw1 : 1 < 2 ^ w)
    (cs : List (List ℕ)) (pre suf : List ℕ) (i₀ : ℕ)
    (hk_w : i₀ + cs.length < 2 ^ w)
    (hpos_w : (pre ++ cs.flatMap (fun c => c.length :: c)).length < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = pre ++ cs.flatMap (fun c => c.length :: c) ++ suf)
    (hri : s.regs r_i = i₀)
    (hrk : s.regs r_k = i₀ + cs.length)
    (hrpos : s.regs r_pos = pre.length) :
    ∃ s' t,
      Exec w (forUp r_i (.reg r_k) (scanFolioPrefixBody a_src r_pos r_len)) s s' t ∧
      t ≤ 3 + 17 * cs.length ∧
      s'.regs r_pos = (pre ++ cs.flatMap (fun c => c.length :: c)).length ∧
      (∀ a : Arr, s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_i → r ≠ r_pos → r ≠ r_len → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction cs generalizing pre i₀ s with
  | nil =>
    have hi₀_w : i₀ < 2 ^ w := by simpa using hk_w
    have hcond : (Expr.op .lt (.reg r_i) (.reg r_k)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrk, hi₀_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by simp, by simpa using hrpos,
      fun _ => rfl, fun _ _ _ _ => rfl⟩
  | cons c cs ih =>
    simp only [List.length_cons, List.flatMap_cons] at hk_w hpos_w hsrc hrk
    have hi₀_lt : i₀ < i₀ + (cs.length + 1) := by omega
    have hi₀_w : i₀ < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_i) (.reg r_k)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrk, hi₀_w, hk_w, hi₀_lt, hw1]
    have hpre_w : pre.length < 2 ^ w := by
      simp only [List.length_append, List.length_cons] at hpos_w
      omega
    have hclen_w : c.length < 2 ^ w := by
      simp only [List.length_append, List.length_cons] at hpos_w
      omega
    have hpre1_w : pre.length + 1 < 2 ^ w := by
      simp only [List.length_append, List.length_cons] at hpos_w
      omega
    have hnext_w : pre.length + 1 + c.length < 2 ^ w := by
      simp only [List.length_append, List.length_cons] at hpos_w
      omega
    have hidx_lt : pre.length < (s.arrs a_src).length := by
      rw [hsrc]
      simp only [List.length_append, List.length_cons]
      omega
    have hget_len : (s.arrs a_src)[pre.length]'hidx_lt = c.length := by
      have hsrc' : s.arrs a_src = pre ++ (c.length :: (c ++ cs.flatMap (fun c => c.length :: c) ++ suf)) := by
        simpa [List.append_assoc] using hsrc
      have h1 : (pre ++ (c.length :: (c ++ cs.flatMap (fun c => c.length :: c) ++ suf)))[pre.length]'(by simp) = c.length := by
        rw [List.getElem_append_right (le_refl _)]
        simp
      simp [hsrc']
    -- 1. r_len := a_src[r_pos]
    let s₁ := s.setReg r_len c.length
    have hread : (Expr.read a_src (.reg r_pos)).eval w s = some c.length := by
      unfold Expr.eval
      have hreg_pos : (Expr.reg r_pos).eval w s = some pre.length := by
        simp [Expr.eval, checkWord, hrpos, hpre_w]
      rw [hreg_pos]
      simp [hidx_lt, hget_len, checkWord, hclen_w]
    have hex₁ : Exec w (.assign r_len (.read a_src (.reg r_pos))) s s₁ 3 :=
      .assign hread
    -- 2. r_pos := (r_pos + 1) + r_len
    have hrpos₁ : s₁.regs r_pos = pre.length := by
      simp [s₁, State.setReg, hne_pl, hrpos]
    let s₂ := s₁.setReg r_pos (pre.length + 1 + c.length)
    have hex₂ : Exec w (.assign r_pos (.op .add (.op .add (.reg r_pos) (.const 1)) (.reg r_len)))
        s₁ s₂ 6 :=
      .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hrpos₁, hpre_w, hw1, hpre1_w, hclen_w, hnext_w])
    -- 3. r_i := r_i + 1
    have hri₂ : s₂.regs r_i = i₀ := by
      simp [s₂, s₁, State.setReg, hne_ip, hne_il, hri]
    let s₃ := s₂.setReg r_i (i₀ + 1)
    have hex₃ : Exec w (.assign r_i (.op .add (.reg r_i) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hri₂, hi₀_w, hw1, show i₀ + 1 < 2 ^ w by omega])
    let pre' := pre ++ (c.length :: c)
    have hpre'_len : pre'.length = pre.length + 1 + c.length := by
      simp [pre']; omega
    have hsrc₃ : s₃.arrs a_src = pre' ++ cs.flatMap (fun c => c.length :: c) ++ suf := by
      simpa [s₃, s₂, s₁, pre', List.append_assoc] using hsrc
    rcases ih pre' (i₀ + 1) (by omega)
        (by simpa [pre', List.append_assoc] using hpos_w)
        (s := s₃) hsrc₃
        (by simp [s₃])
        (by
          simp only [s₃, s₂, s₁, State.setReg_regs_ne _ _ hne_ik.symm,
            State.setReg_regs_ne _ _ hne_kp, State.setReg_regs_ne _ _ hne_kl, hrk]
          omega)
        (by simp [s₃, s₂, State.setReg, hne_ip.symm, hpre'_len]) with
      ⟨s₄, t₄, hex₄, ht₄, hrpos₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((3 + 6) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex₂) hex₃) hex₄,
      by simp only [List.length_cons]; omega,
      by simpa [pre', List.append_assoc] using hrpos₄,
      harr₄,
      fun r hri_ne hrp_ne hrl_ne => by
        rw [hreg₄ r hri_ne hrp_ne hrl_ne]
        simp [s₃, s₂, s₁, State.setReg, hri_ne, hrp_ne, hrl_ne]⟩

/-- Truncate `a_src = outArr` holding `encFolioSetRep F ++ rest` to `encFolioSetRep F` in `outArr`,
using scratch array `a_tmp` and registers `r_base .. r_base + 7`. -/
def truncFolioOutProg (a_tmp : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.read outArr (.const 0)))
    (.seq (.assign (r_base + 1) (.const 1))
      (.seq (.assign (r_base + 2) (.const 0))
        (.seq (forUp (r_base + 2) (.reg r_base)
            (scanFolioPrefixBody outArr (r_base + 1) (r_base + 3)))
          (.seq (readSliceProg outArr (.const 0) a_tmp (.reg (r_base + 1)) (r_base + 4))
            (copyFullArrProg a_tmp outArr (r_base + 1) (r_base + 4))))))

/-- Upper bound on `(encFolioSetRep F).length` for any `F : FolioSetRep q δ` with `q ≤ ξ`. -/
def maxEncFolioSetRepLen (ξ δ : ℕ) : ℕ :=
  1 + ((List.range (ξ + 1)).map (fun q => (allDetailLeCodes q δ).length)).sum * (3 + ξ + 2 * δ)

theorem length_codes_le_sum_range {q ξ δ : ℕ} (hq : q ≤ ξ) (F : FolioSetRep q δ) :
    F.codes.length ≤ ((List.range (ξ + 1)).map (fun q' => (allDetailLeCodes q' δ).length)).sum := by
  have h1 := length_codes_le_allDetailLeCodes F
  have hmem : q ∈ List.range (ξ + 1) := List.mem_range.mpr (by omega)
  have h2 : (allDetailLeCodes q δ).length ≤
      ((List.range (ξ + 1)).map (fun q' => (allDetailLeCodes q' δ).length)).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem hmem)
  omega

theorem length_encFolioSetRep_le_max {q ξ δ : ℕ} (hq : q ≤ ξ) (F : FolioSetRep q δ) :
    (encFolioSetRep F).length ≤ maxEncFolioSetRepLen ξ δ := by
  have hcodes_len := length_codes_le_sum_range hq F
  have hall : ∀ c ∈ F.codes, (c.length :: c).length ≤ 3 + ξ + 2 * δ := by
    intro c hc
    rcases length_and_words_le_of_isDetailLeCode (F.all_detail c hc) with ⟨hlen, _⟩
    simp only [List.length_cons]
    omega
  have hflat : (F.codes.flatMap (fun c => c.length :: c)).length ≤
      F.codes.length * (3 + ξ + 2 * δ) := by
    generalize F.codes = cs at hall
    induction cs with
    | nil => simp
    | cons c cs ih =>
      have hc_le := hall c List.mem_cons_self
      have hcs_le := ih (fun c' hc' => hall c' (List.mem_cons_of_mem c hc'))
      simp only [List.flatMap_cons, List.length_append, List.length_cons] at hc_le ⊢
      rw [Nat.add_mul, Nat.one_mul]
      omega
  unfold encFolioSetRep maxEncFolioSetRepLen
  simp only [List.length_append, List.length_singleton]
  have hmul : F.codes.length * (3 + ξ + 2 * δ) ≤
      ((List.range (ξ + 1)).map (fun q' => (allDetailLeCodes q' δ).length)).sum * (3 + ξ + 2 * δ) :=
    Nat.mul_le_mul_right _ hcodes_len
  omega

theorem words_encFolioSetRep_le_max {q ξ δ : ℕ} (hq : q ≤ ξ) (F : FolioSetRep q δ) :
    ∀ u ∈ encFolioSetRep F, u ≤ maxEncFolioSetRepLen ξ δ + ξ + 2 * δ + 3 := by
  intro u hu
  unfold encFolioSetRep at hu
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap] at hu
  rcases hu with rfl | ⟨c, hc, rfl | huc⟩
  · have h1 := length_codes_le_sum_range hq F
    unfold maxEncFolioSetRepLen
    have hmul :
        ((List.range (ξ + 1)).map (fun q' => (allDetailLeCodes q' δ).length)).sum * 1 ≤
        ((List.range (ξ + 1)).map (fun q' => (allDetailLeCodes q' δ).length)).sum * (3 + ξ + 2 * δ) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · rcases length_and_words_le_of_isDetailLeCode (F.all_detail c hc) with ⟨hlen, _⟩
    omega
  · rcases length_and_words_le_of_isDetailLeCode (F.all_detail c hc) with ⟨_, hwords⟩
    have := hwords u huc
    omega

theorem truncFolioOutProg_exec {w q ξ δ : ℕ} (hq : q ≤ ξ) (F : FolioSetRep q δ)
    (rest : List ℕ) (a_tmp : Arr) (r_base : Reg)
    (hne_tmp : a_tmp ≠ outArr)
    (hw_max : maxEncFolioSetRepLen ξ δ + ξ + 2 * δ + 4 < 2 ^ w)
    {s : State}
    (hout : s.arrs outArr = encFolioSetRep F ++ rest) :
    ∃ s' t,
      Exec w (truncFolioOutProg a_tmp r_base) s s' t ∧
      t ≤ 80 * maxEncFolioSetRepLen ξ δ + 60 ∧
      s'.arrs outArr = encFolioSetRep F ∧
      (∀ a : Arr, a ≠ outArr → a ≠ a_tmp → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hlen_F := length_encFolioSetRep_le_max hq F
  have hk_le : F.codes.length ≤ maxEncFolioSetRepLen ξ δ := by
    have : F.codes.length ≤ (encFolioSetRep F).length := by
      unfold encFolioSetRep
      simp only [List.length_append, List.length_singleton]
      have : F.codes.length ≤ (F.codes.flatMap (fun c => c.length :: c)).length := by
        induction F.codes with
        | nil => simp
        | cons c cs ih =>
          simp only [List.flatMap_cons, List.length_append, List.length_cons]
          omega
      omega
    omega
  have hk_w : F.codes.length < 2 ^ w := by omega
  have hpos_w : (encFolioSetRep F).length < 2 ^ w := by omega
  have hidx0 : 0 < (s.arrs outArr).length := by
    rw [hout]; simp [encFolioSetRep]
  have hget0 : (s.arrs outArr)[0]'hidx0 = F.codes.length := by
    simp [hout, encFolioSetRep]
  -- 1. r_base := outArr[0]
  let s₁ := s.setReg r_base F.codes.length
  have hex₁ : Exec w (.assign r_base (.read outArr (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, hidx0, hget0, hk_w])
  -- 2. r_base + 1 := 1
  let s₂ := s₁.setReg (r_base + 1) 1
  have hex₂ : Exec w (.assign (r_base + 1) (.const 1)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h1_w])
  -- 3. r_base + 2 := 0
  let s₃ := s₂.setReg (r_base + 2) 0
  have hex₃ : Exec w (.assign (r_base + 2) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 4. scanFolioPrefixLoop
  rcases scanFolioPrefixLoop_exec outArr (r_base + 2) r_base (r_base + 1) (r_base + 3)
      (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
      h1_w F.codes [F.codes.length] rest 0
      (by simpa using hk_w) (by simpa [encFolioSetRep] using hpos_w)
      (s := s₃)
      (by simpa [s₃, s₂, s₁, encFolioSetRep] using hout)
      (by simp [s₃])
      (by simp [s₃, s₂, s₁, State.setReg])
      (by simp [s₃, s₂, State.setReg]) with
    ⟨s₄, t₄, hex₄, ht₄, hrpos₄, harr₄, hreg₄⟩
  have hrpos₄' : s₄.regs (r_base + 1) = (encFolioSetRep F).length := by
    simpa [encFolioSetRep] using hrpos₄
  -- 5. readSliceProg outArr 0 a_tmp (r_base + 1) (r_base + 4)
  have hout₄ : s₄.arrs outArr = ([] : List ℕ) ++ encFolioSetRep F ++ rest := by
    rw [harr₄ outArr]
    simpa [s₃, s₂, s₁] using hout
  have hwords_F : ∀ u ∈ encFolioSetRep F, u < 2 ^ w := by
    intro u hu
    have := words_encFolioSetRep_le_max hq F u hu
    omega
  rcases readSliceProg_exec (w := w) (n := (encFolioSetRep F).length) (off := 0)
      outArr a_tmp (.const 0) (r_base + 1) (r_base + 4)
      hne_tmp.symm (by omega) [] (encFolioSetRep F) rest rfl rfl
      hwords_F h1_w (by omega)
      (by simp [Expr.eval, checkWord, h0_w])
      hout₄ hrpos₄' with
    ⟨s₅, t₅, hex₅, ht₅, htmp₅, harr₅, hreg₅⟩
  dsimp [Expr.cost] at ht₅
  -- 6. copyFullArrProg a_tmp outArr (r_base + 1) (r_base + 4)
  have hrpos₅ : s₅.regs (r_base + 1) = (encFolioSetRep F).length :=
    (hreg₅ (r_base + 1) (by omega)).trans hrpos₄'
  rcases copyFullArrProg_exec (w := w) (len := (encFolioSetRep F).length)
      a_tmp outArr (r_base + 1) (r_base + 4)
      hne_tmp (by omega) (encFolioSetRep F) rfl hwords_F h1_w hpos_w
      htmp₅ hrpos₅ with
    ⟨s₆, t₆, hex₆, ht₆, hout₆, harr₆, hreg₆⟩
  refine ⟨s₆, 3 + (2 + (2 + (t₄ + (t₅ + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, hout₆,
    fun a ha_out ha_tmp => by
      rw [harr₆ a ha_out, harr₅ a ha_tmp, harr₄ a]
      simp [s₃, s₂, s₁],
    fun r hr => by
      dsimp [Reg] at hr
      rw [hreg₆ r (by dsimp [Reg]; omega), hreg₅ r (by dsimp [Reg]; omega),
          hreg₄ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
      simp [s₃, s₂, s₁, State.setReg,
        show (r : Reg) ≠ r_base + 2 by dsimp [Reg]; omega,
        show (r : Reg) ≠ r_base + 1 by dsimp [Reg]; omega,
        show (r : Reg) ≠ r_base by dsimp [Reg]; omega]⟩

/-- **Adapter 1 (`Claim41 → Alg105.Alg41RawSpec p ξ δ B`):**
Proves `Alg105.Alg41RawSpec p ξ δ B` (`Specs105.lean`) from `Claim41` by normalizing the written
branch-decomposition (`normalizeBD41Prog`), packing `encAlg41CoreIn` into `inArr`
(`packAlg41InProg`), running `P` from `Claim41 δ ξ B`, and truncating `outArr` to its
`encFolioSetRep F` prefix (`truncFolioOutProg`). -/
theorem alg41RawSpec_of_claim41 (h41 : Claim41) (p ξ δ B : ℕ) :
    Alg105.Alg41RawSpec p ξ δ B := by
  rcases h41 δ ξ B with ⟨P, C₀, c₀, hC₀, hc₀, hexec₀⟩
  let b := alg105ArrBase p
  let L := maxEncFolioSetRepLen ξ δ
  let c41 := c₀ + L + ξ + 2 * δ + 5
  let C41 := C₀ + 80 * L + 250
  refine ⟨.seq (normalizeBD41Prog b)
      (.seq (packAlg41InProg b) (.seq P (truncFolioOutProg 60 60))),
    C41, c41, by omega, by omega,
    fun {w n_i} G_i Z_i t par f_tau s₀ hw hZ hbd _ hb1 hr26 hr28 hr52
      hb2_len hb2_get hb3_len hb3_get hb5 hb6 => ?_⟩
  let N := n_i + G_i.numEdges + 1
  have hpow_c41 : (N + 2) ^ c41 < 2 ^ w :=
    Nat.lt_of_lt_of_le (pow_lt_two_pow_wordSize (c := c41) (by omega) N)
      (Nat.pow_le_pow_right (by omega) hw)
  have hbase_ge3 : 3 ≤ N + 2 := by omega
  have hc41_lt : c41 < 2 ^ w := by
    have : c41 < (N + 2) ^ c41 := by
      have h1 : c41 < 2 ^ c41 := Nat.lt_two_pow_self
      have h2 : 2 ^ c41 ≤ (N + 2) ^ c41 := Nat.pow_le_pow_left (by omega) c41
      omega
    omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hsz_w : 5 * (G_i.numEdges + n_i + 1) < 2 ^ w := by
    have hcube : (N + 2) ^ 3 ≤ (N + 2) ^ c41 :=
      Nat.pow_le_pow_right (by omega) (by omega : 3 ≤ c41)
    have hexp : 5 * N + 2 < (N + 2) ^ 3 := by
      have h1 : (N + 2) ^ 3 = (N + 2) * ((N + 2) * (N + 2)) := by
        rw [show (3 : ℕ) = 2 + 1 by rfl, Nat.pow_succ, Nat.pow_two, Nat.mul_comm]
      have h2 : 3 * ((N + 2) * (N + 2)) ≤ (N + 2) * ((N + 2) * (N + 2)) :=
        Nat.mul_le_mul_right _ hbase_ge3
      have h3 : 2 * N + 4 ≤ (N + 2) * (N + 2) := by
        rw [Nat.add_mul, Nat.mul_add]; omega
      omega
    dsimp [N] at *
    omega
  have hm_w : G_i.numEdges < 2 ^ w := by omega
  -- 1. normalizeBD41Prog b
  rcases normalizeBD41Prog_exec G_i Z_i hZ b par f_tau hw2 hm_w hbd
      hr28 hr52 hb2_len hb2_get hb3_len hb3_get with
    ⟨s₁, t₁, hex₁, ht₁, hr52_1, hb2_1, hb3_1, harr₁, hreg₁⟩
  -- 2. packAlg41InProg b
  rcases packAlg41InProg_exec G_i Z_i hZ p par f_tau hw3 hsz_w hbd
      ((hreg₁ 26 (by decide)).trans hr26)
      ((hreg₁ 28 (by decide)).trans hr28)
      hr52_1
      ((harr₁ (b + 1) (by dsimp [b, alg105ArrBase, Arr]; omega)
        (by dsimp [b, alg105ArrBase, Arr]; omega)).trans hb1)
      hb2_1 hb3_1
      ((harr₁ (b + 5) (by dsimp [b, alg105ArrBase, Arr]; omega)
        (by dsimp [b, alg105ArrBase, Arr]; omega)).trans hb5)
      ((harr₁ (b + 6) (by dsimp [b, alg105ArrBase, Arr]; omega)
        (by dsimp [b, alg105ArrBase, Arr]; omega)).trans hb6) with
    ⟨s₂, t₂, hex₂, ht₂, hin₂⟩
  -- 3. P from Claim41 δ ξ B
  let x41 := writtenToAlg41CodeInput G_i Z_i hZ t par f_tau hbd
  let x_core := x41.toCoreInput
  have hin₂_core : s₂.arrs inArr = encAlg41CoreIn x_core := by
    rw [x41.encAlg41CoreIn_toCoreInput, hin₂]
  rcases hexec₀ x_core s₂ hin₂_core with ⟨s₃, t₃, hex₃_w0, ht₃, hout₃⟩
  dsimp only at ht₃
  have hsz_core : alg41CoreSize x_core = G_i.numEdges + n_i + 1 := by
    rw [x41.alg41CoreSize_toCoreInput]
    rfl
  have hw0_le : wordSize c₀ (alg41CoreSize x_core) ≤ w := by
    rw [hsz_core, Nat.add_comm G_i.numEdges n_i]
    exact le_trans (wordSize_mono_left (by omega : c₀ ≤ c41) N) hw
  have hex₃ : Exec w P s₂ s₃ t₃ := Exec.mono_wordSize hw0_le hex₃_w0
  -- 4. truncFolioOutProg 60 60
  let T := computeFolioDP x_core.G x_core.Z δ x_core.ht x_core.p x_core.hp x_core.τ
  have hout₃_eq : s₃.arrs outArr = encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList :=
    hout₃
  rcases truncFolioOutProg_exec (w := w) hZ T.toFolioSetRep (encRawCertModels T.toRawList)
      60 60 (by decide) (by omega) hout₃_eq with
    ⟨s₄, t₄, hex₄, ht₄, hout₄, _, _⟩
  -- 5. T.toFolioSetRep satisfies IsDeltaFolioRep δ G_i Z_i
  have hvalid : IsValidAlg41CodeOutput δ x41 (certTableToAlg41CodeOutput x41 T) :=
    isValidAlg41CodeOutput_certTableToAlg41CodeOutput x41 δ T
  have hF_eq : T.toFolioSetRep = hvalid.toFolioSetRep := by
    unfold CertFolioTable.toFolioSetRep IsValidAlg41CodeOutput.toFolioSetRep
      certTableToAlg41CodeOutput
    congr 1
    rw [List.map_map]
    rfl
  have hdelta : IsDeltaFolioRep δ G_i Z_i T.toFolioSetRep := by
    rw [hF_eq]
    exact hvalid.isDeltaFolioRep
  rw [hsz_core] at ht₃
  have htot : t₁ + (t₂ + (t₃ + t₄)) ≤ C41 * (n_i + G_i.numEdges + 1) := by
    have h1 : 1 ≤ n_i + G_i.numEdges + 1 := by omega
    have hmul : C41 * (n_i + G_i.numEdges + 1) =
        C₀ * (G_i.numEdges + n_i + 1) +
        250 * (n_i + G_i.numEdges + 1) +
        (80 * L) * (n_i + G_i.numEdges + 1) := by
      dsimp [C41]
      ring
    have hge : 80 * L ≤ (80 * L) * (n_i + G_i.numEdges + 1) :=
      Nat.le_mul_of_pos_right _ h1
    omega
  exact ⟨s₄, t₁ + (t₂ + (t₃ + t₄)), T.toFolioSetRep,
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), htot, hout₄, hdelta⟩

end GraphMinor.Compute
