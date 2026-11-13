module

public import GraphMinor.Compute.Algorithm74Route

/-!
# Height-Independent Word RAM Program for Graph Minors XIII, (7.4)

This file completes the height-independent Word RAM implementation for Graph Minors XIII, (7.4)
(page 90):

1. **Sub-step 5a (`inWallCoordBranchSetExpr`, `wallEdgeActiveExpr`):**
   Word RAM boolean expressions testing coarse-grid membership (`inHSegExpr`, `inVSegExpr`,
   `inPerimPathExpr`, `isPuncturedByExpr`, `inConnPathExpr`, `inDetourPathExpr`,
   `inInteriorBranchSetExpr`, `inRoutedBranchSetExpr`, `inLiftGridCoarseBranchSetExpr`) and lifted
   wall membership (`inWallCoordBranchSetExpr`, `wallEdgeActiveExpr`) directly from the routed
   terminal registers.
2. **Sub-step 5b (`markWallBranchVertsCmd`):**
   Runtime `.while` loop over the `V_J = elemWallNumVerts x.h` branch vertices in `inArr`,
   marking those in `wallCoordBranchSet hp x gamma` in `outArr`.
3. **Sub-step 5c (`markWallInternalVertsCmd`):**
   Runtime `.while` loop over the `E_J = (elemWallEdges x.h).length` internal vertex lists in
   `inArr`, marking `x.W.internalVerts k` for each active wall edge `k`.
4. **Sub-step 5d (`alg74Prog` and `algorithm_7_4`):**
   Assembles the complete height-independent program `alg74Prog p` (depending only on `p`) and
   proves `algorithm_7_4 : Algorithm74Statement`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph
open scoped BigOperators

set_option linter.deprecated false

attribute [local irreducible] elemWallCoords elemWallNumVerts elemWallEdges coordOf alg74LiftRadius

/-! ### Section 5: Populating Wall Branch Sets in `outArr` and Final Assembly -/

/-- For `1 ≤ h`, the elementary wall of height `h` has at least one edge. -/
theorem elemWallEdges_length_pos {h : ℕ} (hh1 : 1 ≤ h) :
    0 < (elemWallEdges h).length := by
  have hV : 2 ≤ elemWallNumVerts h := by
    rw [elemWallNumVerts_eq]
    have : 2 * h + 4 ≤ (h + 1) * (2 * h + 2) := by nlinarith
    omega
  have h1 : 0 < (elemWallEdgesPrefix h 1).length := by
    rw [elemWallEdgesPrefix_succ, elemWallEdgesPrefix_zero, List.nil_append, List.length_append]
    have hhoriz : (elemWallHorizEdge h 0).length = 1 := by
      unfold elemWallHorizEdge
      have hmod : (0 + 1) % (2 * h + 2) = 1 := Nat.mod_eq_of_lt (by omega)
      have hcond : (0 + 1) % (2 * h + 2) + 1 < 2 * h + 2 ∧ 0 + 1 < elemWallNumVerts h := by
        rw [hmod]
        exact ⟨by omega, by omega⟩
      rw [dif_pos hcond]
      rfl
    omega
  have hle : (elemWallEdgesPrefix h 1).length ≤ (elemWallEdges h).length := by
    rw [← elemWallEdgesPrefix_full]
    exact elemWallEdgesPrefix_length_mono h (by omega)
  omega

/-- For `1 ≤ h`, `2 * h + 2 ≤ elemWallNumVerts h`. -/
theorem two_mul_add_two_le_elemWallNumVerts {h : ℕ} (hh1 : 1 ≤ h) :
    2 * h + 2 ≤ elemWallNumVerts h := by
  rw [elemWallNumVerts_eq]
  have : 2 * h + 4 ≤ (h + 1) * (2 * h + 2) := by nlinarith
  omega

/-- Word-size bounds used throughout Section 5. -/
structure Section5WordBounds (w p r : ℕ) (x : Alg74Input p r) : Prop where
  hw3 : 3 < 2 ^ w
  hp_w : p < 2 ^ w
  hK_w : (completeGraphEdges p).length < 2 ^ w
  hn_w : x.n < 2 ^ w
  hm_w : 2 + 3 * x.G.numActivePairs < 2 ^ w
  hwall_w : elemWallNumVerts x.h + (elemWallEdges x.h).length + 1 < 2 ^ w
  hVJW_w : elemWallNumVerts x.h + (2 * x.h + 2) < 2 ^ w
  hroute_w : 2 * x.h + 2 + alg74BoxMarginConst p < 2 ^ w
  hin_w : (encAlg74In x).length < 2 ^ w
  hout_w : 2 + 2 * (completeGraphEdges p).length + p * x.n < 2 ^ w

namespace Section5WordBounds

variable {w p r : ℕ} {x : Alg74Input p r}

theorem hw0 (hw : Section5WordBounds w p r x) : 0 < 2 ^ w := by
  have := hw.hw3; omega

theorem hw1 (hw : Section5WordBounds w p r x) : 1 < 2 ^ w := by
  have := hw.hw3; omega

theorem hw2 (hw : Section5WordBounds w p r x) : 2 < 2 ^ w := by
  have := hw.hw3; omega

theorem hh_w (hw : Section5WordBounds w p r x) : x.h < 2 ^ w := by
  have := hw.hroute_w; omega

theorem hh1_w (hw : Section5WordBounds w p r x) : x.h + 1 < 2 ^ w := by
  have := hw.hroute_w; omega

theorem h2h2_w (hw : Section5WordBounds w p r x) : 2 * x.h + 2 < 2 ^ w := by
  have := hw.hroute_w; omega

theorem hloc_w (hw : Section5WordBounds w p r x) :
    elemWallNumVerts x.h + (elemWallEdges x.h).length < 2 ^ w := by
  have := hw.hwall_w; omega

end Section5WordBounds

/-- Bundled state invariant holding after `routeTerminalsCmd` and preserved throughout Section 5. -/
structure RoutingStateHolds {p r : ℕ} (hp0 : 0 < p) (x : Alg74Input p r) (s : State) : Prop where
  hin : s.arrs inArr = encAlg74In x
  hr0 : s.regs 0 = x.n
  hr2 : s.regs 2 = 2 + 3 * x.G.numActivePairs
  hr3 : s.regs 3 = x.h
  hr12 : s.regs 12 = elemWallNumVerts x.h
  hr13 : s.regs 13 = (elemWallEdges x.h).length
  hr14 : s.regs 14 = 2 * x.h + 2
  hloc_len : (s.arrs locArr).length = x.n
  hloc_val : ∀ v ∈ x.W.vertexFinset,
    (s.arrs locArr)[v.1]'(by rw [hloc_len]; exact v.2) = termLocCode x.W v
  hu1_len : (s.arrs edgeU1Arr).length = (elemWallEdges x.h).length
  hu1_val : ∀ k : Fin (elemWallEdges x.h).length,
    (s.arrs edgeU1Arr)[k.1]'(by rw [hu1_len]; exact k.2) = ((elemWallEdges x.h)[k.1]'k.2).1.1
  hu2_len : (s.arrs edgeU2Arr).length = (elemWallEdges x.h).length
  hu2_val : ∀ k : Fin (elemWallEdges x.h).length,
    (s.arrs edgeU2Arr)[k.1]'(by rw [hu2_len]; exact k.2) = ((elemWallEdges x.h)[k.1]'k.2).2.1
  hterm_edges : ∀ e : Fin (completeGraphEdges p).length,
    s.regs (20 + 2 * e.1) = (alg74TermVert x (edgeStartTerm e)).1 ∧
    s.regs (20 + 2 * e.1 + 1) = (alg74TermVert x (edgeEndTerm e)).1
  hr15 : s.regs 15 = chooseBoxMargin p x.h (alg74NumTerms p) (alg74Term x)
  hr16 : s.regs 16 =
    (perimTermInfo x.h (chooseBoxMargin p x.h (alg74NumTerms p) (alg74Term x))
      (alg74NumTerms p) (alg74Term x) (alg74RawColor p)).1
  hr17 : s.regs 17 =
    (perimTermInfo x.h (chooseBoxMargin p x.h (alg74NumTerms p) (alg74Term x))
      (alg74NumTerms p) (alg74Term x) (alg74RawColor p)).2.1
  hr18 : s.regs 18 =
    (perimTermInfo x.h (chooseBoxMargin p x.h (alg74NumTerms p) (alg74Term x))
      (alg74NumTerms p) (alg74Term x) (alg74RawColor p)).2.2.1
  hr19 : s.regs 19 =
    (perimTermInfo x.h (chooseBoxMargin p x.h (alg74NumTerms p) (alg74Term x))
      (alg74NumTerms p) (alg74Term x) (alg74RawColor p)).2.2.2
  htermC : ∀ a : Fin (alg74NumTerms p),
    s.regs (regTermC p a.1) = (alg74Term x a).1 ∧
    s.regs (regTermY p a.1) = (alg74Term x a).2
  hperm : ∀ g : Fin p,
    s.regs (regPermColor p g.1) =
      (colorPerm p x.h (chooseBoxMargin p x.h (alg74NumTerms p) (alg74Term x))
        (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p) g).1
  hslots : ∀ j : Fin (alg74NumTerms p),
    SortSlotHolds hp0 x (chooseBoxMargin p x.h (alg74NumTerms p) (alg74Term x)) s j.1
      (fullSortedGet x.h (chooseBoxMargin p x.h (alg74NumTerms p) (alg74Term x))
        (alg74NumTerms p) (alg74Term x) j)
  hsafe : ∀ j < alg74NumTerms p,
    s.regs (regSafeC p j) =
      safeCol p (fullColSeq x.h (chooseBoxMargin p x.h (alg74NumTerms p) (alg74Term x))
        (alg74NumTerms p) (alg74Term x)) j

/-- `RoutingStateHolds` is preserved whenever registers in `{0, 2, 3} ∪ {r | 12 ≤ r}` and arrays
`a ≠ outArr` are unchanged. -/
theorem RoutingStateHolds.of_preserve {p r : ℕ} {hp0 : 0 < p} {x : Alg74Input p r}
    {s s' : State} (hs : RoutingStateHolds hp0 x s)
    (hregs : ∀ reg : Reg, (reg = 0 ∨ reg = 2 ∨ reg = 3 ∨ 12 ≤ reg) → s'.regs reg = s.regs reg)
    (harrs : ∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a) :
    RoutingStateHolds hp0 x s' where
  hin := by rw [harrs inArr (by decide), hs.hin]
  hr0 := by rw [hregs 0 (Or.inl rfl), hs.hr0]
  hr2 := by rw [hregs 2 (Or.inr (Or.inl rfl)), hs.hr2]
  hr3 := by rw [hregs 3 (Or.inr (Or.inr (Or.inl rfl))), hs.hr3]
  hr12 := by rw [hregs 12 (by dsimp [Reg]; omega), hs.hr12]
  hr13 := by rw [hregs 13 (by dsimp [Reg]; omega), hs.hr13]
  hr14 := by rw [hregs 14 (by dsimp [Reg]; omega), hs.hr14]
  hloc_len := by rw [harrs locArr (by decide), hs.hloc_len]
  hloc_val := by
    intro v hv
    simp [harrs locArr (by decide), hs.hloc_val v hv]
  hu1_len := by rw [harrs edgeU1Arr (by decide), hs.hu1_len]
  hu1_val := by
    intro k
    simp [harrs edgeU1Arr (by decide), hs.hu1_val k]
  hu2_len := by rw [harrs edgeU2Arr (by decide), hs.hu2_len]
  hu2_val := by
    intro k
    simp [harrs edgeU2Arr (by decide), hs.hu2_val k]
  hterm_edges := by
    intro e
    rw [hregs (20 + 2 * e.1) (by dsimp [Reg]; omega),
      hregs (20 + 2 * e.1 + 1) (by dsimp [Reg]; omega)]
    exact hs.hterm_edges e
  hr15 := by rw [hregs 15 (by dsimp [Reg]; omega), hs.hr15]
  hr16 := by rw [hregs 16 (by dsimp [Reg]; omega), hs.hr16]
  hr17 := by rw [hregs 17 (by dsimp [Reg]; omega), hs.hr17]
  hr18 := by rw [hregs 18 (by dsimp [Reg]; omega), hs.hr18]
  hr19 := by rw [hregs 19 (by dsimp [Reg]; omega), hs.hr19]
  htermC := by
    intro a
    rw [hregs (regTermC p a.1) (by dsimp [regTermC, Reg]; omega),
      hregs (regTermY p a.1) (by dsimp [regTermY, Reg]; omega)]
    exact hs.htermC a
  hperm := by
    intro g
    rw [hregs (regPermColor p g.1) (by dsimp [regPermColor, Reg]; omega)]
    exact hs.hperm g
  hslots := by
    intro j
    refine sortSlotHolds_congr (hs.hslots j)
      (hregs _ (by dsimp [regSortKey, regSortBase, Reg]; omega))
      (hregs _ (by dsimp [regSortC, regSortBase, Reg]; omega))
      (hregs _ (by dsimp [regSortY, regSortBase, Reg]; omega))
      (hregs _ (by dsimp [regSortG, regSortBase, Reg]; omega))
  hsafe := by
    intro j hj
    rw [hregs (regSafeC p j) (by dsimp [regSafeC, regSortBase, Reg]; omega)]
    exact hs.hsafe j hj

/-! #### Sub-step 5a: Coarse Grid and Wall Branch Set Expressions -/

theorem eval_const {w : ℕ} (s : State) {c : ℕ} (hc : c < 2 ^ w) :
    (Expr.const c).eval w s = some c := by
  simp [Expr.eval, checkWord, hc]

theorem eval_op_add {w : ℕ} {s : State} {e₁ e₂ : Expr} {v₁ v₂ : ℕ}
    (h₁ : e₁.eval w s = some v₁) (h₂ : e₂.eval w s = some v₂)
    (hw : v₁ + v₂ < 2 ^ w) :
    (Expr.op .add e₁ e₂).eval w s = some (v₁ + v₂) := by
  simp [Expr.eval, h₁, h₂, BinOp.eval, BinOp.raw, checkWord, hw]

theorem eval_op_sub {w : ℕ} {s : State} {e₁ e₂ : Expr} {v₁ v₂ : ℕ}
    (h₁ : e₁.eval w s = some v₁) (h₂ : e₂.eval w s = some v₂) :
    (Expr.op .sub e₁ e₂).eval w s = some (v₁ - v₂) := by
  have hv₁ : v₁ < 2 ^ w := eval_lt_two_pow h₁
  have hsub : v₁ - v₂ < 2 ^ w := by omega
  simp [Expr.eval, h₁, h₂, BinOp.eval, BinOp.raw, checkWord, hsub]

theorem eval_op_mul {w : ℕ} {s : State} {e₁ e₂ : Expr} {v₁ v₂ : ℕ}
    (h₁ : e₁.eval w s = some v₁) (h₂ : e₂.eval w s = some v₂)
    (hw : v₁ * v₂ < 2 ^ w) :
    (Expr.op .mul e₁ e₂).eval w s = some (v₁ * v₂) := by
  simp [Expr.eval, h₁, h₂, BinOp.eval, BinOp.raw, checkWord, hw]

theorem eval_op_div {w : ℕ} {s : State} {e₁ e₂ : Expr} {v₁ v₂ : ℕ}
    (h₁ : e₁.eval w s = some v₁) (h₂ : e₂.eval w s = some v₂)
    (hv₂ : 0 < v₂) :
    (Expr.op .div e₁ e₂).eval w s = some (v₁ / v₂) := by
  have hv₁ : v₁ < 2 ^ w := eval_lt_two_pow h₁
  have hdiv : v₁ / v₂ ≤ v₁ := Nat.div_le_self v₁ v₂
  have hdiv_w : v₁ / v₂ < 2 ^ w := by omega
  have hv₂_ne : v₂ ≠ 0 := by omega
  simp [Expr.eval, h₁, h₂, BinOp.eval, BinOp.raw, checkWord, hv₂_ne, hdiv_w]

theorem eval_op_mod {w : ℕ} {s : State} {e₁ e₂ : Expr} {v₁ v₂ : ℕ}
    (h₁ : e₁.eval w s = some v₁) (h₂ : e₂.eval w s = some v₂)
    (hv₂ : 0 < v₂) :
    (Expr.op .mod e₁ e₂).eval w s = some (v₁ % v₂) := by
  have hv₂_w : v₂ < 2 ^ w := eval_lt_two_pow h₂
  have hmod : v₁ % v₂ < v₂ := Nat.mod_lt v₁ hv₂
  have hmod_w : v₁ % v₂ < 2 ^ w := by omega
  have hv₂_ne : v₂ ≠ 0 := by omega
  simp [Expr.eval, h₁, h₂, BinOp.eval, BinOp.raw, checkWord, hv₂_ne, hmod_w]

/-- Conditional value expression `e_cond * e_t + (1 - e_cond) * e_f` for `0`/`1`-valued `e_cond`. -/
def exprIte (e_cond e_t e_f : Expr) : Expr :=
  .op .add (.op .mul e_cond e_t) (.op .mul (exprNot e_cond) e_f)

theorem eval_exprIte {w : ℕ} {s : State} {e_cond e_t e_f : Expr}
    {P : Prop} [Decidable P] {vt vf : ℕ}
    (hw1 : 1 < 2 ^ w)
    (hcond : e_cond.eval w s = some (if P then 1 else 0))
    (ht : e_t.eval w s = some vt)
    (hf : e_f.eval w s = some vf) :
    (exprIte e_cond e_t e_f).eval w s = some (if P then vt else vf) := by
  have hw0 : 0 < 2 ^ w := by omega
  have hvt_w : vt < 2 ^ w := eval_lt_two_pow ht
  have hvf_w : vf < 2 ^ w := eval_lt_two_pow hf
  have hnot := eval_exprNot hw1 hcond
  unfold exprIte
  by_cases hP : P
  · rw [if_pos hP] at hcond ⊢
    simp [hP] at hnot
    have hm1 := eval_op_mul hcond ht (by omega)
    have hm2 := eval_op_mul hnot hf (by omega)
    simpa using eval_op_add hm1 hm2 (by omega)
  · rw [if_neg hP] at hcond ⊢
    simp [hP] at hnot
    have hm1 := eval_op_mul hcond ht (by omega)
    have hm2 := eval_op_mul hnot hf (by omega)
    simpa using eval_op_add hm1 hm2 (by omega)

private theorem eval_exprOr_inst {w : ℕ} {s : State} {e₁ e₂ : Expr} {P₁ P₂ : Prop}
    {inst₁ : Decidable P₁} {inst₂ : Decidable P₂}
    (hw2 : 2 < 2 ^ w)
    (h₁ : e₁.eval w s = some (@ite _ P₁ inst₁ 1 0))
    (h₂ : e₂.eval w s = some (@ite _ P₂ inst₂ 1 0)) :
    (exprOr e₁ e₂).eval w s = some (@ite _ (P₁ ∨ P₂) (@instDecidableOr P₁ P₂ inst₁ inst₂) 1 0) :=
  @eval_exprOr w s e₁ e₂ P₁ P₂ inst₁ inst₂ hw2 h₁ h₂

private theorem eval_exprAnd_inst {w : ℕ} {s : State} {e₁ e₂ : Expr} {P₁ P₂ : Prop}
    {inst₁ : Decidable P₁} {inst₂ : Decidable P₂}
    (hw1 : 1 < 2 ^ w)
    (h₁ : e₁.eval w s = some (@ite _ P₁ inst₁ 1 0))
    (h₂ : e₂.eval w s = some (@ite _ P₂ inst₂ 1 0)) :
    (exprAnd e₁ e₂).eval w s = some (@ite _ (P₁ ∧ P₂) (@instDecidableAnd P₁ P₂ inst₁ inst₂) 1 0) :=
  @eval_exprAnd w s e₁ e₂ P₁ P₂ inst₁ inst₂ hw1 h₁ h₂

private theorem ite_congr_prop {c₁ c₂ : Prop} {inst₁ : Decidable c₁} {inst₂ : Decidable c₂}
    (h : c₁ ↔ c₂) :
    @ite _ c₁ inst₁ 1 0 = @ite _ c₂ inst₂ 1 0 := by
  by_cases hc₁ : c₁
  · have hc₂ : c₂ := h.mp hc₁
    simp [hc₁, hc₂]
  · have hc₂ : ¬ c₂ := fun h2 => hc₁ (h.mpr h2)
    simp [hc₁, hc₂]

private theorem eval_eq_of_iff {w : ℕ} {s : State} {e : Expr} {P Q : Prop}
    {instP : Decidable P} {instQ : Decidable Q}
    (he : e.eval w s = some (@ite _ P instP 1 0))
    (hiff : P ↔ Q) :
    e.eval w s = some (@ite _ Q instQ 1 0) := by
  rw [he, ite_congr_prop hiff]

/-- Expression testing `(c, y) ∈ hSeg y0 x1 x2`. -/
def inHSegExpr (e_y0 e_x1 e_x2 e_c e_y : Expr) : Expr :=
  exprAnd (exprEq e_y e_y0)
    (exprOr
      (exprAnd (exprLe e_x1 e_c) (exprLe e_c e_x2))
      (exprAnd (exprLe e_x2 e_c) (exprLe e_c e_x1)))

theorem eval_inHSegExpr {w : ℕ} {s : State} {e_y0 e_x1 e_x2 e_c e_y : Expr}
    {vy0 vx1 vx2 vc vy : ℕ}
    (hw2 : 2 < 2 ^ w)
    (hy0 : e_y0.eval w s = some vy0)
    (hx1 : e_x1.eval w s = some vx1)
    (hx2 : e_x2.eval w s = some vx2)
    (hc : e_c.eval w s = some vc)
    (hy : e_y.eval w s = some vy) :
    (inHSegExpr e_y0 e_x1 e_x2 e_c e_y).eval w s =
      some (if (vc, vy) ∈ hSeg vy0 vx1 vx2 then 1 else 0) := by
  have hw1 : 1 < 2 ^ w := by omega
  unfold inHSegExpr
  rw [eval_exprAnd hw1 (eval_exprEq hw1 hy hy0)
    (eval_exprOr hw2
      (eval_exprAnd hw1 (eval_exprLe hw1 hx1 hc) (eval_exprLe hw1 hc hx2))
      (eval_exprAnd hw1 (eval_exprLe hw1 hx2 hc) (eval_exprLe hw1 hc hx1)))]
  congr 1
  apply if_congr _ rfl rfl
  rw [mem_hSeg]
  dsimp only
  omega

/-- Expression testing `(c, y) ∈ vSeg x0 y1 y2`. -/
def inVSegExpr (e_x0 e_y1 e_y2 e_c e_y : Expr) : Expr :=
  exprAnd (exprEq e_c e_x0)
    (exprOr
      (exprAnd (exprLe e_y1 e_y) (exprLe e_y e_y2))
      (exprAnd (exprLe e_y2 e_y) (exprLe e_y e_y1)))

theorem eval_inVSegExpr {w : ℕ} {s : State} {e_x0 e_y1 e_y2 e_c e_y : Expr}
    {vx0 vy1 vy2 vc vy : ℕ}
    (hw2 : 2 < 2 ^ w)
    (hx0 : e_x0.eval w s = some vx0)
    (hy1 : e_y1.eval w s = some vy1)
    (hy2 : e_y2.eval w s = some vy2)
    (hc : e_c.eval w s = some vc)
    (hy : e_y.eval w s = some vy) :
    (inVSegExpr e_x0 e_y1 e_y2 e_c e_y).eval w s =
      some (if (vc, vy) ∈ vSeg vx0 vy1 vy2 then 1 else 0) := by
  have hw1 : 1 < 2 ^ w := by omega
  unfold inVSegExpr
  rw [eval_exprAnd hw1 (eval_exprEq hw1 hc hx0)
    (eval_exprOr hw2
      (eval_exprAnd hw1 (eval_exprLe hw1 hy1 hy) (eval_exprLe hw1 hy hy2))
      (eval_exprAnd hw1 (eval_exprLe hw1 hy2 hy) (eval_exprLe hw1 hy hy1)))]
  congr 1
  apply if_congr _ rfl rfl
  rw [mem_vSeg]
  dsimp only
  omega

/-- Expression testing `(c, y) ∈ perimPath h B cp yp`. -/
def inPerimPathExpr (e_h e_B e_cp e_yp e_c e_y : Expr) : Expr :=
  let h_sub_B := Expr.op .sub e_h e_B
  let h_sub_1 := Expr.op .sub e_h (.const 1)
  let c1 := exprLt h_sub_B e_yp
  let b1 :=
    exprOr (inVSegExpr e_cp e_yp h_sub_1 e_c e_y)
      (exprOr (inHSegExpr h_sub_1 e_B e_cp e_c e_y)
        (inVSegExpr e_B h_sub_B h_sub_1 e_c e_y))
  let c2 := exprLt e_yp e_B
  let b2 :=
    exprOr (inVSegExpr e_cp (.const 1) e_yp e_c e_y)
      (exprOr (inHSegExpr (.const 1) (.const 1) e_cp e_c e_y)
        (exprOr (inVSegExpr (.const 1) (.const 1) h_sub_1 e_c e_y)
          (exprOr (inHSegExpr h_sub_1 (.const 1) e_B e_c e_y)
            (inVSegExpr e_B h_sub_B h_sub_1 e_c e_y))))
  let c3 := exprLt e_cp e_B
  let b3 :=
    exprOr (inHSegExpr e_yp (.const 1) e_cp e_c e_y)
      (exprOr (inVSegExpr (.const 1) e_yp h_sub_1 e_c e_y)
        (exprOr (inHSegExpr h_sub_1 (.const 1) e_B e_c e_y)
          (inVSegExpr e_B h_sub_B h_sub_1 e_c e_y)))
  let b4 :=
    exprOr (inHSegExpr e_yp e_cp e_h e_c e_y)
      (exprOr (inVSegExpr e_h e_yp h_sub_1 e_c e_y)
        (exprOr (inHSegExpr h_sub_1 e_B e_h e_c e_y)
          (inVSegExpr e_B h_sub_B h_sub_1 e_c e_y)))
  exprIte c1 b1 (exprIte c2 b2 (exprIte c3 b3 b4))

theorem eval_inPerimPathExpr {w : ℕ} {s : State} {e_h e_B e_cp e_yp e_c e_y : Expr}
    {vh vB vcp vyp vc vy : ℕ}
    (hw2 : 2 < 2 ^ w)
    (hh : e_h.eval w s = some vh)
    (hB : e_B.eval w s = some vB)
    (hcp : e_cp.eval w s = some vcp)
    (hyp : e_yp.eval w s = some vyp)
    (hc : e_c.eval w s = some vc)
    (hy : e_y.eval w s = some vy) :
    (inPerimPathExpr e_h e_B e_cp e_yp e_c e_y).eval w s =
      some (if (vc, vy) ∈ perimPath vh vB vcp vyp then 1 else 0) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hc1 := eval_const s hw1
  have hhB := eval_op_sub hh hB
  have hh1 := eval_op_sub hh hc1
  have hb1 :=
    eval_exprOr hw2 (eval_inVSegExpr hw2 hcp hyp hh1 hc hy)
      (eval_exprOr hw2 (eval_inHSegExpr hw2 hh1 hB hcp hc hy)
        (eval_inVSegExpr hw2 hB hhB hh1 hc hy))
  have hb2 :=
    eval_exprOr hw2 (eval_inVSegExpr hw2 hcp hc1 hyp hc hy)
      (eval_exprOr hw2 (eval_inHSegExpr hw2 hc1 hc1 hcp hc hy)
        (eval_exprOr hw2 (eval_inVSegExpr hw2 hc1 hc1 hh1 hc hy)
          (eval_exprOr hw2 (eval_inHSegExpr hw2 hh1 hc1 hB hc hy)
            (eval_inVSegExpr hw2 hB hhB hh1 hc hy))))
  have hb3 :=
    eval_exprOr hw2 (eval_inHSegExpr hw2 hyp hc1 hcp hc hy)
      (eval_exprOr hw2 (eval_inVSegExpr hw2 hc1 hyp hh1 hc hy)
        (eval_exprOr hw2 (eval_inHSegExpr hw2 hh1 hc1 hB hc hy)
          (eval_inVSegExpr hw2 hB hhB hh1 hc hy)))
  have hb4 :=
    eval_exprOr hw2 (eval_inHSegExpr hw2 hyp hcp hh hc hy)
      (eval_exprOr hw2 (eval_inVSegExpr hw2 hh hyp hh1 hc hy)
        (eval_exprOr hw2 (eval_inHSegExpr hw2 hh1 hB hh hc hy)
          (eval_inVSegExpr hw2 hB hhB hh1 hc hy)))
  unfold inPerimPathExpr
  rw [eval_exprIte hw1 (eval_exprLt hw1 hhB hyp) hb1
    (eval_exprIte hw1 (eval_exprLt hw1 hyp hB) hb2
      (eval_exprIte hw1 (eval_exprLt hw1 hcp hB) hb3 hb4))]
  congr 1
  unfold perimPath
  by_cases h1 : vh - vB < vyp
  · simp only [h1, ↓reduceIte]
    exact ite_congr_prop (by simp only [Finset.mem_union, or_assoc])
  · simp only [h1, ↓reduceIte]
    by_cases h2 : vyp < vB
    · simp only [h2, ↓reduceIte]
      exact ite_congr_prop (by simp only [Finset.mem_union, or_assoc])
    · simp only [h2, ↓reduceIte]
      by_cases h3 : vcp < vB
      · simp only [h3, ↓reduceIte]
        exact ite_congr_prop (by simp only [Finset.mem_union, or_assoc])
      · simp only [h3, ↓reduceIte]
        exact ite_congr_prop (by simp only [Finset.mem_union, or_assoc])

/-- Expression testing `IsPuncturedBy g cStar c`. -/
def isPuncturedByExpr (e_g e_cStar e_c : Expr) : Expr :=
  exprAnd
    (exprLe (.op .add e_cStar (.const 1)) (.op .add e_c e_g))
    (exprLe (.op .add e_c (.const 1)) (.op .add e_cStar e_g))

theorem eval_isPuncturedByExpr {w : ℕ} {s : State} {e_g e_cStar e_c : Expr}
    {vg vcStar vc : ℕ}
    (hw1 : 1 < 2 ^ w)
    (hw_cs : vcStar + vg + 1 < 2 ^ w)
    (hw_c : vc + vg + 1 < 2 ^ w)
    (hg : e_g.eval w s = some vg)
    (hcs : e_cStar.eval w s = some vcStar)
    (hc : e_c.eval w s = some vc) :
    (isPuncturedByExpr e_g e_cStar e_c).eval w s =
      some (if IsPuncturedBy vg vcStar vc then 1 else 0) := by
  have hc1 := eval_const s hw1
  have h1 := eval_op_add hcs hc1 (by omega)
  have h2 := eval_op_add hc hg (by omega)
  have h3 := eval_op_add hc hc1 (by omega)
  have h4 := eval_op_add hcs hg (by omega)
  unfold isPuncturedByExpr IsPuncturedBy
  exact eval_exprAnd hw1 (eval_exprLe hw1 h1 h2) (eval_exprLe hw1 h3 h4)

/-- Expression testing `(c, y) ∈ connPath y_top ci cStar yi g`. -/
def inConnPathExpr (e_ytop e_ci e_cStar e_yi e_g e_c e_y : Expr) : Expr :=
  exprOr
    (inHSegExpr e_yi e_ci e_cStar e_c e_y)
    (inVSegExpr e_cStar e_yi (.op .sub e_ytop e_g) e_c e_y)

theorem eval_inConnPathExpr {w : ℕ} {s : State}
    {e_ytop e_ci e_cStar e_yi e_g e_c e_y : Expr}
    {vytop vci vcStar vyi vg vc vy : ℕ}
    (hw2 : 2 < 2 ^ w)
    (hytop : e_ytop.eval w s = some vytop)
    (hci : e_ci.eval w s = some vci)
    (hcs : e_cStar.eval w s = some vcStar)
    (hyi : e_yi.eval w s = some vyi)
    (hg : e_g.eval w s = some vg)
    (hc : e_c.eval w s = some vc)
    (hy : e_y.eval w s = some vy) :
    (inConnPathExpr e_ytop e_ci e_cStar e_yi e_g e_c e_y).eval w s =
      some (if (vc, vy) ∈ connPath vytop vci vcStar vyi vg then 1 else 0) := by
  have hsub := eval_op_sub hytop hg
  unfold inConnPathExpr
  rw [eval_exprOr hw2 (eval_inHSegExpr hw2 hyi hci hcs hc hy)
    (eval_inVSegExpr hw2 hcs hyi hsub hc hy)]
  congr 1
  exact if_congr mem_connPath.symm rfl rfl

/-- Expression testing `(c, y) ∈ detourPath y_top ci cStar yi g`. -/
def inDetourPathExpr (e_ytop e_ci e_cStar e_yi e_g e_c e_y : Expr) : Expr :=
  let y_top_sub_g := Expr.op .sub e_ytop e_g
  let cStar_sub_g := Expr.op .sub e_cStar e_g
  let cStar_add_g := Expr.op .add e_cStar e_g
  let ci_sub_g := Expr.op .sub e_ci e_g
  let yi_sub_g := Expr.op .sub e_yi e_g
  let yi_add_g := Expr.op .add e_yi e_g
  exprOr (inVSegExpr cStar_sub_g yi_add_g y_top_sub_g e_c e_y)
    (exprOr (inHSegExpr yi_add_g ci_sub_g cStar_sub_g e_c e_y)
      (exprOr (inVSegExpr ci_sub_g yi_sub_g yi_add_g e_c e_y)
        (exprOr (inHSegExpr yi_sub_g ci_sub_g cStar_add_g e_c e_y)
          (inVSegExpr cStar_add_g yi_sub_g y_top_sub_g e_c e_y))))

theorem eval_inDetourPathExpr {w : ℕ} {s : State}
    {e_ytop e_ci e_cStar e_yi e_g e_c e_y : Expr}
    {vytop vci vcStar vyi vg vc vy : ℕ}
    (hw2 : 2 < 2 ^ w)
    (hw_cs : vcStar + vg < 2 ^ w)
    (hw_yi : vyi + vg < 2 ^ w)
    (hytop : e_ytop.eval w s = some vytop)
    (hci : e_ci.eval w s = some vci)
    (hcs : e_cStar.eval w s = some vcStar)
    (hyi : e_yi.eval w s = some vyi)
    (hg : e_g.eval w s = some vg)
    (hc : e_c.eval w s = some vc)
    (hy : e_y.eval w s = some vy) :
    (inDetourPathExpr e_ytop e_ci e_cStar e_yi e_g e_c e_y).eval w s =
      some (if (vc, vy) ∈ detourPath vytop vci vcStar vyi vg then 1 else 0) := by
  have hytop_sub := eval_op_sub hytop hg
  have hcs_sub := eval_op_sub hcs hg
  have hcs_add := eval_op_add hcs hg hw_cs
  have hci_sub := eval_op_sub hci hg
  have hyi_sub := eval_op_sub hyi hg
  have hyi_add := eval_op_add hyi hg hw_yi
  unfold inDetourPathExpr
  rw [eval_exprOr hw2 (eval_inVSegExpr hw2 hcs_sub hyi_add hytop_sub hc hy)
    (eval_exprOr hw2 (eval_inHSegExpr hw2 hyi_add hci_sub hcs_sub hc hy)
      (eval_exprOr hw2 (eval_inVSegExpr hw2 hci_sub hyi_sub hyi_add hc hy)
        (eval_exprOr hw2 (eval_inHSegExpr hw2 hyi_sub hci_sub hcs_add hc hy)
          (eval_inVSegExpr hw2 hcs_add hyi_sub hytop_sub hc hy))))]
  congr 1
  apply if_congr _ rfl rfl
  unfold detourPath
  simp only [Finset.mem_union, or_assoc]

/-- Expression testing `(c, y) ∈ interiorBranchSet` using the sorted terminal table in registers. -/
def inInteriorBranchSetExpr (p : ℕ) (e_g e_c e_y : Expr) : Expr :=
  let m := alg74NumTerms p
  let h_sub_B := Expr.op .sub (.reg 3) (.reg 15)
  let y_tr := Expr.op .sub h_sub_B e_g
  let in_trunk :=
    exprAnd
      (inHSegExpr y_tr (.reg 15) h_sub_B e_c e_y)
      (exprAll (List.finRange m) (fun i =>
        exprImp
          (exprAnd
            (exprLt (.const 0) (.reg (regSortKey p i.1)))
            (exprLt (.reg (regSortG p i.1)) e_g))
          (exprNot (isPuncturedByExpr e_g (.reg (regSafeC p i.1)) e_c))))
  let in_conn :=
    exprAny (List.finRange m) (fun i =>
      exprAnd
        (exprAnd
          (exprLt (.const 0) (.reg (regSortKey p i.1)))
          (exprEq (.reg (regSortG p i.1)) e_g))
        (inConnPathExpr h_sub_B (.reg (regSortC p i.1)) (.reg (regSafeC p i.1))
          (.reg (regSortY p i.1)) e_g e_c e_y))
  let in_detour :=
    exprAny (List.finRange m) (fun i =>
      exprAnd
        (exprAnd
          (exprLt (.const 0) (.reg (regSortKey p i.1)))
          (exprLt (.reg (regSortG p i.1)) e_g))
        (inDetourPathExpr h_sub_B (.reg (regSortC p i.1)) (.reg (regSafeC p i.1))
          (.reg (regSortY p i.1)) e_g e_c e_y))
  exprOr in_trunk (exprOr in_conn in_detour)

theorem eval_inInteriorBranchSetExpr {w p r : ℕ} (hp0 : 0 < p) (x : Alg74Input p r)
    (hh1 : 1 ≤ x.h)
    (hw : Section5WordBounds w p r x)
    {s : State} (hs : RoutingStateHolds hp0 x s)
    (gamma : Fin p) {e_g e_c e_y : Expr} {vc vy : ℕ}
    (hvc_le : vc ≤ 2 * x.h + 1)
    (hg : e_g.eval w s =
      some (colorPerm p x.h (chooseBoxMargin p x.h (alg74NumTerms p) (alg74Term x))
        (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p) gamma).1)
    (hc : e_c.eval w s = some vc)
    (hy : e_y.eval w s = some vy) :
    let B := chooseBoxMargin p x.h (alg74NumTerms p) (alg74Term x)
    let L := sortedIntList x.h B (alg74NumTerms p) (alg74Term x)
    let perm := colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p)
    (inInteriorBranchSetExpr p e_g e_c e_y).eval w s =
      some (if (vc, vy) ∈ interiorBranchSet p x.h B L.length
        (fun i => alg74Term x (L.get i))
        (fun i => perm (alg74RawColor p (L.get i)))
        (perm gamma) then 1 else 0) := by
  intro B L perm
  let m := alg74NumTerms p
  let g := (perm gamma).1
  have hg_lt : g < p := (perm gamma).2
  have hw0 := hw.hw0
  have hw1 := hw.hw1
  have hw2 := hw.hw2
  have hw_h := hw.hh_w
  have hw_h1 := hw.hh1_w
  have hw_p := hw.hp_w
  have hB_le : B ≤ alg74BoxMarginConst p := by
    dsimp [B]
    rw [chooseBoxMargin_eq_ite]
    split_ifs <;> [ (unfold alg74BoxMarginConst; omega); exact le_rfl ]
  have hw_B : B < 2 ^ w := by have := hw.hroute_w; omega
  have hr3_ev : (Expr.reg 3).eval w s = some x.h := eval_reg hs.hr3 hw_h
  have hr15_ev : (Expr.reg 15).eval w s = some B := eval_reg hs.hr15 hw_B
  have hhB_ev := eval_op_sub hr3_ev hr15_ev
  have hytr_ev := eval_op_sub hhB_ev hg
  have hc0_ev := eval_const s hw0
  let a_i := fun i : Fin m => fullSortedGet x.h B m (alg74Term x) i
  let cSeq := fullColSeq x.h B m (alg74Term x)
  have hslot_eval : ∀ i : Fin m,
      let a := a_i i
      (Expr.reg (regSortKey p i.1)).eval w s = some (termSortKey x.h B (alg74Term x a)) ∧
      (Expr.reg (regSortC p i.1)).eval w s = some (alg74Term x a).1 ∧
      (Expr.reg (regSortY p i.1)).eval w s = some (alg74Term x a).2 ∧
      (Expr.reg (regSortG p i.1)).eval w s = some (perm (alg74RawColor p a)).1 ∧
      (Expr.reg (regSafeC p i.1)).eval w s = some (safeCol p cSeq i.1) ∧
      safeCol p cSeq i.1 + g + 1 < 2 ^ w ∧
      (alg74Term x a).2 + g < 2 ^ w := by
    intro i a
    have hslot := hs.hslots i
    have hkey_le := termSortKey_le x hh1 B a
    have hb_a := alg74Term_bounds x hh1 a
    have hcol_lt := (perm (alg74RawColor p a)).2
    have hsafe_eq := hs.hsafe i.1 i.2
    have hcSeq_le : cSeq i.1 ≤ x.h := by
      dsimp [cSeq, fullColSeq]
      simp only [i.2]
      exact hb_a.2.1
    have hsafe_hi := (safeCol_bounds p cSeq i.1).2
    have hmul : i.1 * (4 * p + 2) ≤ m * (4 * p + 2) :=
      Nat.mul_le_mul_right _ (le_of_lt i.2)
    have hsafe_g_w : safeCol p cSeq i.1 + g + 1 < 2 ^ w := by
      have hbr := hw.hroute_w
      unfold alg74BoxMarginConst at hbr
      dsimp [m] at hmul ⊢
      omega
    have hy_g_w : (alg74Term x a).2 + g < 2 ^ w := by
      have hbr := hw.hroute_w
      unfold alg74BoxMarginConst at hbr
      omega
    refine ⟨eval_reg hslot.1 (by omega),
      eval_reg hslot.2.1 (by omega),
      eval_reg hslot.2.2.1 (by omega),
      eval_reg hslot.2.2.2 (by omega),
      eval_reg hsafe_eq (by omega),
      hsafe_g_w, hy_g_w⟩
  have hvc_g_w : vc + g + 1 < 2 ^ w := by
    have hbr := hw.hroute_w
    unfold alg74BoxMarginConst at hbr
    omega
  have htrunk_all :=
    eval_exprAll (List.finRange m)
      (fun i =>
        exprImp
          (exprAnd
            (exprLt (.const 0) (.reg (regSortKey p i.1)))
            (exprLt (.reg (regSortG p i.1)) e_g))
          (exprNot (isPuncturedByExpr e_g (.reg (regSafeC p i.1)) e_c)))
      (fun i => 0 < termSortKey x.h B (alg74Term x (a_i i)) ∧
        (perm (alg74RawColor p (a_i i))).1 < g →
        ¬ IsPuncturedBy g (safeCol p cSeq i.1) vc) hw1
      (fun i _ => by
        rcases hslot_eval i with ⟨hkey_e, _, _, hg_e, hsafe_e, hsafe_w, _⟩
        exact eval_exprImp hw2
          (eval_exprAnd hw1 (eval_exprLt hw1 hc0_ev hkey_e) (eval_exprLt hw1 hg_e hg))
          (eval_exprNot hw1 (eval_isPuncturedByExpr hw1 hsafe_w hvc_g_w hg hsafe_e hc)))
  have hconn_any :=
    eval_exprAny (List.finRange m)
      (fun i =>
        exprAnd
          (exprAnd
            (exprLt (.const 0) (.reg (regSortKey p i.1)))
            (exprEq (.reg (regSortG p i.1)) e_g))
          (inConnPathExpr (.op .sub (.reg 3) (.reg 15)) (.reg (regSortC p i.1))
            (.reg (regSafeC p i.1)) (.reg (regSortY p i.1)) e_g e_c e_y))
      (fun i => (0 < termSortKey x.h B (alg74Term x (a_i i)) ∧
          (perm (alg74RawColor p (a_i i))).1 = g) ∧
        (vc, vy) ∈ connPath (x.h - B) (alg74Term x (a_i i)).1
          (safeCol p cSeq i.1) (alg74Term x (a_i i)).2 g) hw2
      (fun i _ => by
        rcases hslot_eval i with ⟨hkey_e, hc_e, hy_e, hg_e, hsafe_e, _, _⟩
        exact eval_exprAnd hw1
          (eval_exprAnd hw1 (eval_exprLt hw1 hc0_ev hkey_e) (eval_exprEq hw1 hg_e hg))
          (eval_inConnPathExpr hw2 hhB_ev hc_e hsafe_e hy_e hg hc hy))
  have hdet_any :=
    eval_exprAny (List.finRange m)
      (fun i =>
        exprAnd
          (exprAnd
            (exprLt (.const 0) (.reg (regSortKey p i.1)))
            (exprLt (.reg (regSortG p i.1)) e_g))
          (inDetourPathExpr (.op .sub (.reg 3) (.reg 15)) (.reg (regSortC p i.1))
            (.reg (regSafeC p i.1)) (.reg (regSortY p i.1)) e_g e_c e_y))
      (fun i => (0 < termSortKey x.h B (alg74Term x (a_i i)) ∧
          (perm (alg74RawColor p (a_i i))).1 < g) ∧
        (vc, vy) ∈ detourPath (x.h - B) (alg74Term x (a_i i)).1
          (safeCol p cSeq i.1) (alg74Term x (a_i i)).2 g) hw2
      (fun i _ => by
        rcases hslot_eval i with ⟨hkey_e, hc_e, hy_e, hg_e, hsafe_e, hsafe_w, hy_w⟩
        exact eval_exprAnd hw1
          (eval_exprAnd hw1 (eval_exprLt hw1 hc0_ev hkey_e) (eval_exprLt hw1 hg_e hg))
          (eval_inDetourPathExpr hw2 (by omega) hy_w hhB_ev hc_e hsafe_e hy_e hg hc hy))
  unfold inInteriorBranchSetExpr
  exact eval_eq_of_iff
    (eval_exprOr_inst hw2
      (eval_exprAnd_inst hw1 (eval_inHSegExpr hw2 hytr_ev hr15_ev hhB_ev hc hy) htrunk_all)
      (eval_exprOr_inst hw2 hconn_any hdet_any))
    (mem_interiorBranchSet_iff_fullSortedGet x.h B m hp0 (alg74Term x)
      (alg74RawColor p) gamma (vc, vy)).symm

attribute [local irreducible] interiorBranchSet

/-- Expression testing `(c, y) ∈ alg74CoarseBranchSet hp x gamma`. -/
def inRoutedBranchSetExpr (p : ℕ) (gamma : Fin p) (e_c e_y : Expr) : Expr :=
  let e_g := Expr.reg (regPermColor p gamma.1)
  exprOr
    (exprAnd (exprEq (.reg 16) (.const 1))
      (exprAnd (exprEq e_g (.const 0))
        (inPerimPathExpr (.reg 3) (.reg 15) (.reg 17) (.reg 18) e_c e_y)))
    (inInteriorBranchSetExpr p e_g e_c e_y)

theorem eval_inRoutedBranchSetExpr {w p r : ℕ} (hp : 2 ≤ p) (x : Alg74Input p r)
    (hh1 : 1 ≤ x.h)
    (hw : Section5WordBounds w p r x)
    {s : State} (hs : RoutingStateHolds (by omega : 0 < p) x s)
    (gamma : Fin p) {e_c e_y : Expr} {vc vy : ℕ}
    (hvc_le : vc ≤ 2 * x.h + 1)
    (hc : e_c.eval w s = some vc)
    (hy : e_y.eval w s = some vy) :
    (inRoutedBranchSetExpr p gamma e_c e_y).eval w s =
      some (if (vc, vy) ∈ alg74CoarseBranchSet hp x gamma then 1 else 0) := by
  have hp0 : 0 < p := by omega
  let B := chooseBoxMargin p x.h (alg74NumTerms p) (alg74Term x)
  let perm := colorPerm p x.h B (alg74NumTerms p) hp0 (alg74Term x) (alg74RawColor p)
  let pinfo := perimTermInfo x.h B (alg74NumTerms p) (alg74Term x) (alg74RawColor p)
  have hw0 := hw.hw0
  have hw1 := hw.hw1
  have hw2 := hw.hw2
  have hw_h := hw.hh_w
  have hB_le : B ≤ alg74BoxMarginConst p := by
    dsimp [B]
    rw [chooseBoxMargin_eq_ite]
    split_ifs <;> [ (unfold alg74BoxMarginConst; omega); exact le_rfl ]
  have hw_B : B < 2 ^ w := by have := hw.hroute_w; omega
  have hpinfo_b := perimTermInfo_bounds hp0 x hh1 B
  have hg_w : (perm gamma).1 < 2 ^ w := by
    have := (perm gamma).2; have := hw.hp_w; omega
  have hg_ev : (Expr.reg (regPermColor p gamma.1)).eval w s = some (perm gamma).1 :=
    eval_reg (hs.hperm gamma) hg_w
  have hr3_ev : (Expr.reg 3).eval w s = some x.h := eval_reg hs.hr3 hw_h
  have hr15_ev : (Expr.reg 15).eval w s = some B := eval_reg hs.hr15 hw_B
  have hr16_ev : (Expr.reg 16).eval w s = some pinfo.1 :=
    eval_reg hs.hr16 (by dsimp [pinfo] at *; have := hpinfo_b.1; omega)
  have hr17_ev : (Expr.reg 17).eval w s = some pinfo.2.1 :=
    eval_reg hs.hr17 (by dsimp [pinfo] at *; have := hpinfo_b.2.1; omega)
  have hr18_ev : (Expr.reg 18).eval w s = some pinfo.2.2.1 :=
    eval_reg hs.hr18 (by dsimp [pinfo] at *; have := hpinfo_b.2.2.1; omega)
  have hc0_ev := eval_const s hw0
  have hc1_ev := eval_const s hw1
  unfold inRoutedBranchSetExpr
  refine eval_eq_of_iff
    (eval_exprOr_inst hw2
      (eval_exprAnd_inst hw1 (eval_exprEq hw1 hr16_ev hc1_ev)
        (eval_exprAnd_inst hw1 (eval_exprEq hw1 hg_ev hc0_ev)
          (eval_inPerimPathExpr hw2 hr3_ev hr15_ev hr17_ev hr18_ev hc hy)))
      (eval_inInteriorBranchSetExpr hp0 x hh1 hw hs gamma hvc_le hg_ev hc hy)) ?_
  unfold alg74CoarseBranchSet
  exact (mem_routedBranchSet_iff_perimTermInfo x.h B (alg74NumTerms p) hp0
    (alg74Term x) (alg74RawColor p) gamma (vc, vy)).symm

attribute [local irreducible] routedBranchSet alg74CoarseBranchSet

/-- Expression testing `(qx, qy) ∈ liftGrid (alg74CoarseBranchSet hp x gamma)`. -/
def inLiftGridCoarseBranchSetExpr (p : ℕ) (gamma : Fin p) (e_qx e_qy : Expr) : Expr :=
  exprAnd (exprLe (.const 1) e_qx)
    (exprAnd (exprLe e_qx (.op .mul (.const 2) (.reg 3)))
      (inRoutedBranchSetExpr p gamma (.op .div (.op .add e_qx (.const 1)) (.const 2)) e_qy))

theorem eval_inLiftGridCoarseBranchSetExpr {w p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p))
    (hh1 : 1 ≤ x.h)
    (hw : Section5WordBounds w p (alg74LiftRadius p) x)
    {s : State} (hs : RoutingStateHolds (by omega : 0 < p) x s)
    (gamma : Fin p) {e_qx e_qy : Expr} {vqx vqy : ℕ}
    (hvqx_le : vqx ≤ 2 * x.h + 1)
    (hqx : e_qx.eval w s = some vqx)
    (hqy : e_qy.eval w s = some vqy) :
    (inLiftGridCoarseBranchSetExpr p gamma e_qx e_qy).eval w s =
      some (if (vqx, vqy) ∈ liftGrid (alg74CoarseBranchSet hp x gamma) then 1 else 0) := by
  have hw1 := hw.hw1
  have hw2 := hw.hw2
  have hw_h := hw.hh_w
  have hw_2h2 := hw.h2h2_w
  have hc1_ev := eval_const s hw1
  have hc2_ev := eval_const s hw2
  have hr3_ev : (Expr.reg 3).eval w s = some x.h := eval_reg hs.hr3 hw_h
  have h2h_ev := eval_op_mul hc2_ev hr3_ev (by omega)
  have hdiv_ev := eval_op_div (eval_op_add hqx hc1_ev (by omega)) hc2_ev (by omega)
  have hdiv_le : (vqx + 1) / 2 ≤ 2 * x.h + 1 := by omega
  unfold inLiftGridCoarseBranchSetExpr
  have hspec := alg74CoarseBranchSet_spec hp x
  exact eval_eq_of_iff
    (eval_exprAnd_inst hw1 (eval_exprLe hw1 hc1_ev hqx)
      (eval_exprAnd_inst hw1 (eval_exprLe hw1 hqx h2h_ev)
        (eval_inRoutedBranchSetExpr hp x hh1 hw hs gamma hdiv_le hdiv_ev hqy)))
    (mem_liftGrid_iff_div_two
      (fun p' hp' => ⟨(hspec.1 gamma hp').1, (hspec.1 gamma hp').2.1⟩) (vqx, vqy)).symm

attribute [local irreducible] liftGrid

/-- Expression computing `(coordOf x.h u).1 = (u + 1) % (2 * x.h + 2)` from `e_u` and `r_14`. -/
def uCoordXExpr (e_u : Expr) : Expr :=
  .op .mod (.op .add e_u (.const 1)) (.reg 14)

/-- Expression computing `(coordOf x.h u).2 = (u + 1) / (2 * x.h + 2)` from `e_u` and `r_14`. -/
def uCoordYExpr (e_u : Expr) : Expr :=
  .op .div (.op .add e_u (.const 1)) (.reg 14)

theorem eval_uCoordExpr {w p r : ℕ} {hp0 : 0 < p} {x : Alg74Input p r}
    (hw : Section5WordBounds w p r x)
    {s : State} (hs : RoutingStateHolds hp0 x s)
    (u : Fin (elemWallNumVerts x.h)) {e_u : Expr}
    (hu : e_u.eval w s = some u.1) :
    (uCoordXExpr e_u).eval w s = some (coordOf x.h u).1 ∧
    (uCoordYExpr e_u).eval w s = some (coordOf x.h u).2 := by
  have hw1 := hw.hw1
  have hw_2h2 := hw.h2h2_w
  have hw_loc := hw.hloc_w
  have hu_lt : u.1 < elemWallNumVerts x.h := u.2
  have hc1_ev := eval_const s hw1
  have hu1_ev := eval_op_add hu hc1_ev (by omega)
  have hr14_ev : (Expr.reg 14).eval w s = some (2 * x.h + 2) := eval_reg hs.hr14 hw_2h2
  have hcoord := coordOf_eq x.h u
  have hx_eq : (u.1 + 1) % (2 * x.h + 2) = (coordOf x.h u).1 :=
    (congrArg Prod.fst hcoord).symm
  have hy_eq : (u.1 + 1) / (2 * x.h + 2) = (coordOf x.h u).2 :=
    (congrArg Prod.snd hcoord).symm
  constructor
  · unfold uCoordXExpr
    rw [eval_op_mod hu1_ev hr14_ev (by omega), hx_eq]
  · unfold uCoordYExpr
    rw [eval_op_div hu1_ev hr14_ev (by omega), hy_eq]

/-- Expression testing whether `u` is the representative elementary-wall vertex of terminal `a`. -/
def isRepVertOfTermExpr {p : ℕ} (e_u : Expr) (a : Fin (alg74NumTerms p)) : Expr :=
  let e_loc := Expr.read locArr (.reg (regTermVert a.1))
  let e_rep := exprIte (exprLt e_loc (.reg 12)) e_loc
    (.read edgeU1Arr (.op .sub e_loc (.reg 12)))
  exprEq e_u e_rep

theorem eval_isRepVertOfTermExpr {w p r : ℕ} {hp0 : 0 < p} {x : Alg74Input p r}
    (hh1 : 1 ≤ x.h)
    (hw : Section5WordBounds w p r x)
    {s : State} (hs : RoutingStateHolds hp0 x s)
    (u : Fin (elemWallNumVerts x.h)) {e_u : Expr}
    (hu : e_u.eval w s = some u.1)
    (a : Fin (alg74NumTerms p)) :
    (isRepVertOfTermExpr e_u a).eval w s =
      some (if coordOf x.h u = repCoord x.W (alg74TermVert x a) then 1 else 0) := by
  have hw1 := hw.hw1
  have hw_n := hw.hn_w
  have hw_loc := hw.hloc_w
  let v := alg74TermVert x a
  have hv_mem : v ∈ x.W.vertexFinset := alg74TermVert_mem_vertexFinset x a
  have hv_reg : s.regs (regTermVert a.1) = v.1 :=
    alg74TermVert_val_eq_reg x s hs.hterm_edges a
  have hv_w : v.1 < 2 ^ w := by have := v.2; omega
  have hloc_lt : termLocCode x.W v < elemWallNumVerts x.h + (elemWallEdges x.h).length :=
    termLocCode_lt_of_mem_vertexFinset x.hW_valid.2.2 hv_mem
  have hloc_w : termLocCode x.W v < 2 ^ w := by omega
  have heloc_ev : (Expr.read locArr (.reg (regTermVert a.1))).eval w s = some (termLocCode x.W v) :=
    eval_read (eval_reg hv_reg hv_w) (by rw [hs.hloc_len]; exact v.2) (hs.hloc_val v hv_mem) hloc_w
  have hr12_w : elemWallNumVerts x.h < 2 ^ w := by omega
  have hr12_ev : (Expr.reg 12).eval w s = some (elemWallNumVerts x.h) := eval_reg hs.hr12 hr12_w
  let k_idx := termLocCode x.W v - elemWallNumVerts x.h
  have hEJ_pos : 0 < (elemWallEdges x.h).length := elemWallEdges_length_pos hh1
  have hk_lt : k_idx < (elemWallEdges x.h).length := by omega
  have hsub_ev :
      (Expr.op .sub (.read locArr (.reg (regTermVert a.1))) (.reg 12)).eval w s = some k_idx :=
    eval_op_sub heloc_ev hr12_ev
  let u_edge := ((elemWallEdges x.h)[k_idx]'hk_lt).1
  have huedge_w : u_edge.1 < 2 ^ w := by have := u_edge.2; omega
  have hu1_ev :
      (Expr.read edgeU1Arr
        (.op .sub (.read locArr (.reg (regTermVert a.1))) (.reg 12))).eval w s =
      some u_edge.1 :=
    eval_read hsub_ev (by rw [hs.hu1_len]; exact hk_lt) (hs.hu1_val ⟨k_idx, hk_lt⟩) huedge_w
  have herep_ev :
      (exprIte
        (exprLt (.read locArr (.reg (regTermVert a.1))) (.reg 12))
        (.read locArr (.reg (regTermVert a.1)))
        (.read edgeU1Arr (.op .sub (.read locArr (.reg (regTermVert a.1))) (.reg 12)))).eval w s =
      some (repVertOfLoc x.h (termLocCode x.W v) hloc_lt).1 := by
    rw [eval_exprIte hw1 (eval_exprLt hw1 heloc_ev hr12_ev) heloc_ev hu1_ev]
    congr 1
    unfold repVertOfLoc
    by_cases hlt : termLocCode x.W v < elemWallNumVerts x.h
    · simp [hlt]
    · simp [hlt, k_idx, u_edge]
  unfold isRepVertOfTermExpr
  rw [eval_exprEq hw1 hu herep_ev]
  congr 1
  apply if_congr _ rfl rfl
  have hcoord_rep : coordOf x.h (repVertOfLoc x.h (termLocCode x.W v) hloc_lt) = repCoord x.W v :=
    coordOf_repVertOfLoc_termLocCode x.hW_valid.2.2 hv_mem
  rw [← hcoord_rep]
  exact ⟨fun h => congrArg (coordOf x.h) (Fin.ext h),
    fun h => congrArg Fin.val (coordOf_injective x.h h)⟩

/-- Expression testing `coordOf x.h u ∈ wallCoordBranchSet hp x gamma`. -/
def inWallCoordBranchSetExpr (p : ℕ) (gamma : Fin p) (e_u : Expr) : Expr :=
  exprOr
    (inLiftGridCoarseBranchSetExpr p gamma (uCoordXExpr e_u) (uCoordYExpr e_u))
    (exprAny ((List.finRange (alg74NumTerms p)).filter (fun a => alg74RawColor p a == gamma))
      (fun a => isRepVertOfTermExpr e_u a))

theorem eval_inWallCoordBranchSetExpr {w p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p))
    (hh1 : 1 ≤ x.h)
    (hw : Section5WordBounds w p (alg74LiftRadius p) x)
    {s : State} (hs : RoutingStateHolds (by omega : 0 < p) x s)
    (gamma : Fin p) (u : Fin (elemWallNumVerts x.h)) {e_u : Expr}
    (hu : e_u.eval w s = some u.1) :
    (inWallCoordBranchSetExpr p gamma e_u).eval w s =
      some (if coordOf x.h u ∈ wallCoordBranchSet hp x gamma then 1 else 0) := by
  have hw2 := hw.hw2
  rcases eval_uCoordExpr hw hs u hu with ⟨hqx, hqy⟩
  have hqx_le : (coordOf x.h u).1 ≤ 2 * x.h + 1 := (coordOf_bounds x.h u).1
  have hlift_ev := eval_inLiftGridCoarseBranchSetExpr hp x hh1 hw hs gamma hqx_le hqx hqy
  have hany_ev :=
    eval_exprAny ((List.finRange (alg74NumTerms p)).filter (fun a => alg74RawColor p a == gamma))
      (fun a => isRepVertOfTermExpr e_u a)
      (fun a => coordOf x.h u = repCoord x.W (alg74TermVert x a)) hw2
      (fun a _ => eval_isRepVertOfTermExpr hh1 hw hs u hu a)
  unfold inWallCoordBranchSetExpr
  refine eval_eq_of_iff (eval_exprOr_inst hw2 hlift_ev hany_ev) ?_
  unfold wallCoordBranchSet
  rw [Finset.mem_union]
  refine or_congr Iff.rfl ?_
  rw [Finset.mem_image]
  dsimp only [alg74NumTerms]
  constructor
  · rintro ⟨a, ha, heq⟩
    rw [List.mem_filter, beq_iff_eq] at ha
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩, heq.symm⟩
  · rintro ⟨a, ha, heq⟩
    rw [Finset.mem_filter] at ha
    refine ⟨a, ?_, heq.symm⟩
    rw [List.mem_filter, beq_iff_eq]
    exact ⟨List.mem_finRange a, ha.2⟩

/-- Expression testing `wallEdgeActive hp x gamma k` for the `k`-th elementary-wall edge
`(u1, u2)`. -/
def wallEdgeActiveExpr (p : ℕ) (gamma : Fin p) (e_k e_u1 e_u2 : Expr) : Expr :=
  exprAnd
    (inWallCoordBranchSetExpr p gamma e_u1)
    (exprOr
      (inWallCoordBranchSetExpr p gamma e_u2)
      (exprAny ((List.finRange (alg74NumTerms p)).filter (fun a => alg74RawColor p a == gamma))
        (fun a =>
          exprEq (.read locArr (.reg (regTermVert a.1)))
            (.op .add (.reg 12) e_k))))

theorem eval_wallEdgeActiveExpr {w p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p))
    (hh1 : 1 ≤ x.h)
    (hw : Section5WordBounds w p (alg74LiftRadius p) x)
    {s : State} (hs : RoutingStateHolds (by omega : 0 < p) x s)
    (gamma : Fin p) (k : Fin (elemWallEdges x.h).length)
    {e_k e_u1 e_u2 : Expr}
    (hk : e_k.eval w s = some k.1)
    (hu1 : e_u1.eval w s = some ((elemWallEdges x.h)[k.1]'k.2).1.1)
    (hu2 : e_u2.eval w s = some ((elemWallEdges x.h)[k.1]'k.2).2.1) :
    (wallEdgeActiveExpr p gamma e_k e_u1 e_u2).eval w s =
      some (if wallEdgeActive hp x gamma k then 1 else 0) := by
  have hw1 := hw.hw1
  have hw2 := hw.hw2
  have hw_loc := hw.hloc_w
  let e := (elemWallEdges x.h)[k.1]'k.2
  have hu1_ev := eval_inWallCoordBranchSetExpr hp x hh1 hw hs gamma e.1 hu1
  have hu2_ev := eval_inWallCoordBranchSetExpr hp x hh1 hw hs gamma e.2 hu2
  have hk_lt : k.1 < (elemWallEdges x.h).length := k.2
  have hr12_w : elemWallNumVerts x.h < 2 ^ w := by omega
  have hr12_ev : (Expr.reg 12).eval w s = some (elemWallNumVerts x.h) := eval_reg hs.hr12 hr12_w
  have hadd_ev := eval_op_add hr12_ev hk (by omega)
  have hany_ev :=
    eval_exprAny ((List.finRange (alg74NumTerms p)).filter (fun a => alg74RawColor p a == gamma))
      (fun a =>
        exprEq (.read locArr (.reg (regTermVert a.1)))
          (.op .add (.reg 12) e_k))
      (fun a => alg74TermVert x a ∈ x.W.internalVerts k) hw2
      (fun a _ => by
        let v := alg74TermVert x a
        have hv_mem : v ∈ x.W.vertexFinset := alg74TermVert_mem_vertexFinset x a
        have hv_reg : s.regs (regTermVert a.1) = v.1 :=
          alg74TermVert_val_eq_reg x s hs.hterm_edges a
        have hv_w : v.1 < 2 ^ w := by have := v.2; have := hw.hn_w; omega
        have hloc_lt := termLocCode_lt_of_mem_vertexFinset x.hW_valid.2.2 hv_mem
        have hloc_w : termLocCode x.W v < 2 ^ w := by omega
        have heloc_ev : (Expr.read locArr (.reg (regTermVert a.1))).eval w s =
            some (termLocCode x.W v) :=
          eval_read (eval_reg hv_reg hv_w) (by rw [hs.hloc_len]; exact v.2)
            (hs.hloc_val v hv_mem) hloc_w
        exact eval_eq_of_iff (eval_exprEq hw1 heloc_ev hadd_ev)
          (mem_internalVerts_iff_termLocCode x.hW_valid.2.2 v k).symm)
  unfold wallEdgeActiveExpr
  refine eval_eq_of_iff (eval_exprAnd_inst hw1 hu1_ev (eval_exprOr_inst hw2 hu2_ev hany_ev)) ?_
  unfold wallEdgeActive
  dsimp only [e, alg74NumTerms]
  refine and_congr Iff.rfl (or_congr Iff.rfl ?_)
  constructor
  · rintro ⟨a, ha, hmem⟩
    rw [List.mem_filter, beq_iff_eq] at ha
    exact ⟨a, ha.2, hmem⟩
  · rintro ⟨a, ha, hmem⟩
    refine ⟨a, ?_, hmem⟩
    rw [List.mem_filter, beq_iff_eq]
    exact ⟨List.mem_finRange a, ha⟩

attribute [local irreducible] wallEdgeActive

/-! #### Sub-step 5b: Marking Wall Branch Vertices (`markWallBranchVertsCmd`) -/

/-- If `coordOf x.h u ∈ wallCoordBranchSet hp x gamma` (with `u = r_5`), mark `r_6 = x.W.branchVert u`
in color `gamma`'s bit slice of `outArr`. -/
def markBranchVertForColorCmd (p : ℕ) (gamma : Fin p) : Cmd :=
  let K := (completeGraphEdges p).length
  .ite (inWallCoordBranchSetExpr p gamma (.reg 5))
    (markVertexCmd K gamma.1 (.reg 6))
    .skip

theorem markBranchVertForColorCmd_free (p : ℕ) (gamma : Fin p) :
    (markBranchVertForColorCmd p gamma).IsLoopAllocFree :=
  ⟨trivial, trivial⟩

theorem markBranchVertForColorCmd_exec {w p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p))
    (hh1 : 1 ≤ x.h)
    (hw : Section5WordBounds w p (alg74LiftRadius p) x)
    {s : State} (hs : RoutingStateHolds (by omega : 0 < p) x s)
    (u : Fin (elemWallNumVerts x.h))
    (hr5 : s.regs 5 = u.1)
    (hr6 : s.regs 6 = (x.W.branchVert u).1)
    (hout_len : (s.arrs outArr).length = 2 + 2 * (completeGraphEdges p).length + p * x.n)
    (S : Fin p → Finset (Fin x.n))
    (hS : ∀ g : Fin p,
      IsBitSlice (s.arrs outArr) (2 + 2 * (completeGraphEdges p).length + g.1 * x.n) (S g))
    (gamma : Fin p) :
    let K := (completeGraphEdges p).length
    ∃ s' t,
      Exec w (markBranchVertForColorCmd p gamma) s s' t ∧
      (s'.arrs outArr).length = 2 + 2 * K + p * x.n ∧
      (∀ g : Fin p,
        IsBitSlice (s'.arrs outArr) (2 + 2 * K + g.1 * x.n)
          (if g = gamma ∧ coordOf x.h u ∈ wallCoordBranchSet hp x g then
            insert (x.W.branchVert u) (S g) else S g)) ∧
      (∀ i : ℕ, i < 2 + 2 * K → (s'.arrs outArr)[i]? = (s.arrs outArr)[i]?) ∧
      s'.regs = s.regs ∧
      (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a) := by
  intro K
  have hw1 := hw.hw1
  have hu_w : u.1 < 2 ^ w := by have := u.2; have := hw.hloc_w; omega
  have hr5_ev : (Expr.reg 5).eval w s = some u.1 := eval_reg hr5 hu_w
  have hcond := eval_inWallCoordBranchSetExpr hp x hh1 hw hs gamma u hr5_ev
  by_cases hmem : coordOf x.h u ∈ wallCoordBranchSet hp x gamma
  · rw [if_pos hmem] at hcond
    have hv_w : (x.W.branchVert u).1 < 2 ^ w := by
      have := (x.W.branchVert u).2; have := hw.hn_w; omega
    have hr6_ev : (Expr.reg 6).eval w s = some (x.W.branchVert u).1 := eval_reg hr6 hv_w
    rcases markVertexCmd_exec gamma (.reg 6) (x.W.branchVert u) hw1 hw.hp_w hw.hout_w
        hs.hr0 hr6_ev hout_len with
      ⟨hex_m, hout_len', hS_ins, hS_other, hprefix, hregs, harrs⟩
    refine ⟨_, _, Exec.ite_true hcond (by omega) hex_m, hout_len', ?_, hprefix, hregs, harrs⟩
    intro g
    by_cases hg : g = gamma
    · subst hg
      rw [if_pos ⟨rfl, hmem⟩]
      exact hS_ins (hS g)
    · rw [if_neg (fun h => hg h.1)]
      exact hS_other g hg (hS g)
  · rw [if_neg hmem] at hcond
    refine ⟨s, _, Exec.ite_false hcond (Exec.skip s), hout_len, ?_,
      fun _ _ => rfl, rfl, fun _ _ => rfl⟩
    intro g
    by_cases hg : g = gamma
    · subst hg
      rw [if_neg (fun h => hmem h.2)]
      exact hS g
    · rw [if_neg (fun h => hg h.1)]
      exact hS g

/-- Unrolled loop marking branch vertex `u` across all colors `gs : List (Fin p)`. -/
def markBranchVertAllColorsCmd (p : ℕ) : List (Fin p) → Cmd
  | [] => .skip
  | gamma :: gs => .seq (markBranchVertForColorCmd p gamma) (markBranchVertAllColorsCmd p gs)

theorem markBranchVertAllColorsCmd_free (p : ℕ) :
    ∀ gs : List (Fin p), (markBranchVertAllColorsCmd p gs).IsLoopAllocFree
  | [] => trivial
  | gamma :: gs => ⟨markBranchVertForColorCmd_free p gamma, markBranchVertAllColorsCmd_free p gs⟩

theorem markBranchVertAllColorsCmd_exec {w p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p))
    (hh1 : 1 ≤ x.h)
    (hw : Section5WordBounds w p (alg74LiftRadius p) x)
    (u : Fin (elemWallNumVerts x.h)) :
    ∀ (gs : List (Fin p)) (_hnd : gs.Nodup)
      (S : Fin p → Finset (Fin x.n)) {s : State}
      (_hs : RoutingStateHolds (by omega : 0 < p) x s)
      (_hr5 : s.regs 5 = u.1)
      (_hr6 : s.regs 6 = (x.W.branchVert u).1)
      (_hout_len : (s.arrs outArr).length = 2 + 2 * (completeGraphEdges p).length + p * x.n)
      (_hS : ∀ g : Fin p,
        IsBitSlice (s.arrs outArr) (2 + 2 * (completeGraphEdges p).length + g.1 * x.n) (S g)),
      let K := (completeGraphEdges p).length
      ∃ s' t,
        Exec w (markBranchVertAllColorsCmd p gs) s s' t ∧
        (s'.arrs outArr).length = 2 + 2 * K + p * x.n ∧
        (∀ g : Fin p,
          IsBitSlice (s'.arrs outArr) (2 + 2 * K + g.1 * x.n)
            (if g ∈ gs ∧ coordOf x.h u ∈ wallCoordBranchSet hp x g then
              insert (x.W.branchVert u) (S g) else S g)) ∧
        (∀ i : ℕ, i < 2 + 2 * K → (s'.arrs outArr)[i]? = (s.arrs outArr)[i]?) ∧
        s'.regs = s.regs ∧
        (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a)
  | [], _, S, s, _, _, _, hout_len, hS => by
    refine ⟨s, 1, Exec.skip s, hout_len, ?_, fun _ _ => rfl, rfl, fun _ _ => rfl⟩
    intro g
    simp [hS g]
  | gamma :: rest, hnd, S, s, hs, hr5, hr6, hout_len, hS => by
    rcases List.nodup_cons.mp hnd with ⟨hnot_mem, hnd_rest⟩
    rcases markBranchVertForColorCmd_exec hp x hh1 hw hs u hr5 hr6 hout_len S hS gamma with
      ⟨s₁, t₁, h1, hout_len1, hS₁, hprefix1, hregs1, harrs1⟩
    have hs₁ : RoutingStateHolds (by omega : 0 < p) x s₁ :=
      hs.of_preserve (fun reg _ => by rw [hregs1]) harrs1
    have hr5_1 : s₁.regs 5 = u.1 := by rw [hregs1, hr5]
    have hr6_1 : s₁.regs 6 = (x.W.branchVert u).1 := by rw [hregs1, hr6]
    let S₁ : Fin p → Finset (Fin x.n) := fun g =>
      if g = gamma ∧ coordOf x.h u ∈ wallCoordBranchSet hp x g then
        insert (x.W.branchVert u) (S g) else S g
    rcases markBranchVertAllColorsCmd_exec hp x hh1 hw u rest hnd_rest S₁ hs₁ hr5_1 hr6_1
        hout_len1 hS₁ with
      ⟨s₂, t₂, h2, hout_len2, hS₂, hprefix2, hregs2, harrs2⟩
    refine ⟨s₂, t₁ + t₂, Exec.seq h1 h2, hout_len2, ?_,
      fun i hi => (hprefix2 i hi).trans (hprefix1 i hi),
      hregs2.trans hregs1,
      fun a ha => (harrs2 a ha).trans (harrs1 a ha)⟩
    intro g
    have hg₂ := hS₂ g
    dsimp [S₁] at hg₂
    by_cases hgg : g = gamma
    · subst hgg
      simp only [hnot_mem, false_and, ↓reduceIte, List.mem_cons, true_or] at hg₂ ⊢
      exact hg₂
    · simp only [List.mem_cons, hgg, false_or, false_and, ↓reduceIte] at hg₂ ⊢
      exact hg₂

/-- Set of wall branch vertices `x.W.branchVert u` with `idx ≤ u.1` belonging to color `gamma`'s
branch set. -/
def branchVertsFrom {p r : ℕ} (hp : 2 ≤ p) (x : Alg74Input p r)
    (gamma : Fin p) (idx : ℕ) : Finset (Fin x.n) :=
  (Finset.univ.filter (fun u : Fin (elemWallNumVerts x.h) =>
    idx ≤ u.1 ∧ coordOf x.h u ∈ wallCoordBranchSet hp x gamma)).image x.W.branchVert

theorem branchVertsFrom_self {p r : ℕ} (hp : 2 ≤ p) (x : Alg74Input p r) (gamma : Fin p) :
    branchVertsFrom hp x gamma (elemWallNumVerts x.h) = ∅ := by
  unfold branchVertsFrom
  rw [Finset.image_eq_empty, Finset.filter_eq_empty_iff]
  intro u _
  have := u.2
  omega

theorem branchVertsFrom_step {p r : ℕ} (hp : 2 ≤ p) (x : Alg74Input p r)
    (gamma : Fin p) (u : Fin (elemWallNumVerts x.h)) (S : Finset (Fin x.n)) :
    (if coordOf x.h u ∈ wallCoordBranchSet hp x gamma then
      insert (x.W.branchVert u) S else S) ∪
      branchVertsFrom hp x gamma (u.1 + 1) =
    S ∪ branchVertsFrom hp x gamma u.1 := by
  ext v
  unfold branchVertsFrom
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hv | ⟨u', ⟨hu'1, hu'2⟩, rfl⟩)
    · by_cases hmem : coordOf x.h u ∈ wallCoordBranchSet hp x gamma
      · rw [if_pos hmem] at hv
        rcases Finset.mem_insert.mp hv with rfl | hvS
        · exact Or.inr ⟨u, ⟨le_rfl, hmem⟩, rfl⟩
        · exact Or.inl hvS
      · rw [if_neg hmem] at hv
        exact Or.inl hv
    · exact Or.inr ⟨u', ⟨by omega, hu'2⟩, rfl⟩
  · rintro (hvS | ⟨u', ⟨hu'1, hu'2⟩, rfl⟩)
    · left
      split_ifs with hmem
      · exact Finset.mem_insert_of_mem hvS
      · exact hvS
    · rcases eq_or_lt_of_le hu'1 with heq | hlt
      · left
        have hu_eq : u' = u := Fin.ext heq.symm
        subst hu_eq
        rw [if_pos hu'2]
        exact Finset.mem_insert_self _ _
      · exact Or.inr ⟨u', ⟨by omega, hu'2⟩, rfl⟩

/-- Loop body of `markWallBranchVertsLoop`: reads `r_6 := inArr[r_4]`, marks `r_6` across all
colors `gamma : Fin p` for which `r_5 ∈ wallCoordBranchSet`, and advances `r_4, r_5, r_1`. -/
def markWallBranchVertsBody (p : ℕ) : Cmd :=
  .seq (.assign 6 (.read inArr (.reg 4)))
    (.seq (markBranchVertAllColorsCmd p (List.finRange p))
      (.seq (.assign 4 (.op .add (.reg 4) (.const 1)))
        (.seq (.assign 5 (.op .add (.reg 5) (.const 1)))
          (.assign 1 (.op .sub (.reg 1) (.const 1))))))

theorem markWallBranchVertsBody_free (p : ℕ) :
    (markWallBranchVertsBody p).IsLoopAllocFree :=
  ⟨trivial, markBranchVertAllColorsCmd_free p _, trivial, trivial, trivial⟩

/-- Loop over all `V_J = elemWallNumVerts x.h` branch vertices in `inArr`. -/
def markWallBranchVertsLoop (p : ℕ) : Cmd :=
  .while (.op .lt (.const 0) (.reg 1)) (markWallBranchVertsBody p)

theorem markWallBranchVertsLoop_exec {w p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p))
    (hh1 : 1 ≤ x.h)
    (hw : Section5WordBounds w p (alg74LiftRadius p) x) :
    ∀ (rem idx : ℕ) (_hrem : idx + rem = elemWallNumVerts x.h)
      (S : Fin p → Finset (Fin x.n)) {s : State}
      (_hs : RoutingStateHolds (by omega : 0 < p) x s)
      (_hr4 : s.regs 4 = 2 + 3 * x.G.numActivePairs + 3 + idx)
      (_hr5 : s.regs 5 = idx)
      (_hr1 : s.regs 1 = rem)
      (_hout_len : (s.arrs outArr).length = 2 + 2 * (completeGraphEdges p).length + p * x.n)
      (_hS : ∀ gamma : Fin p,
        IsBitSlice (s.arrs outArr) (2 + 2 * (completeGraphEdges p).length + gamma.1 * x.n)
          (S gamma)),
      let K := (completeGraphEdges p).length
      ∃ s' t,
        Exec w (markWallBranchVertsLoop p) s s' t ∧
        t ≤ ((markWallBranchVertsBody p).maxTime + 3) * rem + 3 ∧
        RoutingStateHolds (by omega : 0 < p) x s' ∧
        s'.regs 4 = 2 + 3 * x.G.numActivePairs + 3 + elemWallNumVerts x.h ∧
        (s'.arrs outArr).length = 2 + 2 * K + p * x.n ∧
        (∀ gamma : Fin p,
          IsBitSlice (s'.arrs outArr) (2 + 2 * K + gamma.1 * x.n)
            (S gamma ∪ branchVertsFrom hp x gamma idx)) ∧
        (∀ i : ℕ, i < 2 + 2 * K → (s'.arrs outArr)[i]? = (s.arrs outArr)[i]?) ∧
        (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a)
  | 0, idx, hrem, S, s, hs, hr4, _, hr1, hout_len, hS => by
    have hidx_eq : idx = elemWallNumVerts x.h := by omega
    subst hidx_eq
    have h0_w := hw.hw0
    have hcond : (Expr.op .lt (.const 0) (.reg 1)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, hs, hr4, hout_len, ?_,
      fun _ _ => rfl, fun _ _ => rfl⟩
    intro gamma
    rw [branchVertsFrom_self, Finset.union_empty]
    exact hS gamma
  | rem + 1, idx, hrem, S, s, hs, hr4, hr5, hr1, hout_len, hS => by
    intro K
    have h0_w := hw.hw0
    have hw1 := hw.hw1
    have hidx_lt : idx < elemWallNumVerts x.h := by omega
    let u : Fin (elemWallNumVerts x.h) := ⟨idx, hidx_lt⟩
    have hrem_w : rem + 1 < 2 ^ w := by have := hw.hloc_w; omega
    have hrem0_w : rem < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 1)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1, h0_w, hw1, hrem_w]
    let pos := 2 + 3 * x.G.numActivePairs + 3 + idx
    have hin_len_ge :
        2 + 3 * x.G.numActivePairs + 3 + elemWallNumVerts x.h ≤ (encAlg74In x).length := by
      simp only [encAlg74In, List.length_append, MultiDigraph.length_enc,
        WallOfHeight.length_encList]
      omega
    have hpos_lt : pos < (s.arrs inArr).length := by
      rw [hs.hin]; dsimp [pos]; omega
    have hpos_w : pos < 2 ^ w := by have := hw.hin_w; dsimp [pos]; omega
    have hpos1_w : pos + 1 < 2 ^ w := by have := hw.hin_w; dsimp [pos]; omega
    have hget_br : (s.arrs inArr)[pos]'hpos_lt = (x.W.branchVert u).1 := by
      apply getElem_of_getElem? _ hpos_lt
      rw [hs.hin]
      exact getElem?_encAlg74In_branchVert x u
    have hbr_w : (x.W.branchVert u).1 < 2 ^ w := by
      have := (x.W.branchVert u).2; have := hw.hn_w; omega
    let s₁ := s.setReg 6 (x.W.branchVert u).1
    have hex₁ : Exec w (.assign 6 (.read inArr (.reg 4))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr4, pos, hpos_w, hpos_lt, hget_br, hbr_w])
    have hs₁ : RoutingStateHolds (by omega : 0 < p) x s₁ :=
      hs.of_preserve (fun reg hreg => by
        have hne : reg ≠ 6 := by dsimp [Reg] at *; omega
        exact State.setReg_regs_ne _ _ hne) (fun _ _ => rfl)
    have hr5_1 : s₁.regs 5 = u.1 := by simp [s₁, hr5, u]
    have hr6_1 : s₁.regs 6 = (x.W.branchVert u).1 := by simp [s₁]
    have hout_len1 : (s₁.arrs outArr).length = 2 + 2 * K + p * x.n := by simp [s₁, hout_len, K]
    have hS₁ : ∀ g : Fin p, IsBitSlice (s₁.arrs outArr) (2 + 2 * K + g.1 * x.n) (S g) := by
      intro g; simpa [s₁] using hS g
    rcases markBranchVertAllColorsCmd_exec hp x hh1 hw u (List.finRange p) (List.nodup_finRange p)
        S hs₁ hr5_1 hr6_1 hout_len1 hS₁ with
      ⟨s₂, t₂, hex₂, hout_len2, hS₂_raw, hprefix2, hregs2, harrs2⟩
    let S₂ : Fin p → Finset (Fin x.n) := fun g =>
      if coordOf x.h u ∈ wallCoordBranchSet hp x g then
        insert (x.W.branchVert u) (S g) else S g
    have hS₂ : ∀ g : Fin p, IsBitSlice (s₂.arrs outArr) (2 + 2 * K + g.1 * x.n) (S₂ g) := by
      intro g
      have h := hS₂_raw g
      simp only [List.mem_finRange, true_and] at h
      exact h
    have hr4_2 : s₂.regs 4 = pos := by rw [hregs2]; simp [s₁, hr4, pos]
    have hr5_2 : s₂.regs 5 = idx := by rw [hregs2]; simp [s₁, hr5]
    have hr1_2 : s₂.regs 1 = rem + 1 := by rw [hregs2]; simp [s₁, hr1]
    have hidx_w : idx < 2 ^ w := by have := hw.hloc_w; omega
    have hidx1_w : idx + 1 < 2 ^ w := by have := hw.hloc_w; omega
    let s₃ := s₂.setReg 4 (pos + 1)
    have hex₃ : Exec w (.assign 4 (.op .add (.reg 4) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_2, hpos_w, hw1, hpos1_w])
    let s₄ := s₃.setReg 5 (idx + 1)
    have hex₄ : Exec w (.assign 5 (.op .add (.reg 5) (.const 1))) s₃ s₄ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, hr5_2, hidx_w, hw1, hidx1_w])
    let s₅ := s₄.setReg 1 rem
    have hex₅ : Exec w (.assign 1 (.op .sub (.reg 1) (.const 1))) s₄ s₅ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₄, s₃, hr1_2,
        hrem_w, hw1, hrem0_w])
    have hex_body : Exec w (markWallBranchVertsBody p) s s₅ (3 + (t₂ + (4 + (4 + 4)))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))
    have ht_body := Exec.time_le_maxTime hex_body (markWallBranchVertsBody_free p)
    have hs₅ : RoutingStateHolds (by omega : 0 < p) x s₅ :=
      hs.of_preserve (fun reg hreg => by
        have h1 : reg ≠ 1 := by dsimp [Reg] at *; omega
        have h4 : reg ≠ 4 := by dsimp [Reg] at *; omega
        have h5 : reg ≠ 5 := by dsimp [Reg] at *; omega
        have h6 : reg ≠ 6 := by dsimp [Reg] at *; omega
        simp [s₅, s₄, s₃, h1, h4, h5, hregs2, s₁, h6])
      (fun a ha => by simp [s₅, s₄, s₃, harrs2 a ha, s₁])
    have hr4_5 : s₅.regs 4 = 2 + 3 * x.G.numActivePairs + 3 + (idx + 1) := by
      simp [s₅, s₄, s₃, pos]; omega
    have hr5_5 : s₅.regs 5 = idx + 1 := by simp [s₅, s₄]
    have hr1_5 : s₅.regs 1 = rem := by simp [s₅]
    have hout_len5 : (s₅.arrs outArr).length = 2 + 2 * K + p * x.n := by
      simpa [s₅, s₄, s₃] using hout_len2
    have hS₅ : ∀ g : Fin p, IsBitSlice (s₅.arrs outArr) (2 + 2 * K + g.1 * x.n) (S₂ g) := by
      intro g; simpa [s₅, s₄, s₃] using hS₂ g
    rcases markWallBranchVertsLoop_exec hp x hh1 hw rem (idx + 1) (by omega) S₂ hs₅
        hr4_5 hr5_5 hr1_5 hout_len5 hS₅ with
      ⟨s', t_rest, hex_rest, ht_rest, hs', hr4', hout_len', hS', hprefix', harrs'⟩
    refine ⟨s', 3 + (3 + (t₂ + (4 + (4 + 4)))) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      by rw [Nat.mul_succ]; omega,
      hs', hr4', hout_len', ?_,
      fun i hi => by rw [hprefix' i hi]; simpa [s₅, s₄, s₃, s₁] using hprefix2 i hi,
      fun a ha => by rw [harrs' a ha]; simp [s₅, s₄, s₃, harrs2 a ha, s₁]⟩
    intro gamma
    have h := hS' gamma
    dsimp [S₂] at h
    rwa [show idx + 1 = u.1 + 1 from rfl, branchVertsFrom_step] at h

/-- Step 5b (`markWallBranchVertsCmd p`): initializes `r_4 = r_2 + 3`, `r_5 = 0`, `r_1 = r_12`
and runs `markWallBranchVertsLoop p`. -/
def markWallBranchVertsCmd (p : ℕ) : Cmd :=
  .seq (.assign 4 (.op .add (.reg 2) (.const 3)))
    (.seq (.assign 5 (.const 0))
      (.seq (.assign 1 (.reg 12))
        (markWallBranchVertsLoop p)))

theorem markWallBranchVertsCmd_exec {w p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p))
    (hh1 : 1 ≤ x.h)
    (hw : Section5WordBounds w p (alg74LiftRadius p) x)
    (S : Fin p → Finset (Fin x.n))
    {s : State} (hs : RoutingStateHolds (by omega : 0 < p) x s)
    (hout_len : (s.arrs outArr).length = 2 + 2 * (completeGraphEdges p).length + p * x.n)
    (hS : ∀ gamma : Fin p,
      IsBitSlice (s.arrs outArr) (2 + 2 * (completeGraphEdges p).length + gamma.1 * x.n)
        (S gamma)) :
    let K := (completeGraphEdges p).length
    ∃ s' t,
      Exec w (markWallBranchVertsCmd p) s s' t ∧
      t ≤ ((markWallBranchVertsBody p).maxTime + 3) * elemWallNumVerts x.h + 15 ∧
      RoutingStateHolds (by omega : 0 < p) x s' ∧
      s'.regs 4 = 2 + 3 * x.G.numActivePairs + 3 + elemWallNumVerts x.h ∧
      (s'.arrs outArr).length = 2 + 2 * K + p * x.n ∧
      (∀ gamma : Fin p,
        IsBitSlice (s'.arrs outArr) (2 + 2 * K + gamma.1 * x.n)
          (S gamma ∪ branchVertsFrom hp x gamma 0)) ∧
      (∀ i : ℕ, i < 2 + 2 * K → (s'.arrs outArr)[i]? = (s.arrs outArr)[i]?) ∧
      (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a) := by
  intro K
  have h0_w := hw.hw0
  have hw3 := hw.hw3
  have hin_len_ge :
      2 + 3 * x.G.numActivePairs + 3 ≤ (encAlg74In x).length := by
    simp only [encAlg74In, List.length_append, MultiDigraph.length_enc,
      WallOfHeight.length_encList]
    omega
  have hwoff_w : 2 + 3 * x.G.numActivePairs < 2 ^ w := hw.hm_w
  have hwoff3_w : 2 + 3 * x.G.numActivePairs + 3 < 2 ^ w := by
    have := hw.hin_w; omega
  have hVJ_w : elemWallNumVerts x.h < 2 ^ w := by have := hw.hloc_w; omega
  let s₁ := s.setReg 4 (2 + 3 * x.G.numActivePairs + 3)
  have hex₁ : Exec w (.assign 4 (.op .add (.reg 2) (.const 3))) s s₁ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hs.hr2, hwoff_w, hw3, hwoff3_w])
  let s₂ := s₁.setReg 5 0
  have hex₂ : Exec w (.assign 5 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₃ := s₂.setReg 1 (elemWallNumVerts x.h)
  have hex₃ : Exec w (.assign 1 (.reg 12)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₂, s₁, hs.hr12, hVJ_w])
  have hs₃ : RoutingStateHolds (by omega : 0 < p) x s₃ :=
    hs.of_preserve (fun reg hreg => by
      have h1 : reg ≠ 1 := by dsimp [Reg] at *; omega
      have h4 : reg ≠ 4 := by dsimp [Reg] at *; omega
      have h5 : reg ≠ 5 := by dsimp [Reg] at *; omega
      simp [s₃, s₂, s₁, h1, h4, h5])
    (fun _ _ => rfl)
  rcases markWallBranchVertsLoop_exec hp x hh1 hw (elemWallNumVerts x.h) 0 (Nat.zero_add _) S hs₃
      (by simp [s₃, s₂, s₁]) (by simp [s₃, s₂]) (by simp [s₃])
      (by simp [s₃, s₂, s₁, hout_len])
      (fun gamma => by simpa [s₃, s₂, s₁] using hS gamma) with
    ⟨s', t_loop, hex₄, ht_loop, hs', hr4', hout_len', hS', hprefix', harrs'⟩
  refine ⟨s', 4 + (2 + (2 + t_loop)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hs', hr4', hout_len', hS',
    fun i hi => by rw [hprefix' i hi]; rfl,
    fun a ha => by rw [harrs' a ha]; rfl⟩

/-! #### Sub-step 5c: Marking Wall Internal Vertices (`markWallInternalVertsCmd`) -/

/-- If `wallEdgeActive hp x gamma k` holds (with `k = r_5`, `u1 = r_6`, `u2 = r_7`), mark all
vertices of `x.W.internalVerts k` in color `gamma`'s bit slice of `outArr` using
`markPathListLoop`. -/
def markInternalEdgeForColorCmd (p : ℕ) (gamma : Fin p) : Cmd :=
  let K := (completeGraphEdges p).length
  .ite (wallEdgeActiveExpr p gamma (.reg 5) (.reg 6) (.reg 7))
    (.seq (.assign 8 (.op .add (.reg 4) (.const 1)))
      (.seq (.assign 9 (.reg 10))
        (markPathListLoop K gamma.1)))
    .skip

theorem markInternalEdgeForColorCmd_exec {w p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p))
    (hh1 : 1 ≤ x.h)
    (hw : Section5WordBounds w p (alg74LiftRadius p) x)
    (k : Fin (elemWallEdges x.h).length)
    (pre suf : List ℕ)
    (S : Fin p → Finset (Fin x.n))
    {s : State} (hs : RoutingStateHolds (by omega : 0 < p) x s)
    (hsplit : encAlg74In x =
      pre ++ ((x.W.internalVerts k).length :: (x.W.internalVerts k).map Fin.val ++ suf))
    (hr4 : s.regs 4 = pre.length)
    (hr5 : s.regs 5 = k.1)
    (hr6 : s.regs 6 = ((elemWallEdges x.h)[k.1]'k.2).1.1)
    (hr7 : s.regs 7 = ((elemWallEdges x.h)[k.1]'k.2).2.1)
    (hr10 : s.regs 10 = (x.W.internalVerts k).length)
    (hout_len : (s.arrs outArr).length = 2 + 2 * (completeGraphEdges p).length + p * x.n)
    (hS : ∀ g : Fin p,
      IsBitSlice (s.arrs outArr) (2 + 2 * (completeGraphEdges p).length + g.1 * x.n) (S g))
    (gamma : Fin p) :
    let K := (completeGraphEdges p).length
    ∃ s' t,
      Exec w (markInternalEdgeForColorCmd p gamma) s s' t ∧
      t ≤ (wallEdgeActiveExpr p gamma (.reg 5) (.reg 6) (.reg 7)).cost + 10 +
        23 * (x.W.internalVerts k).length ∧
      (s'.arrs outArr).length = 2 + 2 * K + p * x.n ∧
      (∀ g : Fin p,
        IsBitSlice (s'.arrs outArr) (2 + 2 * K + g.1 * x.n)
          (if g = gamma ∧ wallEdgeActive hp x g k then
            S g ∪ (x.W.internalVerts k).toFinset else S g)) ∧
      (∀ i : ℕ, i < 2 + 2 * K → (s'.arrs outArr)[i]? = (s.arrs outArr)[i]?) ∧
      (∀ reg : Reg, reg ≠ 8 → reg ≠ 9 → reg ≠ 11 → s'.regs reg = s.regs reg) ∧
      (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a) := by
  intro K
  have hw1 := hw.hw1
  have hk_w : k.1 < 2 ^ w := by have := k.2; have := hw.hloc_w; omega
  let e := (elemWallEdges x.h)[k.1]'k.2
  have hu1_w : e.1.1 < 2 ^ w := by have := e.1.2; have := hw.hloc_w; omega
  have hu2_w : e.2.1 < 2 ^ w := by have := e.2.2; have := hw.hloc_w; omega
  have hcond := eval_wallEdgeActiveExpr hp x hh1 hw hs gamma k
    (eval_reg hr5 hk_w) (eval_reg hr6 hu1_w) (eval_reg hr7 hu2_w)
  by_cases hact : wallEdgeActive hp x gamma k
  · rw [if_pos hact] at hcond
    have hlen_in :
        pre.length + 1 + (x.W.internalVerts k).length ≤ (encAlg74In x).length := by
      rw [hsplit]
      simp only [List.length_append, List.length_cons, List.length_map]
      omega
    have hpre_w : pre.length < 2 ^ w := by have := hw.hin_w; omega
    have hpre1_w : pre.length + 1 < 2 ^ w := by have := hw.hin_w; omega
    have hlenk_w : (x.W.internalVerts k).length < 2 ^ w := by have := hw.hin_w; omega
    let s₁ := s.setReg 8 (pre.length + 1)
    have hex₁ : Exec w (.assign 8 (.op .add (.reg 4) (.const 1))) s s₁ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4, hpre_w, hw1, hpre1_w])
    let s₂ := s₁.setReg 9 (x.W.internalVerts k).length
    have hex₂ : Exec w (.assign 9 (.reg 10)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, s₁, hr10, hlenk_w])
    have hin₂ :
        s₂.arrs inArr =
          (pre ++ [(x.W.internalVerts k).length]) ++
            ((x.W.internalVerts k).map Fin.val ++ suf) := by
      have heq : s₂.arrs inArr = encAlg74In x := by simp [s₂, s₁, hs.hin]
      rw [heq, hsplit]
      simp
    have hin_w2 : (s₂.arrs inArr).length < 2 ^ w := by
      have heq : s₂.arrs inArr = encAlg74In x := by simp [s₂, s₁, hs.hin]
      rw [heq]; exact hw.hin_w
    rcases markPathListLoop_exec gamma hw1 hw.hp_w hw.hn_w hw.hout_w
        (x.W.internalVerts k) (pre ++ [(x.W.internalVerts k).length]) suf (S gamma) (s := s₂)
        hin₂ hin_w2 (by simp [s₂, s₁, hs.hr0])
        (by simp [s₂, s₁]) (by simp [s₂])
        (by simp [s₂, s₁, hout_len])
        (by simpa [s₂, s₁] using hS gamma) with
      ⟨s₃, t₃, hex₃, ht₃, hout_len3, hS₃, hS_other3, hprefix3, hregs3, harrs3⟩
    refine ⟨s₃, _,
      Exec.ite_true hcond (by omega) (.seq hex₁ (.seq hex₂ hex₃)),
      by omega, hout_len3, ?_,
      fun i hi => by rw [hprefix3 i hi]; rfl,
      fun reg h8 h9 h11 => by
        rw [hregs3 reg h8 h9 h11]
        simp [s₂, s₁, h8, h9],
      fun a ha => by rw [harrs3 a ha]; rfl⟩
    intro g
    by_cases hg : g = gamma
    · subst hg
      rw [if_pos ⟨rfl, hact⟩]
      exact hS₃
    · rw [if_neg (fun h => hg h.1)]
      exact hS_other3 g hg (by simpa [s₂, s₁] using hS g)
  · rw [if_neg hact] at hcond
    refine ⟨s, _, Exec.ite_false hcond (Exec.skip s), by omega, hout_len, ?_,
      fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
    intro g
    by_cases hg : g = gamma
    · subst hg
      rw [if_neg (fun h => hact h.2)]
      exact hS g
    · rw [if_neg (fun h => hg h.1)]
      exact hS g

/-- Cost constant for evaluating `wallEdgeActiveExpr` across `gs : List (Fin p)`. -/
def markActCost (p : ℕ) : List (Fin p) → ℕ
  | [] => 1
  | gamma :: gs =>
    (wallEdgeActiveExpr p gamma (.reg 5) (.reg 6) (.reg 7)).cost + 10 + markActCost p gs

/-- Unrolled loop marking `x.W.internalVerts k` across all colors `gs : List (Fin p)`. -/
def markInternalEdgeAllColorsCmd (p : ℕ) : List (Fin p) → Cmd
  | [] => .skip
  | gamma :: gs => .seq (markInternalEdgeForColorCmd p gamma) (markInternalEdgeAllColorsCmd p gs)

theorem markInternalEdgeAllColorsCmd_exec {w p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p))
    (hh1 : 1 ≤ x.h)
    (hw : Section5WordBounds w p (alg74LiftRadius p) x)
    (k : Fin (elemWallEdges x.h).length)
    (pre suf : List ℕ) :
    ∀ (gs : List (Fin p)) (_hnd : gs.Nodup)
      (S : Fin p → Finset (Fin x.n)) {s : State}
      (_hs : RoutingStateHolds (by omega : 0 < p) x s)
      (_hsplit : encAlg74In x =
        pre ++ ((x.W.internalVerts k).length :: (x.W.internalVerts k).map Fin.val ++ suf))
      (_hr4 : s.regs 4 = pre.length)
      (_hr5 : s.regs 5 = k.1)
      (_hr6 : s.regs 6 = ((elemWallEdges x.h)[k.1]'k.2).1.1)
      (_hr7 : s.regs 7 = ((elemWallEdges x.h)[k.1]'k.2).2.1)
      (_hr10 : s.regs 10 = (x.W.internalVerts k).length)
      (_hout_len : (s.arrs outArr).length = 2 + 2 * (completeGraphEdges p).length + p * x.n)
      (_hS : ∀ g : Fin p,
        IsBitSlice (s.arrs outArr) (2 + 2 * (completeGraphEdges p).length + g.1 * x.n) (S g)),
      let K := (completeGraphEdges p).length
      ∃ s' t,
        Exec w (markInternalEdgeAllColorsCmd p gs) s s' t ∧
        t ≤ markActCost p gs + 23 * gs.length * (x.W.internalVerts k).length ∧
        (s'.arrs outArr).length = 2 + 2 * K + p * x.n ∧
        (∀ g : Fin p,
          IsBitSlice (s'.arrs outArr) (2 + 2 * K + g.1 * x.n)
            (if g ∈ gs ∧ wallEdgeActive hp x g k then
              S g ∪ (x.W.internalVerts k).toFinset else S g)) ∧
        (∀ i : ℕ, i < 2 + 2 * K → (s'.arrs outArr)[i]? = (s.arrs outArr)[i]?) ∧
        (∀ reg : Reg, reg ≠ 8 → reg ≠ 9 → reg ≠ 11 → s'.regs reg = s.regs reg) ∧
        (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a)
  | [], _, S, s, _, _, _, _, _, _, _, hout_len, hS => by
    refine ⟨s, 1, Exec.skip s, by simp [markActCost], hout_len, ?_,
      fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
    intro g
    simp [hS g]
  | gamma :: rest, hnd, S, s, hs, hsplit, hr4, hr5, hr6, hr7, hr10, hout_len, hS => by
    rcases List.nodup_cons.mp hnd with ⟨hnot_mem, hnd_rest⟩
    rcases markInternalEdgeForColorCmd_exec hp x hh1 hw k pre suf S hs hsplit
        hr4 hr5 hr6 hr7 hr10 hout_len hS gamma with
      ⟨s₁, t₁, h1, ht₁, hout_len1, hS₁, hprefix1, hregs1, harrs1⟩
    have hs₁ : RoutingStateHolds (by omega : 0 < p) x s₁ :=
      hs.of_preserve (fun reg hreg =>
        hregs1 reg (by dsimp [Reg] at *; omega) (by dsimp [Reg] at *; omega)
          (by dsimp [Reg] at *; omega)) harrs1
    have hr4_1 : s₁.regs 4 = pre.length := by
      rw [hregs1 4 (by decide) (by decide) (by decide), hr4]
    have hr5_1 : s₁.regs 5 = k.1 := by
      rw [hregs1 5 (by decide) (by decide) (by decide), hr5]
    have hr6_1 : s₁.regs 6 = ((elemWallEdges x.h)[k.1]'k.2).1.1 := by
      rw [hregs1 6 (by decide) (by decide) (by decide), hr6]
    have hr7_1 : s₁.regs 7 = ((elemWallEdges x.h)[k.1]'k.2).2.1 := by
      rw [hregs1 7 (by decide) (by decide) (by decide), hr7]
    have hr10_1 : s₁.regs 10 = (x.W.internalVerts k).length := by
      rw [hregs1 10 (by decide) (by decide) (by decide), hr10]
    let S₁ : Fin p → Finset (Fin x.n) := fun g =>
      if g = gamma ∧ wallEdgeActive hp x g k then
        S g ∪ (x.W.internalVerts k).toFinset else S g
    rcases markInternalEdgeAllColorsCmd_exec hp x hh1 hw k pre suf rest hnd_rest S₁ hs₁
        hsplit hr4_1 hr5_1 hr6_1 hr7_1 hr10_1 hout_len1 hS₁ with
      ⟨s₂, t₂, h2, ht₂, hout_len2, hS₂, hprefix2, hregs2, harrs2⟩
    refine ⟨s₂, t₁ + t₂, Exec.seq h1 h2, ?_, hout_len2, ?_,
      fun i hi => (hprefix2 i hi).trans (hprefix1 i hi),
      fun reg h8 h9 h11 => (hregs2 reg h8 h9 h11).trans (hregs1 reg h8 h9 h11),
      fun a ha => (harrs2 a ha).trans (harrs1 a ha)⟩
    · simp only [markActCost, List.length_cons]
      nlinarith
    · intro g
      have hg₂ := hS₂ g
      dsimp [S₁] at hg₂
      by_cases hgg : g = gamma
      · subst hgg
        simp only [hnot_mem, false_and, ↓reduceIte, List.mem_cons, true_or] at hg₂ ⊢
        exact hg₂
      · simp only [List.mem_cons, hgg, false_or, false_and, ↓reduceIte] at hg₂ ⊢
        exact hg₂

/-- Union of `(x.W.internalVerts k).toFinset` over active edges `k ∈ ks` for color `gamma`. -/
def internalVertsSliceUnion {p r : ℕ} (hp : 2 ≤ p) (x : Alg74Input p r)
    (gamma : Fin p) : List (Fin (elemWallEdges x.h).length) → Finset (Fin x.n)
  | [] => ∅
  | k :: rest =>
    (if wallEdgeActive hp x gamma k then (x.W.internalVerts k).toFinset else ∅) ∪
      internalVertsSliceUnion hp x gamma rest

theorem mem_internalVertsSliceUnion_iff {p r : ℕ} (hp : 2 ≤ p) (x : Alg74Input p r)
    (gamma : Fin p) :
    ∀ (ks : List (Fin (elemWallEdges x.h).length)) (v : Fin x.n),
      v ∈ internalVertsSliceUnion hp x gamma ks ↔
        ∃ k ∈ ks, wallEdgeActive hp x gamma k ∧ v ∈ x.W.internalVerts k
  | [], v => by simp [internalVertsSliceUnion]
  | k :: rest, v => by
    simp only [internalVertsSliceUnion, Finset.mem_union,
      mem_internalVertsSliceUnion_iff hp x gamma rest v, List.mem_cons, exists_eq_or_imp]
    by_cases hact : wallEdgeActive hp x gamma k <;> simp [hact]

theorem branchVertsFrom_zero_union_internalVertsSliceUnion_finRange {p r : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p r) (gamma : Fin p) :
    branchVertsFrom hp x gamma 0 ∪
      internalVertsSliceUnion hp x gamma (List.finRange (elemWallEdges x.h).length) =
    wallVertBranchSet hp x gamma := by
  ext v
  unfold wallVertBranchSet branchVertsFrom
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Nat.zero_le, Finset.mem_biUnion, List.mem_toFinset, mem_internalVertsSliceUnion_iff,
    List.mem_finRange]

/-- Loop body of `markWallInternalVertsLoop`: reads `r_6 = edgeU1Arr[r_5]`, `r_7 = edgeU2Arr[r_5]`,
`r_10 = inArr[r_4]`, marks `x.W.internalVerts r_5` across all colors `gamma : Fin p`, and advances
`r_4, r_5, r_1`. -/
def markWallInternalVertsBody (p : ℕ) : Cmd :=
  .seq (.assign 6 (.read edgeU1Arr (.reg 5)))
    (.seq (.assign 7 (.read edgeU2Arr (.reg 5)))
      (.seq (.assign 10 (.read inArr (.reg 4)))
        (.seq (markInternalEdgeAllColorsCmd p (List.finRange p))
          (.seq (.assign 4 (.op .add (.op .add (.reg 4) (.const 1)) (.reg 10)))
            (.seq (.assign 5 (.op .add (.reg 5) (.const 1)))
              (.assign 1 (.op .sub (.reg 1) (.const 1))))))))

/-- Loop over all `E_J = (elemWallEdges x.h).length` internal vertex lists in `inArr`. -/
def markWallInternalVertsLoop (p : ℕ) : Cmd :=
  .while (.op .lt (.const 0) (.reg 1)) (markWallInternalVertsBody p)

private theorem getElem_append_cons {α : Type*} (pre : List α) (a : α) (suf : List α)
    (pos : ℕ) (hpos : pre.length = pos) :
    (pre ++ (a :: suf))[pos]'(by simp [hpos]) = a := by
  subst hpos
  rw [List.getElem_append_right le_rfl]
  simp

theorem markWallInternalVertsLoop_exec {w p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p))
    (hh1 : 1 ≤ x.h)
    (hw : Section5WordBounds w p (alg74LiftRadius p) x) :
    ∀ (ks : List (Fin (elemWallEdges x.h).length)) (_hnd : ks.Nodup)
      (pre suf : List ℕ)
      (S : Fin p → Finset (Fin x.n)) {s : State}
      (_hs : RoutingStateHolds (by omega : 0 < p) x s)
      (_hsplit : encAlg74In x = pre ++ (encInternalSlice x.W ks ++ suf))
      (_hr4 : s.regs 4 = pre.length)
      (_hr5 : ∀ k_head, ks.head? = some k_head → s.regs 5 = k_head.1)
      (_hconsec : ∀ i (hi : i + 1 < ks.length),
        (ks[i + 1]'hi).1 = (ks[i]'(by omega)).1 + 1)
      (_hr1 : s.regs 1 = ks.length)
      (_hout_len : (s.arrs outArr).length = 2 + 2 * (completeGraphEdges p).length + p * x.n)
      (_hS : ∀ gamma : Fin p,
        IsBitSlice (s.arrs outArr) (2 + 2 * (completeGraphEdges p).length + gamma.1 * x.n)
          (S gamma)),
      let K := (completeGraphEdges p).length
      ∃ s' t,
        Exec w (markWallInternalVertsLoop p) s s' t ∧
        t ≤ (markActCost p (List.finRange p) + 30) * ks.length +
          23 * p * (encInternalSlice x.W ks).length + 3 ∧
        (s'.arrs outArr).length = 2 + 2 * K + p * x.n ∧
        (∀ gamma : Fin p,
          IsBitSlice (s'.arrs outArr) (2 + 2 * K + gamma.1 * x.n)
            (S gamma ∪ internalVertsSliceUnion hp x gamma ks)) ∧
        (∀ i : ℕ, i < 2 + 2 * K → (s'.arrs outArr)[i]? = (s.arrs outArr)[i]?)
  | [], _, pre, suf, S, s, _, _, _, _, _, hr1, hout_len, hS => by
    have h0_w := hw.hw0
    have hcond : (Expr.op .lt (.const 0) (.reg 1)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, hout_len, ?_, fun _ _ => rfl⟩
    intro gamma
    simp [internalVertsSliceUnion, hS gamma]
  | k :: rest, hnd, pre, suf, S, s, hs, hsplit, hr4, hr5, hconsec, hr1, hout_len, hS => by
    intro K
    rcases List.nodup_cons.mp hnd with ⟨_, hnd_rest⟩
    have h0_w := hw.hw0
    have hw1 := hw.hw1
    have hsplit_k :
        encAlg74In x =
          pre ++ ((x.W.internalVerts k).length :: (x.W.internalVerts k).map Fin.val ++
            (encInternalSlice x.W rest ++ suf)) := by
      simpa [encInternalSlice_cons, List.append_assoc] using hsplit
    have hlen_in_eq :
        (encAlg74In x).length =
          pre.length + 1 + (x.W.internalVerts k).length +
            (encInternalSlice x.W rest).length + suf.length := by
      rw [hsplit_k]
      simp only [List.length_append, List.length_cons, List.length_map]
      omega
    have hpos_w : pre.length < 2 ^ w := by have := hw.hin_w; omega
    have hpos1_w : pre.length + 1 < 2 ^ w := by have := hw.hin_w; omega
    have hlenk_w : (x.W.internalVerts k).length < 2 ^ w := by have := hw.hin_w; omega
    have hpos_next_w : (pre.length + 1) + (x.W.internalVerts k).length < 2 ^ w := by
      have := hw.hin_w; omega
    have hrem_w : rest.length + 1 < 2 ^ w := by
      have := k.2; have := hw.hloc_w
      have hrest := length_le_length_encInternalSlice x.W rest
      have := hw.hin_w; omega
    have hrem0_w : rest.length < 2 ^ w := by omega
    have hr5_k : s.regs 5 = k.1 := hr5 k rfl
    have hk_lt : k.1 < (elemWallEdges x.h).length := k.2
    have hk_w : k.1 < 2 ^ w := by have := hw.hloc_w; omega
    have hk1_w : k.1 + 1 < 2 ^ w := by have := hw.hloc_w; omega
    have hr1_eq : s.regs 1 = rest.length + 1 := by simpa using hr1
    have hcond : (Expr.op .lt (.const 0) (.reg 1)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1_eq, h0_w, hw1, hrem_w]
    let e := (elemWallEdges x.h)[k.1]'k.2
    have hu1_w : e.1.1 < 2 ^ w := by have := e.1.2; have := hw.hloc_w; omega
    have hu2_w : e.2.1 < 2 ^ w := by have := e.2.2; have := hw.hloc_w; omega
    let s₁ := s.setReg 6 e.1.1
    have hex₁ : Exec w (.assign 6 (.read edgeU1Arr (.reg 5))) s s₁ 3 := by
      have hlt_u1 : k.1 < (s.arrs edgeU1Arr).length := by rw [hs.hu1_len]; exact hk_lt
      exact .assign (eval_read (eval_reg hr5_k hk_w) hlt_u1 (hs.hu1_val k) hu1_w)
    let s₂ := s₁.setReg 7 e.2.1
    have hex₂ : Exec w (.assign 7 (.read edgeU2Arr (.reg 5))) s₁ s₂ 3 := by
      have hlt_u2 : k.1 < (s₁.arrs edgeU2Arr).length := by simp [s₁, hs.hu2_len, hk_lt]
      exact .assign (eval_read (eval_reg (by simp [s₁, hr5_k]) hk_w) hlt_u2 (hs.hu2_val k) hu2_w)
    have hpos_lt : pre.length < (s₂.arrs inArr).length := by
      simp [s₂, s₁, hs.hin]; omega
    have hget_len : (s₂.arrs inArr)[pre.length]'hpos_lt = (x.W.internalVerts k).length := by
      simp only [s₂, s₁, State.setReg_arrs, hs.hin, hsplit_k, List.cons_append]
      exact getElem_append_cons pre (x.W.internalVerts k).length _ pre.length rfl
    let s₃ := s₂.setReg 10 (x.W.internalVerts k).length
    have hex₃ : Exec w (.assign 10 (.read inArr (.reg 4))) s₂ s₃ 3 :=
      .assign (eval_read (eval_reg (by simp [s₂, s₁, hr4]) hpos_w) hpos_lt hget_len hlenk_w)
    have hs₃ : RoutingStateHolds (by omega : 0 < p) x s₃ :=
      hs.of_preserve (fun reg hreg => by
        have h6 : reg ≠ 6 := by dsimp [Reg] at *; omega
        have h7 : reg ≠ 7 := by dsimp [Reg] at *; omega
        have h10 : reg ≠ 10 := by dsimp [Reg] at *; omega
        simp [s₃, s₂, s₁, h6, h7, h10])
      (fun _ _ => rfl)
    rcases markInternalEdgeAllColorsCmd_exec hp x hh1 hw k pre
        (encInternalSlice x.W rest ++ suf) (List.finRange p) (List.nodup_finRange p) S hs₃
        hsplit_k (by simp [s₃, s₂, s₁, hr4]) (by simp [s₃, s₂, s₁, hr5_k])
        (by simp [s₃, s₂, s₁, e]) (by simp [s₃, s₂, e]) (by simp [s₃])
        (by simp [s₃, s₂, s₁, hout_len])
        (fun g => by simpa [s₃, s₂, s₁] using hS g) with
      ⟨s₄, t₄, hex₄, ht₄, hout_len4, hS₄_raw, hprefix4, hregs4, harrs4⟩
    simp only [List.length_finRange] at ht₄
    let S₄ : Fin p → Finset (Fin x.n) := fun g =>
      S g ∪ (if wallEdgeActive hp x g k then (x.W.internalVerts k).toFinset else ∅)
    have hS₄ : ∀ g : Fin p, IsBitSlice (s₄.arrs outArr) (2 + 2 * K + g.1 * x.n) (S₄ g) := by
      intro g
      have h := hS₄_raw g
      simp only [List.mem_finRange, true_and] at h
      dsimp [S₄]
      by_cases hact : wallEdgeActive hp x g k <;> simp [hact] at h ⊢ <;> exact h
    have hr4_4 : s₄.regs 4 = pre.length := by
      rw [hregs4 4 (by decide) (by decide) (by decide)]; simp [s₃, s₂, s₁, hr4]
    have hr5_4 : s₄.regs 5 = k.1 := by
      rw [hregs4 5 (by decide) (by decide) (by decide)]; simp [s₃, s₂, s₁, hr5_k]
    have hr10_4 : s₄.regs 10 = (x.W.internalVerts k).length := by
      rw [hregs4 10 (by decide) (by decide) (by decide)]; simp [s₃]
    have hr1_4 : s₄.regs 1 = rest.length + 1 := by
      rw [hregs4 1 (by decide) (by decide) (by decide)]; simp [s₃, s₂, s₁, hr1_eq]
    let pre₁ := pre ++ ((x.W.internalVerts k).length :: (x.W.internalVerts k).map Fin.val)
    have hpre1_len : pre₁.length = (pre.length + 1) + (x.W.internalVerts k).length := by
      simp [pre₁]; omega
    let s₅ := s₄.setReg 4 pre₁.length
    have hex₅ : Exec w (.assign 4 (.op .add (.op .add (.reg 4) (.const 1)) (.reg 10))) s₄ s₅ 6 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_4, hr10_4,
        hpos_w, hw1, hpos1_w, hlenk_w, hpre1_len, hpos_next_w])
    let s₆ := s₅.setReg 5 (k.1 + 1)
    have hex₆ : Exec w (.assign 5 (.op .add (.reg 5) (.const 1))) s₅ s₆ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₅, hr5_4, hk_w, hw1, hk1_w])
    let s₇ := s₆.setReg 1 rest.length
    have hex₇ : Exec w (.assign 1 (.op .sub (.reg 1) (.const 1))) s₆ s₇ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₆, s₅, hr1_4,
        hrem_w, hw1, hrem0_w])
    have hex_body : Exec w (markWallInternalVertsBody p) s s₇
        (3 + (3 + (3 + (t₄ + (6 + (4 + 4)))))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇)))))
    have hs₇ : RoutingStateHolds (by omega : 0 < p) x s₇ :=
      hs₃.of_preserve (fun reg hreg => by
        have h1 : reg ≠ 1 := by dsimp [Reg] at *; omega
        have h4 : reg ≠ 4 := by dsimp [Reg] at *; omega
        have h5 : reg ≠ 5 := by dsimp [Reg] at *; omega
        have h8 : reg ≠ 8 := by dsimp [Reg] at *; omega
        have h9 : reg ≠ 9 := by dsimp [Reg] at *; omega
        have h11 : reg ≠ 11 := by dsimp [Reg] at *; omega
        simp [s₇, s₆, s₅, h1, h4, h5, hregs4 reg h8 h9 h11])
      (fun a ha => by simp [s₇, s₆, s₅, harrs4 a ha])
    have hsplit_rest : encAlg74In x = pre₁ ++ (encInternalSlice x.W rest ++ suf) := by
      simpa [pre₁, List.append_assoc] using hsplit_k
    have hr5_7 : ∀ k_head, rest.head? = some k_head → s₇.regs 5 = k_head.1 := by
      intro k_head hhead
      cases rest with
      | nil => simp at hhead
      | cons k' rest' =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        have hc0 := hconsec 0 (by simp)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hc0
        simp [s₇, s₆, hc0]
    have hconsec_rest : ∀ i (hi : i + 1 < rest.length),
        (rest[i + 1]'hi).1 = (rest[i]'(by omega)).1 + 1 := by
      intro i hi
      have hc := hconsec (i + 1) (by simp; omega)
      rwa [List.getElem_cons_succ, List.getElem_cons_succ] at hc
    rcases markWallInternalVertsLoop_exec hp x hh1 hw rest hnd_rest pre₁ suf S₄ hs₇
        hsplit_rest (by simp [s₇, s₆, s₅]) hr5_7 hconsec_rest (by simp [s₇])
        (by simpa [s₇, s₆, s₅] using hout_len4)
        (fun g => by simpa [s₇, s₆, s₅] using hS₄ g) with
      ⟨s', t_rest, hex_rest, ht_rest, hout_len', hS', hprefix'⟩
    have hslice_len :
        (encInternalSlice x.W (k :: rest)).length =
          1 + (x.W.internalVerts k).length + (encInternalSlice x.W rest).length := by
      simp [encInternalSlice_cons]; omega
    refine ⟨s', 3 + (3 + (3 + (3 + (t₄ + (6 + (4 + 4)))))) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      ?_, hout_len', ?_,
      fun i hi => by rw [hprefix' i hi]; simpa [s₇, s₆, s₅, s₃, s₂, s₁] using hprefix4 i hi⟩
    · rw [hslice_len, List.length_cons, Nat.mul_succ]
      have hmul :
          23 * p * (1 + (x.W.internalVerts k).length + (encInternalSlice x.W rest).length) =
            23 * p + 23 * p * (x.W.internalVerts k).length +
              23 * p * (encInternalSlice x.W rest).length := by ring
      omega
    · intro gamma
      have h := hS' gamma
      dsimp [S₄] at h
      rwa [Finset.union_assoc, ← internalVertsSliceUnion] at h

private theorem finRange_head?_val {n : ℕ} {k : Fin n}
    (h : (List.finRange n).head? = some k) : k.1 = 0 := by
  cases n with
  | zero => exact k.elim0
  | succ m =>
    rw [List.finRange_succ, List.head?_cons, Option.some.injEq] at h
    subst h
    rfl

/-- Step 5c (`markWallInternalVertsCmd p`): sets `r_5 = 0`, `r_1 = r_13`, and runs
`markWallInternalVertsLoop p`. -/
def markWallInternalVertsCmd (p : ℕ) : Cmd :=
  .seq (.assign 5 (.const 0))
    (.seq (.assign 1 (.reg 13))
      (markWallInternalVertsLoop p))

theorem markWallInternalVertsCmd_exec {w p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p))
    (hh1 : 1 ≤ x.h)
    (hw : Section5WordBounds w p (alg74LiftRadius p) x)
    (S : Fin p → Finset (Fin x.n))
    {s : State} (hs : RoutingStateHolds (by omega : 0 < p) x s)
    (hr4 : s.regs 4 = 2 + 3 * x.G.numActivePairs + 3 + elemWallNumVerts x.h)
    (hout_len : (s.arrs outArr).length = 2 + 2 * (completeGraphEdges p).length + p * x.n)
    (hS : ∀ gamma : Fin p,
      IsBitSlice (s.arrs outArr) (2 + 2 * (completeGraphEdges p).length + gamma.1 * x.n)
        (S gamma)) :
    let K := (completeGraphEdges p).length
    let E_J := (elemWallEdges x.h).length
    ∃ s' t,
      Exec w (markWallInternalVertsCmd p) s s' t ∧
      t ≤ (markActCost p (List.finRange p) + 30) * E_J +
        23 * p * x.W.encList.length + 10 ∧
      (s'.arrs outArr).length = 2 + 2 * K + p * x.n ∧
      (∀ gamma : Fin p,
        IsBitSlice (s'.arrs outArr) (2 + 2 * K + gamma.1 * x.n)
          (S gamma ∪ internalVertsSliceUnion hp x gamma (List.finRange E_J))) ∧
      (∀ i : ℕ, i < 2 + 2 * K → (s'.arrs outArr)[i]? = (s.arrs outArr)[i]?) := by
  intro K E_J
  let V_J := elemWallNumVerts x.h
  have h0_w := hw.hw0
  have hEJ_w : E_J < 2 ^ w := by dsimp [E_J]; have := hw.hloc_w; omega
  let s₁ := s.setReg 5 0
  have hex₁ : Exec w (.assign 5 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₁.setReg 1 E_J
  have hex₂ : Exec w (.assign 1 (.reg 13)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₁, hs.hr13, hEJ_w, E_J])
  have hs₂ : RoutingStateHolds (by omega : 0 < p) x s₂ :=
    hs.of_preserve (fun reg hreg => by
      have h1 : reg ≠ 1 := by dsimp [Reg] at *; omega
      have h5 : reg ≠ 5 := by dsimp [Reg] at *; omega
      simp [s₂, s₁, h1, h5])
    (fun _ _ => rfl)
  let pre :=
    x.G.enc ++
      ([x.h, V_J, E_J] ++ (List.finRange V_J).map (fun u => (x.W.branchVert u).1))
  have hpre_len : pre.length = 2 + 3 * x.G.numActivePairs + 3 + V_J := by
    simp [pre, MultiDigraph.length_enc]; omega
  have hsplit :
      encAlg74In x =
        pre ++ (encInternalSlice x.W (List.finRange E_J) ++ encHPaths x.paths) := by
    unfold encAlg74In
    rw [wallEncList_eq_append_encInternalSlice]
    dsimp [pre, V_J, E_J]
    simp [List.append_assoc]
  have hr4_2 : s₂.regs 4 = pre.length := by simp [s₂, s₁, hr4, hpre_len, V_J]
  have hr5_2 : ∀ k_head, (List.finRange E_J).head? = some k_head → s₂.regs 5 = k_head.1 := by
    intro k_head hhead
    rw [finRange_head?_val hhead]
    simp [s₂, s₁]
  have hconsec : ∀ i (hi : i + 1 < (List.finRange E_J).length),
      ((List.finRange E_J)[i + 1]'hi).1 = ((List.finRange E_J)[i]'(by omega)).1 + 1 := by
    intro i _
    simp
  rcases markWallInternalVertsLoop_exec hp x hh1 hw (List.finRange E_J) (List.nodup_finRange E_J)
      pre (encHPaths x.paths) S hs₂ hsplit hr4_2 hr5_2 hconsec
      (by simp [s₂]) (by simp [s₂, s₁, hout_len])
      (fun gamma => by simpa [s₂, s₁] using hS gamma) with
    ⟨s', t_loop, hex₃, ht_loop, hout_len', hS', hprefix'⟩
  have hslice_le : (encInternalSlice x.W (List.finRange E_J)).length ≤ x.W.encList.length := by
    rw [wallEncList_eq_append_encInternalSlice]
    dsimp [E_J]
    simp only [List.length_append]
    omega
  refine ⟨s', 2 + (2 + t_loop), .seq hex₁ (.seq hex₂ hex₃), ?_, hout_len', hS',
    fun i hi => by rw [hprefix' i hi]; rfl⟩
  simp only [List.length_finRange] at ht_loop
  have hmul :
      23 * p * (encInternalSlice x.W (List.finRange E_J)).length ≤
        23 * p * x.W.encList.length :=
    Nat.mul_le_mul_left (23 * p) hslice_le
  omega

/-! #### Sub-step 5d: Final Assembly (`alg74Prog` and `gm13_algorithm_7_4`) -/

theorem pathBranchUnion_union_wallVertBranchSet_eq_modelBranchSet {p r : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p r) (gamma : Fin p) :
    pathBranchUnion x (List.finRange (completeGraphEdges p).length) gamma ∪
      wallVertBranchSet hp x gamma =
    modelBranchSet hp x gamma := by
  ext v
  rw [mem_modelBranchSet_iff]
  simp only [pathBranchUnion, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    List.mem_toFinset, List.mem_finRange, true_and]
  exact or_comm

theorem outArr_eq_encUnderlyingGraphModel {p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p))
    (arr : List ℕ)
    (hlen : arr.length = 2 + 2 * (completeGraphEdges p).length + p * x.n)
    (h0 : arr[0]? = some p)
    (h1 : arr[1]? = some (completeGraphEdges p).length)
    (hedges : ∀ e : Fin (completeGraphEdges p).length,
      arr[2 + 2 * e.1]? = some (alg74EdgePair x e).1.1 ∧
      arr[2 + 2 * e.1 + 1]? = some (alg74EdgePair x e).2.1)
    (hverts : ∀ gamma : Fin p,
      IsBitSlice arr (2 + 2 * (completeGraphEdges p).length + gamma.1 * x.n)
        (modelBranchSet hp x gamma)) :
    arr = encUnderlyingGraphModel (alg74UnderlyingModel hp x) := by
  let K := (completeGraphEdges p).length
  let edgeList :=
    (List.finRange K).flatMap (fun e =>
      [(alg74EdgePair x e).1.1, (alg74EdgePair x e).2.1])
  let vertList :=
    (List.finRange p).flatMap (fun gamma =>
      bitSetList (modelBranchSet hp x gamma))
  have hedge_len : edgeList.length = 2 * K := by
    have h := length_flatMap_of_const_len (List.finRange K) 2
      (fun e => [(alg74EdgePair x e).1.1, (alg74EdgePair x e).2.1]) (fun _ _ => rfl)
    dsimp [edgeList]
    rw [h, List.length_finRange, Nat.mul_comm]
  have hvert_len : vertList.length = p * x.n := by
    have h := length_flatMap_of_const_len (List.finRange p) x.n
      (fun gamma => bitSetList (modelBranchSet hp x gamma))
      (fun gamma _ => length_bitSetList (modelBranchSet hp x gamma))
    dsimp [vertList]
    rw [h, List.length_finRange]
  rw [encUnderlyingGraphModel_alg74 hp x]
  apply List.ext_getElem
  · rw [List.length_append, List.length_append, hvert_len, hedge_len, hlen]
    simp [K]
  · intro i hi₁ hi₂
    by_cases hi2 : i < 2
    · interval_cases i
      · have h0' : arr[0]'hi₁ = p :=
          Option.some.inj (by rw [← List.getElem?_eq_getElem hi₁, h0])
        simp [h0']
      · have h1' : arr[1]'hi₁ = K :=
          Option.some.inj (by rw [← List.getElem?_eq_getElem hi₁, h1])
        simp [h1', K]
    · by_cases hi_edge : i < 2 + 2 * K
      · have h_sub_lt : i - 2 < K * 2 := by omega
        let q := (i - 2) / 2
        let r := (i - 2) % 2
        have hq_lt : q < (List.finRange K).length := by
          simp only [List.length_finRange]
          omega
        have hr_lt : r < 2 := by omega
        let e : Fin K := ⟨q, by omega⟩
        have hfin_q : (List.finRange K)[q]'hq_lt = e := by simp [e]
        have hflat := getElem_flatMap_of_const_len (List.finRange K) 2
          (fun e' => [(alg74EdgePair x e').1.1, (alg74EdgePair x e').2.1])
          (fun _ _ => rfl) q hq_lt r hr_lt
        have hget_rhs :
            (([p, K] ++ edgeList) ++ vertList)[i]'hi₂ =
              ([(alg74EdgePair x e).1.1, (alg74EdgePair x e).2.1])[r]'hr_lt := by
          have hi_lt_left : i < ([p, K] ++ edgeList).length := by
            simp [hedge_len]; omega
          rw [List.getElem_append_left hi_lt_left,
            List.getElem_append_right (by simp; omega : ([p, K] : List ℕ).length ≤ i)]
          have hsub : i - ([p, K] : List ℕ).length = q * 2 + r := by
            dsimp [q, r]
            have hdiv := Nat.div_add_mod (i - 2) 2
            omega
          rw [getElem_congr_idx _ hsub]
          simpa [edgeList, hfin_q] using hflat
        rw [hget_rhs]
        rcases (show r = 0 ∨ r = 1 by omega) with hr0 | hr1
        · have hi_eq : i = 2 + 2 * e.1 := by dsimp [e, q, r] at hr0 ⊢; omega
          have he0 : arr[i]'hi₁ = (alg74EdgePair x e).1.1 :=
            Option.some.inj (by rw [← List.getElem?_eq_getElem hi₁, hi_eq, (hedges e).1])
          simp [hr0, he0]
        · have hi_eq : i = 2 + 2 * e.1 + 1 := by dsimp [e, q, r] at hr1 ⊢; omega
          have he1 : arr[i]'hi₁ = (alg74EdgePair x e).2.1 :=
            Option.some.inj (by rw [← List.getElem?_eq_getElem hi₁, hi_eq, (hedges e).2])
          simp [hr1, he1]
      · have h_sub_lt : i - (2 + 2 * K) < p * x.n := by omega
        have hn_pos : 0 < x.n := by
          by_contra hle
          have hn0 : x.n = 0 := by omega
          rw [hn0] at h_sub_lt
          omega
        let q := (i - (2 + 2 * K)) / x.n
        let r := (i - (2 + 2 * K)) % x.n
        have hq_lt : q < p :=
          (Nat.div_lt_iff_lt_mul hn_pos).mpr h_sub_lt
        have hr_lt : r < x.n := Nat.mod_lt _ hn_pos
        let gamma : Fin p := ⟨q, hq_lt⟩
        let v : Fin x.n := ⟨r, hr_lt⟩
        have hq_fin_lt : q < (List.finRange p).length := by simpa using hq_lt
        have hfin_q : (List.finRange p)[q]'hq_fin_lt = gamma := by simp [gamma]
        have hflat := getElem_flatMap_of_const_len (List.finRange p) x.n
          (fun g => bitSetList (modelBranchSet hp x g))
          (fun g _ => length_bitSetList (modelBranchSet hp x g))
          q hq_fin_lt r hr_lt
        have hget_rhs :
            (([p, K] ++ edgeList) ++ vertList)[i]'hi₂ =
              (bitSetList (modelBranchSet hp x gamma))[r]'(by rw [length_bitSetList]; exact hr_lt) := by
          have hi_ge_left : ([p, K] ++ edgeList).length ≤ i := by
            simp [hedge_len]; omega
          have hlen_left : ([p, K] ++ edgeList).length = 2 + 2 * K := by
            simp [hedge_len]; omega
          rw [List.getElem_append_right hi_ge_left]
          have hsub : i - ([p, K] ++ edgeList).length = q * x.n + r := by
            rw [hlen_left]
            dsimp [q, r]
            have hdiv := Nat.div_add_mod (i - (2 + 2 * K)) x.n
            rw [Nat.mul_comm] at hdiv
            omega
          rw [getElem_congr_idx _ hsub]
          simpa [vertList, hfin_q] using hflat
        rw [hget_rhs, getElem_bitSetList (modelBranchSet hp x gamma) v]
        have hi_eq : i = 2 + 2 * K + gamma.1 * x.n + v.1 := by
          dsimp [gamma, v, q, r]
          have hdiv := Nat.div_add_mod (i - (2 + 2 * K)) x.n
          rw [Nat.mul_comm] at hdiv
          omega
        rcases hverts gamma with ⟨_, hbit⟩
        simpa [hi_eq] using hbit v

/-- Complete height-independent Word RAM program for Graph Minors XIII, (7.4) depending only on `p`. -/
def alg74Prog (p : ℕ) : Cmd :=
  let K := (completeGraphEdges p).length
  .seq (initCmd p)
    (.seq scanWallCmd
      (.seq buildWallEdgesCmd
        (.seq (processPathsCmd p (List.finRange K))
          (.seq (routeTerminalsCmd p)
            (.seq (markWallBranchVertsCmd p)
              (markWallInternalVertsCmd p))))))

theorem alg74Prog_exec {w p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p))
    (hw : Section5WordBounds w p (alg74LiftRadius p) x)
    {s : State} (hin : s.arrs inArr = encAlg74In x) :
    let K := (completeGraphEdges p).length
    let V_J := elemWallNumVerts x.h
    let E_J := (elemWallEdges x.h).length
    ∃ s' t,
      Exec w (alg74Prog p) s s' t ∧
      t ≤ ((p + 1) * x.n + 2 * E_J + 2 * K + 60) +
        (22 * V_J + 26 * E_J + 17 * x.W.encList.length + 25) +
        (95 * V_J + 10) +
        ((30 * x.G.numActivePairs + 23 * x.n + 65) * K + 1) +
        (routeTerminalsCmd p).maxTime +
        (((markWallBranchVertsBody p).maxTime + 3) * V_J + 15) +
        ((markActCost p (List.finRange p) + 30) * E_J +
          23 * p * x.W.encList.length + 10) ∧
      s'.arrs outArr = encUnderlyingGraphModel (alg74UnderlyingModel hp x) := by
  intro K V_J E_J
  have hh1 : 1 ≤ x.h := by have := x.hW_valid.1; omega
  have hVJ_w : V_J < 2 ^ w := by dsimp [V_J]; have := hw.hloc_w; omega
  have hEJ_w : E_J < 2 ^ w := by dsimp [E_J]; have := hw.hloc_w; omega
  rcases initCmd_exec x hw.hw3 hw.hp_w hw.hK_w hw.hn_w hw.h2h2_w hVJ_w hEJ_w
      hw.hin_w hw.hout_w hin with
    ⟨s₁, t₁, hex₁, ht₁, hin₁, hr0_1, hr1_1, hr2_1, hr3_1, hr12_1, hr13_1, hr14_1,
      hout_len1, hout0_1, hout1_1, hS₁, hloc_len1, hu1_len1, hu2_len1⟩
  rcases scanWallCmd_exec x hw.hw3 hw.hn_w hw.hloc_w hw.hin_w
      hin₁ hloc_len1 hr2_1 hr12_1 hr13_1 with
    ⟨s₂, t₂, hex₂, ht₂, hr4_2, hloc_len2, hloc_val2, hregs2, harrs2⟩
  have hr12_2 : s₂.regs 12 = V_J := by
    rw [hregs2 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hr12_1]
  have hr14_2 : s₂.regs 14 = 2 * x.h + 2 := by
    rw [hregs2 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hr14_1]
  have hu1_len2 : (s₂.arrs edgeU1Arr).length = E_J := by
    rw [harrs2 edgeU1Arr (by decide), hu1_len1]
  have hu2_len2 : (s₂.arrs edgeU2Arr).length = E_J := by
    rw [harrs2 edgeU2Arr (by decide), hu2_len1]
  rcases buildWallEdgesCmd_exec hw.hw3 hw.hVJW_w hEJ_w hr12_2 hr14_2 hu1_len2 hu2_len2 with
    ⟨s₃, t₃, hex₃, ht₃, hu1_len3, hu2_len3, hedges3, hregs3, harrs3⟩
  have hin₃ : s₃.arrs inArr = encAlg74In x := by
    rw [harrs3 inArr (by decide) (by decide), harrs2 inArr (by decide), hin₁]
  have hsplit₃ :
      encAlg74In x =
        (x.G.enc ++ x.W.encList) ++ (encHPathsSlice x (List.finRange K) ++ []) := by
    unfold encAlg74In
    rw [encHPathsSlice_finRange, List.append_nil]
  have hr0_3 : s₃.regs 0 = x.n := by
    rw [hregs3 0 (by decide) (by decide) (by decide) (by decide) (by decide),
      hregs2 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hr0_1]
  have hr1_3 : s₃.regs 1 = x.G.numActivePairs := by
    rw [hregs3 1 (by decide) (by decide) (by decide) (by decide) (by decide),
      hregs2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hr1_1]
  have hr2_3 : s₃.regs 2 = 2 + 3 * x.G.numActivePairs := by
    rw [hregs3 2 (by decide) (by decide) (by decide) (by decide) (by decide),
      hregs2 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hr2_1]
  have hr3_3 : s₃.regs 3 = x.h := by
    rw [hregs3 3 (by decide) (by decide) (by decide) (by decide) (by decide),
      hregs2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hr3_1]
  have hr4_3 : s₃.regs 4 = (x.G.enc ++ x.W.encList).length := by
    rw [hregs3 4 (by decide) (by decide) (by decide) (by decide) (by decide), hr4_2]
  have hout_s3 : s₃.arrs outArr = s₁.arrs outArr := by
    rw [harrs3 outArr (by decide) (by decide), harrs2 outArr (by decide)]
  have hout_len3 : (s₃.arrs outArr).length = 2 + 2 * K + p * x.n := by
    rw [hout_s3, hout_len1]
  have hS₃ : ∀ gamma : Fin p,
      IsBitSlice (s₃.arrs outArr) (2 + 2 * K + gamma.1 * x.n) (∅ : Finset (Fin x.n)) := by
    intro gamma
    rw [hout_s3]
    exact hS₁ gamma
  rcases processPathsCmd_exec x hw.hw3 hw.hp_w hw.hn_w hw.hm_w hw.hin_w hw.hout_w
      (List.finRange K) (List.nodup_finRange K) (x.G.enc ++ x.W.encList) [] (fun _ => ∅)
      hin₃ hsplit₃ hr0_3 hr1_3 hr4_3 hout_len3 hS₃ with
    ⟨s₄, t₄, hex₄, ht₄, hin₄, hout_len4, hr0_4, _, hr2_4_eq, hr3_4_eq,
      hpaths_done4, hregs4, hout_prefix4, hS₄_raw, harrs4⟩
  simp only [List.length_finRange] at ht₄
  have hr2_4 : s₄.regs 2 = 2 + 3 * x.G.numActivePairs := hr2_4_eq.trans hr2_3
  have hr3_4 : s₄.regs 3 = x.h := hr3_4_eq.trans hr3_3
  have hr12_4 : s₄.regs 12 = V_J := by
    rw [hregs4 12 (by decide) (fun e _ => ⟨by dsimp [Reg]; omega, by dsimp [Reg]; omega⟩),
      hregs3 12 (by decide) (by decide) (by decide) (by decide) (by decide), hr12_2]
  have hr13_4 : s₄.regs 13 = E_J := by
    rw [hregs4 13 (by decide) (fun e _ => ⟨by dsimp [Reg]; omega, by dsimp [Reg]; omega⟩),
      hregs3 13 (by decide) (by decide) (by decide) (by decide) (by decide),
      hregs2 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hr13_1]
  have hr14_4 : s₄.regs 14 = 2 * x.h + 2 := by
    rw [hregs4 14 (by decide) (fun e _ => ⟨by dsimp [Reg]; omega, by dsimp [Reg]; omega⟩),
      hregs3 14 (by decide) (by decide) (by decide) (by decide) (by decide), hr14_2]
  have hloc_s4 : s₄.arrs locArr = s₂.arrs locArr := by
    rw [harrs4 locArr (by decide), harrs3 locArr (by decide) (by decide)]
  have hloc_len4 : (s₄.arrs locArr).length = x.n := by
    rw [hloc_s4, hloc_len2]
  have hloc_val4 : ∀ v ∈ x.W.vertexFinset,
      (s₄.arrs locArr)[v.1]'(by rw [hloc_len4]; exact v.2) = termLocCode x.W v := by
    intro v hv
    apply getElem_of_getElem?
    rw [hloc_s4]
    exact hloc_val2 v hv
  have hu1_s4 : s₄.arrs edgeU1Arr = s₃.arrs edgeU1Arr := harrs4 edgeU1Arr (by decide)
  have hu2_s4 : s₄.arrs edgeU2Arr = s₃.arrs edgeU2Arr := harrs4 edgeU2Arr (by decide)
  have hu1_len4 : (s₄.arrs edgeU1Arr).length = E_J := by rw [hu1_s4, hu1_len3]
  have hu2_len4 : (s₄.arrs edgeU2Arr).length = E_J := by rw [hu2_s4, hu2_len3]
  have hu1_val4 : ∀ k : Fin E_J,
      (s₄.arrs edgeU1Arr)[k.1]'(by rw [hu1_len4]; exact k.2) = ((elemWallEdges x.h)[k.1]'k.2).1.1 := by
    intro k
    apply getElem_of_getElem?
    rw [hu1_s4]
    exact (hedges3 k).1
  have hu2_val4 : ∀ k : Fin E_J,
      (s₄.arrs edgeU2Arr)[k.1]'(by rw [hu2_len4]; exact k.2) = ((elemWallEdges x.h)[k.1]'k.2).2.1 := by
    intro k
    apply getElem_of_getElem?
    rw [hu2_s4]
    exact (hedges3 k).2
  have hterm_edges4 : ∀ e : Fin K,
      s₄.regs (20 + 2 * e.1) = (alg74TermVert x (edgeStartTerm e)).1 ∧
      s₄.regs (20 + 2 * e.1 + 1) = (alg74TermVert x (edgeEndTerm e)).1 := by
    intro e
    have he := hpaths_done4 e (List.mem_finRange e)
    exact ⟨he.1, he.2.1⟩
  have hout0_4 : (s₄.arrs outArr)[0]? = some p := by
    rw [hout_prefix4 0 (by omega) (fun e _ => ⟨by omega, by omega⟩), hout_s3, hout0_1]
  have hout1_4 : (s₄.arrs outArr)[1]? = some K := by
    rw [hout_prefix4 1 (by omega) (fun e _ => ⟨by omega, by omega⟩), hout_s3, hout1_1]
  have hedges_out4 : ∀ e : Fin K,
      (s₄.arrs outArr)[2 + 2 * e.1]? = some (alg74EdgePair x e).1.1 ∧
      (s₄.arrs outArr)[2 + 2 * e.1 + 1]? = some (alg74EdgePair x e).2.1 := by
    intro e
    have he := hpaths_done4 e (List.mem_finRange e)
    exact ⟨he.2.2.1, he.2.2.2⟩
  let S₄ : Fin p → Finset (Fin x.n) := fun gamma => pathBranchUnion x (List.finRange K) gamma
  have hS₄ : ∀ gamma : Fin p, IsBitSlice (s₄.arrs outArr) (2 + 2 * K + gamma.1 * x.n) (S₄ gamma) := by
    intro gamma
    simpa [S₄] using hS₄_raw gamma
  rcases routeTerminalsCmd_exec (by omega : 0 < p) x hh1 hw.hn_w hw.hloc_w hw.hroute_w s₄
      hr3_4 hr12_4 hr14_4 hloc_len4 hloc_val4 hu1_len4 hu1_val4 hterm_edges4 with
    ⟨s₅, t₅, hex₅, ht₅, harrs5, hregs5, hr15_5, hr16_5, hr17_5, hr18_5, hr19_5,
      hterm_cy5, hperm5, hslots5, hsafe5⟩
  have hs₅ : RoutingStateHolds (by omega : 0 < p) x s₅ := by
    refine
      { hin := by rw [harrs5, hin₄]
        hr0 := by rw [hregs5 0 (Or.inl (by decide)), hr0_4]
        hr2 := by rw [hregs5 2 (Or.inl (by decide)), hr2_4]
        hr3 := by rw [hregs5 3 (Or.inl (by decide)), hr3_4]
        hr12 := by rw [hregs5 12 (Or.inr (Or.inl rfl)), hr12_4]
        hr13 := by rw [hregs5 13 (Or.inr (Or.inr (Or.inl rfl))), hr13_4]
        hr14 := by rw [hregs5 14 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hr14_4]
        hloc_len := by rw [harrs5, hloc_len4]
        hloc_val := fun v hv => by simp [harrs5, hloc_val4 v hv]
        hu1_len := by rw [harrs5, hu1_len4]
        hu1_val := fun k => by simp [harrs5, hu1_val4 k]
        hu2_len := by rw [harrs5, hu2_len4]
        hu2_val := fun k => by simp [harrs5, hu2_val4 k]
        hterm_edges := fun e => by
          have he : e.1 < K := e.2
          have h0 : 20 ≤ 20 + 2 * e.1 ∧ 20 + 2 * e.1 < 20 + alg74NumTerms p := by
            dsimp [alg74NumTerms, K] at *
            omega
          have h1 : 20 ≤ 20 + 2 * e.1 + 1 ∧ 20 + 2 * e.1 + 1 < 20 + alg74NumTerms p := by
            dsimp [alg74NumTerms, K] at *
            omega
          rw [hregs5 (20 + 2 * e.1) (Or.inr (Or.inr (Or.inr (Or.inr h0)))),
            hregs5 (20 + 2 * e.1 + 1) (Or.inr (Or.inr (Or.inr (Or.inr h1))))]
          exact hterm_edges4 e
        hr15 := hr15_5
        hr16 := hr16_5
        hr17 := hr17_5
        hr18 := hr18_5
        hr19 := hr19_5
        htermC := hterm_cy5
        hperm := hperm5
        hslots := hslots5
        hsafe := hsafe5 }
  have hout_len5 : (s₅.arrs outArr).length = 2 + 2 * K + p * x.n := by
    rw [harrs5, hout_len4]
  have hS₅ : ∀ gamma : Fin p, IsBitSlice (s₅.arrs outArr) (2 + 2 * K + gamma.1 * x.n) (S₄ gamma) := by
    intro gamma
    rw [harrs5]
    exact hS₄ gamma
  rcases markWallBranchVertsCmd_exec hp x hh1 hw S₄ hs₅ hout_len5 hS₅ with
    ⟨s₆, t₆, hex₆, ht₆, hs₆, hr4_6, hout_len6, hS₆, hprefix6, _⟩
  let S₆ : Fin p → Finset (Fin x.n) := fun gamma => S₄ gamma ∪ branchVertsFrom hp x gamma 0
  rcases markWallInternalVertsCmd_exec hp x hh1 hw S₆ hs₆ hr4_6 hout_len6 hS₆ with
    ⟨s₇, t₇, hex₇, ht₇, hout_len7, hS₇, hprefix7⟩
  have hex_all :
      Exec w (alg74Prog p) s s₇
        (t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + t₇)))))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇)))))
  have hprefix_74 : ∀ i : ℕ, i < 2 + 2 * K → (s₇.arrs outArr)[i]? = (s₄.arrs outArr)[i]? := by
    intro i hi
    rw [hprefix7 i hi, hprefix6 i hi, harrs5]
  refine ⟨s₇, _, hex_all, by dsimp only [K, V_J, E_J] at *; omega, ?_⟩
  apply outArr_eq_encUnderlyingGraphModel hp x (s₇.arrs outArr) hout_len7
  · rw [hprefix_74 0 (by omega), hout0_4]
  · rw [hprefix_74 1 (by omega), hout1_4]
  · intro e
    have he := e.2
    rw [hprefix_74 (2 + 2 * e.1) (by omega), hprefix_74 (2 + 2 * e.1 + 1) (by omega)]
    exact hedges_out4 e
  · intro gamma
    have h := hS₇ gamma
    dsimp [S₆, S₄] at h
    rwa [Finset.union_assoc,
      branchVertsFrom_zero_union_internalVertsSliceUnion_finRange hp x gamma,
      pathBranchUnion_union_wallVertBranchSet_eq_modelBranchSet hp x gamma] at h

/-- Constant `c(p) ≥ 1` such that `wordSize (alg74WordConst p) (alg74Size x)` satisfies
`Section5WordBounds` for every `x : Alg74Input p (alg74LiftRadius p)`. -/
def alg74WordConst (p : ℕ) : ℕ :=
  let K := (completeGraphEdges p).length
  4 * K + 3 * p + alg74BoxMarginConst p + 12

theorem alg74_section5_word_bounds {p : ℕ} (hp : 2 ≤ p)
    (x : Alg74Input p (alg74LiftRadius p)) :
    Section5WordBounds (wordSize (alg74WordConst p) (alg74Size x)) p (alg74LiftRadius p) x := by
  let K := (completeGraphEdges p).length
  let c := alg74WordConst p
  let m := alg74Size x
  let w := wordSize c m
  have hc1 : 1 ≤ c := by dsimp [c, alg74WordConst]; omega
  have hmul_w : c * (m + 2) < 2 ^ w := mul_lt_two_pow_wordSize hc1 m
  have hm_eq : m = x.G.numEdges + x.n + 1 := rfl
  have hm_ge1 : 1 ≤ m := by omega
  have hact_le : x.G.numActivePairs ≤ x.G.numEdges := numActivePairs_le_numEdges x.G
  have hVJ_le : elemWallNumVerts x.h ≤ x.n ∧ 2 * x.h ≤ elemWallNumVerts x.h :=
    elemWallNumVerts_le_n x
  have hh1 : 1 ≤ x.h := by have := x.hW_valid.1; omega
  have h2h2_le_VJ : 2 * x.h + 2 ≤ elemWallNumVerts x.h :=
    two_mul_add_two_le_elemWallNumVerts hh1
  have hEJ_le : (elemWallEdges x.h).length ≤ 2 * elemWallNumVerts x.h :=
    length_elemWallEdges_le x.h
  have hW_len_le : x.W.encList.length ≤ 3 + 3 * x.n :=
    x.W.length_encList_le x.hW_valid.2.2
  have hpaths_len_le : (encHPaths x.paths).length ≤ K * (x.n + 1) := by
    rw [← encHPathsSlice_finRange]
    simpa [K] using length_encHPathsSlice_le x (List.finRange K)
  have hin_len_eq :
      (encAlg74In x).length =
        2 + 3 * x.G.numActivePairs + x.W.encList.length + (encHPaths x.paths).length := by
    simp [encAlg74In, MultiDigraph.length_enc]
    omega
  have hc_def : c = 4 * K + 3 * p + alg74BoxMarginConst p + 12 := rfl
  refine
    { hw3 := by nlinarith
      hp_w := by nlinarith
      hK_w := by change K < 2 ^ w; nlinarith
      hn_w := by nlinarith
      hm_w := by nlinarith
      hwall_w := by nlinarith
      hVJW_w := by nlinarith
      hroute_w := by nlinarith
      hin_w := by nlinarith
      hout_w := by change 2 + 2 * K + p * x.n < 2 ^ w; nlinarith }

/-- Time-bound constant `C(p)` for `alg74Prog p`: running time is `≤ alg74TimeConst p * alg74Size x`. -/
def alg74TimeConst (p : ℕ) : ℕ :=
  let K := (completeGraphEdges p).length
  (p + 1) + 281 + 69 * p + 67 * K +
  (routeTerminalsCmd p).maxTime +
  ((markWallBranchVertsBody p).maxTime + 3) +
  2 * (markActCost p (List.finRange p) + 30) +
  180

/-- **Graph Minors XIII, (7.4) Algorithm** (page 90):
For every integer `p ≥ 2`, there exists `r ≥ 0` and a single height-independent Word RAM program `P`
(depending only on `p`) with running time `≤ C(p) * ε(G)` that outputs a model of $K_p$ in `G`. -/
public theorem gm13_algorithm_7_4 : Algorithm74Statement := by
  intro p hp
  refine ⟨alg74LiftRadius p, alg74Prog p, alg74TimeConst p, alg74WordConst p, ?_, ?_, ?_⟩
  · unfold alg74TimeConst; dsimp only; omega
  · unfold alg74WordConst; dsimp only; omega
  · intro x s hin
    let w := wordSize (alg74WordConst p) (alg74Size x)
    have hw : Section5WordBounds w p (alg74LiftRadius p) x :=
      alg74_section5_word_bounds hp x
    rcases alg74Prog_exec hp x hw hin with ⟨s', t, hex, ht, hout⟩
    refine ⟨s', t, hex, ?_, ⟨alg74UnderlyingModel hp x, hout⟩⟩
    let K := (completeGraphEdges p).length
    let V_J := elemWallNumVerts x.h
    let E_J := (elemWallEdges x.h).length
    let m := alg74Size x
    have hm_eq : m = x.G.numEdges + x.n + 1 := rfl
    have hact_le : x.G.numActivePairs ≤ x.G.numEdges := numActivePairs_le_numEdges x.G
    have hVJ_le : V_J ≤ x.n := (elemWallNumVerts_le_n x).1
    have hEJ_le : E_J ≤ 2 * V_J := length_elemWallEdges_le x.h
    have hW_len_le : x.W.encList.length ≤ 3 + 3 * x.n :=
      x.W.length_encList_le x.hW_valid.2.2
    have h1 : (p + 1) * x.n ≤ (p + 1) * m :=
      Nat.mul_le_mul_left (p + 1) (by omega)
    have h2 : (30 * x.G.numActivePairs + 23 * x.n + 65) * K + 2 * K ≤ (67 * K) * m := by
      have hle : 30 * x.G.numActivePairs + 23 * x.n + 65 + 2 ≤ 67 * m := by omega
      calc (30 * x.G.numActivePairs + 23 * x.n + 65) * K + 2 * K
        _ = (30 * x.G.numActivePairs + 23 * x.n + 65 + 2) * K := by ring
        _ ≤ (67 * m) * K := Nat.mul_le_mul_right K hle
        _ = (67 * K) * m := by ring
    have h3 : (routeTerminalsCmd p).maxTime ≤ (routeTerminalsCmd p).maxTime * m :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h4 :
        ((markWallBranchVertsBody p).maxTime + 3) * V_J ≤
          ((markWallBranchVertsBody p).maxTime + 3) * m :=
      Nat.mul_le_mul_left _ (by omega)
    have h5 :
        (markActCost p (List.finRange p) + 30) * E_J ≤
          (2 * (markActCost p (List.finRange p) + 30)) * m := by
      calc (markActCost p (List.finRange p) + 30) * E_J
        _ ≤ (markActCost p (List.finRange p) + 30) * (2 * m) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = (2 * (markActCost p (List.finRange p) + 30)) * m := by ring
    have h6 : 23 * p * x.W.encList.length ≤ (69 * p) * m := by
      calc 23 * p * x.W.encList.length
        _ ≤ 23 * p * (3 * m) := Nat.mul_le_mul_left (23 * p) (by omega)
        _ = (69 * p) * m := by ring
    have h7 :
        2 * E_J + 60 + (22 * V_J + 26 * E_J + 17 * x.W.encList.length + 25) +
          (95 * V_J + 10) + 1 + 15 + 10 ≤ (281 + 180) * m := by
      omega
    have hsum :
        alg74TimeConst p * m =
          (p + 1) * m + (281 + 180) * m + (69 * p) * m + (67 * K) * m +
          (routeTerminalsCmd p).maxTime * m +
          ((markWallBranchVertsBody p).maxTime + 3) * m +
          (2 * (markActCost p (List.finRange p) + 30)) * m := by
      unfold alg74TimeConst
      dsimp only [K]
      ring
    change t ≤ alg74TimeConst p * m
    change t ≤
      ((p + 1) * x.n + 2 * E_J + 2 * K + 60) +
      (22 * V_J + 26 * E_J + 17 * x.W.encList.length + 25) +
      (95 * V_J + 10) +
      ((30 * x.G.numActivePairs + 23 * x.n + 65) * K + 1) +
      (routeTerminalsCmd p).maxTime +
      (((markWallBranchVertsBody p).maxTime + 3) * V_J + 15) +
      ((markActCost p (List.finRange p) + 30) * E_J +
        23 * p * x.W.encList.length + 10) at ht
    omega

end GraphMinor.Compute
