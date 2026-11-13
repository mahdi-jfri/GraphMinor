module

public import GraphMinor.Compute.Algorithm99State
import GraphMinor.Compute.DPToDCS
import GraphMinor.Compute.Algorithm94Scan
import GraphMinor.Compute.Algorithm77Prog75Full

/-!
# Step (3) of Algorithm (9.9): one call of (9.7)

Step (3) of the proof of (9.8) in Graph Minors XIII (page 104) begins: "(3) We apply (9.7) to
$G_i, H_i$. If we obtain a model of $K_p$ in $G_i$ and hence in $G$ we stop."

The program `alg99Step3Prog P97 B R` writes `G_i.enc ++ H_i.encList` (arrays `B + 1` and `B + 4`
of a stored state, `Alg99Iter.StoredIn`) into the input array, runs `P97`, and reads the tag of
its output into register `R` (`alg99Step3Prog_exec`). Since `P97` writes no array at `B` or above,
the stored state is kept.

"and hence in $G$": a model of `K_p` in `G_i` is mapped through `orig` to a model of `K_p` in `G`
(`IsCliqueModel.map_orig`), since every edge of `G_i` is an edge of `G` between the images of its
ends (`Alg99Iter.IsValid`).
-/

@[expose] public section

namespace GraphMinor.Compute

/-- `omega` after unfolding `Reg` and `Arr`, which `omega` does not see as `ℕ`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr, inArr, outArr] at *); omega))

/-! ### Section 1: The call -/

/-- The input of (9.7) for a valid state: `G_i` with the wall `H_i`. -/
def Alg99Iter.toAlg97Input {h' n : ℕ} {G : MultiDigraph n} (st : Alg99Iter h' G)
    (hh' : 2 ≤ h' ∧ Even h') (hH : st.H.IsValid) : Alg97Input h' where
  n := st.v
  G := st.Gi
  W := st.H
  hW_valid := ⟨hh'.1, hh'.2, hH⟩

/-- Step (3) of (9.9): write `G_i.enc ++ H_i.encList` into `inArr`, run `P97`, and read the tag
of its output into register `R`. Registers `R + 1` to `R + 4` are scratch. -/
def alg99Step3Prog (P97 : Cmd) (B R : ℕ) : Cmd :=
  .seq (.assign (R + 3) (.len (B + 1)))
    (.seq (.assign (R + 4) (.len (B + 4)))
      (.seq (concatTwoArrsProg (B + 1) (B + 4) inArr (R + 3) (R + 4) (R + 1))
        (.seq P97 (.assign R (.read outArr (.const 0))))))

private theorem getElem_zero_eq_headD' (l : List ℕ) (h : 0 < l.length) : l[0] = l.headD 0 := by
  cases l with
  | nil => simp at h
  | cons a l => rfl

/-- The first word of an output of (9.7) is `0` or `1`. -/
theorem headD_lt_two_of_isAlg97Output {p s h h' : ℕ} {x : Alg97Input h'} {out : List ℕ}
    (hout : IsAlg97Output p s h h' x out) : 0 < out.length ∧ out.headD 0 < 2 := by
  rcases hout with ⟨K, rfl, _⟩ | ⟨X, W, _, rfl, _⟩ <;> simp

/-- **Step (3) of Algorithm (9.9)** (Graph Minors XIII, page 104), the call of (9.7), on the
Word RAM. -/
theorem alg99Step3Prog_exec {p s₀ h h' C c : ℕ} {P97 : Cmd}
    (hP : RunsAsSubroutine (alg97Size (h' := h')) (encAlg97In (h' := h'))
      (IsAlg97Output p s₀ h h') P97 (fun m => m) C c)
    {B R : ℕ} (hB : folioCallerArrBase P97 ≤ B) (hR : folioCallerRegBase P97 ≤ R)
    {n : ℕ} {G : MultiDigraph n} (st : Alg99Iter h' G) (hh' : 2 ≤ h' ∧ Even h')
    (hH : st.H.IsValid) {w : ℕ}
    (hw : wordSize c (alg97Size (st.toAlg97Input hh' hH)) ≤ w)
    (hw1 : 1 < 2 ^ w) (hv_w : st.v < 2 ^ w) (hm_w : st.Gi.numEdges < 2 ^ w)
    (hh_w : h' < 2 ^ w) (hc_w : 3 + 2 * elemWallNumVerts h' < 2 ^ w)
    (hlen_w : st.Gi.enc.length + st.H.encList.length < 2 ^ w)
    (sa : State) (hst : st.StoredIn B sa) :
    ∃ s' t, Exec w (alg99Step3Prog P97 B R) sa s' t ∧
      t ≤ C * alg97Size (st.toAlg97Input hh' hH) +
        15 * (st.Gi.enc.length + st.H.encList.length) + 30 ∧
      st.StoredIn B s' ∧
      IsAlg97Output p s₀ h h' (st.toAlg97Input hh' hH) (s'.arrs outArr) ∧
      s'.regs R = (s'.arrs outArr).headD 0 ∧
      (∀ a : ℕ, B ≤ a → s'.arrs a = sa.arrs a) ∧
      (∀ r : ℕ, R + 4 < r → s'.regs r = sa.regs r) := by
  obtain ⟨hG, horig, hZ, hHenc⟩ := hst
  have hB2 : 2 ≤ B := le_trans (le_max_left _ _) hB
  have cG := checkWord_of_lt (w := w) (v := st.Gi.enc.length) (by omega)
  have cH := checkWord_of_lt (w := w) (v := st.H.encList.length) (by omega)
  let s₁ := sa.setReg (R + 3) st.Gi.enc.length
  have hex₁ : Exec w (.assign (R + 3) (.len (B + 1))) sa s₁ 2 :=
    .assign (by simp only [Expr.eval, hG, cG])
  let s₂ := s₁.setReg (R + 4) st.H.encList.length
  have hex₂ : Exec w (.assign (R + 4) (.len (B + 4))) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, s₁, State.setReg_arrs, hHenc, cH])
  have hvalG := mem_enc_lt_two_pow st.Gi hv_w hm_w
  have hvalH := all_lt_encList_of_isValid st.H hH le_rfl hh_w hc_w hv_w
  obtain ⟨s₃, t₃, hex₃, ht₃, hin₃, harr₃, hreg₃⟩ :=
    concatTwoArrsProg_exec (B + 1) (B + 4) inArr (R + 3) (R + 4) (R + 1)
      st.Gi.enc [] st.H.encList [] (by romega) (by romega) (by omega) (by omega) rfl rfl hw1
      hlen_w hvalG hvalH (s := s₂) (by simp [s₂, s₁, hG]) (by simp [s₂, s₁, hHenc])
      (by simp [s₂, s₁]) (by simp [s₂])
  obtain ⟨s₄, t₄, hex₄, ht₄, hout₄, hreg₄, harr₄⟩ :=
    hP (st.toAlg97Input hh' hH) w hw s₃ hin₃
  obtain ⟨hpos, htag⟩ := headD_lt_two_of_isAlg97Output hout₄
  have hread : (Expr.read outArr (.const 0)).eval w s₄ = some ((s₄.arrs outArr).headD 0) := by
    have h0 : checkWord w 0 = some 0 := checkWord_of_lt (by omega)
    simp only [Expr.eval, h0, hpos, ↓reduceDIte, getElem_zero_eq_headD' _ hpos]
    exact checkWord_of_lt (by omega)
  have hkeep : ∀ a : ℕ, B ≤ a → (s₄.setReg R ((s₄.arrs outArr).headD 0)).arrs a = sa.arrs a := by
    intro a ha
    rw [State.setReg_arrs, harr₄ a (by romega), harr₃ a (by romega)]
    rfl
  refine ⟨s₄.setReg R ((s₄.arrs outArr).headD 0), 2 + (2 + (t₃ + (t₄ +
      ((Expr.read outArr (.const 0)).cost + 1)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.assign hread)))), ?_,
    ⟨?_, ?_, ?_, ?_⟩, hout₄, by simp, hkeep, fun r hr => ?_⟩
  · dsimp only at ht₄; simp only [Expr.cost]; omega
  · rw [hkeep _ (by omega), hG]
  · rw [hkeep _ (by omega), horig]
  · rw [hkeep _ (by omega), hZ]
  · rw [hkeep _ (by omega), hHenc]
  · rw [State.setReg_regs_ne _ _ (by romega), hreg₄ r (by romega), hreg₃ r (by omega)]
    simp only [s₂, s₁, State.setReg_regs_ne _ _ (show r ≠ R + 4 by omega),
      State.setReg_regs_ne _ _ (show r ≠ R + 3 by omega)]

/-! ### Section 2: A model in `G_i` is a model in `G` -/

/-- A model of `K_p` is carried by an embedding of graphs. -/
theorem IsCliqueModel.map_embedding {v n p : ℕ} {H : SimpleGraph (Fin v)}
    {G : SimpleGraph (Fin n)} (f : Fin v ↪ Fin n) (hf : ∀ u w, H.Adj u w → G.Adj (f u) (f w))
    {K : Fin p → Finset (Fin v)} (hK : IsCliqueModel H p K) :
    IsCliqueModel G p (fun j => (K j).map f) := by
  obtain ⟨hconn, hdisj, hadj⟩ := hK
  refine ⟨fun i => ⟨(hconn i).1.map, ?_⟩, fun i j hij => ?_, fun i j hij => ?_⟩
  · let φ : H.induce (K i : Set (Fin v)) →g G.induce (((K i).map f : Finset (Fin n)) : Set (Fin n)) :=
      { toFun := fun x => ⟨f x.1, by simp⟩
        map_rel' := fun {x y} hxy => hf _ _ hxy }
    refine (hconn i).2.map φ ?_
    rintro ⟨y, hy⟩
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  · exact Finset.disjoint_map f |>.mpr (hdisj i j hij)
  · obtain ⟨u, hu, w, hw, huw⟩ := hadj i j hij
    exact ⟨f u, Finset.mem_map_of_mem f hu, f w, Finset.mem_map_of_mem f hw, hf u w huw⟩

/-- Every edge of `G_i` is an edge of `G` between the images of its ends. -/
theorem Alg99Iter.IsValid.toSimpleGraph_adj {h' n s : ℕ} {G : MultiDigraph n}
    {st : Alg99Iter h' G} (hst : st.IsValid s) {u w : Fin st.v}
    (huw : st.Gi.toSimpleGraph.Adj u w) :
    G.toSimpleGraph.Adj (st.orig u) (st.orig w) := by
  obtain ⟨hne, hpos⟩ := huw
  refine ⟨fun h => hne (hst.orig_injective h), ?_⟩
  rcases hpos with hpos | hpos
  · rcases hst.edgeMult_eq u w with h0 | heq
    · omega
    · exact Or.inl (heq ▸ hpos)
  · rcases hst.edgeMult_eq w u with h0 | heq
    · omega
    · exact Or.inr (heq ▸ hpos)

/-- **Step (3) of Algorithm (9.9)** (page 104): "If we obtain a model of $K_p$ in $G_i$ and hence
in $G$ we stop." A model of `K_p` in `G_i` is mapped by `orig` to a model of `K_p` in `G`. -/
theorem IsCliqueModel.map_orig {h' n s p : ℕ} {G : MultiDigraph n} {st : Alg99Iter h' G}
    (hst : st.IsValid s) {K : Fin p → Finset (Fin st.v)}
    (hK : IsCliqueModel st.Gi.toSimpleGraph p K) :
    IsCliqueModel G.toSimpleGraph p (fun j => (K j).map ⟨st.orig, hst.orig_injective⟩) :=
  IsCliqueModel.map_embedding ⟨st.orig, hst.orig_injective⟩
    (fun _ _ h => hst.toSimpleGraph_adj h) hK

end GraphMinor.Compute
