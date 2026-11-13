module

public import GraphMinor.Compute.Algorithm99Step58
public import GraphMinor.Compute.Algorithm99Step3
public import GraphMinor.Compute.Algorithm99LoopModel
import GraphMinor.Compute.Algorithm91Parse
import GraphMinor.Compute.Algorithm94Scan
import GraphMinor.Compute.Join13WordSize72

/-!
# One iteration of the loop of Algorithm (9.9)

An iteration of the recursion of Algorithm (9.9) (Graph Minors XIII, pages 104–105) is step (3),
then either the model branch ("If we obtain a model of $K_p$ in $G_i$ and hence in $G$ we stop")
or step (4) followed by steps (5) to (8). The program is `alg99BodyProg`. Its execution theorem
`alg99BodyProg_exec` says: from a valid state stored at `B`, one iteration either stops with an
output of (9.9) (`Alg99StopOut`) and the loop flag `Q + 5` cleared, or stores the next state,
which is valid and at most half as large, and keeps the flag. Its time is at most
`alg99IterConst … * (n + 1) * (|E(G_i)| + v_i + 1)`.

Layout. The state is in arrays `B + 1` to `B + 4`. Step (3) runs at register base `Q`; the loop
flag is register `Q + 5` and `n = |V(G)|` is in register `Q + 6`; the tag of the program of steps
(5) to (7) is in register `Q + 7`; step (4) and the programs after the program of steps (5) to (7)
use registers from `Q + 10`.

The word size is at least `wordSize (alg99WordConst …) ((n + 1) * (|E(G_i)| + v_i + 1))`; every
bound on a word that the called programs need follows from it (`alg99_word_lt`).
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph

/-- `omega` after unfolding `Reg` and `Arr`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr, inArr, outArr] at *); omega))

/-! ### Section 1: The program and its constants -/

/-- One iteration of the loop of (9.9): step (3), then on tag `1` of (9.7) step (4) and steps
(5) to (8), and on tag `0` the model branch. -/
def alg99BodyProg (P97 P : Cmd) (pp h : ℕ) (h2 : 2 ≤ h) (h' : ℕ) (h2' : 2 ≤ h') (B Q : ℕ) :
    Cmd :=
  .seq (alg99Step3Prog P97 B Q)
    (.ite (.reg Q)
      (.seq (alg99Step4Prog h h2 h' h2' B (Q + 10) (pp.choose 2 + 5)) (alg99Step58Prog P B Q))
      (alg99ModelOutProg pp B Q))

/-- The constant of the word size of the loop of (9.9). -/
def alg99WordConst (pp h h' c97 c C_blk : ℕ) : ℕ :=
  c97 + c + C_blk + pp + (pp.choose 2 + 5) + (pp.choose 2 + 5) *
    (3 + elemWallNumVerts h + (elemWallEdges h).length) + 4 * elemWallNumVerts h' +
    2 * elemWallNumVerts h + (elemWallEdges h').length + h + h' + 20

/-- The constant of the time of one iteration of the loop of (9.9). -/
def alg99IterConst (pp h' C97 K4 C C_blk : ℕ) : ℕ :=
  C97 + K4 + C + 131 * C_blk + 46 * pp +
    65 * (elemWallNumVerts h' + (elemWallEdges h').length) + 2400

/-- What an iteration that stops writes in `outArr`, for the state `st` of that iteration:
the model of `K_p` of step (3) mapped by `orig`, or output (iii) built from output (a) of
steps (5) to (7) for a wall chosen by step (4). -/
def Alg99StopOut (pp h ω : ℕ) (h2 : 2 ≤ h) (he : Even h) (C_blk w B : ℕ) {h' n : ℕ}
    {G : MultiDigraph n} (st : Alg99Iter h' G) (hst : st.IsValid (pp.choose 2 + 5))
    (out : List ℕ) : Prop :=
  (∃ K : Fin pp → Finset (Fin st.v), IsCliqueModel st.Gi.toSimpleGraph pp K ∧
      out = 1 :: encBitSetsUpTo (fun j => (K j).map ⟨st.orig, hst.orig_injective⟩) pp) ∨
  (∃ X : Finset (Fin st.v), X.card < pp.choose 2 ∧
    ∃ (W : WallOfHeight h ((WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).deleteVertices X))
      (hW : W.IsValid),
      Disjoint W.compassFinset st.Z ∧
      W.compassFinset.toNatSet =
        V(GM13.wallCompass (delGraph (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X)
          (W.toGMWall h2 he hW)) ∧
      ∃ (s_m : State)
        (p : ParsedCase3Block ((WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).deleteVertices X)
          X),
        IsCase3StepsOutputA h ω (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X W h2 he hW
          C_blk w (B - 1) (B - 3) s_m ∧
        parseCase3Block _ X (s_m.arrs (B - 3)) = some p ∧
        out = 2 :: (bitSetList (X.image st.orig) ++
          p.movedBlock hst.orig_injective (hst.edgeMult_wallUnion X)))

/-! ### Section 2: Bounds -/

/-- A word bounded by `D (S + 1)` with `D ≤ alg99WordConst …` fits. -/
theorem alg99_word_lt {pp h h' c97 c C_blk w S D q : ℕ}
    (hw : wordSize (alg99WordConst pp h h' c97 c C_blk) S ≤ w)
    (hD : D ≤ alg99WordConst pp h h' c97 c C_blk) (hq : q ≤ D * (S + 1)) : q < 2 ^ w :=
  hq.trans_lt (linear_lt_wordSize72 (by unfold alg99WordConst; omega) hD hw)

/-- The length of output (ii) of (9.7). -/
theorem length_alg97Out_le {n s h : ℕ} {G : MultiDigraph n} (X : Finset (Fin n))
    (W_flat : Fin s → WallOfHeight h G) (hW : ∀ a, (W_flat a).IsValid) :
    (1 :: (bitSetList X ++ (List.finRange s).flatMap (fun a => (W_flat a).encList))).length ≤
      1 + n + s * (3 + elemWallNumVerts h + (elemWallEdges h).length + n) := by
  simp only [List.length_cons, List.length_append, length_bitSetList, List.length_flatMap]
  have hsum := List.sum_le_length_nsmul
    ((List.finRange s).map (fun a => (W_flat a).encList.length))
    (3 + elemWallNumVerts h + (elemWallEdges h).length + n) (by
      intro x hx
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
      exact Alg91.length_encList_le_of_isValid (hW a))
  simp only [List.length_map, List.length_finRange, smul_eq_mul] at hsum
  omega

/-! ### Section 3: One iteration -/

/-- **One iteration of the recursion of Algorithm (9.9)** (Graph Minors XIII, pages 104–105),
on the Word RAM. From a valid state `st` stored at `B`, with `n` in register `Q + 6`, the
iteration ends in one of two ways:
* it stops: the flag `Q + 5` is `0` and `outArr` holds `Alg99StopOut … st`;
* it goes on: the flag is unchanged, and a next state, valid and at most half as large
  (`2 (|E(G_{i+1})| + v_{i+1} + 1) ≤ |E(G_i)| + v_i + 1`), is stored at `B`. -/
theorem alg99BodyProg_exec {pp h h' ω C97 c97 C C_blk c K4 : ℕ} {h2 : 2 ≤ h} {he : Even h}
    {h2' : 2 ≤ h'} {he' : Even h'} {P97 P : Cmd} {B Q : ℕ}
    (hP97 : RunsAsSubroutine (alg97Size (h' := h')) (encAlg97In (h' := h'))
      (IsAlg97Output pp (pp.choose 2 + 5) h h') P97 (fun m => m) C97 c97)
    (hP : Case3StepsRuns h h' ω h2 he h2' he' C C_blk c 23 16 (B + 5) 33 (B - 1) (B - 2) (B - 3)
      (B - 4) (B + 6) (Q + 7) (Q + 10) P)
    (hK4 : ∀ n m, alg99Step4Cost (pp.choose 2 + 5) h h' B n m ≤ K4 * (n + m + 1))
    (hB : 40 ≤ B) (hB97 : folioCallerArrBase P97 ≤ B) (hQ : 15 ≤ Q)
    (hQ97 : folioCallerRegBase P97 ≤ Q)
    {n : ℕ} {G : MultiDigraph n} {st : Alg99Iter h' G} (hst : st.IsValid (pp.choose 2 + 5))
    {w : ℕ}
    (hw : wordSize (alg99WordConst pp h h' c97 c C_blk)
      ((n + 1) * (st.Gi.numEdges + st.v + 1)) ≤ w)
    {s : State} (hS : st.StoredIn B s) (hn : s.regs (Q + 6) = n) :
    ∃ s' t, Exec w (alg99BodyProg P97 P pp h h2 h' h2' B Q) s s' t ∧
      t ≤ alg99IterConst pp h' C97 K4 C C_blk * ((n + 1) * (st.Gi.numEdges + st.v + 1)) ∧
      s'.regs (Q + 6) = n ∧
      ((s'.regs (Q + 5) = 0 ∧ Alg99StopOut pp h ω h2 he C_blk w B st hst (s'.arrs outArr)) ∨
        (s'.regs (Q + 5) = s.regs (Q + 5) ∧
          ∃ (X V_A Bd : Finset (Fin st.v)) (A_sub : MultiDigraph st.v)
            (W_A : WallOfHeight h' (A_sub.deleteVerticesCompact V_Aᶜ)),
            (st.step8 X V_A Bd W_A).StoredIn B s' ∧
            (st.step8 X V_A Bd W_A).IsValid (pp.choose 2 + 5) ∧
            2 * ((st.step8 X V_A Bd W_A).Gi.numEdges + (st.step8 X V_A Bd W_A).v + 1) ≤
              st.Gi.numEdges + st.v + 1)) := by
  -- Sizes.
  set M := st.Gi.numEdges + st.v + 1 with hM
  set S := (n + 1) * M with hSdef
  have hvn : st.v ≤ n := le_of_injective_orig hst.orig_injective
  have hM1 : 1 ≤ M := by omega
  have hMS : M ≤ S := Nat.le_mul_of_pos_left M (by omega)
  have hnS : n + 1 ≤ S := Nat.le_mul_of_pos_right (n + 1) hM1
  have hAP : st.Gi.numActivePairs ≤ st.Gi.numEdges := MultiDigraph.numActivePairs_le_numEdges _
  have hHv := Alg91.length_encList_le_of_isValid hst.wall_isValid
  set e' := elemWallNumVerts h' with he'_def
  set d' := (elemWallEdges h').length with hd'_def
  set cW := alg99WordConst pp h h' c97 c C_blk with hcW
  have hcW' : cW = c97 + c + C_blk + pp + (pp.choose 2 + 5) + (pp.choose 2 + 5) *
      (3 + elemWallNumVerts h + (elemWallEdges h).length) + 4 * e' + 2 * elemWallNumVerts h +
      d' + h + h' + 20 := rfl
  have wl : ∀ {D q : ℕ}, D ≤ cW → q ≤ D * (S + 1) → q < 2 ^ w := fun hD hq =>
    alg99_word_lt hw hD hq
  have wS : ∀ {q : ℕ}, q ≤ S → q < 2 ^ w := fun hq =>
    wl (D := 1) (by omega) (by omega)
  have wc : ∀ {q : ℕ}, q ≤ cW → q < 2 ^ w := fun hq =>
    wl (D := cW) le_rfl (hq.trans (Nat.le_mul_of_pos_right _ (by omega)))
  have hw4 : 4 < 2 ^ w := wc (by omega)
  have wD : ∀ {D q : ℕ}, 1 ≤ D → D ≤ cW → q ≤ D + S → q < 2 ^ w := fun {D q} h1 hD hq =>
    wl hD (hq.trans (by
      have := Nat.le_mul_of_pos_left S (show 0 < D by omega)
      rw [Nat.mul_succ]; omega))
  -- Step (3).
  have hsz97 : alg97Size (st.toAlg97Input ⟨h2', he'⟩ hst.wall_isValid) ≤ S := by
    change (st.v + 1) * (st.Gi.numEdges + st.v + 1) ≤ (n + 1) * M
    exact Nat.mul_le_mul (by omega) le_rfl
  have hw97 : wordSize c97 (alg97Size (st.toAlg97Input ⟨h2', he'⟩ hst.wall_isValid)) ≤ w :=
    ((wordSize_mono_right c97 hsz97).trans (wordSize_mono_left (by omega) S)).trans hw
  have hlen3 : st.Gi.enc.length + st.H.encList.length ≤ (8 + e' + d') * M := by
    rw [MultiDigraph.length_enc]
    obtain ⟨k, hk⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    rw [hk, Nat.mul_succ]
    have := Nat.mul_le_mul_right k (show 3 ≤ 8 + e' + d' by omega)
    omega
  have hlen3S : (8 + e' + d') * M ≤ (8 + e' + d') * (S + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  obtain ⟨s₁, t₁, hex₁, ht₁, hS₁, hout₁, hR₁, harr₁, hreg₁⟩ :=
    alg99Step3Prog_exec hP97 (B := B) (R := Q) hB97 hQ97 st ⟨h2', he'⟩ hst.wall_isValid hw97
      (by omega) (wS (by omega)) (wS (by omega)) (wc (by omega)) (wc (by omega))
      (wl (D := 8 + e' + d') (by omega) (hlen3.trans hlen3S)) s hS
  have hn₁ : s₁.regs (Q + 6) = n := by rw [hreg₁ _ (by romega)]; exact hn
  have hf₁ : s₁.regs (Q + 5) = s.regs (Q + 5) := hreg₁ _ (by romega)
  have ht3 : t₁ ≤ C97 * S + 15 * ((8 + e' + d') * S) + 30 := by
    have a := Nat.mul_le_mul_left C97 hsz97
    have b := Nat.mul_le_mul_left (8 + e' + d') hMS
    omega
  rcases hout₁ with ⟨K, hK0, hKm⟩ | ⟨X, W_flat, hsub, hout, hXc, hpair, hall⟩
  · -- The model branch.
    have hcond : (Expr.reg Q).eval w s₁ = some 0 := by
      simp [Expr.eval, hR₁, hK0, checkWord, show (0 : ℕ) < 2 ^ w by omega]
    have hppS : (pp + 1) * (S + 1) = pp * S + pp + S + 1 := by ring
    have hpn := Nat.mul_le_mul_left pp (show n ≤ S by omega)
    have hpv := Nat.mul_le_mul_left pp (show st.v ≤ S by omega)
    obtain ⟨s₂, t₂, hex₂, ht₂, hout₂, hflag₂, hreg₂⟩ :=
      alg99ModelOutProg_exec hst K B Q (by omega) (by omega) (wc (by omega)) (wS (by omega))
        (wS (by omega)) (wl (D := pp + 1) (by omega) (by omega))
        (wl (D := pp + 1) (by omega) (by omega)) hS₁ hK0 hn₁
    refine ⟨s₂, t₁ + (1 + t₂), .seq hex₁ (.ite_false hcond hex₂), ?_, ?_,
      Or.inl ⟨hflag₂, Or.inl ⟨K, hKm, hout₂⟩⟩⟩
    · have hK : alg99IterConst pp h' C97 K4 C C_blk * S = C97 * S + K4 * S + C * S +
          131 * (C_blk * S) + 46 * (pp * S) + 65 * ((e' + d') * S) + 2400 * S := by
        unfold alg99IterConst; ring
      have c1 : (8 + e' + d') * S = 8 * S + (e' + d') * S := by ring
      rw [hK]
      omega
    · rw [hreg₂ _ (by romega) (by romega) (by romega), hn₁]
  · -- Step (4), then steps (5) to (8).
    have hcond : (Expr.reg Q).eval w s₁ = some 1 := by
      simp [Expr.eval, hR₁, hout, checkWord, show (1 : ℕ) < 2 ^ w by omega]
    have hWv : ∀ a, (W_flat a).IsValid := fun a =>
      st.H.isValid_of_isSubwallOf hst.wall_isValid (hsub a)
    have hout_w : (s₁.arrs outArr).length < 2 ^ w := by
      set sC := pp.choose 2 + 5 with hsC
      set Bq := 3 + elemWallNumVerts h + (elemWallEdges h).length with hBq
      have hlenOut : (s₁.arrs outArr).length ≤ 1 + st.v + sC * (Bq + st.v) := by
        rw [hout]; exact length_alg97Out_le X W_flat hWv
      refine wl (D := 1 + sC + sC * Bq) (by omega) ?_
      have e1 : sC * (Bq + st.v) = sC * Bq + sC * st.v := by ring
      have e2 : (1 + sC + sC * Bq) * (S + 1) = S + 1 + sC * S + sC + sC * Bq * S + sC * Bq := by
        ring
      have := Nat.mul_le_mul_left sC (show st.v ≤ S by omega)
      omega
    obtain ⟨s₂, t₂, hex₂, ht₂, h23, h16, ⟨a, hW, hB5, h33, hWX, hflat, hcX, hK, hKZ, h4⟩, harr₂,
        hreg₂⟩ :=
      alg99Step4Prog_exec (p := pp) hst.wall_isValid h2' he' h2 he hXc
        (by have := hst.card_Z; omega) W_flat hsub hpair (fun a => (hall a).1)
        (fun a => (hall a).2.1) (fun a => (hall a).2.2) B (Q + 10) hB (by omega)
        (wc (by omega)) (wS (by omega)) (wl (D := 3) (by omega) (by omega))
        (wl (D := 4) (by omega) (by omega)) (wc (by omega)) (wc (by omega)) (wc (by omega))
        (wD (D := 4 + 3 * e') (by omega) (by omega) (by omega)) hS₁.1 hS₁.2.2.1 hS₁.2.2.2 hout
        hout_w
    have hS₂ : st.StoredIn B s₂ := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        (rw [harr₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega)]; first | exact hS₁.1 | exact hS₁.2.1 | exact hS₁.2.2.1 | exact hS₁.2.2.2)
    have hn₂ : s₂.regs (Q + 6) = n := by rw [hreg₂ _ (by omega) (by omega)]; exact hn₁
    have hf₂ : s₂.regs (Q + 5) = s₁.regs (Q + 5) := hreg₂ _ (by omega) (by omega)
    have hE' := WallOfHeight.wallUnionMultiDigraph_numEdges_le st.Gi X st.H
    have hsz' : (st.v + 1) * ((WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).numEdges +
        st.v + 1) ≤ S := Nat.mul_le_mul (by omega) (by omega)
    have hblk := Nat.mul_le_mul_left C_blk (show st.v +
      (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).numEdges + 1 ≤ S by omega)
    obtain ⟨s₃, t₃, hex₃, ht₃, hn₃, hcase⟩ :=
      alg99Step58_exec hP hB hst rfl hXc rfl hWX hflat hcX hK hKZ h4
        (((wordSize_mono_right c hsz').trans (wordSize_mono_left (by omega) S)).trans hw)
        hw4 (wS (by omega)) (wS (by omega)) (wl (D := 3) (by omega) (by omega)) (wS (by omega))
        (wc (by omega)) (wc (by omega)) (wD (D := 3 + e' + d') (by omega) (by omega) (by omega))
        (wl (D := C_blk + 1) (by omega) (by
          have : (C_blk + 1) * (S + 1) = C_blk * S + C_blk + S + 1 := by ring
          omega))
        hS₂ h23 h16 hB5 h33 hn₂
    refine ⟨s₃, t₁ + (1 + (t₂ + t₃)), .seq hex₁ (.ite_true hcond (by omega) (.seq hex₂ hex₃)),
      ?_, hn₃, ?_⟩
    · have hK4' := (hK4 st.v st.Gi.numEdges).trans (Nat.mul_le_mul_left K4
        (show st.v + st.Gi.numEdges + 1 ≤ S by omega))
      have hC := Nat.mul_le_mul_left C hsz'
      rw [← Nat.mul_assoc] at hC
      have hed := Nat.le_mul_of_pos_right (e' + d') (show 0 < S by omega)
      have hK : alg99IterConst pp h' C97 K4 C C_blk * S = C97 * S + K4 * S + C * S +
          131 * (C_blk * S) + 46 * (pp * S) + 65 * ((e' + d') * S) + 2400 * S := by
        unfold alg99IterConst; ring
      have c1 : (8 + e' + d') * S = 8 * S + (e' + d') * S := by ring
      rw [hK]
      omega
    · rcases hcase with ⟨hflag, s_m, p, hA, hparse, hout3⟩ |
        ⟨hflag, V_A, Bd, A_sub, W_A, hS', hval, hsize⟩
      · exact Or.inl ⟨hflag, Or.inr ⟨X, hXc, _, hW, hKZ, hK, s_m, p, hA, hparse, hout3⟩⟩
      · exact Or.inr ⟨by rw [hflag, hf₂, hf₁], X, V_A, Bd, A_sub, W_A, hS', hval, hsize⟩

end GraphMinor.Compute
