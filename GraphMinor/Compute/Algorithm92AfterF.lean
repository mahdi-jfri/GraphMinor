module

public import GraphMinor.Compute.Algorithm92MainFacts

/-!
# Graph Minors XIII, (9.2): the program after `F` (`Algorithm92AfterF.lean`)

Page 101 of Graph Minors XIII: after `F` is found, the algorithm compresses `H ∪ F`, looks the
compressed graph up in a table, and lifts the answer back to `G`. The program `afterF` does this
on the arrays that the program of `F92ProgClaim` writes (`aG = x.G.enc`, `aW = x.W.encList`,
`aF = encSegs92 segs`):

1. `buildProg` writes the layout of `H ∪ F` and the nodes;
2. `sweepProg` writes the runs; `rankProg` numbers the compressed vertices;
3. `keyProg` writes the key `compKey x segs`; `padProg` pads it;
4. `dispatchK` writes the table entry `tableK (compKey x segs)` into `aAns`;
5. `modelProg` or `starProg` lifts the answer, by the first entry of `aAns`.

`afterF_exec` shows that the output is correct for `x` and gives the time.
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

section Defs

variable (l m p h k r : ℕ)

/-- The finite list of candidate keys. -/
def keys92 : List (List ℕ) := lists (bound92 h k) (keyLen92 h k)

/-- The table, read at a key. -/
noncomputable def ans92 (κ : List ℕ) : List ℕ := tableK h l m p k r κ

/-- A bound on the length and on the entries of every table entry. -/
noncomputable def tsum92 : ℕ :=
  ((keys92 h k).map (fun κ => (ans92 l m p h k r κ).length + (ans92 l m p h k r κ).sum)).sum

/-- **The program after `F`.** -/
noncomputable def afterF : Cmd :=
  .seq (buildProg h) <| .seq sweepProg <| .seq rankProg <|
  .seq (keyProg (elemWallNumVerts h)) <| .seq (padProg (keyLen92 h k)) <|
  .seq (dispatchK (keyLen92 h k) (ans92 l m p h k r) (keys92 h k)) <|
  .ite (.read aAns (.const 0)) (modelProg p) (starProg l)

end Defs

variable {l m p h k r : ℕ}

theorem le_tsum92 {κ : List ℕ} (hκ : κ ∈ keys92 h k) :
    (ans92 l m p h k r κ).length + (ans92 l m p h k r κ).sum ≤ tsum92 l m p h k r :=
  List.le_sum_of_mem (List.mem_map_of_mem hκ)

theorem rankF_lt {x : Alg92Input l m p h k r} {segs : List (List (Fin x.n))} {z : ℕ}
    (hz : z < x.n) : rankF x segs z < x.n := by
  unfold rankF
  split_ifs
  · exact lt_of_le_of_lt (length_vlist_le z) hz
  · omega

variable (l m p h k r) in
/-- The time of `afterF`, as a function of `n`, of the length `b` of the layout and of the time
of `buildProg`. -/
noncomputable def afterTime (n b bt : ℕ) : ℕ :=
  bt + (20 + 2 * n + 25 * b) + (10 + 3 * n + 47 * n) + (50 + 40 * elemWallNumVerts h + 50 * b) +
    (20 + 16 * keyLen92 h k) +
    ((keys92 h k).length * (6 + 5 * keyLen92 h k) + (3 + 4 * tsum92 l m p h k r)) + 2 +
    ((20 + 13 * p + 33 * (p * n)) +
      (60 + l * (37 + tsum92 l m p h k r * (67 + 15 * b)) +
        17 * (tsum92 l m p h k r * (b + 1) + 3)))

variable (l m p h k r) in
/-- The word bound that `afterF` needs. -/
noncomputable def afterWord (n b bB : ℕ) : ℕ :=
  2 * (tsum92 l m p h k r * (b + 1) + 3) + 3 * b + p * n + 4 * n + p +
    2 * elemWallNumVerts h + 2 * keyLen92 h k + 2 * bound92 h k + 2 * tsum92 l m p h k r + bB + 30

/-- **The program after `F` computes a correct output.** From the arrays of `F92ProgClaim` for a
list `segs` with `IsFSystem x segs paths`, `afterF` writes into `outArr` an output that is correct
for `x` (in the sense of `IsAlg92Output`). The hypothesis `hex` is that every input has a correct
output; it is proved from Theorem (9.2) of the paper in `exists_isAlg92Output`. -/
theorem afterF_exec (hl : 3 ≤ l) (hex : ∀ y : Alg92Input l m p h k r, ∃ out, IsAlg92Output l m p y out)
    {x : Alg92Input l m p h k r} {segs : List (List (Fin x.n))} {paths : Fin k → List (Fin x.n)}
    (hF : IsFSystem x segs paths) (hs : segs.length ≤ k) {w : ℕ} {s : State}
    (hG : s.arrs aG = x.G.enc) (hW : s.arrs aW = x.W.encList) (hFa : s.arrs aF = encSegs92 segs)
    (hw : afterWord l m p h k r x.n (layout x segs).length (bigB x segs) < 2 ^ w) :
    ∃ s' t, Exec w (afterF l m p h k r) s s' t ∧
      t ≤ afterTime l m p h k r x.n (layout x segs).length (buildTime x segs) ∧
      IsAlg92Output l m p x (s'.arrs outArr) := by
  classical
  unfold afterWord at hw
  have hnd : ∀ P ∈ segs, P.length ≤ x.n := fun P hP => by
    simpa using (hF.nodup P hP).length_le_card
  have hNn : (fVerts x segs).card ≤ x.n := card_fVerts_le_n
  have hBB := le_length_encList (x := x)
  have hbB : (layout x segs).length + x.W.encList.length ≤ bigB x segs := by unfold bigB; omega
  have hLn : ∀ v ∈ layout x segs, v ≤ x.n := fun v hv => le_of_mem_layout hv
  have hLw : ∀ v ∈ layout x segs, v < 2 ^ w := fun v hv => by have := hLn v hv; omega
  -- 1. the layout and the nodes
  obtain ⟨s1, t1, ex1, ht1, hrn1, hL1, hN1, -, ha1⟩ :=
    buildProg_exec (h := h) (s := s) (w := w) hG hW hFa hnd (by omega)
  -- 2. the runs
  obtain ⟨s2, t2, ex2, ht2, hRS2, hEn2, hP2, ha2, hr2⟩ :=
    sweepProg_exec (s := s1) (w := w) hL1 hN1 hrn1 hLn (by omega)
  rw [tab_pF] at hP2
  -- 3. the numbers of the compressed vertices
  obtain ⟨s3, t3, ex3, ht3, hrN3, hRep3, hRank3, hE3, ha3, hr3⟩ :=
    rankProg_exec (s := s2) (w := w) (rep := repF x segs)
      (by rw [hr2 rn (by decide) (by decide) (by decide), hrn1])
      (by rw [ha2 aN (by decide) (by decide) (by decide), hN1]) hP2 hRS2 hEn2
      (by rw [ha2 aL (by decide) (by decide) (by decide), hL1])
      (fun y hy hnd' hop => by
        obtain ⟨h1, h2, h3⟩ := hrep_layout hF y hy hnd' hop
        exact ⟨h1, h2, h3⟩)
      (fun y hy => by
        have : repF x segs y < x.n := by simp [repF, hy]
        omega)
      (by omega) hLw
  rw [length_vlist_eq_card hF] at hrN3
  -- 4. the key
  have hrank : s3.arrs aRank = tab x.n (rankF x segs) := hRank3
  have hWa : s3.arrs aW = x.W.encList := by
    rw [ha3 aW (by decide) (by decide) (by decide), ha2 aW (by decide) (by decide) (by decide),
      ha1 aW (by decide) (by decide) (by decide), hW]
  have hrn3 : s3.regs rn = x.n := by
    rw [hr3 rn (by decide) (by decide) (by decide), hr2 rn (by decide) (by decide) (by decide),
      hrn1]
  have hL3 : s3.arrs aL = layout x segs := by
    rw [ha3 aL (by decide) (by decide) (by decide), ha2 aL (by decide) (by decide) (by decide), hL1]
  obtain ⟨s4, t4, ex4, ht4, hK4, ha4, hr4⟩ :=
    keyProg_exec (s := s3) (w := w) (V := elemWallNumVerts h) (repA := repvF x segs) (n := x.n)
      (N := (fVerts x segs).card)
      (rankA := rankF x segs) hL3 hWa hRep3 hrank hrn3 hrN3 hLn hBB
      (fun u hu => by rw [getD_encList_bv u hu]; exact (x.W.branchVert _).2)
      (fun v hv => lt_of_mem_encList_w (segs := segs) (by omega) hv) (by omega)
      (fun v hv => by have := rankF_lt (segs := segs) hv; omega)
      (fun v hv => by
        have : repvF x segs v < x.n := by rw [repvF, repv_eq hF hv]; exact (cRep _ _ _).2
        omega)
  rw [keyArr_eq_compKey hF] at hK4
  -- 5. the look-up
  have hκ : compKey x segs ∈ keys92 h k :=
    mem_lists _ _ (length_compKey_le hF hs) (fun v hv => le_of_mem_compKey hF hs hv)
  have hT := le_tsum92 (l := l) (m := m) (p := p) (r := r) hκ
  have hAw : ∀ v ∈ ans92 l m p h k r (compKey x segs), v < 2 ^ w := fun v hv => by
    have := List.le_sum_of_mem hv; omega
  obtain ⟨s5, t5, ex5, ht5, hKP5, ha5, hr5⟩ :=
    padProg_exec (s := s4) (w := w) (Λ := keyLen92 h k) hK4 (length_compKey_le hF hs)
      (fun v hv => by have := le_of_mem_compKey hF hs hv; omega) (by omega)
  obtain ⟨s6, t6, ex6, ht6, hA6, ha6, hr6⟩ :=
    dispatchK_exec (s := s5) (w := w) (Λ := keyLen92 h k) (B := bound92 h k)
      (ans := ans92 l m p h k r) hKP5 (length_compKey_le hF hs)
      (fun v hv => le_of_mem_compKey hF hs hv) (by omega) (by omega) hAw (keys92 h k)
      (fun κ hκ => le_of_mem_lists hκ) hκ
  -- the arrays and registers that the lift reads
  have hfr : ∀ a, a ≠ aKP → a ≠ aAns → a ≠ aK → a ≠ aKey → s6.arrs a = s3.arrs a := fun a h1 h2 h3 h4 => by
    rw [ha6 a h2, ha5 a h1, ha4 a h3 h4]
  have hN6 : s6.arrs aN = tab (x.n + 1) (fun v => if ndB x segs v then 1 else 0) := by
    rw [hfr aN (by decide) (by decide) (by decide) (by decide),
      ha3 aN (by decide) (by decide) (by decide), ha2 aN (by decide) (by decide) (by decide), hN1]
  have hP6 : s6.arrs aP = tab (x.n + 1) (fun v => if onpB x segs v then 1 else 0) := by
    rw [hfr aP (by decide) (by decide) (by decide) (by decide),
      ha3 aP (by decide) (by decide) (by decide), hP2]
  have hRS6 : s6.arrs aRS = tab (x.n + 1)
      (rsF (ndB x segs) (layout x segs) (layout x segs).length) := by
    rw [hfr aRS (by decide) (by decide) (by decide) (by decide),
      ha3 aRS (by decide) (by decide) (by decide), hRS2]
  have hEn6 : s6.arrs aEn = tab (layout x segs).length
      (enF (ndB x segs) (layout x segs) (layout x segs).length) := by
    rw [hfr aEn (by decide) (by decide) (by decide) (by decide),
      ha3 aEn (by decide) (by decide) (by decide), hEn2]
  have hL6 : s6.arrs aL = layout x segs := by
    rw [hfr aL (by decide) (by decide) (by decide) (by decide), hL3]
  have hRep6 : s6.arrs aRep = tab x.n (repvF x segs) := by
    rw [hfr aRep (by decide) (by decide) (by decide) (by decide), hRep3]; rfl
  have hRank6 : s6.arrs aRank = tab x.n (rankF x segs) := by
    rw [hfr aRank (by decide) (by decide) (by decide) (by decide), hrank]
  have hE6 : s6.arrs aE = tab x.n
      (fun c => (vlist (ndB x segs) (onpB x segs) (repF x segs) x.n).getD c 0) := by
    rw [hfr aE (by decide) (by decide) (by decide) (by decide), hE3]
  have hrn6 : s6.regs rn = x.n := by
    rw [hr6, hr5 rn (by decide) (by decide) (by decide) (by decide),
      hr4 rn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hrn3]
  have hrN6 : s6.regs rN = (fVerts x segs).card := by
    rw [hr6, hr5 rN (by decide) (by decide) (by decide) (by decide),
      hr4 rN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hrN3]
  -- the answer is correct for the compressed input
  have hout := isAlg92Output_tableK hex hF
  have hBM : (fBlobMap x segs).IsBlobMap (compressInput hF).G x.G :=
    isBlobMap_cBlobMap _ _ hF.isPathSystem hF.isCompression.inj hF.isCompression.mem_cVerts
      hF.isCompression.e_ι
  have hBW : (fBlobMap x segs).IsWallBlobMap (compressInput hF).W x.W :=
    hF.isCompression.isWallBlobMap_cBlobMap
  have htime : ∀ t7, t7 ≤ (20 + 13 * p + 33 * (p * x.n)) +
      (60 + l * (37 + tsum92 l m p h k r * (67 + 15 * (layout x segs).length)) +
        17 * (tsum92 l m p h k r * ((layout x segs).length + 1) + 3)) →
      t1 + (t2 + (t3 + (t4 + (t5 + (t6 + ((Expr.read aAns (.const 0)).cost + t7)))))) ≤
        afterTime l m p h k r x.n (layout x segs).length (buildTime x segs) := by
    intro t7 ht7
    unfold afterTime
    simp only [Expr.cost]
    omega
  generalize hAdef : ans92 l m p h k r (compKey x segs) = A at hAw hA6 hT
  have hAeq : tableK h l m p k r (compKey x segs) = A := hAdef
  rw [hAeq] at hout
  have hAT : A.length ≤ tsum92 l m p h k r := by omega
  have e2 : A.length * ((layout x segs).length + 1) ≤
      tsum92 l m p h k r * ((layout x segs).length + 1) := Nat.mul_le_mul_right _ hAT
  have hrk : ∀ u < x.n, rankF x segs u < 2 ^ w := fun u hu => by
    have := rankF_lt (segs := segs) hu; omega
  rcases hout with ⟨c, rays, hAc, hrays, hdisj, hfar⟩ | ⟨K, hAK, hK⟩
  · -- the star
    obtain ⟨h1, h2, h3⟩ := BlobMap.isStarRay_liftRay hBM hBW hl hrays hdisj hfar
    have hA0 : A = 0 :: c.val :: ((((List.finRange l).map (fun i => (rays i).map Fin.val)).map
        lenPre).flatten) := by rw [hAc, encHPaths_eq]
    have hc : c.val < (fVerts x segs).card := c.2
    have hcond : (Expr.read aAns (.const 0)).eval w s6 = some 0 :=
      ev_read (ev_const (by omega)) (by rw [hA6, hA0]; simp) (by rw [hA6, hA0]; rfl) (by omega)
    obtain ⟨s7, t7, ex7, ht7, hout7, -⟩ := starProg_exec (s := s6) (w := w) (l := l) (n := x.n)
      (E := vlist (ndB x segs) (onpB x segs) (repF x segs) x.n) (L := layout x segs)
      (nd := ndB x segs) (rsA := rsF (ndB x segs) (layout x segs) (layout x segs).length)
      (enA := enF (ndB x segs) (layout x segs) (layout x segs).length) (rankA := rankF x segs)
      (c := c.val) (rays := (List.finRange l).map (fun i => (rays i).map Fin.val))
      hE6 hN6 hRS6 hEn6 hL6 hRank6 (by rw [hA6, hA0]) (by simp) (by omega)
      (by rw [getD_vlist_eq_fE hF ⟨c.val, hc⟩]; exact (fE _ _ _).2)
      (fun r hr v hv => by
        simp only [List.mem_map, List.mem_finRange, true_and] at hr
        obtain ⟨i, rfl⟩ := hr
        rw [List.mem_map] at hv
        obtain ⟨u, -, rfl⟩ := hv
        exact goodV_of_fVerts hF u)
      hLw (by rw [← hA0]; exact hAw) hrk
      (fun u hu => by have := (mem_vlist.mp hu).1; omega) (by rw [← hA0]; omega)
    rw [← hA0] at ht7
    refine ⟨s7, _, .seq ex1 (.seq ex2 (.seq ex3 (.seq ex4 (.seq ex5 (.seq ex6
      (.ite_false hcond ex7)))))), htime t7 ?_, ?_⟩
    · have e1 : l * (37 + A.length * (67 + 15 * (layout x segs).length)) ≤
          l * (37 + tsum92 l m p h k r * (67 + 15 * (layout x segs).length)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ hAT) _)
      omega
    · have hlift := liftRays_eq_encHPaths hF (l' := l) (x := x) (segs := segs) rays
      rw [hout7, getD_vlist_eq_fE hF ⟨c.val, hc⟩]
      exact Or.inl ⟨(fBlobMap x segs).node c, fun i => (fBlobMap x segs).liftRay (rays i),
        congrArg _ (congrArg _ hlift), h1, h2, h3⟩
  · -- the model
    have hcond : (Expr.read aAns (.const 0)).eval w s6 = some 1 :=
      ev_read (ev_const (by omega)) (by rw [hA6, hAK]; simp) (by rw [hA6, hAK]; rfl) (by omega)
    obtain ⟨s7, t7, ex7, ht7, hout7, -⟩ := modelProg_exec (s := s6) (w := w) (p := p) (n := x.n)
      (N := (fVerts x segs).card) (nd := ndB x segs) (onp := onpB x segs) (repA := repvF x segs)
      (rankA := rankF x segs) (A := A) hN6 hP6 hRep6 hRank6 hA6 hAw hrn6 hrN6
      (by rw [hAK]; exact modelRange hF K) hrk (by omega)
    refine ⟨s7, _, .seq ex1 (.seq ex2 (.seq ex3 (.seq ex4 (.seq ex5 (.seq ex6
      (.ite_true hcond one_ne_zero ex7)))))), htime t7 (by omega), ?_⟩
    have hlift := mOut_eq_lift hF (x := x) (segs := segs) (p := p) K
    rw [hout7, hAK]
    exact Or.inr ⟨fun i => (fBlobMap x segs).liftSet (K i), hlift,
      BlobMap.isCliqueModel_liftSets hBM hK⟩

end Alg92

end GraphMinor.Compute
