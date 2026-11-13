module

public import GraphMinor.Compute.GM06CutActiveBits
public import GraphMinor.Compute.GM06FaceSuccessors
public import GraphMinor.Compute.GM06Alg34CrossExpr

/-!
# Computing neighbour membership from a copied rotation row

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) obtains
adjacency from copied outgoing ends. The other endpoint of dart d is the origin
of its reverse. This scan marks those neighbours whose two directed
ends and two vertices are active, excluding loops from the search
graph. A dense bitmap removes repeated neighbours from parallel
edges. The edge and dart labels remain in the cut data for later use.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- The other endpoint read through a copied dart's reverse. -/
def gm06CutNeighbourHead (origins : List ℕ) (d : ℕ) : ℕ := origins[gm06DartMate d]?.getD 0

/-- Keep a search neighbour exactly when both ends and vertices are
active and the edge does not return to its starting vertex. -/
def gm06CutNeighbourKeep (origins active live : List ℕ) (u d : ℕ) : Bool :=
  decide (d ∈ active ∧ gm06DartMate d ∈ active ∧ u ∈ live ∧
    gm06CutNeighbourHead origins d ∈ live ∧ gm06CutNeighbourHead origins d ≠ u)

/-- The neighbour candidates of a row, retaining repeats from parallel edges. -/
def gm06CutNeighbourCandidates (origins active live : List ℕ) (u : ℕ) (row : List ℕ) : List ℕ :=
  (row.filter (gm06CutNeighbourKeep origins active live u)).map (gm06CutNeighbourHead origins)

/-- One more processed dart appends exactly its possible neighbour. -/
theorem gm06CutNeighbourCandidates_take_succ (origins active live row : List ℕ) (u i : ℕ) (hi : i < row.length) :
    gm06CutNeighbourCandidates origins active live u (row.take (i + 1)) =
      gm06CutNeighbourCandidates origins active live u (row.take i) ++
        (if gm06CutNeighbourKeep origins active live u row[i] then [gm06CutNeighbourHead origins row[i]] else []) := by
  rw [gm06CutNeighbourCandidates, List.take_succ_eq_append_getElem hi, List.filter_append, List.map_append]
  cases h : gm06CutNeighbourKeep origins active live u row[i] <;> simp [h, gm06CutNeighbourCandidates]

/-- Read a dense finite membership bit through an evaluated word index. -/
theorem gm06ReadBits_eval {w q a d : ℕ} (labels : List ℕ) (s : State) (idx : Expr)
    (hw : 1 < 2 ^ w) (hd : d < q) (he : idx.eval w s = some d)
    (ha : s.arrs a = gm06IncidenceBits q labels) :
    (Expr.read a idx).eval w s = some (if d ∈ labels then 1 else 0) := by
  have hi : d < (s.arrs a).length := by simpa [ha, gm06IncidenceBits] using hd
  have hg : (s.arrs a)[d]'hi = (if d ∈ labels then 1 else 0) := by simp [ha, gm06IncidenceBits]
  have hr := GraphMinor.Compute.Crossing.eval_read he hi (by rw [hg]; split_ifs <;> omega)
  simpa only [hg] using hr

/-- Runtime active-end, live-vertex and nonloop guard for a copied dart. -/
def gm06CutNeighbourGuard : Expr :=
  exprAnd (.read 627 (.reg 651))
    (exprAnd (.read 627 (.reg 652))
      (exprAnd (.read 619 (.reg 666))
        (exprAnd (.read 619 (.reg 653)) (exprNe (.reg 653) (.reg 666)))))

/-- The guard computes exactly the finite candidate predicate. -/
theorem gm06CutNeighbourGuard_eval {w n m u d : ℕ} (origins active live : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w) (hu : u < n) (hd : d < 2 * m)
    (hv : gm06CutNeighbourHead origins d < n)
    (h627 : s.arrs 627 = gm06IncidenceBits (2 * m) active)
    (h619 : s.arrs 619 = gm06IncidenceBits n live)
    (h651 : s.regs 651 = d) (h652 : s.regs 652 = gm06DartMate d)
    (h653 : s.regs 653 = gm06CutNeighbourHead origins d) (h666 : s.regs 666 = u) :
    gm06CutNeighbourGuard.eval w s = some (if gm06CutNeighbourKeep origins active live u d then 1 else 0) := by
  have hed := GraphMinor.Compute.Crossing.eval_reg h651 (hd.trans hm)
  have hem := GraphMinor.Compute.Crossing.eval_reg h652 ((gm06DartMate_lt hd).trans hm)
  have heu := GraphMinor.Compute.Crossing.eval_reg h666 (hu.trans hn)
  have hev := GraphMinor.Compute.Crossing.eval_reg h653 (hv.trans hn)
  have hneq : (exprNe (.reg 653) (.reg 666)).eval w s =
      some (if gm06CutNeighbourHead origins d ≠ u then 1 else 0) := by
    simpa only [ne_eq, ite_not] using eval_exprNe hw hev heu
  have he := eval_exprAnd hw (gm06ReadBits_eval active s (.reg 651) hw hd hed h627)
    (eval_exprAnd hw (gm06ReadBits_eval active s (.reg 652) hw (gm06DartMate_lt hd) hem h627)
      (eval_exprAnd hw (gm06ReadBits_eval live s (.reg 666) hw hu heu h619)
        (eval_exprAnd hw (gm06ReadBits_eval live s (.reg 653) hw hv hev h619) hneq)))
  simpa only [gm06CutNeighbourGuard, gm06CutNeighbourKeep, decide_eq_true_eq] using he

/-- Read a copied end, its reverse and its other vertex, then mark
that vertex when the finite edge/vertex guard passes. -/
def gm06CutNeighbourBody : Cmd :=
  .seq (.assign 651 (.read 611 (.reg 650)))
    (.seq (.assign 652 (gm06DartMateExpr (.reg 651)))
      (.seq (.assign 653 (.read 626 (.reg 652)))
        (.ite gm06CutNeighbourGuard (.write 614 (.reg 653) (.const 1)) .skip)))

/-- Scan one copied rotation into neighbour-membership table 614. -/
def gm06CutNeighbourMarkProg : Cmd :=
  .seq (.assign 650 (.const 0)) (forUp 650 (.len 611) gm06CutNeighbourBody)

/-- Exact neighbour-mark scatter computed from the copied row and
endpoint data. No neighbour list or adjacency certificate is supplied. -/
theorem gm06CutNeighbourMarkProg_exec {w n m u : ℕ} (origins active live row seen : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w) (hu : u < n)
    (hl : row.length < 2 ^ w) (horgLen : origins.length = 2 * m) (hseenLen : seen.length = n)
    (hkeys : ∀ d ∈ row, d < 2 * m) (hvalues : ∀ v ∈ origins, v < n)
    (h611 : s.arrs 611 = row) (h626 : s.arrs 626 = origins) (h614 : s.arrs 614 = seen)
    (h627 : s.arrs 627 = gm06IncidenceBits (2 * m) active)
    (h619 : s.arrs 619 = gm06IncidenceBits n live) (h666 : s.regs 666 = u) :
    ∃ sf t, Exec w gm06CutNeighbourMarkProg s sf t ∧ t ≤ 5 + 107 * row.length ∧
      Keeps [650, 651, 652, 653] [614] s sf ∧
      sf.arrs 614 = gm06Scatter
        ((gm06CutNeighbourCandidates origins active live u row).map (fun v => (v, 1))) seen := by
  have hw1 : 1 < 2 ^ w := by omega
  let scan := fun i => gm06Scatter
    ((gm06CutNeighbourCandidates origins active live u (row.take i)).map (fun v => (v, 1))) seen
  let Inv := fun i st => st.regs 650 = i ∧ Keeps [650, 651, 652, 653] [614] s st ∧ st.arrs 614 = scan i
  let s₀ := s.setReg 650 0
  have hI₀ : Inv 0 s₀ := ⟨by simp [s₀], (Keeps.refl _ _ s).setReg (by simp) _, h614⟩
  obtain ⟨sf, tf, hef, htf, hIf⟩ := GraphMinor.Compute.Crossing.forUp_exec'
    (r_i := 650) (hi := .len 611) (body := gm06CutNeighbourBody) Inv row.length 100 hw1 hl
    (fun _ _ st h => ⟨h.1, GraphMinor.Compute.Crossing.eval_len ((h.2.1.2 611 (by decide)).trans h611) hl⟩)
    (fun i hi st h => by
      obtain ⟨hidx, hk, htable⟩ := h
      have hsrc : st.arrs 611 = row := (hk.2 611 (by decide)).trans h611
      have horg : st.arrs 626 = origins := (hk.2 626 (by decide)).trans h626
      have hd : row[i] < 2 * m := hkeys _ (List.getElem_mem hi)
      have hmate : gm06DartMate row[i] < origins.length := horgLen ▸ gm06DartMate_lt hd
      have hhead : gm06CutNeighbourHead origins row[i] = origins[gm06DartMate row[i]] := by
        simp only [gm06CutNeighbourHead, List.getElem?_eq_getElem hmate, Option.getD_some]
      have hv : gm06CutNeighbourHead origins row[i] < n := by rw [hhead]; exact hvalues _ (List.getElem_mem hmate)
      have hread : (Expr.read 611 (.reg 650)).eval w st = some row[i] := by
        have he := GraphMinor.Compute.Crossing.eval_read (a := 611)
          (GraphMinor.Compute.Crossing.eval_reg hidx (hi.trans hl))
          (by simpa [hsrc] using hi) (by simpa [hsrc] using hd.trans hm)
        simpa only [hsrc] using he
      let st₁ := st.setReg 651 row[i]
      let st₂ := st₁.setReg 652 (gm06DartMate row[i])
      let st₃ := st₂.setReg 653 (gm06CutNeighbourHead origins row[i])
      have he₁ : Exec w (.assign 651 (.read 611 (.reg 650))) st st₁ 3 := .assign hread
      have he₂ : Exec w (.assign 652 (gm06DartMateExpr (.reg 651))) st₁ st₂ 12 :=
        .assign (gm06DartMateExpr_eval hw hm hd (GraphMinor.Compute.Crossing.eval_reg (by simp [st₁]) (hd.trans hm)))
      have hreadHead : (Expr.read 626 (.reg 652)).eval w st₂ = some (gm06CutNeighbourHead origins row[i]) := by
        have he := GraphMinor.Compute.Crossing.eval_read (a := 626) (s := st₂)
          (GraphMinor.Compute.Crossing.eval_reg (r := 652) (by simp [st₂]) ((gm06DartMate_lt hd).trans hm))
          (by simpa [st₂, st₁, horg] using hmate) (by simpa [st₂, st₁, horg, ← hhead] using hv.trans hn)
        simpa only [st₂, st₁, State.setReg_arrs, horg, ← hhead] using he
      have he₃ : Exec w (.assign 653 (.read 626 (.reg 652))) st₂ st₃ 3 := .assign hreadHead
      have hk₃ : Keeps [650, 651, 652, 653] [614] s st₃ :=
        ((hk.setReg (by simp) _).setReg (by simp) _).setReg (by simp) _
      have hcond := gm06CutNeighbourGuard_eval origins active live st₃ hw1 hn hm hu hd hv
        ((hk₃.2 627 (by decide)).trans h627) ((hk₃.2 619 (by decide)).trans h619)
        (by simp [st₃, st₂, st₁]) (by simp [st₃, st₂]) (by simp [st₃])
        ((hk₃.1 666 (by decide)).trans h666)
      have hlen : (st₃.arrs 614).length = n := by simp [st₃, st₂, st₁, htable, scan, gm06Scatter_length, hseenLen]
      have hguard : ∃ st₄ t₄, Exec w (.ite gm06CutNeighbourGuard (.write 614 (.reg 653) (.const 1)) .skip)
          st₃ st₄ t₄ ∧ t₄ ≤ gm06CutNeighbourGuard.cost + 3 ∧
          Keeps [650, 651, 652, 653] [614] s st₄ ∧
          st₄.arrs 614 = (if gm06CutNeighbourKeep origins active live u row[i] then
            (st.arrs 614).set (gm06CutNeighbourHead origins row[i]) 1 else st.arrs 614) ∧
          st₄.regs 650 = i := by
        cases hs : gm06CutNeighbourKeep origins active live u row[i]
        · refine ⟨st₃, gm06CutNeighbourGuard.cost + 1, .ite_false (by simpa [hs] using hcond) (.skip st₃),
            by omega, hk₃, by simp [hs, st₃, st₂, st₁], by simpa [st₃, st₂, st₁] using hidx⟩
        · let st₄ := st₃.writeArr 614 (gm06CutNeighbourHead origins row[i]) 1
          have hew : Exec w (.write 614 (.reg 653) (.const 1)) st₃ st₄ 3 :=
            .write (GraphMinor.Compute.Crossing.eval_reg (by simp [st₃]) (hv.trans hn))
              (GraphMinor.Compute.Crossing.eval_const hw1) (by rw [hlen]; exact hv)
          exact ⟨st₄, gm06CutNeighbourGuard.cost + 3, .ite_true (by simpa [hs] using hcond) (by decide : (1 : ℕ) ≠ 0) hew,
            le_rfl, hk₃.writeArr (by simp) _ _, by simp [st₄, st₃, st₂, st₁, State.writeArr, hs],
            by simpa [st₄, st₃, st₂, st₁, State.writeArr] using hidx⟩
      obtain ⟨st₄, t₄, he₄, ht₄, hk₄, ha₄, hi₄⟩ := hguard
      refine ⟨st₄, 3 + (12 + (3 + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)), ?_,
        ⟨by simp, hk₄.setReg (by simp) _, ?_⟩, hi₄⟩
      · have hc : gm06CutNeighbourGuard.cost + 21 ≤ 100 := by decide
        omega
      · simp only [State.setReg_arrs, ha₄, scan, gm06CutNeighbourCandidates_take_succ _ _ _ _ _ _ hi,
          List.map_append, gm06Scatter_append]
        rw [htable]
        cases hs : gm06CutNeighbourKeep origins active live u row[i] <;> simp [hs, gm06Scatter, scan]) s₀ hI₀
  refine ⟨sf, 2 + tf, .seq (.assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))) hef,
    ?_, hIf.2.1, ?_⟩
  · simp only [Expr.cost] at htf
    omega
  · simpa only [scan, List.take_length] using hIf.2.2

end GraphMinor.Compute
