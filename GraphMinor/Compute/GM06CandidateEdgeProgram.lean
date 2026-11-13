module

public import GraphMinor.Compute.GM06CandidateEdges

/-!
# Computing the retained edge bits of A_(i,j)

Section 12 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) excludes
cuff edges and every edge missing either retained endpoint. The program
reads the ordinary-edge flags, face incidence and computed endpoint
bits. It writes the same decision at both permanent dart slots.
Loops and parallel edge labels are retained in this table even
though the simple BFS graph discards loops and duplicate neighbours.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- The permanent edge label of the dart being tabulated. -/
def gm06CandidateEdgeIndex : Expr := .op .div (.reg 650) (.const 2)

/-- Test ordinary status, face incidence and both retained endpoints. -/
def gm06CandidateEdgeExpr : Expr :=
  exprAnd (.read 624 gm06CandidateEdgeIndex)
    (exprAnd (exprNe (.read 607 gm06CandidateEdgeIndex) (.const 0))
      (exprAnd (.read 619 (.read 626 (.op .mul (.const 2) gm06CandidateEdgeIndex)))
        (.read 619 (.read 626 (.op .add (.op .mul (.const 2) gm06CandidateEdgeIndex) (.const 1))))))

private theorem candidate_read {w n j v : ℕ} (incV upper path : List ℕ) (s : State)
    (idx : Expr) (hw : 1 < 2 ^ w) (hv : v < n) (he : idx.eval w s = some v)
    (ha : s.arrs 619 = gm06CandidateVertexBits n incV upper path j) :
    (Expr.read 619 idx).eval w s =
      some (if gm06CandidateVertex incV upper path j v then 1 else 0) := by
  have hi : v < (s.arrs 619).length := by
    simpa only [ha, gm06CandidateVertexBits_length] using hv
  have hg : (s.arrs 619)[v]'hi = (if gm06CandidateVertex incV upper path j v then 1 else 0) := by
    simp only [ha, gm06CandidateVertexBits, List.getElem_ofFn]
  have hread := GraphMinor.Compute.Crossing.eval_read he hi (by rw [hg]; split <;> omega)
  simpa only [hg] using hread

/-- Every array read in the edge decision agrees with the exact
ordinary, incident, two-retained-endpoint criterion. -/
theorem gm06CandidateEdgeExpr_eval {w n m j d : ℕ} (origins : List ℕ) (ordinary : List Bool)
    (incV incE upper path : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w) (hd : d < 2 * m)
    (horgLen : origins.length = 2 * m) (hvalues : ∀ v ∈ origins, v < n)
    (hordinary : ordinary.length = m) (hElen : incE.length = m)
    (hEwords : ∀ x ∈ incE, x < 2 ^ w)
    (h624 : s.arrs 624 = ordinary.map Bool.toNat) (h607 : s.arrs 607 = incE)
    (h626 : s.arrs 626 = origins) (h619 : s.arrs 619 = gm06CandidateVertexBits n incV upper path j)
    (h650 : s.regs 650 = d) :
    gm06CandidateEdgeExpr.eval w s = some (if d ∈
      gm06CandidateDarts m origins ordinary incV incE upper path j then 1 else 0) := by
  have hw1 : 1 < 2 ^ w := by omega
  let e := d / 2
  have he : e < m := by dsimp only [e]; omega
  have hp : 2 * e < origins.length := by omega
  have hq : 2 * e + 1 < origins.length := by omega
  have hvp : origins[2 * e] < n := hvalues _ (List.getElem_mem hp)
  have hvq : origins[2 * e + 1] < n := hvalues _ (List.getElem_mem hq)
  have heval : gm06CandidateEdgeIndex.eval w s = some e := by
    exact GraphMinor.Compute.Crossing.eval_div
      (GraphMinor.Compute.Crossing.eval_reg h650 (hd.trans hm))
      (GraphMinor.Compute.Crossing.eval_const hw) (by decide) (by omega)
  have hpos : (Expr.op .mul (.const 2) gm06CandidateEdgeIndex).eval w s = some (2 * e) :=
    GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw) heval (by omega)
  have hneg : (Expr.op .add (.op .mul (.const 2) gm06CandidateEdgeIndex) (.const 1)).eval w s =
      some (2 * e + 1) := GraphMinor.Compute.Crossing.eval_add hpos
        (GraphMinor.Compute.Crossing.eval_const hw1) (by omega)
  have hreadP := GraphMinor.Compute.Crossing.eval_read (a := 626) hpos
    (by simpa only [h626] using hp) (by simpa only [h626] using hvp.trans hn)
  have hreadQ := GraphMinor.Compute.Crossing.eval_read (a := 626) hneg
    (by simpa only [h626] using hq) (by simpa only [h626] using hvq.trans hn)
  have hP := candidate_read incV upper path s
    (.read 626 (.op .mul (.const 2) gm06CandidateEdgeIndex)) hw1 hvp
    (by simpa only [h626] using hreadP) h619
  have hQ := candidate_read incV upper path s
    (.read 626 (.op .add (.op .mul (.const 2) gm06CandidateEdgeIndex) (.const 1))) hw1 hvq
    (by simpa only [h626] using hreadQ) h619
  have heOrd : e < ordinary.length := hordinary ▸ he
  have heInc : e < incE.length := hElen ▸ he
  have hOrd : (Expr.read 624 gm06CandidateEdgeIndex).eval w s =
      some (if ordinary[e] then 1 else 0) := by
    have hget : (s.arrs 624)[e]'(by simp only [h624, List.length_map]; exact heOrd) =
        (if ordinary[e] then 1 else 0) := by
      simp only [h624, List.getElem_map]
      cases ordinary[e] <;> rfl
    have hr := GraphMinor.Compute.Crossing.eval_read (a := 624) heval
      (by simp only [h624, List.length_map]; exact heOrd) (by rw [hget]; split <;> omega)
    simpa only [hget] using hr
  have hInc : (exprNe (.read 607 gm06CandidateEdgeIndex) (.const 0)).eval w s =
      some (if gm06Incident incE e then 1 else 0) := by
    have hr := GraphMinor.Compute.Crossing.eval_read (a := 607) heval
      (by simpa only [h607] using heInc) (by simpa only [h607] using hEwords _ (List.getElem_mem heInc))
    simpa only [h607, gm06Incident, List.getElem?_eq_getElem heInc, Option.getD_some,
      bne_iff_ne, ne_eq, ite_not] using eval_exprNe hw1 hr
        (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hresult := eval_exprAnd hw1 hOrd (eval_exprAnd hw1 hInc (eval_exprAnd hw1 hP hQ))
  have hends := gm06CandidateEnds_get origins he
  have hcriterion : (d ∈ gm06CandidateDarts m origins ordinary incV incE upper path j) ↔
      ordinary[e] = true ∧ gm06Incident incE e = true ∧
        gm06CandidateVertex incV upper path j origins[2 * e] = true ∧
        gm06CandidateVertex incV upper path j origins[2 * e + 1] = true := by
    rw [gm06CandidateDarts_mem_iff]
    change (d < 2 * m ∧ e ∈ gm06CandidateEdges (gm06CandidateEnds m origins) ordinary
      incV incE upper path j) ↔ _
    rw [gm06CandidateEdges_mem_iff]
    simp only [hd, true_and, gm06CandidateEnds_length, he, hends,
      List.getElem?_eq_getElem heOrd, List.getElem?_eq_getElem hp, List.getElem?_eq_getElem hq,
      Option.getD_some, gm06Incident, bne_iff_ne]
  simpa only [gm06CandidateEdgeExpr, ← hcriterion] using hresult

/-- Tabulate both directed slots of every retained edge in 627. -/
def gm06CandidateEdgeBitsProg : Cmd :=
  gm13TabulateProg 650 (.op .mul (.const 2) (.reg 649)) gm06CandidateEdgeExpr 627

/-- The edge pass computes exactly the complete-pair candidate bitmap,
with linear time in the permanent edge space. -/
theorem gm06CandidateEdgeBitsProg_exec {w n m j : ℕ} (origins : List ℕ) (ordinary : List Bool)
    (incV incE upper path : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (horgLen : origins.length = 2 * m) (hvalues : ∀ v ∈ origins, v < n)
    (hordinary : ordinary.length = m) (hElen : incE.length = m)
    (hEwords : ∀ x ∈ incE, x < 2 ^ w)
    (h624 : s.arrs 624 = ordinary.map Bool.toNat) (h607 : s.arrs 607 = incE)
    (h626 : s.arrs 626 = origins) (h619 : s.arrs 619 = gm06CandidateVertexBits n incV upper path j)
    (h649 : s.regs 649 = m) :
    ∃ sf t, Exec w gm06CandidateEdgeBitsProg s sf t ∧ t ≤ 10 + 150 * m ∧
      Keeps [650] [627] s sf ∧ sf.arrs 627 =
        gm06IncidenceBits (2 * m) (gm06CandidateDarts m origins ordinary incV incE upper path j) := by
  let out := gm06IncidenceBits (2 * m) (gm06CandidateDarts m origins ordinary incV incE upper path j)
  have hlen : out.length = 2 * m := by simp only [out, gm06IncidenceBits, List.length_ofFn]
  obtain ⟨sf, t, he, ht, hk, hd⟩ := gm13TabulateProg_exec
    650 (.op .mul (.const 2) (.reg 649)) gm06CandidateEdgeExpr 627 out s (by omega) (hlen ▸ hm)
    (fun st hk => by
      rw [hlen]
      exact GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw)
        (GraphMinor.Compute.Crossing.eval_reg ((hk.1 649 (by decide)).trans h649) (by omega)) hm)
    (fun st i hi hk hr => by
      have hi' : i < 2 * m := hlen ▸ hi
      have he := gm06CandidateEdgeExpr_eval origins ordinary incV incE upper path st hw hn hm hi'
        horgLen hvalues hordinary hElen hEwords ((hk.2 624 (by decide)).trans h624)
        ((hk.2 607 (by decide)).trans h607) ((hk.2 626 (by decide)).trans h626)
        ((hk.2 619 (by decide)).trans h619) hr
      simpa only [out, gm06IncidenceBits, List.getElem_ofFn] using he)
  refine ⟨sf, t, he, ?_, hk, hd⟩
  have hcost : gm06CandidateEdgeExpr.cost ≤ 60 := by decide
  simp only [Expr.cost, hlen, Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at ht
  have hmul := Nat.mul_le_mul_left (2 * m) hcost
  simp only [Nat.mul_assoc] at hmul
  omega

end GraphMinor.Compute
