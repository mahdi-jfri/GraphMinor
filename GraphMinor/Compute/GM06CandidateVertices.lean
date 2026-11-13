module

public import GraphMinor.Compute.GM06Reduction4Contacts
public import GraphMinor.Compute.GM06CutNeighbourMarks
public import GraphMinor.Compute.GM13SocietyTabulate
import GraphMinor.Compute.GM06CutFaceInput

/-!
# Deleting the opposite boundary and retained tail

Section 12 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) keeps
precisely face-incident vertices outside the opposite boundary and the strict
retained tail. The program copies that tail from the linkage row,
marks both forbidden sets, and computes the retained-vertex bits.
The forbidden sets and the vertex decision are computed from the
input lists, rather than supplied as search certificates.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Dense vertex table for the exact candidate graph of Section 12. -/
def gm06CandidateVertexBits (n : ℕ) (incV upper path : List ℕ) (j : ℕ) : List ℕ :=
  List.ofFn (fun v : Fin n => if gm06CandidateVertex incV upper path j v then 1 else 0)

/-- The candidate table has every permanent vertex slot. -/
theorem gm06CandidateVertexBits_length (n : ℕ) (incV upper path : List ℕ) (j : ℕ) :
    (gm06CandidateVertexBits n incV upper path j).length = n := by
  simp only [gm06CandidateVertexBits, List.length_ofFn]

/-- Dense membership marking also accepts bounded natural-number labels. -/
theorem gm06IncidenceBitsProg_exec_words {w n : ℕ} (src dst size : ℕ) (hne : src ≠ dst)
    (labels : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hn : n < 2 ^ w) (hl : labels.length < 2 ^ w)
    (hkeys : ∀ x ∈ labels, x < n) (hsize : s.regs size = n) (hsrc : s.arrs src = labels) :
    ∃ sf t, Exec w (gm06IncidenceBitsProg src dst size) s sf t ∧
      t ≤ n + 10 + 14 * labels.length ∧ Keeps [610, 611, 612] [dst] s sf ∧
      sf.arrs dst = gm06IncidenceBits n labels := by
  have hvals := gm06FinLabels_map_val n labels hkeys
  have hlen : (gm06FinLabels n labels).length = labels.length := by
    simpa only [List.length_map] using congrArg List.length hvals
  obtain ⟨sf, t, he, ht, hk, hd⟩ := gm06IncidenceBitsProg_exec src dst size hne
    (gm06FinLabels n labels) s hw hn (by simpa only [hlen] using hl) hsize (hsrc.trans hvals.symm)
  exact ⟨sf, t, he, by simpa only [hlen] using ht, hk, by simpa only [hvals] using hd⟩

/-- Copy precisely the linkage vertices strictly after contact 673. -/
def gm06CandidateTailProg : Cmd :=
  gm13TabulateProg 650 (.op .sub (.len 609) (.op .add (.reg 673) (.const 1)))
    (.read 609 (.op .add (.reg 650) (.op .add (.reg 673) (.const 1)))) 611

/-- The tail copy reads the actual path and retains its order. -/
theorem gm06CandidateTailProg_exec {w j : ℕ} (path : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hlen : path.length < 2 ^ w) (hj : j < path.length)
    (hwords : ∀ x ∈ path, x < 2 ^ w) (h609 : s.arrs 609 = path) (h673 : s.regs 673 = j) :
    ∃ sf t, Exec w gm06CandidateTailProg s sf t ∧ t ≤ 14 + 22 * path.length ∧
      Keeps [650] [611] s sf ∧ sf.arrs 611 = path.drop (j + 1) := by
  have htlen : (path.drop (j + 1)).length = path.length - (j + 1) := List.length_drop
  obtain ⟨sf, t, he, ht, hk, hd⟩ := gm13TabulateProg_exec 650
    (.op .sub (.len 609) (.op .add (.reg 673) (.const 1)))
    (.read 609 (.op .add (.reg 650) (.op .add (.reg 673) (.const 1)))) 611
    (path.drop (j + 1)) s hw (by rw [htlen]; omega)
    (fun st hk => by
      rw [htlen]
      exact GraphMinor.Compute.Crossing.eval_sub
        (GraphMinor.Compute.Crossing.eval_len ((hk.2 609 (by decide)).trans h609) hlen)
        (GraphMinor.Compute.Crossing.eval_add
          (GraphMinor.Compute.Crossing.eval_reg ((hk.1 673 (by decide)).trans h673) (by omega))
          (GraphMinor.Compute.Crossing.eval_const hw) (by omega)))
    (fun st i hi hk hr => by
      have hi' : i < path.length - (j + 1) := htlen ▸ hi
      have hindex : i + (j + 1) < path.length := by omega
      have ha := (hk.2 609 (by decide)).trans h609
      have hx := GraphMinor.Compute.Crossing.eval_add
        (GraphMinor.Compute.Crossing.eval_reg hr (by omega))
        (GraphMinor.Compute.Crossing.eval_add
          (GraphMinor.Compute.Crossing.eval_reg ((hk.1 673 (by decide)).trans h673) (by omega))
          (GraphMinor.Compute.Crossing.eval_const hw) (by omega)) (hindex.trans hlen)
      have he := GraphMinor.Compute.Crossing.eval_read (a := 609) hx (by simpa only [ha] using hindex)
        (by simpa only [ha] using hwords _ (List.getElem_mem hindex))
      simpa only [ha, List.getElem_drop, Nat.add_comm] using he)
  refine ⟨sf, t, he, ?_, hk, hd⟩
  simp only [Expr.cost, htlen] at ht
  omega

/-- Read incidence and both computed forbidden-set bitmaps. -/
def gm06CandidateVertexExpr : Expr :=
  exprAnd (exprAnd (exprNe (.read 606 (.reg 650)) (.const 0))
    (exprNot (.read 623 (.reg 650)))) (exprNot (.read 615 (.reg 650)))

/-- The three RAM tests have exactly the retained-vertex meaning. -/
theorem gm06CandidateVertexExpr_eval {w n j v : ℕ} (incV upper path : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hv : v < n)
    (hVlen : incV.length = n) (hwords : ∀ x ∈ incV, x < 2 ^ w)
    (h606 : s.arrs 606 = incV) (h623 : s.arrs 623 = gm06IncidenceBits n upper)
    (h615 : s.arrs 615 = gm06IncidenceBits n (path.drop (j + 1))) (h650 : s.regs 650 = v) :
    gm06CandidateVertexExpr.eval w s =
      some (if gm06CandidateVertex incV upper path j v then 1 else 0) := by
  have hv' : v < incV.length := hVlen ▸ hv
  have hx := GraphMinor.Compute.Crossing.eval_reg h650 (hv.trans hn)
  have hread := GraphMinor.Compute.Crossing.eval_read (a := 606) hx
    (by simpa only [h606] using hv')
    (by simpa only [h606] using hwords _ (List.getElem_mem hv'))
  have hinc : (exprNe (.read 606 (.reg 650)) (.const 0)).eval w s =
      some (if incV[v]?.getD 0 ≠ 0 then 1 else 0) := by
    simpa only [h606, List.getElem?_eq_getElem hv', Option.getD_some, ne_eq, ite_not] using
      eval_exprNe hw hread (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hupper := eval_exprNot hw (gm06ReadBits_eval upper s (.reg 650) hw hv hx h623)
  have htail := eval_exprNot hw (gm06ReadBits_eval (path.drop (j + 1)) s (.reg 650) hw hv hx h615)
  have he := eval_exprAnd hw (eval_exprAnd hw hinc hupper) htail
  simpa only [gm06CandidateVertexExpr, gm06CandidateVertex_iff, and_assoc] using he

/-- Build forbidden-set bitmaps, then compute the candidate vertices. -/
def gm06CandidateVerticesProg : Cmd :=
  .seq gm06CandidateTailProg
    (.seq (gm06IncidenceBitsProg 611 615 620)
      (.seq (gm06IncidenceBitsProg 608 623 620)
        (gm13TabulateProg 650 (.reg 620) gm06CandidateVertexExpr 619)))

/-- The RAM constructs exactly the candidate-vertex table from the
incidence and boundary/path rows, with a linear time bound. -/
theorem gm06CandidateVerticesProg_exec {w n j : ℕ} (incV upper path : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hlen : path.length < 2 ^ w)
    (hupperLen : upper.length < 2 ^ w) (hj : j < path.length)
    (hVlen : incV.length = n) (hVwords : ∀ x ∈ incV, x < 2 ^ w)
    (hpath : ∀ x ∈ path, x < n) (hupper : ∀ x ∈ upper, x < n)
    (h606 : s.arrs 606 = incV) (h608 : s.arrs 608 = upper) (h609 : s.arrs 609 = path)
    (h620 : s.regs 620 = n) (h673 : s.regs 673 = j) :
    ∃ sf t, Exec w gm06CandidateVerticesProg s sf t ∧
      t ≤ 100 * (n + path.length + upper.length + 1) ∧
      Keeps [650, 610, 611, 612] [611, 615, 623, 619] s sf ∧
      sf.arrs 619 = gm06CandidateVertexBits n incV upper path j := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm06CandidateTailProg_exec path s hw hlen hj
    (fun x hx => (hpath x hx).trans hn) h609 h673
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩ := gm06IncidenceBitsProg_exec_words
    611 615 620 (by decide) (path.drop (j + 1)) s₁ hw hn
    (by rw [List.length_drop]; omega)
    (fun x hx => hpath x (List.mem_of_mem_drop hx)) ((hk₁.1 620 (by decide)).trans h620) hd₁
  have hk₁₂ : Keeps [650, 610, 611, 612] [611, 615] s s₂ :=
    (hk₁.mono (by simp) (by simp)).trans hk₂ (by simp) (by simp)
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hd₃⟩ := gm06IncidenceBitsProg_exec_words
    608 623 620 (by decide) upper s₂ hw hn hupperLen hupper
    ((hk₁₂.1 620 (by decide)).trans h620) ((hk₁₂.2 608 (by decide)).trans h608)
  have hk₁₃ : Keeps [650, 610, 611, 612] [611, 615, 623] s s₃ :=
    (hk₁₂.mono (fun _ h => h) (by simp)).trans hk₃ (by simp) (by simp)
  let out := gm06CandidateVertexBits n incV upper path j
  have houtlen : out.length = n := gm06CandidateVertexBits_length n incV upper path j
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm13TabulateProg_exec
    650 (.reg 620) gm06CandidateVertexExpr 619 out s₃ hw (houtlen ▸ hn)
    (fun st hk => by
      rw [houtlen]
      exact GraphMinor.Compute.Crossing.eval_reg
        ((hk.1 620 (by decide)).trans ((hk₁₃.1 620 (by decide)).trans h620)) hn)
    (fun st i hi hk hr => by
      have hin : i < n := houtlen ▸ hi
      have he := gm06CandidateVertexExpr_eval incV upper path st hw hn hin hVlen hVwords
        ((hk.2 606 (by decide)).trans ((hk₁₃.2 606 (by decide)).trans h606))
        ((hk.2 623 (by decide)).trans hd₃)
        ((hk.2 615 (by decide)).trans ((hk₃.2 615 (by decide)).trans hd₂)) hr
      simpa only [out, gm06CandidateVertexBits, List.getElem_ofFn] using he)
  refine ⟨sf, t₁ + (t₂ + (t₃ + tf)), .seq he₁ (.seq he₂ (.seq he₃ hef)), ?_,
    (hk₁₃.mono (fun _ h => h) (by simp)).trans hkf (by simp) (by simp), hdf⟩
  · have hdrop : (path.drop (j + 1)).length ≤ path.length := by
      rw [List.length_drop]
      omega
    have hcost : gm06CandidateVertexExpr.cost ≤ 30 := by decide
    simp only [Expr.cost, houtlen] at htf
    have hmul := Nat.mul_le_mul_left n hcost
    simp only [Nat.mul_add, Nat.mul_one] at htf
    omega

end GraphMinor.Compute
