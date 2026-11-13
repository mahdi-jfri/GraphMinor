module

public import GraphMinor.Compute.GM06FaceSuccessors
public import GraphMinor.Compute.GM06FaceIncidence
public import GraphMinor.Compute.GM06WordRows
import GraphMinor.Compute.GM06CandidateVertices

/-!
# Heads and first-contact targets for the terminal face trace

Section 15 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) stops at the
first vertex in the left boundary other than the starting copy, or
in the opposite boundary. This file computes that target bitmap from
the two actual boundary rows, and computes dart heads by reading the
origin of each reverse dart. Repeated boundary vertices cause no
problem for dense membership marking.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Every dart's head is the origin of its reverse. -/
def gm06DartHeads (origins : List ℕ) : List ℕ :=
  (List.range origins.length).map (fun d => origins[gm06DartMate d]?.getD 0)

/-- The head table covers the full permanent dart space. -/
theorem gm06DartHeads_length (origins : List ℕ) : (gm06DartHeads origins).length = origins.length := by
  simp only [gm06DartHeads, List.length_map, List.length_range]

/-- Every valid head lookup agrees with the reverse-origin definition. -/
theorem gm06DartHeads_get {d : ℕ} (origins : List ℕ) (hd : d < origins.length) :
    (gm06DartHeads origins)[d]?.getD 0 = origins[gm06DartMate d]?.getD 0 := by
  have hi : d < (gm06DartHeads origins).length := by simpa only [gm06DartHeads_length] using hd
  rw [List.getElem?_eq_getElem hi]
  simp only [Option.getD_some, gm06DartHeads, List.getElem_map, List.getElem_range]

/-- Proper origin labels give proper head labels throughout the table. -/
theorem gm06DartHeads_bounds {n m : ℕ} (origins : List ℕ) (hlen : origins.length = 2 * m)
    (hvalues : ∀ v ∈ origins, v < n) : ∀ v ∈ gm06DartHeads origins, v < n := by
  intro v hv
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
  have hd' : d < 2 * m := hlen ▸ List.mem_range.mp hd
  have hm : gm06DartMate d < origins.length := hlen ▸ gm06DartMate_lt hd'
  simpa only [List.getElem?_eq_getElem hm, Option.getD_some] using hvalues _ (List.getElem_mem hm)

/-- Compute heads 601 from permanent origins 626. -/
def gm06DartHeadsProg : Cmd :=
  gm13TabulateProg 650 (.len 626) (.read 626 (gm06DartMateExpr (.reg 650))) 601

/-- Exact head construction has linear cost in the permanent dart space. -/
theorem gm06DartHeadsProg_exec {w n m : ℕ} (origins : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hlen : origins.length = 2 * m) (hvalues : ∀ v ∈ origins, v < n) (h626 : s.arrs 626 = origins) :
    ∃ sf t, Exec w gm06DartHeadsProg s sf t ∧ t ≤ 6 + 30 * (2 * m) ∧
      Keeps [650] [601] s sf ∧ sf.arrs 601 = gm06DartHeads origins := by
  have houtlen : (gm06DartHeads origins).length = 2 * m := (gm06DartHeads_length origins).trans hlen
  obtain ⟨sf, t, he, ht, hk, hd⟩ := gm13TabulateProg_exec (w := w) 650 (.len 626)
    (.read 626 (gm06DartMateExpr (.reg 650))) 601 (gm06DartHeads origins) s (by omega) (houtlen ▸ hm)
    (fun st hk => by
      simpa only [gm06DartHeads_length] using
        GraphMinor.Compute.Crossing.eval_len ((hk.2 626 (by decide)).trans h626) (hlen ▸ hm))
    (fun st i hi hk hr => by
      have hi' : i < 2 * m := houtlen ▸ hi
      have hmate : gm06DartMate i < origins.length := hlen ▸ gm06DartMate_lt hi'
      have hv : origins[gm06DartMate i] < n := hvalues _ (List.getElem_mem hmate)
      have ha := (hk.2 626 (by decide)).trans h626
      have he := GraphMinor.Compute.Crossing.eval_read (a := 626)
        (gm06DartMateExpr_eval hw hm hi' (GraphMinor.Compute.Crossing.eval_reg (w := w) hr (hi'.trans hm)))
        (by simpa only [ha] using hmate) (by simpa only [ha] using hv.trans hn)
      have hout := gm06DartHeads_get origins (hlen ▸ hi')
      rw [List.getElem?_eq_getElem hi] at hout
      have he' : (Expr.read 626 (gm06DartMateExpr (.reg 650))).eval w st =
          some (origins[gm06DartMate i]?.getD 0) := by
        simpa only [ha, List.getElem?_eq_getElem hmate, Option.getD_some] using he
      simpa only [Option.getD_some] using he'.trans (congrArg some hout.symm))
  exact ⟨sf, t, he, by simp only [Expr.cost, gm06DartMateExpr, houtlen] at ht; omega, hk, hd⟩

/-- Targets are all opposite-boundary vertices and left-boundary vertices
other than the selected starting copy. -/
def gm06TerminalTargetLabels (source : ℕ) (left upper : List ℕ) : List ℕ :=
  left.filter (fun v => v != source) ++ upper

/-- The finite target list states exactly the set T_i of Section 15. -/
theorem gm06TerminalTargetLabels_mem (source : ℕ) (left upper : List ℕ) (v : ℕ) :
    v ∈ gm06TerminalTargetLabels source left upper ↔ (v ∈ left ∧ v ≠ source) ∨ v ∈ upper := by
  simp only [gm06TerminalTargetLabels, List.mem_append, List.mem_filter, bne_iff_ne]

private theorem filter_flatMap (xs : List ℕ) (keep : ℕ → Bool) :
    xs.flatMap (fun x => if keep x then [x] else []) = xs.filter keep := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hx : keep x <;> simp [hx, ih]

/-- Filter source 606 out of left row 609, append upper row 608,
then build the exact dense target bits in array 602. -/
def gm06TerminalTargetsProg : Cmd :=
  .seq (.alloc 604 (.op .add (.len 609) (.len 608)))
    (.seq (.assign 655 (.const 0))
      (.seq (gm06FilterMapArrayProg 609 604 650 651 652 655 (exprNe (.reg 652) (.reg 606)) (.reg 652))
        (.seq (gm06AppendWordsProg 608 604)
          (.seq (gm13TabulateProg 650 (.reg 655) (.read 604 (.reg 650)) 605)
            (gm06IncidenceBitsProg 605 602 648)))))

/-- Target preparation computes T_i from its actual boundary rows,
with linear cost and no supplied membership table. -/
theorem gm06TerminalTargetsProg_exec {w n source : ℕ} (left upper : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hsource : source < n)
    (hfit : left.length + upper.length + 2 < 2 ^ w)
    (hleft : ∀ v ∈ left, v < n) (hupper : ∀ v ∈ upper, v < n)
    (h609 : s.arrs 609 = left) (h608 : s.arrs 608 = upper)
    (h606 : s.regs 606 = source) (h648 : s.regs 648 = n) :
    ∃ sf t, Exec w gm06TerminalTargetsProg s sf t ∧
      t ≤ 40 + n + 60 * (left.length + upper.length) ∧
      Keeps [650, 651, 652, 655, 610, 611, 612] [604, 605, 602] s sf ∧
      sf.arrs 602 = gm06IncidenceBits n (gm06TerminalTargetLabels source left upper) := by
  let cap := left.length + upper.length
  let kept := left.filter (fun v => v != source)
  let labels := gm06TerminalTargetLabels source left upper
  have hkLen : kept.length ≤ left.length := List.length_filter_le _ _
  have hlabelsLen : labels.length = kept.length + upper.length := List.length_append
  have hlabelsWords : ∀ v ∈ labels, v < n := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hleft v (List.mem_filter.mp hv).1
    · exact hupper v hv
  let s₀ := s.setArr 604 (List.replicate cap 0)
  let s₁ := s₀.setReg 655 0
  have he₀ : Exec w (.alloc 604 (.op .add (.len 609) (.len 608))) s s₀ (3 + cap) :=
    .alloc (GraphMinor.Compute.Crossing.eval_add (GraphMinor.Compute.Crossing.eval_len h609 (by omega))
      (GraphMinor.Compute.Crossing.eval_len h608 (by omega)) (by omega))
  have he₁ : Exec w (.assign 655 (.const 0)) s₀ s₁ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hk₁ : Keeps [650, 651, 652, 655] [604] s s₁ :=
    ((Keeps.refl _ _ s).setArr (by simp) _).setReg (by simp) _
  obtain ⟨s₂, t₂, he₂, ht₂, hb₂, ha₂, hr₂⟩ := gm06FilterMapArrayProg_exec
    (w := w) (pre := []) (cap := cap) 609 604 650 651 652 655
    (exprNe (.reg 652) (.reg 606)) (.reg 652) (fun v => v != source) id
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hw ((hk₁.2 609 (by decide)).trans h609) (by omega) (fun v hv => (hleft v hv).trans hn)
    (by simp [GraphMinor.Compute.Crossing.IsBuf, s₁, s₀])
    (by simpa only [id_eq, filter_flatMap] using hkLen.trans (by omega))
    (by simpa only [List.length_nil, Nat.zero_add] using hfit)
    (fun st v hv _ hr hcurrent => by
      have he := eval_exprNe hw (GraphMinor.Compute.Crossing.eval_reg hcurrent ((hleft v hv).trans hn))
        (GraphMinor.Compute.Crossing.eval_reg
          ((hr 606 (by decide) (by decide) (by decide) (by decide)).trans
            ((hk₁.1 606 (by decide)).trans h606)) (hsource.trans hn))
      simpa only [bne_iff_ne, ne_eq, ite_not] using he)
    (fun _ v hv _ _ _ hr => GraphMinor.Compute.Crossing.eval_reg (w := w) hr ((hleft v hv).trans hn))
  have hk₂ : Keeps [650, 651, 652, 655] [604] s₁ s₂ := by
    constructor
    · intro r hr
      have h : r ≠ 650 ∧ r ≠ 651 ∧ r ≠ 652 ∧ r ≠ 655 := by simpa using hr
      exact hr₂ r h.1 h.2.1 h.2.2.1 h.2.2.2
    · intro a ha
      exact ha₂ a (by simpa using ha)
  have hk₁₂ := hk₁.trans hk₂ (fun _ h => h) (fun _ h => h)
  have hbuf₂ : GraphMinor.Compute.Crossing.IsBuf 604 655 kept (cap - kept.length) s₂ := by
    simpa only [List.nil_append, id_eq, filter_flatMap] using hb₂
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hb₃⟩ := gm06AppendWordsProg_exec (cap := cap - kept.length)
    (by decide : 608 ≠ 604) upper kept s₂ hw (fun v hv => (hupper v hv).trans hn)
    ((hk₁₂.2 608 (by decide)).trans h608) (by dsimp only [cap]; omega)
    (by dsimp only [cap]; omega) hbuf₂
  have hk₁₃ := hk₁₂.trans hk₃ (fun _ h => h) (fun _ h => h)
  have hbuf₃ : GraphMinor.Compute.Crossing.IsBuf 604 655 labels (cap - labels.length) s₃ := by
    simpa only [labels, gm06TerminalTargetLabels, kept, List.length_append, Nat.sub_sub] using hb₃
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hd₄⟩ := gm13TabulateProg_exec (w := w)
    650 (.reg 655) (.read 604 (.reg 650)) 605 labels s₃ hw (by omega)
    (fun st hk => GraphMinor.Compute.Crossing.eval_reg ((hk.1 655 (by decide)).trans hbuf₃.2) (by omega))
    (fun st i hi hk hr => by
      have ha := (hk.2 604 (by decide)).trans hbuf₃.1
      have he := GraphMinor.Compute.Crossing.eval_read (a := 604)
        (GraphMinor.Compute.Crossing.eval_reg (w := w) hr (by omega))
        (by simp only [ha, List.length_append, List.length_replicate]; omega)
        (by simpa only [ha, List.getElem_append_left hi] using (hlabelsWords _ (List.getElem_mem hi)).trans hn)
      simpa only [ha, List.getElem_append_left hi] using he)
  have hk₁₄ : Keeps [650, 651, 652, 655] [604, 605] s s₄ :=
    (hk₁₃.mono (fun _ h => h) (by simp)).trans hk₄ (by simp) (by simp)
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm06IncidenceBitsProg_exec_words 605 602 648 (by decide)
    labels s₄ hw hn (by omega) hlabelsWords ((hk₁₄.1 648 (by decide)).trans h648) hd₄
  refine ⟨sf, (3 + cap) + (2 + (t₂ + (t₃ + (t₄ + tf)))),
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ hef)))), ?_,
    (hk₁₄.mono (by simp) (by simp)).trans hkf (by simp) (by simp), hdf⟩
  simp only [Expr.cost, exprNe, exprNot, exprEq] at ht₂ ht₄
  dsimp only [cap] at *
  omega

end GraphMinor.Compute
