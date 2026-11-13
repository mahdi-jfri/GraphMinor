module

public import GraphMinor.Compute.GM06CutActiveBits
public import GraphMinor.Compute.GM06Alg34FilterMapArray
public import GraphMinor.Compute.GM13SocietyTabulate

/-!
# Returning copied active darts in permanent label order

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) needs the
active copied ends for later component and face scans. The origin pass
computes their bitmap. This program constructs the full permanent
label range and filters it using that bitmap, then returns exactly
the selected prefix. Thus the active list is computed in increasing
order rather than supplied as input.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

private theorem filter_flatMap (xs : List ℕ) (keep : ℕ → Bool) :
    xs.flatMap (fun d => if keep d then [d] else []) = xs.filter keep := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : keep x <;> simp [h, ih]

/-- Read active bits 627 and copied dart count 647. Return the
increasing active labels in 628, using range 620 and buffer 621. -/
def gm06CutActiveProg : Cmd :=
  .seq (gm13TabulateProg 650 (.reg 647) (.reg 650) 620)
    (.seq (.alloc 621 (.reg 647))
      (.seq (.assign 653 (.const 0))
        (.seq (gm06FilterMapArrayProg 620 621 650 651 652 653 (.read 627 (.reg 652)) (.reg 652))
          (gm13TabulateProg 650 (.reg 653) (.read 621 (.reg 650)) 628))))

/-- Exact increasing active-label output, with linear time in its
permanent label space. All graph rows, origins and input bits survive. -/
theorem gm06CutActiveProg_exec {w q : ℕ} (labels : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hfit : q + 2 < 2 ^ w)
    (h647 : s.regs 647 = q) (h627 : s.arrs 627 = gm06IncidenceBits q labels) :
    ∃ sf t, Exec w gm06CutActiveProg s sf t ∧ t ≤ 30 + 50 * q ∧
      Keeps [650, 651, 652, 653] [620, 621, 628] s sf ∧
      sf.arrs 628 = (List.range q).filter (fun d => decide (d ∈ labels)) := by
  have hq : q < 2 ^ w := by omega
  let keep := fun d => decide (d ∈ labels)
  let out := (List.range q).filter keep
  have houtlen : out.length ≤ q := by simpa only [List.length_range] using List.length_filter_le keep (List.range q)
  have houtword : ∀ d ∈ out, d < 2 ^ w := by
    intro d hd
    exact (List.mem_range.mp (List.mem_filter.mp hd).1).trans hq
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm13TabulateProg_exec
    650 (.reg 647) (.reg 650) 620 (List.range q) s hw (by simpa using hq)
    (fun st hk => by simpa only [List.length_range] using (GraphMinor.Compute.Crossing.eval_reg
      ((hk.1 647 (by decide)).trans h647) hq))
    (fun st i hi _ hr => by
      have hiq : i < q := by simpa using hi
      simpa only [List.getElem_range] using GraphMinor.Compute.Crossing.eval_reg hr (hiq.trans hq))
  let s₂ := s₁.setArr 621 (List.replicate q 0)
  let s₃ := s₂.setReg 653 0
  have he₂ : Exec w (.alloc 621 (.reg 647)) s₁ s₂ (1 + q) :=
    .alloc (GraphMinor.Compute.Crossing.eval_reg ((hk₁.1 647 (by decide)).trans h647) hq)
  have he₃ : Exec w (.assign 653 (.const 0)) s₂ s₃ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hk₁₃ : Keeps [650, 651, 652, 653] [620, 621] s s₃ :=
    ((hk₁.mono (by simp) (by simp)).setArr (by simp) _).setReg (by simp) _
  have hsource : s₃.arrs 620 = List.range q := by simpa [s₃, s₂] using hd₁
  obtain ⟨s₄, t₄, he₄, ht₄, hb₄, ha₄, hr₄⟩ := gm06FilterMapArrayProg_exec
    (l := List.range q) (pre := []) (cap := q) (s := s₃)
    620 621 650 651 652 653 (.read 627 (.reg 652)) (.reg 652) keep id
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hw hsource (by simpa using hq) (fun d hd => (List.mem_range.mp hd).trans hq)
    (by simp [GraphMinor.Compute.Crossing.IsBuf, s₃, s₂])
    (by simpa only [id_eq, filter_flatMap] using houtlen) (by simpa using hfit)
    (fun z d hd harr _ hcurrent => by
      have hdq := List.mem_range.mp hd
      have hbits : z.arrs 627 = gm06IncidenceBits q labels :=
        (harr 627 (by decide)).trans ((hk₁₃.2 627 (by decide)).trans h627)
      have hi : d < (z.arrs 627).length := by simpa [hbits, gm06IncidenceBits] using hdq
      have hget : (z.arrs 627)[d]'hi = (if d ∈ labels then 1 else 0) := by simp [hbits, gm06IncidenceBits]
      have he := GraphMinor.Compute.Crossing.eval_read (a := 627)
        (GraphMinor.Compute.Crossing.eval_reg hcurrent (hdq.trans hq)) hi
        (by rw [hget]; split_ifs <;> omega)
      simpa only [hget, keep, decide_eq_true_eq] using he)
    (fun _ d hd _ _ _ hcurrent => GraphMinor.Compute.Crossing.eval_reg hcurrent ((List.mem_range.mp hd).trans hq))
  have hbuffer : s₄.arrs 621 = out ++ List.replicate (q - out.length) 0 := by
    simpa only [id_eq, filter_flatMap, List.nil_append] using hb₄.1
  have hcursor : s₄.regs 653 = out.length := by simpa only [id_eq, filter_flatMap, List.nil_append] using hb₄.2
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm13TabulateProg_exec
    650 (.reg 653) (.read 621 (.reg 650)) 628 out s₄ hw (houtlen.trans_lt hq)
    (fun st hk => GraphMinor.Compute.Crossing.eval_reg ((hk.1 653 (by decide)).trans hcursor) (houtlen.trans_lt hq))
    (fun st i hi hk hr => by
      have hb : st.arrs 621 = out ++ List.replicate (q - out.length) 0 := (hk.2 621 (by decide)).trans hbuffer
      have he := GraphMinor.Compute.Crossing.eval_read (a := 621)
        (GraphMinor.Compute.Crossing.eval_reg hr (hi.trans (houtlen.trans_lt hq)))
        (by simp only [hb, List.length_append, List.length_replicate]; omega)
        (by simpa [hb, List.getElem_append_left hi] using houtword _ (List.getElem_mem hi))
      simpa [hb, List.getElem_append_left hi] using he)
  have hk₄ : Keeps [650, 651, 652, 653] [621] s₃ s₄ := by
    constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact hr₄ r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
    · intro A hA
      exact ha₄ A (by simpa using hA)
  refine ⟨sf, t₁ + ((1 + q) + (2 + (t₄ + tf))), .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ hef))), ?_,
    (((hk₁₃.trans hk₄ (fun _ h => h) (by simp)).mono (fun _ h => h) (by simp)).trans hkf (by simp) (by simp)), hdf⟩
  simp only [Expr.cost, List.length_range] at ht₁ ht₄ htf
  omega

end GraphMinor.Compute
