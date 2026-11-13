module

public import GraphMinor.Compute.GM06Reduction4Contacts
public import GraphMinor.Compute.GM13SocietyTabulate

/-!
# The complete contact scan for FIND_4

Section 13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) maintains
the prefix flag (11) while scanning a linkage row. This program starts the
flag from its first vertex, reads each edge and arrival, and returns
exactly the eligible positive positions. Its input contains the path
and incidence arrays. The contact list is built by the scan itself.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Initialize the prefix and contact buffer, scan the path, then
return its exact contact list in array 617. -/
def gm06Reduction4ContactsProg : Cmd :=
  .seq (.alloc 611 (.len 610))
    (.seq (.assign 653 (.const 0))
      (.seq (.assign 672 (exprNe (.read 606 (.read 609 (.const 0))) (.const 0)))
        (.seq (.assign 650 (.const 0))
          (.seq (forUp 650 (.len 610) gm06Reduction4ContactStep)
            (gm13TabulateProg 650 (.reg 653) (.read 611 (.reg 650)) 617)))))

/-- The complete scan returns the exact pure contact function and the
final prefix flag, in linear time. No eligibility table is supplied. -/
theorem gm06Reduction4ContactsProg_exec {w : ℕ}
    (incV incE : List ℕ) (start : ℕ) (steps : List (ℕ × ℕ)) (s : State)
    (hw : 1 < 2 ^ w) (hfit : steps.length + 2 < 2 ^ w)
    (hVfit : incV.length < 2 ^ w) (hEfit : incE.length < 2 ^ w)
    (hstart : start < incV.length)
    (hkeys : ∀ step ∈ steps, step.1 < incE.length ∧ step.2 < incV.length)
    (hVwords : ∀ x ∈ incV, x < 2 ^ w) (hEwords : ∀ x ∈ incE, x < 2 ^ w)
    (h606 : s.arrs 606 = incV) (h607 : s.arrs 607 = incE)
    (h609 : s.arrs 609 = start :: steps.map Prod.snd)
    (h610 : s.arrs 610 = steps.map Prod.fst) :
    ∃ sf t, Exec w gm06Reduction4ContactsProg s sf t ∧ t ≤ 25 + 85 * steps.length ∧
      Keeps [650, 652, 653, 672, 674] [611, 617] s sf ∧
      sf.arrs 617 = gm06Reduction4Contacts incV incE start steps ∧
      sf.regs 672 = (if gm06PrefixOK incV incE start steps then 1 else 0) := by
  let r := steps.length
  let contacts := fun i => gm06Reduction4Contacts incV incE start (steps.take i)
  let flagAt := fun i => gm06PrefixOK incV incE start (steps.take i)
  let s₀ := s.setArr 611 (List.replicate r 0)
  let s₁ := s₀.setReg 653 0
  let s₂ := s₁.setReg 672 (if gm06Incident incV start then 1 else 0)
  let s₃ := s₂.setReg 650 0
  have hr : r < 2 ^ w := by dsimp only [r]; omega
  have he₀ : Exec w (.alloc 611 (.len 610)) s s₀ (1 + r) :=
    .alloc (by simpa only [List.length_map, r] using
      GraphMinor.Compute.Crossing.eval_len h610 (by simpa using hr))
  have he₁ : Exec w (.assign 653 (.const 0)) s₀ s₁ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hreadStart : (Expr.read 609 (.const 0)).eval w s₁ = some start := by
    have he := GraphMinor.Compute.Crossing.eval_read (w := w) (s := s₁) (a := 609)
      (GraphMinor.Compute.Crossing.eval_const (c := 0) (Nat.two_pow_pos w))
      (by simp [s₁, s₀, h609]) (by simpa [s₁, s₀, h609] using hstart.trans hVfit)
    simpa [s₁, s₀, h609] using he
  have hreadInc : (Expr.read 606 (.read 609 (.const 0))).eval w s₁ = some incV[start] := by
    have he := GraphMinor.Compute.Crossing.eval_read (a := 606) hreadStart
      (by simpa [s₁, s₀, h606] using hstart)
      (by simpa [s₁, s₀, h606] using hVwords _ (List.getElem_mem hstart))
    simpa [s₁, s₀, h606] using he
  have he₂ : Exec w (.assign 672 (exprNe (.read 606 (.read 609 (.const 0))) (.const 0)))
      s₁ s₂ 8 := by
    apply Exec.assign
    simpa only [gm06Incident, List.getElem?_eq_getElem hstart, Option.getD_some, bne_iff_ne,
      ne_eq, ite_not] using eval_exprNe hw hreadInc
        (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have he₃ : Exec w (.assign 650 (.const 0)) s₂ s₃ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hk₃ : Keeps [650, 652, 653, 672, 674] [611] s s₃ :=
    ((((Keeps.refl _ _ s).setArr (by simp) _).setReg (by simp) _).setReg (by simp) _).setReg (by simp) _
  let Inv := fun i st => st.regs 650 = i ∧ Keeps [650, 652, 653, 672, 674] [611] s st ∧
    st.regs 672 = (if flagAt i then 1 else 0) ∧
    GraphMinor.Compute.Crossing.IsBuf 611 653 (contacts i) (r - (contacts i).length) st
  have hI₀ : Inv 0 s₃ := by
    refine ⟨by simp [s₃], hk₃, ?_, ?_⟩
    · simp [s₃, s₂, flagAt, gm06PrefixOK]
      rfl
    · simp [GraphMinor.Compute.Crossing.IsBuf, s₃, s₂, s₁, s₀, contacts, gm06Reduction4Contacts]
  obtain ⟨s₄, t₄, he₄, ht₄, hI₄⟩ := GraphMinor.Compute.Crossing.forUp_exec'
    (r_i := 650) (hi := .len 610) (body := gm06Reduction4ContactStep)
    Inv r 60 hw hr
    (fun i _ st h => ⟨h.1, by simpa only [List.length_map, r] using
      (GraphMinor.Compute.Crossing.eval_len ((h.2.1.2 610 (by decide)).trans h610)
        (by simpa using hr))⟩)
    (fun i hi st h => by
      obtain ⟨hidx, hk, hf, hb⟩ := h
      have hi' : i < steps.length := hi
      have hstep := hkeys steps[i] (List.getElem_mem hi')
      have hcount : (contacts i).length ≤ i :=
        (gm06Reduction4Contacts_length_le incV incE start (steps.take i)).trans
          (by simp only [List.length_take]; exact Nat.min_le_left _ _)
      have htake : steps.take (i + 1) = steps.take i ++ [steps[i]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some]
      obtain ⟨st', t', he', ht', hk', hf', hb'⟩ := gm06Reduction4ContactStep_exec
        incV incE (start :: steps.map Prod.snd) (steps.map Prod.fst) start (steps.take i) st
        hw (by simp only [List.length_take]; omega)
        (List.length_take_of_le hi'.le) (by simpa using hi') (by simpa using hi')
        (by simp) (by simp) hstep.1 hstep.2
        (hEwords _ (List.getElem_mem hstep.1)) (hVwords _ (List.getElem_mem hstep.2))
        (hstep.1.trans hEfit) (hstep.2.trans hVfit)
        ((hk.2 606 (by decide)).trans h606) ((hk.2 607 (by decide)).trans h607)
        ((hk.2 609 (by decide)).trans h609) ((hk.2 610 (by decide)).trans h610) hidx hf hb
        (by dsimp only [r]; omega)
      have hlenNext : (contacts (i + 1)).length = (contacts i).length +
          (if gm06Incident incV steps[i].2 &&
            !gm06PrefixOK incV incE start (steps.take (i + 1)) then 1 else 0) := by
        dsimp only [contacts]
        rw [htake, gm06Reduction4Contacts_append_one, List.length_append]
        split <;> simp
      refine ⟨st', t', he', ht', ⟨by simp, (hk.trans hk' (by simp) (by simp)).setReg (by simp) _,
        ?_, ?_⟩, (hk'.1 650 (by decide)).trans hidx⟩
      · simpa only [flagAt, htake, State.setReg_regs_ne _ _ (by decide : 672 ≠ 650)] using hf'
      · have hcapEq : r - (contacts (i + 1)).length = r - (contacts i).length -
            (if gm06Incident incV steps[i].2 &&
              !gm06PrefixOK incV incE start (steps.take (i + 1)) then 1 else 0) := by omega
        rw [hcapEq]
        simpa only [contacts, htake, GraphMinor.Compute.Crossing.IsBuf, State.setReg_arrs,
          State.setReg_regs_ne _ _ (by decide : 653 ≠ 650)] using hb') s₃ hI₀
  let out := gm06Reduction4Contacts incV incE start steps
  have hbuffer : GraphMinor.Compute.Crossing.IsBuf 611 653 out (r - out.length) s₄ := by
    simpa only [contacts, r, List.take_length] using hI₄.2.2.2
  have houtlen : out.length ≤ r := gm06Reduction4Contacts_length_le incV incE start steps
  have houtwords : ∀ x ∈ out, x < 2 ^ w := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    have hq' := List.mem_range.mp (List.mem_filter.mp hq).1
    omega
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm13TabulateProg_exec
    650 (.reg 653) (.read 611 (.reg 650)) 617 out s₄ hw (houtlen.trans_lt hr)
    (fun st hk => GraphMinor.Compute.Crossing.eval_reg
      ((hk.1 653 (by decide)).trans hbuffer.2) (houtlen.trans_lt hr))
    (fun st i hi hk hr' => by
      have ha : st.arrs 611 = out ++ List.replicate (r - out.length) 0 :=
        (hk.2 611 (by decide)).trans hbuffer.1
      have he := GraphMinor.Compute.Crossing.eval_read (a := 611)
        (GraphMinor.Compute.Crossing.eval_reg hr' (hi.trans (houtlen.trans_lt hr)))
        (by simp only [ha, List.length_append, List.length_replicate]; omega)
        (by simpa only [ha, List.getElem_append_left hi] using houtwords _ (List.getElem_mem hi))
      simpa only [ha, List.getElem_append_left hi] using he)
  refine ⟨sf, (1 + r) + (2 + (8 + (2 + (t₄ + tf)))),
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ hef)))), ?_,
    ((hI₄.2.1.mono (fun _ h => h) (by simp)).trans hkf (by simp) (by simp)), hdf, ?_⟩
  · simp only [Expr.cost] at ht₄ htf
    dsimp only [r] at hr houtlen ⊢
    omega
  · exact (hkf.1 672 (by decide)).trans (by simpa only [flagAt, r, List.take_length] using hI₄.2.2.1)

end GraphMinor.Compute
