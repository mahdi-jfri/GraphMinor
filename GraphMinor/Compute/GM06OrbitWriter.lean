module

public import GraphMinor.Compute.GM06FaceSuccessors
import GraphMinor.Compute.Join13Adapter101Defs

/-!
# Writing one face orbit on the RAM

The traversal in FACE_ROWS, Section 5 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`) writes each dart to the current row and labels it with the
row's number. It then follows the successor table and stops at the start. This file verifies the
traversal itself. The loop proof follows the remaining suffix of a cyclic row, so its only stopping
condition is return to the start. The orbit lemmas supply that row
when the complete face enumerator invokes the traversal.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Mark current dart 651 with row label 654, append it at cursor 656,
and advance to its successor. Arrays 603/605/606 hold successors,
row labels and the output buffer, respectively. -/
def gm06OrbitWriteStep : Cmd :=
  .seq (.write 605 (.reg 651) (.reg 654))
    (.seq (.write 606 (.reg 656) (.reg 651))
      (.seq (.assign 656 (.op .add (.reg 656) (.const 1)))
        (.assign 651 (.read 603 (.reg 651)))))

/-- Continue exactly while the current dart differs from start 652. -/
def gm06OrbitContinue : Expr :=
  .op .eq (.op .eq (.reg 651) (.reg 652)) (.const 0)

/-- Write the first dart, then follow successors until the start returns. -/
def gm06OrbitWriteProg : Cmd :=
  .seq gm06OrbitWriteStep (.while gm06OrbitContinue gm06OrbitWriteStep)

private theorem orbit_condition_eval {w d start : ℕ} {s : State}
    (hw : 1 < 2 ^ w) (hd : d < 2 ^ w) (hs : start < 2 ^ w)
    (h651 : s.regs 651 = d) (h652 : s.regs 652 = start) :
    gm06OrbitContinue.eval w s = some (if d = start then 0 else 1) := by
  have he := GraphMinor.Compute.Crossing.eval_eq
    (GraphMinor.Compute.Crossing.eval_eq (GraphMinor.Compute.Crossing.eval_reg h651 hd)
      (GraphMinor.Compute.Crossing.eval_reg h652 hs) hw)
    (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w)) hw
  by_cases h : d = start <;> simpa [gm06OrbitContinue, h] using he

/-- A single traversal step performs the exact label write and append. -/
theorem gm06OrbitWriteStep_exec {w : ℕ} (successors owners pre : List ℕ)
    (rem d next label : ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hn : successors.length < 2 ^ w) (hlen : owners.length = successors.length)
    (hd : d < successors.length) (hnext : successors[d]? = some next)
    (hword : next < 2 ^ w) (hlabel : label < 2 ^ w)
    (hrem : 0 < rem) (hcap : pre.length + rem < 2 ^ w)
    (h603 : s.arrs 603 = successors) (h605 : s.arrs 605 = owners)
    (h606 : s.arrs 606 = pre ++ List.replicate rem 0)
    (h651 : s.regs 651 = d) (h654 : s.regs 654 = label) (h656 : s.regs 656 = pre.length) :
    ∃ sf, Exec w gm06OrbitWriteStep s sf 13 ∧
      Keeps [651, 656] [605, 606] s sf ∧
      sf.arrs 605 = owners.set d label ∧
      sf.arrs 606 = (pre ++ [d]) ++ List.replicate (rem - 1) 0 ∧
      sf.regs 651 = next ∧ sf.regs 656 = pre.length + 1 := by
  let s₁ := s.writeArr 605 d label
  let s₂ := s₁.writeArr 606 pre.length d
  let s₃ := s₂.setReg 656 (pre.length + 1)
  let sf := s₃.setReg 651 next
  have hdw : d < 2 ^ w := hd.trans hn
  have he₁ : Exec w (.write 605 (.reg 651) (.reg 654)) s s₁ 3 :=
    .write (GraphMinor.Compute.Crossing.eval_reg h651 hdw)
      (GraphMinor.Compute.Crossing.eval_reg h654 hlabel) (by simpa [h605, hlen] using hd)
  have he₂ : Exec w (.write 606 (.reg 656) (.reg 651)) s₁ s₂ 3 :=
    .write (GraphMinor.Compute.Crossing.eval_reg h656 (by omega))
      (GraphMinor.Compute.Crossing.eval_reg h651 hdw) (by simp [s₁, h606]; omega)
  have he₃ : Exec w (.assign 656 (.op .add (.reg 656) (.const 1))) s₂ s₃ 4 :=
    .assign (GraphMinor.Compute.Crossing.eval_add (GraphMinor.Compute.Crossing.eval_reg h656 (by omega))
      (GraphMinor.Compute.Crossing.eval_const hw) (by omega))
  have ha₃ : s₃.arrs 603 = successors := by simp [s₃, s₂, s₁, State.writeArr, h603]
  have hi₃ : s₃.regs 651 = d := by simp [s₃, s₂, s₁, h651]
  have hget : successors[d] = next := by
    exact Option.some.inj ((List.getElem?_eq_getElem hd).symm.trans hnext)
  have he₄ : Exec w (.assign 651 (.read 603 (.reg 651))) s₃ sf 3 :=
    .assign (by
      have he := GraphMinor.Compute.Crossing.eval_read (a := 603)
        (GraphMinor.Compute.Crossing.eval_reg hi₃ hdw) (by simpa only [ha₃] using hd)
        (by simpa only [ha₃, hget] using hword)
      simpa only [ha₃, hget] using he)
  refine ⟨sf, .seq he₁ (.seq he₂ (.seq he₃ he₄)), ?_, ?_, ?_, by simp [sf], by simp [sf, s₃]⟩
  · exact ((((Keeps.refl _ _ s).writeArr (by simp) _ _).writeArr
      (by simp) _ _).setReg (by simp) _).setReg (by simp) _
  · simp [sf, s₃, s₂, s₁, State.writeArr, h605]
  · simp only [sf, s₃, s₂, State.setReg_arrs, State.writeArr, State.setArr_arrs_self]
    rw [show s₁.arrs 606 = pre ++ List.replicate rem 0 by simp [s₁, State.writeArr, h606],
      list_set_append_replicate_zero_step pre rem d hrem]

/-- A suffix avoiding the start is traversed completely and stops
at its first following start. This is the suffix form of the orbit loop. -/
theorem gm06OrbitTailProg_exec {w : ℕ} (successors owners pre rest : List ℕ)
    (rem start label : ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hn : successors.length < 2 ^ w) (hlen : owners.length = successors.length)
    (hs : start < successors.length) (hd : ∀ d ∈ rest, d < successors.length)
    (hnot : start ∉ rest)
    (hchain : List.IsChain (fun a b => successors[a]? = some b) (rest ++ [start]))
    (hlabel : label < 2 ^ w) (hroom : rest.length ≤ rem)
    (hcap : pre.length + rem < 2 ^ w)
    (h603 : s.arrs 603 = successors) (h605 : s.arrs 605 = owners)
    (h606 : s.arrs 606 = pre ++ List.replicate rem 0)
    (h651 : s.regs 651 = rest.headD start) (h652 : s.regs 652 = start)
    (h654 : s.regs 654 = label) (h656 : s.regs 656 = pre.length) :
    ∃ sf t, Exec w (.while gm06OrbitContinue gm06OrbitWriteStep) s sf t ∧
      t ≤ 5 + 18 * rest.length ∧ Keeps [651, 656] [605, 606] s sf ∧
      sf.arrs 605 = gm06Scatter (rest.map (fun d => (d, label))) owners ∧
      sf.arrs 606 = (pre ++ rest) ++ List.replicate (rem - rest.length) 0 ∧
      sf.regs 651 = start ∧ sf.regs 656 = pre.length + rest.length := by
  induction rest generalizing owners pre rem s with
  | nil =>
    refine ⟨s, 5, .while_false ?_, by simp, Keeps.refl _ _ _, h605, ?_, h651, ?_⟩
    · simpa using orbit_condition_eval hw (hs.trans hn) (hs.trans hn) h651 h652
    · simpa using h606
    · simpa using h656
  | cons d ds ih =>
    have hne : d ≠ start := fun heq => hnot (by simp [← heq])
    have hdi : d < successors.length := hd d List.mem_cons_self
    let next := ds.headD start
    have hnext : successors[d]? = some next := by
      cases ds with
      | nil =>
        have hh := (List.isChain_cons_cons.mp hchain).1
        exact hh
      | cons e es => exact (List.isChain_cons_cons.mp hchain).1
    have hnxt : next < successors.length := by
      cases ds with
      | nil => exact hs
      | cons e es => exact hd e (by simp)
    have hrem : 0 < rem := by simp only [List.length_cons] at hroom; omega
    obtain ⟨s₁, he₁, hk₁, hd₁, hb₁, hq₁, hp₁⟩ := gm06OrbitWriteStep_exec
      successors owners pre rem d next label s hw hn hlen hdi hnext (hnxt.trans hn) hlabel hrem hcap
      h603 h605 h606 h651 h654 h656
    have h603₁ : s₁.arrs 603 = successors := (hk₁.2 603 (by decide)).trans h603
    have hstart₁ : s₁.regs 652 = start := (hk₁.1 652 (by decide)).trans h652
    have hlabel₁ : s₁.regs 654 = label := (hk₁.1 654 (by decide)).trans h654
    obtain ⟨sf, tf, hef, htf, hkf, hdf, hbf, hqf, hpf⟩ := ih (owners.set d label) (pre ++ [d])
      (rem - 1) s₁ (by simpa using hlen)
      (fun e he => hd e (List.mem_cons_of_mem d he))
      (fun h => hnot (List.mem_cons_of_mem d h)) hchain.tail
      (by simp only [List.length_cons] at hroom; omega)
      (by simp only [List.length_append, List.length_singleton]; omega)
      h603₁ hd₁ hb₁ hq₁ hstart₁ hlabel₁ (by simpa using hp₁)
    refine ⟨sf, 5 + 13 + tf, .while_true ?_ (by decide : (1 : ℕ) ≠ 0) he₁ hef,
      by simp only [List.length_cons]; omega, hk₁.trans hkf (fun _ h => h) (fun _ h => h),
      hdf, ?_, hqf, ?_⟩
    · simpa only [List.headD_cons, hne, ↓reduceIte] using
        orbit_condition_eval hw (hdi.trans hn) (hs.trans hn) h651 h652
    · simpa only [List.append_assoc, List.singleton_append, List.length_cons, Nat.sub_sub,
        Nat.add_comm 1] using hbf
    · simpa only [List.length_append, List.length_singleton, List.length_cons,
        Nat.add_assoc, Nat.add_comm 1, List.length_nil, Nat.zero_add] using hpf

/-- One complete cyclic row is written exactly, and every dart receives
its row label. The traversal ends at the start and costs linear time. -/
theorem gm06OrbitWriteProg_exec {w : ℕ} (successors owners pre rest : List ℕ)
    (rem start label : ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hn : successors.length < 2 ^ w) (hlen : owners.length = successors.length)
    (hs : start < successors.length) (hd : ∀ d ∈ rest, d < successors.length)
    (hnot : start ∉ rest)
    (hchain : List.IsChain (fun a b => successors[a]? = some b) (start :: rest ++ [start]))
    (hlabel : label < 2 ^ w) (hroom : rest.length + 1 ≤ rem)
    (hcap : pre.length + rem < 2 ^ w)
    (h603 : s.arrs 603 = successors) (h605 : s.arrs 605 = owners)
    (h606 : s.arrs 606 = pre ++ List.replicate rem 0)
    (h651 : s.regs 651 = start) (h652 : s.regs 652 = start)
    (h654 : s.regs 654 = label) (h656 : s.regs 656 = pre.length) :
    ∃ sf t, Exec w gm06OrbitWriteProg s sf t ∧
      t ≤ 18 * (rest.length + 1) ∧ Keeps [651, 656] [605, 606] s sf ∧
      sf.arrs 605 = gm06Scatter ((start :: rest).map (fun d => (d, label))) owners ∧
      sf.arrs 606 = (pre ++ (start :: rest)) ++ List.replicate (rem - (rest.length + 1)) 0 ∧
      sf.regs 651 = start ∧ sf.regs 656 = pre.length + (rest.length + 1) := by
  let next := rest.headD start
  have hnext : successors[start]? = some next := by
    cases rest with
    | nil =>
      have hh := (List.isChain_cons_cons.mp hchain).1
      exact hh
    | cons d ds => exact (List.isChain_cons_cons.mp hchain).1
  have hnxt : next < successors.length := by
    cases rest with
    | nil => exact hs
    | cons d ds => exact hd d List.mem_cons_self
  have hrem : 0 < rem := by omega
  obtain ⟨s₁, he₁, hk₁, hd₁, hb₁, hq₁, hp₁⟩ := gm06OrbitWriteStep_exec
    successors owners pre rem start next label s hw hn hlen hs hnext (hnxt.trans hn)
    hlabel hrem hcap h603 h605 h606 h651 h654 h656
  obtain ⟨sf, tf, hef, htf, hkf, hdf, hbf, hqf, hpf⟩ := gm06OrbitTailProg_exec
    successors (owners.set start label) (pre ++ [start]) rest (rem - 1) start label s₁ hw hn
    (by simpa using hlen) hs hd hnot hchain.tail hlabel (by omega)
    (by simp only [List.length_append, List.length_singleton]; omega)
    ((hk₁.2 603 (by decide)).trans h603) hd₁ hb₁ hq₁
    ((hk₁.1 652 (by decide)).trans h652) ((hk₁.1 654 (by decide)).trans h654) (by simpa using hp₁)
  refine ⟨sf, 13 + tf, .seq he₁ hef, by omega, hk₁.trans hkf (fun _ h => h) (fun _ h => h),
    hdf, ?_, hqf, ?_⟩
  · simpa only [List.append_assoc, List.singleton_append, Nat.sub_sub, Nat.add_comm 1] using hbf
  · simpa only [List.length_append, List.length_singleton, Nat.add_assoc, Nat.add_comm 1, List.length_nil, Nat.zero_add] using hpf

end GraphMinor.Compute
