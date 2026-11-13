module

public import GraphMinor.Compute.CrossingOpsReplFind

/-!
# Adding the missing clique neighbours

For a boundary vertex, the replacement scans the boundary list and appends each other
boundary vertex that was not already adjacent to it. Each candidate uses the old-list
membership test. Since the boundary has at most three entries, these scans take linear time
in the old list length.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Append the missing clique neighbours from the boundary array. -/
def emitBoundaryProg (a_bd a_s a_e a_ent buf R : ℕ) : Cmd :=
  forArrProg a_bd (R + 5) (R + 6) (R + 7) (emitMissingNeighbourProg a_s a_e a_ent buf R)

/-- At most three boundary candidates require at most three scans of the old list. -/
theorem emitBoundaryProg_exec {w : ℕ} (a_bd a_s a_e a_ent buf R : ℕ)
    {s : State} {bl l pre : List ℕ} {k x st en : ℕ}
    (hbd : a_bd ≠ buf) (hs : a_s ≠ buf) (he : a_e ≠ buf) (hent : a_ent ≠ buf)
    (hbl : s.arrs a_bd = bl) (hsmall : bl.length ≤ 3)
    (hl : IsListAt a_s a_e a_ent x st en l s) (hx : s.regs R = x)
    (hb : IsBuf buf (R + 4) pre k s)
    (hk : (bl.filter (fun y => y ≠ x ∧ y ∉ l)).length ≤ k)
    (hblw : ∀ y ∈ bl, y < 2 ^ w) (hblen : bl.length < 2 ^ w)
    (hlt : ∀ y ∈ l, y < 2 ^ w) (hxw : x < 2 ^ w) (hen : en < 2 ^ w)
    (hw : pre.length + k + 2 < 2 ^ w) :
    ∃ s' t, Exec w (emitBoundaryProg a_bd a_s a_e a_ent buf R) s s' t ∧
      t ≤ 103 + 45 * l.length ∧
      IsBuf buf (R + 4) (pre ++ bl.filter (fun y => y ≠ x ∧ y ∉ l))
        (k - (bl.filter (fun y => y ≠ x ∧ y ∉ l)).length) s' ∧
      (∀ a, a ≠ buf → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 →
        r ≠ R + 5 → r ≠ R + 6 → r ≠ R + 7 → r ≠ R + 9 → s'.regs r = s.regs r) := by
  classical
  let g : ℕ → List ℕ := fun y => if y ≠ x ∧ y ∉ l then [y] else []
  have hg : bl.flatMap g = bl.filter (fun y => y ≠ x ∧ y ∉ l) := by
    clear hbl hl hk hsmall hblw hblen
    induction bl with
    | nil => rfl
    | cons y bl ih =>
      simp only [List.flatMap_cons, List.filter_cons]
      by_cases h : y ≠ x ∧ y ∉ l <;> simpa [g, h] using ih
  let Q : ℕ → State → Prop := fun _ z =>
    (∀ a, a ≠ buf → z.arrs a = s.arrs a) ∧
    (∀ r, r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 →
      r ≠ R + 5 → r ≠ R + 6 → r ≠ R + 7 → r ≠ R + 9 → z.regs r = s.regs r)
  obtain ⟨s', t, hex, ht, hQ, hb'⟩ := forArrEmit_exec (w := w) a_bd (R + 5) (R + 6) (R + 7)
    buf (R + 4) (emitMissingNeighbourProg a_s a_e a_ent buf R) g Q (22 + 15 * l.length)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simpa only [hbl] using hblen) (by simpa only [hbl] using hblw)
    ⟨fun _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl⟩ hb (by rw [hbl, hg]; exact hk)
    (fun j z z' h ha hr => ⟨fun a ha' => by rw [ha]; exact h.1 a ha',
      fun r h1 h2 h3 h4 h5 h6 h7 h9 =>
        (hr r h5 h6 h7).trans (h.2 r h1 h2 h3 h4 h5 h6 h7 h9)⟩)
    (fun _ z h => h.1 a_bd hbd)
    (fun j hj z pre' k' h hri hrn hry hb'' hk' hcap => by
      have hl' := hl.of_arrs_eq (h.1 a_s hs) (h.1 a_e he) (h.1 a_ent hent)
      have hx' : z.regs R = x := (h.2 R (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)).trans hx
      obtain ⟨z', t', he', ht', hb''', ha', hr'⟩ := emitMissingNeighbourProg_exec (w := w)
        a_s a_e a_ent buf R hl' hx' hry hxw
        (by rw [← hbl] at hblw; exact hblw _ (List.getElem_mem hj)) hen hlt (by omega) hb''
        (by by_cases h : (s.arrs a_bd)[j] ≠ x ∧ (s.arrs a_bd)[j] ∉ l <;>
          simpa [g, h] using hk') (by omega)
      refine ⟨z', t', he', ht', ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · intro a ha; exact (ha' a ha).trans (h.1 a ha)
      · intro r h1 h2 h3 h4 h5 h6 h7 h9
        exact (hr' r h1 h2 h3 h4 h9).trans (h.2 r h1 h2 h3 h4 h5 h6 h7 h9)
      · exact (hr' (R + 5) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hri
      · exact (hr' (R + 6) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hrn
      · by_cases h : (s.arrs a_bd)[j] ≠ x ∧ (s.arrs a_bd)[j] ∉ l <;>
          simpa [g, h] using hb''')
  refine ⟨s', t, hex, ?_, by simpa only [hbl, hg] using hb', hQ.1, hQ.2⟩
  rw [hbl] at ht
  have hc := Nat.mul_le_mul_right (10 + (22 + 15 * l.length)) hsmall
  omega

end GraphMinor.Compute.Crossing
