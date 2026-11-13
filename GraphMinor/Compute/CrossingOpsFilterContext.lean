module

public import GraphMinor.Compute.CrossingOpsFilter

/-!
# Filtering with immutable register context

The retention test reads saved cutoff and cycle-length registers as well as arrays.
This version of the filtering rule carries all unchanged registers through the list loop.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Filtering takes time proportional to the old list length. The test hypothesis
may also use registers outside the loop counters, neighbour register, and buffer cursor. -/
theorem filterListProg_context_exec {w : ℕ} (a_s a_e a_ent buf R : ℕ) (test : Expr)
    {s : State} {l pre : List ℕ} {x st en k : ℕ} (keep : ℕ → Bool)
    (hne : a_ent ≠ buf) (hl : IsListAt a_s a_e a_ent x st en l s)
    (hx : s.regs R = x) (hb : IsBuf buf (R + 4) pre k s)
    (hk : (l.filter keep).length ≤ k) (hyword : ∀ y ∈ l, y < 2 ^ w)
    (hxword : x < 2 ^ w) (hen : en < 2 ^ w) (hw : 1 < 2 ^ w)
    (hcap : pre.length + k + 2 < 2 ^ w)
    (htest : ∀ z y, y ∈ l → (∀ a, a ≠ buf → z.arrs a = s.arrs a) →
      (∀ r, r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 → z.regs r = s.regs r) →
      z.regs (R + 3) = y →
      test.eval w z = some (if keep y then 1 else 0)) :
    ∃ s' t, Exec w (filterListProg a_s a_e a_ent buf R test) s s' t ∧
      t ≤ 9 + l.length * (17 + test.cost) ∧
      IsBuf buf (R + 4) (pre ++ l.filter keep) (k - (l.filter keep).length) s' ∧
      (∀ a, a ≠ buf → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 → s'.regs r = s.regs r) := by
  let g : ℕ → List ℕ := fun y => if keep y then [y] else []
  have hg : l.flatMap g = l.filter keep := by
    clear hl hk hyword htest
    induction l with
    | nil => rfl
    | cons y l ih => cases hy : keep y <;> simp [g, hy, ih]
  let Q : ℕ → State → Prop := fun _ z =>
    (∀ a, a ≠ buf → z.arrs a = s.arrs a) ∧
    (∀ r, r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 → z.regs r = s.regs r)
  obtain ⟨s', t, he, ht, hQ, hb'⟩ := forListEmit_exec a_s a_e a_ent R (R + 1) (R + 2)
    (R + 3) buf (R + 4) (emitWhenProg buf (R + 4) (R + 3) test)
    x st en l g Q (test.cost + 7) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hw hen hxword hl hx hyword
    ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩ hb (by simpa only [hg] using hk)
    (fun j z z' h ha hr => ⟨fun a hh => (congrFun ha a).trans (h.1 a hh),
      (fun r h1 h2 h3 h4 => (hr r h1 h2 h3).trans (h.2 r h1 h2 h3 h4))⟩)
    (fun _ _ h => h.1 _ hne)
    (fun j hj z pre' k' h hri hrhi hry hb'' hk' htotal => by
      have hkg : (if keep l[j] then 1 else 0) ≤ k' := by
        cases hh : keep l[j] <;> simpa [g, hh] using hk'
      obtain ⟨z', t', he', ht', hb''', ha, hr⟩ := emitWhenProg_exec buf (R + 4) (R + 3)
        test (keep l[j]) (htest z l[j] (List.getElem_mem hj) h.1 h.2 hry) hb'' hry
        (hyword _ (List.getElem_mem hj)) (by omega) hkg
      refine ⟨z', t', he', ht', ⟨fun a hh => (ha a hh).trans (h.1 a hh),
        (fun r h1 h2 h3 h4 => (hr r h4).trans (h.2 r h1 h2 h3 h4))⟩,
        (hr _ (by omega)).trans hri, (hr _ (by omega)).trans hrhi, ?_⟩
      cases hh : keep l[j] <;> simpa [g, hh] using hb''')
  have hcost : 10 + (test.cost + 7) = 17 + test.cost := by omega
  rw [hcost] at ht
  refine ⟨s', t, he, ht, by simpa only [hg] using hb', hQ.1, ?_⟩
  intro r h1 h2 h3 h4
  exact he.regs_eq_of_not_mem_writtenRegs (by
    simp [forList, forUp, emitWhenProg, emitProg, Cmd.writtenRegs, h1, h2, h3, h4])


end GraphMinor.Compute.Crossing
