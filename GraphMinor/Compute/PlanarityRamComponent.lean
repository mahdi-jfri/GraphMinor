module

public import GraphMinor.Compute.PlanarityRamSearchKeep

/-!
# The whole DFS component loop

The one-step refinement is iterated using the exact decrease of remaining
work. Each loop condition costs one step and each body at most 200. The
bound charges 201 steps to each consumed work unit and one final condition.
The successful functional result is `searchFrames` with the given fuel.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

private theorem component_time_add (before after final step rest : ℕ)
    (hwork : after + 1 = before) (hfinal : final ≤ after)
    (hstep : step ≤ 200) (hrest : rest ≤ 201 * (after - final) + 1) :
    1 + (step + rest) ≤ 201 * (before - final) + 1 := by omega

/-- The component loop refines `searchFrames` with a linear bound in the
work it actually consumes. The hypotheses are adjacency encoding, the two
memory relations, the functional invariants and record budget, word bounds,
and fuel greater than remaining work. -/
theorem searchComponentProg_refines {N M w : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} (fuel : ℕ) (search : Search) (stack : List Frame) (s : State)
    (hadj : IsAdjList G 30 31 32 lists s)
    (h : DfsSearchAt N M s search) (hf : FramesAt N s stack)
    (hb : SearchBounded N search) (hs : FrameInvariant (List.ofFn lists).toArray search stack)
    (hbudget : search.edges.size + searchWork (List.ofFn lists).toArray 0 search stack ≤ M)
    (hw : 2 * (N + M + 2) < 2 ^ w) (hentries : (s.arrs 32).length < 2 ^ w)
    (hfuel : searchWork (List.ofFn lists).toArray 1 search stack < fuel) :
    ∃ result s' t,
      searchFrames (List.ofFn lists).toArray fuel search stack = some result ∧
      Exec w searchComponentProg s s' t ∧
      t ≤ 201 * (searchWork (List.ofFn lists).toArray 1 search stack -
        searchWork (List.ofFn lists).toArray 1 result []) + 1 ∧
      FramesAt N s' [] ∧ DfsSearchAt N M s' result ∧ SearchBounded N result ∧
      FrameInvariant (List.ofFn lists).toArray result [] ∧
      searchWork (List.ofFn lists).toArray 1 result [] ≤ searchWork (List.ofFn lists).toArray 1 search stack ∧
      result.edges.size + searchWork (List.ofFn lists).toArray 0 result [] ≤ M := by
  induction fuel generalizing search stack s with
  | zero => omega
  | succ fuel ih =>
    cases stack with
    | nil =>
      refine ⟨search, s, 1, rfl, ?_, by simp, hf, h, hb, hs, le_rfl, hbudget⟩
      apply Exec.while_false
      simp [Expr.eval, hf.1]
    | cons f stack =>
      obtain ⟨next, nextStack, s1, t1, hstep, hx1, ht1, hf1, h1⟩ :=
        searchFrameStepProg_refines hadj h hf hb hs hbudget hw hentries
      obtain ⟨invSearch, invStack, hinv, hbInv, hsInv, hwork, hrecords⟩ :=
        frameStep_invariant (List.ofFn lists).toArray (adjacency_labels_valid hadj.2)
          search f stack (by simpa using hb) hs
      have heq : (invSearch, invStack) = (next, nextStack) := Option.some.inj (hinv.symm.trans hstep)
      have heqParts := Prod.mk.inj heq
      obtain ⟨heqSearch, heqStack⟩ := heqParts
      subst invSearch
      subst invStack
      have hb1 : SearchBounded N next := by simpa using hbInv
      have hbudget1 : next.edges.size + searchWork (List.ofFn lists).toArray 0 next nextStack ≤ M :=
        Nat.le_trans hrecords hbudget
      have hadj1 := searchFrameStepProg_adj hadj hx1
      have hentries1 : (s1.arrs 32).length < 2 ^ w := by
        rw [searchFrameStepProg_input_eq hx1 32 (by decide)]
        exact hentries
      obtain ⟨result, s2, t2, hresult, hx2, ht2, hf2, h2, hb2, hs2, hwork2, hbudget2⟩ :=
        ih next nextStack s1 hadj1 h1 hf1 hb1 hsInv hbudget1 hentries1 (by omega)
      have hcapacity : stack.length + 1 ≤ N := by
        have hh := hs.capacity
        simp only [List.length_cons, List.size_toArray, List.length_ofFn] at hh
        omega
      have hcount : s.regs 38 = stack.length + 1 := by simpa using hf.1
      have hcond : (Expr.reg 38).eval w s = some (stack.length + 1) := by
        simpa [Expr.eval, hcount] using checkWord_of_lt (show stack.length + 1 < 2 ^ w by omega)
      refine ⟨result, s2, 1 + (t1 + t2), ?_,
        (by simpa only [searchComponentProg, Expr.cost, Nat.add_assoc] using
          Exec.while_true hcond (by omega) hx1 hx2),
        component_time_add _ _ _ _ _ hwork hwork2 ht1 ht2, hf2, h2, hb2, hs2, ?_, hbudget2⟩
      · rw [searchFrames_step, hstep]
        exact hresult
      · omega

end GraphMinor.Compute.PlanarityRam
