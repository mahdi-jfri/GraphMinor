module

public import GraphMinor.Compute.GM02TerminatedInput
public import GraphMinor.Compute.GM13SocietyTabulate

/-!
# Constructing the all-vertex subset for routine A1

Routine A1 applies the separator algorithm with the whole vertex set.
Read the vertex count from the plain graph header and write one bit for
every vertex. The routine does not inspect the endpoint suffix.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing TwoPaths

/-- Build all-vertex membership bits, using loop counter 282. -/
def gm02AllVertexSupportProg (src dst : Arr) : Cmd :=
  gm13TabulateProg 282 (.read src (.const 0)) (.const 1) dst

/-- The A1 subset builder reads only the plain vertex-count header and
writes the all-one array in linear time. -/
theorem gm02AllVertexSupportProg_exec {w : ℕ} (x : GM02SimpleTerminatedInput)
    (src dst : Arr) (hne : src ≠ dst) (s : State) (hsrc : s.arrs src = x.enc)
    (hn : x.n < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t, Exec w (gm02AllVertexSupportProg src dst) s s' t ∧
      t ≤ 8 + 14 * x.n ∧ Keeps [282] [dst] s s' ∧
      s'.arrs dst = List.replicate x.n 1 := by
  obtain ⟨s', t, he, ht, hk, hout⟩ := gm13TabulateProg_exec (w := w) 282
    (.read src (.const 0)) (.const 1) dst (List.replicate x.n 1) s hw
    (by simpa only [List.length_replicate] using hn)
    (fun st hk => by
      have hsa : st.arrs src = x.enc :=
        (hk.2 _ (by simpa only [List.mem_singleton] using hne)).trans hsrc
      simp [Expr.eval, hsa, GM02SimpleTerminatedInput.enc, encGraph,
        checkWord_of_lt (by omega : 0 < 2 ^ w), checkWord_of_lt hn])
    (fun st i hi _ _ => by
      simpa only [List.getElem_replicate] using (eval_const (s := st) hw))
  refine ⟨s', t, he, ?_, hk, hout⟩
  simp only [Expr.cost_read, Expr.cost_const, List.length_replicate] at ht
  omega

end GraphMinor.Compute
