module

public import GraphMinor.Compute.GM06CutVertexCopies
public import GraphMinor.Compute.GM13SocietyTabulate

/-!
# Computing the live vertex list of the cut graph

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) copies
linkage vertices twice and keeps every other live vertex once. This pass
scans only the original live labels, reads their computed incoming
and outgoing marks, and emits their prescribed copies. The returned
list therefore excludes deleted labels and unused right slots.
The exact output and a linear RAM bound follow from the local
vertex-emission lemma and the finite buffer invariant.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Copied live labels stay in the doubled permanent vertex space. -/
theorem gm06CutVertexCopies_bound {n v : ℕ} (marks : GM06CutTables) (hv : v < n) :
    ∀ u ∈ gm06CutVertexCopies marks v, u < 2 * n := by
  intro u hu
  unfold gm06CutVertexCopies at hu
  split_ifs at hu <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  · subst u
    omega
  · rcases hu with rfl | rfl <;> omega

/-- Compute live copied labels 629 from original live labels 618,
using the two computed path-mark tables 620/621 and buffer 619. -/
def gm06CutVertexProg : Cmd :=
  .seq (.alloc 619 (.op .mul (.const 2) (.len 618)))
    (.seq (.assign 653 (.const 0))
      (.seq (GraphMinor.Compute.Crossing.forArrProg 618 650 651 652 gm06CutVertexEmitProg)
        (gm13TabulateProg 650 (.reg 653) (.read 619 (.reg 650)) 629)))

/-- Exact construction of all and only live copied vertices.
Every membership decision comes from the computed path-mark tables. -/
theorem gm06CutVertexProg_exec {w n : ℕ} (marks : GM06CutTables) (live : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : 2 * n < 2 ^ w) (hfit : 2 * live.length + 2 < 2 ^ w)
    (hin : marks.incoming.length = n) (hout : marks.outgoing.length = n)
    (hwords : ∀ x ∈ marks.incoming ++ marks.outgoing, x < 2 ^ w)
    (hlive : ∀ v ∈ live, v < n)
    (h620 : s.arrs 620 = marks.incoming) (h621 : s.arrs 621 = marks.outgoing) (h618 : s.arrs 618 = live) :
    ∃ sf t, Exec w gm06CutVertexProg s sf t ∧ t ≤ 30 + 110 * live.length ∧
      Keeps [650, 651, 652, 653] [619, 629] s sf ∧ sf.arrs 629 = gm06CutVertices marks live := by
  have hw1 : 1 < 2 ^ w := by omega
  have hn' : n < 2 ^ w := by omega
  have hl : live.length < 2 ^ w := by omega
  let out := gm06CutVertices marks live
  have houtlen : out.length ≤ 2 * live.length := gm06CutVertices_length_le _ _
  have houtwords : ∀ u ∈ out, u < 2 ^ w := by
    intro u hu
    change u ∈ gm06CutVertices marks live at hu
    rw [gm06CutVertices_eq_flatMap] at hu
    obtain ⟨v, hv, hu⟩ := List.mem_flatMap.mp hu
    exact (gm06CutVertexCopies_bound marks (hlive v hv) u hu).trans hn
  let s₁ := s.setArr 619 (List.replicate (2 * live.length) 0)
  let s₂ := s₁.setReg 653 0
  have he₁ : Exec w (.alloc 619 (.op .mul (.const 2) (.len 618))) s s₁ (3 + 2 * live.length) :=
    .alloc (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw)
      (GraphMinor.Compute.Crossing.eval_len h618 hl) (by omega))
  have he₂ : Exec w (.assign 653 (.const 0)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hk₀ : Keeps [650, 651, 652, 653] [619] s s₂ :=
    ((Keeps.refl _ _ s).setArr (by simp) _).setReg (by simp) _
  let Q := fun (_ : ℕ) (z : State) => (∀ A, A ≠ 619 → z.arrs A = s₂.arrs A) ∧
    (∀ r, r ≠ 650 → r ≠ 651 → r ≠ 652 → r ≠ 653 → z.regs r = s₂.regs r)
  obtain ⟨s₃, t₃, he₃, ht₃, hQ₃, hb₃⟩ := GraphMinor.Compute.Crossing.forArrEmit_exec
    (s := s₂) (pre := []) (k := 2 * live.length)
    618 650 651 652 619 653 gm06CutVertexEmitProg (gm06CutVertexCopies marks) Q 60
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw1
    (by simpa [s₂, s₁, h618] using hl)
    (by simpa [s₂, s₁, h618] using fun v hv => (hlive v hv).trans hn')
    ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩ (by simp [GraphMinor.Compute.Crossing.IsBuf, s₂, s₁])
    (by simpa only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ (by decide : 618 ≠ 619),
      h618, ← gm06CutVertices_eq_flatMap] using houtlen)
    (fun _ z z' h harr hreg => ⟨fun A hA => (congrFun harr A).trans (h.1 A hA),
      fun r h1 h2 h3 h4 => (hreg r h1 h2 h3).trans (h.2 r h1 h2 h3 h4)⟩)
    (fun _ z h => h.1 618 (by decide))
    (fun j hj z pre cap h hri hrn hry hb hcap htotal => by
      have hsource : s₂.arrs 618 = live := by simp [s₂, s₁, h618]
      have hvLive : (s₂.arrs 618)[j] ∈ live := by rw [← hsource]; exact List.getElem_mem hj
      obtain ⟨z', t', he', ht', hk', hb'⟩ := gm06CutVertexEmitProg_exec marks pre z hw hn
        (hlive _ hvLive) hin hout hwords
        ((h.1 620 (by decide)).trans ((hk₀.2 620 (by decide)).trans h620))
        ((h.1 621 (by decide)).trans ((hk₀.2 621 (by decide)).trans h621)) hry hb hcap (by simp only [List.length_nil, Nat.zero_add] at htotal; omega)
      refine ⟨z', t', he', ht', ⟨?_, ?_⟩,
        (hk'.1 650 (by decide)).trans hri, (hk'.1 651 (by decide)).trans hrn, hb'⟩
      · intro A hA
        exact (hk'.2 A (by simpa using hA)).trans (h.1 A hA)
      · intro r h1 h2 h3 h4
        exact (hk'.1 r (by simpa using h4)).trans (h.2 r h1 h2 h3 h4))
  have hbuffer : s₃.arrs 619 = out ++ List.replicate (2 * live.length - out.length) 0 := by
    simpa only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ (by decide : 618 ≠ 619),
      h618, ← gm06CutVertices_eq_flatMap, List.nil_append] using hb₃.1
  have hcursor : s₃.regs 653 = out.length := by
    simpa only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ (by decide : 618 ≠ 619),
      h618, ← gm06CutVertices_eq_flatMap, List.nil_append] using hb₃.2
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm13TabulateProg_exec
    650 (.reg 653) (.read 619 (.reg 650)) 629 out s₃ hw1 (by omega)
    (fun st hk => GraphMinor.Compute.Crossing.eval_reg ((hk.1 653 (by decide)).trans hcursor) (by omega))
    (fun st i hi hk hidx => by
      have hb : st.arrs 619 = out ++ List.replicate (2 * live.length - out.length) 0 :=
        (hk.2 619 (by decide)).trans hbuffer
      have he := GraphMinor.Compute.Crossing.eval_read (a := 619) (w := w)
        (GraphMinor.Compute.Crossing.eval_reg hidx (by omega))
        (by simp only [hb, List.length_append, List.length_replicate]; omega)
        (by simpa [hb, List.getElem_append_left hi] using houtwords _ (List.getElem_mem hi))
      simpa [hb, List.getElem_append_left hi] using he)
  have hk₃ : Keeps [650, 651, 652, 653] [619] s₂ s₃ := by
    constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact hQ₃.2 r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
    · intro A hA
      exact hQ₃.1 A (by simpa using hA)
  refine ⟨sf, (3 + 2 * live.length) + (2 + (t₃ + tf)), .seq he₁ (.seq he₂ (.seq he₃ hef)), ?_,
    ((hk₀.trans hk₃ (fun _ h => h) (fun _ h => h)).mono (fun _ h => h) (by simp)).trans hkf (by simp) (by simp), hdf⟩
  simp only [Expr.cost, s₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ (by decide : 618 ≠ 619), h618] at ht₃ htf
  omega

end GraphMinor.Compute
