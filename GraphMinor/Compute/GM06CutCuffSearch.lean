module

public import GraphMinor.Compute.GM06CutAdjacencyMath
public import GraphMinor.Compute.GM06ComponentSearch

/-!
# Starting a cut component search at its inner cuff edge

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) indexes a
component by the positive dart of its inner cuff edge. Original inner edge i
has label m+i. Its copied dart is 4*(m+i). The program computes this
address, reads the actual copied origin and uses it as the source of
the complete queue search. No component label or search root is supplied.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Address of the positive copied inner cuff dart at runtime index 667. -/
def gm06CutInnerDartExpr : Expr :=
  .op .mul (.const 4) (.op .add (.reg 649) (.reg 667))

/-- The cuff address expression retains the original permanent edge base. -/
theorem gm06CutInnerDartExpr_eval {w m i : ℕ} (s : State)
    (hw : 4 < 2 ^ w) (hfit : 4 * (m + i) < 2 ^ w)
    (h649 : s.regs 649 = m) (h667 : s.regs 667 = i) :
    gm06CutInnerDartExpr.eval w s = some (4 * (m + i)) := by
  exact GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw)
    (GraphMinor.Compute.Crossing.eval_add (GraphMinor.Compute.Crossing.eval_reg h649 (by omega))
      (GraphMinor.Compute.Crossing.eval_reg h667 (by omega)) (by omega)) hfit

/-- Read the inner cuff dart's origin, then search its whole component. -/
def gm06CutCuffSearchProg : Cmd :=
  .seq (.assign 644 (.read 626 gm06CutInnerDartExpr)) gm06ComponentSearchProg

/-- Exact component bits from an actual inner cuff edge. The root bound
comes from the endpoint table, rather than an assumed search answer. -/
theorem gm06CutCuffSearchProg_exec {w n m i : ℕ} (data : GM06CutData)
    (s : State) (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    (horgFit : data.origins.length < 2 ^ w) (hidx : 4 * (m + i) < data.origins.length)
    (hvalues : ∀ v ∈ data.origins, v < n)
    (h620 : s.regs 620 = n) (h649 : s.regs 649 = m) (h667 : s.regs 667 = i)
    (h626 : s.arrs 626 = data.origins)
    (hadj : IsAdjList (gm06CutGraph n data) 620 621 622 (gm06CutAdjacencyLists n data) s)
    (hentries : (s.arrs 622).length < 2 ^ w) :
    let r := gm06CutInnerRoot data m i
    let hr : r < n := by
      change data.origins[4 * (m + i)]?.getD 0 < n
      simpa only [List.getElem?_eq_getElem hidx, Option.getD_some] using
        hvalues _ (List.getElem_mem hidx)
    ∃ sf t, Exec w gm06CutCuffSearchProg s sf t ∧
      t ≤ 67 + 22 * n + 29 * totalAdjEntries (gm06CutAdjacencyLists n data) ∧
      Keeps (644 :: List.range' 630 11) [630, 631, 632, 633] s sf ∧
      sf.arrs 630 = gm06ComponentBits (gm06CutGraph n data) ⟨r, hr⟩ := by
  have hr : gm06CutInnerRoot data m i < n := by
    simpa only [gm06CutInnerRoot, List.getElem?_eq_getElem hidx, Option.getD_some] using
      hvalues _ (List.getElem_mem hidx)
  have hrootGet : data.origins[4 * (m + i)] = gm06CutInnerRoot data m i := by
    simp only [gm06CutInnerRoot, List.getElem?_eq_getElem hidx, Option.getD_some]
  let s₀ := s.setReg 644 (gm06CutInnerRoot data m i)
  have he₀ : Exec w (.assign 644 (.read 626 gm06CutInnerDartExpr)) s s₀ 7 :=
    .assign (by
      have he := GraphMinor.Compute.Crossing.eval_read (a := 626)
        (gm06CutInnerDartExpr_eval s hw (hidx.trans horgFit) h649 h667)
        (by simpa only [h626] using hidx) (by simpa only [h626, hrootGet] using hr.trans hn)
      simpa only [h626, hrootGet] using he)
  obtain ⟨sf, tf, hef, htf, hkf, hbf⟩ := gm06ComponentSearchProg_exec
    (gm06CutGraph n data) (gm06CutAdjacencyLists n data) ⟨gm06CutInnerRoot data m i, hr⟩ s₀
    hw hn (by simpa [s₀] using h620) (by simp [s₀]) hadj hentries
  refine ⟨sf, 7 + tf, .seq he₀ hef, by omega,
    ((Keeps.refl _ _ s).setReg (by simp) _).trans hkf (by intro r hr; exact List.mem_cons_of_mem _ hr) (fun _ h => h), hbf⟩

end GraphMinor.Compute
