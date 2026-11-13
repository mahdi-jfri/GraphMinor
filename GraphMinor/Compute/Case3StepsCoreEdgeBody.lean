module

public import GraphMinor.Compute.Case3StepsReadCoreEdgeProg
public import GraphMinor.Compute.Case3StepsCoreEdgeLabelProg

/-!
# Writing one core-edge representative

The program reads a canonical edge and tests whether both endpoints lie in
the core. Such an edge is assigned its merged boundary label. Other edges
receive the missing sentinel because their member is determined by an
outside endpoint's component. This is the core-edge part of step (5).
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Test membership of both endpoint registers in the core. -/
def case3BothCoreExpr : Expr := .op .mul (.read 10 (.reg 42)) (.read 10 (.reg 43))

/-- Read an edge and write its group label to array 28. -/
def case3CoreEdgeBody : Cmd :=
  .seq case3ReadCoreEdgeProg
    (.ite case3BothCoreExpr
      (.seq case3CoreEdgeLabelProg (.write 28 (.reg 18) (.reg 44)))
      (.write 28 (.reg 18) (.op .add (.reg 14) (.reg 17))))

private theorem bothCore_eval {w n : ℕ} (Z : Finset (Fin n)) (u v : Fin n)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) {s : State}
    (hZ : IsBitSet Z 10 s) (hru : s.regs 42 = u.1) (hrv : s.regs 43 = v.1) :
    case3BothCoreExpr.eval w s = some (if u ∈ Z ∧ v ∈ Z then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  have huw : u.1 < 2 ^ w := u.2.trans hn
  have hvw : v.1 < 2 ^ w := v.2.trans hn
  have hui : u.1 < (s.arrs 10).length := by rw [hZ.1]; exact u.2
  have hvi : v.1 < (s.arrs 10).length := by rw [hZ.1]; exact v.2
  have hub : (s.arrs 10)[u.1]'hui = if u ∈ Z then 1 else 0 := by
    simpa only [hZ.arr_eq_bitSetList] using getElem_bitSetList Z u.1 u.2
  have hvb : (s.arrs 10)[v.1]'hvi = if v ∈ Z then 1 else 0 := by
    simpa only [hZ.arr_eq_bitSetList] using getElem_bitSetList Z v.1 v.2
  by_cases hu : u ∈ Z <;> by_cases hv : v ∈ Z <;>
    simp [case3BothCoreExpr, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hru, hrv, huw, hvw, hui, hvi, hub, hvb, hu, hv, hw, h0]

/-- One core-edge iteration takes at most `56 n + 50` steps. Its graph,
core, component-key, and component-representative arrays are retained. -/
theorem case3CoreEdgeBody_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (j : Fin (case3InputEdges x).length)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    (hsum : x.n + (case3InputEdges x).length < 2 ^ w)
    {s : State} (hin : s.arrs 16 = encGraph x.G) (hZ : IsBitSet d.core.Z 10 s)
    (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z)
    (hlen : (s.arrs 28).length = (case3InputEdges x).length)
    (hrn : s.regs 14 = x.n) (hrm : s.regs 17 = (case3InputEdges x).length)
    (hrj : s.regs 18 = j.1) :
    ∃ s' t, Exec w case3CoreEdgeBody s s' t ∧ t ≤ 56 * x.n + 50 ∧
      s'.arrs 28 = (s.arrs 28).set j.1
        (let e := (case3InputEdges x)[j.1]
         if e.1 ∈ d.core.Z ∧ e.2 ∈ d.core.Z then
           case3CoreEdgeRepresentative x d.core.Z e.1 e.2 j.1
         else x.n + (case3InputEdges x).length) ∧
      (∀ a, a ≠ 25 → a ≠ 28 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 40 → r ≠ 41 → r ≠ 42 → r ≠ 43 → r ≠ 44 → s'.regs r = s.regs r) := by
  classical
  let u := ((case3InputEdges x)[j.1]).1
  let v := ((case3InputEdges x)[j.1]).2
  have huv : u < v := (case3InputEdges_get_spec x j).1
  have hnw : x.n < 2 ^ w := by omega
  have hjw : j.1 < 2 ^ w := by have := j.2; omega
  have hsumj : x.n + j.1 < 2 ^ w := by have := j.2; omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hru₁, hrv₁, harr₁, hreg₁⟩ :=
    case3ReadCoreEdgeProg_exec x j (by omega) hnw hm hin hrj
  have hrn₁ : s₁.regs 14 = x.n := (hreg₁ 14 (by decide) (by decide) (by decide)).trans hrn
  have hrm₁ : s₁.regs 17 = (case3InputEdges x).length :=
    (hreg₁ 17 (by decide) (by decide) (by decide)).trans hrm
  have hrj₁ : s₁.regs 18 = j.1 := (hreg₁ 18 (by decide) (by decide) (by decide)).trans hrj
  have hZ₁ : IsBitSet d.core.Z 10 s₁ := hZ.of_arr_eq (harr₁ 10)
  have htab₁ : s₁.arrs 26 = case3AttachmentKeys x d.core.Z := (harr₁ 26).trans htab
  have hc := bothCore_eval d.core.Z u v (by omega) hnw hZ₁ hru₁ hrv₁
  by_cases hcore : u ∈ d.core.Z ∧ v ∈ d.core.Z
  · have hc' : case3BothCoreExpr.eval w s₁ = some 1 := by simpa [hcore] using hc
    obtain ⟨s₂, t₂, hex₂, ht₂, hlabel₂, harr₂, hreg₂⟩ :=
      case3CoreEdgeLabelProg_exec x d hd u v huv j.1 hw hn hkeys hsumj
        hZ₁ htab₁ hrn₁ hrj₁ hru₁ hrv₁
    have hrj₂ : s₂.regs 18 = j.1 := (hreg₂ 18 (by decide) (by decide) (by decide)).trans hrj₁
    have harr28 : s₂.arrs 28 = s.arrs 28 := (harr₂ 28 (by decide)).trans (harr₁ 28)
    have hlabelw : case3CoreEdgeRepresentative x d.core.Z u v j.1 < 2 ^ w :=
      (case3CoreEdgeRepresentative_lt x d.core.Z u v j.1 j.2).trans hsum
    have hex₃ : Exec w (.write 28 (.reg 18) (.reg 44)) s₂
        (s₂.writeArr 28 j.1 (case3CoreEdgeRepresentative x d.core.Z u v j.1)) 3 :=
      .write (by simp only [Expr.eval, checkWord, hrj₂, hjw, ↓reduceIte])
        (by simp only [Expr.eval, checkWord, hlabel₂, hlabelw, ↓reduceIte])
        (by rw [harr28, hlen]; exact j.2)
    refine ⟨s₂.writeArr 28 j.1 (case3CoreEdgeRepresentative x d.core.Z u v j.1),
      t₁ + (5 + (t₂ + 3)), .seq hex₁ (.ite_true (t := t₂ + 3) hc' (by decide) (.seq hex₂ hex₃)),
      by omega, ?_, ?_, ?_⟩
    · simp [u, v, State.writeArr_arrs_self, harr28, hcore]
    · intro a h25 h28
      exact (State.writeArr_arrs_ne _ _ _ h28).trans ((harr₂ a h25).trans (harr₁ a))
    · intro r h40 h41 h42 h43 h44
      rw [State.writeArr_regs, hreg₂ r h40 h41 h44]
      exact hreg₁ r h42 h43 h44
  · have hc' : case3BothCoreExpr.eval w s₁ = some 0 := by simpa [hcore] using hc
    have hex₂ : Exec w (.write 28 (.reg 18) (.op .add (.reg 14) (.reg 17))) s₁
        (s₁.writeArr 28 j.1 (x.n + (case3InputEdges x).length)) 5 :=
      .write (by simp only [Expr.eval, checkWord, hrj₁, hjw, ↓reduceIte])
        (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrn₁, hrm₁, hnw, hsum,
          show (case3InputEdges x).length < 2 ^ w by omega])
        (by rw [harr₁ 28, hlen]; exact j.2)
    refine ⟨s₁.writeArr 28 j.1 (x.n + (case3InputEdges x).length), t₁ + 10,
      .seq hex₁ (.ite_false (t := 5) hc' hex₂), by omega, ?_, ?_, ?_⟩
    · simp only [u, v, State.writeArr_arrs_self, harr₁ 28, hcore, ↓reduceIte]
    · intro a _ h28
      exact (State.writeArr_arrs_ne _ _ _ h28).trans (harr₁ a)
    · intro r _ _ h42 h43 h44
      exact hreg₁ r h42 h43 h44

end GraphMinor.Compute
