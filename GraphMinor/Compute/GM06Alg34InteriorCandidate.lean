module

public import GraphMinor.Compute.GM06Alg34ComponentQuery
public import GraphMinor.Compute.GM06Alg34KeepSingleton

/-!
# Retaining the first cuff-disjoint component found

Query the component of the current supplied source label. Copy that
label into the candidate register and use the verified first-candidate
retainer. An earlier successful source is kept, and a successful current
query is retained exactly when no earlier source was found.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Query the current source and retain it if it is the first interior component. -/
def gm06InteriorCandidateProg : Cmd :=
  .seq gm06ComponentQueryProg (.seq (.assign 111 (.reg 187)) gm06KeepSingletonProg)

/-- A query followed by the retainer computes exactly first-success
option combination, changing no input or adjacency arrays. -/
theorem gm06InteriorCandidateProg_exec {w : ℕ} (x : GM06DrawingData) {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) (a : Fin x.n) (found : Option ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) (hsquare : x.n * x.n < 2 ^ w)
    (hinputSize : x.words.length < 2 ^ w) {s : State}
    (hinput : s.arrs 0 = x.words) (hsize : s.regs 4 = x.n)
    (hsource : s.regs 187 = a.val) (hcount : s.regs 105 = L.length)
    (hstart : s.regs 261 = x.cuffOffset + 2)
    (hlists : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s)
    (hlen : (s.arrs 32).length = x.n * x.n) (hfound : gm06SingletonRegs found s) :
    ∃ s' t, Exec w gm06InteriorCandidateProg s s' t ∧
      t ≤ 26 * (x.n * x.n) + 23 * x.n + 22 * L.length + 41 ∧
      gm06SingletonRegs (found.or (if x.isInteriorComponent a then some a.val else none)) s' ∧
      (∀ A : ℕ, A ≠ 33 → A ≠ 34 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, (q < 190 ∨ 197 ≤ q) → q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 111 →
        q ≠ 112 → q ≠ 113 → q ≠ 114 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hflag₁, _, ha₁, hg₁⟩ :=
    gm06ComponentQueryProg_exec x hL a hw hn hsquare hinputSize hinput hsize hsource hcount hstart hlists hlen
  let candidate : Option ℕ := if x.isInteriorComponent a then some a.val else none
  have hcandidate : ∀ v, candidate = some v → v = a.val := by
    intro v hv
    cases hb : x.isInteriorComponent a <;> simp [candidate, hb] at hv
    exact hv.symm
  let s₂ := s₁.setReg 111 a.val
  have hsource₁ : s₁.regs 187 = a.val :=
    (hg₁ 187 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsource
  have hex₂ : Exec w (.assign 111 (.reg 187)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hsource₁, a.isLt.trans hn])
  have hfound₂ : gm06SingletonRegs found s₂ := by
    constructor
    · exact (hg₁ 113 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfound.1
    · intro v hv
      exact (hg₁ 114 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hfound.2 v hv)
  have hflag₂ : s₂.regs 112 = (if candidate.isSome then 1 else 0) := by
    change s₁.regs 112 = _
    rw [hflag₁]
    cases hb : x.isInteriorComponent a <;> simp [candidate, hb]
  obtain ⟨s₃, t₃, hex₃, ht₃, hfound₃, ha₃, hg₃⟩ :=
    gm06KeepSingletonProg_exec found candidate hw
      (fun v hv => (hcandidate v hv) ▸ a.isLt.trans hn) hfound₂ hflag₂
      (by intro v hv; rw [hcandidate v hv]; simp [s₂])
  refine ⟨s₃, t₁ + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hfound₃, ?_, ?_⟩
  · intro A h33 h34
    exact (ha₃ A).trans (ha₁ A h33 h34)
  · intro q hq h103 h108 h109 h111 h112 h113 h114
    rw [hg₃ q h113 h114]
    change (s₁.setReg 111 a.val).regs q = _
    rw [State.setReg_regs_ne _ _ h111]
    exact hg₁ q hq h103 h108 h109 h112

end GraphMinor.Compute
