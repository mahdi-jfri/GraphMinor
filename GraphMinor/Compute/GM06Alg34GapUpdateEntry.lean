module

public import GraphMinor.Compute.GM06Alg34GapUpdateRead
public import GraphMinor.Compute.GM06Alg34GapUpdateEmit
public import GraphMinor.Compute.GM06Alg34GapRegionQuery

/-!
# Updating one supplied cuff gap on the RAM

Test the supplied cuff vertex's survival. For a surviving vertex, read
its old incident region, compute its new region number, and emit that
number. For a deleted vertex emit nothing. The finite update therefore
keeps exactly the gaps paired with surviving vertices, in their old order.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Update the cuff gap at 6403, emitting retained labels to buffer 48. -/
def gm06GapUpdateEntryProg : Cmd :=
  .ite gm06GapUpdateActiveExpr
    (.seq (.assign 6402 gm06GapUpdateRegionExpr)
      (.seq gm06GapRegionQueryProg gm06GapUpdateEmitProg)) .skip

/-- One gap update emits exactly its reindexed region when its supplied
vertex survives and otherwise leaves the buffer and count unchanged. -/
theorem gm06GapUpdateEntryProg_exec {w k : ℕ} (x : GM06DrawingData)
    (vs L : List (Fin x.n)) (g : Fin L.length → Fin x.regions.length)
    (i : Fin L.length) (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w) (hK : L.length < 2 ^ w)
    (hk : k + 1 < 2 ^ w) {s : State} (hsize : s.regs 4 = x.cellCount)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hi : s.regs 6403 = i.val) (hcount : s.regs 6404 = k)
    (hcap : k < (s.arrs 48).length) (hL : s.arrs 2 = L.map Fin.val)
    (hR : s.arrs 47 = List.ofFn (fun j => (g j).val))
    (hv : s.arrs 4 = gm06VertexMask vs)
    (hlists : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s)
    (hlen : (s.arrs 32).length = x.cellCount * x.cellCount)
    (hmask : s.arrs 36 = gm06RootMask x vs)
    (hranks : s.arrs 37 = List.ofFn (fun b : Fin x.cellCount => ((gm06RootMask x vs).take b.val).sum)) :
    ∃ s' t, Exec w gm06GapUpdateEntryProg s s' t ∧
      t ≤ 26 * (x.cellCount * x.cellCount) + 37 * x.cellCount + 50 ∧
      s'.arrs 48 = (if L.get i ∈ vs then
        (s.arrs 48).set k (x.regionAfterDeletion vs (g i)).val else s.arrs 48) ∧
      s'.regs 6404 = k + (if L.get i ∈ vs then 1 else 0) ∧
      (∀ A : ℕ, A ≠ 33 → A ≠ 34 → A ≠ 48 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, (q < 190 ∨ 197 ≤ q) → q ≠ 187 → q ≠ 6400 → q ≠ 6401 →
        q ≠ 6402 → q ≠ 6404 → s'.regs q = s.regs q) := by
  have hnle : x.n ≤ x.cellCount := by dsimp only [GM06DrawingData.cellCount]; omega
  have hrle : x.regions.length ≤ x.cellCount := by dsimp only [GM06DrawingData.cellCount]; omega
  have htest := gm06GapUpdateActiveExpr_eval vs L i hw (hnle.trans_lt hN) hK hi hL hv
  by_cases hkeep : L.get i ∈ vs
  · have htest' : gm06GapUpdateActiveExpr.eval w s = some 1 := by simpa only [ite_eq_left hkeep] using htest
    have hread := gm06GapUpdateRegionExpr_eval g i hK (hrle.trans_lt hN) hi hR
    let s₁ := s.setReg 6402 (g i).val
    have hex₁ : Exec w (.assign 6402 gm06GapUpdateRegionExpr) s s₁ 3 := .assign hread
    have hlists₁ : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s₁ := hlists
    obtain ⟨s₂, t₂, hex₂, ht₂, hvalue, harr₂, hreg₂⟩ :=
      gm06GapRegionQueryProg_exec x vs (g i) hw hN hsquare
        (by simpa [s₁] using hsize) (by simpa [s₁] using hn)
        (by simpa [s₁] using hm) (by simp [s₁]) hlists₁ hlen hmask hranks
    have hcount₂ : s₂.regs 6404 = k :=
      (hreg₂ _ (Or.inr (by decide)) (by decide) (by decide) (by decide)).trans
        (by simpa [s₁] using hcount)
    have hcap₂ : k < (s₂.arrs 48).length := by rw [harr₂ 48 (by decide) (by decide)]; exact hcap
    have hbound : (x.regionAfterDeletion vs (g i)).val < 2 ^ w := by
      have hh : (x.regionAfterDeletion vs (g i)).val < (x.regionRoots vs).length := by
        simpa only [x.inducedData_regions_length vs] using (x.regionAfterDeletion vs (g i)).isLt
      have hrootlen := gm06RootMask_sum_le x vs
      rw [gm06RootMask_sum] at hrootlen
      exact (hh.trans_le hrootlen).trans hN
    let s₃ := (s₂.writeArr 48 k (x.regionAfterDeletion vs (g i)).val).setReg 6404 (k + 1)
    have hex₃ : Exec w gm06GapUpdateEmitProg s₂ s₃ 7 :=
      gm06GapUpdateEmitProg_exec hw hk hbound hcount₂ hvalue hcap₂
    refine ⟨s₃, 3 + (3 + (t₂ + 7)), .ite_true htest' (by decide) (.seq hex₁ (.seq hex₂ hex₃)),
      by omega, ?_, by simp only [s₃, State.setReg_regs_self, ite_eq_left hkeep], ?_, ?_⟩
    · simp only [s₃, State.setReg_arrs, State.writeArr_arrs_self, hkeep, ↓reduceIte]
      rw [harr₂ 48 (by decide) (by decide)]
      rfl
    · intro A hA hA' hA''
      exact (State.writeArr_arrs_ne _ _ _ hA'').trans (harr₂ A hA hA')
    · intro q hq hq' hq₀ hq₁ hq₂ hq₄
      exact (State.setReg_regs_ne _ _ hq₄).trans
        ((hreg₂ q hq hq' hq₀ hq₁).trans (State.setReg_regs_ne _ _ hq₂))
  · have htest' : gm06GapUpdateActiveExpr.eval w s = some 0 := by simpa only [ite_eq_right hkeep] using htest
    exact ⟨s, 4, .ite_false htest' (.skip s), by omega, by simp only [ite_eq_right hkeep],
      by simp only [ite_eq_right hkeep, Nat.add_zero, hcount], fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

end GraphMinor.Compute
