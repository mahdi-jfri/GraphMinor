module

public import GraphMinor.Compute.GM06Alg34GapUpdateLoop

/-!
# Allocating the retained-gap output buffer

Reserve one word for every old gap and initialize the scan and live
count. The cuff scan then fills exactly the retained and reindexed
region words in the buffer's live prefix. This accepts arbitrary old
scratch contents and uses no geometric information.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Build the live prefix of updated gap region labels in array 48. -/
def gm06GapUpdatePrepareProg : Cmd :=
  .seq (.alloc 48 (.len 47))
    (.seq (.assign 6403 (.const 0))
      (.seq (.assign 6404 (.const 0)) gm06GapUpdateLoopProg))

/-- The prepared gap output is exactly the finite induced gap list,
with a cubic time bound and one reserved word per supplied old gap. -/
theorem gm06GapUpdatePrepareProg_exec {w : ℕ} (x : GM06DrawingData)
    (vs L : List (Fin x.n)) (g : Fin L.length → Fin x.regions.length)
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w) (hK : L.length < 2 ^ w)
    {s : State} (hsize : s.regs 4 = x.cellCount) (hn : s.regs 100 = x.n)
    (hm : s.regs 101 = x.ends.length) (hL : s.arrs 2 = L.map Fin.val)
    (hR : s.arrs 47 = List.ofFn (fun j => (g j).val)) (hv : s.arrs 4 = gm06VertexMask vs)
    (hlists : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s)
    (hlen : (s.arrs 32).length = x.cellCount * x.cellCount)
    (hmask : s.arrs 36 = gm06RootMask x vs)
    (hranks : s.arrs 37 = List.ofFn (fun b : Fin x.cellCount => ((gm06RootMask x vs).take b.val).sum)) :
    ∃ s' t, Exec w gm06GapUpdatePrepareProg s s' t ∧
      t ≤ 8 + L.length * (26 * (x.cellCount * x.cellCount) + 37 * x.cellCount + 58) ∧
      (s'.arrs 48).take (s'.regs 6404) = gm06GapUpdatedWords x vs L g ∧
      s'.regs 6404 = (gm06GapUpdatedWords x vs L g).length ∧
      (s'.arrs 48).length = L.length ∧
      (∀ A : ℕ, A ≠ 33 → A ≠ 34 → A ≠ 48 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, (q < 190 ∨ 197 ≤ q) → q ≠ 187 → q ≠ 6400 → q ≠ 6401 →
        q ≠ 6402 → q ≠ 6403 → q ≠ 6404 → s'.regs q = s.regs q) := by
  let s₁ := s.setArr 48 (List.replicate L.length 0)
  let s₂ := s₁.setReg 6403 0
  let s₃ := s₂.setReg 6404 0
  have hex₁ : Exec w (.alloc 48 (.len 47)) s s₁ (1 + L.length) :=
    .alloc (by simp [Expr.eval, checkWord, hR, hK])
  have hex₂ : Exec w (.assign 6403 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have hex₃ : Exec w (.assign 6404 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have hlists₃ : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s₃ :=
    hlists.of_arrs_eq (by simp [s₃, s₂, s₁]) (by simp [s₃, s₂, s₁]) (by simp [s₃, s₂, s₁])
  obtain ⟨s₄, t, hex, ht, hout, hcount, hcap, harr, hreg⟩ :=
    gm06GapUpdateLoopProg_exec x vs L g hw hN hsquare hK (s := s₃)
      (by simpa [s₃, s₂, s₁] using hsize) (by simpa [s₃, s₂, s₁] using hn)
      (by simpa [s₃, s₂, s₁] using hm) (by simp [s₃, s₂]) (by simp [s₃])
      (by simp [s₃, s₂, s₁]) (by simpa [s₃, s₂, s₁] using hL)
      (by simpa [s₃, s₂, s₁] using hR) (by simpa [s₃, s₂, s₁] using hv)
      hlists₃ (by simpa [s₃, s₂, s₁] using hlen)
      (by simpa [s₃, s₂, s₁] using hmask) (by simpa [s₃, s₂, s₁] using hranks)
  have hcost : L.length * (26 * (x.cellCount * x.cellCount) + 37 * x.cellCount + 58) =
      L.length * (26 * (x.cellCount * x.cellCount) + 37 * x.cellCount + 57) + L.length := by
    rw [show 26 * (x.cellCount * x.cellCount) + 37 * x.cellCount + 58 =
      (26 * (x.cellCount * x.cellCount) + 37 * x.cellCount + 57) + 1 by omega,
      Nat.mul_add, Nat.mul_one]
  refine ⟨s₄, (1 + L.length) + (2 + (2 + t)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex)),
    by rw [hcost]; omega, hout, hcount, ?_, ?_, ?_⟩
  · simpa [s₃, s₂, s₁] using hcap
  · intro A hA hA' hA''
    exact (harr A hA hA' hA'').trans (by simp [s₃, s₂, s₁, hA''])
  · intro q hq hq' hq₀ hq₁ hq₂ hq₃ hq₄
    exact (hreg q hq hq' hq₀ hq₁ hq₂ hq₃ hq₄).trans
      (by simp [s₃, s₂, s₁, hq₃, hq₄])

end GraphMinor.Compute
