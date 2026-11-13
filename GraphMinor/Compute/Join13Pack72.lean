module

public import GraphMinor.Compute.Join13Prepare72

/-!
# Packing the (7.2) core input

The prepared arrays are concatenated in the core program's order. The endpoint
stream remains available for converting the core's raw certificates afterward.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Prepare and pack the empty-root core input. -/
def prepareCore72Prog : Cmd :=
  .seq prepareArrays72Prog (packAlg41InProg 60)

/-- Packing only changes its output array. -/
theorem packCore72_writtenArrs : (packAlg41InProg 60).writtenArrs = {inArr} := by
  simp [packAlg41InProg, appendSliceProg, forUp, Cmd.writtenArrs]

/-- The size registers survive packing. -/
theorem packCore72_writtenRegs : (packAlg41InProg 60).writtenRegs = {55, 56, 57} := by
  decide

/-- The (7.2) caller's codes produce the exact core input in linear time. -/
theorem prepareCore72Prog_exec {w n B : ℕ} (G : MultiDigraph n)
    (bdCode : List ℕ) (hbd : IsValidBranchDecompCode B G bdCode) (s : State)
    (hw : 3 < 2 ^ w) (hsz : 5 * (G.numEdges + n + 1) < 2 ^ w)
    (henc : G.enc.length < 2 ^ w) (hcode : bdCode.length < 2 ^ w)
    (hG : s.arrs 12 = G.enc) (hBD : s.arrs 13 = bdCode) :
    let x := multiCoreInput72 G bdCode hbd
    ∃ s' t, Exec w prepareCore72Prog s s' t ∧
      t ≤ 750 * (n + G.numEdges + 1) ∧
      s'.arrs inArr = encAlg41CoreIn x ∧
      s'.arrs 40 = endpointWords72 x.G ∧
      s'.regs 26 = n ∧ s'.regs 28 = G.numEdges := by
  let x := multiCoreInput72 G bdCode hbd
  have hn : n < 2 ^ w := by omega
  have hm : 2 * G.numEdges < 2 ^ w := by omega
  have htc : x.t ≤ 2 * G.numEdges + 1 := x.ht_le
  have htw : x.t < 2 ^ w := by omega
  have hroot : bitSetList x.Z = List.replicate n 0 := by
    change bitSetList (∅ : Finset (Fin n)) = _
    simp [bitSetList, List.ofFn_const]
  obtain ⟨s₁, t₁, he₁, ht₁, hn₁, hm₁, htree₁, hend₁, hhead₁, htail₁,
      hpar₁, hτ₁, hroot₁⟩ :=
    prepareArrays72Prog_exec G bdCode hbd s hw hn hm henc hcode hG hBD
  obtain ⟨s₂, t₂, he₂, ht₂, hout₂⟩ := packCoreLists72_exec n G.numEdges x.t 60
    (by decide) htc
    (List.ofFn (fun e => (x.G.head e).1))
    (List.ofFn (fun e => (x.G.tail e).1)) (bitSetList x.Z)
    (List.ofFn (fun z : Fin x.t => x.p z.1)) (List.ofFn (fun e => (x.τ e).1))
    (by simp; rfl) (by simp; rfl) (by simp; rfl) (by simp) (by simp; rfl)
    (by intro y hy; obtain ⟨e, rfl⟩ := List.mem_ofFn.1 hy; exact (x.G.head e).2.trans hn)
    (by intro y hy; obtain ⟨e, rfl⟩ := List.mem_ofFn.1 hy; exact (x.G.tail e).2.trans hn)
    (by rw [hroot]; intro y hy; have := List.mem_replicate.1 hy; omega)
    (by
      intro y hy
      obtain ⟨z, rfl⟩ := List.mem_ofFn.1 hy
      have hp : x.p z.1 < x.t := by
        by_cases hz : z.1 = 0
        · rw [hz, x.hp0]; exact x.ht
        · exact (x.hp z.1 (by omega) z.2).trans z.2
      exact hp.trans htw)
    (by intro y hy; obtain ⟨e, rfl⟩ := List.mem_ofFn.1 hy; exact (x.τ e).2.trans htw)
    hw hsz hn₁ hm₁ htree₁ (hroot₁.trans hroot.symm) hpar₁ hτ₁ htail₁ hhead₁
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, by omega, hout₂, ?_, ?_, ?_⟩
  · exact (he₂.arrs_eq_of_not_mem_writtenArrs (by rw [packCore72_writtenArrs]; decide)).trans hend₁
  · exact (he₂.regs_eq_of_not_mem_writtenRegs (by rw [packCore72_writtenRegs]; decide)).trans hn₁
  · exact (he₂.regs_eq_of_not_mem_writtenRegs (by rw [packCore72_writtenRegs]; decide)).trans hm₁

end GraphMinor.Compute
