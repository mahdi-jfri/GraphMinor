module

public import GraphMinor.Compute.Join13Semantics72
public import GraphMinor.Compute.Join13Isolate72
import GraphMinor.Compute.Join13InputBounds72
import GraphMinor.Compute.Join13WordSize72

/-!
# The (4.1) adapter used by (7.2)

The empty-root call packs the input, runs the core in separate memory, and
converts its certified models to the caller's format. A second memory offset
protects the caller's low registers and arrays. All copies and conversions are
linear in the graph size.
-/

public section
namespace GraphMinor.Compute

private theorem budget72 (N R E M δ D W : ℕ) (hD : D = R + E + M + 2 * δ + 10)
    (_hN : 0 < N) (h : D * (N + 1) < W) :
    5 * N < W ∧ R * N + E + M + 2 * δ + 4 < W := by
  have h5 : 5 * N ≤ D * N := Nat.mul_le_mul_right N (by omega)
  have hR : R * N ≤ D * N := Nat.mul_le_mul_right N (by omega)
  rw [Nat.mul_add, Nat.mul_one] at h
  omega

private theorem totalCopies72 (N C K L t : ℕ) (hN : 0 < N)
    (hL : L ≤ K * N) (ht : t ≤ C * N + 16 * L + 44) :
    t ≤ (C + 16 * K + 44) * N := by
  have h44 : 44 ≤ 44 * N := Nat.le_mul_of_pos_right 44 hN
  have hm := Nat.mul_le_mul_left 16 hL
  have heq : (C + 16 * K + 44) * N = C * N + 16 * (K * N) + 44 * N := by ring
  rw [heq]
  omega

/-- Claim (4.1) supplies the empty-root multigraph interface used in (7.2). -/
theorem alg41MultiSpec72_of_claim41 (h41 : Claim41) (δ B : ℕ) :
    ∃ P, Alg41MultiSpec 0 δ B 12 14 13 15 16 20 10 P := by
  obtain ⟨P, C, c, hC, hc, hP⟩ := h41 δ 0 B
  let M := maxEncFolioSetRepLen 0 δ
  let R := M * (2 * δ + 1)
  let E := modelExtra72 0 δ
  let D := R + E + M + 2 * δ + 10
  let ci := c + D
  let Ci := C + 850 + 300 * (R + E + M + 1)
  let Ct := Ci + 16 * (6 + M + R + E) + 44
  refine ⟨isolateAdapter72Prog (internalAdapter72Prog P δ), Ct, ci, by dsimp [Ct, Ci]; omega,
    by dsimp [ci]; omega, ?_⟩
  intro n G Z bdCode w hZ hbd hw _ _ s hG _ hBD
  have hZnil : Z = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst Z
  let N := n + G.numEdges + 1
  let x := multiCoreInput72 G bdCode hbd
  let T := computeFolioDP x.G x.Z δ x.ht x.p x.hp x.τ
  have hN : 0 < N := by dsimp [N]; omega
  have hw' : wordSize ci N ≤ w := by simpa only [N, Nat.add_comm] using hw
  have hlin : D * (N + 1) < 2 ^ w :=
    linear_lt_wordSize72 (by dsimp [ci]; omega) (by dsimp [ci]; omega) hw'
  obtain ⟨hsmall, hbig⟩ := budget72 N R E M δ D (2 ^ w) rfl hN hlin
  have hsmall' : 5 * (G.numEdges + n + 1) < 2 ^ w := by simpa only [N, Nat.add_comm] using hsmall
  have hw3 : 3 < 2 ^ w := by omega
  obtain ⟨hlenG, hlenBD⟩ := inputLengths72_le G bdCode hbd
  have henc : G.enc.length < 2 ^ w := by dsimp [N] at hsmall; omega
  have hcode : bdCode.length < 2 ^ w := by dsimp [N] at hsmall; omega
  have hcore : wordSize c (G.numEdges + n + 1) ≤ w :=
    (wordSize_mono_left (by dsimp [ci]; omega) _).trans hw
  have hraw₀ := length_coreOutput72_le T
  change (encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList).length ≤
    M * (0 + 2 * δ + 1) * N at hraw₀
  have hraw : (encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList).length ≤ R * N := by
    simpa only [Nat.zero_add] using hraw₀
  have hF := length_encFolioSetRep_le_max (le_refl 0) T.toFolioSetRep
  change (encFolioSetRep T.toFolioSetRep).length ≤ M at hF
  have hM := length_models72_le T
  change (encFolioModels T.toFolioSetRep T.toFolioModels72).length ≤
    (encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList).length + E at hM
  have hLF : (encFolioSetRep T.toFolioSetRep).length < 2 ^ w := by omega
  have hLM : (encFolioModels T.toFolioSetRep T.toFolioModels72).length < 2 ^ w := by omega
  have hn : n < 2 ^ w := by dsimp [N] at hsmall; omega
  have hm : G.numEdges < 2 ^ w := by dsimp [N] at hsmall; omega
  have hwordF : ∀ a ∈ encFolioSetRep T.toFolioSetRep, a < 2 ^ w := by
    intro a ha
    have hh := words_encFolioSetRep_le_max (le_refl 0) T.toFolioSetRep a ha
    change a ≤ M + 0 + 2 * δ + 3 at hh
    omega
  have hwordM := words_models72_lt T hLM (by change 0 + δ < _; omega) hn (by omega)
  obtain ⟨s', t, hex, ht, hoF, hoM, hregs, harrs⟩ :=
    isolateAdapter72Prog_exec (internalAdapter72Prog P δ) (Ci * N)
      G.enc bdCode (encFolioSetRep T.toFolioSetRep) (encFolioModels T.toFolioSetRep T.toFolioModels72)
      (fun st hstG hstBD => internalAdapter72Prog_exec G bdCode hbd P C c hP st
        hw3 hcore hsmall' henc hcode hbig hstG hstBD)
      s (by omega) henc hcode hLF hLM (graphWords72_lt G hn hm)
      (fun a ha => (bdWords72_le G bdCode hbd a ha).trans_lt (by dsimp [N] at hsmall; omega))
      hwordF hwordM hG hBD
  obtain ⟨models, hmodels, hfolio⟩ := coreModels72_for_caller (δ := δ) G bdCode hbd
  refine ⟨s', t, T.toFolioSetRep, models, hex, ?_, hfolio, hoF, ?_, hregs, harrs⟩
  · rw [Nat.add_comm G.numEdges n]
    apply totalCopies72 N Ci (6 + M + R + E) _ t hN ?_ ht
    have hMN : M ≤ M * N := Nat.le_mul_of_pos_right M hN
    have hEN : E ≤ E * N := Nat.le_mul_of_pos_right E hN
    change G.enc.length ≤ 3 * (G.numEdges + n + 1) at hlenG
    rw [Nat.add_comm G.numEdges n] at hlenG hlenBD
    change G.enc.length ≤ 3 * N at hlenG
    change bdCode.length ≤ 3 * N at hlenBD
    have heq : (6 + M + R + E) * N = 6 * N + M * N + R * N + E * N := by ring
    rw [heq]
    omega
  · exact hoM.trans hmodels.symm

/-- Claim (4.1) supplies the exact (4.1) specification requested by (7.2). -/
theorem alg41Spec72_of_claim41 (h41 : Claim41) (δ B : ℕ) :
    ∃ P, Alg41Spec 0 δ B 12 14 13 15 16 20 10 P := by
  obtain ⟨P, hP⟩ := alg41MultiSpec72_of_claim41 h41 δ B
  exact ⟨P, (alg41MultiSpec_iff_alg41Spec 0 δ B 12 14 13 15 16 20 10 P).mp hP⟩

end GraphMinor.Compute
