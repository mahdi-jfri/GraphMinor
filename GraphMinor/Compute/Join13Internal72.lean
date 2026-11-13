module

public import GraphMinor.Compute.Join13Call72
public import GraphMinor.Compute.Join13Finish72
public import GraphMinor.Compute.Join13RawBounds72

/-!
# The internal empty-root adapter

This command packs the caller's codes, runs the core in separate memory, and
writes both converted outputs. Its execution lemma keeps the word bounds
explicit so that a single larger word-size constant can cover the whole call.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The complete internal program, before the caller memory range is isolated. -/
def internalAdapter72Prog (P : Cmd) (δ : ℕ) : Cmd :=
  .seq prepareCore72Prog (.seq (callCore72Prog P) (finishCore72Prog 0 δ))

private theorem totalTime72 (N C K t₁ t₂ t₃ : ℕ)
    (h₁ : t₁ ≤ 750 * N) (h₂ : t₂ ≤ (C + 100) * N)
    (h₃ : t₃ ≤ 300 * (K * N)) :
    t₁ + (t₂ + t₃) ≤ (C + 850 + 300 * K) * N := by
  have heq : (C + 850 + 300 * K) * N = 750 * N + (C + 100) * N + 300 * (K * N) := by ring
  rw [heq]
  omega

/-- Linear-time execution of the internal adapter under explicit word bounds. -/
theorem internalAdapter72Prog_exec {w n B δ : ℕ} (G : MultiDigraph n)
    (bdCode : List ℕ) (hbd : IsValidBranchDecompCode B G bdCode)
    (P : Cmd) (C c : ℕ)
    (hP : ∀ (x : Alg41CoreInput 0 B) (s : State),
      s.arrs inArr = encAlg41CoreIn x →
      ∃ s' t, Exec (wordSize c (alg41CoreSize x)) P s s' t ∧
        t ≤ C * alg41CoreSize x ∧
        s'.arrs outArr =
          let T := computeFolioDP x.G x.Z δ x.ht x.p x.hp x.τ
          encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList)
    (s : State) (hw : 3 < 2 ^ w)
    (hcore : wordSize c (G.numEdges + n + 1) ≤ w)
    (hsmall : 5 * (G.numEdges + n + 1) < 2 ^ w)
    (henc : G.enc.length < 2 ^ w) (hcode : bdCode.length < 2 ^ w)
    (hbig : maxEncFolioSetRepLen 0 δ * (2 * δ + 1) * (n + G.numEdges + 1) +
      modelExtra72 0 δ + maxEncFolioSetRepLen 0 δ + 2 * δ + 4 < 2 ^ w)
    (hG : s.arrs 12 = G.enc) (hBD : s.arrs 13 = bdCode) :
    let x := multiCoreInput72 G bdCode hbd
    let T := computeFolioDP x.G x.Z δ x.ht x.p x.hp x.τ
    ∃ s' t, Exec w (internalAdapter72Prog P δ) s s' t ∧
      t ≤ (C + 850 + 300 * (maxEncFolioSetRepLen 0 δ * (2 * δ + 1) +
        modelExtra72 0 δ + maxEncFolioSetRepLen 0 δ + 1)) * (n + G.numEdges + 1) ∧
      s'.arrs 15 = encFolioSetRep T.toFolioSetRep ∧
      s'.arrs 16 = encFolioModels T.toFolioSetRep T.toFolioModels72 := by
  let x := multiCoreInput72 G bdCode hbd
  let T := computeFolioDP x.G x.Z δ x.ht x.p x.hp x.τ
  obtain ⟨s₁, t₁, he₁, ht₁, hin₁, hend₁, hn₁, hm₁⟩ :=
    prepareCore72Prog_exec G bdCode hbd s hw hsmall henc hcode hG hBD
  obtain ⟨s₂, t₂, he₂, ht₂, hout₂, ha₂, hr₂⟩ :=
    callCore72Prog_exec x P C c hP s₁ hcore hsmall hin₁
  have hlen := length_coreOutput72_le T
  change (encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList).length ≤
    maxEncFolioSetRepLen 0 δ * (0 + 2 * δ + 1) * (n + G.numEdges + 1) at hlen
  have hraw : (s₂.arrs 201).length ≤
      maxEncFolioSetRepLen 0 δ * (2 * δ + 1) * (n + G.numEdges + 1) := by
    rw [hout₂]
    simpa only [Nat.zero_add] using hlen
  obtain ⟨s₃, t₃, he₃, ht₃, hfolio₃, hmodels₃⟩ :=
    finishCore72Prog_exec (w := w) T s₂ (by omega) (by change n + G.numEdges < _; omega)
      (by change 2 * G.numEdges < _; omega) (by change 0 + δ < _; omega)
      (by change (s₂.arrs 201).length + modelExtra72 0 δ < _; omega)
      (fun a ha => (words_encFolioSetRep_le_max (le_refl 0) T.toFolioSetRep a ha).trans_lt (by omega))
      hout₂ ((ha₂ 40 (by decide)).trans hend₁)
      ((hr₂ 26 (by decide)).trans hn₁) ((hr₂ 28 (by decide)).trans hm₁)
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq he₁ (.seq he₂ he₃), ?_, hfolio₃, hmodels₃⟩
  have hN : 1 ≤ n + G.numEdges + 1 := by omega
  have hconst := Nat.mul_le_mul_left
    (modelExtra72 0 δ + maxEncFolioSetRepLen 0 δ + 1) hN
  have hsum : (s₂.arrs 201).length + modelExtra72 0 δ + maxEncFolioSetRepLen 0 δ + 1 ≤
      (maxEncFolioSetRepLen 0 δ * (2 * δ + 1) + modelExtra72 0 δ +
        maxEncFolioSetRepLen 0 δ + 1) * (n + G.numEdges + 1) := by
    simp only [Nat.add_mul] at hconst ⊢
    omega
  change t₃ ≤ 300 * ((s₂.arrs 201).length + modelExtra72 0 δ +
    maxEncFolioSetRepLen 0 δ + 1) at ht₃
  have ht₃' := ht₃.trans (Nat.mul_le_mul_left 300 hsum)
  change t₂ ≤ (C + 100) * (G.numEdges + n + 1) at ht₂
  rw [Nat.add_comm G.numEdges n] at ht₂
  exact totalTime72 _ _ _ _ _ _ ht₁ ht₂ ht₃'

end GraphMinor.Compute
