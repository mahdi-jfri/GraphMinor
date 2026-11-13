module

public import GraphMinor.Compute.Algorithm41Read

/-!
# The Word RAM Theorem for GM XIII (4.1)

The verified core reads the input, computes the finite folio tables, and writes
all models. These theorems apply it to the public input forms and use only the
pure output readers to describe the result.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Graph Minors XIII, (4.1), pages 75–76:
"(4.1) **Algorithm.**

*Input:* A digraph $G$, and a subset $Z \subseteq V(G)$ with $|Z| \le \xi$, and a branch-decomposition $(T, \tau)$ of $G$ of width $\le \omega$.

*Output:* The $\delta$-folio of $G$ relative to $Z$, and a modelling of it.

*Running time:* $O(\varepsilon)$."
The output reader reads the written codes, edge indices, and branch bit lists. -/
theorem gm13_algorithm_4_1 (δ ξ ω : ℕ) :
    ComputesArrRelInTime (alg41Size (ξ := ξ) (ω := ω)) encAlg41In
      (fun x out => IsValidAlg41ReadOutput δ x (decAlg41Out δ x out))
      (alg41Prog δ ξ ω) (fun n => n) := by
  refine ⟨C_core41 δ ξ ω, B_word41 δ ξ ω + 1, ?_, by omega, ?_⟩
  · unfold C_core41
    omega
  · intro x s hinput
    have hcore : s.arrs inArr = encAlg41CoreIn x.toCore := by rw [x.enc_toCore]; exact hinput
    rcases alg41CoreProg_exec x.toCore hcore with ⟨s', time, hex, htime, hout⟩
    let T := computeFolioDP x.toCore.G x.toCore.Z δ x.toCore.ht x.toCore.p x.toCore.hp x.toCore.τ
    refine ⟨s', time, ?_, ?_, T, ?_⟩
    · simpa only [Alg41Input.size_toCore, alg41Prog] using hex
    · simpa only [Alg41Input.size_toCore] using htime
    · unfold decAlg41Out
      rw [hout]
      exact T.readOutput_encode

/-- Execute the code-input program with the fixed global time and word-size constants. -/
theorem alg41CodeProg_exec {δ ξ ω : ℕ} (x : Alg41CodeInput ξ ω) {s : State}
    (hinput : s.arrs inArr = encAlg41CodeIn x) :
    ∃ s' time,
      Exec (wordSize (B_word41 δ ξ ω + 1) (alg41CodeSize x)) (alg41Prog δ ξ ω) s s' time ∧
      time ≤ C_core41 δ ξ ω * alg41CodeSize x ∧
      IsValidAlg41ReadCodeOutput δ x (decAlg41CodeOut δ x (s'.arrs outArr)) := by
  by_cases hge2 : 2 ≤ x.G.numEdges
  · let q := (x.toAlg41Input hge2).toCore
    have hc : x.toCore = q := by simp only [Alg41CodeInput.toCore, hge2, ↓reduceDIte]; rfl
    have hsize : alg41CoreSize q = alg41CodeSize x := by rw [← hc]; exact x.size_toCore
    have hcore : s.arrs inArr = encAlg41CoreIn q := by rw [← hc, x.enc_toCore]; exact hinput
    rcases alg41CoreProg_exec q hcore with ⟨s', time, hex, htime, hout⟩
    let T := computeFolioDP q.G q.Z δ q.ht q.p q.hp q.τ
    refine ⟨s', time, ?_, ?_, T, ?_⟩
    · simpa only [hsize, alg41Prog] using hex
    · simpa only [hsize] using htime
    · unfold decAlg41CodeOut
      rw [hout]
      exact T.readOutput_encode
  · let q : Alg41CoreInput ξ ω := small41CoreInput x.G.toComputeDigraph x.Z x.hZ
      (by have hm : x.G.toComputeDigraph.numEdges = x.G.numEdges := x.G.length_directedEdgesList; omega)
    have hc : x.toCore = q := by simp only [Alg41CodeInput.toCore, hge2, ↓reduceDIte]; rfl
    have hsize : alg41CoreSize q = alg41CodeSize x := by rw [← hc]; exact x.size_toCore
    have hcore : s.arrs inArr = encAlg41CoreIn q := by rw [← hc, x.enc_toCore]; exact hinput
    rcases alg41CoreProg_exec q hcore with ⟨s', time, hex, htime, hout⟩
    let T := computeFolioDP q.G q.Z δ q.ht q.p q.hp q.τ
    refine ⟨s', time, ?_, ?_, T, ?_⟩
    · simpa only [hsize, alg41Prog] using hex
    · simpa only [hsize] using htime
    · unfold decAlg41CodeOut
      rw [hout]
      exact T.readOutput_encode


/-- GM XIII (4.1), pages 75–76, for serialized branch-decomposition input.
The zero-edge and one-edge conventions use a single-node core and the same program. -/
theorem algorithm_4_1_code (δ ξ ω : ℕ) :
    ComputesArrRelInTime (alg41CodeSize (ξ := ξ) (ω := ω)) encAlg41CodeIn
      (fun x out => IsValidAlg41ReadCodeOutput δ x (decAlg41CodeOut δ x out))
      (alg41Prog δ ξ ω) (fun n => n) := by
  refine ⟨C_core41 δ ξ ω, B_word41 δ ξ ω + 1, ?_, by omega, ?_⟩
  · unfold C_core41
    omega
  · intro x s hinput
    exact alg41CodeProg_exec x hinput

/-- GM XIII (4.1) on a branch-decomposition written as a code. -/
abbrev algorithm_4_1_gm13 := @algorithm_4_1_code

end GraphMinor.Compute
