module

public import GraphMinor.Compute.Algorithm99Main
public import GraphMinor.Compute.Algorithm86

/-!
# Algorithm (9.9) from (7.2), (9.7) and `Case3StepsClaim`

This file collects the programs that Algorithm (9.9) of Graph Minors XIII (page 104) calls and
proves the program on its own.

* `alg99_parts`: from `Algorithm97Statement` (at `s = C(p, 2) + 5`), `Algorithm72Statement` (at
  the height `h'` of (9.7)), `Shiloach80Statement` (through (8.6)) and `Case3StepsClaim`, the
  programs of (7.2), (9.7) and of steps (5) to (7), for every choice of the bases `B ≥ 40`,
  `Q ≥ 15`.
* `algorithm_9_9_standalone_of_case3Steps`: the first half of `Algorithm99Statement`, the
  program on its own, in time `O(vε)`.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- The programs that (9.9) calls, for `p` and `h`: (7.2) at the height `h'` of (9.7), (9.7)
at `s = C(p, 2) + 5`, and the program of steps (5) to (7) for the array and register layout of
`alg99Step58Prog`. -/
theorem alg99_parts (hShiloach : Shiloach80Statement) (h72 : Algorithm72Statement)
    (h97 : Algorithm97Statement) (hC3 : Case3StepsClaim) (pp h : ℕ) (h2 : 2 ≤ h)
    (he : Even h) :
    ∃ (h' ω : ℕ) (h2' : 2 ≤ h') (he' : Even h') (P72 P97 : Cmd) (C72 c72 C97 c97 : ℕ),
      RunsAsSubroutine algorithm72Size encAlgorithm72In (IsAlgorithm72Output ω h') P72
        (fun s => s) C72 c72 ∧
      RunsAsSubroutine (alg97Size (h' := h')) (encAlg97In (h' := h'))
        (IsAlg97Output pp (pp.choose 2 + 5) h h') P97 (fun m => m) C97 c97 ∧
      ∃ C C_blk c : ℕ, ∀ B Q : ℕ, 40 ≤ B → ∃ P : Cmd,
        Case3StepsRuns h h' ω h2 he h2' he' C C_blk c 23 16 (B + 5) 33 (B - 1) (B - 2) (B - 3)
          (B - 4) (B + 6) (Q + 7) (Q + 10) P := by
  obtain ⟨h', hh', he', P97, hP97⟩ := h97 pp (pp.choose 2 + 5) h h2 he
  have h2' : 2 ≤ h' := le_trans (Nat.le_add_left 2 _) hh'
  obtain ⟨ω, P72, hP72⟩ := h72 h' h2' he'
  obtain ⟨shiloachProg, h86⟩ := gm13_algorithm_8_6 hShiloach
  obtain ⟨C72, c72, -, -, hR72⟩ := hP72.runsAsSubroutine
  obtain ⟨C97, c97, -, -, hR97⟩ := hP97.runsAsSubroutine
  obtain ⟨C, C_blk, c, hC⟩ :=
    case3StepsRuns_of_claim hC3 h h' ω h2 he h2' he' shiloachProg h86 P72 hP72
  refine ⟨h', ω, h2', he', P72, P97, C72, c72, C97, c97, hR72, hR97, C, C_blk, c,
    fun B Q hB => hC _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ (by omega)⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    omega
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    omega
  · intro a ha hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    omega

/-- **Graph Minors XIII, (9.8) and Algorithm (9.9)** (page 104), the program on its own: for
every `p` and even `h ≥ 2` there are `ω` and a program that computes an output of (9.9) in time
`O(vε)`, from (7.2), (9.7), Shiloach's algorithm and `Case3StepsClaim`. -/
theorem algorithm_9_9_standalone_of_case3Steps (hShiloach : Shiloach80Statement)
    (h72 : Algorithm72Statement) (h97 : Algorithm97Statement) (hC3 : Case3StepsClaim)
    (pp h : ℕ) (h2 : 2 ≤ h) (he : Even h) :
    ∃ ω : ℕ, ∃ P : Cmd,
      ComputesArrRelInTime alg99Size encAlg99In (IsAlg99Output case3Decoder pp h ω) P
        (fun m => m) := by
  obtain ⟨h', ω, h2', he', P72, P97, C72, c72, C97, c97, hR72, hR97, C, C_blk, c, hC⟩ :=
    alg99_parts hShiloach h72 h97 hC3 pp h h2 he
  set B := max 40 (max (folioCallerArrBase P72) (folioCallerArrBase P97))
  set Q := max 15 (max (folioCallerRegBase P72) (folioCallerRegBase P97))
  obtain ⟨P, hP⟩ := hC B Q (le_max_left _ _)
  obtain ⟨K4, hK4⟩ := alg99Step4Cost_le (pp.choose 2 + 5) h h' B
  exact ⟨ω, _, alg99MainProg_computes hR72 hR97 hP hK4 (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_right _ _) (le_max_right _ _))⟩

end GraphMinor.Compute
