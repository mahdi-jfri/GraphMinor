module

public import GraphMinor.Compute.DisjointPathsFinal
public import GraphMinor.Compute.Algorithm81
public import GraphMinor.Compute.Algorithm86
public import GraphMinor.Compute.Algorithm94
public import GraphMinor.Compute.Algorithm97
public import GraphMinor.Compute.Algorithm99Complete
public import GraphMinor.Compute.Algorithm105
public import GraphMinor.Compute.Join104
import GraphMinor.Compute.CrossingTop
import GraphMinor.Compute.SpecsCrossingReductionProved
import GraphMinor.Compute.Algorithm72
import GraphMinor.Compute.Algorithm92Final
import GraphMinor.Compute.CrossingClassProg
import GraphMinor.Compute.CrossingLiftProg
import GraphMinor.Compute.Case3StepsClaim

/-!
# Closed program chains in Graph Minors XIII

The proved crossing extractor supplies the external two-paths subroutine.
The programs of (7.7), (9.2), and (7.2) then close (9.4), (9.7), and (9.9).
Their caller specifications and the proved (10.4) program close (10.5).
Each conclusion includes a Word RAM program, its output condition, and its time bound.
-/

public section
namespace GraphMinor.Compute

open GraphMinor.Compute.Crossing

/-- The external two-paths algorithm used in XIII, (8.1), page 93, obtained
from the proved planarity test and crossing extractor. -/
theorem gm13_twoPaths : Shiloach80Statement :=
  shiloach80Statement_of_crossingExtractor

/-- Graph Minors XIII, Algorithm (8.1), page 93:
"(8.1) Algorithm.
*Input:* A society $(G, \Omega)$.
*Output:* A cross in $(G, \Omega)$ if one exists.
*Running time:* $O(v\varepsilon)$."
The program and its `O(vε)` bound use the proved external two-paths subroutine. -/
theorem algorithm_8_1_proved :
    ∃ shiloachProg : Cmd,
      ComputesArrRelInTime alg81Size encAlg81In
        (fun x out => IsValidAlg81Output x (decAlg81Out x out))
        (alg81Prog shiloachProg) (fun s => s) :=
  gm13_algorithm_8_1 gm13_twoPaths

/-- Graph Minors XIII, Algorithm (8.6), page 96:
"(8.6) Algorithm.
*Input:* A society $(G, \Omega)$.
*Output:* Either a cross in $(G, \Omega)$, or a rural division of $(G, \Omega)$.
*Running time:* $O(\nu\varepsilon)$."
The program runs in `O(vε)` time. -/
theorem algorithm_8_6_proved :
    ∃ shiloachProg : Cmd,
      ComputesArrRelInTime alg81Size encAlg81In
        (fun x out => IsValidAlg86Output x (decAlg86Out x out))
        (alg86Prog shiloachProg) (fun s => s) :=
  gm13_algorithm_8_6 gm13_twoPaths

/-- Graph Minors XIII, (9.3) and Algorithm (9.4), page 102: the linear-time
program, using the proved programs of (7.7) and (9.2). -/
theorem algorithm_9_4_proved : Algorithm94Statement :=
  gm13_algorithm_9_4 gm13_algorithm_7_7 Alg92.gm13_algorithm_9_2

/-- Graph Minors XIII, (9.6) and Algorithm (9.7), page 103: the `O(vε)`
program, using the proved two-paths and (9.4) programs. -/
theorem algorithm_9_7_proved : Algorithm97Statement :=
  gm13_algorithm_9_7 gm13_twoPaths algorithm_9_4_proved

/-- Graph Minors XIII, (9.8) and Algorithm (9.9), pages 103–106: both the
standalone `O(vε)` program and its caller specification, using the proved
(7.2), (9.7), and Steps (5)–(7) programs. -/
theorem gm13_algorithm_9_9 : Algorithm99Statement case3Decoder :=
  algorithm_9_9_of_case3Steps gm13_twoPaths algorithm_7_2_statement
    algorithm_9_7_proved case3StepsClaim_proved

/-- Graph Minors XIII, (10.3), pages 107–108:
"For all $q$, $\delta \ge 0$ there exists $h \ge 0$, even, such that for all
$\omega \ge 0$ there is an algorithm as in (10.4) with running time $O(\varepsilon^2)$."
The array-layout parameter `p` is arbitrary. The chosen height is independent
of both `p` and the supplied branch-width bound. -/
theorem gm13_algorithm_10_3 (q δ : ℕ) :
    ∃ h : ℕ, 2 ≤ h ∧ Even h ∧ ∀ p ω : ℕ,
      Alg104Spec case3Decoder p q δ h ω := by
  exact ⟨GM13.sec10MaxWallHeight GM13.theorem_10_2_proof.{0, 0} q δ,
    (GM13.two_le_and_even_sec10MaxWallHeight q δ).1,
    (GM13.two_le_and_even_sec10MaxWallHeight q δ).2,
    fun p ω => gm13_algorithm_10_4 p q δ ω⟩

/-- Graph Minors XIII, Algorithm (10.5), pages 108–109: for fixed root and
detail bounds, a program computes the folio in `O(v³)` time. The chosen
width and wall height come from the proved (9.9) and (10.3) programs. -/
theorem algorithm_10_5_proved (ξ δ : ℕ) :
    ∃ (ω : ℕ) (P : Cmd),
      ComputesArrRelInTime (folioSize (ξ := ξ)) encFolioIn
        (IsValidAlg105Output δ (max ω 2 + ξ)) P (fun v => (v + 1) ^ 3) := by
  obtain ⟨ω, _, h99⟩ := gm13_algorithm_9_9 (alg62Param ξ δ) (sec105WallHeight ξ δ)
    (two_le_and_even_sec105WallHeight ξ δ).1
    (two_le_and_even_sec105WallHeight ξ δ).2
  obtain ⟨P, hP⟩ := gm13_algorithm_10_5 ξ δ (sec105WallHeight ξ δ) ω case3Decoder
    h99 alg104Spec_proved
  exact ⟨ω, P, hP⟩

end GraphMinor.Compute
