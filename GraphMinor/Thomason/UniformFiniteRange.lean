module
public import GraphMinor.Thomason.UniformRows
import Mathlib.Tactic.IntervalCases
import GraphMinor.Thomason.UniformFinite51
import GraphMinor.Thomason.UniformFinite52
import GraphMinor.Thomason.UniformFinite53
import GraphMinor.Thomason.UniformFinite54
import GraphMinor.Thomason.UniformFinite55
import GraphMinor.Thomason.UniformFinite56
import GraphMinor.Thomason.UniformFinite57
import GraphMinor.Thomason.UniformFinite58
import GraphMinor.Thomason.UniformFinite59
import GraphMinor.Thomason.UniformFinite60
import GraphMinor.Thomason.UniformFinite61
import GraphMinor.Thomason.UniformFinite62
import GraphMinor.Thomason.UniformFinite63
import GraphMinor.Thomason.UniformFinite64
import GraphMinor.Thomason.UniformFinite65
import GraphMinor.Thomason.UniformFinite66
import GraphMinor.Thomason.UniformFinite67
import GraphMinor.Thomason.UniformFinite68
import GraphMinor.Thomason.UniformFinite69
import GraphMinor.Thomason.UniformFinite70
import GraphMinor.Thomason.UniformFinite71
import GraphMinor.Thomason.UniformFinite72
import GraphMinor.Thomason.UniformFinite73
import GraphMinor.Thomason.UniformFinite74
import GraphMinor.Thomason.UniformFinite75
import GraphMinor.Thomason.UniformFinite76
import GraphMinor.Thomason.UniformFinite77
import GraphMinor.Thomason.UniformFinite78
import GraphMinor.Thomason.UniformFinite79
import GraphMinor.Thomason.UniformFinite80
import GraphMinor.Thomason.UniformFinite81
import GraphMinor.Thomason.UniformFinite82
import GraphMinor.Thomason.UniformFinite83
import GraphMinor.Thomason.UniformFinite84
import GraphMinor.Thomason.UniformFinite85
import GraphMinor.Thomason.UniformFinite86
import GraphMinor.Thomason.UniformFinite87
import GraphMinor.Thomason.UniformFinite88
import GraphMinor.Thomason.UniformFinite89
import GraphMinor.Thomason.UniformFinite90
import GraphMinor.Thomason.UniformFinite91
import GraphMinor.Thomason.UniformFinite92
import GraphMinor.Thomason.UniformFinite93
import GraphMinor.Thomason.UniformFinite94
import GraphMinor.Thomason.UniformFinite95
import GraphMinor.Thomason.UniformFinite96
import GraphMinor.Thomason.UniformFinite97
import GraphMinor.Thomason.UniformFinite98
import GraphMinor.Thomason.UniformFinite99
import GraphMinor.Thomason.UniformFinite100
import GraphMinor.Thomason.UniformFinite101
import GraphMinor.Thomason.UniformFinite102
import GraphMinor.Thomason.UniformFinite103
import GraphMinor.Thomason.UniformFinite104
import GraphMinor.Thomason.UniformFinite105
import GraphMinor.Thomason.UniformFinite106
import GraphMinor.Thomason.UniformFinite107
import GraphMinor.Thomason.UniformFinite108
import GraphMinor.Thomason.UniformFinite109

/-!
# The finite range `51 ≤ p ≤ 109`

Section 4 of the note `docs/thomason/uniform_minor_bound.tex`: every `p` in this
range has a certificate row accepted by `rowOK`. The rows are in the files
`UniformFinite51.lean` to `UniformFinite109.lean`, generated from
`global_finite_certificate.jsonl` by `gen_lean_finite.py`, and each is
checked by the kernel.
-/

public section
namespace GraphMinor.Thomason.Uniform

/-- Every `51 ≤ p ≤ 109` has an accepted certificate row. -/
theorem exists_rowOK_of_finite (p : ℕ) (hp : 51 ≤ p) (hp' : p ≤ 109) :
    ∃ c a b es, rowOK p c a b es = true := by
  interval_cases p
  · exact ⟨_, _, _, _, finiteRow51_ok⟩
  · exact ⟨_, _, _, _, finiteRow52_ok⟩
  · exact ⟨_, _, _, _, finiteRow53_ok⟩
  · exact ⟨_, _, _, _, finiteRow54_ok⟩
  · exact ⟨_, _, _, _, finiteRow55_ok⟩
  · exact ⟨_, _, _, _, finiteRow56_ok⟩
  · exact ⟨_, _, _, _, finiteRow57_ok⟩
  · exact ⟨_, _, _, _, finiteRow58_ok⟩
  · exact ⟨_, _, _, _, finiteRow59_ok⟩
  · exact ⟨_, _, _, _, finiteRow60_ok⟩
  · exact ⟨_, _, _, _, finiteRow61_ok⟩
  · exact ⟨_, _, _, _, finiteRow62_ok⟩
  · exact ⟨_, _, _, _, finiteRow63_ok⟩
  · exact ⟨_, _, _, _, finiteRow64_ok⟩
  · exact ⟨_, _, _, _, finiteRow65_ok⟩
  · exact ⟨_, _, _, _, finiteRow66_ok⟩
  · exact ⟨_, _, _, _, finiteRow67_ok⟩
  · exact ⟨_, _, _, _, finiteRow68_ok⟩
  · exact ⟨_, _, _, _, finiteRow69_ok⟩
  · exact ⟨_, _, _, _, finiteRow70_ok⟩
  · exact ⟨_, _, _, _, finiteRow71_ok⟩
  · exact ⟨_, _, _, _, finiteRow72_ok⟩
  · exact ⟨_, _, _, _, finiteRow73_ok⟩
  · exact ⟨_, _, _, _, finiteRow74_ok⟩
  · exact ⟨_, _, _, _, finiteRow75_ok⟩
  · exact ⟨_, _, _, _, finiteRow76_ok⟩
  · exact ⟨_, _, _, _, finiteRow77_ok⟩
  · exact ⟨_, _, _, _, finiteRow78_ok⟩
  · exact ⟨_, _, _, _, finiteRow79_ok⟩
  · exact ⟨_, _, _, _, finiteRow80_ok⟩
  · exact ⟨_, _, _, _, finiteRow81_ok⟩
  · exact ⟨_, _, _, _, finiteRow82_ok⟩
  · exact ⟨_, _, _, _, finiteRow83_ok⟩
  · exact ⟨_, _, _, _, finiteRow84_ok⟩
  · exact ⟨_, _, _, _, finiteRow85_ok⟩
  · exact ⟨_, _, _, _, finiteRow86_ok⟩
  · exact ⟨_, _, _, _, finiteRow87_ok⟩
  · exact ⟨_, _, _, _, finiteRow88_ok⟩
  · exact ⟨_, _, _, _, finiteRow89_ok⟩
  · exact ⟨_, _, _, _, finiteRow90_ok⟩
  · exact ⟨_, _, _, _, finiteRow91_ok⟩
  · exact ⟨_, _, _, _, finiteRow92_ok⟩
  · exact ⟨_, _, _, _, finiteRow93_ok⟩
  · exact ⟨_, _, _, _, finiteRow94_ok⟩
  · exact ⟨_, _, _, _, finiteRow95_ok⟩
  · exact ⟨_, _, _, _, finiteRow96_ok⟩
  · exact ⟨_, _, _, _, finiteRow97_ok⟩
  · exact ⟨_, _, _, _, finiteRow98_ok⟩
  · exact ⟨_, _, _, _, finiteRow99_ok⟩
  · exact ⟨_, _, _, _, finiteRow100_ok⟩
  · exact ⟨_, _, _, _, finiteRow101_ok⟩
  · exact ⟨_, _, _, _, finiteRow102_ok⟩
  · exact ⟨_, _, _, _, finiteRow103_ok⟩
  · exact ⟨_, _, _, _, finiteRow104_ok⟩
  · exact ⟨_, _, _, _, finiteRow105_ok⟩
  · exact ⟨_, _, _, _, finiteRow106_ok⟩
  · exact ⟨_, _, _, _, finiteRow107_ok⟩
  · exact ⟨_, _, _, _, finiteRow108_ok⟩
  · exact ⟨_, _, _, _, finiteRow109_ok⟩

end GraphMinor.Thomason.Uniform
