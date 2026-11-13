module

public import GraphMinor.GM08.Section16Defs
public import GraphMinor.GM08.Section16PrintedDefs
import GraphMinor.GM08.Section16
import GraphMinor.GM08.Section15Conclusion
import GraphMinor.GM08.Section13
import GraphMinor.GM08.Section14
import GraphMinor.GM08.Section4
import GraphMinor.GM08.Section16FiniteLabels

/-!
# Graph Minors VIII (16.1)

The three classes on the right of (16.2) are well-rooted. Use (15.4)
for the no-inner-tube classes, (13.1) for the direct sums, (13.3) for
root identifications, and (4.2) for their union. Restricting to the
unlinked-framing class proves (16.1).

The decomposition (16.2) needs room for new vertex labels, so this argument
is run for an infinite label type. If the label type is finite, every class of
grafts is well-rooted by Dickson's lemma (`GM08.isWellRootedGraftClass_of_finite`),
so (16.1) holds for every label type.
-/

public section

namespace GraphMinor.GM08

universe u v

/-- Graph Minors VIII, (16.1), pages 282 and 284, for an infinite label type,
by the paper's proof. The infinite label type gives labels to the pieces of
the decomposition (16.2). -/
theorem theorem_16_1_of_infinite {α : Type u} {β : Type v} [Infinite α] (k r s : ℕ)
    (hprev : IsWellRootedGraftClass (classB (α := α) (β := β) ((k : ℤ) - 1))) :
    IsWellRootedGraftClass (printedClassBUnlinked (α := α) (β := β) k r s) := by
  apply isWellRootedGraftClass_mono (theorem_16_2_proof k r s)
  exact theorem_4_2_proof
    (theorem_4_2_proof (theorem_15_4_proof k r s)
      (theorem_13_3_proof (theorem_13_1_proof hprev (theorem_15_4_proof (2 * k) r (s + 2)))))
    (theorem_13_3_proof (theorem_13_1_proof hprev hprev))

/-- **Graph Minors VIII, (16.1)** (page 282): "(16.1) *If $\mathcal{B}(k - 1)$ is
well-rooted then so is $\mathcal{B}(k, r, s)$, for any integers $k, r, s \ge 0$.*"
For an infinite label type this is the paper's proof (`GM08.theorem_16_1_of_infinite`).
For a finite label type every class of grafts is well-rooted
(`GM08.isWellRootedGraftClass_of_finite`). -/
theorem theorem_16_1_proof {α : Type u} {β : Type v} (k r s : ℕ)
    (hprev : IsWellRootedGraftClass (classB (α := α) (β := β) ((k : ℤ) - 1))) :
    IsWellRootedGraftClass (printedClassBUnlinked (α := α) (β := β) k r s) := by
  rcases finite_or_infinite α with hα | hα
  · exact isWellRootedGraftClass_of_finite _
  · exact theorem_16_1_of_infinite k r s hprev

end GraphMinor.GM08
