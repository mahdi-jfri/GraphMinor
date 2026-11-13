module

public import GraphMinor.Compute.Case3StepsFirstIndex

/-!
# A first-match scan through a prefix

The scan starts with a missing sentinel and records the first successful
index. Its invariant says that a missing value means no earlier success,
and a recorded value is the least successful index. At the end this is the
first-index specification used for loop owners.
-/

@[expose] public section

namespace GraphMinor.Compute

open Classical

/-- The first success encountered before the scan reaches `k`, or the sentinel. -/
noncomputable def case3FirstSeen {n : ℕ} (P : Fin n → Prop) : ℕ → ℕ
  | 0 => n
  | k + 1 => if h : k < n then
      if case3FirstSeen P k = n ∧ P ⟨k, h⟩ then k else case3FirstSeen P k
    else case3FirstSeen P k

/-- The recorded value is missing precisely until a successful index is visited;
a successful value has no earlier successful competitor. -/
theorem case3FirstSeen_invariant {n : ℕ} (P : Fin n → Prop) (k : ℕ) (hk : k ≤ n) :
    case3FirstSeen P k ≤ n ∧
      (case3FirstSeen P k = n → ∀ v : Fin n, v.1 < k → ¬ P v) ∧
      (∀ h : case3FirstSeen P k < n,
        (P ⟨case3FirstSeen P k, h⟩ ∧
          ∀ v : Fin n, v.1 < case3FirstSeen P k → ¬ P v) ∧
        case3FirstSeen P k < k) := by
  induction k with
  | zero =>
    refine ⟨le_rfl, ?_, ?_⟩
    · intro _ v hv
      omega
    · intro h
      change n < n at h
      omega
  | succ k ih =>
    have hkn : k < n := by omega
    have hs := ih (by omega)
    simpa only [case3FirstSeen, hkn, ↓reduceDIte] using
      case3FirstIndex_scan_step P k (case3FirstSeen P k) hkn hs.1 hs.2.1 hs.2.2

/-- After the last index the scan agrees with the least-match specification. -/
theorem case3FirstSeen_done {n : ℕ} (P : Fin n → Prop) :
    case3FirstSeen P n = case3FirstIndex P := by
  have hs := case3FirstSeen_invariant P n le_rfl
  apply case3FirstIndex_unique P _ hs.1
  · intro h v
    exact hs.2.1 h v v.2
  · intro h
    exact (hs.2.2 h).1

end GraphMinor.Compute
