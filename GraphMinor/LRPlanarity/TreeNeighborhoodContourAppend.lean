module

public import GraphMinor.LRPlanarity.DefsContour
import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
# Concatenating independent component contours

Part IV, Section 5 and Section 7c of the planarity note concatenates the
component words. Each back-edge pair lies wholly in one component. Pairs
in different blocks cannot alternate, since both positions of the first
block precede every position of the second block.
-/

public section
namespace GraphMinor.LRPlanarity

private theorem not_alternating_eq_left (a b c : ℕ) : ¬ AlternatingIndices a a b c := by
  simp only [AlternatingIndices,min_self,max_self]
  omega

private theorem not_alternating_eq_right (a b c : ℕ) : ¬ AlternatingIndices a b c c := by
  simp only [AlternatingIndices,min_self,max_self]
  omega

private theorem not_alternating_separated {a b c d k : ℕ}
    (ha : a < k) (hb : b < k) (hc : k ≤ c) (hd : k ≤ d) : ¬ AlternatingIndices a b c d := by
  simp only [AlternatingIndices]
  omega

private theorem not_alternating_separated_rev {a b c d k : ℕ}
    (ha : k ≤ a) (hb : k ≤ b) (hc : c < k) (hd : d < k) : ¬ AlternatingIndices a b c d := by
  simp only [AlternatingIndices]
  omega

/-- Part IV, Sections 5 and 7c: concatenation preserves nonalternation
when each word contains either both ports of an edge or neither. -/
theorem nonalternating_append {N : ℕ} (left right : List (Port N))
    (hlpair : ∀ b : Arc N, (⟨b,true⟩ : Port N) ∈ left ↔ ⟨b,false⟩ ∈ left)
    (hrpair : ∀ b : Arc N, (⟨b,true⟩ : Port N) ∈ right ↔ ⟨b,false⟩ ∈ right)
    (hl : Nonalternating left) (hr : Nonalternating right) : Nonalternating (left ++ right) := by
  intro b c hbc
  have missing : ∀ e : Arc N, (⟨e,true⟩ : Port N) ∉ left → (⟨e,true⟩ : Port N) ∉ right →
      (left ++ right).idxOf ⟨e,true⟩ = (left ++ right).idxOf ⟨e,false⟩ := by
    intro e hle hre
    have hs : (⟨e,true⟩ : Port N) ∉ left ++ right := by simp only [List.mem_append]; exact not_or.mpr ⟨hle,hre⟩
    have ht : (⟨e,false⟩ : Port N) ∉ left ++ right := by
      simp only [List.mem_append]
      exact not_or.mpr ⟨fun h => hle ((hlpair e).mpr h),fun h => hre ((hrpair e).mpr h)⟩
    rw [List.idxOf_eq_length hs,List.idxOf_eq_length ht]
  by_cases hb : (⟨b,true⟩ : Port N) ∈ left
  · have hbt := (hlpair b).mp hb
    rw [List.idxOf_append_of_mem hb,List.idxOf_append_of_mem hbt]
    by_cases hc : (⟨c,true⟩ : Port N) ∈ left
    · rw [List.idxOf_append_of_mem hc,List.idxOf_append_of_mem ((hlpair c).mp hc)]
      exact hl b c hbc
    · by_cases hcr : (⟨c,true⟩ : Port N) ∈ right
      · rw [List.idxOf_append_of_notMem hc,
          List.idxOf_append_of_notMem (fun h => hc ((hlpair c).mpr h))]
        exact not_alternating_separated (List.idxOf_lt_length_of_mem hb)
          (List.idxOf_lt_length_of_mem hbt) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
      · rw [missing c hc hcr]
        exact not_alternating_eq_right _ _ _
  · have hbt : (⟨b,false⟩ : Port N) ∉ left := fun h => hb ((hlpair b).mpr h)
    by_cases hbr : (⟨b,true⟩ : Port N) ∈ right
    · rw [List.idxOf_append_of_notMem hb,List.idxOf_append_of_notMem hbt]
      by_cases hc : (⟨c,true⟩ : Port N) ∈ left
      · rw [List.idxOf_append_of_mem hc,List.idxOf_append_of_mem ((hlpair c).mp hc)]
        exact not_alternating_separated_rev (Nat.le_add_right _ _) (Nat.le_add_right _ _)
          (List.idxOf_lt_length_of_mem hc) (List.idxOf_lt_length_of_mem ((hlpair c).mp hc))
      · by_cases hcr : (⟨c,true⟩ : Port N) ∈ right
        · rw [List.idxOf_append_of_notMem hc,
            List.idxOf_append_of_notMem (fun h => hc ((hlpair c).mpr h))]
          have h := hr b c hbc
          simp only [AlternatingIndices] at h ⊢
          omega
        · rw [missing c hc hcr]
          exact not_alternating_eq_right _ _ _
    · rw [missing b hb hbr]
      exact not_alternating_eq_left _ _ _

/-- Part IV, Sections 5 and 7c: concatenating whole-pair nonalternating
component words gives a nonalternating word. -/
theorem nonalternating_flatMap {N : ℕ} {α : Type*} (roots : List α) (word : α → List (Port N))
    (hpairs : ∀ r ∈ roots, ∀ b : Arc N, (⟨b,true⟩ : Port N) ∈ word r ↔ ⟨b,false⟩ ∈ word r)
    (hnonalt : ∀ r ∈ roots, Nonalternating (word r)) : Nonalternating (roots.flatMap word) := by
  induction roots with
  | nil =>
    intro b c _
    exact not_alternating_eq_left _ _ _
  | cons r roots ih =>
    rw [List.flatMap_cons]
    apply nonalternating_append
    · exact hpairs r List.mem_cons_self
    · intro b
      simp only [List.mem_flatMap]
      constructor
      · rintro ⟨q,hq,hb⟩
        exact ⟨q,hq,(hpairs q (List.mem_cons_of_mem _ hq) b).mp hb⟩
      · rintro ⟨q,hq,hb⟩
        exact ⟨q,hq,(hpairs q (List.mem_cons_of_mem _ hq) b).mpr hb⟩
    · exact hnonalt r List.mem_cons_self
    · exact ih (fun q hq => hpairs q (List.mem_cons_of_mem _ hq))
        (fun q hq => hnonalt q (List.mem_cons_of_mem _ hq))

end GraphMinor.LRPlanarity
