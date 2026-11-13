module

public import GraphMinor.Compute.GM06Alg34FilterOrder

/-!
# Crossing order survives filtering a cuff list

For retained labels, filtering preserves all index comparisons and
therefore both cyclic-interval tests. Missing labels give no crossing
in either list. This proves that deleting other vertices does not alter
the cyclic crossing relation on the surviving cuff vertices.
-/

public section
namespace GraphMinor.Compute

open GM06DrawingData

private theorem gm06_cyclicBetween_filter {n : ℕ} (L : List (Fin n)) (hL : L.Nodup)
    (p : Fin n → Bool) {a c b : Fin n}
    (ha : a ∈ L.filter p) (hc : c ∈ L.filter p) (hb : b ∈ L.filter p) :
    cyclicBetween ((L.filter p).idxOf a) ((L.filter p).idxOf c) ((L.filter p).idxOf b) =
      cyclicBetween (L.idxOf a) (L.idxOf c) (L.idxOf b) := by
  have hac := gm06_idxOf_lt_idxOf_filter L hL p ha hc
  have hab := gm06_idxOf_lt_idxOf_filter L hL p ha hb
  have hbc := gm06_idxOf_lt_idxOf_filter L hL p hb hc
  simp only [cyclicBetween, hac, hab, hbc]

private theorem gm06_crossesOnList_false {n : ℕ} (L : List (Fin n)) (a c b d : Fin n)
    (h : ¬ (a ∈ L ∧ c ∈ L ∧ b ∈ L ∧ d ∈ L)) : crossesOnList L a c b d = false := by
  have hg : ¬ (a ∈ L ∧ c ∈ L ∧ b ∈ L ∧ d ∈ L ∧
      a ≠ c ∧ b ≠ d ∧ a ≠ b ∧ a ≠ d ∧ c ≠ b ∧ c ≠ d) :=
    fun hp => h ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩
  simp only [crossesOnList, hg, decide_false, Bool.false_and]

/-- Filtering a nonrepeating cuff list preserves its crossing test on
any four labels that the filter retains. -/
theorem gm06_crossesOnList_filter {n : ℕ} (L : List (Fin n)) (hL : L.Nodup)
    (p : Fin n → Bool) (a c b d : Fin n)
    (ha : p a = true) (hc : p c = true) (hb : p b = true) (hd : p d = true) :
    crossesOnList (L.filter p) a c b d = crossesOnList L a c b d := by
  by_cases hall : a ∈ L ∧ c ∈ L ∧ b ∈ L ∧ d ∈ L
  · obtain ⟨haL, hcL, hbL, hdL⟩ := hall
    have haF : a ∈ L.filter p := List.mem_filter.mpr ⟨haL, ha⟩
    have hcF : c ∈ L.filter p := List.mem_filter.mpr ⟨hcL, hc⟩
    have hbF : b ∈ L.filter p := List.mem_filter.mpr ⟨hbL, hb⟩
    have hdF : d ∈ L.filter p := List.mem_filter.mpr ⟨hdL, hd⟩
    simp only [crossesOnList, haF, hcF, hbF, hdF, haL, hcL, hbL, hdL, true_and]
    rw [gm06_cyclicBetween_filter L hL p haF hcF hbF,
      gm06_cyclicBetween_filter L hL p haF hcF hdF]
  · have hfilter : ¬ (a ∈ L.filter p ∧ c ∈ L.filter p ∧ b ∈ L.filter p ∧ d ∈ L.filter p) := by
      rintro ⟨haF, hcF, hbF, hdF⟩
      exact hall ⟨List.mem_of_mem_filter haF, List.mem_of_mem_filter hcF,
        List.mem_of_mem_filter hbF, List.mem_of_mem_filter hdF⟩
    rw [gm06_crossesOnList_false _ _ _ _ _ hfilter, gm06_crossesOnList_false _ _ _ _ _ hall]

end GraphMinor.Compute
