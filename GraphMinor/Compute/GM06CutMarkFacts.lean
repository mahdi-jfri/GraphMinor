module

public import GraphMinor.Compute.GM06CutTables

/-!
# Lookup and word bounds for computed cut marks

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) obtains each
local position from the linkage and the two cuff orders. The lookup
lemmas identify the stored plus-one path end when its vertex key
is unique. The bounds show that the complete mark construction uses
only words in the original label ranges. Scattering preserves these
bounds even at unused permanent vertex slots.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Scattering values satisfying a predicate preserves that predicate
in every table entry. An out-of-range write leaves the table unchanged. -/
theorem gm06Scatter_forall (P : ℕ → Prop) (pairs : List (ℕ × ℕ)) (table : List ℕ)
    (hp : ∀ p ∈ pairs, P p.2) (ht : ∀ x ∈ table, P x) :
    ∀ x ∈ gm06Scatter pairs table, P x := by
  induction pairs generalizing table with
  | nil => exact ht
  | cons p ps ih =>
    apply ih (table.set p.1 p.2) (fun q hq => hp q (by simp [hq]))
    intro x hx
    rcases List.mem_or_eq_of_mem_set hx with hx | rfl
    · exact ht x hx
    · exact hp p List.mem_cons_self

/-- Path-end keys are the corresponding origins of the directed ends. -/
theorem gm06CutPathEndPairs_keys (origins darts : List ℕ) (incoming : Bool) :
    (gm06CutPathEndPairs origins darts incoming).map Prod.fst =
      darts.map (fun d => origins[(if incoming then gm06DartMate d else d)]?.getD 0) := by
  simp only [gm06CutPathEndPairs, List.map_map, Function.comp_def]

/-- A present path dart writes its own plus-one end at its origin. -/
theorem gm06CutPathEndPairs_mem (origins darts : List ℕ) (incoming : Bool)
    (d : ℕ) (hd : d ∈ darts) :
    let q := if incoming then gm06DartMate d else d
    (origins[q]?.getD 0, q + 1) ∈ gm06CutPathEndPairs origins darts incoming :=
  List.mem_map.mpr ⟨d, hd, rfl⟩

/-- Every stored path-end mark is at most the ordinary dart count. -/
theorem gm06CutPathEndPairs_bound {m : ℕ} (origins darts : List ℕ) (incoming : Bool)
    (hd : ∀ d ∈ darts, d < 2 * m) :
    ∀ p ∈ gm06CutPathEndPairs origins darts incoming, p.2 ≤ 2 * m := by
  intro p hp
  obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hp
  have hdi := hd d hd'
  have hmate := gm06DartMate_lt hdi
  cases incoming <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- A unique outgoing path-end key stores exactly the indicated dart. -/
theorem gm06BuildCutTables_outgoing_at {n m d : ℕ} (origins : List ℕ)
    (paths : List (List ℕ)) (inner outer : List ℕ)
    (hd : d ∈ paths.flatten) (hv : origins[d]?.getD 0 < n)
    (hkeys : ((gm06CutPathEndPairs origins paths.flatten false).map Prod.fst).Nodup) :
    (gm06BuildCutTables n m origins paths inner outer).outgoing[origins[d]?.getD 0]? = some (d + 1) := by
  exact gm06Scatter_getElem?_of_mem _ _ hkeys _
    (gm06CutPathEndPairs_mem origins paths.flatten false d hd) (by simpa using hv)

/-- A unique incoming path-end key stores the arriving dart's reverse. -/
theorem gm06BuildCutTables_incoming_at {n m d : ℕ} (origins : List ℕ)
    (paths : List (List ℕ)) (inner outer : List ℕ)
    (hd : d ∈ paths.flatten) (hv : origins[gm06DartMate d]?.getD 0 < n)
    (hkeys : ((gm06CutPathEndPairs origins paths.flatten true).map Prod.fst).Nodup) :
    (gm06BuildCutTables n m origins paths inner outer).incoming[origins[gm06DartMate d]?.getD 0]? =
      some (gm06DartMate d + 1) := by
  exact gm06Scatter_getElem?_of_mem _ _ hkeys _
    (gm06CutPathEndPairs_mem origins paths.flatten true d hd) (by simpa using hv)

/-- Signed cuff writes have exactly their supplied vertex order as keys. -/
theorem gm06CutCuffPairs_keys (base : ℕ) (cuff : List ℕ) (positive : Bool) :
    (gm06CutCuffPairs base cuff positive).map Prod.fst = cuff := by
  simp only [gm06CutCuffPairs, List.map_map, Function.comp_def]
  exact List.zipIdx_map_fst _ _

/-- Both cuff signs fit in the augmented dart-label range. -/
theorem gm06CutCuffPairs_bound (base : ℕ) (cuff : List ℕ) (positive : Bool) :
    ∀ p ∈ gm06CutCuffPairs base cuff positive, p.2 < 2 * (base + cuff.length) + 1 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hi : q.2 < cuff.length := by simpa using List.snd_lt_add_of_mem_zipIdx hq
  have hprev := gm06PreviousCuffIndex_lt hi
  cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- All four input-derived cut tables consist of valid words. -/
theorem gm06BuildCutTables_words {w n m : ℕ} (origins : List ℕ) (paths : List (List ℕ))
    (inner outer : List ℕ) (hsize : 2 * (m + inner.length + outer.length) + 1 < 2 ^ w)
    (hd : ∀ d ∈ paths.flatten, d < 2 * m) :
    let marks := gm06BuildCutTables n m origins paths inner outer
    ∀ x ∈ marks.incoming ++ marks.outgoing ++ marks.cuffPositive ++ marks.cuffNegative, x < 2 ^ w := by
  dsimp only [gm06BuildCutTables]
  have hz : ∀ x ∈ List.replicate n 0, x < 2 ^ w := by
    intro x hx
    have he : x = 0 := (List.mem_replicate.mp hx).2
    simpa only [he] using Nat.two_pow_pos w
  have hpath : ∀ incoming, ∀ x ∈ gm06Scatter (gm06CutPathEndPairs origins paths.flatten incoming)
      (List.replicate n 0), x < 2 ^ w := by
    intro incoming
    exact gm06Scatter_forall _ _ _
      (fun p hp => by have hb := gm06CutPathEndPairs_bound origins paths.flatten incoming hd p hp; omega) hz
  have hcuff : ∀ positive, ∀ x ∈ gm06Scatter (gm06CutCuffPairs m inner positive ++
      gm06CutCuffPairs (m + inner.length) outer positive) (List.replicate n 0), x < 2 ^ w := by
    intro positive
    apply gm06Scatter_forall _ _ _ _ hz
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · have hb := gm06CutCuffPairs_bound m inner positive p hp
      omega
    · exact gm06CutCuffPairs_bound (m + inner.length) outer positive p hp |>.trans hsize
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with ((hx | hx) | hx) | hx
  · exact hpath true x hx
  · exact hpath false x hx
  · exact hcuff true x hx
  · exact hcuff false x hx

end GraphMinor.Compute
