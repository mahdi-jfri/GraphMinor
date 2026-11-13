module

public import GraphMinor.Compute.GM06Alg511CopyRow
public import GraphMinor.Compute.GM06Alg511CallRegisters
import Mathlib.Tactic

/-!
# Retaining the original drawing fields across a successor call

VI (5.11), page 134, calls (5.7) repeatedly in the same original
graph. Its reductions may overwrite the working drawing arrays.
Save the original field arrays above all array addresses written
by the callee and above all protected fields. Restore them after
the call, while retaining the returned bit and ordinary path rows.
Each save and restore costs linear time in the retained field size.
The construction uses the command's finite write set and needs no
assumption that the callee preserves its original working arrays.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Copy destination/source array pairs, using the verified full
row copier. Only counter register 20 is used by these copies. -/
def gm06Alg511CopyArrays : List (ℕ × ℕ) → Cmd
  | [] => .skip
  | p :: ps => .seq (gm06Alg511CopyRowProg p.2 p.1) (gm06Alg511CopyArrays ps)

/-- Total size of the source fields before the copies. -/
def gm06Alg511CopyArrayWords (pairs : List (ℕ × ℕ)) (s : State) : ℕ :=
  (pairs.map (fun p => (s.arrs p.2).length)).sum

private theorem copy_arrays_exec {w : ℕ} (pairs : List (ℕ × ℕ)) (s : State)
    (hnd : (pairs.map Prod.fst).Nodup)
    (hdis : ∀ p ∈ pairs, ∀ q ∈ pairs, p.1 ≠ q.2)
    (hw : 1 < 2 ^ w)
    (hlens : ∀ p ∈ pairs, (s.arrs p.2).length < 2 ^ w)
    (hwords : ∀ p ∈ pairs, ∀ d ∈ s.arrs p.2, d < 2 ^ w) :
    ∃ t u, Exec w (gm06Alg511CopyArrays pairs) s t u ∧
      u ≤ 1 + 6 * pairs.length + 12 * gm06Alg511CopyArrayWords pairs s ∧
      (∀ p ∈ pairs, t.arrs p.1 = s.arrs p.2) ∧ Keeps [20] (pairs.map Prod.fst) s t := by
  induction pairs generalizing s with
  | nil => exact ⟨s, 1, .skip s, by simp [gm06Alg511CopyArrayWords], by simp, Keeps.refl _ _ s⟩
  | cons p pairs ih =>
    obtain ⟨s₁, u₁, he₁, ht₁, hk₁, hp₁⟩ := gm06Alg511CopyRowProg_exec p.2 p.1
      (hdis p (by simp) p (by simp)).symm (s.arrs p.2) s hw
      (hlens p (by simp)) (hwords p (by simp)) rfl
    have htail : ∀ q ∈ pairs, s₁.arrs q.2 = s.arrs q.2 := by
      intro q hq
      exact hk₁.2 q.2 (by simpa using (hdis p (by simp) q (by simp [hq])).symm)
    obtain ⟨t, u, he, ht, hv, hk⟩ := ih s₁ (List.nodup_cons.mp hnd).2
      (fun q hq r hr => hdis q (by simp [hq]) r (by simp [hr]))
      (fun q hq => by rw [htail q hq]; exact hlens q (by simp [hq]))
      (fun q hq => by rw [htail q hq]; exact hwords q (by simp [hq]))
    have hsize : gm06Alg511CopyArrayWords pairs s₁ = gm06Alg511CopyArrayWords pairs s := by
      unfold gm06Alg511CopyArrayWords
      apply congrArg List.sum
      exact List.map_congr_left (fun q hq => congrArg List.length (htail q hq))
    refine ⟨t, u₁ + u, .seq he₁ he, ?_, ?_, ?_⟩
    · rw [hsize] at ht
      simp only [gm06Alg511CopyArrayWords, List.map_cons, List.sum_cons, List.length_cons] at ht ⊢
      omega
    · intro q hq
      rcases List.mem_cons.mp hq with heq | hq
      · subst q
        exact (hk.2 p.1 (List.nodup_cons.mp hnd).1).trans hp₁
      · exact (hv q hq).trans (htail q hq)
    · exact (hk₁.mono (by simp) (by simp)).trans hk (by simp)
        (by intro a ha; exact List.mem_cons_of_mem p.1 ha)

/-- Fresh save arrays lie above the callee and the protected fields.
The constant also separates them from fixed input-packing scratch. -/
def gm06Alg511CallArrayBase (callee : Cmd) (arrays : List ℕ) : ℕ :=
  callee.writtenArrs.sup id + arrays.toFinset.sup id + 1601

/-- A separate fresh destination for each retained field. -/
def gm06Alg511CallArrayPairs (callee : Cmd) (arrays : List ℕ) : List (ℕ × ℕ) :=
  List.ofFn (fun i : Fin arrays.length => (gm06Alg511CallArrayBase callee arrays + i.val, arrays[i.val]))

/-- Save original drawing fields, run the actual successor command,
and restore precisely those fields. Returned path arrays remain as
returned when their addresses are not among the protected fields. -/
def gm06Alg511PreserveCallArrays (callee : Cmd) (arrays : List ℕ) : Cmd :=
  .seq (gm06Alg511CopyArrays (gm06Alg511CallArrayPairs callee arrays))
    (.seq callee (gm06Alg511CopyArrays ((gm06Alg511CallArrayPairs callee arrays).map Prod.swap)))

private theorem array_pair_bounds (callee : Cmd) (arrays : List ℕ) (p : ℕ × ℕ)
    (hp : p ∈ gm06Alg511CallArrayPairs callee arrays) :
    gm06Alg511CallArrayBase callee arrays ≤ p.1 ∧ p.2 < gm06Alg511CallArrayBase callee arrays := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  have hh := Finset.le_sup (f := id) (List.mem_toFinset.mpr (List.getElem_mem i.isLt))
  dsimp only [Prod.fst, Prod.snd, id, gm06Alg511CallArrayBase] at *
  omega

private theorem array_pair_fresh (callee : Cmd) (arrays : List ℕ) (p : ℕ × ℕ)
    (hp : p ∈ gm06Alg511CallArrayPairs callee arrays) : p.1 ∉ callee.writtenArrs := by
  intro hm
  have hh := Finset.le_sup (f := id) hm
  have hb := (array_pair_bounds callee arrays p hp).1
  dsimp only [id, gm06Alg511CallArrayBase] at *
  omega

private theorem array_save_disjoint (callee : Cmd) (arrays : List ℕ) :
    ∀ p ∈ gm06Alg511CallArrayPairs callee arrays, ∀ q ∈ gm06Alg511CallArrayPairs callee arrays, p.1 ≠ q.2 := by
  intro p hp q hq
  have hp' := (array_pair_bounds callee arrays p hp).1
  have hq' := (array_pair_bounds callee arrays q hq).2
  omega

private theorem array_pair_sources (callee : Cmd) (arrays : List ℕ) :
    (gm06Alg511CallArrayPairs callee arrays).map Prod.snd = arrays := by
  simp only [gm06Alg511CallArrayPairs, List.map_ofFn, Function.comp_def]
  exact List.ofFn_getElem

private theorem array_save_nodup (callee : Cmd) (arrays : List ℕ) :
    ((gm06Alg511CallArrayPairs callee arrays).map Prod.fst).Nodup := by
  simp only [gm06Alg511CallArrayPairs, List.map_ofFn, Function.comp_def]
  apply List.nodup_ofFn_ofInjective
  intro i j hij
  exact Fin.ext (Nat.add_left_cancel hij)

/-- Saving and restoring the supplied original drawing fields
preserves the callee's other arrays and its result register. The
additional cost is linear in their total original word count.
The callee executes from the actual saved state and may overwrite
any of the original protected arrays. -/
theorem gm06Alg511PreserveCallArrays_exec {w B : ℕ} (callee : Cmd) (arrays : List ℕ)
    (hnd : arrays.Nodup) (s : State) (hw : 1 < 2 ^ w)
    (hlens : ∀ a ∈ arrays, (s.arrs a).length < 2 ^ w)
    (hwords : ∀ a ∈ arrays, ∀ d ∈ s.arrs a, d < 2 ^ w)
    (post : State → Prop)
    (hcall : ∀ s₁, (∀ a : ℕ, a < gm06Alg511CallArrayBase callee arrays → s₁.arrs a = s.arrs a) →
      (∀ r : ℕ, r ≠ 20 → s₁.regs r = s.regs r) →
      ∃ t u, Exec w callee s₁ t u ∧ u ≤ B ∧ post t) :
    ∃ t raw u, Exec w (gm06Alg511PreserveCallArrays callee arrays) s t u ∧
      u ≤ B + 2 + 12 * arrays.length + 24 * (arrays.map (fun a => (s.arrs a).length)).sum ∧
      post raw ∧ (∀ a : ℕ, a ∉ arrays → t.arrs a = raw.arrs a) ∧
      (∀ r : ℕ, r ≠ 20 → t.regs r = raw.regs r) ∧
      ∀ a ∈ arrays, t.arrs a = s.arrs a := by
  let pairs := gm06Alg511CallArrayPairs callee arrays
  have hsources : pairs.map Prod.snd = arrays := array_pair_sources callee arrays
  have hmem (p : ℕ × ℕ) (hp : p ∈ pairs) : p.2 ∈ arrays := by
    rw [← hsources]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  obtain ⟨s₁, u₁, he₁, ht₁, hsave, hk₁⟩ := copy_arrays_exec pairs s
    (array_save_nodup callee arrays) (array_save_disjoint callee arrays) hw
    (fun p hp => hlens p.2 (hmem p hp)) (fun p hp => hwords p.2 (hmem p hp))
  have harr₁ : ∀ a : ℕ, a < gm06Alg511CallArrayBase callee arrays → s₁.arrs a = s.arrs a := by
    intro a ha
    apply hk₁.2 a
    intro hm
    obtain ⟨p, hp, hpa⟩ := List.mem_map.mp hm
    have hb := (array_pair_bounds callee arrays p hp).1
    omega
  have hregs₁ : ∀ r : ℕ, r ≠ 20 → s₁.regs r = s.regs r :=
    fun r hr => hk₁.1 r (by simpa using hr)
  obtain ⟨raw, uraw, heraw, huraw, hpost⟩ := hcall s₁ harr₁ hregs₁
  have hsaved : ∀ p ∈ pairs, raw.arrs p.1 = s.arrs p.2 := by
    intro p hp
    exact (heraw.arrs_eq_of_not_mem_writtenArrs (array_pair_fresh callee arrays p hp)).trans (hsave p hp)
  have hrestore_nd : ((pairs.map Prod.swap).map Prod.fst).Nodup := by
    simpa only [List.map_map, Function.comp_def, Prod.fst_swap, hsources] using hnd
  have hrdis : ∀ p ∈ pairs.map Prod.swap, ∀ q ∈ pairs.map Prod.swap, p.1 ≠ q.2 := by
    intro p hp q hq
    obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact (array_save_disjoint callee arrays q' hq' p' hp').symm
  have hrlen : ∀ p ∈ pairs.map Prod.swap, (raw.arrs p.2).length < 2 ^ w := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [show q.swap.2 = q.1 from rfl, hsaved q hq]
    exact hlens q.2 (hmem q hq)
  have hrwords : ∀ p ∈ pairs.map Prod.swap, ∀ d ∈ raw.arrs p.2, d < 2 ^ w := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [show q.swap.2 = q.1 from rfl, hsaved q hq]
    exact hwords q.2 (hmem q hq)
  obtain ⟨t, u₂, he₂, ht₂, hrestore, hk₂⟩ := copy_arrays_exec (pairs.map Prod.swap) raw
    hrestore_nd hrdis hw hrlen hrwords
  have hsize : gm06Alg511CopyArrayWords pairs s = (arrays.map (fun a => (s.arrs a).length)).sum := by
    rw [gm06Alg511CopyArrayWords, ← hsources, List.map_map]
    rfl
  have hrsize : gm06Alg511CopyArrayWords (pairs.map Prod.swap) raw = gm06Alg511CopyArrayWords pairs s := by
    unfold gm06Alg511CopyArrayWords
    rw [List.map_map]
    apply congrArg List.sum
    exact List.map_congr_left (fun p hp => congrArg List.length (hsaved p hp))
  have hlen : pairs.length = arrays.length := List.length_ofFn
  refine ⟨t, raw, u₁ + (uraw + u₂), .seq he₁ (.seq heraw he₂), ?_, hpost, ?_, ?_, ?_⟩
  · rw [hrsize, hsize] at ht₂
    rw [hsize, hlen] at ht₁
    simp only [List.length_map, hlen] at ht₂
    omega
  · intro a ha
    apply hk₂.2 a
    simpa only [List.map_map, Function.comp_def, Prod.fst_swap, hsources] using ha
  · intro r hr
    exact hk₂.1 r (by simpa using hr)
  · intro a ha
    have hm : a ∈ pairs.map Prod.snd := hsources ▸ ha
    obtain ⟨p, hp, hpa⟩ := List.mem_map.mp hm
    have hh := hrestore p.swap (List.mem_map.mpr ⟨p, hp, rfl⟩)
    change t.arrs p.2 = raw.arrs p.1 at hh
    rw [hpa, hsaved p hp, hpa] at hh
    exact hh

/-- Retain both the original drawing fields and the seven scalar
loop words while leaving the callee's bit and path array as returned. -/
def gm06Alg511PreserveSuccessorCall (callee : Cmd) (arrays : List ℕ) : Cmd :=
  gm06Alg511PreserveCallRegisters (gm06Alg511PreserveCallArrays callee arrays)

/-- The complete save/call/restore wrapper preserves all immutable
fields and scalar loop words without assuming either frame property
of the supplied command. The result bit and array 8 are exactly the
callee's outputs, and the overhead is linear in retained field size. -/
theorem gm06Alg511PreserveSuccessorCall_exec {w B : ℕ} (callee : Cmd) (arrays : List ℕ)
    (hnd : arrays.Nodup) (h8 : 8 ∉ arrays) (s : State) (hw : 1 < 2 ^ w)
    (hlens : ∀ a ∈ arrays, (s.arrs a).length < 2 ^ w)
    (hwords : ∀ a ∈ arrays, ∀ d ∈ s.arrs a, d < 2 ^ w)
    (hregs : ∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], s.regs j < 2 ^ w)
    (post : State → Prop)
    (hcall : ∀ s₁, (∀ a : ℕ, a < gm06Alg511CallArrayBase callee arrays → s₁.arrs a = s.arrs a) →
      (∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], s₁.regs j = s.regs j) →
      ∃ t u, Exec w callee s₁ t u ∧ u ≤ B ∧ post t) :
    ∃ t raw u, Exec w (gm06Alg511PreserveSuccessorCall callee arrays) s t u ∧
      u ≤ B + 32 + 12 * arrays.length + 24 * (arrays.map (fun a => (s.arrs a).length)).sum ∧
      post raw ∧ t.regs 0 = raw.regs 0 ∧ t.arrs 8 = raw.arrs 8 ∧
      (∀ a ∈ arrays, t.arrs a = s.arrs a) ∧
      ∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], t.regs j = s.regs j := by
  let Q : State → Prop := fun t => ∃ raw, post raw ∧ t.regs 0 = raw.regs 0 ∧
    t.arrs 8 = raw.arrs 8 ∧ ∀ a ∈ arrays, t.arrs a = s.arrs a
  obtain ⟨t, st, u, he, ht, hQ, ha, h0, hg⟩ :=
    gm06Alg511PreserveCallRegisters_exec (B := B + 2 + 12 * arrays.length +
      24 * (arrays.map (fun a => (s.arrs a).length)).sum)
      (gm06Alg511PreserveCallArrays callee arrays) s hregs Q (by
        intro ss hass hgss
        have hlenss : ∀ a ∈ arrays, (ss.arrs a).length < 2 ^ w := by
          simpa only [hass] using hlens
        have hwordss : ∀ a ∈ arrays, ∀ d ∈ ss.arrs a, d < 2 ^ w := by
          simpa only [hass] using hwords
        obtain ⟨st, raw, u, he, ht, hp, harr, hr, hprotected⟩ :=
          gm06Alg511PreserveCallArrays_exec callee arrays hnd ss hw hlenss hwordss post (by
            intro ss₁ harr₁ hreg₁
            apply hcall ss₁
            · intro a ha
              exact (harr₁ a ha).trans (congrFun hass a)
            · intro j hj
              have hj20 : j ≠ 20 := by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
              exact (hreg₁ j hj20).trans (hgss j hj))
        refine ⟨st, u, he, ?_, raw, hp, hr 0 (by decide), harr 8 h8, ?_⟩
        · simpa only [hass] using ht
        · intro a ha
          exact (hprotected a ha).trans (congrFun hass a))
  obtain ⟨raw, hp, hbit, hpath, hfields⟩ := hQ
  refine ⟨t, raw, u, he, by omega, hp, h0.trans hbit, ?_, ?_, hg⟩
  · exact (congrFun ha 8).trans hpath
  · intro a ha'
    exact (congrFun ha a).trans (hfields a ha')

end GraphMinor.Compute
