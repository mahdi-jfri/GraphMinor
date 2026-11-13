module

public import GraphMinor.Compute.Algorithm94Aux

/-!
# Copying finished private buffers to caller outputs

The final buffers lie at or above the private array base, and the caller
outputs lie below it. Copying an output therefore preserves every source
buffer. Distinct destinations keep earlier outputs intact. The scratch
registers also lie above the caller's register base.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Copy each private source to its caller destination, using high registers. -/
def case3PublishArraysProg (pairs : List (ℕ × ℕ)) (r_base : ℕ) : Cmd :=
  pairs.foldr (fun p rest => .seq (copyArrLoopProg p.1 p.2 (r_base + 132) (r_base + 133)) rest) .skip

/-- All requested outputs receive their original source buffers, with the
caller frame and a linear sum of copying costs. -/
theorem case3PublishArraysProg_exec {w : ℕ} (pairs : List (ℕ × ℕ)) (a_base r_base : ℕ)
    (hindices : ∀ p ∈ pairs, a_base ≤ p.1 ∧ p.2 < a_base)
    (hnd : (pairs.map Prod.snd).Nodup) (hw : 1 < 2 ^ w) (s : State)
    (hlens : ∀ p ∈ pairs, (s.arrs p.1).length < 2 ^ w)
    (hwords : ∀ p ∈ pairs, ∀ x ∈ s.arrs p.1, x < 2 ^ w) :
    ∃ s' t, Exec w (case3PublishArraysProg pairs r_base) s s' t ∧
      t ≤ (pairs.map (fun p => 8 + 15 * (s.arrs p.1).length)).sum + 1 ∧
      (∀ p ∈ pairs, s'.arrs p.2 = s.arrs p.1) ∧
      (∀ a, a ∉ pairs.map Prod.snd → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  induction pairs generalizing s with
  | nil =>
    exact ⟨s, 1, .skip s, by simp, by simp, by simp, fun _ _ => rfl⟩
  | cons p pairs ih =>
    have hp := hindices p List.mem_cons_self
    have htail := fun q hq => hindices q (List.mem_cons_of_mem _ hq)
    have hnodup := List.nodup_cons.mp hnd
    obtain ⟨s₁, t₁, hex₁, ht₁, hbuf₁, harr₁, hreg₁⟩ := copyArrLoopProg_exec
      p.1 p.2 (r_base + 132) (r_base + 133) (by romega) (by romega) hw s
      (hlens p List.mem_cons_self) (hwords p List.mem_cons_self)
    have hsource : ∀ q ∈ pairs, s₁.arrs q.1 = s.arrs q.1 := by
      intro q hq
      exact harr₁ q.1 (by have hq' := htail q hq; romega)
    obtain ⟨s₂, t₂, hex₂, ht₂, hbuf₂, harr₂, hreg₂⟩ := ih htail hnodup.2 s₁
      (by intro q hq; rw [hsource q hq]; exact hlens q (List.mem_cons_of_mem _ hq))
      (by intro q hq; rw [hsource q hq]; exact hwords q (List.mem_cons_of_mem _ hq))
    have hcost : (pairs.map (fun q => 8 + 15 * (s₁.arrs q.1).length)).sum =
        (pairs.map (fun q => 8 + 15 * (s.arrs q.1).length)).sum := by
      congr 1
      exact List.map_congr_left (fun q hq => by rw [hsource q hq])
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, ?_, ?_, ?_⟩
    · rw [hcost] at ht₂
      simp only [List.map_cons, List.sum_cons]
      omega
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (harr₂ q.2 hnodup.1).trans hbuf₁
      · exact (hbuf₂ q hq).trans (hsource q hq)
    · intro a ha
      have hne : a ≠ p.2 := by intro h; exact ha (by simp [h])
      have hnot : a ∉ pairs.map Prod.snd := fun h => ha (List.mem_cons_of_mem _ h)
      exact (harr₂ a hnot).trans (harr₁ a hne)
    · intro r hr
      exact (hreg₂ r hr).trans (hreg₁ r (by romega) (by romega))

end GraphMinor.Compute
