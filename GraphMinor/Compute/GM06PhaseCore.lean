module

public import GraphMinor.Compute.GM06PhaseRows
public import GraphMinor.Compute.GM06Reduction4Phase
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Loading the current core for the finite phases

The two phases of VI (5.7), page 133, read the current endpoint,
rotation, cuff and linkage arrays. This pass copies these fields into
the finite cut program's input arrays and constructs the permanent
vertex-slot range. No face, component or incidence table is an input.
The source arrays remain available throughout both phases.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Copy a list of core fields into distinct reserved scratch arrays. -/
def gm06PhaseCopyFieldsProg : List (ℕ × ℕ) → Cmd
  | [] => .skip
  | (src, dst) :: jobs => .seq (gm06PhaseCopyProg src dst) (gm06PhaseCopyFieldsProg jobs)

/-- The field copier reads only low core arrays and preserves every
array outside its destination list. Its time is linear in the copied words. -/
theorem gm06PhaseCopyFieldsProg_exec {w : ℕ} (jobs : List (ℕ × ℕ)) (s : State)
    (hw : 1 < 2 ^ w)
    (hslots : ∀ p ∈ jobs, p.1 < 600 ∧ 600 ≤ p.2)
    (hnd : (jobs.map Prod.snd).Nodup)
    (hfit : ∀ p ∈ jobs, (s.arrs p.1).length < 2 ^ w)
    (hwords : ∀ p ∈ jobs, ∀ x ∈ s.arrs p.1, x < 2 ^ w) :
    ∃ sf t, Exec w (gm06PhaseCopyFieldsProg jobs) s sf t ∧
      t ≤ 1 + 6 * jobs.length + 14 * (jobs.map (fun p => (s.arrs p.1).length)).sum ∧
      Keeps [650] (jobs.map Prod.snd) s sf ∧
      ∀ p ∈ jobs, sf.arrs p.2 = s.arrs p.1 := by
  induction jobs generalizing s with
  | nil => exact ⟨s, 1, .skip s, by simp, Keeps.refl _ _ _, by simp⟩
  | cons p jobs ih =>
    obtain ⟨src, dst⟩ := p
    have hp := hslots (src, dst) List.mem_cons_self
    have hneq : src ≠ dst := by omega
    obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm06PhaseCopyProg_exec src dst hneq (s.arrs src) s hw
      (hfit _ List.mem_cons_self) (hwords _ List.mem_cons_self) rfl
    have htail : ∀ p ∈ jobs, p.1 < 600 ∧ 600 ≤ p.2 :=
      fun p hp => hslots p (List.mem_cons_of_mem _ hp)
    have hsrc : ∀ p ∈ jobs, s₁.arrs p.1 = s.arrs p.1 := by
      intro p hp
      exact hk₁.2 p.1 (by simp only [List.mem_singleton]; have := htail p hp; omega)
    have hnd' : (dst :: jobs.map Prod.snd).Nodup := hnd
    obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := ih s₁ htail (List.nodup_cons.mp hnd').2
      (fun p hp => by rw [hsrc p hp]; exact hfit p (List.mem_cons_of_mem _ hp))
      (fun p hp => by rw [hsrc p hp]; exact hwords p (List.mem_cons_of_mem _ hp))
    have hsum : (jobs.map (fun p => (s₁.arrs p.1).length)).sum =
        (jobs.map (fun p => (s.arrs p.1).length)).sum := by
      congr 1
      exact List.map_congr_left (fun p hp => congrArg List.length (hsrc p hp))
    refine ⟨sf, t₁ + tf, .seq he₁ hef, ?_, ?_, ?_⟩
    · rw [hsum] at htf
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
    · exact (hk₁.mono (fun _ h => h) (by simp)).trans hkf (fun _ h => h)
        (by intro a ha; exact List.mem_cons_of_mem _ ha)
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact (hkf.2 dst (List.nodup_cons.mp hnd').1).trans hd₁
      · exact (hdf p hp).trans (hsrc p hp)

/-- Current core fields required by the cut, with no cached rows. -/
def gm06PhaseCoreCopies : List (ℕ × ℕ) :=
  [(4, 600), (3, 601), (8, 608), (6, 609), (7, 610)]

/-- Construct the permanent vertex-slot range in array 618. -/
def gm06PhaseVertexSlotsProg : Cmd :=
  gm13TabulateProg 650 (.reg 648) (.reg 650) 618

/-- The vertex list is computed from the original slot count. -/
theorem gm06PhaseVertexSlotsProg_exec {w n : ℕ} (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (h648 : s.regs 648 = n) :
    ∃ sf t, Exec w gm06PhaseVertexSlotsProg s sf t ∧ t ≤ 6 + 13 * n ∧
      Keeps [650] [618] s sf ∧ sf.arrs 618 = List.range n := by
  obtain ⟨sf, t, he, ht, hk, hd⟩ := gm13TabulateProg_exec 650 (.reg 648) (.reg 650) 618 (List.range n) s hw
    (by simpa using hn)
    (fun st hk => by simpa using GraphMinor.Compute.Crossing.eval_reg ((hk.1 648 (by decide)).trans h648) hn)
    (fun st i hi _ hr => by
      have hi' : i < n := by simpa using hi
      simpa only [List.getElem_range] using GraphMinor.Compute.Crossing.eval_reg hr (hi'.trans hn))
  exact ⟨sf, t, he, by simpa only [Expr.cost, List.length_range, Nat.mul_comm] using ht, hk, hd⟩

/-- Load runtime counts, copy the actual core, and enumerate vertex slots. -/
def gm06PhaseLoadCoreProg : Cmd :=
  .seq (.assign 648 (.reg 100))
    (.seq (.assign 649 (.len 12))
      (.seq (gm06PhaseCopyFieldsProg gm06PhaseCoreCopies) gm06PhaseVertexSlotsProg))

/-- Scratch arrays written while loading the core. -/
def gm06PhaseLoadCoreArrs : List ℕ := [600, 601, 608, 609, 610, 618]

/-- Registers written while loading the core. -/
def gm06PhaseLoadCoreRegs : List ℕ := [648, 649, 650]

/-- Exact current-core loading for either phase. The ordinary count is
the length of the permanent edge mask, including retired edge slots.
Every array and register outside the listed scratch frame is unchanged. -/
theorem gm06PhaseLoadCoreProg_exec {w m : ℕ} (x : GM06SuccessorInput) (s : State)
    (hw : 1 < 2 ^ w) (hn : x.vertexCount < 2 ^ w) (hm : m < 2 ^ w)
    (h100 : s.regs 100 = x.vertexCount) (h12 : (s.arrs 12).length = m)
    (h4 : s.arrs 4 = gm06EncodeRows x.rotations) (h3 : s.arrs 3 = x.endpoints)
    (h8 : s.arrs 8 = gm06EncodeRows x.linkage) (h6 : s.arrs 6 = x.innerCuff) (h7 : s.arrs 7 = x.outerCuff)
    (hfit : ∀ p ∈ gm06PhaseCoreCopies, (s.arrs p.1).length < 2 ^ w)
    (hwords : ∀ p ∈ gm06PhaseCoreCopies, ∀ a ∈ s.arrs p.1, a < 2 ^ w) :
    ∃ sf t, Exec w gm06PhaseLoadCoreProg s sf t ∧
      t ≤ 41 + 13 * x.vertexCount + 14 *
        ((gm06EncodeRows x.rotations).length + x.endpoints.length +
          (gm06EncodeRows x.linkage).length + x.innerCuff.length + x.outerCuff.length) ∧
      Keeps gm06PhaseLoadCoreRegs gm06PhaseLoadCoreArrs s sf ∧
      sf.arrs 600 = gm06EncodeRows x.rotations ∧ sf.arrs 601 = x.endpoints ∧
      sf.arrs 608 = gm06EncodeRows x.linkage ∧ sf.arrs 609 = x.innerCuff ∧ sf.arrs 610 = x.outerCuff ∧
      sf.arrs 618 = List.range x.vertexCount ∧ sf.regs 648 = x.vertexCount ∧ sf.regs 649 = m := by
  let s₀ := s.setReg 648 x.vertexCount
  let s₁ := s₀.setReg 649 m
  have he₀ : Exec w (.assign 648 (.reg 100)) s s₀ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg h100 hn)
  have he₁ : Exec w (.assign 649 (.len 12)) s₀ s₁ 2 :=
    .assign (by simpa only [h12] using GraphMinor.Compute.Crossing.eval_len (show s₀.arrs 12 = s.arrs 12 from rfl) (by rw [h12]; exact hm))
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩ := gm06PhaseCopyFieldsProg_exec gm06PhaseCoreCopies s₁ hw
    (by simp [gm06PhaseCoreCopies]) (by decide)
    (by simpa only [s₁, s₀, State.setReg_arrs] using hfit)
    (by simpa only [s₁, s₀, State.setReg_arrs] using hwords)
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm06PhaseVertexSlotsProg_exec s₂ hw hn
    ((hk₂.1 648 (by decide)).trans (by simp [s₁, s₀]))
  have hs₁ : Keeps gm06PhaseLoadCoreRegs gm06PhaseLoadCoreArrs s s₁ :=
    ((Keeps.refl _ _ s).setReg (by simp [gm06PhaseLoadCoreRegs]) _).setReg (by simp [gm06PhaseLoadCoreRegs]) _
  have hk : Keeps gm06PhaseLoadCoreRegs gm06PhaseLoadCoreArrs s sf :=
    (hs₁.trans hk₂ (by simp [gm06PhaseLoadCoreRegs]) (by simp [gm06PhaseCoreCopies, gm06PhaseLoadCoreArrs])).trans hkf
      (by simp [gm06PhaseLoadCoreRegs]) (by simp [gm06PhaseLoadCoreArrs])
  have hfield : ∀ p ∈ gm06PhaseCoreCopies, sf.arrs p.2 = s.arrs p.1 := by
    intro p hp
    have hneq : p.2 ≠ 618 := by
      simp only [gm06PhaseCoreCopies, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hkf.2 p.2 (by simpa using hneq)).trans (hd₂ p hp)
  refine ⟨sf, 2 + (2 + (t₂ + tf)), .seq he₀ (.seq he₁ (.seq he₂ hef)), ?_, hk,
    (hfield (4, 600) (by simp [gm06PhaseCoreCopies])).trans h4,
    (hfield (3, 601) (by simp [gm06PhaseCoreCopies])).trans h3,
    (hfield (8, 608) (by simp [gm06PhaseCoreCopies])).trans h8,
    (hfield (6, 609) (by simp [gm06PhaseCoreCopies])).trans h6,
    (hfield (7, 610) (by simp [gm06PhaseCoreCopies])).trans h7, hdf,
    (hkf.1 648 (by decide)).trans ((hk₂.1 648 (by decide)).trans (by simp [s₁, s₀])),
    (hkf.1 649 (by decide)).trans ((hk₂.1 649 (by decide)).trans (by simp [s₁]))⟩
  simp only [gm06PhaseCoreCopies, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, h4, h3, h8, h6, h7, s₁, s₀, State.setReg_arrs] at ht₂
  omega

end GraphMinor.Compute
