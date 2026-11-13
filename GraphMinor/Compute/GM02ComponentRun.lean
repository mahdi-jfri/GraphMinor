module

public import GraphMinor.Compute.GM02ComponentLabelsProg
public import GraphMinor.Compute.GM02SingleComponentProg
public import GraphMinor.Compute.GM02ComponentCounts

/-!
# Running and counting one component test

Initialize the separator labels, search from the selected vertex, then
count input terminals reached by that search. This combines the verified
RAM operations into the component operation used by II (3.1), page 316.
The graph's adjacency arrays and the input subset are preserved.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set TwoPaths Classical

/-- Registers used by one candidate component operation. -/
def gm02ComponentRegs : List ℕ := [60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 180, 182, 183]

/-- Arrays used by the forbidden-vertex search. -/
def gm02ComponentArrays : List ℕ := [60, 61, 62, 63]

/-- A search frame permits only the component-operation scratch locations. -/
theorem gm02Component_keeps_of_frame {s₀ s : State} (hs : SFrame s₀ s) :
    Keeps gm02ComponentRegs gm02ComponentArrays s₀ s := by
  constructor
  · intro r hr
    apply hs.1 r
    simp only [gm02ComponentRegs, List.mem_cons, not_or] at hr
    dsimp only [Reg] at hr ⊢
    omega
  · intro a ha
    apply hs.2 a <;> intro he <;> apply ha <;> simp [gm02ComponentArrays, he, aLab, aPar, aQue]

/-- Search a component and count its original terminals, using arrays
10, 11, 12 for graph adjacency and array 5 for the original subset bits. -/
def gm02ComponentRunProg (k : ℕ) : Cmd :=
  .seq (gm02ComponentLabelsProg 200 k)
    (.seq (gm02SingleComponentProg 10 11 12) (gm02CountIntersectionProg 5 aLab 1))

/-- The combined operation returns the exact terminal count of the selected
component. Every input array and candidate-slot register survives. -/
theorem gm02ComponentRunProg_exec {n k w : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (Q : Finset (Fin n)) (f : Fin k → ℕ)
    (hf : ∀ i, f i ≤ n) (a : Fin n) (ha : a ∉ gm02SlotVertices (n := n) f)
    (s : State) (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    (hadj : IsAdjList G 10 11 12 lists s) (hent : (s.arrs 12).length < 2 ^ w)
    (hrn : s.regs 40 = n) (hra : s.regs 181 = a.val)
    (hq : s.arrs 5 = gm02VertexBits Q) (hslots : ∀ i, s.regs (200 + i.val) = f i) :
    ∃ s' t, Exec w (gm02ComponentRunProg k) s s' t ∧
      t ≤ 73 + n * (k * 6 + 57) + 29 * totalAdjEntries lists ∧
      Keeps gm02ComponentRegs gm02ComponentArrays s s' ∧
      s'.regs 183 = (GM02.deletedComponent (Graph.ofSimpleGraph G)
        (gm02SlotVertices (n := n) f : Set (Fin n)) a ∩ (Q : Set (Fin n))).ncard ∧
      ∃ mask : Fin n → ℕ, s'.arrs aLab = List.ofFn mask ∧
        (∀ v, mask v ≤ 2) ∧ (∀ v, mask v = 1 ↔
          v ∈ GM02.deletedComponent (Graph.ofSimpleGraph G)
            (gm02SlotVertices (n := n) f : Set (Fin n)) a) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hl₁⟩ := gm02ComponentLabelsProg_exec 200 (by decide)
    f hf s (by omega) hn hrn hslots
  have hadj₁ : IsAdjList G 10 11 12 lists s₁ :=
    hadj.of_arrs_eq (hk₁.2 _ (by decide)) (hk₁.2 _ (by decide)) (hk₁.2 _ (by decide))
  obtain ⟨s₂, t₂, items, hex₂, ht₂, _, _, hs₂⟩ := gm02SingleComponentProg_exec G lists
    10 11 12 (by decide) (by decide) (by decide) (gm02SlotVertices (n := n) f) a ha s₁ hadj₁
    (by simpa only [hk₁.2 12 (by decide)] using hent)
    ((hk₁.1 _ (by decide)).trans hrn) ((hk₁.1 _ (by decide)).trans hra) hw hn hl₁
  let mid := (s₁.setArr aSrc [0]).writeArr aSrc 0 a.val
  have hmid : Keeps gm02ComponentRegs gm02ComponentArrays s₁ mid :=
    ((Keeps.refl _ _ s₁).setArr (by decide) _).writeArr (by decide) _ _
  have hk₂ : Keeps gm02ComponentRegs gm02ComponentArrays s₁ s₂ :=
    hmid.trans (gm02Component_keeps_of_frame hs₂.frame) (fun _ h => h) (fun _ h => h)
  have hnr₂ : s₂.regs 40 = n := (hk₂.1 _ (by decide)).trans ((hk₁.1 _ (by decide)).trans hrn)
  have hq₂ : s₂.arrs 5 = gm02VertexBits Q :=
    (hk₂.2 _ (by decide)).trans ((hk₁.2 _ (by decide)).trans hq)
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hout⟩ := gm02CountComponent_exec G Q (gm02SlotVertices (n := n) f)
    a ha 5 mid s₂ items hs₂ (by omega) hn hnr₂ hq₂
  have hk₁' : Keeps gm02ComponentRegs gm02ComponentArrays s s₁ :=
    hk₁.mono (by intro r hr; obtain rfl := List.mem_singleton.1 hr; decide)
      (by intro a ha; obtain rfl := List.mem_singleton.1 ha; decide)
  have hk₃' : Keeps gm02ComponentRegs gm02ComponentArrays s₂ s₃ :=
    hk₃.mono
      (by
        intro r hr
        rcases List.mem_cons.1 hr with rfl | hr
        · decide
        · obtain rfl := List.mem_singleton.1 hr
          decide)
      (by simp)

  refine ⟨s₃, t₁ + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃), ?_,
    (hk₁'.trans hk₂ (fun _ h => h) (fun _ h => h)).trans hk₃' (fun _ h => h) (fun _ h => h), hout, ?_⟩
  · have hc : n * (k * 6 + 57) = n * (k * 6 + 19) + 21 * n + n * 17 := by ring
    rw [hc]
    omega
  · let mask : Fin n → ℕ := fun v => if v.val ∈ items then 1 else gm02ComponentLabels (gm02SlotVertices (n := n) f) v
    refine ⟨mask, (hk₃.2 _ (by simp)).trans hs₂.lab, ?_, ?_⟩
    · intro v
      dsimp [mask, gm02ComponentLabels]
      split_ifs <;> omega
    · intro v
      rw [← gm02ComponentSearch_mem_iff ha hs₂]
      by_cases hv : v.val ∈ items <;> by_cases hx : v ∈ gm02SlotVertices (n := n) f <;>
        simp [mask, gm02ComponentLabels, hv, hx]

end GraphMinor.Compute
