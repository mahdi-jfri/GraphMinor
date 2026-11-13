module

public import GraphMinor.Compute.Case3StepsCompass
public import GraphMinor.Compute.Algorithm94Aux
public import GraphMinor.Compute.Algorithm33Multigraph

/-!
# Finding the outside components in step (5)

The raw members of (8.6) include the components outside the core, with their
attachments (XIII, Section 8, page 96). A search in the graph restricted to
vertices outside the core finds exactly one such component. The shifted
search keeps the caller's low arrays and registers and writes the component
bitset for the later member construction.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

private theorem case3RestrictedWalk_end_mem {n : ℕ} {G : SimpleGraph (Fin n)}
    {Y : Finset (Fin n)} : ∀ {u v : Fin n}, (restrictGraph G Y).Walk u v → u ∈ Y → v ∈ Y
  | _, _, .nil, hu => hu
  | _, _, .cons h rest, _ => case3RestrictedWalk_end_mem rest h.2.1

/-- A search starting outside the core cannot reach a core vertex. -/
theorem case3ReachSet_outside {x : Alg81Input} {Z : Finset (Fin x.n)}
    {u v : Fin x.n} (hu : u ∉ Z)
    (hv : v ∈ reachSet (restrictGraph x.G (Finset.univ \ Z)) u) : v ∉ Z := by
  obtain ⟨p⟩ := (mem_reachSet _ _ _).mp hv
  have h := case3RestrictedWalk_end_mem p (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu⟩)
  exact (Finset.mem_sdiff.mp h).2

/-- Outside the core, the component constructor is exactly the search's
reachable set. -/
theorem case3CompOutside_eq_reachSet {x : Alg81Input} {Z : Finset (Fin x.n)}
    {u : Fin x.n} (hu : u ∉ Z) :
    compOutside x Z u = reachSet (restrictGraph x.G (Finset.univ \ Z)) u := by
  classical
  ext v
  simp only [compOutside, Finset.mem_filter, mem_reachSet]
  constructor
  · exact And.right
  · intro hv
    exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      case3ReachSet_outside hu ((mem_reachSet _ _ _).mpr hv)⟩, hv⟩

/-- A breadth-first search on the graph outside the core, run in shifted storage. -/
def case3ComponentSearchProg (a_off r_off : ℕ) : Cmd :=
  bfsFromRegInstProg.shift a_off r_off

/-- Execution and time bound for one outside-component search. The adjacency
lists are those of the graph restricted to vertices outside the core. -/
theorem case3ComponentSearchProg_exec {w : ℕ} (x : Alg81Input)
    (Z : Finset (Fin x.n)) (u : Fin x.n) (hu : u ∉ Z)
    (lists : Fin x.n → List ℕ) (a_off r_off : ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) {s : State}
    (hadj : IsAdjList (restrictGraph x.G (Finset.univ \ Z))
      (36 + a_off) (37 + a_off) (38 + a_off) lists s)
    (hent : (s.arrs (38 + a_off)).length < 2 ^ w)
    (hrn : s.regs (1 + r_off) = x.n) (hru : s.regs (14 + r_off) = u.1) :
    ∃ s' t, Exec w (case3ComponentSearchProg a_off r_off) s s' t ∧
      t ≤ 21 + 21 * x.n + 26 * totalAdjEntries lists ∧
      s'.arrs (32 + a_off) = bitSetList (compOutside x Z u) ∧
      (∀ a, a ≠ 31 + a_off → a ≠ 32 + a_off → s'.arrs a = s.arrs a) ∧
      (∀ r < r_off, s'.regs r = s.regs r) := by
  have hadjSub : IsAdjList (restrictGraph x.G (Finset.univ \ Z)) 36 37 38 lists
      (s.unshift a_off r_off) := by
    simpa only [IsAdjList, IsListFamily, IsListAt, State.unshift_arrs] using hadj
  obtain ⟨s_sub, t, hex, ht, hbits, harr, hreg⟩ :=
    bfsFromRegInstProg_exec (restrictGraph x.G (Finset.univ \ Z)) lists u hw hn hadjSub
      hent hrn hru
  refine ⟨s.applyShifted a_off r_off s_sub, t, Exec.shift_from a_off r_off hex, ht, ?_, ?_, ?_⟩
  · rw [State.applyShifted_arrs_add, hbits.arr_eq_bitSetList, ← case3CompOutside_eq_reachSet hu]
  · intro a h31 h32
    by_cases ha : a_off ≤ a
    · have h31' : a - a_off ≠ 31 := by romega
      have h32' : a - a_off ≠ 32 := by romega
      change (if a_off ≤ a then s_sub.arrs (a - a_off) else s.arrs a) = _
      simp only [ha, ↓reduceIte]
      rw [harr (a - a_off) h31' h32', State.unshift_arrs, Nat.sub_add_cancel ha]
    · exact State.applyShifted_arrs_lt a_off r_off s s_sub (by omega)
  · intro r hr
    exact State.applyShifted_regs_lt a_off r_off s s_sub hr

end GraphMinor.Compute
