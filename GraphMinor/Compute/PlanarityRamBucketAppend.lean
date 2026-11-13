module

public import GraphMinor.Compute.PlanarityRamBucketChain

/-!
# Appending an edge through a stored tail

The outgoing pass of lines 234–241 of `docs/planarity/planarity_linear.py` changes the old last
edge's next pointer. The proof here follows the owned chain to justify that one
write. It does not traverse the chain in the program. The proof's list
induction is only an argument about the representation.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

/-- Append uses an explicitly cleared new link and one old-tail write. -/
def appendLinkState (s : State) (links last i : ℕ) : State :=
  (s.writeArr links i 0).writeArr links last (i + 1)

/-- Appending a fresh identifier to a nonempty owned chain takes two
pointer writes, irrespective of the chain length. -/
theorem EdgeChain.append {s : State} {links p last i : ℕ} {xs : List ℕ}
    (h : EdgeChain s links p xs) (hnd : xs.Nodup) (hlast : xs.getLast? = some last)
    (hfresh : i ∉ xs) (hslot : i < (s.arrs links).length) :
    EdgeChain (appendLinkState s links last i) links p (xs ++ [i]) := by
  induction h with
  | nil => simp at hlast
  | @cons j q rest hn ht ih =>
    have hji : i ≠ j := by intro he; exact hfresh (by simp [he])
    have hrest := List.nodup_cons.mp hnd
    cases rest with
    | nil =>
      have hlastj : last = j := by simpa using hlast.symm
      subst last
      have hq : q = 0 := EdgeChain.nil_iff.mp ht
      have hjbound : j < (s.arrs links).length := (List.getElem?_eq_some_iff.mp hn).1
      refine .cons ?_ (.cons ?_ .nil)
      · simp [appendLinkState, hjbound]
      · simp only [appendLinkState, State.writeArr_arrs_self, List.getElem?_set,
          ite_eq_right (Ne.symm hji), hslot, ↓reduceIte]
    | cons k ks =>
      have hlastRest : (k :: ks).getLast? = some last := by simpa using hlast
      have hlastMem : last ∈ k :: ks := List.mem_of_getLast? hlastRest
      have hjlast : last ≠ j := by intro he; exact hrest.1 (he ▸ hlastMem)
      have htail := ih hrest.2 hlastRest (fun hm => hfresh (by simp [hm]))
      refine .cons ?_ htail
      simpa only [appendLinkState, State.writeArr_arrs_self, List.getElem?_set,
        ite_eq_right hjlast, ite_eq_right hji] using hn

end GraphMinor.Compute.PlanarityRam
