module

public import GraphMinor.GM01.PathWidth
public import GraphMinor.Minor.Model
import GraphMinor.GM01.SaturatedBags
import GraphMinor.GM01.ConnectedBagIntervals
import GraphMinor.GM01.AttachmentOrder

/-!
# Three large branches force a larger bag

To prove that tree path-width is unbounded, as used on page 40 of
Graph Minors I, take three disjoint branches. Each fills a bag in
a decomposition of the proposed width. Order these three bags.
A connected subgraph joining the first and last branches while
avoiding the middle branch must meet the middle bag. That vertex
cannot fit, since the middle branch already fills the bag.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- Three disjoint branches requiring width at least `k`, with a
connected bypass around each branch, preclude width `k`. This is
the inductive lower-bound argument for observation (b) on page 40
of Graph Minors I. -/
theorem not_hasPathWidthLE_of_three_branches {α β : Type*}
    {G : Graph α β} {k : ℕ} (hk : 0 < k)
    (K C : Fin 3 → Graph α β) (hKG : ∀ r, K r ≤ G)
    (hDis : Pairwise fun r s ↦ Disjoint V(K r) V(K s))
    (hNo : ∀ r, ¬ HasPathWidthLE (K r) (k - 1))
    (hCG : ∀ r, C r ≤ G) (hCC : ∀ r, GraphConnected (C r))
    (hBypass : ∀ r s, s ≠ r → V(K s) ⊆ V(C r))
    (hAvoid : ∀ r, Disjoint V(C r) V(K r)) : ¬ HasPathWidthLE G k := by
  classical
  rintro ⟨D, hD⟩
  have hs : ∀ r, ∃ i, (D.bag i).Nonempty ∧ D.bag i ⊆ V(K r) :=
    fun r ↦ D.exists_saturated_bag hD hk (hKG r) (hNo r)
  choose t htNon htSub using hs
  have ht : Function.Injective t := by
    intro r s heq
    by_contra hrs
    obtain ⟨x, hx⟩ := htNon r
    have hxs : x ∈ D.bag (t s) := heq ▸ hx
    exact Set.disjoint_left.mp (hDis hrs) (htSub r hx) (htSub s hxs)
  obtain ⟨e, hOrder⟩ := exists_strictMono_attachment_reindexing t ht
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have h21 : e 2 ≠ e 1 := e.injective.ne (by decide)
  have hfirst : (V(C (e 1)) ∩ D.bag (t (e 0))).Nonempty := by
    obtain ⟨x, hx⟩ := htNon (e 0)
    exact ⟨x, hBypass (e 1) (e 0) h01 (htSub (e 0) hx), hx⟩
  have hlast : (V(C (e 1)) ∩ D.bag (t (e 2))).Nonempty := by
    obtain ⟨x, hx⟩ := htNon (e 2)
    exact ⟨x, hBypass (e 1) (e 2) h21 (htSub (e 2) hx), hx⟩
  obtain ⟨x, hxC, hxBag⟩ := D.connected_meets_middle (hCG (e 1)) (hCC (e 1))
    (le_of_lt (hOrder (by decide : (0 : Fin 3) < 1)))
    (le_of_lt (hOrder (by decide : (1 : Fin 3) < 2))) hfirst hlast
  exact Set.disjoint_left.mp (hAvoid (e 1)) hxC (htSub (e 1) hxBag)

end GraphMinor.GM01
