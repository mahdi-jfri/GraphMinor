module

public import GraphMinor.GM01.Section4RootSeparation
public import GraphMinor.GM01.OrderedBlockWindows
import GraphMinor.GM01.SeparatorPathTransfer
import GraphMinor.GM01.CombPrefixes

/-!
# The order of the sampled separators

Graph Minors I, (4.5), pages 56–57, samples the small minimal separators
at multiples of the window length. Their attachment windows are
disjoint. A vertex of one sampled separator has a path inside its
window to a block. That path avoids every other sampled separator, so
(4.4) decides whether it is separated from the root. The equal-index
case holds because the vertex itself lies in the cut.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.5), pages 56–57:
"For $1 \le i, i' \le T$ and for every $y \in Y_{i'}$, $Y_i$ separates $y$ and $\rho(G)$ if and only if $i \le i'$."

Indices start at zero. The functions `left` and `right` record the
boundary indices of the sampled windows. The minimal separators are
those of (4.3) and (4.4). -/
theorem theorem_4_5_proof {α : Type u} {β : Type v} {γ δ L n : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G)
    {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    {P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb (γ - 1) L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val
      (c (rootedPathComb (γ - 1) L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root})
    {T ν : ℕ} (hν : 3 ≤ ν) (left right : Fin T → Fin n)
    (hleft : ∀ i, (left i).val = ν * i.val)
    (hright : ∀ i, (right i).val + 1 = ν * (i.val + 1))
    (Y : Fin T → Set α)
    (hY : ∀ i, IsMinimalGraphSeparator G.graph (Y i)
      (⋃ k : Fin n, ⋃ (_ : k ≤ left i), combBlock hL (subgraphUnion G.graph N R) c k)
      (⋃ k : Fin n, ⋃ (_ : right i ≤ k), combBlock hL (subgraphUnion G.graph N R) c k))
    (i i' : Fin T) {y : α} (hy : y ∈ Y i') :
    GraphSeparates G.graph (Y i) {y} {G.root.val} ↔ i ≤ i' := by
  classical
  let H := subgraphUnion G.graph N R
  let S := fun k : Fin n ↦ combBlock hL H c k
  have hwindow : ∀ i, (left i).val + ν = (right i).val + 1 := by
    intro i
    rw [hleft, hright, Nat.mul_add, Nat.mul_one]
  have hlr : ∀ i, left i ≤ right i := by
    intro i
    have hw := hwindow i
    change (left i).val ≤ (right i).val
    omega
  have hgap : ∀ i i', i < i' → right i < left i' := by
    intro i i' hii'
    have hm := Nat.mul_le_mul_left ν (Nat.succ_le_of_lt hii')
    change ν * (i.val + 1) ≤ ν * i'.val at hm
    have hr := hright i
    have hl := hleft i'
    change (right i).val < (left i').val
    omega
  have hlocal : ∀ i, Y i ⊆ blockAttachmentWindow G.graph S (left i) (right i) := by
    intro i
    exact theorem_4_3_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
      ν hν (left i) (right i) (hwindow i) (hY i)
  have hcentres : ∀ v, c v ∈ V(N) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  have hPN : ∀ e, P e ≤ N := by
    intro e
    obtain ⟨_, _, _, _, hPath, _⟩ := hPaths e
    exact hPath.le
  have hRanges : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  have hpart := combBlock_partition hL (Nat.zero_lt_of_lt (right i).isLt) hN hR.le hc
    hcentres hPN hE hRanges (fun e f hne ↦ (hInter e f hne).1) hmeetR
  have hSG : ∀ k, S k ⊆ V(G.graph) := fun k ↦
    (combBlock_subset_graph hL H c k).trans (subgraphUnion_le hN hR.le).vertexSet_mono
  have hsep := fun k ↦ block_separates_strict hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR k
  by_cases heq : i = i'
  · subst i'
    exact ⟨fun _ ↦ le_rfl, fun _ ↦ graphSeparates_singleton_of_mem hy⟩
  have hdisWindows : Disjoint
      (blockAttachmentWindow G.graph S (left i') (right i'))
      (blockAttachmentWindow G.graph S (left i) (right i)) := by
    rcases lt_or_gt_of_ne heq with hii' | hi'i
    · exact (disjoint_blockAttachmentWindows S hSG hpart.1 hsep
        (left i) (right i) (left i') (right i') (hlr i) (hlr i') (hgap i i' hii')).symm
    · exact disjoint_blockAttachmentWindows S hSG hpart.1 hsep
        (left i') (right i') (left i) (right i) (hlr i') (hlr i) (hgap i' i hi'i)
  obtain ⟨k, hlk, hkr, s, hs, Q, hQ, hQWindow⟩ :=
    exists_path_in_blockAttachmentWindow hSG (hlr i') (hlocal i' hy)
  have hAvoid : Disjoint V(Q) (Y i) := hdisWindows.mono hQWindow (hlocal i)
  have htransfer := graphSeparates_singleton_iff_of_path (root := G.root.val) hQ hAvoid
  have hrootsep := theorem_4_4_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
    ν hν (left i) (right i) (hwindow i) (hY i) k hs
  rcases lt_or_gt_of_ne heq with hii' | hi'i
  · have hrightk : right i ≤ k := (hgap i i' hii').le.trans hlk
    exact ⟨fun _ ↦ hii'.le, fun _ ↦ htransfer.mpr (hrootsep.1 hrightk)⟩
  · have hki : k.val + ν ≤ (right i).val := by
      have hm := Nat.mul_le_mul_left ν (Nat.succ_le_of_lt hi'i)
      change ν * (i'.val + 1) ≤ ν * i.val at hm
      have hr := hright i
      have hr' := hright i'
      have hk : k.val ≤ (right i').val := hkr
      rw [Nat.mul_add, Nat.mul_one] at hr
      omega
    exact ⟨fun h ↦ False.elim (hrootsep.2 hki (htransfer.mp h)),
      fun h ↦ False.elim ((not_le_of_gt hi'i) h)⟩

end GraphMinor.GM01
