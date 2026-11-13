module

public import GraphMinor.Surface.SurfaceGraph
public import GraphMinor.HP25.Web
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import GraphMinor.Surface.EdgeLoop
import GraphMinor.Surface.TriPath
import GraphMinor.Surface.Lunes
import Mathlib.Analysis.Convex.PathConnected

/-!
# Paths in the finite segment arrangement

Part IV, Section 7a of the planarity note takes a simple graph path in the
segment arrangement. The vertices are the arrangement points and two
vertices are adjacent when their straight segment is an arrangement edge.
A line inside the arrangement joins reachable vertices: split it at any
interior arrangement vertex and induct on the finite number of vertices
on the line. The arrangement graph has its given plane drawing by straight
segments.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- The graph of a finite segment arrangement in Part IV, Section 7a. -/
@[expose] def segmentArrangementGraph (V : Set ℂ) (E : Set (Set ℂ)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ segment ℝ u.val v.val ∈ E
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [segment_symm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem line_eq_segment {L : Set ℂ} {u v : ℂ}
    (hL : IsLineWithEnds L u v) (hstraight : ∃ a b : ℂ, L = segment ℝ a b) :
    L = segment ℝ u v := by
  obtain ⟨a, b, heq⟩ := hstraight
  have hconv : Convex ℝ L := heq ▸ convex_segment a b
  exact (hL.eq_of_subset ((convex_segment u v).isPreconnected)
    (hconv.segment_subset hL.left_mem hL.right_mem)
    (left_mem_segment _ _ _) (right_mem_segment _ _ _)).symm

private theorem segment_graph_avoid {V : Set ℂ} {E : Set (Set ℂ)} (h : IsGraph V E)
    {u v w : ℂ} (hu : u ∈ V) (hv : v ∈ V) (hw : w ∈ V)
    (hne : u ≠ v) (he : segment ℝ u v ∈ E) (hm : w ∈ segment ℝ u v) :
    w = u ∨ w = v := by
  obtain ⟨a, b, _, _, hi⟩ := h.edge _ he
  have huab : u = a ∨ u = b :=
    show u ∈ ({a, b} : Set ℂ) from hi ▸ ⟨left_mem_segment _ _ _, hu⟩
  have hvab : v = a ∨ v = b :=
    show v ∈ ({a, b} : Set ℂ) from hi ▸ ⟨right_mem_segment _ _ _, hv⟩
  have hwab : w = a ∨ w = b := show w ∈ ({a, b} : Set ℂ) from hi ▸ ⟨hm, hw⟩
  rcases huab with rfl | rfl <;> rcases hvab with rfl | rfl
  · exact (hne rfl).elim
  · exact hwab
  · exact hwab.symm
  · exact (hne rfl).elim

/-- The straight plane embedding of the segment arrangement graph used in
Part IV, Section 7a. -/
@[expose] def segmentArrangementEmbedding {V : Set ℂ} {E : Set (Set ℂ)}
    (h : IsGraph V E) : HP25.PlaneEmbedding (segmentArrangementGraph V E) univ where
  pt := Subtype.val
  line u v := segment ℝ u.val v.val
  finite := by
    let : Finite V := h.fin.to_subtype
    exact Set.toFinite _
  injOn := Subtype.val_injective.injOn
  line_comm _ _ := segment_symm _ _ _
  isLine u _ v _ huv := by
    exact isLineWithEnds_segment (fun he => huv.1 (Subtype.ext he))
  avoid u _ v _ huv w _ hw := by
    rcases segment_graph_avoid h u.property v.property w.property
      (fun he => huv.1 (Subtype.ext he)) huv.2 hw with he | he
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr (Subtype.ext he)
  inter u _ v _ u' _ v' _ huv huv' hne x hx := by
    have he : segment ℝ u.val v.val ≠ segment ℝ u'.val v'.val := by
      intro heq
      have hu' := segment_graph_avoid h u.property v.property u'.property
        (fun he => huv.1 (Subtype.ext he)) huv.2
        (heq.symm ▸ left_mem_segment ℝ u'.val v'.val)
      have hv' := segment_graph_avoid h u.property v.property v'.property
        (fun he => huv.1 (Subtype.ext he)) huv.2
        (heq.symm ▸ right_mem_segment ℝ u'.val v'.val)
      apply hne
      apply (Sym2.mem_and_mem_iff huv'.1).mp
      exact ⟨Sym2.mem_iff.mpr (hu'.imp Subtype.ext Subtype.ext),
        Sym2.mem_iff.mpr (hv'.imp Subtype.ext Subtype.ext)⟩
    have hxV := h.disj _ huv.2 _ huv'.2 he hx
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    constructor
    · rcases segment_graph_avoid h u.property v.property hxV
        (fun he => huv.1 (Subtype.ext he)) huv.2 hx.1 with he | he
      · exact Or.inl (Subtype.ext he)
      · exact Or.inr (Subtype.ext he)
    · rcases segment_graph_avoid h u'.property v'.property hxV
        (fun he => huv'.1 (Subtype.ext he)) huv'.2 hx.2 with he | he
      · exact Or.inl (Subtype.ext he)
      · exact Or.inr (Subtype.ext he)

/-- The reachability step of Part IV, Section 7a: the ends of a line contained
in a finite straight segment arrangement are connected by a graph walk. -/
theorem segment_arrangement_reachable {V : Set ℂ} {E : Set (Set ℂ)} (h : IsGraph V E)
    (hstraight : ∀ e ∈ E, ∃ a b : ℂ, e = segment ℝ a b)
    {L : Set ℂ} {u v : ℂ} (hL : IsLineWithEnds L u v) (hu : u ∈ V) (hv : v ∈ V)
    (hsub : L ⊆ gr V E) :
    (segmentArrangementGraph V E).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  classical
  suffices ∀ n : ℕ, ∀ {L : Set ℂ} {u v : ℂ} (hu : u ∈ V) (hv : v ∈ V),
      (L ∩ V).ncard = n → IsLineWithEnds L u v → L ⊆ gr V E →
      (segmentArrangementGraph V E).Reachable ⟨u, hu⟩ ⟨v, hv⟩ by
    exact this _ hu hv rfl hL hsub
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L u v hu hv hn hL hsub
    by_cases huv : u = v
    · subst v
      exact SimpleGraph.Reachable.refl _
    by_cases hbase : (L ∩ V) \ {u, v} = ∅
    · have hi : L ∩ V = {u, v} := by
        apply (sdiff_eq_empty.mp hbase).antisymm
        rintro x (rfl | rfl)
        · exact ⟨hL.left_mem, hu⟩
        · exact ⟨hL.right_mem, hv⟩
      have hLE := h.line_mem hL huv hsub hi
      have heq := line_eq_segment hL (hstraight L hLE)
      exact SimpleGraph.Adj.reachable ⟨fun he => huv (congrArg Subtype.val he), heq ▸ hLE⟩
    obtain ⟨w, hw⟩ := nonempty_iff_ne_empty.mpr hbase
    have hwu : w ≠ u := fun he => hw.2 (Or.inl he)
    have hwv : w ≠ v := fun he => hw.2 (Or.inr he)
    obtain ⟨P, Q, hP, hQ, hPQ, hmeet⟩ := hL.split hw.1.1 hwu hwv
    have hPL : P ⊆ L := hPQ ▸ subset_union_left
    have hQL : Q ⊆ L := hPQ ▸ subset_union_right
    have hvP : v ∉ P := fun hm => hwv
      (mem_singleton_iff.mp (hmeet ▸ ⟨hm, hQ.right_mem⟩)).symm
    have huQ : u ∉ Q := fun hm => hwu
      (mem_singleton_iff.mp (hmeet ▸ ⟨hP.left_mem, hm⟩)).symm
    have hfin : (L ∩ V).Finite := h.fin.subset inter_subset_right
    have hltP : (P ∩ V).ncard < n := by
      rw [← hn]
      apply ncard_lt_ncard _ hfin
      refine ⟨inter_subset_inter_left V hPL, ?_⟩
      intro he
      exact hvP (he ⟨hL.right_mem, hv⟩).1
    have hltQ : (Q ∩ V).ncard < n := by
      rw [← hn]
      apply ncard_lt_ncard _ hfin
      refine ⟨inter_subset_inter_left V hQL, ?_⟩
      intro he
      exact huQ (he ⟨hL.left_mem, hu⟩).1
    exact (ih _ hltP hu hw.1.2 rfl hP (hPL.trans hsub)).trans
      (ih _ hltQ hw.1.2 hv rfl hQ (hQL.trans hsub))

end GraphMinor.LRPlanarity
