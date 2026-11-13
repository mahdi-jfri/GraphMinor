module

public import GraphMinor.GM12.Section3RerouteCarrier
public import GraphMinor.GM12.Section3FiniteSubarcGraph
public import GraphMinor.GM12.Section3SubpathIntervals
import GraphMinor.GM12.Section3FiniteGraphSolid

/-!
# Extending a finite graph without losing the path homotopy

The circle-intersection step used by XII (3.1), page 245, needs a finite
graph inside the original union which retains the relevant homotopy.
Reroute an injective path locally along the old finite graph. The exact
carrier formula expresses the extension by finitely many original
subarcs, each with finite contact with the old graph. The finite-subarc
construction therefore gives the enlarged graph. Its new carrier is
exactly the old graph union the rerouted path, and stays inside the old
graph union the original path.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- An injective path starting on a finite graph can be rerouted up
to fixed-end homotopy so that its union with the graph is again a finite
graph. The enlarged carrier stays in the original graph union path. -/
theorem exists_graph_add_homotopic_arc
    {S : Type*} [TopologicalSpace S] [T2Space S] (hS : IsSurface S)
    {V : Set S} {E : Set (Set S)} (hG : IsGraph V E)
    {a b : S} (p : Path a b) (hp : Function.Injective p) (ha : a ∈ gr V E) :
    ∃ (V' : Set S) (E' : Set (Set S)) (q : Path a b),
      V ⊆ V' ∧ IsGraph V' E' ∧ p.Homotopic q ∧
      gr V' E' = gr V E ∪ range q ∧ gr V' E' ⊆ gr V E ∪ range p := by
  classical
  let F := gr V E
  have hsolid := isSolid_gr_of_isGraph hG
  obtain ⟨n, t, s, u, q, ht0, htlast, hmono, hpq, hcarrier, hpieces⟩ :=
    exists_global_homotopic_reroute_carrier hS hsolid p ha
  let l : Fin n × Bool → unitInterval := fun z =>
    if z.2 then Icc.convexComb (t z.1.castSucc) (t z.1.succ) (u z.1) else t z.1.castSucc
  let r : Fin n × Bool → unitInterval := fun z =>
    if z.2 then t z.1.succ else Icc.convexComb (t z.1.castSucc) (t z.1.succ) (s z.1)
  have hle : ∀ i : Fin n, t i.castSucc ≤ t i.succ := fun i => hmono (Nat.le_succ i.val)
  have hcontact : ∀ z ∈ (Finset.univ : Finset (Fin n × Bool)),
      ((p '' Icc (l z) (r z)) ∩ F).Finite := by
    rintro ⟨i, c⟩ _
    cases c
    · change ((p '' Icc (t i.castSucc) (Icc.convexComb (t i.castSucc) (t i.succ) (s i))) ∩ F).Finite
      rw [← range_left_outer_subpath p (hle i) (s i)]
      exact (finite_singleton _).subset (hpieces i).2.1
    · change ((p '' Icc (Icc.convexComb (t i.castSucc) (t i.succ) (u i)) (t i.succ)) ∩ F).Finite
      rw [← range_right_outer_subpath p (hle i) (u i)]
      exact (finite_singleton _).subset (hpieces i).2.2
  obtain ⟨V', E', hVV', hG', hgr'⟩ := exists_graph_union_finite_subarcs
    ⟨p.continuous, hp⟩ hG rfl Finset.univ l r hcontact
  have hsub : gr V' E' ⊆ F ∪ range p := by
    rw [hgr']
    rintro x (hxF | hxJ)
    · exact Or.inl hxF
    · obtain ⟨z, _, w, _, rfl⟩ := mem_iUnion₂.mp hxJ
      exact Or.inr (mem_range_self w)
  have hU : (⋃ z ∈ (Finset.univ : Finset (Fin n × Bool)), p '' Icc (l z) (r z)) =
      ⋃ i : Fin n, (range ((p.subpath (t i.castSucc) (t i.succ)).subpath 0 (s i)) ∪
        range ((p.subpath (t i.castSucc) (t i.succ)).subpath (u i) 1)) := by
    simp only [Finset.mem_univ, iUnion_true]
    ext x
    constructor
    · intro hx
      obtain ⟨⟨i, c⟩, hi⟩ := mem_iUnion.mp hx
      cases c
      · change x ∈ p '' Icc (t i.castSucc) (Icc.convexComb (t i.castSucc) (t i.succ) (s i)) at hi
        rw [← range_left_outer_subpath p (hle i) (s i)] at hi
        exact mem_iUnion.mpr ⟨i, Or.inl hi⟩
      · change x ∈ p '' Icc (Icc.convexComb (t i.castSucc) (t i.succ) (u i)) (t i.succ) at hi
        rw [← range_right_outer_subpath p (hle i) (u i)] at hi
        exact mem_iUnion.mpr ⟨i, Or.inr hi⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rcases hi with hi | hi
      · refine mem_iUnion.mpr ⟨(i, false), ?_⟩
        change x ∈ p '' Icc (t i.castSucc) (Icc.convexComb (t i.castSucc) (t i.succ) (s i))
        rw [← range_left_outer_subpath p (hle i) (s i)]
        exact hi
      · refine mem_iUnion.mpr ⟨(i, true), ?_⟩
        change x ∈ p '' Icc (Icc.convexComb (t i.castSucc) (t i.succ) (u i)) (t i.succ)
        rw [← range_right_outer_subpath p (hle i) (u i)]
        exact hi
  exact ⟨V', E', q, hVV', hG', hpq,
    hgr'.trans ((congrArg (fun X => F ∪ X) hU).trans hcarrier.symm), hsub⟩

end GraphMinor.GM12
