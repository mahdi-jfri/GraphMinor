module

public import GraphMinor.GM08.Section11Ring
import GraphMinor.GM11.Walks
import GraphMinor.GM22.Section3Disc
import GraphMinor.GM07.Section3

/-!
# Graph Minors VIII, (11.1)

Let `Γ*` be a truncation of `Γ` induced by the foundation `F_1, …, F_t`, and let `(T, Y)` be a
tree-decomposition of `Γ*` of width at most `w`. The paper applies the strengthened III (3.8) "to
each $G_i$ in turn". We remove the vertices inside `F_1`, then those inside `F_2`, and so on. At
step `k` the graph is `Γ*` induced on the vertices not inside `F_1, …, F_k`. The step
`exists_ring_decomposition` keeps the width, keeps the old bags on the vertices that stay, and
puts the vertices on `F_k` in one bag. After `t` steps we have a tree-decomposition of the graph
on the vertices of `Γ*` not inside any `F_i`, in which each `V(Γ) ∩ F_i` lies in one bag
(`exists_truncation_decomposition`).

The nodes of the painting `(U', N')` are these vertices. Its cells are the discs `Σ_i` bounded
by `F_i`, whose nodes are the vertices on `F_i`, and the thickened edges `D(e)`, whose nodes are
the ends of `e`. So cutting the bags down to `N'` gives the hypertree that shows that the
painting has tree-width at most `w` (`theorem_11_1`).
-/

public section

namespace GraphMinor
namespace GM08

open Set Graph GM03 GM06 GM09 Surface

universe u w u' v'

variable {S : Type u} [TopologicalSpace S] {ι : Type w}

/-- A closed disc is Hausdorff. -/
theorem t2Space_of_univ (hS : IsClosedDisc (univ : Set S)) : T2Space S := by
  obtain ⟨e⟩ := hS
  exact (GM07.isSurface_of_homeo (e.trans (Homeomorph.Set.univ S))
    GM22.isSurface_closedUnitDisc).2.1

/-- The vertices of `Γ*` that are not inside any of `F_j` for `j < k`. -/
def truncStage (Dstar : Drawing S) {t : ℕ} (F : Fin t → Set S) (k : ℕ) : Set S :=
  {x ∈ Dstar.V | ∀ j : Fin t, j.1 < k → ¬ InsideOArc univ (F j) x}

/-- The proof of Graph Minors VIII, (11.1) (page 273), applied to each `F_i` in turn: a
tree-decomposition of a truncation `Γ*` of width at most `w` gives one of the graph of `Γ*`
on the vertices not inside any `F_i`, of width at most `w`, in which each `V(Γ) ∩ F_i` lies in a
single bag. -/
theorem exists_truncation_decomposition (hS : IsClosedDisc (univ : Set S)) {Γ Dstar : Drawing S}
    {t : ℕ} {F : Fin t → Set S} (hD : IsTruncationInducedBy Γ univ F Dstar) [Fintype ι]
    {T : SimpleGraph ι} {Y : ι → Set S} (hTD : IsTreeDecomposition Dstar.toGraph T Y) {w : ℕ}
    (hYw : TreeDecompHasWidthLE Y w) :
    ∃ X : ι → Set S, IsTreeDecomposition (Dstar.toGraph.induce (truncStage Dstar F t)) T X ∧
      TreeDecompHasWidthLE X w ∧
      ∀ j : Fin t, ∃ t₀, Γ.V ∩ F j ∩ truncStage Dstar F t ⊆ X t₀ := by
  classical
  have : T2Space S := t2Space_of_univ hS
  obtain ⟨hFound, -, Γs, hsl, hDV, hDE⟩ := hD
  obtain ⟨-, -, -, -, -, hdisj, -, -⟩ := hFound
  choose _ _ _ _ sd hsdV hsdE using hsl
  -- The sleeves are subdrawings of `Γ*`.
  have hsubV : ∀ i, (Γs i).V ⊆ Dstar.V := fun i x hx => by
    rw [hDV]; exact Or.inr (mem_iUnion.mpr ⟨i, hx⟩)
  have hsubE : ∀ i, (Γs i).E ⊆ Dstar.E := fun i x hx => by
    rw [hDE]; exact Or.inr (mem_iUnion.mpr ⟨i, hx⟩)
  have hcirc : ∀ i j, ((sd i).circuitDraw j).IsSubdrawing Dstar := fun i j =>
    ⟨fun x hx => hsubV i (by rw [hsdV i]; exact Or.inl (mem_iUnion.mpr ⟨j, hx⟩)),
      fun e he => hsubE i (by rw [hsdE i]; exact Or.inl (mem_iUnion.mpr ⟨j, he⟩))⟩
  have hspoke : ∀ i j, ((sd i).spoke j).IsSubdrawing Dstar := fun i j =>
    ⟨fun x hx => hsubV i (by rw [hsdV i]; exact Or.inr (mem_iUnion.mpr ⟨j, hx⟩)),
      fun e he => hsubE i (by rw [hsdE i]; exact Or.inr (mem_iUnion.mpr ⟨j, he⟩))⟩
  have hfin : ∀ k, (truncStage Dstar F k).Finite := fun k =>
    Dstar.finite_V.subset fun x hx => hx.1
  -- The induction over the rings `F_0, …, F_{t-1}`.
  have key : ∀ k, k ≤ t → ∃ X : ι → Set S,
      IsTreeDecomposition (Dstar.toGraph.induce (truncStage Dstar F k)) T X ∧
      TreeDecompHasWidthLE X w ∧
      ∀ j : Fin t, j.1 < k → ∃ t₀, Γ.V ∩ F j ∩ truncStage Dstar F k ⊆ X t₀ := by
    intro k
    induction k with
    | zero =>
      intro _
      have hle : Dstar.toGraph.induce (truncStage Dstar F 0) ≤ Dstar.toGraph :=
        induce_le fun x hx => hx.1
      refine ⟨_, IsTreeDecomposition.restrict hTD hle, fun s => ?_, fun j hj => absurd hj (by omega)⟩
      exact (ncard_le_ncard inter_subset_left
        (Dstar.finite_V.subset (hTD.bag_subset s))).trans (hYw s)
    | succ k ih =>
      intro hk
      obtain ⟨X, hX, hXw, hXF⟩ := ih (by omega)
      let kk : Fin t := ⟨k, by omega⟩
      have hstage : truncStage Dstar F (k + 1) =
          {x ∈ truncStage Dstar F k | ¬ InsideOArc univ (F kk) x} := by
        ext x
        simp only [truncStage, mem_ofPred_eq]
        constructor
        · rintro ⟨hx, hj⟩
          exact ⟨⟨hx, fun j hjk => hj j (by omega)⟩, hj kk (by simp [kk])⟩
        · rintro ⟨⟨hx, hj⟩, hkk⟩
          refine ⟨hx, fun j hjk => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with h | h
          · exact hj j h
          · have : j = kk := Fin.ext h
            exact this ▸ hkk
      -- The sleeve for `F_k` has no vertex inside an earlier ring.
      have hsW : ∀ x ∈ (⋃ j, ((sd kk).circuitDraw j).V) ∪ (⋃ i, ((sd kk).spoke i).V),
          x ∈ truncStage Dstar F k := by
        intro x hx
        refine ⟨hsubV kk (by rw [hsdV kk]; exact hx), fun j hj => ?_⟩
        have hne : kk ≠ j := fun h => by rw [← h] at hj; simp [kk] at hj
        exact SleeveData.not_insideOArc hS (sd kk) (hdisj hne) hx
      obtain ⟨X', hX', hX'w, hXX', t₀, ht₀⟩ := exists_ring_decomposition hS (sd kk) (hcirc kk)
        (hspoke kk) (fun x hx => hx.1) hsW hX
      rw [← hstage] at hX' hXX'
      refine ⟨X', hX', hX'w w hXw, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · obtain ⟨s, hs⟩ := hXF j h
        refine ⟨s, fun x hx => hXX' s ⟨hs ⟨hx.1, ?_⟩, hx.2⟩⟩
        rw [hstage] at hx
        exact hx.2.1
      · have : j = kk := Fin.ext h
        subst this
        exact ⟨t₀, fun x hx => ht₀ hx.1⟩
  exact (key t le_rfl).imp fun X ⟨hX, hXw, hXF⟩ => ⟨hX, hXw, fun j => hXF j j.2⟩

/-- Graph Minors VIII, (11.1) (page 272):
"(11.1) *With notation as above, the tree-width of* $(U', V')$ *is no greater than the tree-width of any corresponding truncation of* $\Gamma$."
Here $(U', V')$ is the painting $(U', N')$ of the portrait `P` derived via `gd` and `F`, and the
truncation is one induced by the same foundation `F`. The proof is on page 273. The paper applies
the strengthened III (3.8), which is about a cylinder, while a truncation has a sleeve in its place.
As the paper does, we contract each sleeve onto the cylinder (`exists_ring_decomposition`). -/
theorem theorem_11_1_proof {α : Type u'} {β : Type v'} {k : ℕ} (hS : IsClosedDisc (univ : Set S))
    {X : RootedGraph α β} {gd : Surface.GraftDrawing X.G X.toGraft.T S} {t : ℕ}
    {F : Fin t → Set S} {P : QPortrait (QKElem α β S ((k : ℤ) - 1)) S}
    (hP : IsDerivedPortraitVia X gd F P) {Dstar : Drawing S}
    (hD : IsTruncationInducedBy gd.drawing univ F Dstar) {w : ℕ}
    (hw : DrawingTreeWidthLE Dstar w) : PortraitTreeWidthLE P w := by
  classical
  obtain ⟨ι, hι, T, Y, hY, hYw, hYe⟩ := hw
  -- The hypertree of `Γ*` is a tree-decomposition of its graph.
  have hTD : IsTreeDecomposition Dstar.toGraph T Y :=
    ⟨hY.isTree, fun s => hY.iUnion_eq ▸ subset_iUnion Y s, hY.iUnion_eq, hYe,
      fun _ _ _ h => hY.inter_subset h⟩
  obtain ⟨Z, hZ, hZw, hZF⟩ := exists_truncation_decomposition hS hD hTD hYw
  obtain ⟨-, hDsub, Γs, -, hDV, hDE⟩ := hD
  obtain ⟨-, -, -, -, -, -, α_ring, G_sub, hG_sub, D_edge, -, hedge, hN, -, hcells, hdisc,
    hedge'⟩ := hP
  set Γ := gd.drawing
  set W := truncStage Dstar F t
  have hne : Nonempty ι := hY.isTree.connected.nonempty
  -- The nodes `N'` are vertices of `Γ*` not inside any ring.
  have hNW : P.painting.N ⊆ W := by
    rw [hN]
    intro x hx
    refine ⟨?_, fun j _ => hx.2 j⟩
    rw [hDV]
    exact Or.inl hx
  have hZfin : ∀ s, (Z s).Finite := fun s =>
    (Dstar.finite_V.subset fun x hx => hx.1).subset (hZ.bag_subset s)
  -- Two vertices, both in one bag when both stay, lie in one bag as far as they stay.
  have hpair : ∀ a b : S, (a ∈ W → b ∈ W → ∃ s, a ∈ Z s ∧ b ∈ Z s) →
      ∃ s, ∀ x ∈ W, x = a ∨ x = b → x ∈ Z s := by
    intro a b hab
    have hbag : ∀ y ∈ W, ∃ s, y ∈ Z s := fun y hy => by
      have : y ∈ ⋃ s, Z s := hZ.iUnion_bags ▸ hy
      exact mem_iUnion.mp this
    by_cases ha : a ∈ W <;> by_cases hb : b ∈ W
    · obtain ⟨s, has, hbs⟩ := hab ha hb
      exact ⟨s, fun x _ hx => hx.elim (fun h => h ▸ has) (fun h => h ▸ hbs)⟩
    · obtain ⟨s, hs⟩ := hbag a ha
      exact ⟨s, fun x hxW hx => hx.elim (fun h => h ▸ hs) (fun h => absurd (h ▸ hxW) hb)⟩
    · obtain ⟨s, hs⟩ := hbag b hb
      exact ⟨s, fun x hxW hx => hx.elim (fun h => absurd (h ▸ hxW) ha) (fun h => h ▸ hs)⟩
    · obtain ⟨s⟩ := hne
      exact ⟨s, fun x hxW hx =>
        hx.elim (fun h => absurd (h ▸ hxW) ha) (fun h => absurd (h ▸ hxW) hb)⟩
  refine ⟨ι, hι, T, fun s => Z s ∩ P.painting.N, ⟨P.painting.finite_N, hY.isTree, ?_, ?_⟩,
    fun s => (ncard_le_ncard inter_subset_left (hZfin s)).trans (hZw s), ?_⟩
  · rw [← iUnion_inter, hZ.iUnion_bags]
    exact inter_eq_right.mpr hNW
  · intro s s' s'' h x hx
    exact ⟨hZ.inter_subset_on_path h ⟨hx.1.1, hx.2.1⟩, hx.1.2⟩
  intro c hc
  rw [hcells] at hc
  rcases hc with ⟨i, rfl⟩ | ⟨e, he, rfl⟩
  · -- A disc `Σ_i`: its nodes are the vertices on `F_i`.
    obtain ⟨s, hs⟩ := hZF i
    refine ⟨s, fun x hx => ?_⟩
    rw [(hdisc i).1] at hx
    have hxN : x ∈ P.painting.N := by
      by_contra h
      exact hx.2 ⟨hx.1, by rw [hN] at h; exact h⟩
    have hxN' := hxN
    rw [hN] at hxN'
    have hxF : x ∈ F i := by
      rcases hx.1 with h | h
      · exact h
      · exact absurd h (hxN'.2 i)
    exact ⟨hs ⟨⟨hxN'.1, hxF⟩, hNW hxN⟩, hxN⟩
  · -- A thickened edge `D(e)`: its nodes are the ends of `e`.
    obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet (G := Γ.toGraph) he.1
    have heD : e ∈ Dstar.E := by rw [hDE]; exact Or.inl he
    have hlink : Dstar.toGraph.IsLink e a b := (hDsub.isLink_iff heD).mpr hab
    obtain ⟨s, hs⟩ := hpair a b fun ha hb => hZ.edge_in_bag ⟨hlink, ha, hb⟩
    refine ⟨s, fun x hx => ?_⟩
    rw [(hedge' e he).1] at hx
    have hxN : x ∈ P.painting.N := by
      by_contra h
      exact hx.2 ⟨hx.1, by rw [hN] at h; exact h⟩
    have hxV : x ∈ Γ.V := by rw [hN] at hxN; exact hxN.1
    have hxe : x ∈ closure e := by
      rw [← (hedge e he).2.2.1]
      exact ⟨hx.1, Γ.V_subset_U hxV⟩
    have hxab : x ∈ ({a, b} : Set S) := by
      rw [← hab.2.2.2]
      exact ⟨hxe, hxV⟩
    exact ⟨hs x (hNW hxN) hxab, hxN⟩

end GM08
end GraphMinor
