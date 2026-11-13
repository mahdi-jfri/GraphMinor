module

public import GraphMinor.HP25.Web
public import GraphMinor.Surface.ArcTools

/-!
# Assembling the ten arcs of the exterior complete graph

Part IV, Section 7c of the planarity note has five distinct points and ten
arcs, one for each pair. If every arc avoids the other points and different
arcs meet only at those five points, these data form a plane embedding.
The finite indexing below lists the ten pairs explicitly.
-/

@[expose] public section
namespace GraphMinor.LRPlanarity

open Set

/-- The ten pairs, with the center first and the four boundary ports after it,
used to assemble the graph in Part IV, Section 7c. -/
def completeFiveEnds : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (2, 3), (3, 4),
    (1, 4), (1, 3), (2, 4)]

private def edgeIndex : Fin 5 → Fin 5 → Fin 10 :=
  ![![0, 0, 1, 2, 3], ![0, 0, 4, 8, 7], ![1, 4, 0, 5, 9],
    ![2, 8, 5, 0, 6], ![3, 7, 9, 6, 0]]

private theorem edgeIndex_comm : ∀ u v, edgeIndex u v = edgeIndex v u := by decide

private theorem ends_edgeIndex : ∀ u v, u ≠ v →
    s((completeFiveEnds (edgeIndex u v)).1, (completeFiveEnds (edgeIndex u v)).2) =
      s(u, v) := by decide

/-- The finite assembly step of Part IV, Section 7c. The hypotheses describe
five distinct points and the ten arcs between them, with all meetings confined
to those points and no arc passing through a third point. -/
theorem planeEmbedding_of_complete_five_arcs (pt : Fin 5 → ℂ)
    (arc : Fin 10 → Set ℂ) (hinj : Function.Injective pt)
    (hline : ∀ i, Surface.IsLineWithEnds (arc i)
      (pt (completeFiveEnds i).1) (pt (completeFiveEnds i).2))
    (havoid : ∀ i w, pt w ∈ arc i →
      w = (completeFiveEnds i).1 ∨ w = (completeFiveEnds i).2)
    (hinter : ∀ i j, i ≠ j → arc i ∩ arc j ⊆ range pt) :
    Nonempty (HP25.PlaneEmbedding (⊤ : SimpleGraph (Fin 5)) univ) := by
  have avoid : ∀ u v, u ≠ v → ∀ w, pt w ∈ arc (edgeIndex u v) → w = u ∨ w = v := by
    intro u v huv w hw
    have he := ends_edgeIndex u v huv
    have hm : w ∈ s((completeFiveEnds (edgeIndex u v)).1,
        (completeFiveEnds (edgeIndex u v)).2) := Sym2.mem_iff.mpr (havoid _ _ hw)
    rw [he] at hm
    exact Sym2.mem_iff.mp hm
  refine ⟨{
    pt := pt
    line := fun u v => arc (edgeIndex u v)
    finite := Set.toFinite _
    injOn := hinj.injOn
    line_comm := fun u v => congrArg arc (edgeIndex_comm u v)
    isLine := ?_
    inter := ?_
    avoid := ?_
  }⟩
  · intro u _ v _ huv
    have huv' : u ≠ v := SimpleGraph.top_adj u v |>.mp huv
    rcases Sym2.eq_iff.mp (ends_edgeIndex u v huv') with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · simpa only [h₁, h₂] using hline (edgeIndex u v)
    · simpa only [h₁, h₂] using (hline (edgeIndex u v)).symm
  · intro u _ v _ u' _ v' _ huv huv' hne x hx
    have hn : edgeIndex u v ≠ edgeIndex u' v' := by
      intro he
      apply hne
      have h₁ := ends_edgeIndex u v (SimpleGraph.top_adj u v |>.mp huv)
      have h₂ := ends_edgeIndex u' v' (SimpleGraph.top_adj u' v' |>.mp huv')
      rw [he] at h₁
      exact h₁.symm.trans h₂
    obtain ⟨w, rfl⟩ := hinter _ _ hn hx
    exact ⟨w, ⟨avoid u v (SimpleGraph.top_adj u v |>.mp huv) w hx.1,
      avoid u' v' (SimpleGraph.top_adj u' v' |>.mp huv') w hx.2⟩, rfl⟩
  · intro u _ v _ huv w _ hw
    exact avoid u v (SimpleGraph.top_adj u v |>.mp huv) w hw

end GraphMinor.LRPlanarity
