module

public import GraphMinor.Compute.GM06Alg34InducedData
public import GraphMinor.Compute.GM06Alg34MapCrossing

/-!
# Cuff order in the computed induced drawing data

The new cuff lists filter old lists and use canonical new vertex
numbers. Reading the new numbers gives exactly the old filtered list.
Filtering preserves crossing order, and injective renumbering preserves
it again. The new cuff lists therefore have no repetitions and describe
exactly the original crossing relation on the surviving labels.
-/

public section
namespace GraphMinor.Compute.GM06DrawingData

/-- A nonrepeating cuff list stays nonrepeating after filtering and renumbering. -/
theorem relabelVertexList_nodup (x : GM06DrawingData) (vs L : List (Fin x.n)) (hL : L.Nodup) :
    (x.relabelVertexList vs L).Nodup := by
  apply List.Nodup.of_map (fun i => (x.activeVertices vs).get i)
  rw [x.map_relabelVertexList vs L]
  exact hL.filter _

/-- The crossing test on a new cuff list is exactly the old cuff's test
on the corresponding surviving old labels. -/
theorem crossesOnList_relabelVertexList (x : GM06DrawingData) (vs L : List (Fin x.n))
    (hL : L.Nodup) (a c b d : Fin (x.activeVertices vs).length) :
    crossesOnList (x.relabelVertexList vs L) a c b d =
      crossesOnList L ((x.activeVertices vs).get a) ((x.activeVertices vs).get c)
        ((x.activeVertices vs).get b) ((x.activeVertices vs).get d) := by
  let f := fun i : Fin (x.activeVertices vs).length => (x.activeVertices vs).get i
  have hf : Function.Injective f := fun _ _ h => (x.activeVertices_nodup vs).get_inj_iff.mp h
  have hactive (i : Fin (x.activeVertices vs).length) : decide (f i ∈ vs) = true :=
    decide_eq_true ((x.mem_activeVertices_iff vs _).mp (List.get_mem _ i))
  calc
    _ = crossesOnList ((x.relabelVertexList vs L).map f) (f a) (f c) (f b) (f d) :=
      (gm06_crossesOnList_map f hf _ a c b d).symm
    _ = crossesOnList (L.filter (fun v => decide (v ∈ vs))) (f a) (f c) (f b) (f d) := by
      rw [x.map_relabelVertexList vs L]
    _ = _ := gm06_crossesOnList_filter L hL _ _ _ _ _ (hactive a) (hactive c) (hactive b) (hactive d)

/-- All cuff crossing tests in the computed induced data agree with the
old drawing on its surviving vertex labels. -/
theorem inducedData_crosses (x : GM06DrawingData) (vs : List (Fin x.n))
    (hnd : ∀ L ∈ x.cuffs, L.Nodup) (a c b d : Fin (x.activeVertices vs).length) :
    (x.inducedData vs).crosses a c b d =
      x.crosses ((x.activeVertices vs).get a) ((x.activeVertices vs).get c)
        ((x.activeVertices vs).get b) ((x.activeVertices vs).get d) := by
  simp only [crosses, inducedData, List.any_map, Function.comp_def]
  have aux (Ls : List (List (Fin x.n))) (hLs : ∀ L ∈ Ls, L.Nodup) :
      Ls.any (fun L => crossesOnList (x.relabelVertexList vs L) a c b d) =
        Ls.any (fun L => crossesOnList L ((x.activeVertices vs).get a)
          ((x.activeVertices vs).get c) ((x.activeVertices vs).get b) ((x.activeVertices vs).get d)) := by
    induction Ls with
    | nil => rfl
    | cons L Ls ih =>
      rw [List.any_cons, List.any_cons,
        x.crossesOnList_relabelVertexList vs L (hLs L List.mem_cons_self) a c b d,
        ih (fun M hM => hLs M (List.mem_cons_of_mem L hM))]
  exact aux x.cuffs hnd

end GraphMinor.Compute.GM06DrawingData
