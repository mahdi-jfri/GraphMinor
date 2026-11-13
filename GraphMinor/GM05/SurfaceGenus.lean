module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.ModelCriterion
import GraphMinor.Surface.CutComp
public import Mathlib.Data.Multiset.Sort
import Mathlib.Order.Lattice.Nat

/-!
# Genus lists of closed surfaces

Graph Minors V, page 112, defines the genus of a connected orientable
surface as its number of handles. We use the library's handle model
`SurfaceModel g 0 0`. The definition is invariant under homeomorphism and
has value `g` on that model, by the proved model criterion. A closed
surface has finitely many connected components. Collect their genera
and sort them in nonincreasing order, retaining genus-zero components.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

universe u v

/-- The number of handles of a connected orientable closed surface,
Graph Minors V, page 112. It is the least `g` for which the surface is
homeomorphic to the sphere with `g` handles. -/
noncomputable def connectedGenus (S : Type u) [TopologicalSpace S] : ℕ :=
  sInf {g : ℕ | Nonempty (S ≃ₜ SurfaceModel g 0 0)}

/-- Genus is unchanged by homeomorphism. -/
theorem connectedGenus_homeo {S : Type u} [TopologicalSpace S]
    {T : Type v} [TopologicalSpace T] (e : S ≃ₜ T) : connectedGenus S=connectedGenus T := by
  unfold connectedGenus
  congr 1
  ext g
  constructor
  · rintro ⟨f⟩
    exact ⟨e.symm.trans f⟩
  · rintro ⟨f⟩
    exact ⟨e.trans f⟩

/-- The connected genus of a sphere with `g` handles is exactly `g`. -/
theorem connectedGenus_model (g : ℕ) : connectedGenus (SurfaceModel g 0 0)=g := by
  have he : {h : ℕ | Nonempty (SurfaceModel g 0 0 ≃ₜ SurfaceModel h 0 0)}={g} := by
    ext h
    constructor
    · intro hh
      have hn := ((modelCriterion.2 g 0 0 h 0 0).mp hh).2.1
      change h=g
      omega
    · intro hh
      have hh' : h=g := hh
      subst h
      exact ⟨Homeomorph.refl _⟩
  unfold connectedGenus
  rw [he]
  simp

/-- A representation by the handle model computes the connected genus. -/
theorem connectedGenus_eq_of_model {S : Type u} [TopologicalSpace S] {g : ℕ}
    (e : S ≃ₜ SurfaceModel g 0 0) : connectedGenus S=g :=
  (connectedGenus_homeo e).trans (connectedGenus_model g)

/-- The nonincreasing list of component genera, including the zero genera
of spherical components, as defined in Graph Minors V, page 112. -/
noncomputable def surfaceGenusList (S : Type u) [TopologicalSpace S] (hS : IsClosedSurface S) : List ℕ := by
  classical
  let : CompactSpace S := hS.1
  have hsurface : IsSurface S := ⟨hS.1,hS.2.1,fun x ↦ (hS.2.2 x).isManifoldPoint⟩
  let : LocallyConnectedSpace S := hsurface.locallyConnected
  let : Fintype (ConnectedComponents S) := Fintype.ofFinite _
  exact (Finset.univ.val.map (fun c : ConnectedComponents S ↦
    connectedGenus (ConnectedComponents.mk ⁻¹' {c} : Set S))).sort (· ≥ ·)

/-- The component-genus list can be computed using any enumeration of
its connected components. -/
theorem surfaceGenusList_eq_sort (S : Type u) [TopologicalSpace S]
    (hS : IsClosedSurface S) [Fintype (ConnectedComponents S)] :
    surfaceGenusList S hS=(Finset.univ.val.map (fun c : ConnectedComponents S ↦
      connectedGenus (ConnectedComponents.mk ⁻¹' {c} : Set S))).sort (· ≥ ·) := by
  classical
  unfold surfaceGenusList
  dsimp only
  congr 3
  ext c
  simp

/-- Component genera are listed in nonincreasing order. -/
theorem surfaceGenusList_sorted (S : Type u) [TopologicalSpace S] (hS : IsClosedSurface S) :
    (surfaceGenusList S hS).Pairwise (· ≥ ·) := by
  unfold surfaceGenusList
  exact Multiset.pairwise_sort _ _

/-- The list contains one entry for each connected component. -/
theorem surfaceGenusList_length (S : Type u) [TopologicalSpace S] (hS : IsClosedSurface S) :
    (surfaceGenusList S hS).length=Nat.card (ConnectedComponents S) := by
  classical
  let : CompactSpace S := hS.1
  have hsurface : IsSurface S := ⟨hS.1,hS.2.1,fun x ↦ (hS.2.2 x).isManifoldPoint⟩
  let : LocallyConnectedSpace S := hsurface.locallyConnected
  let : Fintype (ConnectedComponents S) := Fintype.ofFinite _
  simp [surfaceGenusList,Nat.card_eq_fintype_card]

/-- The empty surface has the empty genus list. -/
theorem surfaceGenusList_of_isEmpty (S : Type u) [TopologicalSpace S] [IsEmpty S]
    (hS : IsClosedSurface S) : surfaceGenusList S hS=[] := by
  let : IsEmpty (ConnectedComponents S) := ⟨fun c ↦ by
    obtain ⟨x,hx⟩ := ConnectedComponents.surjective_coe c
    exact isEmptyElim x⟩
  apply List.length_eq_zero_iff.mp
  rw [surfaceGenusList_length]
  simp

/-- A connected closed surface has the singleton genus list. -/
theorem surfaceGenusList_of_connected (S : Type u) [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) : surfaceGenusList S hS=[connectedGenus S] := by
  classical
  let : CompactSpace S := hS.1
  have hsurface : IsSurface S := ⟨hS.1,hS.2.1,fun x ↦ (hS.2.2 x).isManifoldPoint⟩
  let : LocallyConnectedSpace S := hsurface.locallyConnected
  let : Fintype (ConnectedComponents S) := Fintype.ofFinite _
  let c₀ : ConnectedComponents S := ConnectedComponents.mk (Classical.choice (inferInstance : Nonempty S))
  have hu : (Finset.univ : Finset (ConnectedComponents S))={c₀} := by
    ext c
    simp only [Finset.mem_univ,Finset.mem_singleton,true_iff]
    exact Subsingleton.elim c c₀
  have hf : (ConnectedComponents.mk ⁻¹' {c₀} : Set S)=univ := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,mem_univ,iff_true]
    exact Subsingleton.elim _ _
  have hg : connectedGenus (ConnectedComponents.mk ⁻¹' {c₀} : Set S)=connectedGenus S :=
    connectedGenus_homeo ((Homeomorph.setCongr hf).trans (Homeomorph.Set.univ S))
  unfold surfaceGenusList
  change (Finset.univ.val.map (fun c : ConnectedComponents S ↦
    connectedGenus (ConnectedComponents.mk ⁻¹' {c} : Set S))).sort (· ≥ ·)=[connectedGenus S]
  rw [hu]
  simpa only [Finset.singleton_val,Multiset.map_singleton,Multiset.sort_singleton] using congrArg (fun n ↦ [n]) hg

/-- A sphere with `g` handles has the genus list `[g]`; in particular the
sphere contributes a zero entry, rather than being omitted. -/
theorem surfaceGenusList_model (g : ℕ) (hS : IsClosedSurface (SurfaceModel g 0 0)) :
    surfaceGenusList (SurfaceModel g 0 0) hS=[g] := by
  let : ConnectedSpace (SurfaceModel g 0 0) := (modelCriterion.1 g 0 0).2
  rw [surfaceGenusList_of_connected,connectedGenus_model]

end GraphMinor.GM05
