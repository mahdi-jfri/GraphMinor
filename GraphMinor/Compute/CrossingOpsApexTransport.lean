module

public import GraphMinor.Compute.CrossingOpsApexLists
public import GraphMinor.Compute.CrossingOpsForestTransport

/-!
# Connecting numerical apex forests to the graph interface

The equivalence sends old indices to `some` vertices and the final index to `none`.
Transporting a sequence of numerical forests along it yields the same successive
forest condition on the apex graph used in the sparsification specification.
-/

public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

@[simp] theorem apexIndexEquiv_symm_some {N : ℕ} (u : Fin N) :
    (apexIndexEquiv N).symm (some u) = u.castSucc := by
  apply (apexIndexEquiv N).injective
  simp

@[simp] theorem apexIndexEquiv_symm_none (N : ℕ) :
    (apexIndexEquiv N).symm none = Fin.last N := by
  apply (apexIndexEquiv N).injective
  simp

/-- Undoing the numerical indexing gives exactly the interface's apex graph. -/
theorem apexFinGraph_comap {N : ℕ} (G : SimpleGraph (Fin N)) (D : List (Fin N)) :
    (apexFinGraph G D).comap (apexIndexEquiv N).symm = apex G D := by
  ext a b
  simp only [apexFinGraph, SimpleGraph.comap_adj, Equiv.apply_symm_apply]

/-- The image of the active numerical vertices is exactly the active apex vertex set. -/
theorem apexFinVerts_image {N : ℕ} (S : Finset (Fin N)) :
    apexIndexEquiv N '' (↑(apexFinVerts S) : Set (Fin (N + 1))) = apexVerts (↑S) := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (mem_apexFinVerts_iff S u).mp hu
  · intro hy
    refine ⟨(apexIndexEquiv N).symm y, ?_, (apexIndexEquiv N).apply_symm_apply y⟩
    exact (mem_apexFinVerts_iff S _).mpr (by simpa only [Equiv.apply_symm_apply] using hy)

/-- A numerical scan-first sequence transports to the apex graph in the specification. -/
theorem apex_isScanFirstSequence {N : ℕ} {G : SimpleGraph (Fin N)} {D : List (Fin N)}
    (S : Finset (Fin N)) {Fs : List (SimpleGraph (Fin (N + 1)))}
    (h : IsScanFirstSequence (apexFinGraph G D) (↑(apexFinVerts S)) Fs) :
    IsScanFirstSequence (apex G D) (apexVerts (↑S))
      (Fs.map (fun F => F.comap (apexIndexEquiv N).symm)) := by
  have hh := isScanFirstSequence_equiv (apexIndexEquiv N) h
  simpa only [apexFinGraph_comap, apexFinVerts_image] using hh

/-- A non-apex edge belongs to the transported forest union exactly when its numerical
edge belongs to the original union. -/
theorem apex_forestUnion_adj {N : ℕ} (Fs : List (SimpleGraph (Fin (N + 1)))) (u v : Fin N) :
    (forestUnion (Fs.map (fun F => F.comap (apexIndexEquiv N).symm))).Adj (some u) (some v) ↔
      (forestUnion Fs).Adj u.castSucc v.castSucc := by
  induction Fs with
  | nil => rfl
  | cons F Fs ih =>
    simpa only [List.map_cons, forestUnion, SimpleGraph.sup_adj, SimpleGraph.comap_adj,
      apexIndexEquiv_symm_some] using or_congr Iff.rfl ih

end GraphMinor.Compute.Crossing
