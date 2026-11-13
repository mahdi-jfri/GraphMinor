module

public import GraphMinor.Crossing.DefsForest
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Renaming scan-first forests

The numerical apex encoding and the graph interface use different vertex types.
Renaming by an equivalence preserves scan orders, parent choices, and successive
forest deletion. The scan order is renamed by the same equivalence.
-/

public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

universe u v
variable {V : Type u} {W : Type v} [DecidableEq V] [DecidableEq W]

private theorem idxOf_map_equiv (e : V ≃ W) (l : List V) (a : V) :
    (l.map e).idxOf (e a) = l.idxOf a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [List.idxOf_cons, e.injective.eq_iff, ih]

private theorem reachIn_equiv_symm (e : V ≃ W) {G : SimpleGraph V} {T : Set V}
    {a b : V} (hr : ReachIn (G.comap e.symm) (e '' T) (e a) (e b)) : ReachIn G T a b := by
  let f : (G.comap e.symm) →g G := ⟨e.symm, fun h => h⟩
  obtain ⟨p, hp⟩ := hr
  have hh : ReachIn G T (e.symm (e a)) (e.symm (e b)) := by
    refine ⟨p.map f, ?_⟩
    intro y hy
    rw [SimpleGraph.Walk.support_map] at hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    obtain ⟨x, hx, hxe⟩ := hp z hz
    change e.symm z ∈ T
    rw [← hxe, Equiv.symm_apply_apply]
    exact hx
  simpa only [Equiv.symm_apply_apply] using hh

/-- Renaming the vertices and the scan order preserves the scan-order condition. -/
theorem isScanOrder_equiv (e : V ≃ W) {G : SimpleGraph V} {T : Set V} {σ : List V}
    (h : IsScanOrder G T σ) : IsScanOrder (G.comap e.symm) (e '' T) (σ.map e) := by
  refine ⟨h.1.map e.injective, ?_, ?_⟩
  · intro y
    simp only [List.mem_map, Set.mem_image]
    exact exists_congr (fun x => and_congr_left (fun _ => h.2.1 x))
  · intro i j a b hij hia hjb hr
    rw [List.getElem?_map] at hia hjb
    obtain ⟨a', hia', rfl⟩ := Option.map_eq_some_iff.mp hia
    obtain ⟨b', hjb', rfl⟩ := Option.map_eq_some_iff.mp hjb
    obtain ⟨k, hkj, c, hc, hadj⟩ := h.2.2 i j a' b' hij hia' hjb' (reachIn_equiv_symm e hr)
    refine ⟨k, hkj, e c, ?_, ?_⟩
    · simp only [List.getElem?_map, hc, Option.map_some]
    · simpa only [SimpleGraph.comap_adj, Equiv.symm_apply_apply] using hadj

/-- Parent choice is preserved by renaming both the vertex and its potential parent. -/
theorem isScanParent_equiv (e : V ≃ W) (G : SimpleGraph V) (σ : List V) (c p : V) :
    IsScanParent (G.comap e.symm) (σ.map e) (e c) (e p) ↔ IsScanParent G σ c p := by
  simp only [IsScanParent, SimpleGraph.comap_adj, Equiv.symm_apply_apply, idxOf_map_equiv]
  constructor
  · rintro ⟨ha, hl, hmin⟩
    refine ⟨ha, hl, fun y hy => ?_⟩
    simpa only [Equiv.symm_apply_apply, idxOf_map_equiv] using hmin (e y) (by simpa using hy)
  · rintro ⟨ha, hl, hmin⟩
    refine ⟨ha, hl, fun y hy => ?_⟩
    have hh := hmin (e.symm y) hy
    simpa only [← idxOf_map_equiv e σ (e.symm y), Equiv.apply_symm_apply] using hh

/-- A scan-first forest remains scan-first after renaming the graph and active vertices. -/
theorem isScanFirstForest_equiv (e : V ≃ W) {G F : SimpleGraph V} {T : Set V}
    (h : IsScanFirstForest G T F) :
    IsScanFirstForest (G.comap e.symm) (e '' T) (F.comap e.symm) := by
  obtain ⟨σ, hs, rfl⟩ := h
  refine ⟨σ.map e, isScanOrder_equiv e hs, ?_⟩
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  simp only [SimpleGraph.comap_adj, Equiv.symm_apply_apply, scanForest,
    isScanParent_equiv]

/-- Renaming commutes with graph difference and therefore preserves successive forests. -/
theorem isScanFirstSequence_equiv (e : V ≃ W) {G : SimpleGraph V} {T : Set V}
    {Fs : List (SimpleGraph V)} (h : IsScanFirstSequence G T Fs) :
    IsScanFirstSequence (G.comap e.symm) (e '' T) (Fs.map (fun F => F.comap e.symm)) := by
  induction Fs generalizing G with
  | nil => trivial
  | cons F Fs ih =>
    refine ⟨isScanFirstForest_equiv e h.1, ?_⟩
    have hh := ih h.2
    have heq : (G \ F).comap e.symm = G.comap e.symm \ F.comap e.symm := by ext a b; rfl
    simpa only [heq] using hh

end GraphMinor.Compute.Crossing
