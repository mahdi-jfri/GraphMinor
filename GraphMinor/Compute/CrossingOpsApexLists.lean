module

public import GraphMinor.Compute.CrossingOpsReplLists
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Numerical adjacency lists for the apex graph

Section 2 adds a vertex adjacent to every cycle vertex. We give that vertex index `N`,
leaving all old indices unchanged. Its list is the cycle list, and each cycle vertex's
old list receives the single new index. These lists represent the apex graph exactly.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Identify the numerical apex index `N` with `none`, and each old index with `some`. -/
def apexIndexEquiv (N : ℕ) : Fin (N + 1) ≃ Option (Fin N) := finSuccEquiv' (Fin.last N)

@[simp] theorem apexIndexEquiv_last (N : ℕ) : apexIndexEquiv N (Fin.last N) = none :=
  finSuccEquiv'_at _

@[simp] theorem apexIndexEquiv_castSucc {N : ℕ} (u : Fin N) :
    apexIndexEquiv N u.castSucc = some u := finSuccEquiv'_below u.isLt

/-- The apex graph with numerical vertex indices. -/
def apexFinGraph {N : ℕ} (G : SimpleGraph (Fin N)) (D : List (Fin N)) :
    SimpleGraph (Fin (N + 1)) := (apex G D).comap (apexIndexEquiv N)

/-- The active vertices of the numerical apex graph. -/
def apexFinVerts {N : ℕ} (S : Finset (Fin N)) : Finset (Fin (N + 1)) :=
  insert (Fin.last N) (S.map Fin.castSuccEmb)

@[simp] theorem mem_apexFinVerts_last {N : ℕ} (S : Finset (Fin N)) :
    Fin.last N ∈ apexFinVerts S := Finset.mem_insert_self _ _

@[simp] theorem mem_apexFinVerts_castSucc {N : ℕ} (S : Finset (Fin N)) (u : Fin N) :
    u.castSucc ∈ apexFinVerts S ↔ u ∈ S := by
  simp only [apexFinVerts, Finset.mem_insert, Fin.ext_iff, Fin.val_last, Fin.val_castSucc,
    show u.val ≠ N from Nat.ne_of_lt u.isLt, false_or, Finset.mem_map, Fin.castSuccEmb_apply]
  simp only [Fin.val_injective.eq_iff]
  simp

/-- The active numerical vertices correspond exactly to the apex vertex set. -/
theorem mem_apexFinVerts_iff {N : ℕ} (S : Finset (Fin N)) (u : Fin (N + 1)) :
    u ∈ apexFinVerts S ↔ apexIndexEquiv N u ∈ apexVerts (↑S) := by
  refine Fin.lastCases ?_ (fun v => ?_) u
  · simp [apexVerts]
  · simp [apexVerts]

/-- The apex graph stays supported on its active vertices when the cycle vertices are active. -/
theorem apexFinGraph_supported {N : ℕ} {G : SimpleGraph (Fin N)} {D : List (Fin N)}
    (S : Finset (Fin N)) (hG : HP25.IsSupportedOn G (↑S)) (hD : ∀ v ∈ D, v ∈ S) :
    HP25.IsSupportedOn (apexFinGraph G D) (↑(apexFinVerts S)) := by
  intro u v h
  revert h
  refine Fin.lastCases ?_ (fun a => ?_) u
  · intro _; exact mem_apexFinVerts_last S
  · refine Fin.lastCases ?_ (fun b => ?_) v
    · intro h
      apply (mem_apexFinVerts_castSucc S a).mpr
      exact hD a (by simpa [apexFinGraph, apex, apexAdj] using h)
    · intro h
      apply (mem_apexFinVerts_castSucc S a).mpr
      exact hG (by simpa [apexFinGraph, apex, apexAdj] using h)

/-- Numerical lists for the apex graph: old lists gain `N` on the cycle, and row `N` is `D`. -/
def apexList {N : ℕ} (lists : Fin N → List ℕ) (D : List (Fin N)) (x : ℕ) : List ℕ :=
  if hx : x < N then lists ⟨x, hx⟩ ++ (if (⟨x, hx⟩ : Fin N) ∈ D then [N] else [])
  else if x = N then D.map Fin.val else []

/-- The apex lists represent the graph with a new apex at index `N`. -/
theorem isAdjListFamily_apexList {N : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} (h : IsAdjListFamily G lists) (D : List (Fin N))
    (hD : D.Nodup) :
    IsAdjListFamily (apexFinGraph G D) (fun u => apexList lists D u.val) := by
  intro u
  refine Fin.lastCases ?_ (fun a => ?_) u
  · simp only [apexList, Fin.val_last, lt_self_iff_false, dite_false, ite_true]
    refine ⟨?_, hD.map Fin.val_injective, ?_, ?_⟩
    · intro y hy
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hy
      exact Nat.lt.step v.isLt
    · have hh := hD.length_le_card
      simp only [Fintype.card_fin] at hh
      simp only [List.length_map]
      omega
    · intro v
      refine Fin.lastCases ?_ (fun b => ?_) v
      · simp [apexFinGraph, apex, apexAdj]
        intro x _
        exact Nat.ne_of_lt x.isLt
      · simp [apexFinGraph, apex, apexAdj, List.mem_map, Fin.val_injective.eq_iff]
  · simp only [apexList, Fin.val_castSucc, a.isLt, dite_true, Fin.eta]
    have hnot : N ∉ lists a := fun hm => Nat.lt_irrefl N ((h a).1 N hm)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact Nat.lt.step ((h a).1 y hy)
      · split_ifs at hy <;> simp_all
    · by_cases ha : a ∈ D
      · simp only [ha, ite_true]
        exact (h a).2.1.append (by simp) (fun y hy heq => by
          have hyN : y = N := by simpa using heq
          exact hnot (hyN ▸ hy))
      · simpa only [ha, ite_false, List.append_nil] using (h a).2.1
    · have hh := (h a).2.2.1
      by_cases ha : a ∈ D <;> simp [ha] <;> omega
    · intro v
      refine Fin.lastCases ?_ (fun b => ?_) v
      · simp [apexFinGraph, apex, apexAdj, hnot]
      · have hb : b.val ≠ N := Nat.ne_of_lt b.isLt
        simp [apexFinGraph, apex, apexAdj, hb, (h a).2.2.2 b]

end GraphMinor.Compute.Crossing
