module

public import GraphMinor.Compute.GM06Alg34ComponentEdgeMass

/-!
# An additive work weight for the reduction queue

Charge a nonempty problem by three times its vertices plus a fixed
multiple of its edges, minus one. Charge an empty problem by one.
Component branching conserves vertex and edge mass but loses one unit
for each additional child. Vertex deletion lowers the weight. With the
edge multiplier larger than the fixed vertex bound, losing an edge
also lowers the weight even when duality exchanges vertices and regions.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

/-- Vertex and edge mass with a fixed edge multiplier. -/
def workMass (C : ℕ) (x : GM06DrawingData) : ℕ := x.n + C * x.ends.length

/-- An additive queue charge, including one unit for an empty problem. -/
def workWeight (C : ℕ) (x : GM06DrawingData) : ℕ :=
  if x.n = 0 then 1 else 3 * x.workMass C - 1

/-- Every current problem has a positive charge. -/
theorem workWeight_pos (C : ℕ) (x : GM06DrawingData) : 0 < x.workWeight C := by
  unfold workWeight workMass
  split <;> omega

/-- Vertex deletion without adding edges strictly lowers mass. -/
theorem workMass_lt_of_vertices (C : ℕ) (x y : GM06DrawingData)
    (hn : y.n < x.n) (he : y.ends.length ≤ x.ends.length) :
    y.workMass C < x.workMass C := by
  have hm := Nat.mul_le_mul_left C he
  unfold workMass
  omega

/-- Losing an edge offsets any new vertex count bounded by the fixed vertex bound. -/
theorem workMass_lt_of_edges (M : ℕ) (x y : GM06DrawingData)
    (hn : y.n ≤ M) (he : y.ends.length < x.ends.length) :
    y.workMass (M + 1) < x.workMass (M + 1) := by
  have hm := Nat.mul_le_mul_left (M + 1) (show y.ends.length + 1 ≤ x.ends.length by omega)
  simp only [Nat.mul_add, Nat.mul_one] at hm
  unfold workMass
  omega

/-- A strict mass decrease from a nonempty problem strictly lowers the queue charge. -/
theorem workWeight_lt_of_mass (C : ℕ) (x y : GM06DrawingData)
    (hn : 0 < x.n) (hm : y.workMass C < x.workMass C) :
    y.workWeight C < x.workWeight C := by
  have hp : 0 < x.workMass C := by unfold workMass; omega
  unfold workWeight
  split <;> split <;> omega

/-- All canonical component inputs are nonempty. -/
theorem componentData_n_pos (x : GM06DrawingData) (a : Fin x.n) :
    0 < (x.componentData a).n := by
  rw [x.componentData_n]
  exact List.length_pos_of_mem (x.mem_componentVertices_self a)

/-- The weighted mass of all child problems equals the parent's weighted mass. -/
theorem componentData_sum_workMass (C : ℕ) (x : GM06DrawingData) :
    (x.componentRoots.map (fun a => (x.componentData a).workMass C)).sum = x.workMass C := by
  simp only [workMass, List.sum_map_add, List.sum_map_mul_left,
    x.componentData_sum_n, x.componentData_sum_edges]

private theorem sum_charge {α : Type*} (L : List α) (f : α → ℕ)
    (hp : ∀ a ∈ L, 0 < f a) :
    (L.map (fun a => 3 * f a - 1)).sum + L.length = 3 * (L.map f).sum := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.mul_zero]
  | cons a L ih =>
    have ha := hp a (List.mem_cons_self ..)
    have ht := ih (fun b hb => hp b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add]
    omega

/-- Component branching has a precise charge loss of one per child. -/
theorem componentData_sum_workWeight (C : ℕ) (x : GM06DrawingData) :
    (x.componentRoots.map (fun a => (x.componentData a).workWeight C)).sum +
      x.componentRoots.length = 3 * x.workMass C := by
  have he : (fun a : Fin x.n => (x.componentData a).workWeight C) =
      (fun a => 3 * (x.componentData a).workMass C - 1) := by
    funext a
    exact if_neg (Nat.ne_of_gt (x.componentData_n_pos a))
  rw [he]
  have h := sum_charge x.componentRoots (fun a => (x.componentData a).workMass C)
    (fun a _ => by have hp := x.componentData_n_pos a; unfold workMass; omega)
  rw [x.componentData_sum_workMass C] at h
  exact h

/-- Branching into at least two canonical components strictly lowers total queue charge. -/
theorem componentData_workWeight_lt (C : ℕ) (x : GM06DrawingData)
    (hk : 2 ≤ x.componentRoots.length) :
    (x.componentRoots.map (fun a => (x.componentData a).workWeight C)).sum < x.workWeight C := by
  have hn : x.n ≠ 0 := by
    cases hr : x.componentRoots with
    | nil =>
      simp only [hr, List.length_nil] at hk
      omega
    | cons a L =>
      have ht := a.isLt
      omega
  have hh := x.componentData_sum_workWeight C
  rw [show x.workWeight C = 3 * x.workMass C - 1 from ite_eq_right hn]
  omega

end GraphMinor.Compute.GM06DrawingData
