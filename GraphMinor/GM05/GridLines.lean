module

public import GraphMinor.GM05.Defs

/-!
# Rows and columns used in the grid width lower bound

A row or column, optionally omitting an initial segment, is the image of a
path. We record its vertices, connectivity, and containment in the grid.
These are the connected pieces used for Graph Minors V, (1.4).
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

/-- The square grid as a subgraph of the complete graph on its vertices. -/
@[expose] def squareGrid (n : ℕ) : (⊤ : SimpleGraph (Fin n × Fin n)).Subgraph :=
  SimpleGraph.toSubgraph (pathGraph n □ pathGraph n) le_top

private def rowHom {n : ℕ} (i : Fin n) (lo : ℕ) :
    pathGraph (n - lo) →g (pathGraph n □ pathGraph n) where
  toFun j := (i, ⟨lo + j.1, by have := j.isLt; omega⟩)
  map_rel' h := by
    apply boxProd_adj.mpr
    right
    refine ⟨?_, rfl⟩
    apply pathGraph_adj.mpr
    rcases pathGraph_adj.mp h with h | h
    · left; dsimp; omega
    · right; dsimp; omega

private def colHom {n : ℕ} (j : Fin n) (lo : ℕ) :
    pathGraph (n - lo) →g (pathGraph n □ pathGraph n) where
  toFun i := (⟨lo + i.1, by have := i.isLt; omega⟩, j)
  map_rel' h := by
    apply boxProd_adj.mpr
    left
    refine ⟨?_, rfl⟩
    apply pathGraph_adj.mpr
    rcases pathGraph_adj.mp h with h | h
    · left; dsimp; omega
    · right; dsimp; omega

private def pathImage {n m : ℕ} (f : pathGraph m →g (pathGraph n □ pathGraph n)) :
    (⊤ : SimpleGraph (Fin n × Fin n)).Subgraph :=
  (⊤ : (pathGraph m).Subgraph).map
    { toFun := f, map_rel' := fun h ↦ (f.map_rel h).ne }

private lemma pathImage_le {n m : ℕ}
    (f : pathGraph m →g (pathGraph n □ pathGraph n)) : pathImage f ≤ squareGrid n := by
  refine ⟨fun _ _ ↦ mem_univ _, ?_⟩
  rintro x y ⟨a, b, hab, rfl, rfl⟩
  exact f.map_rel hab

private lemma pathImage_connected {n m : ℕ}
    (f : pathGraph m →g (pathGraph n □ pathGraph n)) (hm : 0 < m) :
    (pathImage f).Connected := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hconn : (pathGraph m).Connected := ⟨pathGraph_preconnected m⟩
  let g : pathGraph m →g (pathImage f).coe := {
    toFun := fun a ↦ ⟨f a, ⟨a, mem_univ a, rfl⟩⟩
    map_rel' := fun {a b} h ↦ ⟨a, b, h, rfl, rfl⟩ }
  have hg : Function.Surjective g := by
    rintro ⟨x, a, ha, rfl⟩
    exact ⟨a, rfl⟩
  exact ⟨hconn.map g hg⟩

/-- The part of row `i` in columns at least `lo`. -/
def gridRow {n : ℕ} (i : Fin n) (lo : ℕ) :
    (⊤ : SimpleGraph (Fin n × Fin n)).Subgraph := pathImage (rowHom i lo)

/-- The part of column `j` in rows at least `lo`. -/
def gridCol {n : ℕ} (j : Fin n) (lo : ℕ) :
    (⊤ : SimpleGraph (Fin n × Fin n)).Subgraph := pathImage (colHom j lo)

@[simp] theorem mem_gridRow {n : ℕ} {i : Fin n} {lo : ℕ} {v : Fin n × Fin n} :
    v ∈ (gridRow i lo).verts ↔ v.1 = i ∧ lo ≤ v.2.1 := by
  constructor
  · rintro ⟨a, ha, he⟩
    change (i, ⟨lo + a.1, _⟩) = v at he
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg (fun z : Fin n × Fin n ↦ z.2.1) he
    exact ⟨h₁.symm, by dsimp at h₂; omega⟩
  · rintro ⟨h₁, h₂⟩
    let a : Fin (n - lo) := ⟨v.2.1 - lo, by have := v.2.isLt; omega⟩
    refine ⟨a, mem_univ a, ?_⟩
    apply Prod.ext h₁.symm
    apply Fin.ext
    change lo + (v.2.1 - lo) = v.2.1
    omega

@[simp] theorem mem_gridCol {n : ℕ} {j : Fin n} {lo : ℕ} {v : Fin n × Fin n} :
    v ∈ (gridCol j lo).verts ↔ v.2 = j ∧ lo ≤ v.1.1 := by
  constructor
  · rintro ⟨a, ha, he⟩
    change (⟨lo + a.1, _⟩, j) = v at he
    have h₁ := congrArg Prod.snd he
    have h₂ := congrArg (fun z : Fin n × Fin n ↦ z.1.1) he
    exact ⟨h₁.symm, by dsimp at h₂; omega⟩
  · rintro ⟨h₁, h₂⟩
    let a : Fin (n - lo) := ⟨v.1.1 - lo, by have := v.1.isLt; omega⟩
    refine ⟨a, mem_univ a, ?_⟩
    apply Prod.ext ?_ h₁.symm
    apply Fin.ext
    change lo + (v.1.1 - lo) = v.1.1
    omega

theorem gridRow_le {n : ℕ} (i : Fin n) (lo : ℕ) : gridRow i lo ≤ squareGrid n :=
  pathImage_le _

theorem gridCol_le {n : ℕ} (j : Fin n) (lo : ℕ) : gridCol j lo ≤ squareGrid n :=
  pathImage_le _

theorem gridRow_connected {n : ℕ} (i : Fin n) {lo : ℕ} (hlo : lo < n) :
    (gridRow i lo).Connected := pathImage_connected _ (by omega)

theorem gridCol_connected {n : ℕ} (j : Fin n) {lo : ℕ} (hlo : lo < n) :
    (gridCol j lo).Connected := pathImage_connected _ (by omega)

end GraphMinor.GM05
