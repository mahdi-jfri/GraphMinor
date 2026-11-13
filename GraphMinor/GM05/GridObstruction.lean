module

public import GraphMinor.GM05.GridLines

/-!
# A touching family in the square grid

For Graph Minors V, (1.4), use the first row, the first column without its
first vertex, and the crosses in the remaining smaller square. Every member
is connected and every two touch. Hitting all crosses in the smaller square
requires at least `n - 1` vertices there, in addition to vertices in the two
boundary members.
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

/-- The positive coordinate corresponding to an index in the smaller grid. -/
@[expose] def gridPos {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨i.1 + 1, by have := i.isLt; omega⟩

private lemma gridPos_injective {n : ℕ} : Function.Injective (@gridPos n) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [gridPos] at hv
  omega

/-- The first row, the rest of the first column, and crosses in the smaller
square obtained by removing that row and column. -/
@[expose] def gridTouchingFamily {n : ℕ} (hn : 2 ≤ n) :
    Bool ⊕ (Fin (n - 1) × Fin (n - 1)) → (⊤ : SimpleGraph (Fin n × Fin n)).Subgraph
  | .inl false => gridRow ⟨0, by omega⟩ 0
  | .inl true => gridCol ⟨0, by omega⟩ 1
  | .inr (i, j) => gridRow (gridPos i) 1 ⊔ gridCol (gridPos j) 1

theorem gridTouchingFamily_le {n : ℕ} (hn : 2 ≤ n) (a) :
    gridTouchingFamily hn a ≤ squareGrid n := by
  cases a with
  | inl b => cases b <;> first | exact gridRow_le _ _ | exact gridCol_le _ _
  | inr ij => exact sup_le (gridRow_le _ _) (gridCol_le _ _)

theorem gridTouchingFamily_connected {n : ℕ} (hn : 2 ≤ n) (a) :
    (gridTouchingFamily hn a).Connected := by
  cases a with
  | inl b =>
    cases b
    · exact gridRow_connected _ (by omega)
    · exact gridCol_connected _ (by omega)
  | inr ij =>
    obtain ⟨i, j⟩ := ij
    apply Subgraph.connected_sup (gridRow_connected _ (by omega)).preconnected
      (gridCol_connected _ (by omega)).preconnected
    refine ⟨(gridPos i, gridPos j), ?_, ?_⟩ <;> simp [gridPos]

/-- Every two members of the grid family share a vertex or are joined by
an edge of the grid. -/
theorem gridTouchingFamily_touch {n : ℕ} (hn : 2 ≤ n) (a b) :
    ∃ x ∈ (gridTouchingFamily hn a).verts, ∃ y ∈ (gridTouchingFamily hn b).verts,
      x = y ∨ (squareGrid n).Adj x y := by
  let z : Fin n := ⟨0, by omega⟩
  let k : Fin (n - 1) := ⟨0, by omega⟩
  have hr (j : Fin n) : (z, j) ∈ (gridTouchingFamily hn (.inl false)).verts := by
    simp [gridTouchingFamily, z]
  have hc (i : Fin (n - 1)) :
      (gridPos i, z) ∈ (gridTouchingFamily hn (.inl true)).verts := by
    simp [gridTouchingFamily, z, gridPos]
  have hcr (i j l : Fin (n - 1)) :
      (gridPos i, gridPos l) ∈ (gridTouchingFamily hn (.inr (i, j))).verts := by
    exact Or.inl (by simp [gridPos])
  have hcc (i j l : Fin (n - 1)) :
      (gridPos l, gridPos j) ∈ (gridTouchingFamily hn (.inr (i, j))).verts := by
    exact Or.inr (by simp [gridPos])
  have hh (i : Fin n) : (squareGrid n).Adj (i, z) (i, gridPos k) := by
    apply boxProd_adj.mpr
    exact Or.inr ⟨pathGraph_adj.mpr (Or.inl rfl), rfl⟩
  have hv (j : Fin n) : (squareGrid n).Adj (z, j) (gridPos k, j) := by
    apply boxProd_adj.mpr
    exact Or.inl ⟨pathGraph_adj.mpr (Or.inl rfl), rfl⟩
  rcases a with a | ⟨i, j⟩ <;> rcases b with b | ⟨l, m⟩
  · cases a <;> cases b
    · exact ⟨(z, z), hr z, (z, z), hr z, Or.inl rfl⟩
    · exact ⟨(z, z), hr z, (gridPos k, z), hc k, Or.inr (hv z)⟩
    · exact ⟨(gridPos k, z), hc k, (z, z), hr z, Or.inr (hv z).symm⟩
    · exact ⟨(gridPos k, z), hc k, (gridPos k, z), hc k, Or.inl rfl⟩
  · cases a
    · exact ⟨(z, gridPos m), hr _, (gridPos k, gridPos m), hcc l m k,
        Or.inr (hv _)⟩
    · exact ⟨(gridPos l, z), hc l, (gridPos l, gridPos k), hcr l m k,
        Or.inr (hh _)⟩
  · cases b
    · exact ⟨(gridPos k, gridPos j), hcc i j k, (z, gridPos j), hr _,
        Or.inr (hv _).symm⟩
    · exact ⟨(gridPos i, gridPos k), hcr i j k, (gridPos i, z), hc i,
        Or.inr (hh _).symm⟩
  · exact ⟨(gridPos i, gridPos m), hcr i j m, (gridPos i, gridPos m), hcc l m i,
      Or.inl rfl⟩

private lemma inner_points_count {n : ℕ} {X : Set (Fin n × Fin n)}
    (hX : X.Finite)
    (hrows : (∀ i : Fin (n - 1), (X ∩ (gridRow (gridPos i) 1).verts).Nonempty) ∨
      (∀ j : Fin (n - 1), (X ∩ (gridCol (gridPos j) 1).verts).Nonempty)) :
    n - 1 ≤ {v ∈ X | 0 < v.1.1 ∧ 0 < v.2.1}.ncard := by
  classical
  let S : Set (Fin n × Fin n) := {v ∈ X | 0 < v.1.1 ∧ 0 < v.2.1}
  have hS : S.Finite := hX.subset (fun _ h ↦ h.1)
  let : Finite S := hS.to_subtype
  rcases hrows with hrows | hcols
  · choose p hpX hp using hrows
    let f : Fin (n - 1) → S := fun i ↦ ⟨p i, hpX i, by
      have hi := (mem_gridRow.mp (hp i)).1
      have hj := (mem_gridRow.mp (hp i)).2
      rw [hi]
      dsimp [gridPos]
      omega⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply gridPos_injective
      have he := congrArg (fun v : S ↦ v.1.1) hij
      change (p i).1 = (p j).1 at he
      exact (mem_gridRow.mp (hp i)).1.symm.trans (he.trans (mem_gridRow.mp (hp j)).1)
    have hc := Nat.card_le_card_of_injective f hf
    have hnc : Nat.card (Fin (n - 1)) = n - 1 := by simp
    rw [hnc, Nat.card_coe_set_eq] at hc
    exact hc
  · choose p hpX hp using hcols
    let f : Fin (n - 1) → S := fun i ↦ ⟨p i, hpX i, by
      have hi := (mem_gridCol.mp (hp i)).2
      have hj := (mem_gridCol.mp (hp i)).1
      rw [hj]
      dsimp [gridPos]
      omega⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply gridPos_injective
      have he := congrArg (fun v : S ↦ v.1.2) hij
      change (p i).2 = (p j).2 at he
      exact (mem_gridCol.mp (hp i)).1.symm.trans (he.trans (mem_gridCol.mp (hp j)).1)
    have hc := Nat.card_le_card_of_injective f hf
    have hnc : Nat.card (Fin (n - 1)) = n - 1 := by simp
    rw [hnc, Nat.card_coe_set_eq] at hc
    exact hc

/-- Any set meeting the boundary members and all smaller-grid crosses has
at least `n + 1` vertices. -/
theorem gridTouchingFamily_hitting_card {n : ℕ} (hn : 2 ≤ n)
    {X : Set (Fin n × Fin n)} (hX : X.Finite)
    (hhit : ∀ a, (X ∩ (gridTouchingFamily hn a).verts).Nonempty) : n + 1 ≤ X.ncard := by
  classical
  let S : Set (Fin n × Fin n) := {v ∈ X | 0 < v.1.1 ∧ 0 < v.2.1}
  have hS : S.Finite := hX.subset (fun _ h ↦ h.1)
  have hinner : n - 1 ≤ S.ncard := by
    apply inner_points_count hX
    by_cases hrows : ∀ i : Fin (n - 1), (X ∩ (gridRow (gridPos i) 1).verts).Nonempty
    · exact Or.inl hrows
    · right
      push Not at hrows
      obtain ⟨i, hi⟩ := hrows
      intro j
      obtain ⟨v, hvX, hv⟩ := hhit (.inr (i, j))
      rcases hv with hv | hv
      · have hm : v ∈ X ∩ (gridRow (gridPos i) 1).verts := ⟨hvX, hv⟩
        rw [hi] at hm
        exact hm.elim
      · exact ⟨v, hvX, hv⟩
  obtain ⟨x, hxX, hx⟩ := hhit (.inl false)
  obtain ⟨y, hyX, hy⟩ := hhit (.inl true)
  have hx0 : x.1.1 = 0 := congrArg Fin.val (mem_gridRow.mp hx).1
  have hy0 : y.2.1 = 0 := congrArg Fin.val (mem_gridCol.mp hy).1
  have hy1 : 1 ≤ y.1.1 := (mem_gridCol.mp hy).2
  have hxS : x ∉ S := by intro h; have := h.2.1; omega
  have hyS : y ∉ S := by intro h; have := h.2.2; omega
  have hxy : x ≠ y := by intro he; have := congrArg (fun v : Fin n × Fin n ↦ v.1.1) he; omega
  have hsub : insert x (insert y S) ⊆ X := by
    intro v hv
    rcases hv with rfl | rfl | hv
    · exact hxX
    · exact hyX
    · exact hv.1
  have hc := ncard_le_ncard hsub hX
  rw [ncard_insert_of_notMem (by simp [hxy, hxS]) (hS.insert y),
    ncard_insert_of_notMem hyS hS] at hc
  omega

end GraphMinor.GM05
