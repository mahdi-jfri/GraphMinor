module

public import GraphMinor.GM01.Defs

/-!
# Placing disjoint grids in a larger grid

Place the `i`th copy of a `θ`-grid in rows from `i*θ` to `(i+1)*θ-1`.
The copy index and the two original coordinates are recoverable from the
new coordinates. Links inside each copy remain grid links. This supplies
the vertex and edge maps for the copy-grid minor used in (8.8).
-/

public section

namespace GraphMinor.GM05

open Graph SimpleGraph Set GM01

/-- Place grid copies in consecutive row blocks of a larger square grid. -/
@[expose] def gridCopyVertex {k θ : ℕ} (p : Fin k × (Fin θ × Fin θ)) :
    Fin ((k+1)*θ) × Fin ((k+1)*θ) :=
  (⟨p.1.val*θ+p.2.1.val,by
      have hi := Nat.mul_le_mul_right θ p.1.isLt
      have hr := p.2.1.isLt
      rw [Nat.succ_mul] at hi
      rw [Nat.add_mul,Nat.one_mul]
      omega⟩,
    ⟨p.2.2.val,by
      have hk : θ≤(k+1)*θ := by
        calc
          θ=1*θ := (one_mul _).symm
          _≤(k+1)*θ := Nat.mul_le_mul_right θ (by omega)
      exact p.2.2.isLt.trans_le hk⟩)

private lemma block_lt {k θ : ℕ} (i j : Fin k) (r s : Fin θ) (hij : i.val<j.val) :
    i.val*θ+r.val < j.val*θ+s.val := by
  have h := Nat.mul_le_mul_right θ hij
  rw [Nat.succ_mul] at h
  have hr := r.isLt
  omega

/-- The placement of grid copies is injective on all their vertices. -/
theorem gridCopyVertex_injective {k θ : ℕ} :
    Function.Injective (@gridCopyVertex k θ) := by
  intro p q h
  have hr := congrArg (fun v ↦ v.1.val) h
  have hc := congrArg (fun v ↦ v.2.val) h
  dsimp [gridCopyVertex] at hr hc
  have hi : p.1=q.1 := by
    by_contra hn
    have hne : p.1.val≠q.1.val := fun he ↦ hn (Fin.ext he)
    rcases Nat.lt_or_gt_of_ne hne with hlt|hlt
    · have hh := block_lt p.1 q.1 p.2.1 q.2.1 hlt
      omega
    · have hh := block_lt q.1 p.1 q.2.1 p.2.1 hlt
      omega
  apply Prod.ext hi
  apply Prod.ext
  · apply Fin.ext
    rw [hi] at hr
    exact Nat.add_left_cancel hr
  · exact Fin.ext hc

/-- Links of a smaller grid stay links under placement in a row block. -/
theorem gridCopyVertex_link {k θ : ℕ} (i : Fin k) {e : Sym2 (Fin θ × Fin θ)}
    {u v : Fin θ × Fin θ} (hl : (gridGraph θ).IsLink e u v) :
    (gridGraph ((k+1)*θ)).IsLink
      (Sym2.map (fun w ↦ gridCopyVertex (i,w)) e) (gridCopyVertex (i,u)) (gridCopyVertex (i,v)) := by
  have hadj : (pathGraph θ □ pathGraph θ).Adj u v := by
    have he : s(u,v)∈(pathGraph θ □ pathGraph θ).edgeSet := hl.1 ▸ hl.2
    exact he
  refine ⟨?_,?_⟩
  · rw [hl.1]
    rfl
  · rw [hl.1]
    change (pathGraph ((k+1)*θ) □ pathGraph ((k+1)*θ)).Adj _ _
    simp only [boxProd_adj,pathGraph_adj] at hadj ⊢
    rcases hadj with ⟨hrow,hcol⟩|⟨hcol,hrow⟩
    · left
      refine ⟨?_,?_⟩
      · dsimp [gridCopyVertex]
        rcases hrow with h|h
        · left; omega
        · right; omega
      · apply Fin.ext
        change u.2.val=v.2.val
        exact congrArg (fun z : Fin θ ↦ z.val) hcol
    · right
      refine ⟨?_,?_⟩
      · exact hcol
      · apply Fin.ext
        change i.val*θ+u.1.val=i.val*θ+v.1.val
        rw [hrow]

end GraphMinor.GM05
