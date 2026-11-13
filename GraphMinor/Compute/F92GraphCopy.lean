module

public import GraphMinor.Compute.F92Copy

/-!
# Moving the parsed graph into the search block

Copy CSR starts and ends with the entry-array length as bound. Copy neighbour entries with
the vertex count as bound. CSR offsets and used neighbours are within these bounds, so the
copied graph has exactly the same adjacency lists, regardless of unused array entries.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- Bounded copies of the three CSR arrays represent the same graph. -/
theorem f92AdjList_of_bounded_copies {n : ℕ} {G : SimpleGraph (Fin n)}
    {lists : Fin n → List ℕ} {aS aE aEnt bS bE bEnt : Arr} {s s' : State}
    (hadj : IsAdjList G aS aE aEnt lists s)
    (hS : s'.arrs bS = (s.arrs aS).map (fun v => min v (s.arrs aEnt).length))
    (hE : s'.arrs bE = (s.arrs aE).map (fun v => min v (s.arrs aEnt).length))
    (hEnt : s'.arrs bEnt = (s.arrs aEnt).map (fun v => min v n)) :
    IsAdjList G bS bE bEnt lists s' := by
  refine ⟨⟨by rw [hS, List.length_map]; exact hadj.1.1,
    by rw [hE, List.length_map]; exact hadj.1.2.1, ?_⟩, hadj.2⟩
  intro u
  obtain ⟨st, en, huS, huE, hen, hdiff, hst, henval, hle, hlist⟩ := hadj.1.2.2 u
  refine ⟨st, en, ?_, ?_, ?_, hdiff, ?_, ?_, hle, ?_⟩
  · rw [hS, List.length_map]; exact huS
  · rw [hE, List.length_map]; exact huE
  · rw [hEnt, List.length_map]; exact hen
  · simp only [hS, List.getElem_map, hst]
    exact Nat.min_eq_left (hle.trans hen)
  · simp only [hE, List.getElem_map, henval]
    exact Nat.min_eq_left hen
  · intro j hj
    simp only [hEnt, List.getElem_map, hlist j hj]
    exact Nat.min_eq_left (Nat.le_of_lt ((hadj.2 u).1 _ (List.getElem_mem hj)))

/-- Copy the graph into offsets 40–42 and set the search's size register. -/
def f92GraphCopyProg (aS aE aEnt r_n base : ℕ) : Cmd :=
  .seq (.assign (base + 75) (.len aEnt))
    (.seq (f92CopyBoundedProg aS (base + 40) (base + 75) (base + 80))
      (.seq (f92CopyBoundedProg aE (base + 41) (base + 75) (base + 80))
        (.seq (.assign (base + 75) (.reg r_n))
          (.seq (f92CopyBoundedProg aEnt (base + 42) (base + 75) (base + 80))
            (.assign (base + 40) (.reg r_n))))))

/-- The graph copy preserves all caller arrays and registers and gives the representation
needed by every subwall search. Its cost is linear in vertices plus adjacency entries. -/
theorem f92GraphCopyProg_exec {w n : ℕ} (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (aS aE aEnt r_n base : ℕ) (hSbase : aS < base) (hEbase : aE < base)
    (hEntbase : aEnt < base) (hrbase : r_n < base)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) {s : State}
    (hadj : IsAdjList G aS aE aEnt lists s) (hent : (s.arrs aEnt).length < 2 ^ w)
    (hrn : s.regs r_n = n) :
    ∃ s' t, Exec w (f92GraphCopyProg aS aE aEnt r_n base) s s' t ∧
      t ≤ 30 + 34 * n + 17 * (s.arrs aEnt).length ∧
      IsAdjList G (base + 40) (base + 41) (base + 42) lists s' ∧
      s'.regs (base + 40) = n ∧ (s'.arrs (base + 42)).length = (s.arrs aEnt).length ∧
      (∀ b < base, s'.arrs b = s.arrs b) ∧
      (∀ q < base, s'.regs q = s.regs q) := by
  let M := (s.arrs aEnt).length
  let s₁ := s.setReg (base + 75) M
  have hex₁ : Exec w (.assign (base + 75) (.len aEnt)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, M, hent])
  have hSlen : (s.arrs aS).length < 2 ^ w := by rw [hadj.1.1]; exact hn
  have hElen : (s.arrs aE).length < 2 ^ w := by rw [hadj.1.2.1]; exact hn
  obtain ⟨s₂, t₂, hex₂, ht₂, hS₂, harr₂, hreg₂⟩ :=
    f92CopyBoundedProg_exec aS (base + 40) (base + 75) (base + 80) M
      (by omega) (by omega) (s.arrs aS) hw hent hSlen (s := s₁) rfl (by simp [s₁])
  obtain ⟨s₃, t₃, hex₃, ht₃, hE₃, harr₃, hreg₃⟩ :=
    f92CopyBoundedProg_exec aE (base + 41) (base + 75) (base + 80) M
      (by omega) (by omega) (s.arrs aE) hw hent hElen (s := s₂)
      (harr₂ aE (by omega)) (by rw [hreg₂ (base + 75) (by omega)]; simp [s₁])
  let s₄ := s₃.setReg (base + 75) n
  have hrn₃ : s₃.regs r_n = n := by
    rw [hreg₃ r_n (by omega), hreg₂ r_n (by omega)]
    simp [s₁, State.setReg, show r_n ≠ base + 75 by omega, hrn]
  have hex₄ : Exec w (.assign (base + 75) (.reg r_n)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrn₃, hn])
  obtain ⟨s₅, t₅, hex₅, ht₅, hEnt₅, harr₅, hreg₅⟩ :=
    f92CopyBoundedProg_exec aEnt (base + 42) (base + 75) (base + 80) n
      (by omega) (by omega) (s.arrs aEnt) hw hn hent (s := s₄)
      (by change s₃.arrs aEnt = s.arrs aEnt; rw [harr₃ aEnt (by omega), harr₂ aEnt (by omega)]; rfl)
      (by simp [s₄])
  have hrn₅ : s₅.regs r_n = n := by
    rw [hreg₅ r_n (by omega)]
    simp [s₄, State.setReg, show r_n ≠ base + 75 by omega, hrn₃]
  let s₆ := s₅.setReg (base + 40) n
  have hex₆ : Exec w (.assign (base + 40) (.reg r_n)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrn₅, hn])
  have hS₆ : s₆.arrs (base + 40) = (s.arrs aS).map (fun v => min v M) := by
    rw [State.setReg_arrs, harr₅ (base + 40) (by omega), State.setReg_arrs, harr₃ (base + 40) (by omega)]
    exact hS₂
  have hE₆ : s₆.arrs (base + 41) = (s.arrs aE).map (fun v => min v M) := by
    rw [State.setReg_arrs, harr₅ (base + 41) (by omega), State.setReg_arrs]
    exact hE₃
  have hEnt₆ : s₆.arrs (base + 42) = (s.arrs aEnt).map (fun v => min v n) := hEnt₅
  have hex : Exec w (f92GraphCopyProg aS aE aEnt r_n base) s s₆
      (2 + (t₂ + (t₃ + (2 + (t₅ + 2))))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆))))
  refine ⟨s₆, _, hex, ?_, f92AdjList_of_bounded_copies hadj hS₆ hE₆ hEnt₆,
    by simp [s₆], by rw [hEnt₆, List.length_map], ?_, ?_⟩
  · rw [hadj.1.1] at ht₂
    rw [hadj.1.2.1] at ht₃
    omega
  · intro b hbb
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [f92GraphCopyProg, f92CopyBoundedProg, forUp, Cmd.writtenArrs,
        show b ≠ base + 40 by omega, show b ≠ base + 41 by omega, show b ≠ base + 42 by omega])
  · intro q hqb
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [f92GraphCopyProg, f92CopyBoundedProg, forUp, Cmd.writtenRegs,
        show q ≠ base + 40 by omega, show q ≠ base + 75 by omega,
        show q ≠ base + 80 by omega, show q ≠ base + 81 by omega])

end GraphMinor.Compute.Alg92
