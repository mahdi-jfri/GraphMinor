module

public import GraphMinor.Compute.Algorithm81Aux
public import GraphMinor.Compute.Bridge13
public import GraphMinor.Compute.Cited
public import GraphMinor.Compute.Parse
public import Mathlib.Tactic.Ring

/-!
# Graph Minors XIII, (8.1): Testing if a Society Has a Cross in `O(vε)` Time

This file completes the Word RAM implementation and verification of Algorithm (8.1) from
Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*, Section 8, page 93:

* `matToAdjListRegProg` and `matToAdjListRegProg_exec`: builds CSR adjacency lists
  `(a_start, a_end, a_entries)` from an `N × N` adjacency matrix `a_mat` when `N` is held in
  register `r_N`, in `O(N²)` steps.
* `buildAuxMatProg` and `buildAuxMatProg_exec`: given a society `(G, Ω)` in `inArr` with
  `|Ω̄| ≥ 4`, builds the `N × N` adjacency matrix (`N = |V(G)| + |Ω̄|`) of `G ∪ H`
  (`auxGraph81 G omega`) in array `28` in `O(N² + m)` steps.
* `alg81WritePathsOutProg` and `alg81WritePathsOutProg_exec`: serializes the two vertex-disjoint
  paths returned by Shiloach's algorithm in arrays `33` and `34` into `outArr`.
* `alg81Prog`, `decAlg81Out`, `IsValidAlg81Output`, and `algorithm_8_1`: end-to-end `O(vε)` Word
  RAM program for (8.1), taking `(hShiloach : Shiloach80Statement)` as hypothesis.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Size and Edge-Count Bounds for `auxGraph81` -/

/-- The number of edges of `auxGraph81 G omega` is at most `G.edgeFinset.card + 3 * omega.length`. -/
theorem card_edgeFinset_auxGraph81_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (omega : List (Fin n)) :
    (auxGraph81 G omega).edgeFinset.card ≤ G.edgeFinset.card + 3 * omega.length := by
  classical
  let k := omega.length
  let E_G : Finset (Sym2 (Fin (n + k))) :=
    G.edgeFinset.image (Sym2.map (inGVert k))
  let E_C1 : Finset (Sym2 (Fin (n + k))) :=
    (Finset.univ : Finset (Fin k)).image (fun i =>
      s(c1Vert n k i.1 i.2,
        c1Vert n k ((i.1 + 1) % k) (Nat.mod_lt _ (Nat.pos_of_ne_zero (by have := i.2; omega)))))
  let E_rung : Finset (Sym2 (Fin (n + k))) :=
    (Finset.univ : Finset (Fin k)).image (fun i =>
      s(c1Vert n k i.1 i.2, inGVert k (omega[i.1]'i.2)))
  let E_C2 : Finset (Sym2 (Fin (n + k))) :=
    (Finset.univ : Finset (Fin k)).image (fun i =>
      s(inGVert k (omega[i.1]'i.2),
        inGVert k (omega[(i.1 + 1) % k]'(Nat.mod_lt _ (Nat.pos_of_ne_zero (by have := i.2; omega))))))
  have hsub : (auxGraph81 G omega).edgeFinset ⊆ E_G ∪ E_C1 ∪ E_rung ∪ E_C2 := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at he
      rcases he with ⟨_, hadj⟩
      simp only [Finset.mem_union, E_G, E_C1, E_rung, E_C2, Finset.mem_image, Finset.mem_univ,
        true_and]
      rcases hadj with ⟨hx, hy, hG⟩ | ⟨i, h1⟩ | ⟨i, h2⟩ | ⟨i, hpos, h3⟩
      · left; left; left
        refine ⟨s(⟨x.1, hx⟩, ⟨y.1, hy⟩), SimpleGraph.mem_edgeFinset.mpr hG, ?_⟩
        rfl
      · left; left; right
        refine ⟨i, ?_⟩
        rcases h1 with ⟨hx, hy⟩ | ⟨hy, hx⟩
        · have hx' : x = c1Vert n k i.1 i.2 := Fin.ext hx
          have hy' : y = c1Vert n k ((i.1 + 1) % k)
              (Nat.mod_lt _ (Nat.pos_of_ne_zero (by have := i.2; omega))) := Fin.ext hy
          rw [hx', hy']
        · have hy' : y = c1Vert n k i.1 i.2 := Fin.ext hy
          have hx' : x = c1Vert n k ((i.1 + 1) % k)
              (Nat.mod_lt _ (Nat.pos_of_ne_zero (by have := i.2; omega))) := Fin.ext hx
          rw [hx', hy', Sym2.eq_swap]
      · left; right
        refine ⟨i, ?_⟩
        rcases h2 with ⟨hx, hy⟩ | ⟨hy, hx⟩
        · have hx' : x = c1Vert n k i.1 i.2 := Fin.ext hx
          have hy' : y = inGVert k (omega[i.1]'i.2) := Fin.ext hy
          rw [hx', hy']
        · have hy' : y = c1Vert n k i.1 i.2 := Fin.ext hy
          have hx' : x = inGVert k (omega[i.1]'i.2) := Fin.ext hx
          rw [hx', hy', Sym2.eq_swap]
      · right
        refine ⟨i, ?_⟩
        rcases h3 with ⟨hx, hy⟩ | ⟨hy, hx⟩
        · have hx' : x = inGVert k (omega[i.1]'i.2) := Fin.ext hx
          have hy' : y = inGVert k (omega[(i.1 + 1) % k]'(Nat.mod_lt _ hpos)) := Fin.ext hy
          rw [hx', hy']
        · have hy' : y = inGVert k (omega[i.1]'i.2) := Fin.ext hy
          have hx' : x = inGVert k (omega[(i.1 + 1) % k]'(Nat.mod_lt _ hpos)) := Fin.ext hx
          rw [hx', hy', Sym2.eq_swap]
  have hcard_G : E_G.card ≤ G.edgeFinset.card := Finset.card_image_le
  have hcard_C1 : E_C1.card ≤ k := by
    calc E_C1.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
      _ = k := by simp
  have hcard_rung : E_rung.card ≤ k := by
    calc E_rung.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
      _ = k := by simp
  have hcard_C2 : E_C2.card ≤ k := by
    calc E_C2.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
      _ = k := by simp
  have hcard_le := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (E_G ∪ E_C1 ∪ E_rung) E_C2
  have hu2 := Finset.card_union_le (E_G ∪ E_C1) E_rung
  have hu3 := Finset.card_union_le E_G E_C1
  omega

/-- The problem size `(N + 1) * (|E(G ∪ H)| + N + 1)` passed to Shiloach's algorithm on
`auxGraph81 x.G x.omega` is at most `10 * alg81Size x`. -/
theorem auxGraph81_shiloachSize_le (x : Alg81Input) :
    (x.n + x.omega.length + 1) *
      ((auxGraph81 x.G x.omega).edgeFinset.card + (x.n + x.omega.length) + 1) ≤
      10 * alg81Size x := by
  have hk_le : x.omega.length ≤ x.n := length_omega_le_n x.nodup_omega
  have he_le := card_edgeFinset_auxGraph81_le x.G x.omega
  have h1 : x.n + x.omega.length + 1 ≤ 2 * (x.n + 1) := by omega
  have h2 : (auxGraph81 x.G x.omega).edgeFinset.card + (x.n + x.omega.length) + 1 ≤
      5 * (x.G.edgeFinset.card + x.n + 1) := by omega
  calc (x.n + x.omega.length + 1) *
        ((auxGraph81 x.G x.omega).edgeFinset.card + (x.n + x.omega.length) + 1)
    _ ≤ (2 * (x.n + 1)) * (5 * (x.G.edgeFinset.card + x.n + 1)) := Nat.mul_le_mul h1 h2
    _ = 10 * ((x.n + 1) * (x.G.edgeFinset.card + x.n + 1)) := by ring
    _ = 10 * alg81Size x := rfl

/-! ### Section 2: Register-Parameterized Adjacency Matrix to Adjacency List (`matToAdjListRegProg`) -/

/-- Build CSR adjacency lists `(a_start, a_end, a_entries)` from the `N × N` adjacency matrix
`a_mat` when `N` is stored in register `r_N`, using scratch registers `r_u, r_v, r_cnt, r_val`. -/
def matToAdjListRegProg (r_N : Reg) (a_mat a_start a_end a_entries : Arr)
    (r_u r_v r_cnt r_val : Reg) : Cmd :=
  .seq (.alloc a_start (.reg r_N))
    (.seq (.alloc a_end (.reg r_N))
      (.seq (.alloc a_entries (.op .mul (.reg r_N) (.reg r_N)))
        (.seq (.assign r_u (.const 0))
          (forUp r_u (.reg r_N)
            (.seq (.assign r_cnt (.op .mul (.reg r_u) (.reg r_N)))
              (.seq (.write a_start (.reg r_u) (.reg r_cnt))
                (.seq (.write a_end (.reg r_u) (.reg r_cnt))
                  (.seq (.assign r_v (.const 0))
                    (forUp r_v (.reg r_N)
                      (.seq (.assign r_val
                          (.read a_mat (.op .add (.op .mul (.reg r_u) (.reg r_N)) (.reg r_v))))
                        (.ite (.reg r_val)
                          (listAppend a_end a_entries r_u r_cnt (.reg r_v))
                          .skip)))))))))))

private lemma isListAt_preserve_prev_reg {n : ℕ} {a_start a_end a_entries : ℕ}
    (hne_se : a_start ≠ a_end) (hne_sent : a_start ≠ a_entries) (hne_eent : a_end ≠ a_entries)
    {u' u cnt val_end val_ent : ℕ} {l : List ℕ} {s : State}
    (hu' : u' < u) (hlen_l : l.length ≤ n) (hcnt : u * n ≤ cnt)
    (hlist : IsListAt a_start a_end a_entries u' (u' * n) (u' * n + l.length) l s) :
    IsListAt a_start a_end a_entries u' (u' * n) (u' * n + l.length) l
      ((s.writeArr a_entries cnt val_ent).writeArr a_end u val_end) := by
  have hne_se' : (a_start : Arr) ≠ a_end := by omega
  have hne_sent' : (a_start : Arr) ≠ a_entries := by omega
  have hne_eent' : (a_end : Arr) ≠ a_entries := by omega
  rcases hlist with ⟨hu'_st, hu'_en, hen_ent, hdiff, hst, hen, hle, helem⟩
  refine ⟨by simpa using hu'_st,
    by simpa using hu'_en,
    by simpa using hen_ent,
    hdiff,
    by simpa [hne_se', hne_sent'] using hst,
    ?_, hle, ?_⟩
  · simp only [State.writeArr_arrs_self, State.writeArr_arrs_ne _ _ _ hne_eent']
    rw [List.getElem_set_ne (by omega)]
    exact hen
  · intro k hk
    simp only [State.writeArr_arrs_ne _ _ _ hne_eent'.symm, State.writeArr_arrs_self]
    have hk_lt_n : k < n := by omega
    have hlt_un : u' * n + k < u * n := by
      have h1 : (u' + 1) * n ≤ u * n := Nat.mul_le_mul_right n hu'
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    rw [List.getElem_set_ne (by omega)]
    exact helem k hk

/-- Specification for `matToAdjListRegProg` on `r_N = 4`, `a_mat = 28`, `a_start = 30`,
`a_end = 31`, `a_entries = 32`, and scratch registers `5, 6, 7, 8`. -/
theorem matToAdjListRegProg_exec {w n : ℕ} (G : SimpleGraph (Fin n)) {s₀ : State}
    (hw : 1 < 2 ^ w) (hnn_w : n * n < 2 ^ w)
    (hmat₀ : IsAdjMatrix G 28 s₀) (hrN₀ : s₀.regs 4 = n) :
    ∃ s' t,
      Exec w (matToAdjListRegProg 4 28 30 31 32 5 6 7 8) s₀ s' t ∧
      t ≤ 26 * (n * n) + 24 * n + 12 ∧
      IsAdjList G 30 31 32 (adjListOf G) s' ∧
      (s'.arrs 32).length = n * n ∧
      (∀ r : ℕ, r < 5 → s'.regs r = s₀.regs r) ∧
      (∀ a : ℕ, a < 30 → s'.arrs a = s₀.arrs a) := by
  have hn_le_nn : n ≤ n * n := Nat.le_mul_self n
  have hn_w : n < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  -- 1. Allocations of 30, 31, 32 and r_5 := 0
  have hn_eval₀ : (Expr.reg 4).eval w s₀ = some n := by simp [Expr.eval, checkWord, hrN₀, hn_w]
  let s₁ := s₀.setArr 30 (List.replicate n 0)
  have hex₁ : Exec w (.alloc 30 (.reg 4)) s₀ s₁ (1 + n) := .alloc hn_eval₀
  have hn_eval₁ : (Expr.reg 4).eval w s₁ = some n := by simp [s₁, Expr.eval, checkWord, hrN₀, hn_w]
  let s₂ := s₁.setArr 31 (List.replicate n 0)
  have hex₂ : Exec w (.alloc 31 (.reg 4)) s₁ s₂ (1 + n) := .alloc hn_eval₁
  have hnn_eval₂ : (Expr.op .mul (.reg 4) (.reg 4)).eval w s₂ = some (n * n) := by
    simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrN₀, hn_w, hnn_w]
  let s₃ := s₂.setArr 32 (List.replicate (n * n) 0)
  have hex₃ : Exec w (.alloc 32 (.op .mul (.reg 4) (.reg 4))) s₂ s₃ (3 + n * n) := .alloc hnn_eval₂
  have h0_eval₃ : (Expr.const 0).eval w s₃ = some 0 := by simp [checkWord, h0_w]
  let s₄ := s₃.setReg 5 0
  have hex₄ : Exec w (.assign 5 (.const 0)) s₃ s₄ 2 := .assign h0_eval₃
  -- Outer loop invariant
  let OuterInv (u : ℕ) (s : State) : Prop :=
    IsAdjMatrix G 28 s ∧
    (s.arrs 30).length = n ∧
    (s.arrs 31).length = n ∧
    (s.arrs 32).length = n * n ∧
    s.regs 4 = n ∧
    s.regs 5 = u ∧
    (∀ r : ℕ, r < 5 → s.regs r = s₀.regs r) ∧
    (∀ a : ℕ, a < 30 → s.arrs a = s₀.arrs a) ∧
    ∀ (u' : Fin n), u'.1 < u →
      IsListAt 30 31 32 u'.1 (u'.1 * n)
        (u'.1 * n + (adjListOf G u').length) (adjListOf G u') s
  have hOuter₀ : OuterInv 0 s₄ := by
    refine ⟨hmat₀.of_arrs_eq (by simp [s₄, s₃, s₂, s₁]),
      by simp [s₄, s₃, s₂, s₁],
      by simp [s₄, s₃, s₂],
      by simp [s₄, s₃],
      by simp [s₄, s₃, s₂, s₁, hrN₀],
      by simp [s₄],
      fun r hr => by
        have hr5 : (r : Reg) ≠ 5 := by dsimp [Reg]; omega
        simp [s₄, s₃, s₂, s₁, State.setReg, hr5],
      fun a ha => by
        have ha30 : (a : Arr) ≠ 30 := by dsimp [Arr]; omega
        have ha31 : (a : Arr) ≠ 31 := by dsimp [Arr]; omega
        have ha32 : (a : Arr) ≠ 32 := by dsimp [Arr]; omega
        simp [s₄, s₃, s₂, s₁, State.setArr, ha30, ha31, ha32],
      fun u' hu' => by omega⟩
  have hOuterLoop :
      ⦃OuterInv 0⦄[w]
        forUp 5 (.reg 4)
          (.seq (.assign 7 (.op .mul (.reg 5) (.reg 4)))
            (.seq (.write 30 (.reg 5) (.reg 7))
              (.seq (.write 31 (.reg 5) (.reg 7))
                (.seq (.assign 6 (.const 0))
                  (forUp 6 (.reg 4)
                    (.seq (.assign 8
                        (.read 28 (.op .add (.op .mul (.reg 5) (.reg 4)) (.reg 6))))
                      (.ite (.reg 8)
                        (listAppend 31 32 5 7 (.reg 6))
                        .skip)))))))
      ⦃OuterInv n⦄ ≤ fun _ => 3 + n * (7 + (15 + 25 * n)) := by
    apply Triple.forUp_const OuterInv n (15 + 25 * n) hw hn_w
    · intro u _ s ⟨_, _, _, _, hr4, hr5, _, _, _⟩
      exact ⟨hr5, by simp [Expr.eval, checkWord, hr4, hn_w]⟩
    · intro u hu s_u ⟨hmat_u, hlen_s_u, hlen_e_u, hlen_ent_u, hr4_u, hru_u, hregs_u, harrs_u, hprev_u⟩
      let uFin : Fin n := ⟨u, hu⟩
      have hu_w : u < 2 ^ w := by omega
      have hun_le_nn : u * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
      have hun_w : u * n < 2 ^ w := by omega
      -- 1. r_7 := r_5 * r_4 (cost 4)
      have hmul_eval : (Expr.op .mul (.reg 5) (.reg 4)).eval w s_u = some (u * n) := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru_u, hr4_u, hu_w, hn_w, hun_w]
      let sa₁ := s_u.setReg 7 (u * n)
      have hexa₁ : Exec w (.assign 7 (.op .mul (.reg 5) (.reg 4))) s_u sa₁ 4 :=
        .assign hmul_eval
      -- 2. 30[r_5] := r_7 (cost 3)
      have hru_sa₁ : (Expr.reg 5).eval w sa₁ = some u := by
        simp [sa₁, Expr.eval, checkWord, hru_u, hu_w]
      have hrcnt_sa₁ : (Expr.reg 7).eval w sa₁ = some (u * n) := by
        simp [sa₁, Expr.eval, checkWord, hun_w]
      let sa₂ := sa₁.writeArr 30 u (u * n)
      have hexa₂ : Exec w (.write 30 (.reg 5) (.reg 7)) sa₁ sa₂ 3 :=
        .write hru_sa₁ hrcnt_sa₁ (by simp [sa₁, hlen_s_u, hu])
      -- 3. 31[r_5] := r_7 (cost 3)
      have hru_sa₂ : (Expr.reg 5).eval w sa₂ = some u := by
        simp [sa₂, sa₁, Expr.eval, checkWord, hru_u, hu_w]
      have hrcnt_sa₂ : (Expr.reg 7).eval w sa₂ = some (u * n) := by
        simp [sa₂, sa₁, Expr.eval, checkWord, hun_w]
      let sa₃ := sa₂.writeArr 31 u (u * n)
      have hexa₃ : Exec w (.write 31 (.reg 5) (.reg 7)) sa₂ sa₃ 3 :=
        .write hru_sa₂ hrcnt_sa₂ (by simp [sa₂, sa₁, hlen_e_u, hu])
      -- 4. r_6 := 0 (cost 2)
      have h0_sa₃ : (Expr.const 0).eval w sa₃ = some 0 := by simp [checkWord, h0_w]
      let sa₄ := sa₃.setReg 6 0
      have hexa₄ : Exec w (.assign 6 (.const 0)) sa₃ sa₄ 2 := .assign h0_sa₃
      -- Inner loop invariant over v ≤ n
      let InnerInv (v : ℕ) (s : State) : Prop :=
        IsAdjMatrix G 28 s ∧
        (s.arrs 30).length = n ∧
        (s.arrs 31).length = n ∧
        (s.arrs 32).length = n * n ∧
        s.regs 4 = n ∧
        s.regs 5 = u ∧
        s.regs 6 = v ∧
        s.regs 7 = u * n + (adjListUpTo G uFin v).length ∧
        (∀ r : ℕ, r < 5 → s.regs r = s₀.regs r) ∧
        (∀ a : ℕ, a < 30 → s.arrs a = s₀.arrs a) ∧
        IsListAt 30 31 32 u (u * n)
          (u * n + (adjListUpTo G uFin v).length) (adjListUpTo G uFin v) s ∧
        ∀ (u' : Fin n), u'.1 < u →
          IsListAt 30 31 32 u'.1 (u'.1 * n)
            (u'.1 * n + (adjListOf G u').length) (adjListOf G u') s
      have hInner₀ : InnerInv 0 sa₄ := by
        refine ⟨hmat_u.of_arrs_eq (by simp [sa₄, sa₃, sa₂, sa₁]),
          by simp [sa₄, sa₃, sa₂, sa₁, hlen_s_u],
          by simp [sa₄, sa₃, sa₂, sa₁, hlen_e_u],
          by simp [sa₄, sa₃, sa₂, sa₁, hlen_ent_u],
          by simp [sa₄, sa₃, sa₂, sa₁, hr4_u],
          by simp [sa₄, sa₃, sa₂, sa₁, hru_u],
          by simp [sa₄],
          by simp [sa₄, sa₃, sa₂, sa₁, adjListUpTo],
          fun r hr => by
            have hr6 : (r : Reg) ≠ 6 := by dsimp [Reg]; omega
            have hr7 : (r : Reg) ≠ 7 := by dsimp [Reg]; omega
            rw [show sa₄.regs r = s_u.regs r by simp [sa₄, sa₃, sa₂, sa₁, State.setReg, hr6, hr7]]
            exact hregs_u r hr,
          fun a ha => by
            have ha30 : (a : Arr) ≠ 30 := by dsimp [Arr]; omega
            have ha31 : (a : Arr) ≠ 31 := by dsimp [Arr]; omega
            simp [sa₄, sa₃, sa₂, sa₁, ha30, ha31, harrs_u a ha],
          ?_, ?_⟩
        · refine ⟨by simp [sa₄, sa₃, sa₂, sa₁, hlen_s_u, hu],
            by simp [sa₄, sa₃, sa₂, sa₁, hlen_e_u, hu],
            by simp [sa₄, sa₃, sa₂, sa₁, hlen_ent_u, adjListUpTo, hun_le_nn],
            by simp [adjListUpTo],
            ?_, ?_, by simp [adjListUpTo], fun k hk => by simp [adjListUpTo] at hk⟩
          · simp only [sa₄, sa₃, sa₂, sa₁, State.setReg_arrs,
              State.writeArr_arrs_ne _ _ _ (by decide : (30 : Arr) ≠ 31), State.writeArr_arrs_self]
            exact List.getElem_set_self (by simp [hlen_s_u, hu])
          · simp only [sa₄, sa₃, sa₂, sa₁, State.setReg_arrs, State.writeArr_arrs_self]
            exact List.getElem_set_self (by simp [hlen_e_u, hu])
        · intro u' hu'
          rcases hprev_u u' hu' with ⟨hu'_st, hu'_en, hen_ent, hdiff, hst, hen, hle, helem⟩
          refine ⟨by simpa [sa₄, sa₃, sa₂, sa₁] using hu'_st,
            by simpa [sa₄, sa₃, sa₂, sa₁] using hu'_en,
            by simpa [sa₄, sa₃, sa₂, sa₁] using hen_ent,
            hdiff, ?_, ?_, hle,
            fun k hk => by simpa [sa₄, sa₃, sa₂, sa₁] using helem k hk⟩
          · simp only [sa₄, sa₃, sa₂, sa₁, State.setReg_arrs,
              State.writeArr_arrs_ne _ _ _ (by decide : (30 : Arr) ≠ 31), State.writeArr_arrs_self]
            rw [List.getElem_set_ne (by omega)]
            exact hst
          · simp only [sa₄, sa₃, sa₂, sa₁, State.setReg_arrs, State.writeArr_arrs_self,
              State.writeArr_arrs_ne _ _ _ (by decide : (31 : Arr) ≠ 30)]
            rw [List.getElem_set_ne (by omega)]
            exact hen
      have hInnerLoop :
          ⦃InnerInv 0⦄[w]
            forUp 6 (.reg 4)
              (.seq (.assign 8
                  (.read 28 (.op .add (.op .mul (.reg 5) (.reg 4)) (.reg 6))))
                (.ite (.reg 8)
                  (listAppend 31 32 5 7 (.reg 6))
                  .skip))
          ⦃InnerInv n⦄ ≤ fun _ => 3 + n * (7 + 18) := by
        apply Triple.forUp_const InnerInv n 18 hw hn_w
        · intro v _ s ⟨_, _, _, _, hr4, _, hrv, _, _, _, _, _⟩
          exact ⟨hrv, by simp [Expr.eval, checkWord, hr4, hn_w]⟩
        · intro v hv s_v ⟨hmat_v, hlen_s_v, hlen_e_v, hlen_ent_v, hr4_v, hru_v, hrv_v, hrcnt_v,
            hregs_v, harrs_v, hlist_v, hprev_v⟩
          let vFin : Fin n := ⟨v, hv⟩
          have hv_w : v < 2 ^ w := by omega
          have hidx_lt : u * n + v < n * n := mul_add_lt_mul hu hv
          have hidx_w : u * n + v < 2 ^ w := by omega
          rcases hmat_v with ⟨hlen_mat, hmat_entries⟩
          obtain ⟨hmat_iff, hmat_le1⟩ := hmat_entries uFin vFin
          let mval := (s_v.arrs 28)[u * n + v]'(by rw [hlen_mat]; exact hidx_lt)
          have hmval_le1 : mval ≤ 1 := hmat_le1
          have hmval_w : mval < 2 ^ w := by omega
          have hread_mat :
              (Expr.read 28 (.op .add (.op .mul (.reg 5) (.reg 4)) (.reg 6))).eval w s_v =
                some mval := by
            have hidx_a : u * n + v < (s_v.arrs 28).length := by rw [hlen_mat]; exact hidx_lt
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru_v, hr4_v, hu_w, hn_w, hun_w,
              hrv_v, hv_w, hidx_w, hidx_a, mval, hmval_w]
          let sb₁ := s_v.setReg 8 mval
          have hexb₁ : Exec w
              (.assign 8 (.read 28 (.op .add (.op .mul (.reg 5) (.reg 4)) (.reg 6))))
              s_v sb₁ 7 := .assign hread_mat
          have hcond_sb₁ : (Expr.reg 8).eval w sb₁ = some mval := by
            simp [sb₁, Expr.eval, checkWord, hmval_w]
          have hlen_cur_le : (adjListUpTo G uFin v).length ≤ v := adjListUpTo_length_le G uFin v
          have hcnt_lt_nn : u * n + (adjListUpTo G uFin v).length < n * n := by
            have := mul_add_lt_mul hu hv
            omega
          have hcnt1_w : u * n + (adjListUpTo G uFin v).length + 1 < 2 ^ w := by omega
          by_cases hadj_uv : G.Adj uFin vFin
          · have hmval_ne : mval ≠ 0 := hmat_iff.mpr hadj_uv
            have hlist_sb₁ : IsListAt 30 31 32 u (u * n)
                (u * n + (adjListUpTo G uFin v).length) (adjListUpTo G uFin v) sb₁ := hlist_v
            rcases Triple.listAppend_spec 30 31 32 5 7 (.reg 6)
                u (u * n) (adjListUpTo G uFin v) v
                (by decide) (by decide) (by decide) (by decide)
                hw hu_w hcnt1_w sb₁
                ⟨hlist_sb₁,
                  by simp [sb₁, hru_v],
                  by simp [sb₁, hrcnt_v],
                  by simp [sb₁, hlen_ent_v, hcnt_lt_nn],
                  by simp [sb₁, Expr.eval, checkWord, hrv_v, hv_w]⟩ with
              ⟨sb₂, t_app, hex_app, ht_app, hlist_sb₂, hru_sb₂, hrcnt_sb₂⟩
            dsimp [Expr.cost] at ht_app
            have hex_ite : Exec w
                (.ite (.reg 8) (listAppend 31 32 5 7 (.reg 6)) .skip)
                sb₁ sb₂ (1 + t_app) := .ite_true hcond_sb₁ hmval_ne hex_app
            refine ⟨sb₂, 7 + (1 + t_app), .seq hexb₁ hex_ite, by dsimp only; omega, ?_, ?_⟩
            · have hadj_step := adjListUpTo_succ_pos hv hadj_uv
              dsimp only [InnerInv]
              rw [hadj_step]
              cases hex_app with
              | seq hex_w1 hex_rest =>
                cases hex_rest with
                | seq hex_inc hex_w2 =>
                  cases hex_w1 with
                  | write hidx1 hval1 _ =>
                    cases hex_inc with
                    | assign hinc1 =>
                      cases hex_w2 with
                      | write hidx2 hval2 _ =>
                        simp [sb₁, Expr.eval, checkWord, hrcnt_v,
                          show u * n + (adjListUpTo G uFin v).length < 2 ^ w by omega] at hidx1
                        subst hidx1
                        simp [sb₁, Expr.eval, checkWord, hru_v, hu_w] at hidx2
                        subst hidx2
                        have hmat_orig : IsAdjMatrix G 28 s_v := ⟨hlen_mat, hmat_entries⟩
                        refine ⟨hmat_orig.of_arrs_eq (by simp [sb₁]),
                          by simp [sb₁, hlen_s_v],
                          by simp [sb₁, hlen_e_v],
                          by simp [sb₁, hlen_ent_v],
                          by simp [sb₁, hr4_v],
                          by simp [hru_sb₂],
                          by simp,
                          by simp [hrcnt_sb₂],
                          fun r hr => by
                            have hr6 : (r : Reg) ≠ 6 := by dsimp [Reg]; omega
                            have hr7 : (r : Reg) ≠ 7 := by dsimp [Reg]; omega
                            have hr8 : (r : Reg) ≠ 8 := by dsimp [Reg]; omega
                            simp only [sb₁, State.writeArr_regs, State.setReg,
                              Function.update_of_ne hr6, Function.update_of_ne hr7,
                              Function.update_of_ne hr8]
                            exact hregs_v r hr,
                          fun a ha => by
                            have ha31 : (a : Arr) ≠ 31 := by dsimp [Arr]; omega
                            have ha32 : (a : Arr) ≠ 32 := by dsimp [Arr]; omega
                            simp [sb₁, ha31, ha32, harrs_v a ha],
                          hlist_sb₂.of_arrs_eq rfl rfl rfl,
                          fun u' hu' => ?_⟩
                        have hlen_u' : (adjListOf G u').length ≤ n := adjListUpTo_length_le G u' n
                        exact (isListAt_preserve_prev_reg (by decide) (by decide) (by decide)
                          hu' hlen_u' (by omega) (hprev_v u' hu')).of_arrs_eq rfl rfl rfl
            · have hnot_rv : (6 : Reg) ∉ (listAppend 31 32 5 7 (.reg 6)).writtenRegs := by
                simp [listAppend, Cmd.writtenRegs]
              have hrv_eq := Exec.regs_eq_of_not_mem_writtenRegs hex_app hnot_rv
              simp [hrv_eq, sb₁, hrv_v]
          · have hmval_eq0 : mval = 0 := by
              by_contra hne0
              exact hadj_uv (hmat_iff.mp hne0)
            rw [hmval_eq0] at hcond_sb₁
            have hex_ite : Exec w
                (.ite (.reg 8) (listAppend 31 32 5 7 (.reg 6)) .skip)
                sb₁ sb₁ (1 + 1) := .ite_false hcond_sb₁ (.skip sb₁)
            refine ⟨sb₁, 7 + (1 + 1), .seq hexb₁ hex_ite, by dsimp only; omega, ?_,
              by simp [sb₁, hrv_v]⟩
            have hadj_step := adjListUpTo_succ_neg hv hadj_uv
            dsimp only [InnerInv]
            rw [hadj_step]
            refine ⟨⟨hlen_mat, hmat_entries⟩, hlen_s_v, hlen_e_v, hlen_ent_v,
              by simp [sb₁, hr4_v],
              by simp [sb₁, hru_v],
              by simp,
              by simp [sb₁, hrcnt_v],
              fun r hr => by
                have hr6 : (r : Reg) ≠ 6 := by dsimp [Reg]; omega
                have hr8 : (r : Reg) ≠ 8 := by dsimp [Reg]; omega
                simp only [sb₁, State.setReg, Function.update_of_ne hr6, Function.update_of_ne hr8]
                exact hregs_v r hr,
              harrs_v,
              hlist_v, hprev_v⟩
      rcases hInnerLoop sa₄ hInner₀ with
        ⟨s_end, t_in, hex_in, ht_in, hmat_end, hlen_s_end, hlen_e_end, hlen_ent_end,
          hr4_end, hru_end, _, _, hregs_end, harrs_end, hlist_end, hprev_end⟩
      dsimp only at ht_in
      refine ⟨s_end, 4 + (3 + (3 + (2 + t_in))),
        .seq hexa₁ (.seq hexa₂ (.seq hexa₃ (.seq hexa₄ hex_in))),
        by dsimp only; omega, ?_, hru_end⟩
      refine ⟨hmat_end, hlen_s_end, hlen_e_end, hlen_ent_end,
        by simp [hr4_end], by simp,
        fun r hr => by
          have hr5 : (r : Reg) ≠ 5 := by dsimp [Reg]; omega
          simp only [State.setReg, Function.update_of_ne hr5]
          exact hregs_end r hr,
        harrs_end, fun u' hu' => ?_⟩
      by_cases hu'_eq : u'.1 = u
      · have hu'_fin : u' = uFin := Fin.ext hu'_eq
        subst hu'_fin
        exact hlist_end.of_arrs_eq rfl rfl rfl
      · exact (hprev_end u' (by omega)).of_arrs_eq rfl rfl rfl
  rcases hOuterLoop s₄ hOuter₀ with
    ⟨s_final, t_out, hex_out, ht_out, _, hlen_s_final, hlen_e_final, hlen_ent_final,
      _, _, hregs_final, harrs_final, hlists_final⟩
  dsimp only at ht_out
  refine ⟨s_final, (1 + n) + ((1 + n) + ((3 + n * n) + (2 + t_out))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex_out))), ?_,
    ?_, hlen_ent_final, hregs_final, harrs_final⟩
  · have hmul : n * (7 + (15 + 25 * n)) = n * 22 + n * (25 * n) := by
      have h715 : 7 + (15 + 25 * n) = 22 + 25 * n := by omega
      rw [h715, Nat.mul_add]
    have hmul2 : n * (25 * n) = 25 * (n * n) := Nat.mul_left_comm n 25 n
    omega
  · refine ⟨⟨hlen_s_final, hlen_e_final, fun u => ?_⟩, isAdjListFamily_adjListOf G⟩
    exact ⟨u.1 * n, u.1 * n + (adjListOf G u).length, hlists_final u u.2⟩

/-! ### Section 3: Building the Adjacency Matrix of `auxGraph81 G omega` (`buildAuxMatProg`) -/

/-- Write a symmetric entry `(r_u, r_v)` with value `1` into the `r_N × r_N` matrix `a_mat`. -/
def writeSymMat (a_mat : Arr) (r_N r_u r_v : Reg) : Cmd :=
  .seq (.write a_mat (.op .add (.op .mul (.reg r_u) (.reg r_N)) (.reg r_v)) (.const 1))
    (.write a_mat (.op .add (.op .mul (.reg r_v) (.reg r_N)) (.reg r_u)) (.const 1))

/-- Loop 1 body of `buildAuxMatProg`: for edge index `r_5 < r_1 = m`, reads
`r_6 := inArr[2 + 2 * r_5]` and `r_7 := inArr[3 + 2 * r_5]` and sets `28[r_6, r_7] := 1` and
`28[r_7, r_6] := 1`. -/
def buildAuxMatEdgeBody : Cmd :=
  .seq (.assign 6 (.read inArr (.op .add (.const 2) (.op .mul (.const 2) (.reg 5)))))
    (.seq (.assign 7 (.read inArr (.op .add (.const 3) (.op .mul (.const 2) (.reg 5)))))
      (writeSymMat 28 4 6 7))

/-- Loop 2 body of `buildAuxMatProg`: for index `r_5 < r_3 = k`, sets
`r_6 := (r_5 + 1) % r_3`, `r_7 := r_0 + r_5` (`c1Vert i`), `r_8 := r_0 + r_6` (`c1Vert ((i+1)%k)`),
`r_9 := inArr[3 + 2 * r_1 + r_5]` (`omega[i]`), `r_10 := inArr[3 + 2 * r_1 + r_6]`
(`omega[(i+1)%k]`), and writes the `C_1` edge, rung edge, and `C_2` edge into matrix `28`. -/
def buildAuxMatCycleBody : Cmd :=
  .seq (.assign 6 (.op .mod (.op .add (.reg 5) (.const 1)) (.reg 3)))
    (.seq (.assign 7 (.op .add (.reg 0) (.reg 5)))
      (.seq (.assign 8 (.op .add (.reg 0) (.reg 6)))
        (.seq (.assign 9 (.read inArr
            (.op .add (.op .add (.const 1) (.reg 2)) (.reg 5))))
          (.seq (.assign 10 (.read inArr
              (.op .add (.op .add (.const 1) (.reg 2)) (.reg 6))))
            (.seq (writeSymMat 28 4 7 8)
              (.seq (writeSymMat 28 4 7 9)
                (writeSymMat 28 4 9 10)))))))

/-- Build the `N × N` adjacency matrix of `auxGraph81 x.G x.omega` in array `28`. -/
def buildAuxMatProg : Cmd :=
  .seq (.alloc 28 (.op .mul (.reg 4) (.reg 4)))
    (.seq (.assign 5 (.const 0))
      (.seq (forUp 5 (.reg 1) buildAuxMatEdgeBody)
        (.seq (.assign 5 (.const 0))
          (forUp 5 (.reg 3) buildAuxMatCycleBody))))

theorem writeSymMat_exec {w N : ℕ} {s : State} {u v : ℕ}
    (r_u r_v : ℕ) (_h4_u : r_u ≠ 4) (_h4_v : r_v ≠ 4) (_huv : r_u ≠ r_v)
    (hw : 1 < 2 ^ w) (hNN_w : N * N < 2 ^ w)
    (hu_lt : u < N) (hv_lt : v < N)
    (hlen : (s.arrs 28).length = N * N)
    (hrN : s.regs 4 = N) (hru : s.regs r_u = u) (hrv : s.regs r_v = v) :
    ∃ s',
      Exec w (writeSymMat 28 4 r_u r_v) s s' 14 ∧
      s'.regs = s.regs ∧
      (∀ a : ℕ, a ≠ 28 → s'.arrs a = s.arrs a) ∧
      ∃ (hlen' : (s'.arrs 28).length = N * N),
        (∀ (x y : Fin N),
          (s'.arrs 28)[x.1 * N + y.1]'(by rw [hlen']; exact mul_add_lt_mul x.2 y.2) ≤ 1 ↔
          ((x.1 = u ∧ y.1 = v) ∨ (x.1 = v ∧ y.1 = u) ∨
            (s.arrs 28)[x.1 * N + y.1]'(by rw [hlen]; exact mul_add_lt_mul x.2 y.2) ≤ 1)) ∧
        (∀ (x y : Fin N),
          (s'.arrs 28)[x.1 * N + y.1]'(by rw [hlen']; exact mul_add_lt_mul x.2 y.2) ≠ 0 ↔
          ((x.1 = u ∧ y.1 = v) ∨ (x.1 = v ∧ y.1 = u) ∨
            (s.arrs 28)[x.1 * N + y.1]'(by rw [hlen]; exact mul_add_lt_mul x.2 y.2) ≠ 0)) := by
  have hN_le_NN : N ≤ N * N := Nat.le_mul_self N
  have hN_w : N < 2 ^ w := by omega
  have hu_w : u < 2 ^ w := by omega
  have hv_w : v < 2 ^ w := by omega
  have idx1_lt : u * N + v < N * N := mul_add_lt_mul hu_lt hv_lt
  have idx2_lt : v * N + u < N * N := mul_add_lt_mul hv_lt hu_lt
  have huN_w : u * N < 2 ^ w := by omega
  have hvN_w : v * N < 2 ^ w := by omega
  have hidx1_w : u * N + v < 2 ^ w := by omega
  have hidx2_w : v * N + u < 2 ^ w := by omega
  have heval1 : (Expr.op .add (.op .mul (.reg r_u) (.reg 4)) (.reg r_v)).eval w s =
      some (u * N + v) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrN, hrv, hu_w, hN_w, huN_w, hv_w, hidx1_w]
  have hone_s : (Expr.const 1).eval w s = some 1 := by simp [checkWord, hw]
  let s₁ := s.writeArr 28 (u * N + v) 1
  have hex₁ : Exec w (.write 28 (.op .add (.op .mul (.reg r_u) (.reg 4)) (.reg r_v)) (.const 1))
      s s₁ 7 := .write heval1 hone_s (by rw [hlen]; exact idx1_lt)
  have heval2 : (Expr.op .add (.op .mul (.reg r_v) (.reg 4)) (.reg r_u)).eval w s₁ =
      some (v * N + u) := by
    simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrv, hrN, hru, hv_w, hN_w, hvN_w, hu_w, hidx2_w]
  have hone_s₁ : (Expr.const 1).eval w s₁ = some 1 := by simp [checkWord, hw]
  let s₂ := s₁.writeArr 28 (v * N + u) 1
  have hex₂ : Exec w (.write 28 (.op .add (.op .mul (.reg r_v) (.reg 4)) (.reg r_u)) (.const 1))
      s₁ s₂ 7 := .write heval2 hone_s₁ (by simp [s₁, hlen, idx2_lt])
  refine ⟨s₂, .seq hex₁ hex₂, rfl,
    fun a ha => by
      have ha28 : (a : Arr) ≠ 28 := by dsimp [Arr]; omega
      simp [s₂, s₁, ha28],
    by simp [s₂, s₁, hlen], ?_, ?_⟩
  · intro x y
    simp only [s₂, s₁, State.writeArr_arrs_self]
    by_cases h2 : x.1 * N + y.1 = v * N + u
    · have ⟨hx_eq, hy_eq⟩ := mul_add_inj y.2 hu_lt h2
      have hset2 : (((s.arrs 28).set (u * N + v) 1).set (v * N + u) 1)[x.1 * N + y.1]'(by
          rw [List.length_set, List.length_set, hlen]; exact mul_add_lt_mul x.2 y.2) = 1 := by
        simp only [h2]
        exact List.getElem_set_self (by simp [hlen, idx2_lt])
      rw [hset2]
      exact ⟨fun _ => Or.inr (Or.inl ⟨hx_eq, hy_eq⟩), fun _ => le_rfl⟩
    · rw [List.getElem_set_ne (Ne.symm h2)]
      by_cases h1 : x.1 * N + y.1 = u * N + v
      · have ⟨hx_eq, hy_eq⟩ := mul_add_inj y.2 hv_lt h1
        have hset1 : ((s.arrs 28).set (u * N + v) 1)[x.1 * N + y.1]'(by
            rw [List.length_set, hlen]; exact mul_add_lt_mul x.2 y.2) = 1 := by
          simp only [h1]
          exact List.getElem_set_self (by simp [hlen, idx1_lt])
        rw [hset1]
        exact ⟨fun _ => Or.inl ⟨hx_eq, hy_eq⟩, fun _ => le_rfl⟩
      · rw [List.getElem_set_ne (Ne.symm h1)]
        constructor
        · intro hle
          exact Or.inr (Or.inr hle)
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hle)
          · exact absurd rfl h1
          · exact absurd rfl h2
          · exact hle
  · intro x y
    simp only [s₂, s₁, State.writeArr_arrs_self]
    by_cases h2 : x.1 * N + y.1 = v * N + u
    · have ⟨hx_eq, hy_eq⟩ := mul_add_inj y.2 hu_lt h2
      have hset2 : (((s.arrs 28).set (u * N + v) 1).set (v * N + u) 1)[x.1 * N + y.1]'(by
          rw [List.length_set, List.length_set, hlen]; exact mul_add_lt_mul x.2 y.2) = 1 := by
        simp only [h2]
        exact List.getElem_set_self (by simp [hlen, idx2_lt])
      rw [hset2]
      exact ⟨fun _ => Or.inr (Or.inl ⟨hx_eq, hy_eq⟩), fun _ => one_ne_zero⟩
    · rw [List.getElem_set_ne (Ne.symm h2)]
      by_cases h1 : x.1 * N + y.1 = u * N + v
      · have ⟨hx_eq, hy_eq⟩ := mul_add_inj y.2 hv_lt h1
        have hset1 : ((s.arrs 28).set (u * N + v) 1)[x.1 * N + y.1]'(by
            rw [List.length_set, hlen]; exact mul_add_lt_mul x.2 y.2) = 1 := by
          simp only [h1]
          exact List.getElem_set_self (by simp [hlen, idx1_lt])
        rw [hset1]
        exact ⟨fun _ => Or.inl ⟨hx_eq, hy_eq⟩, fun _ => one_ne_zero⟩
      · rw [List.getElem_set_ne (Ne.symm h1)]
        constructor
        · intro hne0
          exact Or.inr (Or.inr hne0)
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hne0)
          · exact absurd rfl h1
          · exact absurd rfl h2
          · exact hne0

theorem inArr_getElem_alg81 (x : Alg81Input) :
    (encAlg81In x).length = 3 + 2 * (edgeListOf x.G).length + x.omega.length ∧
    (encAlg81In x)[0]'(by simp [encAlg81In, encGraph]) = x.n ∧
    (encAlg81In x)[1]'(by simp [encAlg81In, encGraph]) = (edgeListOf x.G).length ∧
    (encAlg81In x)[2 + 2 * (edgeListOf x.G).length]'(by simp [encAlg81In, encGraph]; omega) =
      x.omega.length ∧
    (∀ i (hi : i < (edgeListOf x.G).length),
      (encAlg81In x)[2 + 2 * i]'(by simp [encAlg81In, encGraph]; omega) = ((edgeListOf x.G)[i]).1.1 ∧
      (encAlg81In x)[3 + 2 * i]'(by simp [encAlg81In, encGraph]; omega) = ((edgeListOf x.G)[i]).2.1) ∧
    (∀ i (hi : i < x.omega.length),
      (encAlg81In x)[3 + 2 * (edgeListOf x.G).length + i]'(by simp [encAlg81In, encGraph]; omega) =
        (x.omega[i]).1) := by
  have hlen : (encAlg81In x).length = 3 + 2 * (edgeListOf x.G).length + x.omega.length := by
    simp [encAlg81In, encGraph]
    omega
  refine ⟨hlen, ?_, ?_, ?_, ?_, ?_⟩
  · simp [encAlg81In, encGraph]
  · simp [encAlg81In, encGraph]
  · simp only [encAlg81In, encGraph, List.append_assoc]
    rw [List.getElem_append_right (by simp)]
    rw [List.getElem_append_right (by simp)]
    simp
  · intro i hi
    simp only [encAlg81In, encGraph, List.append_assoc]
    constructor
    · rw [List.getElem_append_right (by simp)]
      rw [List.getElem_append_left (by simp; omega)]
      have hidx : 2 + 2 * i - 2 = 2 * i := by omega
      simp only [List.length_cons, List.length_nil, hidx]
      exact getElem_flatEdges_even (edgeListOf x.G) hi
    · rw [List.getElem_append_right (by simp; omega)]
      rw [List.getElem_append_left (by simp; omega)]
      have hidx : 3 + 2 * i - 2 = 2 * i + 1 := by omega
      simp only [List.length_cons, List.length_nil, hidx]
      exact getElem_flatEdges_odd (edgeListOf x.G) hi
  · intro i hi
    simp only [encAlg81In, encGraph, List.append_assoc]
    rw [List.getElem_append_right (by simp; omega)]
    rw [List.getElem_append_right (by simp; omega)]
    rw [List.getElem_append_right (by simp; omega)]
    have hidx : 3 + 2 * (edgeListOf x.G).length + i - 2 - 2 * (edgeListOf x.G).length - 1 = i := by
      omega
    simp only [List.length_cons, List.length_nil, length_flatEdges, List.getElem_map, hidx]

def EdgeInv81 (x : Alg81Input) (s₀ : State) (i : ℕ) (s : State) : Prop :=
  let m := (edgeListOf x.G).length
  let k := x.omega.length
  let N := x.n + k
  s.arrs inArr = encAlg81In x ∧
  s.regs 0 = x.n ∧ s.regs 1 = m ∧ s.regs 2 = 2 + 2 * m ∧ s.regs 3 = k ∧ s.regs 4 = N ∧
  s.regs 5 = i ∧
  (∀ r : ℕ, r < 5 → s.regs r = s₀.regs r) ∧
  ∃ (hlen : (s.arrs 28).length = N * N),
    ∀ (u v : Fin N),
      let val := (s.arrs 28)[u.1 * N + v.1]'(by rw [hlen]; exact mul_add_lt_mul u.2 v.2)
      val ≤ 1 ∧
      (val ≠ 0 ↔
        ∃ j, ∃ (hj : j < i) (hjm : j < m),
          (((edgeListOf x.G)[j]'hjm).1.1 = u.1 ∧ ((edgeListOf x.G)[j]'hjm).2.1 = v.1) ∨
          (((edgeListOf x.G)[j]'hjm).1.1 = v.1 ∧ ((edgeListOf x.G)[j]'hjm).2.1 = u.1))

theorem buildAuxMatEdgeLoop_exec {w : ℕ} (x : Alg81Input)
    (hw3 : 3 < 2 ^ w)
    (hNN_w : (x.n + x.omega.length) * (x.n + x.omega.length) < 2 ^ w)
    (hin_w : 3 + 2 * (edgeListOf x.G).length + x.omega.length < 2 ^ w)
    (s₀ : State) :
    ⦃EdgeInv81 x s₀ 0⦄[w]
      forUp 5 (.reg 1) buildAuxMatEdgeBody
    ⦃EdgeInv81 x s₀ (edgeListOf x.G).length⦄ ≤
      fun _ => 3 + (edgeListOf x.G).length * (7 + 28) := by
  have hw2 : 2 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hm_w : (edgeListOf x.G).length < 2 ^ w := by omega
  have hN_le_NN : x.n + x.omega.length ≤ (x.n + x.omega.length) * (x.n + x.omega.length) :=
    Nat.le_mul_self _
  have hN_w : x.n + x.omega.length < 2 ^ w := by omega
  obtain ⟨hlen_in, _, _, _, hget_edge, _⟩ := inArr_getElem_alg81 x
  apply Triple.forUp_const (EdgeInv81 x s₀) (edgeListOf x.G).length 28 hw hm_w
  · intro i _ s ⟨_, _, hr1_s, _, _, _, hr5_s, _, _⟩
    exact ⟨hr5_s, by simp [Expr.eval, checkWord, hr1_s, hm_w]⟩
  · intro i hi s_i ⟨hin_i, hr0_i, hr1_i, hr2_i, hr3_i, hr4_i, hr5_i, hregs_i, hlen_i, hmat_i⟩
    have hi_w : i < 2 ^ w := by omega
    have h2i_w : 2 * i < 2 ^ w := by omega
    have h22i_w : 2 + 2 * i < 2 ^ w := by omega
    have h32i_w : 3 + 2 * i < 2 ^ w := by omega
    obtain ⟨hget_u, hget_v⟩ := hget_edge i hi
    let u_i := ((edgeListOf x.G)[i]'hi).1
    let v_i := ((edgeListOf x.G)[i]'hi).2
    have hu_lt_N : u_i.1 < x.n + x.omega.length := by have := u_i.2; omega
    have hv_lt_N : v_i.1 < x.n + x.omega.length := by have := v_i.2; omega
    have hu_w : u_i.1 < 2 ^ w := by omega
    have hv_w : v_i.1 < 2 ^ w := by omega
    -- Read u_i into r_6 (cost 7)
    have hread_u :
        (Expr.read inArr (.op .add (.const 2) (.op .mul (.const 2) (.reg 5)))).eval w s_i =
          some u_i.1 := by
      have hidx : 2 + 2 * i < (encAlg81In x).length := by rw [hlen_in]; omega
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr5_i, hw2, hi_w, h2i_w, h22i_w,
        hin_i, hidx, hget_u, u_i, hu_w]
    let sa₁ := s_i.setReg 6 u_i.1
    have hexa₁ : Exec w (.assign 6 (.read inArr (.op .add (.const 2) (.op .mul (.const 2) (.reg 5)))))
        s_i sa₁ 7 := .assign hread_u
    -- Read v_i into r_7 (cost 7)
    have hread_v :
        (Expr.read inArr (.op .add (.const 3) (.op .mul (.const 2) (.reg 5)))).eval w sa₁ =
          some v_i.1 := by
      have hidx : 3 + 2 * i < (encAlg81In x).length := by rw [hlen_in]; omega
      simp [sa₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr5_i, hw3, hw2, hi_w, h2i_w,
        h32i_w, hin_i, hidx, hget_v, v_i, hv_w]
    let sa₂ := sa₁.setReg 7 v_i.1
    have hexa₂ : Exec w (.assign 7 (.read inArr (.op .add (.const 3) (.op .mul (.const 2) (.reg 5)))))
        sa₁ sa₂ 7 := .assign hread_v
    -- writeSymMat 28 4 6 7 (cost 14)
    rcases writeSymMat_exec (w := w) (N := x.n + x.omega.length) (s := sa₂) (u := u_i.1) (v := v_i.1)
        6 7 (by decide) (by decide) (by decide) hw hNN_w hu_lt_N hv_lt_N
        (by simp [sa₂, sa₁, hlen_i])
        (by simp [sa₂, sa₁, hr4_i]) (by simp [sa₂, sa₁]) (by simp [sa₂]) with
      ⟨sa₃, hexa₃, hregs₃, harrs₃, hlen₃, hle₃, hne₃⟩
    refine ⟨sa₃, 7 + (7 + 14), .seq hexa₁ (.seq hexa₂ hexa₃), le_rfl, ?_,
      by rw [hregs₃]; simp [sa₂, sa₁, hr5_i]⟩
    refine ⟨by simp [harrs₃ inArr (by decide), sa₂, sa₁, hin_i],
      by simp [hregs₃, sa₂, sa₁, hr0_i],
      by simp [hregs₃, sa₂, sa₁, hr1_i],
      by simp [hregs₃, sa₂, sa₁, hr2_i],
      by simp [hregs₃, sa₂, sa₁, hr3_i],
      by simp [hregs₃, sa₂, sa₁, hr4_i],
      by simp,
      fun r hr => by
        have hr5 : (r : Reg) ≠ 5 := by dsimp [Reg]; omega
        have hr6 : (r : Reg) ≠ 6 := by dsimp [Reg]; omega
        have hr7 : (r : Reg) ≠ 7 := by dsimp [Reg]; omega
        simp only [State.setReg, Function.update_of_ne hr5, hregs₃, sa₂, sa₁,
          Function.update_of_ne hr7, Function.update_of_ne hr6]
        exact hregs_i r hr,
      hlen₃, fun u v => ?_⟩
    obtain ⟨hle_uv, hiff_uv⟩ := hmat_i u v
    refine ⟨(hle₃ u v).mpr (Or.inr (Or.inr hle_uv)),
      (hne₃ u v).trans ((or_congr_right (or_congr_right hiff_uv)).trans ?_)⟩
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨j, hj, hjm, hmatch⟩)
      · exact ⟨i, by omega, hi, Or.inl ⟨h1.symm, h2.symm⟩⟩
      · exact ⟨i, by omega, hi, Or.inr ⟨h2.symm, h1.symm⟩⟩
      · exact ⟨j, by omega, hjm, hmatch⟩
    · rintro ⟨j, hj, hjm, hmatch⟩
      by_cases hji : j = i
      · subst hji
        rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr (Or.inl ⟨h2.symm, h1.symm⟩)
      · exact Or.inr (Or.inr ⟨j, by omega, hjm, hmatch⟩)

def CycleInv81 (x : Alg81Input) (s₀ : State) (i : ℕ) (s : State) : Prop :=
  let m := (edgeListOf x.G).length
  let k := x.omega.length
  let N := x.n + k
  s.arrs inArr = encAlg81In x ∧
  s.regs 0 = x.n ∧ s.regs 1 = m ∧ s.regs 2 = 2 + 2 * m ∧ s.regs 3 = k ∧ s.regs 4 = N ∧
  s.regs 5 = i ∧
  (∀ r : ℕ, r < 5 → s.regs r = s₀.regs r) ∧
  ∃ (hlen : (s.arrs 28).length = N * N),
    ∀ (u v : Fin N),
      let val := (s.arrs 28)[u.1 * N + v.1]'(by rw [hlen]; exact mul_add_lt_mul u.2 v.2)
      val ≤ 1 ∧
      (val ≠ 0 ↔
        (∃ (hu : u.1 < x.n) (hv : v.1 < x.n), x.G.Adj ⟨u.1, hu⟩ ⟨v.1, hv⟩) ∨
        (∃ (j : Fin k), j.1 < i ∧
          ((u.1 = x.n + j.1 ∧ v.1 = x.n + (j.1 + 1) % k) ∨
           (v.1 = x.n + j.1 ∧ u.1 = x.n + (j.1 + 1) % k) ∨
           (u.1 = x.n + j.1 ∧ v.1 = (x.omega[j.1]'j.2).1) ∨
           (v.1 = x.n + j.1 ∧ u.1 = (x.omega[j.1]'j.2).1) ∨
           (u.1 = (x.omega[j.1]'j.2).1 ∧
            v.1 = (x.omega[(j.1 + 1) % k]'(Nat.mod_lt _ (by have := j.2; omega))).1) ∨
           (v.1 = (x.omega[j.1]'j.2).1 ∧
            u.1 = (x.omega[(j.1 + 1) % k]'(Nat.mod_lt _ (by have := j.2; omega))).1))))

theorem buildAuxMatCycleLoop_exec {w : ℕ} (x : Alg81Input) (hk : 4 ≤ x.omega.length)
    (hw3 : 3 < 2 ^ w)
    (hNN_w : (x.n + x.omega.length) * (x.n + x.omega.length) < 2 ^ w)
    (hin_w : 3 + 2 * (edgeListOf x.G).length + x.omega.length < 2 ^ w)
    (s₀ : State) :
    ⦃CycleInv81 x s₀ 0⦄[w]
      forUp 5 (.reg 3) buildAuxMatCycleBody
    ⦃CycleInv81 x s₀ x.omega.length⦄ ≤
      fun _ => 3 + x.omega.length * (7 + 70) := by
  have hw2 : 2 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hN_le_NN : x.n + x.omega.length ≤ (x.n + x.omega.length) * (x.n + x.omega.length) :=
    Nat.le_mul_self _
  have hN_w : x.n + x.omega.length < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have hk_w : x.omega.length < 2 ^ w := by omega
  obtain ⟨hlen_in, _, _, _, _, hget_omega⟩ := inArr_getElem_alg81 x
  apply Triple.forUp_const (CycleInv81 x s₀) x.omega.length 70 hw hk_w
  · intro i _ s ⟨_, _, _, _, hr3_s, _, hr5_s, _, _⟩
    exact ⟨hr5_s, by simp [Expr.eval, checkWord, hr3_s, hk_w]⟩
  · intro i hi s_i ⟨hin_i, hr0_i, hr1_i, hr2_i, hr3_i, hr4_i, hr5_i, hregs_i, hlen_i, hmat_i⟩
    have hi_w : i < 2 ^ w := by omega
    have hi1_w : i + 1 < 2 ^ w := by omega
    let inext := (i + 1) % x.omega.length
    have hinext_lt : inext < x.omega.length := Nat.mod_lt _ (by omega)
    have hinext_w : inext < 2 ^ w := by omega
    have hni_lt : x.n + i < x.n + x.omega.length := by omega
    have hninext_lt : x.n + inext < x.n + x.omega.length := by omega
    have hni_w : x.n + i < 2 ^ w := by omega
    have hninext_w : x.n + inext < 2 ^ w := by omega
    have h2m_w : 2 + 2 * (edgeListOf x.G).length < 2 ^ w := by omega
    have h3m_w : 1 + (2 + 2 * (edgeListOf x.G).length) < 2 ^ w := by omega
    have hidx_i_w : 1 + (2 + 2 * (edgeListOf x.G).length) + i < 2 ^ w := by omega
    have hidx_inext_w : 1 + (2 + 2 * (edgeListOf x.G).length) + inext < 2 ^ w := by omega
    let wi := x.omega[i]'hi
    let winext := x.omega[inext]'hinext_lt
    have hwi_lt : wi.1 < x.n + x.omega.length := by have := wi.2; omega
    have hwinext_lt : winext.1 < x.n + x.omega.length := by have := winext.2; omega
    have hwi_w : wi.1 < 2 ^ w := by omega
    have hwinext_w : winext.1 < 2 ^ w := by omega
    -- 1. r_6 := (r_5 + 1) % r_3 (cost 6)
    have heval6 : (Expr.op .mod (.op .add (.reg 5) (.const 1)) (.reg 3)).eval w s_i =
        some inext := by
      have hk_ne0 : x.omega.length ≠ 0 := by omega
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr5_i, hr3_i, hi_w, hw, hi1_w,
        hk_w, hk_ne0, inext, hinext_w]
    let sb₁ := s_i.setReg 6 inext
    have hexb₁ : Exec w (.assign 6 (.op .mod (.op .add (.reg 5) (.const 1)) (.reg 3)))
        s_i sb₁ 6 := .assign heval6
    -- 2. r_7 := r_0 + r_5 (cost 4)
    have heval7 : (Expr.op .add (.reg 0) (.reg 5)).eval w sb₁ = some (x.n + i) := by
      simp [sb₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr0_i, hr5_i, hn_w, hi_w, hni_w]
    let sb₂ := sb₁.setReg 7 (x.n + i)
    have hexb₂ : Exec w (.assign 7 (.op .add (.reg 0) (.reg 5))) sb₁ sb₂ 4 := .assign heval7
    -- 3. r_8 := r_0 + r_6 (cost 4)
    have heval8 : (Expr.op .add (.reg 0) (.reg 6)).eval w sb₂ = some (x.n + inext) := by
      simp [sb₂, sb₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr0_i, hn_w, hinext_w, hninext_w]
    let sb₃ := sb₂.setReg 8 (x.n + inext)
    have hexb₃ : Exec w (.assign 8 (.op .add (.reg 0) (.reg 6))) sb₂ sb₃ 4 := .assign heval8
    -- 4. r_9 := inArr[1 + r_2 + r_5] (cost 8)
    have hget_wi := hget_omega i hi
    have heval9 :
        (Expr.read inArr (.op .add (.op .add (.const 1) (.reg 2)) (.reg 5))).eval w sb₃ =
          some wi.1 := by
      have hidx_eq : 1 + (2 + 2 * (edgeListOf x.G).length) + i =
          3 + 2 * (edgeListOf x.G).length + i := by omega
      have hidx_i_w' : 3 + 2 * (edgeListOf x.G).length + i < 2 ^ w := by omega
      have hidx_lt : 3 + 2 * (edgeListOf x.G).length + i < (encAlg81In x).length := by
        rw [hlen_in]; omega
      simp [sb₃, sb₂, sb₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2_i, hr5_i,
        hw, h2m_w, h3m_w, hi_w, hin_i, hidx_eq, hidx_i_w', hidx_lt, hget_wi, wi, hwi_w]
    let sb₄ := sb₃.setReg 9 wi.1
    have hexb₄ : Exec w (.assign 9 (.read inArr (.op .add (.op .add (.const 1) (.reg 2)) (.reg 5))))
        sb₃ sb₄ 7 := .assign heval9
    -- 5. r_10 := inArr[1 + r_2 + r_6] (cost 7)
    have hget_winext := hget_omega inext hinext_lt
    have heval10 :
        (Expr.read inArr (.op .add (.op .add (.const 1) (.reg 2)) (.reg 6))).eval w sb₄ =
          some winext.1 := by
      have hidx_eq : 1 + (2 + 2 * (edgeListOf x.G).length) + inext =
          3 + 2 * (edgeListOf x.G).length + inext := by omega
      have hidx_inext_w' : 3 + 2 * (edgeListOf x.G).length + inext < 2 ^ w := by omega
      have hidx_lt : 3 + 2 * (edgeListOf x.G).length + inext < (encAlg81In x).length := by
        rw [hlen_in]; omega
      simp [sb₄, sb₃, sb₂, sb₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2_i,
        hw, h2m_w, h3m_w, hinext_w, hin_i, hidx_eq, hidx_inext_w', hidx_lt, hget_winext,
        winext, hwinext_w]
    let sb₅ := sb₄.setReg 10 winext.1
    have hexb₅ : Exec w (.assign 10 (.read inArr (.op .add (.op .add (.const 1) (.reg 2)) (.reg 6))))
        sb₄ sb₅ 7 := .assign heval10
    -- 6. writeSymMat 28 4 7 8 (C₁ edge, cost 14)
    rcases writeSymMat_exec (w := w) (N := x.n + x.omega.length) (s := sb₅)
        (u := x.n + i) (v := x.n + inext)
        7 8 (by decide) (by decide) (by decide) hw hNN_w hni_lt hninext_lt
        (by simp [sb₅, sb₄, sb₃, sb₂, sb₁, hlen_i])
        (by simp [sb₅, sb₄, sb₃, sb₂, sb₁, hr4_i])
        (by simp [sb₅, sb₄, sb₃, sb₂])
        (by simp [sb₅, sb₄, sb₃]) with
      ⟨sb₆, hexb₆, hregs₆, harrs₆, hlen₆, hle₆, hne₆⟩
    -- 7. writeSymMat 28 4 7 9 (rung edge, cost 14)
    rcases writeSymMat_exec (w := w) (N := x.n + x.omega.length) (s := sb₆)
        (u := x.n + i) (v := wi.1)
        7 9 (by decide) (by decide) (by decide) hw hNN_w hni_lt hwi_lt
        hlen₆
        (by rw [hregs₆]; simp [sb₅, sb₄, sb₃, sb₂, sb₁, hr4_i])
        (by rw [hregs₆]; simp [sb₅, sb₄, sb₃, sb₂])
        (by rw [hregs₆]; simp [sb₅, sb₄]) with
      ⟨sb₇, hexb₇, hregs₇, harrs₇, hlen₇, hle₇, hne₇⟩
    -- 8. writeSymMat 28 4 9 10 (C₂ edge, cost 14)
    rcases writeSymMat_exec (w := w) (N := x.n + x.omega.length) (s := sb₇)
        (u := wi.1) (v := winext.1)
        9 10 (by decide) (by decide) (by decide) hw hNN_w hwi_lt hwinext_lt
        hlen₇
        (by rw [hregs₇, hregs₆]; simp [sb₅, sb₄, sb₃, sb₂, sb₁, hr4_i])
        (by rw [hregs₇, hregs₆]; simp [sb₅, sb₄])
        (by rw [hregs₇, hregs₆]; simp [sb₅]) with
      ⟨sb₈, hexb₈, hregs₈, harrs₈, hlen₈, hle₈, hne₈⟩
    refine ⟨sb₈, 6 + (4 + (4 + (7 + (7 + (14 + (14 + 14)))))),
      .seq hexb₁ (.seq hexb₂ (.seq hexb₃ (.seq hexb₄ (.seq hexb₅ (.seq hexb₆ (.seq hexb₇ hexb₈)))))),
      le_rfl, ?_, by rw [hregs₈, hregs₇, hregs₆]; simp [sb₅, sb₄, sb₃, sb₂, sb₁, hr5_i]⟩
    have hregs_eq : sb₈.regs = sb₅.regs := by rw [hregs₈, hregs₇, hregs₆]
    refine ⟨by simp [harrs₈ inArr (by decide), harrs₇ inArr (by decide),
        harrs₆ inArr (by decide), sb₅, sb₄, sb₃, sb₂, sb₁, hin_i],
      by simp [hregs_eq, sb₅, sb₄, sb₃, sb₂, sb₁, hr0_i],
      by simp [hregs_eq, sb₅, sb₄, sb₃, sb₂, sb₁, hr1_i],
      by simp [hregs_eq, sb₅, sb₄, sb₃, sb₂, sb₁, hr2_i],
      by simp [hregs_eq, sb₅, sb₄, sb₃, sb₂, sb₁, hr3_i],
      by simp [hregs_eq, sb₅, sb₄, sb₃, sb₂, sb₁, hr4_i],
      by simp,
      fun r hr => by
        have hr5 : (r : Reg) ≠ 5 := by dsimp [Reg]; omega
        have hr6 : (r : Reg) ≠ 6 := by dsimp [Reg]; omega
        have hr7 : (r : Reg) ≠ 7 := by dsimp [Reg]; omega
        have hr8 : (r : Reg) ≠ 8 := by dsimp [Reg]; omega
        have hr9 : (r : Reg) ≠ 9 := by dsimp [Reg]; omega
        have hr10 : (r : Reg) ≠ 10 := by dsimp [Reg]; omega
        simp only [State.setReg, Function.update_of_ne hr5, hregs_eq, sb₅, sb₄, sb₃, sb₂, sb₁,
          Function.update_of_ne hr10, Function.update_of_ne hr9, Function.update_of_ne hr8,
          Function.update_of_ne hr7, Function.update_of_ne hr6]
        exact hregs_i r hr,
      hlen₈, fun u v => ?_⟩
    obtain ⟨hle_uv, hiff_uv⟩ := hmat_i u v
    have hle_6 := (hle₆ u v).mpr (Or.inr (Or.inr hle_uv))
    have hle_7 := (hle₇ u v).mpr (Or.inr (Or.inr hle_6))
    have hle_8 := (hle₈ u v).mpr (Or.inr (Or.inr hle_7))
    have hne_chain := (hne₈ u v).trans
      (or_congr_right (or_congr_right ((hne₇ u v).trans
        (or_congr_right (or_congr_right ((hne₆ u v).trans
          (or_congr_right (or_congr_right hiff_uv))))))))
    refine ⟨hle_8, hne_chain.trans ?_⟩
    let iFin : Fin x.omega.length := ⟨i, hi⟩
    have hiFin : iFin.1 < i + 1 := Nat.lt_succ_self i
    constructor
    · rintro (h_c2_1 | h_c2_2 | h_r_1 | h_r_2 | h_c1_1 | h_c1_2 | (hG | ⟨j, hj, hmatch⟩))
      · exact Or.inr ⟨iFin, hiFin, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h_c2_1))))⟩
      · exact Or.inr ⟨iFin, hiFin, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h_c2_2.symm))))⟩
      · exact Or.inr ⟨iFin, hiFin, Or.inr (Or.inr (Or.inl h_r_1))⟩
      · exact Or.inr ⟨iFin, hiFin, Or.inr (Or.inr (Or.inr (Or.inl h_r_2.symm)))⟩
      · exact Or.inr ⟨iFin, hiFin, Or.inl h_c1_1⟩
      · exact Or.inr ⟨iFin, hiFin, Or.inr (Or.inl h_c1_2.symm)⟩
      · exact Or.inl hG
      · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, hmatch⟩
    · rintro (hG | ⟨j, hj, hmatch⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hG))))))
      · by_cases hji : j.1 = i
        · have hj_eq : j = iFin := Fin.ext hji
          subst hj_eq
          rcases hmatch with h1 | h2 | h3 | h4 | h5 | h6
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h2.symm)))))
          · exact Or.inr (Or.inr (Or.inl h3))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h4.symm)))
          · exact Or.inl h5
          · exact Or.inr (Or.inl h6.symm)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, by omega, hmatch⟩))))))

/-- Specification of `buildAuxMatProg`: builds `IsAdjMatrix (auxGraph81 x.G x.omega) 28 s'`
when `4 ≤ x.omega.length`. -/
theorem buildAuxMatProg_exec {w : ℕ} (x : Alg81Input) (hk : 4 ≤ x.omega.length)
    (hw3 : 3 < 2 ^ w)
    (hNN_w : (x.n + x.omega.length) * (x.n + x.omega.length) < 2 ^ w)
    (hin_w : 3 + 2 * (edgeListOf x.G).length + x.omega.length < 2 ^ w)
    {s₀ : State}
    (hin₀ : s₀.arrs inArr = encAlg81In x)
    (hr0 : s₀.regs 0 = x.n)
    (hr1 : s₀.regs 1 = (edgeListOf x.G).length)
    (hr2 : s₀.regs 2 = 2 + 2 * (edgeListOf x.G).length)
    (hr3 : s₀.regs 3 = x.omega.length)
    (hr4 : s₀.regs 4 = x.n + x.omega.length) :
    ∃ s' t,
      Exec w buildAuxMatProg s₀ s' t ∧
      t ≤ 4 * ((x.n + x.omega.length) * (x.n + x.omega.length)) +
        38 * (edgeListOf x.G).length + 90 * x.omega.length + 20 ∧
      IsAdjMatrix (auxGraph81 x.G x.omega) 28 s' ∧
      s'.arrs inArr = encAlg81In x ∧
      (∀ r : ℕ, r < 5 → s'.regs r = s₀.regs r) := by
  have hN_le_NN : x.n + x.omega.length ≤ (x.n + x.omega.length) * (x.n + x.omega.length) :=
    Nat.le_mul_self _
  have hN_w : x.n + x.omega.length < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  -- 1. alloc 28 (r_4 * r_4) and r_5 := 0
  have hNN_eval : (Expr.op .mul (.reg 4) (.reg 4)).eval w s₀ =
      some ((x.n + x.omega.length) * (x.n + x.omega.length)) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4, hN_w, hNN_w]
  let s₁ := s₀.setArr 28 (List.replicate ((x.n + x.omega.length) * (x.n + x.omega.length)) 0)
  have hex₁ : Exec w (.alloc 28 (.op .mul (.reg 4) (.reg 4))) s₀ s₁
      (3 + (x.n + x.omega.length) * (x.n + x.omega.length)) := .alloc hNN_eval
  let s₂ := s₁.setReg 5 0
  have hex₂ : Exec w (.assign 5 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hEdge₀ : EdgeInv81 x s₀ 0 s₂ := by
    refine ⟨by simp [s₂, s₁, hin₀],
      by simp [s₂, s₁, hr0], by simp [s₂, s₁, hr1],
      by simp [s₂, s₁, hr2], by simp [s₂, s₁, hr3],
      by simp [s₂, s₁, hr4], by simp [s₂],
      fun r hr => by
        have hr5 : (r : Reg) ≠ 5 := by dsimp [Reg]; omega
        simp [s₂, s₁, State.setReg, hr5],
      by simp [s₂, s₁], fun u v => ?_⟩
    simp [s₂, s₁]
  rcases buildAuxMatEdgeLoop_exec x hw3 hNN_w hin_w s₀ s₂ hEdge₀ with
    ⟨s₃, t₃, hex₃, ht₃, hin₃, hr0_3, hr1_3, hr2_3, hr3_3, hr4_3, _, hregs₃, hlen₃, hmat₃⟩
  dsimp only at ht₃
  have hG_iff₃ : ∀ (u v : Fin (x.n + x.omega.length)),
      (s₃.arrs 28)[u.1 * (x.n + x.omega.length) + v.1]'(by rw [hlen₃]; exact mul_add_lt_mul u.2 v.2) ≠ 0 ↔
        ∃ (hu : u.1 < x.n) (hv : v.1 < x.n), x.G.Adj ⟨u.1, hu⟩ ⟨v.1, hv⟩ := by
    intro u v
    rw [(hmat₃ u v).2]
    have hsimple := (isSimpleEdgeList_edgeListOf x.G).2.2
    constructor
    · rintro ⟨j, _, hjm, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · refine ⟨by rw [← h1]; exact ((edgeListOf x.G)[j]'hjm).1.2,
          by rw [← h2]; exact ((edgeListOf x.G)[j]'hjm).2.2, ?_⟩
        exact (hsimple _ _).mpr ⟨j, hjm, Or.inl ⟨Fin.ext h1, Fin.ext h2⟩⟩
      · refine ⟨by rw [← h2]; exact ((edgeListOf x.G)[j]'hjm).2.2,
          by rw [← h1]; exact ((edgeListOf x.G)[j]'hjm).1.2, ?_⟩
        exact (hsimple _ _).mpr ⟨j, hjm, Or.inr ⟨Fin.ext h1, Fin.ext h2⟩⟩
    · rintro ⟨hu, hv, hadj⟩
      rcases (hsimple ⟨u.1, hu⟩ ⟨v.1, hv⟩).mp hadj with ⟨j, hj, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · exact ⟨j, hj, hj, Or.inl ⟨congrArg Fin.val h1, congrArg Fin.val h2⟩⟩
      · exact ⟨j, hj, hj, Or.inr ⟨congrArg Fin.val h1, congrArg Fin.val h2⟩⟩
  let s₄ := s₃.setReg 5 0
  have hex₄ : Exec w (.assign 5 (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hCycle₀ : CycleInv81 x s₀ 0 s₄ := by
    refine ⟨by simp [s₄, hin₃],
      by simp [s₄, hr0_3], by simp [s₄, hr1_3], by simp [s₄, hr2_3],
      by simp [s₄, hr3_3], by simp [s₄, hr4_3], by simp [s₄],
      fun r hr => by
        have hr5 : (r : Reg) ≠ 5 := by dsimp [Reg]; omega
        simp only [s₄, State.setReg, Function.update_of_ne hr5]
        exact hregs₃ r hr,
      hlen₃, fun u v => ?_⟩
    refine ⟨(hmat₃ u v).1, (hG_iff₃ u v).trans ?_⟩
    simp
  rcases buildAuxMatCycleLoop_exec x hk hw3 hNN_w hin_w s₀ s₄ hCycle₀ with
    ⟨s₅, t₅, hex₅, ht₅, hin₅, _, _, _, _, _, _, hregs₅, hlen₅, hmat₅⟩
  dsimp only at ht₅
  refine ⟨s₅, (3 + (x.n + x.omega.length) * (x.n + x.omega.length)) + (2 + (t₃ + (2 + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega, ⟨hlen₅, fun u v => ?_⟩, hin₅, hregs₅⟩
  obtain ⟨hle_uv, hiff_uv⟩ := hmat₅ u v
  refine ⟨hiff_uv.trans ?_, hle_uv⟩
  constructor
  · intro h_or
    have hne_uv : u ≠ v := by
      rintro rfl
      rcases h_or with ⟨hu, _, hadj⟩ | ⟨j, _, hmatch⟩
      · exact x.G.ne_of_adj hadj rfl
      · have hmod_ne : (j.1 + 1) % x.omega.length ≠ j.1 := by
          have := j.2
          by_cases hlast : j.1 + 1 = x.omega.length
          · rw [hlast, Nat.mod_self]; omega
          · rw [Nat.mod_eq_of_lt (by omega)]; omega
        rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · omega
        · omega
        · have := (x.omega[j.1]'j.2).2; omega
        · have := (x.omega[j.1]'j.2).2; omega
        · have heq : x.omega[j.1]'j.2 = x.omega[(j.1 + 1) % x.omega.length]'(Nat.mod_lt _ (by omega)) :=
            Fin.ext (h1.symm.trans h2)
          exact hmod_ne ((x.nodup_omega.getElem_inj_iff).mp heq).symm
        · have heq : x.omega[j.1]'j.2 = x.omega[(j.1 + 1) % x.omega.length]'(Nat.mod_lt _ (by omega)) :=
            Fin.ext (h1.symm.trans h2)
          exact hmod_ne ((x.nodup_omega.getElem_inj_iff).mp heq).symm
    refine ⟨hne_uv, ?_⟩
    rcases h_or with hG | ⟨j, _, h1 | h2 | h3 | h4 | h5 | h6⟩
    · exact Or.inl hG
    · exact Or.inr (Or.inl ⟨j, Or.inl h1⟩)
    · exact Or.inr (Or.inl ⟨j, Or.inr h2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨j, Or.inl h3⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨j, Or.inr h4⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨j, by omega, Or.inl h5⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨j, by omega, Or.inr h6⟩))
  · rintro ⟨_, hG | ⟨j, h1 | h2⟩ | ⟨j, h3 | h4⟩ | ⟨j, _, h5 | h6⟩⟩
    · exact Or.inl hG
    · exact Or.inr ⟨j, j.2, Or.inl h1⟩
    · exact Or.inr ⟨j, j.2, Or.inr (Or.inl h2)⟩
    · exact Or.inr ⟨j, j.2, Or.inr (Or.inr (Or.inl h3))⟩
    · exact Or.inr ⟨j, j.2, Or.inr (Or.inr (Or.inr (Or.inl h4)))⟩
    · exact Or.inr ⟨j, j.2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))⟩
    · exact Or.inr ⟨j, j.2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6))))⟩

/-! ### Section 4: Extracting a Cross on the Word RAM, Pure Reader `decAlg81Out`, and `gm13_algorithm_8_1` -/

/-- Loop body of `buildOmegaPosProg`: reads `w_i = inArr[1 + r_2 + r_5]` into `r_6`, computes
`1 + ((r_5 + r_3 - 2) % r_3)` into `r_7`, and writes `r_7` to `29[r_6]`. -/
def buildOmegaPosBody : Cmd :=
  .seq (.assign 6 (.read inArr (.op .add (.op .add (.const 1) (.reg 2)) (.reg 5))))
    (.seq (.assign 7
        (.op .add (.const 1)
          (.op .mod (.op .sub (.op .add (.reg 5) (.reg 3)) (.const 2)) (.reg 3))))
      (.write 29 (.reg 6) (.reg 7)))

/-- Build the `1`-based cyclic position table `omegaPosVal x.n x.omega` in array `29` of length
`r_4 = x.n + x.omega.length`. -/
def buildOmegaPosProg : Cmd :=
  .seq (.alloc 29 (.reg 4))
    (.seq (.assign 5 (.const 0))
      (forUp 5 (.reg 3) buildOmegaPosBody))

/-- Loop invariant for `buildOmegaPosProg` at index `i ≤ x.omega.length`. -/
def OmegaPosInv81 (x : Alg81Input) (s₀ : State) (i : ℕ) (s : State) : Prop :=
  let m := (edgeListOf x.G).length
  let k := x.omega.length
  let N := x.n + k
  s.arrs inArr = encAlg81In x ∧
  s.regs 0 = x.n ∧ s.regs 2 = 2 + 2 * m ∧ s.regs 3 = k ∧ s.regs 4 = N ∧
  s.regs 5 = i ∧
  (∀ a : ℕ, a ≠ 29 → s.arrs a = s₀.arrs a) ∧
  ∃ (hlen : (s.arrs 29).length = N),
    (∀ j (hj : j < i) (hjk : j < k),
      (s.arrs 29)[(x.omega[j]'hjk).1]'(by rw [hlen]; have := (x.omega[j]'hjk).2; omega) =
        1 + (j + k - 2) % k) ∧
    (∀ u (hu : u < N),
      (∀ j (hj : j < i) (hjk : j < k), (x.omega[j]'hjk).1 ≠ u) →
      (s.arrs 29)[u]'(by rw [hlen]; exact hu) = 0)

theorem buildOmegaPosProg_exec {w : ℕ} (x : Alg81Input) (hk : 4 ≤ x.omega.length)
    (hw3 : 3 < 2 ^ w)
    (h2N_w : 2 * (x.n + x.omega.length) < 2 ^ w)
    (hin_w : 3 + 2 * (edgeListOf x.G).length + x.omega.length < 2 ^ w)
    {s₀ : State}
    (hin₀ : s₀.arrs inArr = encAlg81In x)
    (hr0 : s₀.regs 0 = x.n)
    (hr2 : s₀.regs 2 = 2 + 2 * (edgeListOf x.G).length)
    (hr3 : s₀.regs 3 = x.omega.length)
    (hr4 : s₀.regs 4 = x.n + x.omega.length) :
    ∃ s' t,
      Exec w buildOmegaPosProg s₀ s' t ∧
      t ≤ 28 * (x.n + x.omega.length) + 10 ∧
      s'.arrs inArr = encAlg81In x ∧
      s'.regs 0 = x.n ∧
      s'.regs 3 = x.omega.length ∧
      s'.regs 4 = x.n + x.omega.length ∧
      (∀ a : ℕ, a ≠ 29 → s'.arrs a = s₀.arrs a) ∧
      ∃ (hlen : (s'.arrs 29).length = x.n + x.omega.length),
        ∀ u (hu : u < x.n + x.omega.length),
          (s'.arrs 29)[u]'(by rw [hlen]; exact hu) = omegaPosVal x.n x.omega u := by
  have hw2 : 2 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hN_w : x.n + x.omega.length < 2 ^ w := by omega
  have hk_w : x.omega.length < 2 ^ w := by omega
  obtain ⟨hlen_in, _, _, _, _, hget_omega⟩ := inArr_getElem_alg81 x
  let s₁ := s₀.setArr 29 (List.replicate (x.n + x.omega.length) 0)
  have hex₁ : Exec w (.alloc 29 (.reg 4)) s₀ s₁ (1 + (x.n + x.omega.length)) :=
    .alloc (by simp [Expr.eval, checkWord, hr4, hN_w])
  let s₂ := s₁.setReg 5 0
  have hex₂ : Exec w (.assign 5 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hInv₀ : OmegaPosInv81 x s₀ 0 s₂ := by
    refine ⟨by simp [s₂, s₁, hin₀],
      by simp [s₂, s₁, hr0], by simp [s₂, s₁, hr2],
      by simp [s₂, s₁, hr3], by simp [s₂, s₁, hr4],
      by simp [s₂],
      fun a ha => by
        have ha' : (a : Arr) ≠ 29 := by dsimp [Arr]; omega
        simp [s₂, s₁, State.setArr, ha'],
      by simp [s₂, s₁],
      fun j hj _ => by omega,
      fun u _ _ => by simp [s₂, s₁]⟩
  have hLoop :
      ⦃OmegaPosInv81 x s₀ 0⦄[w]
        forUp 5 (.reg 3) buildOmegaPosBody
      ⦃OmegaPosInv81 x s₀ x.omega.length⦄ ≤
        fun _ => 3 + x.omega.length * (7 + 20) := by
    apply Triple.forUp_const (OmegaPosInv81 x s₀) x.omega.length 20 hw hk_w
    · intro i _ s ⟨_, _, _, hr3_s, _, hr5_s, _, _⟩
      exact ⟨hr5_s, by simp [Expr.eval, checkWord, hr3_s, hk_w]⟩
    · intro i hi s_i ⟨hin_i, hr0_i, hr2_i, hr3_i, hr4_i, hr5_i, harr_i, hlen_i, hset_i, hzero_i⟩
      have hi_w : i < 2 ^ w := by omega
      have hik_w : i + x.omega.length < 2 ^ w := by omega
      have hik2_w : i + x.omega.length - 2 < 2 ^ w := by omega
      let pos_i := 1 + (i + x.omega.length - 2) % x.omega.length
      have hmod_lt : (i + x.omega.length - 2) % x.omega.length < x.omega.length :=
        Nat.mod_lt _ (by omega)
      have hmod_w : (i + x.omega.length - 2) % x.omega.length < 2 ^ w := by omega
      have hpos_w : pos_i < 2 ^ w := by dsimp [pos_i]; omega
      have h2m_w : 2 + 2 * (edgeListOf x.G).length < 2 ^ w := by omega
      have h3m_w : 1 + (2 + 2 * (edgeListOf x.G).length) < 2 ^ w := by omega
      let wi := x.omega[i]'hi
      have hwi_lt : wi.1 < x.n + x.omega.length := by have := wi.2; omega
      have hwi_w : wi.1 < 2 ^ w := by omega
      have hget_wi := hget_omega i hi
      have heval6 :
          (Expr.read inArr (.op .add (.op .add (.const 1) (.reg 2)) (.reg 5))).eval w s_i =
            some wi.1 := by
        have hidx_eq : 1 + (2 + 2 * (edgeListOf x.G).length) + i =
            3 + 2 * (edgeListOf x.G).length + i := by omega
        have hidx_w : 3 + 2 * (edgeListOf x.G).length + i < 2 ^ w := by omega
        have hidx_lt : 3 + 2 * (edgeListOf x.G).length + i < (encAlg81In x).length := by
          rw [hlen_in]; omega
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2_i, hr5_i,
          hw, h2m_w, h3m_w, hi_w, hin_i, hidx_eq, hidx_w, hidx_lt, hget_wi, wi, hwi_w]
      let sb₁ := s_i.setReg 6 wi.1
      have hexb₁ : Exec w
          (.assign 6 (.read inArr (.op .add (.op .add (.const 1) (.reg 2)) (.reg 5))))
          s_i sb₁ 7 := .assign heval6
      have heval7 :
          (Expr.op .add (.const 1)
            (.op .mod (.op .sub (.op .add (.reg 5) (.reg 3)) (.const 2)) (.reg 3))).eval w sb₁ =
          some pos_i := by
        have hk_ne0 : x.omega.length ≠ 0 := by omega
        simp [sb₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr5_i, hr3_i,
          hi_w, hk_w, hik_w, hw2, hik2_w, hk_ne0, hmod_w, hw, pos_i, hpos_w]
      let sb₂ := sb₁.setReg 7 pos_i
      have hexb₂ : Exec w
          (.assign 7 (.op .add (.const 1)
            (.op .mod (.op .sub (.op .add (.reg 5) (.reg 3)) (.const 2)) (.reg 3))))
          sb₁ sb₂ 10 := .assign heval7
      let sb₃ := sb₂.writeArr 29 wi.1 pos_i
      have hexb₃ : Exec w (.write 29 (.reg 6) (.reg 7)) sb₂ sb₃ 3 :=
        .write (by simp [sb₂, sb₁, Expr.eval, checkWord, hwi_w])
          (by simp [sb₂, Expr.eval, checkWord, hpos_w])
          (by simp [sb₂, sb₁, hlen_i, hwi_lt])
      refine ⟨sb₃, 7 + (10 + 3), .seq hexb₁ (.seq hexb₂ hexb₃), le_rfl, ?_,
        by simp [sb₃, sb₂, sb₁, hr5_i]⟩
      refine ⟨by simp [sb₃, sb₂, sb₁, hin_i],
        by simp [sb₃, sb₂, sb₁, hr0_i],
        by simp [sb₃, sb₂, sb₁, hr2_i],
        by simp [sb₃, sb₂, sb₁, hr3_i],
        by simp [sb₃, sb₂, sb₁, hr4_i],
        by simp [sb₃, sb₂, sb₁],
        fun a ha => by
          have ha' : (a : Arr) ≠ 29 := by dsimp [Arr]; omega
          simp [sb₃, sb₂, sb₁, ha', harr_i a ha],
        by simp [sb₃, sb₂, sb₁, hlen_i], ?_, ?_⟩
      · intro j hj hjk
        simp only [sb₃, sb₂, sb₁, State.writeArr_arrs_self, State.setReg_arrs]
        by_cases hji : j = i
        · subst hji
          rw [List.getElem_set_self]
        · have hne_val : (x.omega[j]'hjk).1 ≠ wi.1 := by
            intro heq
            have hfin : x.omega[j]'hjk = x.omega[i]'hi := Fin.ext heq
            exact hji ((x.nodup_omega.getElem_inj_iff).mp hfin)
          rw [List.getElem_set_ne hne_val.symm]
          exact hset_i j (by omega) hjk
      · intro u hu hnone
        simp only [sb₃, sb₂, sb₁, State.writeArr_arrs_self, State.setReg_arrs]
        have hne_i : wi.1 ≠ u := hnone i (by omega) hi
        rw [List.getElem_set_ne hne_i]
        exact hzero_i u hu (fun j hj hjk => hnone j (by omega) hjk)
  rcases hLoop s₂ hInv₀ with ⟨s₃, t₃, hex₃, ht₃, hin₃, hr0_3, _, hr3_3, hr4_3, _, harr₃, hlen₃, hset₃, hzero₃⟩
  dsimp only at ht₃
  refine ⟨s₃, (1 + (x.n + x.omega.length)) + (2 + t₃),
    .seq hex₁ (.seq hex₂ hex₃), by omega, hin₃, hr0_3, hr3_3, hr4_3, harr₃, hlen₃, ?_⟩
  intro u hu
  unfold omegaPosVal
  split_ifs with hu_n hmem
  · let v : Fin x.n := ⟨u, hu_n⟩
    have hj_lt : x.omega.idxOf v < x.omega.length := List.idxOf_lt_length_of_mem hmem
    have hj_eq : x.omega[x.omega.idxOf v]'hj_lt = v := List.getElem_idxOf hj_lt
    have hj_val : (x.omega[x.omega.idxOf v]'hj_lt).1 = u := congrArg Fin.val hj_eq
    have h := hset₃ (x.omega.idxOf v) hj_lt hj_lt
    simp only [hj_val] at h
    exact h
  · apply hzero₃ u hu
    intro j _ hjk heq
    apply hmem
    have hfin : x.omega[j]'hjk = ⟨u, hu_n⟩ := Fin.ext heq
    rw [← hfin]
    exact List.getElem_mem hjk
  · apply hzero₃ u hu
    intro j _ hjk heq
    have := (x.omega[j]'hjk).2
    omega

/-- Word RAM expression evaluating `deltaPosVal (s.regs 20) (s.regs 21) (s.regs 22) (s.regs 23)`. -/
def deltaPosExpr : Expr :=
  .op .sub (.const 1)
    (.op .eq
      (.op .eq (.op .lt (.reg 20) (.reg 22)) (.op .lt (.reg 21) (.reg 22)))
      (.op .eq (.op .lt (.reg 20) (.reg 23)) (.op .lt (.reg 21) (.reg 23))))

/-- Word RAM expression evaluating `segPairTestVal` from `p₁, p₂, q₁, q₂` in `regs 20..23`. -/
def segPairTestExpr : Expr :=
  .op .mul
    (.op .mul (.op .lt (.const 0) (.reg 20))
      (.op .mul (.op .lt (.const 0) (.reg 21))
        (.op .mul (.op .lt (.const 0) (.reg 22))
          (.op .lt (.const 0) (.reg 23)))))
    deltaPosExpr

theorem segPairTestExpr_eval {w n : ℕ} (omega : List (Fin n)) (l₁ l₂ : List ℕ)
    (a₁ b₁ a₂ b₂ : ℕ) {s : State}
    (hw : 1 < 2 ^ w)
    (hk_w : omega.length < 2 ^ w)
    (hr20 : s.regs 20 = omegaPosVal n omega (l₁.getD a₁ 0))
    (hr21 : s.regs 21 = omegaPosVal n omega (l₁.getD b₁ 0))
    (hr22 : s.regs 22 = omegaPosVal n omega (l₂.getD a₂ 0))
    (hr23 : s.regs 23 = omegaPosVal n omega (l₂.getD b₂ 0)) :
    segPairTestExpr.eval w s = some (segPairTestVal n omega l₁ l₂ a₁ b₁ a₂ b₂) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hp₁_le := omegaPosVal_le n omega (l₁.getD a₁ 0)
  have hp₂_le := omegaPosVal_le n omega (l₁.getD b₁ 0)
  have hq₁_le := omegaPosVal_le n omega (l₂.getD a₂ 0)
  have hq₂_le := omegaPosVal_le n omega (l₂.getD b₂ 0)
  have hp₁_w : omegaPosVal n omega (l₁.getD a₁ 0) < 2 ^ w := by omega
  have hp₂_w : omegaPosVal n omega (l₁.getD b₁ 0) < 2 ^ w := by omega
  have hq₁_w : omegaPosVal n omega (l₂.getD a₂ 0) < 2 ^ w := by omega
  have hq₂_w : omegaPosVal n omega (l₂.getD b₂ 0) < 2 ^ w := by omega
  have hite_w : ∀ P : Prop, [Decidable P] → (if P then 1 else 0) < 2 ^ w := by
    intro P _; split_ifs <;> omega
  have hmul_w : ∀ a b : ℕ, a ≤ 1 → b ≤ 1 → a * b < 2 ^ w := by
    intro a b ha hb
    have : a * b ≤ 1 := by
      calc a * b ≤ 1 * 1 := Nat.mul_le_mul ha hb
        _ = 1 := rfl
    omega
  have hsub_w : ∀ a : ℕ, 1 - a < 2 ^ w := by intro a; omega
  have hite_le : ∀ P : Prop, [Decidable P] → (if P then 1 else 0) ≤ 1 := by
    intro P _; split_ifs <;> omega
  have hmul_le : ∀ a b : ℕ, a ≤ 1 → b ≤ 1 → a * b ≤ 1 := by
    intro a b ha hb
    calc a * b ≤ 1 * 1 := Nat.mul_le_mul ha hb
      _ = 1 := rfl
  have hd_le := deltaPosVal_le_one
    (omegaPosVal n omega (l₁.getD a₁ 0))
    (omegaPosVal n omega (l₁.getD b₁ 0))
    (omegaPosVal n omega (l₂.getD a₂ 0))
    (omegaPosVal n omega (l₂.getD b₂ 0))
  have hdelta_eval : deltaPosExpr.eval w s = some (deltaPosVal
      (omegaPosVal n omega (l₁.getD a₁ 0))
      (omegaPosVal n omega (l₁.getD b₁ 0))
      (omegaPosVal n omega (l₂.getD a₂ 0))
      (omegaPosVal n omega (l₂.getD b₂ 0))) := by
    dsimp [deltaPosExpr, deltaPosVal]
    simp only [Expr.eval, BinOp.eval, BinOp.raw, hr20, hr21, hr22, hr23,
      checkWord_of_lt hw,
      checkWord_of_lt hp₁_w, checkWord_of_lt hp₂_w,
      checkWord_of_lt hq₁_w, checkWord_of_lt hq₂_w,
      checkWord_of_lt (hite_w _), checkWord_of_lt (hsub_w _)]
  dsimp [segPairTestExpr, segPairTestVal]
  simp only [Expr.eval, BinOp.eval, BinOp.raw, hdelta_eval, hr20, hr21, hr22, hr23,
    checkWord_of_lt h0_w,
    checkWord_of_lt hp₁_w, checkWord_of_lt hp₂_w,
    checkWord_of_lt hq₁_w, checkWord_of_lt hq₂_w,
    checkWord_of_lt (hite_w _)]
  rw [checkWord_of_lt (hmul_w _ _ (hite_le _) (hite_le _))]
  dsimp only
  rw [checkWord_of_lt (hmul_w _ _ (hite_le _) (hmul_le _ _ (hite_le _) (hite_le _)))]
  dsimp only
  rw [checkWord_of_lt (hmul_w _ _ (hite_le _) (hmul_le _ _ (hite_le _) (hmul_le _ _ (hite_le _) (hite_le _))))]
  dsimp only
  rw [checkWord_of_lt (hmul_w _ _ (hmul_le _ _ (hite_le _) (hmul_le _ _ (hite_le _) (hmul_le _ _ (hite_le _) (hite_le _)))) hd_le)]

/-- Condition expression testing `isHVert x.n x.omega v` from `r_p = omegaPosVal x.n x.omega v.1`
and `r_v = v.1` (with `r_0 = x.n`). -/
def isHVertCondExpr (r_p r_v : Reg) : Expr :=
  .op .add (.reg r_p) (.op .sub (.const 1) (.op .lt (.reg r_v) (.reg 0)))

theorem stepPrevH_exec {w : ℕ} (x : Alg81Input)
    {u₀ v₀ : Fin (x.n + x.omega.length)} (R : (auxGraph81 x.G x.omega).Walk u₀ v₀)
    (r_p r_v r_prev r_k : Reg) (_hne_prev_k : r_prev ≠ r_k)
    {k : ℕ} (hk_lt : k < R.length) (hk1_w : k + 1 < 2 ^ w)
    (hw : 1 < 2 ^ w) (hN_w : x.n + x.omega.length < 2 ^ w)
    {s : State}
    (hr0 : s.regs 0 = x.n)
    (hrk : s.regs r_k = k)
    (hrprev : s.regs r_prev = prevH x.n x.omega R.support k)
    (hrv : s.regs r_v = (R.support[k + 1]'(by rw [Walk.length_support]; omega)).1)
    (hrp : s.regs r_p = omegaPosVal x.n x.omega (R.support[k + 1]'(by rw [Walk.length_support]; omega)).1) :
    ∃ s' t,
      Exec w (.ite (isHVertCondExpr r_p r_v)
        (.assign r_prev (.op .add (.reg r_k) (.const 1))) .skip) s s' t ∧
      t ≤ 11 ∧
      s'.arrs = s.arrs ∧
      s'.regs r_prev = prevH x.n x.omega R.support (k + 1) ∧
      (∀ r : Reg, r ≠ r_prev → s'.regs r = s.regs r) := by
  have hk1_support : k + 1 < R.support.length := by rw [Walk.length_support]; omega
  set vk := R.support[k + 1]'hk1_support
  change s.regs r_v = vk.1 at hrv
  change s.regs r_p = omegaPosVal x.n x.omega vk.1 at hrp
  have hvk_w : vk.1 < 2 ^ w := by have := vk.2; omega
  have hn_w : x.n < 2 ^ w := by omega
  have hk_w : k < 2 ^ w := by omega
  have hp_le := omegaPosVal_le x.n x.omega vk.1
  have hp_w : omegaPosVal x.n x.omega vk.1 < 2 ^ w := by omega
  have hite_w : (if vk.1 < x.n then 1 else 0) < 2 ^ w := by split_ifs <;> omega
  have hsub_w : 1 - (if vk.1 < x.n then 1 else 0) < 2 ^ w := by omega
  have hadd_w : omegaPosVal x.n x.omega vk.1 + (1 - (if vk.1 < x.n then 1 else 0)) < 2 ^ w := by
    split_ifs with hlt
    · omega
    · simp [omegaPosVal, hlt, hw]
  have hcond_eval : (isHVertCondExpr r_p r_v).eval w s =
      some (omegaPosVal x.n x.omega vk.1 + (1 - (if vk.1 < x.n then 1 else 0))) := by
    dsimp [isHVertCondExpr]
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrp, hrv, hr0,
      hp_w, hw, hvk_w, hn_w, hite_w, hsub_w, hadd_w]
  by_cases hH : isHVert x.n x.omega vk = true
  · have hpos : omegaPosVal x.n x.omega vk.1 + (1 - (if vk.1 < x.n then 1 else 0)) ≠ 0 :=
      (isHVert_iff_omegaPosVal_add_sub vk).mpr hH
    let s₁ := s.setReg r_prev (k + 1)
    have hex_asgn : Exec w (.assign r_prev (.op .add (.reg r_k) (.const 1))) s s₁ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hk_w, hw, hk1_w])
    refine ⟨s₁, 7 + 4, .ite_true hcond_eval (by omega) hex_asgn, by omega, rfl, ?_, ?_⟩
    · simp [s₁, prevH, hk_lt, vk, hH]
    · intro r hr
      simp [s₁, State.setReg, hr]
  · have hzero : omegaPosVal x.n x.omega vk.1 + (1 - (if vk.1 < x.n then 1 else 0)) = 0 := by
      by_contra hne
      exact hH ((isHVert_iff_omegaPosVal_add_sub vk).mp hne)
    rw [hzero] at hcond_eval
    refine ⟨s, 7 + 1, .ite_false hcond_eval (.skip s), by omega, rfl, ?_, fun _ _ => rfl⟩
    simp [prevH, hk_lt, vk, hH, hrprev]

/-- Command updating `(r_7, r_8, r_9, r_10, r_11)` when `r_26 ≠ 0`. -/
def updateFoundCmd : Cmd :=
  .ite (.reg 26)
    (.seq (.assign 7 (.const 1))
      (.seq (.assign 8 (.reg 12))
        (.seq (.assign 9 (.op .add (.reg 15) (.const 1)))
          (.seq (.assign 10 (.reg 16))
            (.assign 11 (.op .add (.reg 17) (.const 1)))))))
    .skip

theorem updateFound_exec {w : ℕ} (x : Alg81Input)
    {u₁ v₁ u₂ v₂ : Fin (x.n + x.omega.length)}
    (R₁ : (auxGraph81 x.G x.omega).Walk u₁ v₁)
    (R₂ : (auxGraph81 x.G x.omega).Walk u₂ v₂)
    (hpath₁ : R₁.IsPath) (hpath₂ : R₂.IsPath)
    {k₁ k₂ : ℕ} (hk₁ : k₁ < R₁.length) (hk₂ : k₂ < R₂.length)
    (hk1_w : k₁ + 1 < 2 ^ w) (hk2_w : k₂ + 1 < 2 ^ w)
    (hw : 1 < 2 ^ w)
    {s : State}
    (hr12 : s.regs 12 = prevH x.n x.omega R₁.support k₁)
    (hr15 : s.regs 15 = k₁)
    (hr16 : s.regs 16 = prevH x.n x.omega R₂.support k₂)
    (hr17 : s.regs 17 = k₂)
    (hr26 : s.regs 26 = segPairTestVal x.n x.omega
      (R₁.support.map Fin.val) (R₂.support.map Fin.val)
      (prevH x.n x.omega R₁.support k₁) (k₁ + 1)
      (prevH x.n x.omega R₂.support k₂) (k₂ + 1))
    (hgood : s.regs 7 = 1 → IsGoodSegPair R₁ R₂ (s.regs 8) (s.regs 9) (s.regs 10) (s.regs 11)) :
    ∃ s' t,
      Exec w updateFoundCmd s s' t ∧
      t ≤ 15 ∧
      s'.arrs = s.arrs ∧
      (∀ r : Reg, r < 7 ∨ 11 < r → s'.regs r = s.regs r) ∧
      (s'.regs 7 = 1 → IsGoodSegPair R₁ R₂ (s'.regs 8) (s'.regs 9) (s'.regs 10) (s'.regs 11)) ∧
      (s.regs 7 = 1 → s'.regs 7 = 1) ∧
      (segPairTestVal x.n x.omega
        (R₁.support.map Fin.val) (R₂.support.map Fin.val)
        (prevH x.n x.omega R₁.support k₁) (k₁ + 1)
        (prevH x.n x.omega R₂.support k₂) (k₂ + 1) ≠ 0 → s'.regs 7 = 1) := by
  let test := segPairTestVal x.n x.omega
    (R₁.support.map Fin.val) (R₂.support.map Fin.val)
    (prevH x.n x.omega R₁.support k₁) (k₁ + 1)
    (prevH x.n x.omega R₂.support k₂) (k₂ + 1)
  have htest_le := segPairTestVal_le_one x.n x.omega
    (R₁.support.map Fin.val) (R₂.support.map Fin.val)
    (prevH x.n x.omega R₁.support k₁) (k₁ + 1)
    (prevH x.n x.omega R₂.support k₂) (k₂ + 1)
  have htest_w : test < 2 ^ w := by dsimp [test]; omega
  have hcond_eval : (Expr.reg 26).eval w s = some test := by
    simp [Expr.eval, checkWord, hr26, test, htest_w]
  by_cases hne : test = 0
  · rw [hne] at hcond_eval
    refine ⟨s, 1 + 1, .ite_false hcond_eval (.skip s), by omega, rfl,
      fun _ _ => rfl, hgood, id, fun h => absurd hne h⟩
  · have hprev1_le := prevH_le x.n x.omega R₁.support k₁
    have hprev2_le := prevH_le x.n x.omega R₂.support k₂
    have hk₁_w : k₁ < 2 ^ w := by omega
    have hk₂_w : k₂ < 2 ^ w := by omega
    have hprev1_w : prevH x.n x.omega R₁.support k₁ < 2 ^ w := by omega
    have hprev2_w : prevH x.n x.omega R₂.support k₂ < 2 ^ w := by omega
    let s₁ := s.setReg 7 1
    have hex₁ : Exec w (.assign 7 (.const 1)) s s₁ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw])
    let s₂ := s₁.setReg 8 (prevH x.n x.omega R₁.support k₁)
    have hex₂ : Exec w (.assign 8 (.reg 12)) s₁ s₂ 2 :=
      .assign (by simp [s₁, Expr.eval, checkWord, hr12, hprev1_w])
    let s₃ := s₂.setReg 9 (k₁ + 1)
    have hex₃ : Exec w (.assign 9 (.op .add (.reg 15) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr15, hk₁_w, hw, hk1_w])
    let s₄ := s₃.setReg 10 (prevH x.n x.omega R₂.support k₂)
    have hex₄ : Exec w (.assign 10 (.reg 16)) s₃ s₄ 2 :=
      .assign (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hr16, hprev2_w])
    let s₅ := s₄.setReg 11 (k₂ + 1)
    have hex₅ : Exec w (.assign 11 (.op .add (.reg 17) (.const 1))) s₄ s₅ 4 :=
      .assign (by simp [s₄, s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr17, hk₂_w, hw, hk2_w])
    refine ⟨s₅, 1 + (2 + (2 + (4 + (2 + 4)))),
      .ite_true hcond_eval (by omega) (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))),
      by omega, rfl, ?_, ?_, ?_, ?_⟩
    · intro r hr
      dsimp [Reg] at hr
      have hr7 : (r : Reg) ≠ 7 := by dsimp [Reg]; rcases hr with hr | hr <;> omega
      have hr8 : (r : Reg) ≠ 8 := by dsimp [Reg]; rcases hr with hr | hr <;> omega
      have hr9 : (r : Reg) ≠ 9 := by dsimp [Reg]; rcases hr with hr | hr <;> omega
      have hr10 : (r : Reg) ≠ 10 := by dsimp [Reg]; rcases hr with hr | hr <;> omega
      have hr11 : (r : Reg) ≠ 11 := by dsimp [Reg]; rcases hr with hr | hr <;> omega
      simp [s₅, s₄, s₃, s₂, s₁, State.setReg, hr7, hr8, hr9, hr10, hr11]
    · intro _
      simp only [s₅, s₄, s₃, s₂, s₁, State.setReg]
      exact isGoodSegPair_of_segPairTestVal R₁ R₂ hpath₁ hpath₂ hk₁ hk₂ hne
    · intro _; simp [s₅, s₄, s₃, s₂, s₁, State.setReg]
    · intro _; simp [s₅, s₄, s₃, s₂, s₁, State.setReg]

/-- Inner loop body of `findGoodSegPairProg` over `k₂` in `r_17`. -/
def findGoodSegPairInnerBody : Cmd :=
  .seq (.assign 24 (.read 34 (.reg 16)))
    (.seq (.assign 25 (.read 34 (.op .add (.reg 17) (.const 1))))
      (.seq (.assign 22 (.read 29 (.reg 24)))
        (.seq (.assign 23 (.read 29 (.reg 25)))
          (.seq (.assign 26 segPairTestExpr)
            (.seq updateFoundCmd
              (.ite (isHVertCondExpr 23 25)
                (.assign 16 (.op .add (.reg 17) (.const 1))) .skip))))))

/-- Outer loop body of `findGoodSegPairProg` over `k₁` in `r_15`. -/
def findGoodSegPairOuterBody : Cmd :=
  .seq (.assign 18 (.read 33 (.reg 12)))
    (.seq (.assign 19 (.read 33 (.op .add (.reg 15) (.const 1))))
      (.seq (.assign 20 (.read 29 (.reg 18)))
        (.seq (.assign 21 (.read 29 (.reg 19)))
          (.seq (.assign 16 (.const 0))
            (.seq (.assign 17 (.const 0))
              (.seq (forUp 17 (.reg 14) findGoodSegPairInnerBody)
                (.ite (isHVertCondExpr 21 19)
                  (.assign 12 (.op .add (.reg 15) (.const 1))) .skip)))))))

/-- Scan all pairs of `H`-segments `(k₁, k₂)` of the paths in `33` and `34` to record a pair of
crossing bottom segments `(a₁, b₁, a₂, b₂)` in registers `(8, 9, 10, 11)`. -/
def findGoodSegPairProg : Cmd :=
  .seq (.assign 5 (.len 33))
    (.seq (.assign 6 (.len 34))
      (.seq (.assign 7 (.const 0))
        (.seq (.assign 8 (.const 0))
          (.seq (.assign 9 (.const 0))
            (.seq (.assign 10 (.const 0))
              (.seq (.assign 11 (.const 0))
                (.seq (.assign 12 (.const 0))
                  (.seq (.assign 13 (.op .sub (.reg 5) (.const 1)))
                    (.seq (.assign 14 (.op .sub (.reg 6) (.const 1)))
                      (.seq (.assign 15 (.const 0))
                        (forUp 15 (.reg 13) findGoodSegPairOuterBody)))))))))))

/-- Outer loop invariant of `findGoodSegPairProg` at step `k₁ ≤ R₁.length`. -/
def SegPairOuterInv (x : Alg81Input) (s₀ : State)
    {u₁ v₁ u₂ v₂ : Fin (x.n + x.omega.length)}
    (R₁ : (auxGraph81 x.G x.omega).Walk u₁ v₁)
    (R₂ : (auxGraph81 x.G x.omega).Walk u₂ v₂)
    (k₁ : ℕ) (s : State) : Prop :=
  s.arrs = s₀.arrs ∧
  s.regs 0 = x.n ∧
  s.regs 12 = prevH x.n x.omega R₁.support k₁ ∧
  s.regs 13 = R₁.length ∧
  s.regs 14 = R₂.length ∧
  s.regs 15 = k₁ ∧
  (s.regs 7 = 1 → IsGoodSegPair R₁ R₂ (s.regs 8) (s.regs 9) (s.regs 10) (s.regs 11)) ∧
  (∀ j₁ < k₁, ∀ j₂ < R₂.length,
    segPairTestVal x.n x.omega
      (R₁.support.map Fin.val) (R₂.support.map Fin.val)
      (prevH x.n x.omega R₁.support j₁) (j₁ + 1)
      (prevH x.n x.omega R₂.support j₂) (j₂ + 1) ≠ 0 →
    s.regs 7 = 1)

/-- Inner loop invariant of `findGoodSegPairProg` at `(k₁, k₂)`. -/
def SegPairInnerInv (x : Alg81Input) (s₀ : State)
    {u₁ v₁ u₂ v₂ : Fin (x.n + x.omega.length)}
    (R₁ : (auxGraph81 x.G x.omega).Walk u₁ v₁)
    (R₂ : (auxGraph81 x.G x.omega).Walk u₂ v₂)
    (k₁ : ℕ) (hk₁ : k₁ < R₁.length) (k₂ : ℕ) (s : State) : Prop :=
  let a₁ := prevH x.n x.omega R₁.support k₁
  let b₁ := k₁ + 1
  s.arrs = s₀.arrs ∧
  s.regs 0 = x.n ∧
  s.regs 12 = a₁ ∧
  s.regs 13 = R₁.length ∧
  s.regs 14 = R₂.length ∧
  s.regs 15 = k₁ ∧
  s.regs 16 = prevH x.n x.omega R₂.support k₂ ∧
  s.regs 17 = k₂ ∧
  s.regs 18 = (R₁.support[a₁]'(by
    have := prevH_le x.n x.omega R₁.support k₁; rw [Walk.length_support]; omega)).1 ∧
  s.regs 19 = (R₁.support[b₁]'(by rw [Walk.length_support]; omega)).1 ∧
  s.regs 20 = omegaPosVal x.n x.omega (R₁.support[a₁]'(by
    have := prevH_le x.n x.omega R₁.support k₁; rw [Walk.length_support]; omega)).1 ∧
  s.regs 21 = omegaPosVal x.n x.omega (R₁.support[b₁]'(by rw [Walk.length_support]; omega)).1 ∧
  (s.regs 7 = 1 → IsGoodSegPair R₁ R₂ (s.regs 8) (s.regs 9) (s.regs 10) (s.regs 11)) ∧
  (∀ j₁ < k₁, ∀ j₂ < R₂.length,
    segPairTestVal x.n x.omega
      (R₁.support.map Fin.val) (R₂.support.map Fin.val)
      (prevH x.n x.omega R₁.support j₁) (j₁ + 1)
      (prevH x.n x.omega R₂.support j₂) (j₂ + 1) ≠ 0 →
    s.regs 7 = 1) ∧
  (∀ j₂ < k₂,
    segPairTestVal x.n x.omega
      (R₁.support.map Fin.val) (R₂.support.map Fin.val)
      a₁ b₁ (prevH x.n x.omega R₂.support j₂) (j₂ + 1) ≠ 0 →
    s.regs 7 = 1)

theorem findGoodSegPairProg_exec {w : ℕ} (x : Alg81Input) (hk : 4 ≤ x.omega.length)
    (R₁ : (auxGraph81 x.G x.omega).Walk (s1Vert x.n x.omega.length hk) (t1Vert x.n x.omega.length hk))
    (R₂ : (auxGraph81 x.G x.omega).Walk (s2Vert x.n x.omega.length hk) (t2Vert x.n x.omega.length hk))
    (hpath₁ : R₁.IsPath) (hpath₂ : R₂.IsPath)
    (hdisj : List.Disjoint R₁.support R₂.support)
    (hw : 1 < 2 ^ w) (hN_w : x.n + x.omega.length < 2 ^ w)
    {s₀ : State}
    (hr0 : s₀.regs 0 = x.n)
    (h33 : s₀.arrs 33 = R₁.support.map Fin.val)
    (h34 : s₀.arrs 34 = R₂.support.map Fin.val)
    (hlen29 : (s₀.arrs 29).length = x.n + x.omega.length)
    (h29 : ∀ u (hu : u < x.n + x.omega.length),
      (s₀.arrs 29)[u]'(by rw [hlen29]; exact hu) = omegaPosVal x.n x.omega u) :
    ∃ s' t,
      Exec w findGoodSegPairProg s₀ s' t ∧
      t ≤ 83 * ((x.n + x.omega.length) * (x.n + x.omega.length)) +
        40 * (x.n + x.omega.length) + 40 ∧
      s'.arrs = s₀.arrs ∧
      IsGoodSegPair R₁ R₂ (s'.regs 8) (s'.regs 9) (s'.regs 10) (s'.regs 11) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hk_w : x.omega.length < 2 ^ w := by omega
  have hl₁_len : R₁.support.length ≤ x.n + x.omega.length := by
    simpa [Fintype.card_fin] using hpath₁.support_nodup.length_le_card
  have hl₂_len : R₂.support.length ≤ x.n + x.omega.length := by
    simpa [Fintype.card_fin] using hpath₂.support_nodup.length_le_card
  have hR₁_len : R₁.length < x.n + x.omega.length := by
    rw [Walk.length_support] at hl₁_len; omega
  have hR₂_len : R₂.length < x.n + x.omega.length := by
    rw [Walk.length_support] at hl₂_len; omega
  have hl₁_w : R₁.length + 1 < 2 ^ w := by omega
  have hl₂_w : R₂.length + 1 < 2 ^ w := by omega
  have hR₁_w : R₁.length < 2 ^ w := by omega
  have hR₂_w : R₂.length < 2 ^ w := by omega
  let s₁ := s₀.setReg 5 R₁.support.length
  have hex₁ : Exec w (.assign 5 (.len 33)) s₀ s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h33, hl₁_w])
  let s₂ := s₁.setReg 6 R₂.support.length
  have hex₂ : Exec w (.assign 6 (.len 34)) s₁ s₂ 2 :=
    .assign (by simp [s₁, Expr.eval, checkWord, h34, hl₂_w])
  let s₃ := s₂.setReg 7 0
  have hex₃ : Exec w (.assign 7 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₄ := s₃.setReg 8 0
  have hex₄ : Exec w (.assign 8 (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₅ := s₄.setReg 9 0
  have hex₅ : Exec w (.assign 9 (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₆ := s₅.setReg 10 0
  have hex₆ : Exec w (.assign 10 (.const 0)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₇ := s₆.setReg 11 0
  have hex₇ : Exec w (.assign 11 (.const 0)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₈ := s₇.setReg 12 0
  have hex₈ : Exec w (.assign 12 (.const 0)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₉ := s₈.setReg 13 R₁.length
  have hex₉ : Exec w (.assign 13 (.op .sub (.reg 5) (.const 1))) s₈ s₉ 4 :=
    .assign (by
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hl₁_w, hw, hR₁_w])
  let s₁₀ := s₉.setReg 14 R₂.length
  have hex₁₀ : Exec w (.assign 14 (.op .sub (.reg 6) (.const 1))) s₉ s₁₀ 4 :=
    .assign (by
      simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hl₂_w, hw, hR₂_w])
  let s₁₁ := s₁₀.setReg 15 0
  have hex₁₁ : Exec w (.assign 15 (.const 0)) s₁₀ s₁₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hOuter₀ : SegPairOuterInv x s₀ R₁ R₂ 0 s₁₁ := by
    refine ⟨rfl,
      by simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr0],
      by simp [s₁₁, s₁₀, s₉, s₈, prevH],
      by simp [s₁₁, s₁₀, s₉],
      by simp [s₁₁, s₁₀],
      by simp [s₁₁],
      by simp [s₁₁, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, State.setReg],
      fun j₁ hj₁ => by omega⟩
  have hOuterLoop :
      ⦃SegPairOuterInv x s₀ R₁ R₂ 0⦄[w]
        forUp 15 (.reg 13) findGoodSegPairOuterBody
      ⦃SegPairOuterInv x s₀ R₁ R₂ R₁.length⦄ ≤
        fun _ => 3 + R₁.length * (7 + (32 + R₂.length * (7 + 76))) := by
    apply Triple.forUp_const (SegPairOuterInv x s₀ R₁ R₂) R₁.length
      (32 + R₂.length * (7 + 76)) hw hR₁_w
    · intro k₁ _ s ⟨_, _, _, hr13, _, hr15, _, _⟩
      exact ⟨hr15, by simp [Expr.eval, checkWord, hr13, hR₁_w]⟩
    · intro k₁ hk₁ s_k₁ ⟨harr_k₁, hr0_k₁, hr12_k₁, hr13_k₁, hr14_k₁, hr15_k₁, hgood_k₁, hprev_k₁⟩
      have ha₁_le : prevH x.n x.omega R₁.support k₁ ≤ k₁ := prevH_le x.n x.omega R₁.support k₁
      have hb₁_lt : k₁ + 1 < R₁.support.length := by rw [Walk.length_support]; omega
      have ha₁_lt : prevH x.n x.omega R₁.support k₁ < R₁.support.length := by omega
      have hk₁_w : k₁ < 2 ^ w := by omega
      have hb₁_w : k₁ + 1 < 2 ^ w := by omega
      have ha₁_w : prevH x.n x.omega R₁.support k₁ < 2 ^ w := by omega
      have hu₁_w : (R₁.support[prevH x.n x.omega R₁.support k₁]'ha₁_lt).1 < 2 ^ w := by
        have := (R₁.support[prevH x.n x.omega R₁.support k₁]'ha₁_lt).2; omega
      have hv₁_w : (R₁.support[k₁ + 1]'hb₁_lt).1 < 2 ^ w := by
        have := (R₁.support[k₁ + 1]'hb₁_lt).2; omega
      have hp₁_w : omegaPosVal x.n x.omega (R₁.support[prevH x.n x.omega R₁.support k₁]'ha₁_lt).1 < 2 ^ w := by
        have := omegaPosVal_le x.n x.omega (R₁.support[prevH x.n x.omega R₁.support k₁]'ha₁_lt).1; omega
      have hp₂_w : omegaPosVal x.n x.omega (R₁.support[k₁ + 1]'hb₁_lt).1 < 2 ^ w := by
        have := omegaPosVal_le x.n x.omega (R₁.support[k₁ + 1]'hb₁_lt).1; omega
      have hget_a₁ : (R₁.support.map Fin.val).getD (prevH x.n x.omega R₁.support k₁) 0 =
          (R₁.support[prevH x.n x.omega R₁.support k₁]'ha₁_lt).1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem ha₁_lt]
        rfl
      have hget_b₁ : (R₁.support.map Fin.val).getD (k₁ + 1) 0 =
          (R₁.support[k₁ + 1]'hb₁_lt).1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_getElem hb₁_lt]
        rfl
      have ha₁_le_len : prevH x.n x.omega R₁.support k₁ ≤ R₁.length := by omega
      let sa₁ := s_k₁.setReg 18 (R₁.support[prevH x.n x.omega R₁.support k₁]'ha₁_lt).1
      have hexa₁ : Exec w (.assign 18 (.read 33 (.reg 12))) s_k₁ sa₁ 3 :=
        .assign (by
          simp [Expr.eval, checkWord, hr12_k₁, harr_k₁, h33, ha₁_w, ha₁_le_len, hu₁_w])
      let sa₂ := sa₁.setReg 19 (R₁.support[k₁ + 1]'hb₁_lt).1
      have hexa₂ : Exec w (.assign 19 (.read 33 (.op .add (.reg 15) (.const 1)))) sa₁ sa₂ 5 :=
        .assign (by
          simp [sa₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr15_k₁, hk₁_w, hw, hb₁_w,
            harr_k₁, h33, hk₁, hv₁_w])
      let sa₃ := sa₂.setReg 20 (omegaPosVal x.n x.omega (R₁.support[prevH x.n x.omega R₁.support k₁]'ha₁_lt).1)
      have hexa₃ : Exec w (.assign 20 (.read 29 (.reg 18))) sa₂ sa₃ 3 :=
        .assign (by
          have hu_lt := (R₁.support[prevH x.n x.omega R₁.support k₁]'ha₁_lt).2
          simp [sa₂, sa₁, Expr.eval, checkWord, hu₁_w, harr_k₁, hlen29, hu_lt, h29, hp₁_w])
      let sa₄ := sa₃.setReg 21 (omegaPosVal x.n x.omega (R₁.support[k₁ + 1]'hb₁_lt).1)
      have hexa₄ : Exec w (.assign 21 (.read 29 (.reg 19))) sa₃ sa₄ 3 :=
        .assign (by
          have hv_lt := (R₁.support[k₁ + 1]'hb₁_lt).2
          simp [sa₃, sa₂, sa₁, Expr.eval, checkWord, hv₁_w, harr_k₁, hlen29, hv_lt, h29, hp₂_w])
      let sa₅ := sa₄.setReg 16 0
      have hexa₅ : Exec w (.assign 16 (.const 0)) sa₄ sa₅ 2 :=
        .assign (by simp [Expr.eval, checkWord, h0_w])
      let sa₆ := sa₅.setReg 17 0
      have hexa₆ : Exec w (.assign 17 (.const 0)) sa₅ sa₆ 2 :=
        .assign (by simp [Expr.eval, checkWord, h0_w])
      have hInner₀ : SegPairInnerInv x s₀ R₁ R₂ k₁ hk₁ 0 sa₆ := by
        refine ⟨harr_k₁,
          by simp [sa₆, sa₅, sa₄, sa₃, sa₂, sa₁, hr0_k₁],
          by simp [sa₆, sa₅, sa₄, sa₃, sa₂, sa₁, hr12_k₁],
          by simp [sa₆, sa₅, sa₄, sa₃, sa₂, sa₁, hr13_k₁],
          by simp [sa₆, sa₅, sa₄, sa₃, sa₂, sa₁, hr14_k₁],
          by simp [sa₆, sa₅, sa₄, sa₃, sa₂, sa₁, hr15_k₁],
          by simp [sa₆, sa₅, prevH],
          by simp [sa₆],
          by simp [sa₆, sa₅, sa₄, sa₃, sa₂, sa₁],
          by simp [sa₆, sa₅, sa₄, sa₃, sa₂],
          by simp [sa₆, sa₅, sa₄, sa₃],
          by simp [sa₆, sa₅, sa₄],
          by simpa [sa₆, sa₅, sa₄, sa₃, sa₂, sa₁, State.setReg] using hgood_k₁,
          by simpa [sa₆, sa₅, sa₄, sa₃, sa₂, sa₁, State.setReg] using hprev_k₁,
          fun j₂ hj₂ => by omega⟩
      have hInnerLoop :
          ⦃SegPairInnerInv x s₀ R₁ R₂ k₁ hk₁ 0⦄[w]
            forUp 17 (.reg 14) findGoodSegPairInnerBody
          ⦃SegPairInnerInv x s₀ R₁ R₂ k₁ hk₁ R₂.length⦄ ≤
            fun _ => 3 + R₂.length * (7 + 76) := by
        apply Triple.forUp_const (SegPairInnerInv x s₀ R₁ R₂ k₁ hk₁) R₂.length 76 hw hR₂_w
        · intro k₂ _ s ⟨_, _, _, _, hr14, _, _, hr17, _, _, _, _, _, _, _⟩
          exact ⟨hr17, by simp [Expr.eval, checkWord, hr14, hR₂_w]⟩
        · intro k₂ hk₂ s_k₂
            ⟨harr_2, hr0_2, hr12_2, hr13_2, hr14_2, hr15_2, hr16_2, hr17_2,
             hr18_2, hr19_2, hr20_2, hr21_2, hgood_2, hprev1_2, hprev2_2⟩
          have ha₂_le : prevH x.n x.omega R₂.support k₂ ≤ k₂ := prevH_le x.n x.omega R₂.support k₂
          have hb₂_lt : k₂ + 1 < R₂.support.length := by rw [Walk.length_support]; omega
          have ha₂_lt : prevH x.n x.omega R₂.support k₂ < R₂.support.length := by omega
          have hk₂_w : k₂ < 2 ^ w := by omega
          have hb₂_w : k₂ + 1 < 2 ^ w := by omega
          have ha₂_w : prevH x.n x.omega R₂.support k₂ < 2 ^ w := by omega
          have hu₂_w : (R₂.support[prevH x.n x.omega R₂.support k₂]'ha₂_lt).1 < 2 ^ w := by
            have := (R₂.support[prevH x.n x.omega R₂.support k₂]'ha₂_lt).2; omega
          have hv₂_w : (R₂.support[k₂ + 1]'hb₂_lt).1 < 2 ^ w := by
            have := (R₂.support[k₂ + 1]'hb₂_lt).2; omega
          have hq₁_w : omegaPosVal x.n x.omega (R₂.support[prevH x.n x.omega R₂.support k₂]'ha₂_lt).1 < 2 ^ w := by
            have := omegaPosVal_le x.n x.omega (R₂.support[prevH x.n x.omega R₂.support k₂]'ha₂_lt).1; omega
          have hq₂_w : omegaPosVal x.n x.omega (R₂.support[k₂ + 1]'hb₂_lt).1 < 2 ^ w := by
            have := omegaPosVal_le x.n x.omega (R₂.support[k₂ + 1]'hb₂_lt).1; omega
          have hget_a₂ : (R₂.support.map Fin.val).getD (prevH x.n x.omega R₂.support k₂) 0 =
              (R₂.support[prevH x.n x.omega R₂.support k₂]'ha₂_lt).1 := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_eq_getElem ha₂_lt]
            rfl
          have hget_b₂ : (R₂.support.map Fin.val).getD (k₂ + 1) 0 =
              (R₂.support[k₂ + 1]'hb₂_lt).1 := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_map,
              List.getElem?_eq_getElem hb₂_lt]
            rfl
          have ha₂_le_len : prevH x.n x.omega R₂.support k₂ ≤ R₂.length := by omega
          let sb₁ := s_k₂.setReg 24 (R₂.support[prevH x.n x.omega R₂.support k₂]'ha₂_lt).1
          have hexb₁ : Exec w (.assign 24 (.read 34 (.reg 16))) s_k₂ sb₁ 3 :=
            .assign (by
              simp [Expr.eval, checkWord, hr16_2, harr_2, h34, ha₂_w, ha₂_le_len, hu₂_w])
          let sb₂ := sb₁.setReg 25 (R₂.support[k₂ + 1]'hb₂_lt).1
          have hexb₂ : Exec w (.assign 25 (.read 34 (.op .add (.reg 17) (.const 1)))) sb₁ sb₂ 5 :=
            .assign (by
              simp [sb₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr17_2, hk₂_w, hw, hb₂_w,
                harr_2, h34, hk₂, hv₂_w])
          let sb₃ := sb₂.setReg 22 (omegaPosVal x.n x.omega (R₂.support[prevH x.n x.omega R₂.support k₂]'ha₂_lt).1)
          have hexb₃ : Exec w (.assign 22 (.read 29 (.reg 24))) sb₂ sb₃ 3 :=
            .assign (by
              have hu_lt := (R₂.support[prevH x.n x.omega R₂.support k₂]'ha₂_lt).2
              simp [sb₂, sb₁, Expr.eval, checkWord, hu₂_w, harr_2, hlen29, hu_lt, h29, hq₁_w])
          let sb₄ := sb₃.setReg 23 (omegaPosVal x.n x.omega (R₂.support[k₂ + 1]'hb₂_lt).1)
          have hexb₄ : Exec w (.assign 23 (.read 29 (.reg 25))) sb₃ sb₄ 3 :=
            .assign (by
              have hv_lt := (R₂.support[k₂ + 1]'hb₂_lt).2
              simp [sb₃, sb₂, sb₁, Expr.eval, checkWord, hv₂_w, harr_2, hlen29, hv_lt, h29, hq₂_w])
          let testVal := segPairTestVal x.n x.omega
            (R₁.support.map Fin.val) (R₂.support.map Fin.val)
            (prevH x.n x.omega R₁.support k₁) (k₁ + 1)
            (prevH x.n x.omega R₂.support k₂) (k₂ + 1)
          let sb₅ := sb₄.setReg 26 testVal
          have hexb₅ : Exec w (.assign 26 segPairTestExpr) sb₄ sb₅ 34 :=
            .assign (segPairTestExpr_eval (s := sb₄) x.omega
              (R₁.support.map Fin.val) (R₂.support.map Fin.val)
              (prevH x.n x.omega R₁.support k₁) (k₁ + 1)
              (prevH x.n x.omega R₂.support k₂) (k₂ + 1) hw hk_w
              (by rw [hget_a₁]; exact hr20_2)
              (by rw [hget_b₁]; exact hr21_2)
              (by rw [hget_a₂]; rfl)
              (by rw [hget_b₂]; rfl))
          rcases updateFound_exec x R₁ R₂ hpath₁ hpath₂ hk₁ hk₂ hb₁_w hb₂_w hw
              (s := sb₅)
              (by simp [sb₅, sb₄, sb₃, sb₂, sb₁, hr12_2])
              (by simp [sb₅, sb₄, sb₃, sb₂, sb₁, hr15_2])
              (by simp [sb₅, sb₄, sb₃, sb₂, sb₁, hr16_2])
              (by simp [sb₅, sb₄, sb₃, sb₂, sb₁, hr17_2])
              (by simp [sb₅, testVal])
              (by simpa [sb₅, sb₄, sb₃, sb₂, sb₁, State.setReg] using hgood_2) with
            ⟨sb₆, tb₆, hexb₆, htb₆, harr_b6, hreg_b6, hgood_b6, hmon_b6, hcur_b6⟩
          rcases stepPrevH_exec x R₂ 23 25 16 17 (by decide) hk₂ hb₂_w hw hN_w
              (s := sb₆)
              (by rw [hreg_b6 0 (by decide)]; simp [sb₅, sb₄, sb₃, sb₂, sb₁, hr0_2])
              (by rw [hreg_b6 17 (by decide)]; simp [sb₅, sb₄, sb₃, sb₂, sb₁, hr17_2])
              (by rw [hreg_b6 16 (by decide)]; simp [sb₅, sb₄, sb₃, sb₂, sb₁, hr16_2])
              (by rw [hreg_b6 25 (by decide)]; simp [sb₅, sb₄, sb₃, sb₂])
              (by rw [hreg_b6 23 (by decide)]; simp [sb₅, sb₄]) with
            ⟨sb₇, tb₇, hexb₇, htb₇, harr_b7, hr16_b7, hreg_b7⟩
          refine ⟨sb₇, 3 + (5 + (3 + (3 + (34 + (tb₆ + tb₇))))),
            .seq hexb₁ (.seq hexb₂ (.seq hexb₃ (.seq hexb₄ (.seq hexb₅ (.seq hexb₆ hexb₇))))),
            by dsimp only; omega, ?_,
            by rw [hreg_b7 17 (by decide), hreg_b6 17 (by decide)]; simp [sb₅, sb₄, sb₃, sb₂, sb₁, hr17_2]⟩
          have hr7_eq : sb₇.regs 7 = sb₆.regs 7 := hreg_b7 7 (by decide)
          have hr8_eq : sb₇.regs 8 = sb₆.regs 8 := hreg_b7 8 (by decide)
          have hr9_eq : sb₇.regs 9 = sb₆.regs 9 := hreg_b7 9 (by decide)
          have hr10_eq : sb₇.regs 10 = sb₆.regs 10 := hreg_b7 10 (by decide)
          have hr11_eq : sb₇.regs 11 = sb₆.regs 11 := hreg_b7 11 (by decide)
          have hmon_2 : s_k₂.regs 7 = 1 → sb₇.regs 7 = 1 := by
            intro h7
            rw [hr7_eq]
            apply hmon_b6
            simpa [sb₅, sb₄, sb₃, sb₂, sb₁, State.setReg] using h7
          refine ⟨by simp [harr_b7, harr_b6, sb₅, sb₄, sb₃, sb₂, sb₁, harr_2],
            by simp [hreg_b7 0 (by decide), hreg_b6 0 (by decide), sb₅, sb₄, sb₃, sb₂, sb₁, hr0_2],
            by simp [hreg_b7 12 (by decide), hreg_b6 12 (by decide), sb₅, sb₄, sb₃, sb₂, sb₁, hr12_2],
            by simp [hreg_b7 13 (by decide), hreg_b6 13 (by decide), sb₅, sb₄, sb₃, sb₂, sb₁, hr13_2],
            by simp [hreg_b7 14 (by decide), hreg_b6 14 (by decide), sb₅, sb₄, sb₃, sb₂, sb₁, hr14_2],
            by simp [hreg_b7 15 (by decide), hreg_b6 15 (by decide), sb₅, sb₄, sb₃, sb₂, sb₁, hr15_2],
            by simp [hr16_b7],
            by simp [State.setReg],
            by simp [hreg_b7 18 (by decide), hreg_b6 18 (by decide), sb₅, sb₄, sb₃, sb₂, sb₁, hr18_2],
            by simp [hreg_b7 19 (by decide), hreg_b6 19 (by decide), sb₅, sb₄, sb₃, sb₂, sb₁, hr19_2],
            by simp [hreg_b7 20 (by decide), hreg_b6 20 (by decide), sb₅, sb₄, sb₃, sb₂, sb₁, hr20_2],
            by simp [hreg_b7 21 (by decide), hreg_b6 21 (by decide), sb₅, sb₄, sb₃, sb₂, sb₁, hr21_2],
            by simpa [State.setReg, hr7_eq, hr8_eq, hr9_eq, hr10_eq, hr11_eq] using hgood_b6,
            fun j₁ hj₁ j₂ hj₂ htest => by
              rw [State.setReg_regs_ne _ _ (by decide)]
              exact hmon_2 (hprev1_2 j₁ hj₁ j₂ hj₂ htest),
            fun j₂ hj₂ htest => by
              rw [State.setReg_regs_ne _ _ (by decide)]
              by_cases hj₂_eq : j₂ = k₂
              · subst hj₂_eq
                rw [hr7_eq]
                exact hcur_b6 htest
              · exact hmon_2 (hprev2_2 j₂ (by omega) htest)⟩
      rcases hInnerLoop sa₆ hInner₀ with
        ⟨sa₇, ta₇, hexa₇, hta₇,
         harr_a7, hr0_a7, hr12_a7, hr13_a7, hr14_a7, hr15_a7, _, _,
         _, hr19_a7, _, hr21_a7, hgood_a7, hprev1_a7, hprev2_a7⟩
      dsimp only at hta₇
      rcases stepPrevH_exec x R₁ 21 19 12 15 (by decide) hk₁ hb₁_w hw hN_w
          (s := sa₇) hr0_a7 hr15_a7 hr12_a7 hr19_a7 hr21_a7 with
        ⟨sa₈, ta₈, hexa₈, hta₈, harr_a8, hr12_a8, hreg_a8⟩
      refine ⟨sa₈, 3 + (5 + (3 + (3 + (2 + (2 + (ta₇ + ta₈)))))),
        .seq hexa₁ (.seq hexa₂ (.seq hexa₃ (.seq hexa₄ (.seq hexa₅ (.seq hexa₆ (.seq hexa₇ hexa₈)))))),
        by dsimp only; omega, ?_,
        by rw [hreg_a8 15 (by decide)]; exact hr15_a7⟩
      have hr7_a8 : sa₈.regs 7 = sa₇.regs 7 := hreg_a8 7 (by decide)
      have hr8_a8 : sa₈.regs 8 = sa₇.regs 8 := hreg_a8 8 (by decide)
      have hr9_a8 : sa₈.regs 9 = sa₇.regs 9 := hreg_a8 9 (by decide)
      have hr10_a8 : sa₈.regs 10 = sa₇.regs 10 := hreg_a8 10 (by decide)
      have hr11_a8 : sa₈.regs 11 = sa₇.regs 11 := hreg_a8 11 (by decide)
      refine ⟨by simp [harr_a8, harr_a7],
        by simp [hreg_a8 0 (by decide), hr0_a7],
        by simp [hr12_a8],
        by simp [hreg_a8 13 (by decide), hr13_a7],
        by simp [hreg_a8 14 (by decide), hr14_a7],
        by simp [State.setReg],
        by simpa [State.setReg, hr7_a8, hr8_a8, hr9_a8, hr10_a8, hr11_a8] using hgood_a7,
        fun j₁ hj₁ j₂ hj₂ htest => ?_⟩
      rw [State.setReg_regs_ne _ _ (by decide), hr7_a8]
      by_cases hj₁_eq : j₁ = k₁
      · subst hj₁_eq
        exact hprev2_a7 j₂ hj₂ htest
      · exact hprev1_a7 j₁ (by omega) j₂ hj₂ htest
  rcases hOuterLoop s₁₁ hOuter₀ with
    ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, harr₁₂, _, _, _, _, _, hgood₁₂, hall₁₂⟩
  dsimp only at ht₁₂
  rcases exists_segPairTestVal_of_auxGraph81_paths x.nodup_omega hk R₁ R₂ hpath₁ hpath₂ hdisj with
    ⟨k₁_star, hk₁_star, k₂_star, hk₂_star, htest_star⟩
  have hr7_1 : s₁₂.regs 7 = 1 :=
    hall₁₂ k₁_star hk₁_star k₂_star hk₂_star (by omega)
  have hmul_le :
      R₁.length * (7 + (32 + R₂.length * (7 + 76))) ≤
        83 * ((x.n + x.omega.length) * (x.n + x.omega.length)) +
          39 * (x.n + x.omega.length) := by
    have h1 : R₁.length * (7 + (32 + R₂.length * (7 + 76))) =
        39 * R₁.length + 83 * (R₁.length * R₂.length) := by ring
    have h2 : R₁.length * R₂.length ≤ (x.n + x.omega.length) * (x.n + x.omega.length) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  refine ⟨s₁₂,
    2 + (2 + (2 + (2 + (2 + (2 + (2 + (2 + (4 + (4 + (2 + t₁₂)))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ hex₁₂)))))))))),
    by omega, harr₁₂, hgood₁₂ hr7_1⟩



/-- Copy the slice `(arr(33).drop r_8).take (r_9 + 1 - r_8)` and
`(arr(34).drop r_10).take (r_11 + 1 - r_10)` into `outArr` with header `[1, len₁, len₂]`. -/
def alg81WriteSlicesOutProg : Cmd :=
  .seq (.assign 5 (.op .sub (.op .add (.reg 9) (.const 1)) (.reg 8)))
    (.seq (.assign 6 (.op .sub (.op .add (.reg 11) (.const 1)) (.reg 10)))
      (.seq (.alloc outArr (.op .add (.op .add (.const 3) (.reg 5)) (.reg 6)))
        (.seq (.write outArr (.const 0) (.const 1))
          (.seq (.write outArr (.const 1) (.reg 5))
            (.seq (.write outArr (.const 2) (.reg 6))
              (.seq (.assign 7 (.const 0))
                (.seq (forUp 7 (.reg 5)
                    (.write outArr (.op .add (.const 3) (.reg 7))
                      (.read 33 (.op .add (.reg 8) (.reg 7)))))
                  (.seq (.assign 7 (.const 0))
                    (forUp 7 (.reg 6)
                      (.write outArr
                        (.op .add (.op .add (.const 3) (.reg 5)) (.reg 7))
                        (.read 34 (.op .add (.reg 10) (.reg 7)))))))))))))

theorem copySliceToOut_exec {w : ℕ} (a_src : ℕ) (hne_src : a_src ≠ outArr)
    (off_expr : Expr) (off : ℕ)
    (r_start r_len : ℕ) (hr_start_ne : r_start ≠ 7) (hr_len_ne : r_len ≠ 7)
    (start len : ℕ)
    (pre src post : List ℕ)
    (hw : 1 < 2 ^ w)
    (hslice_bound : start + len ≤ src.length)
    (hstart_len_w : start + len < 2 ^ w)
    (hoff_w : off + len < 2 ^ w)
    (hsrc_w : ∀ v ∈ src, v < 2 ^ w)
    (hpre_len : pre.length = off)
    (rem k : ℕ) (hrem : k + rem = len)
    {s : State}
    (hoff_eval : ∀ s' : State, s'.regs 5 = s.regs 5 → off_expr.eval w s' = some off)
    (hsrc : s.arrs a_src = src)
    (hout : s.arrs outArr =
      pre ++ ((src.drop start).take len).take k ++ List.replicate (len - k) 0 ++ post)
    (hrstart : s.regs r_start = start)
    (hrlen : s.regs r_len = len)
    (hr7 : s.regs 7 = k) :
    ∃ s' t,
      Exec w (forUp 7 (.reg r_len)
        (.write outArr (.op .add off_expr (.reg 7))
          (.read a_src (.op .add (.reg r_start) (.reg 7))))) s s' t ∧
      t ≤ 3 + (14 + off_expr.cost) * rem ∧
      s'.arrs outArr = pre ++ (src.drop start).take len ++ post ∧
      s'.arrs a_src = src ∧
      s'.regs 5 = s.regs 5 ∧
      s'.regs r_start = start ∧
      s'.regs r_len = len := by
  let slice := (src.drop start).take len
  have hslice_len : slice.length = len := by
    simp [slice, List.length_take, List.length_drop]
    omega
  have h0_w : 0 < 2 ^ w := by omega
  have hlen_w : len < 2 ^ w := by omega
  have hstart_w : start < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = len := by omega
    rw [hk_eq] at hr7 hout
    have hcond : (Expr.op .lt (.reg 7) (.reg r_len)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr7, hrlen, hlen_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, ?_, hsrc, rfl, hrstart, hrlen⟩
    simpa [List.take_take] using hout
  | succ rem ih =>
    have hk_lt : k < len := by omega
    have hk_lt_slice : k < slice.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have hstart_k_lt : start + k < src.length := by omega
    have hstart_k_w : start + k < 2 ^ w := by omega
    have hoff_k_w : off + k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 7) (.reg r_len)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr7, hrlen, hk_w, hlen_w, hk_lt, hw]
    have hval_w : src[start + k] < 2 ^ w := hsrc_w src[start + k] (List.getElem_mem hstart_k_lt)
    have hslice_elem : slice[k]'hk_lt_slice = src[start + k]'hstart_k_lt := by
      simp [slice]
    have hidx_eval : (Expr.op .add off_expr (.reg 7)).eval w s = some (off + k) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hoff_eval s rfl, hr7, hk_w, hoff_k_w]
    have hval_eval :
        (Expr.read a_src (.op .add (.reg r_start) (.reg 7))).eval w s = some (slice[k]'hk_lt_slice) := by
      rw [hslice_elem]
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrstart, hr7,
        hstart_w, hk_w, hstart_k_w, hstart_k_lt, hsrc, hval_w]
    have hout_len : off + k < (s.arrs outArr).length := by
      have hlen_eq : (s.arrs outArr).length = off + len + post.length := by
        rw [hout, List.length_append, List.length_append, List.length_append, hpre_len,
          List.length_take, hslice_len, List.length_replicate]
        omega
      omega
    let s₁ := s.writeArr outArr (off + k) (slice[k]'hk_lt_slice)
    have hex_w : Exec w (.write outArr (.op .add off_expr (.reg 7))
        (.read a_src (.op .add (.reg r_start) (.reg 7))))
        s s₁ (off_expr.cost + 7) := by
      have hcost : (Expr.op .add off_expr (.reg 7)).cost +
          (Expr.read a_src (.op .add (.reg r_start) (.reg 7))).cost + 1 =
          off_expr.cost + 7 := rfl
      rw [← hcost]
      exact .write hidx_eval hval_eval hout_len
    let s₂ := s₁.setReg 7 (k + 1)
    have hex_inc : Exec w (.assign 7 (.op .add (.reg 7) (.const 1))) s₁ s₂ 4 :=
      .assign (by
        simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr7, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    have hout₂ : s₂.arrs outArr =
        pre ++ slice.take (k + 1) ++ List.replicate (len - (k + 1)) 0 ++ post := by
      simp only [s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, hout]
      rw [List.set_append_left _ _ (by
        rw [List.length_append, List.length_append, hpre_len, List.length_take, hslice_len,
          List.length_replicate]
        omega)]
      rw [List.set_append_right _ _ (by
        rw [List.length_append, hpre_len, List.length_take, hslice_len]
        omega)]
      have hsub1 : off + k - (pre ++ slice.take k).length = 0 := by
        rw [List.length_append, hpre_len, List.length_take, hslice_len]
        omega
      have hrep : len - k = (len - (k + 1)) + 1 := by omega
      rw [hsub1, hrep, List.replicate_succ, List.set_cons_zero]
      rw [List.take_add_one, List.getElem?_eq_getElem hk_lt_slice, Option.toList_some]
      simp only [slice, List.append_assoc, List.singleton_append]
    have hsrc₂ : s₂.arrs a_src = src := by
      have hne_arr : (a_src : Arr) ≠ outArr := by dsimp [Arr, outArr]; omega
      simp [s₂, s₁, hne_arr, hsrc]
    rcases ih (k + 1) (by omega)
        (fun s' hs' => hoff_eval s' (by simpa [s₂, s₁, State.setReg] using hs'))
        hsrc₂
        hout₂
        (by
          have hr_ne' : (r_start : Reg) ≠ 7 := by dsimp [Reg]; omega
          simp [s₂, s₁, State.setReg, hr_ne', hrstart])
        (by
          have hr_ne' : (r_len : Reg) ≠ 7 := by dsimp [Reg]; omega
          simp [s₂, s₁, State.setReg, hr_ne', hrlen])
        (by simp [s₂]) with
      ⟨s₃, t₃, hex₃, ht₃, hout₃, hsrc₃, hr5₃, hrstart₃, hrlen₃⟩
    refine ⟨s₃, 3 + ((off_expr.cost + 7) + 4) + t₃,
      .while_true hcond (by omega) (.seq hex_w hex_inc) hex₃,
      ?_, hout₃, hsrc₃,
      by simpa [s₂, s₁, State.setReg] using hr5₃, hrstart₃, hrlen₃⟩
    have hmul_step : (14 + off_expr.cost) * (rem + 1) =
        (14 + off_expr.cost) * rem + (14 + off_expr.cost) := Nat.mul_succ _ _
    omega

theorem alg81WriteSlicesOutProg_exec {w N a₁ b₁ a₂ b₂ : ℕ} {l₁ l₂ : List ℕ} {s₀ : State}
    (hw3 : 3 < 2 ^ w)
    (hl₁_len : l₁.length ≤ N) (hl₂_len : l₂.length ≤ N)
    (ha₁_lt : a₁ < b₁) (hb₁_lt : b₁ < l₁.length)
    (ha₂_lt : a₂ < b₂) (hb₂_lt : b₂ < l₂.length)
    (hl₁_w : ∀ v ∈ l₁, v < 2 ^ w) (hl₂_w : ∀ v ∈ l₂, v < 2 ^ w)
    (h32N_w : 3 + 2 * N < 2 ^ w)
    (hr8 : s₀.regs 8 = a₁) (hr9 : s₀.regs 9 = b₁)
    (hr10 : s₀.regs 10 = a₂) (hr11 : s₀.regs 11 = b₂)
    (h33 : s₀.arrs 33 = l₁) (h34 : s₀.arrs 34 = l₂) :
    ∃ s' t,
      Exec w alg81WriteSlicesOutProg s₀ s' t ∧
      t ≤ 34 * N + 50 ∧
      s'.arrs outArr =
        [1, b₁ + 1 - a₁, b₂ + 1 - a₂] ++
          (l₁.drop a₁).take (b₁ + 1 - a₁) ++
          (l₂.drop a₂).take (b₂ + 1 - a₂) := by
  let len₁ := b₁ + 1 - a₁
  let len₂ := b₂ + 1 - a₂
  have hlen₁_le : len₁ ≤ N := by dsimp [len₁]; omega
  have hlen₂_le : len₂ ≤ N := by dsimp [len₂]; omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have ha₁_w : a₁ < 2 ^ w := by omega
  have hb₁_w : b₁ < 2 ^ w := by omega
  have hb₁1_w : b₁ + 1 < 2 ^ w := by omega
  have ha₂_w : a₂ < 2 ^ w := by omega
  have hb₂_w : b₂ < 2 ^ w := by omega
  have hb₂1_w : b₂ + 1 < 2 ^ w := by omega
  have hl1_w : len₁ < 2 ^ w := by omega
  have hl2_w : len₂ < 2 ^ w := by omega
  have h3l1_w : 3 + len₁ < 2 ^ w := by omega
  have htot_w : 3 + len₁ + len₂ < 2 ^ w := by omega
  let s₁ := s₀.setReg 5 len₁
  have hex₁ : Exec w (.assign 5 (.op .sub (.op .add (.reg 9) (.const 1)) (.reg 8))) s₀ s₁ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, hr8, hb₁_w, hw, hb₁1_w, ha₁_w, len₁, hl1_w])
  let s₂ := s₁.setReg 6 len₂
  have hex₂ : Exec w (.assign 6 (.op .sub (.op .add (.reg 11) (.const 1)) (.reg 10))) s₁ s₂ 6 :=
    .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr10, hb₂_w, hw, hb₂1_w, ha₂_w, len₂, hl2_w])
  let s₃ := s₂.setArr outArr (List.replicate (3 + len₁ + len₂) 0)
  have hex₃ : Exec w (.alloc outArr (.op .add (.op .add (.const 3) (.reg 5)) (.reg 6)))
      s₂ s₃ (5 + (3 + len₁ + len₂)) :=
    .alloc (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw3, hl1_w, h3l1_w, hl2_w, htot_w])
  let s₄ := s₃.writeArr outArr 0 1
  have hex₄ : Exec w (.write outArr (.const 0) (.const 1)) s₃ s₄ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w]) (by simp [Expr.eval, checkWord, hw])
      (by simp [s₃])
  let s₅ := s₄.writeArr outArr 1 len₁
  have hex₅ : Exec w (.write outArr (.const 1) (.reg 5)) s₄ s₅ 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp [s₄, s₃, s₂, s₁, Expr.eval, checkWord, hl1_w])
      (by simp [s₄, s₃]; omega)
  let s₆ := s₅.writeArr outArr 2 len₂
  have hex₆ : Exec w (.write outArr (.const 2) (.reg 6)) s₅ s₆ 3 :=
    .write (by simp [Expr.eval, checkWord, hw2])
      (by simp [s₅, s₄, s₃, s₂, Expr.eval, checkWord, hl2_w])
      (by simp [s₅, s₄, s₃]; omega)
  let s₇ := s₆.setReg 7 0
  have hex₇ : Exec w (.assign 7 (.const 0)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hout₇ : s₇.arrs outArr =
      [1, len₁, len₂] ++ ((l₁.drop a₁).take len₁).take 0 ++ List.replicate (len₁ - 0) 0 ++
        List.replicate len₂ 0 := by
    have hrep : List.replicate (3 + len₁ + len₂) 0 =
        0 :: 0 :: 0 :: (List.replicate len₁ 0 ++ List.replicate len₂ 0) := by
      rw [show 3 + len₁ + len₂ = (len₁ + len₂) + 1 + 1 + 1 by omega]
      rw [List.replicate_succ, List.replicate_succ, List.replicate_succ, List.replicate_add]
    simp only [s₇, s₆, s₅, s₄, s₃, State.setReg_arrs, State.writeArr_arrs_self,
      State.setArr_arrs_self, hrep]
    rfl
  rcases copySliceToOut_exec (w := w) 33 (by decide) (.const 3) 3 8 5 (by decide) (by decide)
      a₁ len₁ [1, len₁, len₂] l₁ (List.replicate len₂ 0)
      hw (by dsimp [len₁]; omega) (by dsimp [len₁]; omega) h3l1_w hl₁_w rfl len₁ 0 (by omega)
      (s := s₇)
      (fun _ _ => by simp [Expr.eval, checkWord, hw3])
      (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, h33])
      hout₇
      (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr8])
      (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁])
      (by simp [s₇]) with
    ⟨s₈, t₈, hex₈, ht₈, hout₈, _, hr5_8, _, _⟩
  dsimp [Expr.cost] at ht₈
  let s₉ := s₈.setReg 7 0
  have hex₉ : Exec w (.assign 7 (.const 0)) s₈ s₉ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have h34_9 : s₉.arrs 34 = l₂ := by
    have hnot34 : (34 : Arr) ∉ (forUp 7 (.reg 5)
        (.write outArr (.op .add (.const 3) (.reg 7))
          (.read 33 (.op .add (.reg 8) (.reg 7))))).writtenArrs := by
      simp [forUp, Cmd.writtenArrs]
    have heq := Exec.arrs_eq_of_not_mem_writtenArrs hex₈ hnot34
    simp [s₉, heq, s₇, s₆, s₅, s₄, s₃, s₂, s₁, h34]
  have hr6_9 : s₉.regs 6 = len₂ := by
    have hnot6 : (6 : Reg) ∉ (forUp 7 (.reg 5)
        (.write outArr (.op .add (.const 3) (.reg 7))
          (.read 33 (.op .add (.reg 8) (.reg 7))))).writtenRegs := by
      simp [forUp, Cmd.writtenRegs]
    have heq := Exec.regs_eq_of_not_mem_writtenRegs hex₈ hnot6
    simp [s₉, heq, s₇, s₆, s₅, s₄, s₃, s₂]
  have hr10_9 : s₉.regs 10 = a₂ := by
    have hnot10 : (10 : Reg) ∉ (forUp 7 (.reg 5)
        (.write outArr (.op .add (.const 3) (.reg 7))
          (.read 33 (.op .add (.reg 8) (.reg 7))))).writtenRegs := by
      simp [forUp, Cmd.writtenRegs]
    have heq := Exec.regs_eq_of_not_mem_writtenRegs hex₈ hnot10
    simp [s₉, heq, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr10]
  have hout₉ : s₉.arrs outArr =
      ([1, len₁, len₂] ++ (l₁.drop a₁).take len₁) ++
        ((l₂.drop a₂).take len₂).take 0 ++ List.replicate (len₂ - 0) 0 ++ [] := by
    simp [s₉, hout₈]
  rcases copySliceToOut_exec (w := w) 34 (by decide)
      (.op .add (.const 3) (.reg 5)) (3 + len₁) 10 6 (by decide) (by decide)
      a₂ len₂ ([1, len₁, len₂] ++ (l₁.drop a₁).take len₁) l₂ []
      hw (by dsimp [len₂]; omega) (by dsimp [len₂]; omega) htot_w hl₂_w
      (by simp [List.length_take, List.length_drop]; omega) len₂ 0 (by omega)
      (s := s₉)
      (fun s' hs' => by
        have hr5' : s'.regs 5 = len₁ := by
          rw [hs']; simp [s₉, hr5_8, s₇, s₆, s₅, s₄, s₃, s₂, s₁]
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr5', hw3, hl1_w, h3l1_w])
      h34_9 hout₉ hr10_9 hr6_9 (by simp [s₉]) with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hout₁₀, _, _, _, _⟩
  dsimp [Expr.cost] at ht₁₀
  refine ⟨s₁₀, 6 + (6 + ((5 + (3 + len₁ + len₂)) + (3 + (3 + (3 + (2 + (t₈ + (2 + t₁₀)))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ hex₁₀)))))))),
    by omega, by simpa using hout₁₀⟩

/-- Word RAM program that extracts a cross `(P, Q)` in `(G, Ω)` from the two vertex-disjoint paths
`R₁, R₂` in `auxGraph81 G omega` stored in arrays `33` and `34`, and writes their vertex lists to
`outArr`. -/
def alg81ExtractCrossProg : Cmd :=
  .seq buildOmegaPosProg
    (.seq findGoodSegPairProg
      alg81WriteSlicesOutProg)

theorem alg81ExtractCrossProg_exec {w : ℕ} (x : Alg81Input) (hk : 4 ≤ x.omega.length)
    (R₁ : (auxGraph81 x.G x.omega).Walk (s1Vert x.n x.omega.length hk) (t1Vert x.n x.omega.length hk))
    (R₂ : (auxGraph81 x.G x.omega).Walk (s2Vert x.n x.omega.length hk) (t2Vert x.n x.omega.length hk))
    (hpath₁ : R₁.IsPath) (hpath₂ : R₂.IsPath)
    (hdisj : List.Disjoint R₁.support R₂.support)
    (hw3 : 3 < 2 ^ w)
    (h32N_w : 3 + 2 * (x.n + x.omega.length) < 2 ^ w)
    (hin_w : 3 + 2 * (edgeListOf x.G).length + x.omega.length < 2 ^ w)
    {s₀ : State}
    (hin₀ : s₀.arrs inArr = encAlg81In x)
    (hr0 : s₀.regs 0 = x.n)
    (hr2 : s₀.regs 2 = 2 + 2 * (edgeListOf x.G).length)
    (hr3 : s₀.regs 3 = x.omega.length)
    (hr4 : s₀.regs 4 = x.n + x.omega.length)
    (h33 : s₀.arrs 33 = R₁.support.map Fin.val)
    (h34 : s₀.arrs 34 = R₂.support.map Fin.val) :
    ∃ s' t,
      Exec w alg81ExtractCrossProg s₀ s' t ∧
      t ≤ 83 * ((x.n + x.omega.length) * (x.n + x.omega.length)) +
        102 * (x.n + x.omega.length) + 100 ∧
      s'.arrs inArr = encAlg81In x ∧
      ∃ cw : CrossWitness x.G x.omega,
        cw.IsValid ∧
        s'.arrs outArr =
          [1, cw.P.support.length, cw.Q.support.length] ++
            cw.P.support.map Fin.val ++ cw.Q.support.map Fin.val := by
  have hw : 1 < 2 ^ w := by omega
  have hN_w : x.n + x.omega.length < 2 ^ w := by omega
  have h2N_w : 2 * (x.n + x.omega.length) < 2 ^ w := by omega
  have hl₁_len : (R₁.support.map Fin.val).length ≤ x.n + x.omega.length := by
    rw [List.length_map]
    simpa [Fintype.card_fin] using hpath₁.support_nodup.length_le_card
  have hl₂_len : (R₂.support.map Fin.val).length ≤ x.n + x.omega.length := by
    rw [List.length_map]
    simpa [Fintype.card_fin] using hpath₂.support_nodup.length_le_card
  have hl₁_w : ∀ v ∈ R₁.support.map Fin.val, v < 2 ^ w := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨u, _, rfl⟩
    have := u.2; omega
  have hl₂_w : ∀ v ∈ R₂.support.map Fin.val, v < 2 ^ w := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨u, _, rfl⟩
    have := u.2; omega
  rcases buildOmegaPosProg_exec x hk hw3 h2N_w hin_w hin₀ hr0 hr2 hr3 hr4 with
    ⟨s₁, t₁, hex₁, ht₁, hin₁, hr0_1, _, _, harr₁, hlen29_1, h29_1⟩
  have h33_1 : s₁.arrs 33 = R₁.support.map Fin.val := by
    rw [harr₁ 33 (by decide)]; exact h33
  have h34_1 : s₁.arrs 34 = R₂.support.map Fin.val := by
    rw [harr₁ 34 (by decide)]; exact h34
  rcases findGoodSegPairProg_exec x hk R₁ R₂ hpath₁ hpath₂ hdisj hw hN_w
      hr0_1 h33_1 h34_1 hlen29_1 h29_1 with
    ⟨s₂, t₂, hex₂, ht₂, harr₂, hgood₂⟩
  have h33_2 : s₂.arrs 33 = R₁.support.map Fin.val := by rw [harr₂]; exact h33_1
  have h34_2 : s₂.arrs 34 = R₂.support.map Fin.val := by rw [harr₂]; exact h34_1
  have hin₂ : s₂.arrs inArr = encAlg81In x := by rw [harr₂]; exact hin₁
  have ⟨_, _, ha₁_lt, hb₁_lt, ha₂_lt, hb₂_lt, _⟩ := hgood₂
  rcases alg81WriteSlicesOutProg_exec (N := x.n + x.omega.length)
      hw3 hl₁_len hl₂_len ha₁_lt (by simpa using hb₁_lt) ha₂_lt (by simpa using hb₂_lt)
      hl₁_w hl₂_w h32N_w rfl rfl rfl rfl h33_2 h34_2 with
    ⟨s₃, t₃, hex₃, ht₃, hout₃⟩
  have hin₃ : s₃.arrs inArr = encAlg81In x := by
    have hnot0 : (0 : Arr) ∉ alg81WriteSlicesOutProg.writtenArrs := by decide
    rw [Exec.arrs_eq_of_not_mem_writtenArrs hex₃ hnot0]
    exact hin₂
  rcases crossWitness_of_isGoodSegPair x.nodup_omega hk hdisj hgood₂ with
    ⟨cw, hcw_valid, hlen_P, hlen_Q, hmap_P, hmap_Q⟩
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hin₃,
    cw, hcw_valid, ?_⟩
  rw [hout₃, ← hmap_P, ← hmap_Q, ← hlen_P, ← hlen_Q]

/-- End-to-end Word RAM program for GM XIII Algorithm (8.1), parameterized by Shiloach's program
`shiloachProg : Cmd`:
1. Reads `n = inArr[0]`, `m = inArr[1]`, sets `r_2 := 2 + 2 * m`, and reads `k = inArr[r_2]`.
2. If `k < 4`, allocates `outArr` of length `1` (`outArr = [0]`).
3. If `k ≥ 4`:
   - Sets `r_4 := n + k` (`N = |V(G ∪ H)|`), builds the `N × N` adjacency matrix of `G ∪ H`
     (`auxGraph81 G omega`) in array `28` (`buildAuxMatProg`), and converts it to CSR adjacency
     lists in arrays `(30, 31, 32)` (`matToAdjListRegProg`).
   - Sets `r_30 := N`, `r_31 := n` (`s₁`), `r_32 := n + 2` (`t₁`), `r_33 := n + 1` (`s₂`),
     `r_34 := n + 3` (`t₂`) and invokes `shiloachProg`.
   - If `r_35 ≠ 0`, extracts a cross `(P, Q)` in `(G, Ω)` and writes its two paths to `outArr`
     (`alg81ExtractCrossProg`); otherwise writes `[0]` to `outArr`. -/
def alg81Prog (shiloachProg : Cmd) : Cmd :=
  .seq (.assign 0 (.read inArr (.const 0)))
    (.seq (.assign 1 (.read inArr (.const 1)))
      (.seq (.assign 2 (.op .add (.const 2) (.op .mul (.const 2) (.reg 1))))
        (.seq (.assign 3 (.read inArr (.reg 2)))
          (.ite (.op .lt (.reg 3) (.const 4))
            (.alloc outArr (.const 1))
            (.seq (.assign 4 (.op .add (.reg 0) (.reg 3)))
              (.seq buildAuxMatProg
                (.seq (matToAdjListRegProg 4 28 30 31 32 5 6 7 8)
                  (.seq (.assign 30 (.reg 4))
                    (.seq (.assign 31 (.reg 0))
                      (.seq (.assign 32 (.op .add (.reg 0) (.const 2)))
                        (.seq (.assign 33 (.op .add (.reg 0) (.const 1)))
                          (.seq (.assign 34 (.op .add (.reg 0) (.const 3)))
                            (.seq shiloachProg
                              (.ite (.reg 35)
                                alg81ExtractCrossProg
                                (.alloc outArr (.const 1))))))))))))))))

/-- Pure reader from `outArr : List ℕ` to `Option (CrossWitness x.G x.omega)`:
reads `[1, lenP, lenQ] ++ P_verts ++ Q_verts` into the two walks `P` and `Q` of the cross using
`decGWalk`; returns `none` if the tag is not `1` or the vertex lists do not form walks. -/
def decAlg81Out (x : Alg81Input) (out : List ℕ) : Option (CrossWitness x.G x.omega) :=
  match out with
  | 1 :: lenP :: lenQ :: rest =>
    match decGWalk x.G (rest.take lenP), decGWalk x.G ((rest.drop lenP).take lenQ) with
    | some ⟨p₁, p₂, P⟩, some ⟨q₁, q₂, Q⟩ =>
      some ⟨p₁, p₂, q₁, q₂, P, Q⟩
    | _, _ => none
  | _ => none

/-- Validity predicate for the decoded output of Algorithm (8.1):
- `some w`: `w` is a valid cross in `(x.G, x.omega)` (`w.IsValid`), `(w.toGraphP, w.toGraphQ)` is a
  cross in `x.toSociety` (`x.toSociety.IsCross w.toGraphP w.toGraphQ`), and `x.toSociety` has a
  cross (`GM13.HasCross x.toSociety`).
- `none`: `(x.G, x.omega)` has no cross (`¬ HasCrossInSociety x.G x.omega` and
  `¬ GM13.HasCross x.toSociety`). -/
def IsValidAlg81Output (x : Alg81Input) (res : Option (CrossWitness x.G x.omega)) : Prop :=
  match res with
  | some w =>
    w.IsValid ∧
    x.toSociety.IsCross w.toGraphP w.toGraphQ ∧
    GM13.HasCross x.toSociety
  | none =>
    ¬ HasCrossInSociety x.G x.omega ∧
    ¬ GM13.HasCross x.toSociety

theorem decAlg81Out_encode (x : Alg81Input) (w : CrossWitness x.G x.omega) :
    decAlg81Out x
      ([1, w.P.support.length, w.Q.support.length] ++
        w.P.support.map Fin.val ++ w.Q.support.map Fin.val) = some w := by
  have hlenP : (w.P.support.map Fin.val).length = w.P.support.length := List.length_map _
  have hlenQ : (w.Q.support.map Fin.val).length = w.Q.support.length := List.length_map _
  have htakeP :
      (w.P.support.map Fin.val ++ w.Q.support.map Fin.val).take w.P.support.length =
        w.P.support.map Fin.val :=
    List.take_left' hlenP
  have hdropP :
      ((w.P.support.map Fin.val ++ w.Q.support.map Fin.val).drop w.P.support.length).take
        w.Q.support.length = w.Q.support.map Fin.val := by
    rw [List.drop_left' hlenP, ← hlenQ, List.take_length]
  rcases w with ⟨p₁, p₂, q₁, q₂, P, Q⟩
  dsimp only at htakeP hdropP ⊢
  simp only [List.cons_append, List.nil_append, decAlg81Out,
    htakeP, hdropP, decGWalk_support_map]

theorem decAlg81Out_valid_of_encode {x : Alg81Input} {w : CrossWitness x.G x.omega}
    (hw : w.IsValid) :
    IsValidAlg81Output x
      (decAlg81Out x
        ([1, w.P.support.length, w.Q.support.length] ++
          w.P.support.map Fin.val ++ w.Q.support.map Fin.val)) := by
  rw [decAlg81Out_encode]
  have hcr := CrossWitness.isCross_of_isValid x hw
  exact ⟨hw, hcr, ⟨_, _, hcr⟩⟩

theorem decAlg81Out_eq_none_of_zero (x : Alg81Input) :
    decAlg81Out x [0] = none := rfl

theorem alg81_time_bound {S C_sh n k m t₆ t₇ t_sh t_out : ℕ}
    (_hS_pos : 1 ≤ S) (hk_le_n : k ≤ n) (hS_ge_nm : n + m + 1 ≤ S)
    (hNN_le_4S : (n + k) * (n + k) ≤ 4 * S)
    (ht₆ : t₆ ≤ 4 * ((n + k) * (n + k)) + 38 * m + 90 * k + 20)
    (ht₇ : t₇ ≤ 26 * ((n + k) * (n + k)) + 24 * (n + k) + 12)
    (ht_sh_le : t_sh ≤ C_sh * (10 * S))
    (ht_out : t_out ≤ 83 * ((n + k) * (n + k)) + 102 * (n + k) + 100) :
    3 + (3 + (6 + (3 + (3 + (4 + (t₆ + (t₇ + (2 + (2 + (4 + (4 + (4 + (t_sh + (1 + t_out)))))))))))))) ≤
      (1200 + 10 * C_sh) * S := by
  have : (1200 + 10 * C_sh) * S = 1200 * S + C_sh * (10 * S) := by ring
  omega

/-- Complete execution specification for `alg81Prog shiloachProg`, preserving `inArr = 0` and
producing either a serialized `CrossWitness x.G x.omega` in `outArr` (starting with tag `1`) or
`[0]` when `(x.G, x.omega)` has no cross. -/
theorem alg81Prog_exec {shiloachProg : Cmd} {C_sh c_sh : ℕ}
    (_hC_sh : 0 < C_sh) (_hc_sh : 0 < c_sh)
    (hSh_spec : ∀ (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
      (lists : Fin N → List ℕ) (s₁ t₁ s₂ t₂ : Fin N),
      s₁ ≠ t₁ → s₁ ≠ s₂ → s₁ ≠ t₂ → t₁ ≠ s₂ → t₁ ≠ t₂ → s₂ ≠ t₂ →
      ∀ (w : ℕ), wordSize c_sh ((N + 1) * (G.edgeFinset.card + N + 1)) ≤ w →
      ∀ (s : State),
        IsAdjList G 30 31 32 lists s →
        (s.arrs 32).length < 2 ^ w →
        s.regs 30 = N →
        s.regs 31 = s₁.1 →
        s.regs 32 = t₁.1 →
        s.regs 33 = s₂.1 →
        s.regs 34 = t₂.1 →
        ∃ (s' : State) (t : ℕ),
          Exec w shiloachProg s s' t ∧
          t ≤ C_sh * (N + 1) * (G.edgeFinset.card + N + 1) ∧
          (∀ r < 30, s'.regs r = s.regs r) ∧
          (∀ a < 33, s'.arrs a = s.arrs a) ∧
          ((s'.regs 35 = 1 ∧
              ∃ (P₁ : G.Walk s₁ t₁) (P₂ : G.Walk s₂ t₂),
                P₁.IsPath ∧ P₂.IsPath ∧
                List.Disjoint P₁.support P₂.support ∧
                s'.arrs 33 = P₁.support.map Fin.val ∧
                s'.arrs 34 = P₂.support.map Fin.val) ∨
            (s'.regs 35 = 0 ∧
              ∀ (P₁ : G.Walk s₁ t₁) (P₂ : G.Walk s₂ t₂),
                P₁.IsPath → P₂.IsPath → ¬ List.Disjoint P₁.support P₂.support)))
    (x : Alg81Input) {w : ℕ}
    (hw_ge : wordSize (5 * c_sh + 4) (alg81Size x) ≤ w)
    {s₀ : State} (hs₀ : s₀.arrs inArr = encAlg81In x) :
    ∃ s' t,
      Exec w (alg81Prog shiloachProg) s₀ s' t ∧
      t ≤ (1200 + 10 * C_sh) * alg81Size x ∧
      s'.arrs 0 = encAlg81In x ∧
      ((∃ cw : CrossWitness x.G x.omega,
          cw.IsValid ∧
          s'.arrs outArr =
            [1, cw.P.support.length, cw.Q.support.length] ++
              cw.P.support.map Fin.val ++ cw.Q.support.map Fin.val) ∨
       (s'.arrs outArr = [0] ∧ ¬ HasCrossInSociety x.G x.omega)) := by
  have hm_eq : (edgeListOf x.G).length = x.G.edgeFinset.card :=
    length_edgeListOf_eq_card_edgeFinset x.G
  have hk_le_n : x.omega.length ≤ x.n := length_omega_le_n x.nodup_omega
  have hS_pos : 1 ≤ alg81Size x := by
    dsimp [alg81Size, societySize]
    exact Nat.mul_pos (by omega) (by omega)
  have hpow4 : (alg81Size x + 2) ^ 4 < 2 ^ w := by
    have hpow_c := pow_lt_two_pow_wordSize (c := 5 * c_sh + 4) (by omega) (alg81Size x)
    have hle : (alg81Size x + 2) ^ 4 ≤ (alg81Size x + 2) ^ (5 * c_sh + 4) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hpow_w : 2 ^ wordSize (5 * c_sh + 4) (alg81Size x) ≤ 2 ^ w :=
      Nat.pow_le_pow_right (by omega) hw_ge
    exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hle hpow_c) hpow_w
  have h16_le : 16 * (alg81Size x + 2) ≤ (alg81Size x + 2) ^ 4 := by
    have h3 : 3 ≤ alg81Size x + 2 := by omega
    have h16 : 16 ≤ (alg81Size x + 2) ^ 3 := by
      calc 16 ≤ 3 ^ 3 := by decide
        _ ≤ (alg81Size x + 2) ^ 3 := Nat.pow_le_pow_left h3 3
    have hmul := Nat.mul_le_mul_right (alg81Size x + 2) h16
    simpa [Nat.pow_succ] using hmul
  have h16S_w : 16 * (alg81Size x + 2) < 2 ^ w :=
    Nat.lt_of_le_of_lt h16_le hpow4
  have hS_ge_nm : x.n + (edgeListOf x.G).length + 1 ≤ alg81Size x := by
    dsimp [alg81Size, societySize]
    rw [← hm_eq]
    have : 1 * ((edgeListOf x.G).length + x.n + 1) ≤
        (x.n + 1) * ((edgeListOf x.G).length + x.n + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hNN_le_4S : (x.n + x.omega.length) * (x.n + x.omega.length) ≤ 4 * alg81Size x := by
    have h1 : x.n + x.omega.length ≤ 2 * (x.n + 1) := by omega
    have h2 : x.n + x.omega.length ≤ 2 * ((edgeListOf x.G).length + x.n + 1) := by omega
    calc (x.n + x.omega.length) * (x.n + x.omega.length)
      _ ≤ (2 * (x.n + 1)) * (2 * ((edgeListOf x.G).length + x.n + 1)) := Nat.mul_le_mul h1 h2
      _ = 4 * ((x.n + 1) * ((edgeListOf x.G).length + x.n + 1)) := by ring
      _ = 4 * alg81Size x := by dsimp [alg81Size, societySize]; rw [hm_eq]
  have hw4 : 4 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have hm_w : (edgeListOf x.G).length < 2 ^ w := by omega
  have hk_w : x.omega.length < 2 ^ w := by omega
  have h2m_w : 2 * (edgeListOf x.G).length < 2 ^ w := by omega
  have h22m_w : 2 + 2 * (edgeListOf x.G).length < 2 ^ w := by omega
  have hin_w : 3 + 2 * (edgeListOf x.G).length + x.omega.length < 2 ^ w := by omega
  obtain ⟨hlen_in, hget0, hget1, hget_k, _, _⟩ := inArr_getElem_alg81 x
  let s₁ := s₀.setReg 0 x.n
  have hex₁ : Exec w (.assign 0 (.read inArr (.const 0))) s₀ s₁ 3 :=
    .assign (by
      have hne_in : encAlg81In x ≠ [] := by
        intro h; have := congrArg List.length h; simp [hlen_in] at this
      simp [Expr.eval, checkWord, h0_w, hs₀, hne_in, hget0, hn_w])
  let s₂ := s₁.setReg 1 (edgeListOf x.G).length
  have hex₂ : Exec w (.assign 1 (.read inArr (.const 1))) s₁ s₂ 3 :=
    .assign (by
      have hidx : 1 < (encAlg81In x).length := by rw [hlen_in]; omega
      simp [s₁, Expr.eval, checkWord, hw, hs₀, hidx, hget1, hm_w])
  let s₃ := s₂.setReg 2 (2 + 2 * (edgeListOf x.G).length)
  have hex₃ : Exec w (.assign 2 (.op .add (.const 2) (.op .mul (.const 2) (.reg 1)))) s₂ s₃ 6 :=
    .assign (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw2, hm_w, h2m_w, h22m_w])
  let s₄ := s₃.setReg 3 x.omega.length
  have hex₄ : Exec w (.assign 3 (.read inArr (.reg 2))) s₃ s₄ 3 :=
    .assign (by
      have hidx : 2 + 2 * (edgeListOf x.G).length < (encAlg81In x).length := by
        rw [hlen_in]; omega
      simp [s₃, s₂, s₁, Expr.eval, checkWord, h22m_w, hs₀, hidx, hget_k, hk_w])
  by_cases hk_lt : x.omega.length < 4
  · have hcond_lt : (Expr.op .lt (.reg 3) (.const 4)).eval w s₄ = some 1 := by
      simp [s₄, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hk_w, hw4, hk_lt, hw]
    let s₅ := s₄.setArr outArr (List.replicate 1 0)
    have hex_alloc : Exec w (.alloc outArr (.const 1)) s₄ s₅ (1 + 1) :=
      .alloc (by simp [Expr.eval, checkWord, hw])
    refine ⟨s₅, 3 + (3 + (6 + (3 + (3 + (1 + 1))))),
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.ite_true hcond_lt (by omega) hex_alloc)))),
      le_trans (show 3 + (3 + (6 + (3 + (3 + (1 + 1))))) ≤ (1200 + 10 * C_sh) * 1 by omega)
        (Nat.mul_le_mul_left _ hS_pos),
      by simp [s₅, s₄, s₃, s₂, s₁, hs₀],
      Or.inr ⟨by simp [s₅], not_hasCross_of_lt_four x.G x.omega hk_lt⟩⟩
  · have hk : 4 ≤ x.omega.length := by omega
    have hcond_ge : (Expr.op .lt (.reg 3) (.const 4)).eval w s₄ = some 0 := by
      simp [s₄, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hk_w, hw4, hk_lt, h0_w]
    have hNN_w : (x.n + x.omega.length) * (x.n + x.omega.length) < 2 ^ w := by omega
    have hN_w : x.n + x.omega.length < 2 ^ w := by omega
    have h32N_w : 3 + 2 * (x.n + x.omega.length) < 2 ^ w := by omega
    let s₅ := s₄.setReg 4 (x.n + x.omega.length)
    have hex₅ : Exec w (.assign 4 (.op .add (.reg 0) (.reg 3))) s₄ s₅ 4 :=
      .assign (by simp [s₄, s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hn_w, hk_w, hN_w])
    rcases buildAuxMatProg_exec x hk hw3 hNN_w hin_w (s₀ := s₅)
        (by simp [s₅, s₄, s₃, s₂, s₁, hs₀])
        (by simp [s₅, s₄, s₃, s₂, s₁])
        (by simp [s₅, s₄, s₃, s₂])
        (by simp [s₅, s₄, s₃])
        (by simp [s₅, s₄])
        (by simp [s₅]) with
      ⟨s₆, t₆, hex₆, ht₆, hmat₆, hin₆, hregs₆⟩
    rcases matToAdjListRegProg_exec (auxGraph81 x.G x.omega) hw hNN_w hmat₆
        (by rw [hregs₆ 4 (by omega)]; simp [s₅]) with
      ⟨s₇, t₇, hex₇, ht₇, hadj₇, hent₇, hregs₇, harr₇⟩
    have hin₇ : s₇.arrs 0 = encAlg81In x := by
      rw [harr₇ 0 (by decide), hin₆]
    have hr0_7 : s₇.regs 0 = x.n := by
      rw [hregs₇ 0 (by omega), hregs₆ 0 (by omega)]; simp [s₅, s₄, s₃, s₂, s₁]
    have hr2_7 : s₇.regs 2 = 2 + 2 * (edgeListOf x.G).length := by
      rw [hregs₇ 2 (by omega), hregs₆ 2 (by omega)]; simp [s₅, s₄, s₃]
    have hr3_7 : s₇.regs 3 = x.omega.length := by
      rw [hregs₇ 3 (by omega), hregs₆ 3 (by omega)]; simp [s₅, s₄]
    have hr4_7 : s₇.regs 4 = x.n + x.omega.length := by
      rw [hregs₇ 4 (by omega), hregs₆ 4 (by omega)]; simp [s₅]
    let s₈ := s₇.setReg 30 (x.n + x.omega.length)
    have hex₈ : Exec w (.assign 30 (.reg 4)) s₇ s₈ 2 :=
      .assign (by simp [Expr.eval, checkWord, hr4_7, hN_w])
    let s₉ := s₈.setReg 31 x.n
    have hex₉ : Exec w (.assign 31 (.reg 0)) s₈ s₉ 2 :=
      .assign (by simp [s₈, Expr.eval, checkWord, hr0_7, hn_w])
    have hn2_w : x.n + 2 < 2 ^ w := by omega
    let s₁₀ := s₉.setReg 32 (x.n + 2)
    have hex₁₀ : Exec w (.assign 32 (.op .add (.reg 0) (.const 2))) s₉ s₁₀ 4 :=
      .assign (by simp [s₉, s₈, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr0_7, hn_w, hw2, hn2_w])
    have hn1_w : x.n + 1 < 2 ^ w := by omega
    let s₁₁ := s₁₀.setReg 33 (x.n + 1)
    have hex₁₁ : Exec w (.assign 33 (.op .add (.reg 0) (.const 1))) s₁₀ s₁₁ 4 :=
      .assign (by simp [s₁₀, s₉, s₈, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr0_7, hn_w, hw, hn1_w])
    have hn3_w : x.n + 3 < 2 ^ w := by omega
    let s₁₂ := s₁₁.setReg 34 (x.n + 3)
    have hex₁₂ : Exec w (.assign 34 (.op .add (.reg 0) (.const 3))) s₁₁ s₁₂ 4 :=
      .assign (by simp [s₁₁, s₁₀, s₉, s₈, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr0_7, hn_w, hw3, hn3_w])
    have h_s1_t1 : s1Vert x.n x.omega.length hk ≠ t1Vert x.n x.omega.length hk := by
      intro h; have := congrArg Fin.val h; simp [s1Vert, t1Vert, c1Vert] at this
    have h_s1_s2 : s1Vert x.n x.omega.length hk ≠ s2Vert x.n x.omega.length hk := by
      intro h; have := congrArg Fin.val h; simp [s1Vert, s2Vert, c1Vert] at this
    have h_s1_t2 : s1Vert x.n x.omega.length hk ≠ t2Vert x.n x.omega.length hk := by
      intro h; have := congrArg Fin.val h; simp [s1Vert, t2Vert, c1Vert] at this
    have h_t1_s2 : t1Vert x.n x.omega.length hk ≠ s2Vert x.n x.omega.length hk := by
      intro h; have := congrArg Fin.val h; simp [t1Vert, s2Vert, c1Vert] at this
    have h_t1_t2 : t1Vert x.n x.omega.length hk ≠ t2Vert x.n x.omega.length hk := by
      intro h; have := congrArg Fin.val h; simp [t1Vert, t2Vert, c1Vert] at this
    have h_s2_t2 : s2Vert x.n x.omega.length hk ≠ t2Vert x.n x.omega.length hk := by
      intro h; have := congrArg Fin.val h; simp [s2Vert, t2Vert, c1Vert] at this
    have h_sh_size_le :
        (x.n + x.omega.length + 1) * ((auxGraph81 x.G x.omega).edgeFinset.card + (x.n + x.omega.length) + 1) ≤
          10 * alg81Size x :=
      auxGraph81_shiloachSize_le x
    have hw_sh :
        wordSize c_sh ((x.n + x.omega.length + 1) *
          ((auxGraph81 x.G x.omega).edgeFinset.card + (x.n + x.omega.length) + 1)) ≤ w := by
      have h1 : wordSize c_sh ((x.n + x.omega.length + 1) *
          ((auxGraph81 x.G x.omega).edgeFinset.card + (x.n + x.omega.length) + 1)) ≤
          wordSize c_sh (10 * alg81Size x) := wordSize_mono_right c_sh h_sh_size_le
      have hlog : Nat.log 2 (10 * alg81Size x + 2) ≤ Nat.log 2 (alg81Size x + 2) + 4 := by
        have h3 : 10 * alg81Size x + 2 ≤ (alg81Size x + 2) * 2 ^ 4 := by omega
        calc Nat.log 2 (10 * alg81Size x + 2)
          _ ≤ Nat.log 2 ((alg81Size x + 2) * 2 ^ 4) := Nat.log_mono_right h3
          _ ≤ Nat.log 2 (alg81Size x + 2) + 4 := by
            have hpow_le : (alg81Size x + 2) * 2 ^ 4 < 2 ^ (Nat.log 2 (alg81Size x + 2) + 1 + 4) := by
              have hlt : alg81Size x + 2 < 2 ^ (Nat.log 2 (alg81Size x + 2) + 1) :=
                Nat.lt_pow_succ_log_self (by decide) _
              calc (alg81Size x + 2) * 2 ^ 4 < 2 ^ (Nat.log 2 (alg81Size x + 2) + 1) * 2 ^ 4 :=
                    Nat.mul_lt_mul_of_pos_right hlt (by decide)
                _ = 2 ^ (Nat.log 2 (alg81Size x + 2) + 1 + 4) := (Nat.pow_add 2 _ 4).symm
            exact Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow (by omega) hpow_le)
      dsimp [wordSize] at h1 hw_ge ⊢
      have hmul : c_sh * (Nat.log 2 (10 * alg81Size x + 2) + 1) ≤
          (5 * c_sh + 4) * (Nat.log 2 (alg81Size x + 2) + 1) := by
        have hlog1 : Nat.log 2 (10 * alg81Size x + 2) + 1 ≤ 5 * (Nat.log 2 (alg81Size x + 2) + 1) := by
          omega
        calc c_sh * (Nat.log 2 (10 * alg81Size x + 2) + 1)
          _ ≤ c_sh * (5 * (Nat.log 2 (alg81Size x + 2) + 1)) := Nat.mul_le_mul_left c_sh hlog1
          _ = (5 * c_sh) * (Nat.log 2 (alg81Size x + 2) + 1) := by ring
          _ ≤ (5 * c_sh + 4) * (Nat.log 2 (alg81Size x + 2) + 1) := Nat.mul_le_mul_right _ (by omega)
      omega
    rcases hSh_spec (x.n + x.omega.length) (auxGraph81 x.G x.omega)
        (adjListOf (auxGraph81 x.G x.omega))
        (s1Vert x.n x.omega.length hk) (t1Vert x.n x.omega.length hk)
        (s2Vert x.n x.omega.length hk) (t2Vert x.n x.omega.length hk)
        h_s1_t1 h_s1_s2 h_s1_t2 h_t1_s2 h_t1_t2 h_s2_t2
        w hw_sh s₁₂
        (hadj₇.of_arrs_eq rfl rfl rfl)
        (by simp [s₁₂, s₁₁, s₁₀, s₉, s₈, hent₇, hNN_w])
        (by simp [s₁₂, s₁₁, s₁₀, s₉, s₈, State.setReg])
        (by simp [s₁₂, s₁₁, s₁₀, s₉, State.setReg, s1Vert, c1Vert])
        (by simp [s₁₂, s₁₁, s₁₀, State.setReg, t1Vert, c1Vert])
        (by simp [s₁₂, s₁₁, State.setReg, s2Vert, c1Vert])
        (by simp [s₁₂, State.setReg, t2Vert, c1Vert]) with
      ⟨s₁₃, t_sh, hex_sh, ht_sh, hreg_sh, harr_sh, hres_sh⟩
    have hin₁₃ : s₁₃.arrs 0 = encAlg81In x := by
      rw [harr_sh 0 (by decide)]; exact hin₇
    have hr0_13 : s₁₃.regs 0 = x.n := by
      rw [hreg_sh 0 (by decide)]; simp [s₁₂, s₁₁, s₁₀, s₉, s₈, State.setReg, hr0_7]
    have hr2_13 : s₁₃.regs 2 = 2 + 2 * (edgeListOf x.G).length := by
      rw [hreg_sh 2 (by decide)]; simp [s₁₂, s₁₁, s₁₀, s₉, s₈, State.setReg, hr2_7]
    have hr3_13 : s₁₃.regs 3 = x.omega.length := by
      rw [hreg_sh 3 (by decide)]; simp [s₁₂, s₁₁, s₁₀, s₉, s₈, State.setReg, hr3_7]
    have hr4_13 : s₁₃.regs 4 = x.n + x.omega.length := by
      rw [hreg_sh 4 (by decide)]; simp [s₁₂, s₁₁, s₁₀, s₉, s₈, State.setReg, hr4_7]
    have ht_sh_le : t_sh ≤ C_sh * (10 * alg81Size x) := by
      rw [Nat.mul_assoc C_sh (x.n + x.omega.length + 1)] at ht_sh
      exact le_trans ht_sh (Nat.mul_le_mul_left C_sh h_sh_size_le)
    rcases hres_sh with ⟨hr35_1, P₁, P₂, hP₁, hP₂, hdisj, h33_13, h34_13⟩ | ⟨hr35_0, hno_paths⟩
    · have hcond_35 : (Expr.reg 35).eval w s₁₃ = some 1 := by
        simp [Expr.eval, checkWord, hr35_1, hw]
      rcases alg81ExtractCrossProg_exec x hk P₁ P₂ hP₁ hP₂ hdisj hw3 h32N_w hin_w
          hin₁₃ hr0_13 hr2_13 hr3_13 hr4_13 h33_13 h34_13 with
        ⟨s₁₄, t_out, hex_out, ht_out, hin₁₄, cw, hcw_valid, hout₁₄⟩
      refine ⟨s₁₄, _,
        .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.ite_false hcond_ge
          (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉
            (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂ (.seq hex_sh
              (.ite_true hcond_35 (by omega) hex_out)))))))))))))),
        alg81_time_bound hS_pos hk_le_n hS_ge_nm hNN_le_4S ht₆ ht₇ ht_sh_le ht_out,
        hin₁₄, Or.inl ⟨cw, hcw_valid, hout₁₄⟩⟩
    · have hcond_35 : (Expr.reg 35).eval w s₁₃ = some 0 := by
        simp [Expr.eval, checkWord, hr35_0, h0_w]
      let s₁₄ := s₁₃.setArr outArr (List.replicate 1 0)
      have hex_out : Exec w (.alloc outArr (.const 1)) s₁₃ s₁₄ (1 + 1) :=
        .alloc (by simp [Expr.eval, checkWord, hw])
      refine ⟨s₁₄, _,
        .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.ite_false hcond_ge
          (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉
            (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂ (.seq hex_sh
              (.ite_false hcond_35 hex_out)))))))))))))),
        alg81_time_bound hS_pos hk_le_n hS_ge_nm hNN_le_4S ht₆ ht₇ ht_sh_le (by omega),
        by simp [s₁₄, hin₁₃],
        Or.inr ⟨by simp [s₁₄],
          not_hasCross_of_no_auxGraph81_paths x.nodup_omega hk
            (fun ⟨R₁, R₂, hR₁, hR₂, hdisj⟩ => hno_paths R₁ R₂ hR₁ hR₂ hdisj)⟩⟩

/-- **Graph Minors XIII, (8.1) Algorithm** (page 93):
Given a society `(G, Ω)` encoded as the graph `G` and the cyclic order of `Ω̄`, `alg81Prog`
finds a cross in `(G, Ω)` if one exists (and otherwise reports `none`), in time `O(vε)`
(`alg81Size x = (|V(G)| + 1) * (|E(G)| + |V(G)| + 1)`), assuming `Shiloach80Statement`. -/
theorem gm13_algorithm_8_1 (hShiloach : Shiloach80Statement) :
    ∃ shiloachProg : Cmd,
      ComputesArrRelInTime alg81Size encAlg81In
        (fun x out => IsValidAlg81Output x (decAlg81Out x out))
        (alg81Prog shiloachProg) (fun s => s) := by
  rcases hShiloach with ⟨shiloachProg, C_sh, c_sh, hC_sh, hc_sh, hSh_spec⟩
  refine ⟨shiloachProg, 1200 + 10 * C_sh, 5 * c_sh + 4, by omega, by omega, fun x s₀ hs₀ => ?_⟩
  rcases alg81Prog_exec hC_sh hc_sh hSh_spec x le_rfl hs₀ with
    ⟨s', t, hex, ht, _, hres⟩
  refine ⟨s', t, hex, ht, ?_⟩
  rcases hres with ⟨cw, hcw_valid, hout⟩ | ⟨hout, hno⟩
  · rw [hout]
    exact decAlg81Out_valid_of_encode hcw_valid
  · rw [hout, decAlg81Out_eq_none_of_zero]
    exact ⟨hno, fun h => hno ((hasCrossInSociety_iff_hasCross x).mpr h)⟩

end GraphMinor.Compute
