module

public import GraphMinor.Compute.StackQueue
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.Graph.Basic

/-!
# Finite graph encodings on vertices `0, …, n - 1`

This file defines word RAM encodings for `SimpleGraph (Fin n)` and connects them to Mathlib's
multigraph type `Graph α β`:

* `GraphMinor.Compute.IsAdjMatrixList` and `GraphMinor.Compute.IsAdjMatrix`: flat `n × n`
  row-major adjacency matrix stored in an array `a_mat` of length `n * n`.
* `GraphMinor.Compute.IsAdjListFamily` and `GraphMinor.Compute.IsAdjList`: adjacency lists stored
  as a CSR/slice family `(a_start, a_end, a_entries)` using `IsListFamily`.
* `GraphMinor.Compute.adjListToMatProg` and `Triple.adjListToMatProg_spec`: builds the `n × n`
  adjacency matrix from adjacency lists in `O(n²)` steps.
* `GraphMinor.Compute.matToAdjListProg` and `Triple.matToAdjListProg_spec`: builds adjacency lists
  from the `n × n` adjacency matrix in `O(n²)` steps.
* `GraphMinor.Compute.underlyingSimpleGraph`, `GraphMinor.Compute.IsEdgeList`,
  `GraphMinor.Compute.edgeListToMatProg`, and `Triple.edgeListToMatProg_spec`: given a multigraph
  `H : Graph α β` with vertex numbering `φ : Fin n ≃ V(H)`, reads off the underlying simple graph
  `SimpleGraph (Fin n)` and builds its adjacency matrix from an edge-endpoint array pair in
  `O(n² + m)` steps.
-/

@[expose] public section

namespace GraphMinor.Compute

/-! ### Arithmetic helpers for row-major `n × n` indexing -/

/-- Row-major index bound: `u * n + v < n * n` whenever `u < n` and `v < n`. -/
theorem mul_add_lt_mul {n u v : ℕ} (hu : u < n) (hv : v < n) : u * n + v < n * n := by
  have h1 : (u + 1) * n ≤ n * n := Nat.mul_le_mul_right n hu
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

/-- Row-major index injectivity: if `v₁ < n` and `v₂ < n`, then `u₁ * n + v₁ = u₂ * n + v₂`
implies `u₁ = u₂` and `v₁ = v₂`. -/
theorem mul_add_inj {n u₁ v₁ u₂ v₂ : ℕ} (hv₁ : v₁ < n) (hv₂ : v₂ < n)
    (heq : u₁ * n + v₁ = u₂ * n + v₂) : u₁ = u₂ ∧ v₁ = v₂ := by
  have hu : u₁ = u₂ := by
    rcases Nat.lt_trichotomy u₁ u₂ with hlt | rfl | hgt
    · have h1 : (u₁ + 1) * n ≤ u₂ * n := Nat.mul_le_mul_right n hlt
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
    · rfl
    · have h1 : (u₂ + 1) * n ≤ u₁ * n := Nat.mul_le_mul_right n hgt
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega
  subst hu
  exact ⟨rfl, by omega⟩

@[simp]
theorem State.writeArr_arrs_length (s : State) (a a' : Arr) (i v : ℕ) :
    ((s.writeArr a i v).arrs a').length = (s.arrs a').length := by
  by_cases h : a' = a
  · subst h; simp
  · simp [h]

/-! ### Adjacency Matrix and Adjacency List Encodings -/

/-- A list `mat : List ℕ` of length `n * n` is the row-major adjacency matrix of
`G : SimpleGraph (Fin n)` if every entry is `0` or `1` and `mat[u * n + v] ≠ 0 ↔ G.Adj u v`. -/
def IsAdjMatrixList {n : ℕ} (G : SimpleGraph (Fin n)) (mat : List ℕ) : Prop :=
  ∃ (hlen : mat.length = n * n),
    ∀ u v : Fin n,
      (mat[u.1 * n + v.1]'(by rw [hlen]; exact mul_add_lt_mul u.2 v.2) ≠ 0 ↔ G.Adj u v) ∧
      mat[u.1 * n + v.1]'(by rw [hlen]; exact mul_add_lt_mul u.2 v.2) ≤ 1

/-- State predicate stating that array `a_mat` stores the `n × n` adjacency matrix of `G`. -/
def IsAdjMatrix {n : ℕ} (G : SimpleGraph (Fin n)) (a_mat : Arr) (s : State) : Prop :=
  IsAdjMatrixList G (s.arrs a_mat)

theorem IsAdjMatrix.of_arrs_eq {n : ℕ} {G : SimpleGraph (Fin n)} {a_mat : Arr} {s s' : State}
    (h : IsAdjMatrix G a_mat s) (heq : s'.arrs a_mat = s.arrs a_mat) :
    IsAdjMatrix G a_mat s' := by
  unfold IsAdjMatrix at *
  rwa [heq]

theorem IsListAt.of_arrs_eq {a_start a_end a_entries : Arr} {u st en : ℕ} {l : List ℕ}
    {s s' : State}
    (h : IsListAt a_start a_end a_entries u st en l s)
    (hs : s'.arrs a_start = s.arrs a_start)
    (he : s'.arrs a_end = s.arrs a_end)
    (hent : s'.arrs a_entries = s.arrs a_entries) :
    IsListAt a_start a_end a_entries u st en l s' := by
  rcases h with ⟨hu_st, hu_en, hen_ent, hdiff, hst, hen, hle, helem⟩
  exact ⟨by simpa [hs] using hu_st, by simpa [he] using hu_en,
    by simpa [hent] using hen_ent, hdiff,
    by simpa [hs] using hst, by simpa [he] using hen,
    hle, fun k hk => by simpa [hent] using helem k hk⟩

/-- A family of lists `lists : Fin n → List ℕ` is an adjacency-list representation of
`G : SimpleGraph (Fin n)` if each `lists u` contains distinct vertex indices `< n` and
`v.1 ∈ lists u ↔ G.Adj u v`. -/
def IsAdjListFamily {n : ℕ} (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ) : Prop :=
  ∀ u : Fin n,
    (∀ x ∈ lists u, x < n) ∧
    (lists u).Nodup ∧
    (lists u).length ≤ n ∧
    ∀ v : Fin n, v.1 ∈ lists u ↔ G.Adj u v

/-- State predicate stating that arrays `(a_start, a_end, a_entries)` store an adjacency-list
representation `lists` of `G : SimpleGraph (Fin n)`. -/
def IsAdjList {n : ℕ} (G : SimpleGraph (Fin n))
    (a_start a_end a_entries : Arr) (lists : Fin n → List ℕ) (s : State) : Prop :=
  IsListFamily n a_start a_end a_entries lists s ∧
  IsAdjListFamily G lists

theorem IsAdjList.of_arrs_eq {n : ℕ} {G : SimpleGraph (Fin n)}
    {a_start a_end a_entries : Arr} {lists : Fin n → List ℕ} {s s' : State}
    (h : IsAdjList G a_start a_end a_entries lists s)
    (hs : s'.arrs a_start = s.arrs a_start)
    (he : s'.arrs a_end = s.arrs a_end)
    (hent : s'.arrs a_entries = s.arrs a_entries) :
    IsAdjList G a_start a_end a_entries lists s' := by
  rcases h with ⟨⟨ha_s, ha_e, hfam⟩, hlists⟩
  refine ⟨⟨by simpa [hs] using ha_s, by simpa [he] using ha_e, fun u => ?_⟩, hlists⟩
  rcases hfam u with ⟨st, en, hlist⟩
  exact ⟨st, en, hlist.of_arrs_eq hs he hent⟩

/-! ### Building the Adjacency Matrix from Adjacency Lists (`adjListToMatProg`) -/

/-- Build the `n × n` adjacency matrix in `a_mat` from adjacency lists `(a_start, a_end, a_entries)`
using scratch registers `r_u, r_k, r_hi, r_v`. -/
def adjListToMatProg (n : ℕ) (a_start a_end a_entries a_mat : Arr)
    (r_u r_k r_hi r_v : Reg) : Cmd :=
  .seq (allocFillArr a_mat (.const (n * n)) (.const 0) r_u)
    (.seq (.assign r_u (.const 0))
      (forUp r_u (.const n)
        (forList a_start a_end a_entries r_u r_k r_hi r_v
          (.write a_mat
            (.op .add (.op .mul (.reg r_u) (.const n)) (.reg r_v))
            (.const 1)))))

/-- Partial invariant for `adjListToMatProg` after processing all vertices `< u` and the first `j`
neighbors of vertex `u`. -/
private def AdjMatPartial {n : ℕ} (G : SimpleGraph (Fin n))
    (a_mat : Arr) (u : ℕ) (curList : List ℕ) (s : State) : Prop :=
  ∃ (hlen : (s.arrs a_mat).length = n * n),
    ∀ (x y : Fin n),
      let val := (s.arrs a_mat)[x.1 * n + y.1]'(by rw [hlen]; exact mul_add_lt_mul x.2 y.2)
      val ≤ 1 ∧
      (val ≠ 0 ↔
        (x.1 < u ∧ G.Adj x y) ∨
        (x.1 = u ∧ y.1 ∈ curList))

/-- Specification for `adjListToMatProg`: builds the `n × n` adjacency matrix `a_mat` from
adjacency lists `(a_start, a_end, a_entries)` in at most `30 * (n * n) + 16 * n + 12` steps. -/
theorem Triple.adjListToMatProg_spec {w n : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (a_start a_end a_entries a_mat : ℕ)
    (r_u r_k r_hi r_v : ℕ)
    (hne_sm : a_start ≠ a_mat) (hne_em : a_end ≠ a_mat) (hne_entm : a_entries ≠ a_mat)
    (hne_uk : r_u ≠ r_k) (hne_uh : r_u ≠ r_hi) (hne_uv : r_u ≠ r_v)
    (hne_kh : r_k ≠ r_hi) (hne_kv : r_k ≠ r_v) (hne_hv : r_hi ≠ r_v)
    (hw : 1 < 2 ^ w) (hnn_w : n * n < 2 ^ w)
    (hent_w : ∀ s, IsAdjList G a_start a_end a_entries lists s →
      (s.arrs a_entries).length < 2 ^ w) :
    ⦃IsAdjList G a_start a_end a_entries lists⦄[w]
      adjListToMatProg n a_start a_end a_entries a_mat r_u r_k r_hi r_v
    ⦃fun s' => IsAdjList G a_start a_end a_entries lists s' ∧ IsAdjMatrix G a_mat s'⦄ ≤
      fun _ => 30 * (n * n) + 16 * n + 12 := by
  have hn_le_nn : n ≤ n * n := Nat.le_mul_self n
  have hn_w : n < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hne_sm' : (a_start : Arr) ≠ a_mat := by omega
  have hne_em' : (a_end : Arr) ≠ a_mat := by omega
  have hne_entm' : (a_entries : Arr) ≠ a_mat := by omega
  have hne_uk' : (r_u : Reg) ≠ r_k := by omega
  have hne_uh' : (r_u : Reg) ≠ r_hi := by omega
  have hne_uv' : (r_u : Reg) ≠ r_v := by omega
  have hne_kh' : (r_k : Reg) ≠ r_hi := by omega
  have hne_kv' : (r_k : Reg) ≠ r_v := by omega
  have hne_hv' : (r_hi : Reg) ≠ r_v := by omega
  intro s₀ hs₀
  have hent_len_w : (s₀.arrs a_entries).length < 2 ^ w := hent_w s₀ hs₀
  -- Step 1: allocFillArr a_mat (.const (n * n)) (.const 0) r_u
  rcases Triple.allocFillArr_const a_mat (n * n) 0 r_u hw hnn_w h0_w s₀ trivial with
    ⟨s₁, t₁, hex₁, ht₁, harr₁⟩
  dsimp only at ht₁
  have hlen₁ : (s₁.arrs a_mat).length = n * n := by simp [harr₁]
  have hadj₁ : IsAdjList G a_start a_end a_entries lists s₁ := by
    have hnot_s : (a_start : Arr) ∉ (allocFillArr a_mat (.const (n * n)) (.const 0) r_u).writtenArrs := by
      simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs, hne_sm']
    have hnot_e : (a_end : Arr) ∉ (allocFillArr a_mat (.const (n * n)) (.const 0) r_u).writtenArrs := by
      simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs, hne_em']
    have hnot_ent : (a_entries : Arr) ∉ (allocFillArr a_mat (.const (n * n)) (.const 0) r_u).writtenArrs := by
      simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs, hne_entm']
    exact hs₀.of_arrs_eq
      (Exec.arrs_eq_of_not_mem_writtenArrs hex₁ hnot_s)
      (Exec.arrs_eq_of_not_mem_writtenArrs hex₁ hnot_e)
      (Exec.arrs_eq_of_not_mem_writtenArrs hex₁ hnot_ent)
  -- Step 2: .assign r_u (.const 0)
  have heval0 : (Expr.const 0).eval w s₁ = some 0 := by simp [checkWord, h0_w]
  let s₂ := s₁.setReg r_u 0
  have hex₂ : Exec w (.assign r_u (.const 0)) s₁ s₂ 2 := .assign heval0
  -- Outer loop invariant
  let OuterInv (u : ℕ) (s : State) : Prop :=
    IsAdjList G a_start a_end a_entries lists s ∧
    (s.arrs a_entries).length < 2 ^ w ∧
    s.regs r_u = u ∧
    AdjMatPartial G a_mat u [] s
  have hOuter₀ : OuterInv 0 s₂ := by
    refine ⟨hadj₁.of_arrs_eq rfl rfl rfl, by simpa [s₂] using hent_w s₁ hadj₁, by simp [s₂], ⟨hlen₁, ?_⟩⟩
    intro x y
    simp [s₂, harr₁]
  -- Outer loop verification via Triple.forUp_const
  have hOuterLoop :
      ⦃OuterInv 0⦄[w]
        forUp r_u (.const n)
          (forList a_start a_end a_entries r_u r_k r_hi r_v
            (.write a_mat
              (.op .add (.op .mul (.reg r_u) (.const n)) (.reg r_v))
              (.const 1)))
      ⦃OuterInv n⦄ ≤ fun _ => 3 + n * (7 + (9 + 17 * n)) := by
    apply Triple.forUp_const OuterInv n (9 + 17 * n) hw hn_w
    · intro u _ s ⟨_, _, hru, _⟩
      exact ⟨hru, by simp [Expr.eval, checkWord, hn_w]⟩
    · intro u hu
      let uFin : Fin n := ⟨u, hu⟩
      have hu_w : u < 2 ^ w := by omega
      intro s_u ⟨hadj_u, hent_u_w, hru_u, hpart_u⟩
      obtain ⟨st, en, hlist_u⟩ := hadj_u.1.2.2 uFin
      have hlist_props := hadj_u.2 uFin
      rcases hlist_props with ⟨hmem_lt, hnodup, hlen_le_n, hadj_iff⟩
      have hen_w : en < 2 ^ w := by
        rcases hlist_u with ⟨_, _, hen_ent, _, _, _, _, _⟩
        omega
      -- Inner loop invariant for `forList`
      let InnerInv (j : ℕ) (s : State) : Prop :=
        IsAdjList G a_start a_end a_entries lists s ∧
        (s.arrs a_entries).length < 2 ^ w ∧
        s.regs r_u = u ∧
        IsListAt a_start a_end a_entries u st en (lists uFin) s ∧
        AdjMatPartial G a_mat u ((lists uFin).take j) s
      have hforList :
          ⦃InnerInv 0⦄[w]
            forList a_start a_end a_entries r_u r_k r_hi r_v
              (.write a_mat
                (.op .add (.op .mul (.reg r_u) (.const n)) (.reg r_v))
                (.const 1))
          ⦃InnerInv (lists uFin).length⦄ ≤
            fun _ => 9 + (lists uFin).length * (10 + 7) := by
        apply Triple.forList_const a_start a_end a_entries r_u r_k r_hi r_v
          u st en (lists uFin) InnerInv 7 _ hne_kh hne_uk hw hu_w hen_w
        · intro x hx
          have := hmem_lt x hx
          omega
        · intro s ⟨hadj, hent_w', hru, hlist, hpart⟩
          refine ⟨hlist, hru, hadj, hent_w', ?_, hlist, hpart⟩
          simp [hne_uk', hne_uh', hru]
        · intro j _ s ⟨_, _, _, hlist, _⟩
          exact hlist
        · intro j hj s_v ⟨s, ⟨hadj, hent_w', hru, hlist, ⟨hlen_m, hpart⟩⟩, hs_v, hrk, hrhi⟩
          subst hs_v
          let v := (lists uFin)[j]
          have hv_lt_n : v < n := hmem_lt v (List.getElem_mem hj)
          have hv_w : v < 2 ^ w := by omega
          have hun_w : u * n < 2 ^ w := by
            have : u * n < n * n := by
              have := mul_add_lt_mul hu hv_lt_n
              omega
            omega
          have hidx_lt : u * n + v < n * n := mul_add_lt_mul hu hv_lt_n
          have hidx_w : u * n + v < 2 ^ w := by omega
          have heval_idx :
              (Expr.op .add (.op .mul (.reg r_u) (.const n)) (.reg r_v)).eval w
                (s.setReg r_v v) = some (u * n + v) := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hne_uv', hru, hu_w,
              hn_w, hun_w, hv_w, hidx_w]
          have heval_one : (Expr.const 1).eval w (s.setReg r_v v) = some 1 := by
            simp [Expr.eval, checkWord, hw]
          let s' := (s.setReg r_v v).writeArr a_mat (u * n + v) 1
          have hex_w : Exec w
              (.write a_mat
                (.op .add (.op .mul (.reg r_u) (.const n)) (.reg r_v))
                (.const 1))
              (s.setReg r_v v) s' 7 :=
            .write heval_idx heval_one (by simp [hlen_m, hidx_lt])
          refine ⟨s', 7, hex_w, le_rfl, ?_, by simp [s', hne_kv', hrk], by simp [s', hne_hv', hrhi]⟩
          -- Prove InnerInv (j + 1) (s'.setReg r_k (st + (j + 1)))
          have hadj' : IsAdjList G a_start a_end a_entries lists (s'.setReg r_k (st + (j + 1))) :=
            hadj.of_arrs_eq (by simp [s', hne_sm']) (by simp [s', hne_em']) (by simp [s', hne_entm'])
          have hlist' : IsListAt a_start a_end a_entries u st en (lists uFin)
              (s'.setReg r_k (st + (j + 1))) :=
            hlist.of_arrs_eq (by simp [s', hne_sm']) (by simp [s', hne_em']) (by simp [s', hne_entm'])
          refine ⟨hadj', by simpa [s', hne_entm'] using hent_w',
            by simp [s', hne_uk', hne_uv', hru], hlist', ?_⟩
          refine ⟨by simp [s', hlen_m], fun x y => ?_⟩
          simp only [s', State.setReg_arrs, State.writeArr_arrs_self]
          by_cases hxy : x.1 * n + y.1 = u * n + v
          · have ⟨hx_eq, hy_eq⟩ := mul_add_inj y.2 hv_lt_n hxy
            have hset_self : ((s.arrs a_mat).set (u * n + v) 1)[x.1 * n + y.1]'(by
                rw [List.length_set, hlen_m]; exact mul_add_lt_mul x.2 y.2) = 1 := by
              simp only [hxy]
              exact List.getElem_set_self (by simp [hlen_m, hidx_lt])
            rw [hset_self]
            refine ⟨le_rfl, ?_⟩
            simp only [ne_eq, one_ne_zero, not_false_eq_true, true_iff]
            right
            refine ⟨hx_eq, ?_⟩
            rw [List.take_add_one, List.mem_append]
            right
            simp [List.getElem?_eq_getElem hj, hy_eq, v]
          · rw [List.getElem_set_ne (Ne.symm hxy)]
            obtain ⟨hle_xy, hiff_xy⟩ := hpart x y
            refine ⟨hle_xy, hiff_xy.trans ?_⟩
            rw [List.take_add_one]
            simp only [List.getElem?_eq_getElem hj, Option.toList_some,
              List.mem_append, List.mem_singleton]
            constructor
            · rintro (h1 | ⟨hx_eq, hy_mem⟩)
              · exact Or.inl h1
              · exact Or.inr ⟨hx_eq, Or.inl hy_mem⟩
            · rintro (h1 | ⟨hx_eq, hy_mem | hy_eq⟩)
              · exact Or.inl h1
              · exact Or.inr ⟨hx_eq, hy_mem⟩
              · exfalso
                exact hxy (by rw [hx_eq, hy_eq])
      rcases hforList s_u ⟨hadj_u, hent_u_w, hru_u, hlist_u, by simpa using hpart_u⟩ with
        ⟨s_end, t_u, hex_u, ht_u, hadj_end, hent_end_w, hru_end, _, hpart_end⟩
      dsimp only at ht_u
      have ht_u_bound : t_u ≤ 9 + 17 * n := by
        have : (lists uFin).length * 17 ≤ n * 17 := Nat.mul_le_mul_right 17 hlen_le_n
        omega
      refine ⟨s_end, t_u, hex_u, ht_u_bound, ?_, hru_end⟩
      -- Show OuterInv (u + 1) (s_end.setReg r_u (u + 1))
      refine ⟨hadj_end.of_arrs_eq rfl rfl rfl, hent_end_w, by simp, ?_⟩
      rcases hpart_end with ⟨hlen_end, hxy_end⟩
      rw [List.take_length] at hxy_end
      refine ⟨hlen_end, fun x y => ?_⟩
      obtain ⟨hle_xy, hiff_xy⟩ := hxy_end x y
      refine ⟨hle_xy, hiff_xy.trans ?_⟩
      constructor
      · rintro (⟨hx_lt, hadj_xy⟩ | ⟨hx_eq, hy_mem⟩)
        · exact Or.inl ⟨by omega, hadj_xy⟩
        · left
          refine ⟨by omega, ?_⟩
          have hx_fin : x = uFin := Fin.ext hx_eq
          rw [hx_fin]
          exact (hadj_iff y).mp hy_mem
      · rintro (⟨hx_lt, hadj_xy⟩ | ⟨_, hy_mem⟩)
        · by_cases hx_eq : x.1 = u
          · right
            refine ⟨hx_eq, ?_⟩
            have hx_fin : x = uFin := Fin.ext hx_eq
            rw [hx_fin] at hadj_xy
            exact (hadj_iff y).mpr hadj_xy
          · exact Or.inl ⟨by omega, hadj_xy⟩
        · nomatch hy_mem
  rcases hOuterLoop s₂ hOuter₀ with ⟨s₃, t₃, hex₃, ht₃, hadj₃, _, _, hlen₃, hpart₃⟩
  dsimp only at ht₃
  refine ⟨s₃, t₁ + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), ?_, hadj₃, hlen₃, ?_⟩
  · dsimp only
    have hmul : n * (7 + (9 + 17 * n)) = n * 16 + n * (17 * n) := by
      have h79 : 7 + (9 + 17 * n) = 16 + 17 * n := by omega
      rw [h79, Nat.mul_add]
    have hmul2 : n * (17 * n) = 17 * (n * n) := Nat.mul_left_comm n 17 n
    omega
  · intro x y
    obtain ⟨hle_xy, hiff_xy⟩ := hpart₃ x y
    refine ⟨hiff_xy.trans ?_, hle_xy⟩
    have hx_lt : x.1 < n := x.2
    have hx_ne : x.1 ≠ n := by omega
    simp [hx_lt, hx_ne]

/-! ### Building Adjacency Lists from the Adjacency Matrix (`matToAdjListProg`) -/

/-- The list of neighbors `< k` of vertex `u` in `G : SimpleGraph (Fin n)`, in increasing order. -/
noncomputable def adjListUpTo {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) : ℕ → List ℕ
  | 0 => []
  | v + 1 =>
    if hv : v < n then
      haveI := Classical.propDecidable (G.Adj u ⟨v, hv⟩)
      if G.Adj u ⟨v, hv⟩ then adjListUpTo G u v ++ [v] else adjListUpTo G u v
    else
      adjListUpTo G u v

/-- The full list of neighbors of vertex `u` in `G : SimpleGraph (Fin n)`, in increasing order. -/
noncomputable def adjListOf {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) : List ℕ :=
  adjListUpTo G u n

theorem adjListUpTo_succ_pos {n : ℕ} {G : SimpleGraph (Fin n)} {u : Fin n} {v : ℕ}
    (hv : v < n) (h : G.Adj u ⟨v, hv⟩) :
    adjListUpTo G u (v + 1) = adjListUpTo G u v ++ [v] := by
  dsimp [adjListUpTo]
  simp only [hv, ↓reduceDIte]
  split_ifs with h'
  · rfl
  · exact absurd h h'

theorem adjListUpTo_succ_neg {n : ℕ} {G : SimpleGraph (Fin n)} {u : Fin n} {v : ℕ}
    (hv : v < n) (h : ¬ G.Adj u ⟨v, hv⟩) :
    adjListUpTo G u (v + 1) = adjListUpTo G u v := by
  dsimp [adjListUpTo]
  simp only [hv, ↓reduceDIte]
  split_ifs with h'
  · exact absurd h' h
  · rfl

theorem adjListUpTo_length_le {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    ∀ k, (adjListUpTo G u k).length ≤ k
  | 0 => le_rfl
  | v + 1 => by
    have ih := adjListUpTo_length_le G u v
    dsimp [adjListUpTo]
    split_ifs <;> simp <;> omega

theorem mem_adjListUpTo_iff {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    ∀ {k : ℕ} (hk : k ≤ n) (x : ℕ),
      x ∈ adjListUpTo G u k ↔ ∃ (hx : x < k), G.Adj u ⟨x, Nat.lt_of_lt_of_le hx hk⟩
  | 0, _, x => by simp [adjListUpTo]
  | v + 1, hk, x => by
    have hv : v < n := by omega
    have ih := @mem_adjListUpTo_iff n G u v (by omega) x
    dsimp [adjListUpTo]
    simp only [hv, ↓reduceDIte]
    split_ifs with hadj
    · simp only [List.mem_append, List.mem_singleton, ih]
      constructor
      · rintro (⟨hx, hadj_x⟩ | rfl)
        · exact ⟨by omega, hadj_x⟩
        · exact ⟨by omega, hadj⟩
      · rintro ⟨hx, hadj_x⟩
        by_cases hxv : x = v
        · exact Or.inr hxv
        · exact Or.inl ⟨by omega, hadj_x⟩
    · rw [ih]
      constructor
      · rintro ⟨hx, hadj_x⟩
        exact ⟨by omega, hadj_x⟩
      · rintro ⟨hx, hadj_x⟩
        have hxv : x ≠ v := by
          rintro rfl
          exact hadj hadj_x
        exact ⟨by omega, hadj_x⟩

theorem adjListUpTo_nodup {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    ∀ k (_hk : k ≤ n), (adjListUpTo G u k).Nodup
  | 0, _ => List.nodup_nil
  | v + 1, hk => by
    have hv : v < n := by omega
    have ih := adjListUpTo_nodup G u v (by omega)
    dsimp [adjListUpTo]
    simp only [hv, ↓reduceDIte]
    split_ifs with hadj
    · rw [List.nodup_append]
      refine ⟨ih, List.nodup_singleton v, ?_⟩
      intro x hx y hy hxy
      rw [List.mem_singleton] at hy
      subst hy; subst hxy
      rw [mem_adjListUpTo_iff G u (by omega)] at hx
      rcases hx with ⟨hxv, _⟩
      exact Nat.lt_irrefl x hxv
    · exact ih

/-- `adjListOf G` satisfies `IsAdjListFamily G (adjListOf G)`. -/
theorem isAdjListFamily_adjListOf {n : ℕ} (G : SimpleGraph (Fin n)) :
    IsAdjListFamily G (adjListOf G) := by
  intro u
  refine ⟨?_, adjListUpTo_nodup G u n le_rfl, adjListUpTo_length_le G u n, ?_⟩
  · intro x hx
    rw [adjListOf, mem_adjListUpTo_iff G u le_rfl] at hx
    exact hx.1
  · intro v
    rw [adjListOf, mem_adjListUpTo_iff G u le_rfl]
    exact ⟨fun ⟨_, hadj⟩ => hadj, fun hadj => ⟨v.2, hadj⟩⟩

/-- Build adjacency lists `(a_start, a_end, a_entries)` from the `n × n` adjacency matrix `a_mat`
using scratch registers `r_u, r_v, r_cnt, r_val`. -/
def matToAdjListProg (n : ℕ) (a_mat a_start a_end a_entries : Arr)
    (r_u r_v r_cnt r_val : Reg) : Cmd :=
  .seq (.alloc a_start (.const n))
    (.seq (.alloc a_end (.const n))
      (.seq (.alloc a_entries (.const (n * n)))
        (.seq (.assign r_u (.const 0))
          (forUp r_u (.const n)
            (.seq (.assign r_cnt (.op .mul (.reg r_u) (.const n)))
              (.seq (.write a_start (.reg r_u) (.reg r_cnt))
                (.seq (.write a_end (.reg r_u) (.reg r_cnt))
                  (.seq (.assign r_v (.const 0))
                    (forUp r_v (.const n)
                      (.seq (.assign r_val
                          (.read a_mat (.op .add (.op .mul (.reg r_u) (.const n)) (.reg r_v))))
                        (.ite (.reg r_val)
                          (listAppend a_end a_entries r_u r_cnt (.reg r_v))
                          .skip)))))))))))

/-- Preserving `IsListAt` at an earlier vertex `u' < u` when `matToAdjListProg` modifies `a_end[u]`
and `a_entries[cnt]` with `u * n ≤ cnt`. -/
private lemma isListAt_preserve_prev {n : ℕ} {a_start a_end a_entries : ℕ}
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

/-- Specification for `matToAdjListProg`: builds the adjacency lists `(a_start, a_end, a_entries)`
of `G` from its `n × n` adjacency matrix `a_mat` in at most `26 * (n * n) + 24 * n + 10` steps. -/
theorem Triple.matToAdjListProg_spec {w n : ℕ} (G : SimpleGraph (Fin n))
    (a_mat a_start a_end a_entries : ℕ)
    (r_u r_v r_cnt r_val : ℕ)
    (hne_ms : a_mat ≠ a_start) (hne_me : a_mat ≠ a_end) (hne_ment : a_mat ≠ a_entries)
    (hne_se : a_start ≠ a_end) (hne_sent : a_start ≠ a_entries) (hne_eent : a_end ≠ a_entries)
    (hne_uv : r_u ≠ r_v) (hne_uc : r_u ≠ r_cnt) (hne_uval : r_u ≠ r_val)
    (hne_vc : r_v ≠ r_cnt) (hne_vval : r_v ≠ r_val) (hne_cval : r_cnt ≠ r_val)
    (hw : 1 < 2 ^ w) (hnn_w : n * n < 2 ^ w) :
    ⦃IsAdjMatrix G a_mat⦄[w]
      matToAdjListProg n a_mat a_start a_end a_entries r_u r_v r_cnt r_val
    ⦃fun s' => IsAdjMatrix G a_mat s' ∧
      IsAdjList G a_start a_end a_entries (adjListOf G) s' ∧
      (s'.arrs a_entries).length = n * n⦄ ≤
      fun _ => 26 * (n * n) + 24 * n + 10 := by
  have hn_le_nn : n ≤ n * n := Nat.le_mul_self n
  have hn_w : n < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hne_ms' : (a_mat : Arr) ≠ a_start := by omega
  have hne_me' : (a_mat : Arr) ≠ a_end := by omega
  have hne_ment' : (a_mat : Arr) ≠ a_entries := by omega
  have hne_se' : (a_start : Arr) ≠ a_end := by omega
  have hne_sent' : (a_start : Arr) ≠ a_entries := by omega
  have hne_eent' : (a_end : Arr) ≠ a_entries := by omega
  have hne_uv' : (r_u : Reg) ≠ r_v := by omega
  have hne_uc' : (r_u : Reg) ≠ r_cnt := by omega
  have hne_uval' : (r_u : Reg) ≠ r_val := by omega
  have hne_vc' : (r_v : Reg) ≠ r_cnt := by omega
  have hne_vval' : (r_v : Reg) ≠ r_val := by omega
  have hne_cval' : (r_cnt : Reg) ≠ r_val := by omega
  intro s₀ hs₀
  -- Allocations of a_start, a_end, a_entries and r_u := 0
  have hn_eval₀ : (Expr.const n).eval w s₀ = some n := by simp [checkWord, hn_w]
  let s₁ := s₀.setArr a_start (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_start (.const n)) s₀ s₁ (1 + n) := .alloc hn_eval₀
  have hn_eval₁ : (Expr.const n).eval w s₁ = some n := by simp [checkWord, hn_w]
  let s₂ := s₁.setArr a_end (List.replicate n 0)
  have hex₂ : Exec w (.alloc a_end (.const n)) s₁ s₂ (1 + n) := .alloc hn_eval₁
  have hnn_eval₂ : (Expr.const (n * n)).eval w s₂ = some (n * n) := by simp [checkWord, hnn_w]
  let s₃ := s₂.setArr a_entries (List.replicate (n * n) 0)
  have hex₃ : Exec w (.alloc a_entries (.const (n * n))) s₂ s₃ (1 + n * n) := .alloc hnn_eval₂
  have h0_eval₃ : (Expr.const 0).eval w s₃ = some 0 := by simp [checkWord, h0_w]
  let s₄ := s₃.setReg r_u 0
  have hex₄ : Exec w (.assign r_u (.const 0)) s₃ s₄ 2 := .assign h0_eval₃
  -- Outer loop invariant
  let OuterInv (u : ℕ) (s : State) : Prop :=
    IsAdjMatrix G a_mat s ∧
    (s.arrs a_start).length = n ∧
    (s.arrs a_end).length = n ∧
    (s.arrs a_entries).length = n * n ∧
    s.regs r_u = u ∧
    ∀ (u' : Fin n), u'.1 < u →
      IsListAt a_start a_end a_entries u'.1 (u'.1 * n)
        (u'.1 * n + (adjListOf G u').length) (adjListOf G u') s
  have hOuter₀ : OuterInv 0 s₄ := by
    refine ⟨hs₀.of_arrs_eq (by simp [s₄, s₃, s₂, s₁, hne_ms', hne_me', hne_ment']),
      by simp [s₄, s₃, s₂, s₁, hne_se', hne_sent'],
      by simp [s₄, s₃, s₂, hne_eent'],
      by simp [s₄, s₃],
      by simp [s₄],
      fun u' hu' => by omega⟩
  have hOuterLoop :
      ⦃OuterInv 0⦄[w]
        forUp r_u (.const n)
          (.seq (.assign r_cnt (.op .mul (.reg r_u) (.const n)))
            (.seq (.write a_start (.reg r_u) (.reg r_cnt))
              (.seq (.write a_end (.reg r_u) (.reg r_cnt))
                (.seq (.assign r_v (.const 0))
                  (forUp r_v (.const n)
                    (.seq (.assign r_val
                        (.read a_mat (.op .add (.op .mul (.reg r_u) (.const n)) (.reg r_v))))
                      (.ite (.reg r_val)
                        (listAppend a_end a_entries r_u r_cnt (.reg r_v))
                        .skip)))))))
      ⦃OuterInv n⦄ ≤ fun _ => 3 + n * (7 + (15 + 25 * n)) := by
    apply Triple.forUp_const OuterInv n (15 + 25 * n) hw hn_w
    · intro u _ s ⟨_, _, _, _, hru, _⟩
      exact ⟨hru, by simp [Expr.eval, checkWord, hn_w]⟩
    · intro u hu s_u ⟨hmat_u, hlen_s_u, hlen_e_u, hlen_ent_u, hru_u, hprev_u⟩
      let uFin : Fin n := ⟨u, hu⟩
      have hu_w : u < 2 ^ w := by omega
      have hun_le_nn : u * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
      have hun_w : u * n < 2 ^ w := by omega
      -- 1. r_cnt := r_u * n (cost 4)
      have hmul_eval : (Expr.op .mul (.reg r_u) (.const n)).eval w s_u = some (u * n) := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru_u, hu_w, hn_w, hun_w]
      let sa₁ := s_u.setReg r_cnt (u * n)
      have hexa₁ : Exec w (.assign r_cnt (.op .mul (.reg r_u) (.const n))) s_u sa₁ 4 :=
        .assign hmul_eval
      -- 2. a_start[r_u] := r_cnt (cost 3)
      have hru_sa₁ : (Expr.reg r_u).eval w sa₁ = some u := by
        simp [sa₁, Expr.eval, checkWord, hne_uc', hru_u, hu_w]
      have hrcnt_sa₁ : (Expr.reg r_cnt).eval w sa₁ = some (u * n) := by
        simp [sa₁, Expr.eval, checkWord, hun_w]
      let sa₂ := sa₁.writeArr a_start u (u * n)
      have hexa₂ : Exec w (.write a_start (.reg r_u) (.reg r_cnt)) sa₁ sa₂ 3 :=
        .write hru_sa₁ hrcnt_sa₁ (by simp [sa₁, hlen_s_u, hu])
      -- 3. a_end[r_u] := r_cnt (cost 3)
      have hru_sa₂ : (Expr.reg r_u).eval w sa₂ = some u := by
        simp [sa₂, sa₁, Expr.eval, checkWord, hne_uc', hru_u, hu_w]
      have hrcnt_sa₂ : (Expr.reg r_cnt).eval w sa₂ = some (u * n) := by
        simp [sa₂, sa₁, Expr.eval, checkWord, hun_w]
      let sa₃ := sa₂.writeArr a_end u (u * n)
      have hexa₃ : Exec w (.write a_end (.reg r_u) (.reg r_cnt)) sa₂ sa₃ 3 :=
        .write hru_sa₂ hrcnt_sa₂ (by simp [sa₂, sa₁, hlen_e_u, hu])
      -- 4. r_v := 0 (cost 2)
      have h0_sa₃ : (Expr.const 0).eval w sa₃ = some 0 := by simp [checkWord, h0_w]
      let sa₄ := sa₃.setReg r_v 0
      have hexa₄ : Exec w (.assign r_v (.const 0)) sa₃ sa₄ 2 := .assign h0_sa₃
      -- Inner loop invariant over v ≤ n
      let InnerInv (v : ℕ) (s : State) : Prop :=
        IsAdjMatrix G a_mat s ∧
        (s.arrs a_start).length = n ∧
        (s.arrs a_end).length = n ∧
        (s.arrs a_entries).length = n * n ∧
        s.regs r_u = u ∧
        s.regs r_v = v ∧
        s.regs r_cnt = u * n + (adjListUpTo G uFin v).length ∧
        IsListAt a_start a_end a_entries u (u * n)
          (u * n + (adjListUpTo G uFin v).length) (adjListUpTo G uFin v) s ∧
        ∀ (u' : Fin n), u'.1 < u →
          IsListAt a_start a_end a_entries u'.1 (u'.1 * n)
            (u'.1 * n + (adjListOf G u').length) (adjListOf G u') s
      have hInner₀ : InnerInv 0 sa₄ := by
        refine ⟨hmat_u.of_arrs_eq (by simp [sa₄, sa₃, sa₂, sa₁, hne_ms', hne_me']),
          by simp [sa₄, sa₃, sa₂, sa₁, hlen_s_u],
          by simp [sa₄, sa₃, sa₂, sa₁, hlen_e_u],
          by simp [sa₄, sa₃, sa₂, sa₁, hlen_ent_u],
          by simp [sa₄, sa₃, sa₂, sa₁, hne_uv', hne_uc', hru_u],
          by simp [sa₄],
          by simp [sa₄, sa₃, sa₂, sa₁, hne_vc'.symm, adjListUpTo],
          ?_, ?_⟩
        · refine ⟨by simp [sa₄, sa₃, sa₂, sa₁, hlen_s_u, hu],
            by simp [sa₄, sa₃, sa₂, sa₁, hlen_e_u, hu],
            by simp [sa₄, sa₃, sa₂, sa₁, hlen_ent_u, adjListUpTo, hun_le_nn],
            by simp [adjListUpTo],
            ?_, ?_, by simp [adjListUpTo], fun k hk => by simp [adjListUpTo] at hk⟩
          · simp only [sa₄, sa₃, sa₂, sa₁, State.setReg_arrs,
              State.writeArr_arrs_ne _ _ _ hne_se', State.writeArr_arrs_self]
            exact List.getElem_set_self (by simp [hlen_s_u, hu])
          · simp only [sa₄, sa₃, sa₂, sa₁, State.setReg_arrs, State.writeArr_arrs_self]
            exact List.getElem_set_self (by simp [hlen_e_u, hu])
        · intro u' hu'
          rcases hprev_u u' hu' with ⟨hu'_st, hu'_en, hen_ent, hdiff, hst, hen, hle, helem⟩
          refine ⟨by simpa [sa₄, sa₃, sa₂, sa₁] using hu'_st,
            by simpa [sa₄, sa₃, sa₂, sa₁] using hu'_en,
            by simpa [sa₄, sa₃, sa₂, sa₁] using hen_ent,
            hdiff, ?_, ?_, hle,
            fun k hk => by simpa [sa₄, sa₃, sa₂, sa₁, hne_sent'.symm, hne_eent'.symm] using helem k hk⟩
          · simp only [sa₄, sa₃, sa₂, sa₁, State.setReg_arrs,
              State.writeArr_arrs_ne _ _ _ hne_se', State.writeArr_arrs_self]
            rw [List.getElem_set_ne (by omega)]
            exact hst
          · simp only [sa₄, sa₃, sa₂, sa₁, State.setReg_arrs, State.writeArr_arrs_self,
              State.writeArr_arrs_ne _ _ _ hne_se'.symm]
            rw [List.getElem_set_ne (by omega)]
            exact hen
      -- Inner loop verification via Triple.forUp_const
      have hInnerLoop :
          ⦃InnerInv 0⦄[w]
            forUp r_v (.const n)
              (.seq (.assign r_val
                  (.read a_mat (.op .add (.op .mul (.reg r_u) (.const n)) (.reg r_v))))
                (.ite (.reg r_val)
                  (listAppend a_end a_entries r_u r_cnt (.reg r_v))
                  .skip))
          ⦃InnerInv n⦄ ≤ fun _ => 3 + n * (7 + 18) := by
        apply Triple.forUp_const InnerInv n 18 hw hn_w
        · intro v _ s ⟨_, _, _, _, _, hrv, _, _, _⟩
          exact ⟨hrv, by simp [Expr.eval, checkWord, hn_w]⟩
        · intro v hv s_v ⟨hmat_v, hlen_s_v, hlen_e_v, hlen_ent_v, hru_v, hrv_v, hrcnt_v, hlist_v, hprev_v⟩
          let vFin : Fin n := ⟨v, hv⟩
          have hv_w : v < 2 ^ w := by omega
          have hidx_lt : u * n + v < n * n := mul_add_lt_mul hu hv
          have hidx_w : u * n + v < 2 ^ w := by omega
          rcases hmat_v with ⟨hlen_mat, hmat_entries⟩
          obtain ⟨hmat_iff, hmat_le1⟩ := hmat_entries uFin vFin
          let mval := (s_v.arrs a_mat)[u * n + v]'(by rw [hlen_mat]; exact hidx_lt)
          have hmval_le1 : mval ≤ 1 := hmat_le1
          have hmval_w : mval < 2 ^ w := by omega
          have hread_mat :
              (Expr.read a_mat (.op .add (.op .mul (.reg r_u) (.const n)) (.reg r_v))).eval w s_v =
                some mval := by
            have hidx_a : u * n + v < (s_v.arrs a_mat).length := by rw [hlen_mat]; exact hidx_lt
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru_v, hu_w, hn_w, hun_w,
              hrv_v, hv_w, hidx_w, hidx_a, mval, hmval_w]
          let sb₁ := s_v.setReg r_val mval
          have hexb₁ : Exec w
              (.assign r_val (.read a_mat (.op .add (.op .mul (.reg r_u) (.const n)) (.reg r_v))))
              s_v sb₁ 7 := .assign hread_mat
          have hcond_sb₁ : (Expr.reg r_val).eval w sb₁ = some mval := by
            simp [sb₁, Expr.eval, checkWord, hmval_w]
          have hlen_cur_le : (adjListUpTo G uFin v).length ≤ v := adjListUpTo_length_le G uFin v
          have hcnt_lt_nn : u * n + (adjListUpTo G uFin v).length < n * n := by
            have := mul_add_lt_mul hu hv
            omega
          have hcnt1_w : u * n + (adjListUpTo G uFin v).length + 1 < 2 ^ w := by omega
          by_cases hadj_uv : G.Adj uFin vFin
          · have hmval_ne : mval ≠ 0 := hmat_iff.mpr hadj_uv
            have hlist_sb₁ : IsListAt a_start a_end a_entries u (u * n)
                (u * n + (adjListUpTo G uFin v).length) (adjListUpTo G uFin v) sb₁ := hlist_v
            rcases Triple.listAppend_spec a_start a_end a_entries r_u r_cnt (.reg r_v)
                u (u * n) (adjListUpTo G uFin v) v hne_se hne_sent hne_eent hne_uc
                hw hu_w hcnt1_w sb₁
                ⟨hlist_sb₁,
                  by simp [sb₁, hne_uval', hru_v],
                  by simp [sb₁, hne_cval', hrcnt_v],
                  by simp [sb₁, hlen_ent_v, hcnt_lt_nn],
                  by simp [sb₁, Expr.eval, checkWord, hne_vval', hrv_v, hv_w]⟩ with
              ⟨sb₂, t_app, hex_app, ht_app, hlist_sb₂, hru_sb₂, hrcnt_sb₂⟩
            dsimp [Expr.cost] at ht_app
            have hex_ite : Exec w
                (.ite (.reg r_val) (listAppend a_end a_entries r_u r_cnt (.reg r_v)) .skip)
                sb₁ sb₂ (1 + t_app) := .ite_true hcond_sb₁ hmval_ne hex_app
            refine ⟨sb₂, 7 + (1 + t_app), .seq hexb₁ hex_ite, by dsimp only; omega, ?_, ?_⟩
            · -- InnerInv (v + 1) (sb₂.setReg r_v (v + 1))
              have hadj_step := adjListUpTo_succ_pos hv hadj_uv
              dsimp only [InnerInv]
              rw [hadj_step]
              have hnot_m : (a_mat : Arr) ∉ (listAppend a_end a_entries r_u r_cnt (.reg r_v)).writtenArrs := by
                simp [listAppend, Cmd.writtenArrs, hne_me', hne_ment']
              have hnot_s : (a_start : Arr) ∉ (listAppend a_end a_entries r_u r_cnt (.reg r_v)).writtenArrs := by
                simp [listAppend, Cmd.writtenArrs, hne_se', hne_sent']
              have hmat_eq := Exec.arrs_eq_of_not_mem_writtenArrs hex_app hnot_m
              have hs_eq := Exec.arrs_eq_of_not_mem_writtenArrs hex_app hnot_s
              -- Notice listAppend executes as 3 primitive steps so we can also preserve hprev_v
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
                        simp [sb₁, Expr.eval, checkWord, hne_cval', hrcnt_v,
                          show u * n + (adjListUpTo G uFin v).length < 2 ^ w by omega] at hidx1
                        subst hidx1
                        simp [sb₁, Expr.eval, checkWord, hne_uc', hne_uval', hru_v, hu_w] at hidx2
                        subst hidx2
                        have hmat_orig : IsAdjMatrix G a_mat s_v := ⟨hlen_mat, hmat_entries⟩
                        refine ⟨hmat_orig.of_arrs_eq (by simp [sb₁, hne_me', hne_ment']),
                          by simp [sb₁, hlen_s_v],
                          by simp [sb₁, hlen_e_v],
                          by simp [sb₁, hlen_ent_v],
                          by simp [hne_uv', hru_sb₂],
                          by simp,
                          by simp [hne_vc'.symm, hrcnt_sb₂],
                          hlist_sb₂.of_arrs_eq rfl rfl rfl,
                          fun u' hu' => ?_⟩
                        have hlen_u' : (adjListOf G u').length ≤ n := adjListUpTo_length_le G u' n
                        exact (isListAt_preserve_prev hne_se hne_sent hne_eent hu' hlen_u'
                          (by omega) (hprev_v u' hu')).of_arrs_eq rfl rfl rfl
            · have hnot_rv : (r_v : Reg) ∉ (listAppend a_end a_entries r_u r_cnt (.reg r_v)).writtenRegs := by
                simp [listAppend, Cmd.writtenRegs, hne_vc']
              have hrv_eq := Exec.regs_eq_of_not_mem_writtenRegs hex_app hnot_rv
              simp [hrv_eq, sb₁, hne_vval', hrv_v]
          · have hmval_eq0 : mval = 0 := by
              by_contra hne0
              exact hadj_uv (hmat_iff.mp hne0)
            rw [hmval_eq0] at hcond_sb₁
            have hex_ite : Exec w
                (.ite (.reg r_val) (listAppend a_end a_entries r_u r_cnt (.reg r_v)) .skip)
                sb₁ sb₁ (1 + 1) := .ite_false hcond_sb₁ (.skip sb₁)
            refine ⟨sb₁, 7 + (1 + 1), .seq hexb₁ hex_ite, by dsimp only; omega, ?_,
              by simp [sb₁, hne_vval', hrv_v]⟩
            have hadj_step := adjListUpTo_succ_neg hv hadj_uv
            dsimp only [InnerInv]
            rw [hadj_step]
            refine ⟨⟨hlen_mat, hmat_entries⟩, hlen_s_v, hlen_e_v, hlen_ent_v,
              by simp [sb₁, hne_uv', hne_uval', hru_v],
              by simp,
              by simp [sb₁, hne_vc'.symm, hne_cval', hrcnt_v],
              hlist_v, hprev_v⟩
      rcases hInnerLoop sa₄ hInner₀ with
        ⟨s_end, t_in, hex_in, ht_in, hmat_end, hlen_s_end, hlen_e_end, hlen_ent_end,
          hru_end, _, _, hlist_end, hprev_end⟩
      dsimp only at ht_in
      refine ⟨s_end, 4 + (3 + (3 + (2 + t_in))),
        .seq hexa₁ (.seq hexa₂ (.seq hexa₃ (.seq hexa₄ hex_in))),
        by dsimp only; omega, ?_, hru_end⟩
      refine ⟨hmat_end, hlen_s_end, hlen_e_end, hlen_ent_end, by simp, fun u' hu' => ?_⟩
      by_cases hu'_eq : u'.1 = u
      · have hu'_fin : u' = uFin := Fin.ext hu'_eq
        subst hu'_fin
        exact hlist_end.of_arrs_eq rfl rfl rfl
      · exact (hprev_end u' (by omega)).of_arrs_eq rfl rfl rfl
  rcases hOuterLoop s₄ hOuter₀ with
    ⟨s_final, t_out, hex_out, ht_out, hmat_final, hlen_s_final, hlen_e_final, hlen_ent_final,
      _, hlists_final⟩
  dsimp only at ht_out
  refine ⟨s_final, (1 + n) + ((1 + n) + ((1 + n * n) + (2 + t_out))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex_out))), ?_,
    hmat_final, ?_, hlen_ent_final⟩
  · dsimp only
    have hmul : n * (7 + (15 + 25 * n)) = n * 22 + n * (25 * n) := by
      have h715 : 7 + (15 + 25 * n) = 22 + 25 * n := by omega
      rw [h715, Nat.mul_add]
    have hmul2 : n * (25 * n) = 25 * (n * n) := Nat.mul_left_comm n 25 n
    omega
  · refine ⟨⟨hlen_s_final, hlen_e_final, fun u => ?_⟩, isAdjListFamily_adjListOf G⟩
    exact ⟨u.1 * n, u.1 * n + (adjListOf G u).length, hlists_final u u.2⟩

/-! ### Connection to Mathlib's `Graph α β` -/

/-- Given a multigraph `H : Graph α β` and a vertex numbering `φ : Fin n ≃ H.vertexSet`, read off
the underlying simple graph `SimpleGraph (Fin n)` where distinct vertices `u ≠ v` are adjacent if
and only if `(φ u).1` and `(φ v).1` are adjacent in `H`. -/
def underlyingSimpleGraph {α β : Type*} {n : ℕ} (H : Graph α β) (φ : Fin n ≃ H.vertexSet) :
    SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ H.Adj (φ u).1 (φ v).1
  symm := ⟨fun _ _ ⟨hne, hadj⟩ => ⟨hne.symm, hadj.symm⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

@[simp]
theorem underlyingSimpleGraph_adj {α β : Type*} {n : ℕ} (H : Graph α β)
    (φ : Fin n ≃ H.vertexSet) (u v : Fin n) :
    (underlyingSimpleGraph H φ).Adj u v ↔ u ≠ v ∧ H.Adj (φ u).1 (φ v).1 :=
  Iff.rfl

/-- State predicate stating that arrays `(a_eu, a_ev)` of length `m` list the endpoints of the
edges of `H : Graph α β` under vertex numbering `φ : Fin n ≃ H.vertexSet`. -/
def IsEdgeList {α β : Type*} {n : ℕ} (H : Graph α β) (φ : Fin n ≃ H.vertexSet)
    (a_eu a_ev : Arr) (m : ℕ) (s : State) : Prop :=
  ∃ (heu : (s.arrs a_eu).length = m) (hev : (s.arrs a_ev).length = m),
    (∀ k, ∀ (hk : k < m),
      (s.arrs a_eu)[k]'(by rw [heu]; exact hk) < n ∧
      (s.arrs a_ev)[k]'(by rw [hev]; exact hk) < n) ∧
    ∀ u v : Fin n, u ≠ v →
      (H.Adj (φ u).1 (φ v).1 ↔
        ∃ k, ∃ (hk : k < m),
          ((s.arrs a_eu)[k]'(by rw [heu]; exact hk) = u.1 ∧
            (s.arrs a_ev)[k]'(by rw [hev]; exact hk) = v.1) ∨
          ((s.arrs a_eu)[k]'(by rw [heu]; exact hk) = v.1 ∧
            (s.arrs a_ev)[k]'(by rw [hev]; exact hk) = u.1))

/-- Build the `n × n` adjacency matrix `a_mat` of `underlyingSimpleGraph H φ` from edge-endpoint
arrays `(a_eu, a_ev)` of length `m` using scratch registers `r_k, r_u, r_v`. -/
def edgeListToMatProg (n m : ℕ) (a_eu a_ev a_mat : Arr) (r_k r_u r_v : Reg) : Cmd :=
  .seq (allocFillArr a_mat (.const (n * n)) (.const 0) r_k)
    (.seq (.assign r_k (.const 0))
      (forUp r_k (.const m)
        (.seq (.assign r_u (.read a_eu (.reg r_k)))
          (.seq (.assign r_v (.read a_ev (.reg r_k)))
            (.ite (.op .eq (.reg r_u) (.reg r_v))
              .skip
              (.seq
                (.write a_mat (.op .add (.op .mul (.reg r_u) (.const n)) (.reg r_v)) (.const 1))
                (.write a_mat (.op .add (.op .mul (.reg r_v) (.const n)) (.reg r_u)) (.const 1))))))))

/-- Specification for `edgeListToMatProg`: builds the `n × n` adjacency matrix of
`underlyingSimpleGraph H φ` from edge-endpoint arrays `(a_eu, a_ev)` of length `m` in at most
`13 * (n * n) + 30 * m + 12` steps. -/
theorem Triple.edgeListToMatProg_spec {α β : Type*} {w n m : ℕ}
    (H : Graph α β) (φ : Fin n ≃ H.vertexSet)
    (a_eu a_ev a_mat : ℕ) (r_k r_u r_v : ℕ)
    (hne_um : a_eu ≠ a_mat) (hne_vm : a_ev ≠ a_mat)
    (hne_ku : r_k ≠ r_u) (hne_kv : r_k ≠ r_v) (hne_uv : r_u ≠ r_v)
    (hw : 1 < 2 ^ w) (hnn_w : n * n < 2 ^ w) (hm_w : m < 2 ^ w) :
    ⦃IsEdgeList H φ a_eu a_ev m⦄[w]
      edgeListToMatProg n m a_eu a_ev a_mat r_k r_u r_v
    ⦃IsAdjMatrix (underlyingSimpleGraph H φ) a_mat⦄ ≤
      fun _ => 13 * (n * n) + 30 * m + 12 := by
  have hn_le_nn : n ≤ n * n := Nat.le_mul_self n
  have hn_w : n < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hne_um' : (a_eu : Arr) ≠ a_mat := by omega
  have hne_vm' : (a_ev : Arr) ≠ a_mat := by omega
  have hne_ku' : (r_k : Reg) ≠ r_u := by omega
  have hne_kv' : (r_k : Reg) ≠ r_v := by omega
  have hne_uv' : (r_u : Reg) ≠ r_v := by omega
  intro s₀ hs₀
  -- Step 1: allocFillArr a_mat (.const (n * n)) (.const 0) r_k
  rcases Triple.allocFillArr_const a_mat (n * n) 0 r_k hw hnn_w h0_w s₀ trivial with
    ⟨s₁, t₁, hex₁, ht₁, harr₁⟩
  dsimp only at ht₁
  have hlen₁ : (s₁.arrs a_mat).length = n * n := by simp [harr₁]
  have hnot_eu : (a_eu : Arr) ∉ (allocFillArr a_mat (.const (n * n)) (.const 0) r_k).writtenArrs := by
    simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs, hne_um']
  have hnot_ev : (a_ev : Arr) ∉ (allocFillArr a_mat (.const (n * n)) (.const 0) r_k).writtenArrs := by
    simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs, hne_vm']
  have heu_eq₁ := Exec.arrs_eq_of_not_mem_writtenArrs hex₁ hnot_eu
  have hev_eq₁ := Exec.arrs_eq_of_not_mem_writtenArrs hex₁ hnot_ev
  have hedge₁ : IsEdgeList H φ a_eu a_ev m s₁ := by
    rcases hs₀ with ⟨heu, hev, hbounds, hiff⟩
    exact ⟨by simpa [heu_eq₁] using heu, by simpa [hev_eq₁] using hev,
      fun k hk => by simpa [heu_eq₁, hev_eq₁] using hbounds k hk,
      fun u v hne => by simpa [heu_eq₁, hev_eq₁] using hiff u v hne⟩
  -- Step 2: r_k := 0
  have heval0 : (Expr.const 0).eval w s₁ = some 0 := by simp [checkWord, h0_w]
  let s₂ := s₁.setReg r_k 0
  have hex₂ : Exec w (.assign r_k (.const 0)) s₁ s₂ 2 := .assign heval0
  -- Loop invariant over k ≤ m
  let LoopInv (k : ℕ) (s : State) : Prop :=
    s.regs r_k = k ∧
    IsEdgeList H φ a_eu a_ev m s ∧
    ∃ (hk_le : k ≤ m) (hlen : (s.arrs a_mat).length = n * n)
      (heu : (s.arrs a_eu).length = m) (hev : (s.arrs a_ev).length = m),
      ∀ u v : Fin n,
        let val := (s.arrs a_mat)[u.1 * n + v.1]'(by rw [hlen]; exact mul_add_lt_mul u.2 v.2)
        val ≤ 1 ∧
        (val ≠ 0 ↔
          u ≠ v ∧
          ∃ j, ∃ (hj : j < k),
            ((s.arrs a_eu)[j]'(by omega) = u.1 ∧ (s.arrs a_ev)[j]'(by omega) = v.1) ∨
            ((s.arrs a_eu)[j]'(by omega) = v.1 ∧ (s.arrs a_ev)[j]'(by omega) = u.1))
  have hLoop₀ : LoopInv 0 s₂ := by
    rcases hedge₁ with ⟨heu₁, hev₁, hbounds₁, hiff₁⟩
    refine ⟨by simp [s₂], ⟨heu₁, hev₁, hbounds₁, hiff₁⟩,
      Nat.zero_le m, hlen₁, heu₁, hev₁, fun u v => ?_⟩
    simp [s₂, harr₁]
  have hLoop :
      ⦃LoopInv 0⦄[w]
        forUp r_k (.const m)
          (.seq (.assign r_u (.read a_eu (.reg r_k)))
            (.seq (.assign r_v (.read a_ev (.reg r_k)))
              (.ite (.op .eq (.reg r_u) (.reg r_v))
                .skip
                (.seq
                  (.write a_mat (.op .add (.op .mul (.reg r_u) (.const n)) (.reg r_v)) (.const 1))
                  (.write a_mat (.op .add (.op .mul (.reg r_v) (.const n)) (.reg r_u)) (.const 1))))))
      ⦃LoopInv m⦄ ≤ fun _ => 3 + m * (7 + 23) := by
    apply Triple.forUp_const LoopInv m 23 hw hm_w
    · intro k _ s ⟨hrk, _, _⟩
      exact ⟨hrk, by simp [Expr.eval, checkWord, hm_w]⟩
    · intro k hk s_k ⟨hrk, hedge_k, _, hlen_m, heu_k, hev_k, hmat_k⟩
      have hk_w : k < 2 ^ w := by omega
      rcases hedge_k with ⟨_, _, hbounds_k, hiff_k⟩
      obtain ⟨hu_lt_n, hv_lt_n⟩ := hbounds_k k hk
      have huk_lt_n : (s_k.arrs a_eu)[k]'(by omega) < n := hu_lt_n
      have hvk_lt_n : (s_k.arrs a_ev)[k]'(by omega) < n := hv_lt_n
      have huk_w : (s_k.arrs a_eu)[k]'(by omega) < 2 ^ w := by omega
      have hvk_w : (s_k.arrs a_ev)[k]'(by omega) < 2 ^ w := by omega
      -- Read a_eu[r_k] into r_u (cost 3)
      have hread_u : (Expr.read a_eu (.reg r_k)).eval w s_k =
          some ((s_k.arrs a_eu)[k]'(by omega)) := by
        have hk_eu : k < (s_k.arrs a_eu).length := by omega
        simp [Expr.eval, checkWord, hrk, hk_w, hk_eu, huk_w]
      let sb₁ := s_k.setReg r_u ((s_k.arrs a_eu)[k]'(by omega))
      have hexb₁ : Exec w (.assign r_u (.read a_eu (.reg r_k))) s_k sb₁ 3 := .assign hread_u
      -- Read a_ev[r_k] into r_v (cost 3)
      have hread_v : (Expr.read a_ev (.reg r_k)).eval w sb₁ =
          some ((s_k.arrs a_ev)[k]'(by omega)) := by
        have hk_ev : k < (s_k.arrs a_ev).length := by omega
        simp [sb₁, Expr.eval, checkWord, hne_ku', hrk, hk_w, hk_ev, hvk_w]
      let sb₂ := sb₁.setReg r_v ((s_k.arrs a_ev)[k]'(by omega))
      have hexb₂ : Exec w (.assign r_v (.read a_ev (.reg r_k))) sb₁ sb₂ 3 := .assign hread_v
      by_cases heq_uv : (s_k.arrs a_eu)[k]'(by omega) = (s_k.arrs a_ev)[k]'(by omega)
      · have hcond_eq : (Expr.op .eq (.reg r_u) (.reg r_v)).eval w sb₂ = some 1 := by
          simp [sb₂, sb₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hne_uv',
            heq_uv, hvk_w, hw]
        have hex_ite : Exec w
            (.ite (.op .eq (.reg r_u) (.reg r_v))
              .skip
              (.seq
                (.write a_mat (.op .add (.op .mul (.reg r_u) (.const n)) (.reg r_v)) (.const 1))
                (.write a_mat (.op .add (.op .mul (.reg r_v) (.const n)) (.reg r_u)) (.const 1))))
            sb₂ sb₂ (3 + 1) := .ite_true hcond_eq (by omega) (.skip sb₂)
        refine ⟨sb₂, 3 + (3 + (3 + 1)), .seq hexb₁ (.seq hexb₂ hex_ite), by dsimp only; omega, ?_,
          by simp [sb₂, sb₁, hne_kv', hne_ku', hrk]⟩
        refine ⟨by simp, ⟨heu_k, hev_k, hbounds_k, hiff_k⟩,
          by omega, hlen_m, heu_k, hev_k, fun u v => ?_⟩
        obtain ⟨hle_uv, hiff_uv⟩ := hmat_k u v
        refine ⟨hle_uv, hiff_uv.trans ?_⟩
        constructor
        · rintro ⟨hne, j, hj, hmatch⟩
          exact ⟨hne, j, by omega, hmatch⟩
        · rintro ⟨hne, j, hj, hmatch⟩
          by_cases hjk : j = k
          · subst hjk
            exfalso
            rcases hmatch with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact hne (Fin.ext (by rw [← h1, ← h2]; exact heq_uv))
            · exact hne (Fin.ext (by rw [← h2, ← h1]; exact heq_uv.symm))
          · exact ⟨hne, j, by omega, hmatch⟩
      · have hcond_ne : (Expr.op .eq (.reg r_u) (.reg r_v)).eval w sb₂ = some 0 := by
          simp [sb₂, sb₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hne_uv',
            heq_uv, huk_w, hvk_w, h0_w]
        let uk := (s_k.arrs a_eu)[k]'(by omega)
        let vk := (s_k.arrs a_ev)[k]'(by omega)
        have idx1_lt : uk * n + vk < n * n := mul_add_lt_mul huk_lt_n hvk_lt_n
        have idx2_lt : vk * n + uk < n * n := mul_add_lt_mul hvk_lt_n huk_lt_n
        have hun_w : uk * n < 2 ^ w := by omega
        have hvn_w : vk * n < 2 ^ w := by omega
        have hidx1_w : uk * n + vk < 2 ^ w := by omega
        have hidx2_w : vk * n + uk < 2 ^ w := by omega
        have heval_idx1 :
            (Expr.op .add (.op .mul (.reg r_u) (.const n)) (.reg r_v)).eval w sb₂ =
              some (uk * n + vk) := by
          simp [sb₂, sb₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hne_uv',
            uk, vk, huk_w, hvk_w, hn_w, hun_w, hidx1_w]
        have heval_one1 : (Expr.const 1).eval w sb₂ = some 1 := by simp [checkWord, hw]
        let sb₃ := sb₂.writeArr a_mat (uk * n + vk) 1
        have hex_w1 : Exec w
            (.write a_mat (.op .add (.op .mul (.reg r_u) (.const n)) (.reg r_v)) (.const 1))
            sb₂ sb₃ 7 := .write heval_idx1 heval_one1 (by simp [sb₂, sb₁, hlen_m, idx1_lt])
        have heval_idx2 :
            (Expr.op .add (.op .mul (.reg r_v) (.const n)) (.reg r_u)).eval w sb₃ =
              some (vk * n + uk) := by
          simp [sb₃, sb₂, sb₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hne_uv',
            uk, vk, huk_w, hvk_w, hn_w, hvn_w, hidx2_w]
        have heval_one2 : (Expr.const 1).eval w sb₃ = some 1 := by simp [checkWord, hw]
        let sb₄ := sb₃.writeArr a_mat (vk * n + uk) 1
        have hex_w2 : Exec w
            (.write a_mat (.op .add (.op .mul (.reg r_v) (.const n)) (.reg r_u)) (.const 1))
            sb₃ sb₄ 7 := .write heval_idx2 heval_one2 (by simp [sb₃, sb₂, sb₁, hlen_m, idx2_lt])
        have hex_ite : Exec w
            (.ite (.op .eq (.reg r_u) (.reg r_v))
              .skip
              (.seq
                (.write a_mat (.op .add (.op .mul (.reg r_u) (.const n)) (.reg r_v)) (.const 1))
                (.write a_mat (.op .add (.op .mul (.reg r_v) (.const n)) (.reg r_u)) (.const 1))))
            sb₂ sb₄ (3 + (7 + 7)) := .ite_false hcond_ne (.seq hex_w1 hex_w2)
        refine ⟨sb₄, 3 + (3 + (3 + (7 + 7))), .seq hexb₁ (.seq hexb₂ hex_ite), by dsimp only; omega, ?_,
          by simp [sb₄, sb₃, sb₂, sb₁, hne_kv', hne_ku', hrk]⟩
        refine ⟨by simp,
          ⟨by simp [sb₄, sb₃, sb₂, sb₁, heu_k],
            by simp [sb₄, sb₃, sb₂, sb₁, hev_k],
            fun j hj => by simpa [sb₄, sb₃, sb₂, sb₁, hne_um', hne_vm'] using hbounds_k j hj,
            fun u v hne => by simpa [sb₄, sb₃, sb₂, sb₁, hne_um', hne_vm'] using hiff_k u v hne⟩,
          by omega,
          by simp [sb₄, sb₃, sb₂, sb₁, hlen_m],
          by simp [sb₄, sb₃, sb₂, sb₁, heu_k],
          by simp [sb₄, sb₃, sb₂, sb₁, hev_k],
          fun u v => ?_⟩
        simp only [sb₄, sb₃, sb₂, sb₁, State.setReg_arrs, State.writeArr_arrs_self,
          State.writeArr_arrs_ne _ _ _ hne_um', State.writeArr_arrs_ne _ _ _ hne_vm']
        by_cases h2 : u.1 * n + v.1 = vk * n + uk
        · have ⟨hu_eq, hv_eq⟩ := mul_add_inj v.2 huk_lt_n h2
          have hset2 : (((s_k.arrs a_mat).set (uk * n + vk) 1).set (vk * n + uk) 1)[u.1 * n + v.1]'(by
              rw [List.length_set, List.length_set, hlen_m]; exact mul_add_lt_mul u.2 v.2) = 1 := by
            simp only [h2]
            exact List.getElem_set_self (by simp [hlen_m, idx2_lt])
          rw [hset2]
          refine ⟨le_rfl, ?_⟩
          simp only [ne_eq, one_ne_zero, not_false_eq_true, true_iff]
          refine ⟨fun h_eq => heq_uv (by have := congrArg Fin.val h_eq; omega),
            k, by omega, Or.inr ⟨hv_eq.symm, hu_eq.symm⟩⟩
        · rw [List.getElem_set_ne (Ne.symm h2)]
          by_cases h1 : u.1 * n + v.1 = uk * n + vk
          · have ⟨hu_eq, hv_eq⟩ := mul_add_inj v.2 hvk_lt_n h1
            have hset1 : ((s_k.arrs a_mat).set (uk * n + vk) 1)[u.1 * n + v.1]'(by
                rw [List.length_set, hlen_m]; exact mul_add_lt_mul u.2 v.2) = 1 := by
              simp only [h1]
              exact List.getElem_set_self (by simp [hlen_m, idx1_lt])
            rw [hset1]
            refine ⟨le_rfl, ?_⟩
            simp only [ne_eq, one_ne_zero, not_false_eq_true, true_iff]
            refine ⟨fun h_eq => heq_uv (by have := congrArg Fin.val h_eq; omega),
              k, by omega, Or.inl ⟨hu_eq.symm, hv_eq.symm⟩⟩
          · rw [List.getElem_set_ne (Ne.symm h1)]
            obtain ⟨hle_uv, hiff_uv⟩ := hmat_k u v
            refine ⟨hle_uv, hiff_uv.trans ?_⟩
            constructor
            · rintro ⟨hne, j, hj, hmatch⟩
              exact ⟨hne, j, by omega, hmatch⟩
            · rintro ⟨hne, j, hj, hmatch⟩
              by_cases hjk : j = k
              · subst hjk
                exfalso
                rcases hmatch with ⟨hu_eq, hv_eq⟩ | ⟨hv_eq, hu_eq⟩
                · exact h1 (by rw [← hu_eq, ← hv_eq])
                · exact h2 (by rw [← hu_eq, ← hv_eq])
              · exact ⟨hne, j, by omega, hmatch⟩
  rcases hLoop s₂ hLoop₀ with ⟨s₃, t₃, hex₃, ht₃, _, ⟨_, _, _, hiff₃⟩, _, hlen₃, _, _, hmat₃⟩
  dsimp only at ht₃
  refine ⟨s₃, t₁ + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by dsimp only; omega, hlen₃, ?_⟩
  intro u v
  obtain ⟨hle_uv, hiff_uv⟩ := hmat₃ u v
  refine ⟨hiff_uv.trans ?_, hle_uv⟩
  rw [underlyingSimpleGraph_adj]
  constructor
  · rintro ⟨hne, j, hj, hmatch⟩
    exact ⟨hne, (hiff₃ u v hne).mpr ⟨j, hj, hmatch⟩⟩
  · rintro ⟨hne, hadj⟩
    exact ⟨hne, (hiff₃ u v hne).mp hadj⟩

end GraphMinor.Compute
