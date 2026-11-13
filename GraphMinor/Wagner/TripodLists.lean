module

public import GraphMinor.Wagner.SocietyBridge

/-!
# Tripods as lists of vertices

Graph Minors IX describes a tripod with paths that are subgraphs. For our case analysis it is easier
to work with lists of vertices. This file turns a tripod of the society `society K R L` into a
`Tripod` record: two ends `u`, `v`, three paths between them written as lists, an inner vertex
`s i` on the `i`-th path, and three disjoint paths `s i :: r i` from `s i` to vertices `t i` of
`L`, which meet the first three paths only at `s i` and meet `L` only at `t i`.

The main result is `exists_tripod`.
-/

@[expose] public section

namespace GraphMinor.Wagner

open Set Function Graph GraphMinor GraphMinor.GM09 GraphMinor.Surface

variable {γ : Type*}

/-- The list `l` is a path of `K` inside `R` from `a` to `b`. -/
def IsPathFT (K : SimpleGraph γ) (R : Set γ) (l : List γ) (a b : γ) : Prop :=
  l.Nodup ∧ l.IsChain K.Adj ∧ (∀ x ∈ l, x ∈ R) ∧ l.head? = some a ∧ l.getLast? = some b

variable {K : SimpleGraph γ} {R : Set γ}

theorem walk_support_facts {P : Graph γ (Sym2 γ)} (hP : P ≤ sGraph K R) {a b : γ}
    (W : GraphWalk P a b) :
    W.support.IsChain K.Adj ∧ (∀ x ∈ W.support, x ∈ R) ∧ W.support.head? = some a ∧
      W.support.getLast? = some b := by
  induction W with
  | nil hv =>
    refine ⟨List.isChain_singleton _, ?_, rfl, rfl⟩
    intro x hx
    simp only [GraphWalk.support, List.mem_singleton] at hx
    subst hx
    exact hP.vertexSet_mono hv
  | @cons x y z e hlink rest ih =>
    obtain ⟨hc, hR, hh, hl⟩ := ih
    have hl' := sGraph_isLink.mp (hlink.mono hP)
    simp only [GraphWalk.support]
    rcases hs : rest.support with _ | ⟨w, t⟩
    · rw [hs] at hh
      simp at hh
    · rw [hs] at hh hc hR hl
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      refine ⟨List.IsChain.cons_cons hl'.1.2 hc, ?_, rfl, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hl'.2.1
        · exact hR a ha
      · rw [List.getLast?_cons_cons]
        exact hl

theorem exists_pathFT {P : Graph γ (Sym2 γ)} {a b : γ} (h : IsGraphPathWithEnds (sGraph K R) P a b) :
    ∃ l, IsPathFT K R l a b ∧ V(P) = {x | x ∈ l} := by
  obtain ⟨hle, W, hW, hV, -⟩ := h
  obtain ⟨hc, hR, hh, hl⟩ := walk_support_facts hle W
  exact ⟨W.support, ⟨hW, hc, hR, hh, hl⟩, hV⟩

theorem getLast?_cons_append_singleton (x y : γ) :
    ∀ m : List γ, (x :: (m ++ [y])).getLast? = some y
  | [] => rfl
  | a :: m => by
    rw [List.cons_append, List.getLast?_cons_cons]
    exact getLast?_cons_append_singleton a y m

/-- A path list with distinct ends `a ≠ b` has the form `a :: m ++ [b]`. -/
theorem IsPathFT.eq_cons_append {l : List γ} {a b : γ} (h : IsPathFT K R l a b) (hab : a ≠ b) :
    ∃ m, l = a :: m ++ [b] := by
  obtain ⟨-, -, -, hh, hl⟩ := h
  rcases l with _ | ⟨x, l'⟩
  · simp at hh
  · simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    rcases List.eq_nil_or_concat l' with rfl | ⟨m, y, rfl⟩
    · simp at hl
      exact (hab hl).elim
    · refine ⟨m, ?_⟩
      have hyb : y = b := by
        rw [List.concat_eq_append, getLast?_cons_append_singleton] at hl
        simpa using hl
      subst hyb
      simp

/-- A tripod of a society built from `K`, given by lists of vertices.

The `i`-th path from `u` to `v` is `pl i = u :: pre i ++ s i :: post i ++ [v]`, and the `i`-th
redirecting path is `ql i = s i :: r i`, from `s i` to `t i`. -/
structure Tripod (K : SimpleGraph γ) (R Ω : Set γ) where
  /-- One common end of the three paths. -/
  u : γ
  /-- The other common end of the three paths. -/
  v : γ
  /-- The inner vertex of the `i`-th path where the `i`-th redirecting path starts. -/
  s : Fin 3 → γ
  /-- The end in `Ω` of the `i`-th redirecting path. -/
  t : Fin 3 → γ
  /-- The part of the `i`-th path strictly between `u` and `s i`. -/
  pre : Fin 3 → List γ
  /-- The part of the `i`-th path strictly between `s i` and `v`. -/
  post : Fin 3 → List γ
  /-- The `i`-th redirecting path without its first vertex `s i`. -/
  r : Fin 3 → List γ
  huv : u ≠ v
  hp : ∀ i, IsPathFT K R (u :: pre i ++ s i :: post i ++ [v]) u v
  hpp : ∀ i j, i ≠ j → ∀ x, x ∈ u :: pre i ++ s i :: post i ++ [v] →
    x ∈ u :: pre j ++ s j :: post j ++ [v] → x = u ∨ x = v
  hq : ∀ i, IsPathFT K R (s i :: r i) (s i) (t i)
  ht : ∀ i, t i ∈ Ω
  hqX : ∀ i j x, x ∈ r i → x ∉ u :: pre j ++ s j :: post j ++ [v]
  hqΩ : ∀ i x, x ∈ s i :: r i → x ∈ Ω → x = t i
  hqq : ∀ i j, i ≠ j → ∀ x, x ∈ s i :: r i → x ∉ s j :: r j

/-- A path with distinct ends and an inner vertex `s` splits at `s`. -/
theorem IsPathFT.split {l : List γ} {a b s : γ} (h : IsPathFT K R l a b) (hab : a ≠ b)
    (hs : s ∈ l) (hsa : s ≠ a) (hsb : s ≠ b) :
    ∃ pre post, l = a :: pre ++ s :: post ++ [b] := by
  obtain ⟨m, rfl⟩ := h.eq_cons_append hab
  have hsm : s ∈ m := by
    have hs' : s = a ∨ s ∈ m ∨ s = b := by simpa using hs
    rcases hs' with h | h | h
    · exact (hsa h).elim
    · exact h
    · exact (hsb h).elim
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hsm
  exact ⟨pre, post, by simp⟩

variable [Finite γ] {L : List γ} {hnd : L.Nodup} {hne : L ≠ []} {hLR : ∀ x ∈ L, x ∈ R}

/-- A tripod of `society K R L` gives a `Tripod` record. -/
theorem exists_tripod {T₁ T₂ T₃ : Graph γ (Sym2 γ)}
    (h : (society K R L hnd hne hLR).IsTripod T₁ T₂ T₃) :
    Nonempty (Tripod K R {x | x ∈ L}) := by
  classical
  obtain ⟨u, v, huv, hP₁, hP₂, hP₃, h₁₂, h₁₃, h₂₃, s₁, hs₁, s₂, hs₂, s₃, hs₃, t₁, -, t₂, -, t₃, -,
    hred⟩ := h
  set S := society K R L hnd hne hLR with hS
  -- The three paths, indexed by `Fin 3`.
  let P : Fin 3 → Graph γ (Sym2 γ) := ![T₁, T₂, T₃]
  let s : Fin 3 → γ := ![s₁, s₂, s₃]
  have hP : ∀ i, IsGraphPathWithEnds (sGraph K R) (P i) u v := by
    intro i; fin_cases i
    · exact hP₁
    · exact hP₂
    · exact hP₃
  have hPP : ∀ i j, i ≠ j → V(P i) ∩ V(P j) = {u, v} := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [P, inter_comm]
  have hs : ∀ i, s i ∈ V(P i) \ {u, v} := by
    intro i; fin_cases i
    · exact hs₁
    · exact hs₂
    · exact hs₃
  have hsinj : Injective s := by
    intro i j hij
    by_contra hne'
    have hmem : s i ∈ V(P i) ∩ V(P j) := ⟨(hs i).1, hij ▸ (hs j).1⟩
    rw [hPP i j hne'] at hmem
    exact (hs i).2 hmem
  have hX' : {s₁, s₂, s₃} = range s := by
    ext x
    simp only [mem_insert_iff, mem_singleton_iff, mem_range]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [s]
  -- The redirecting paths.
  obtain ⟨hX'X, hY'Y, -, Pr, hPrdisj, hPr⟩ := hred
  choose x hx y hy hft using hPr
  have hxmem : ∀ k, x k ∈ V(Pr k) := by
    intro k
    have : x k ∈ V(Pr k) ∩ (V(T₁) ∪ V(T₂) ∪ V(T₃)) := by rw [(hft k).2.1]; rfl
    exact this.1
  have hxinj : Injective x := by
    intro k k' hkk'
    by_contra hne'
    exact disjoint_left.mp (hPrdisj hne') (hxmem k) (hkk' ▸ hxmem k')
  -- Each `s i` is the start of one redirecting path.
  have hsurj : ∀ i, ∃ k, x k = s i := by
    let f : Fin ({s₁, s₂, s₃} : Set γ).ncard → ({s₁, s₂, s₃} : Set γ) := fun k => ⟨x k, hx k⟩
    have hf : Injective f := fun k k' h => hxinj (congrArg Subtype.val h)
    have hfs : Surjective f :=
      (Finite.injective_iff_surjective_of_equiv (Finite.equivFin _).symm).mp hf
    intro i
    obtain ⟨k, hk⟩ := hfs ⟨s i, by rw [hX']; exact ⟨i, rfl⟩⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  choose σ hσ using hsurj
  have hσinj : Injective σ := by
    intro i j hij
    apply hsinj
    rw [← hσ i, ← hσ j, hij]
  -- Lists for all the paths.
  choose pl hpl hplV using fun i => exists_pathFT (hP i)
  choose ql hql hqlV using fun i => exists_pathFT (hft (σ i)).1
  have hsplit : ∀ i, ∃ pre post, pl i = u :: pre ++ s i :: post ++ [v] := by
    intro i
    have hsi := hs i
    have hsl : s i ∈ pl i := by
      have := hsi.1
      rw [hplV i] at this
      exact this
    simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or] at hsi
    exact (hpl i).split huv hsl hsi.2.1 hsi.2.2
  choose pre post hpp using hsplit
  have hqform : ∀ i, ∃ r, ql i = s i :: r := by
    intro i
    obtain ⟨-, -, -, hh, -⟩ := hql i
    rcases hqi : ql i with _ | ⟨a, r⟩
    · rw [hqi] at hh; simp at hh
    · rw [hqi] at hh
      simp only [List.head?_cons, Option.some.injEq] at hh
      exact ⟨r, by rw [hh, hσ i]⟩
  choose r hr using hqform
  -- Membership in the vertex set `X` of the three paths.
  have hXmem : ∀ z, (∃ j, z ∈ u :: pre j ++ s j :: post j ++ [v]) →
      z ∈ V(T₁) ∪ V(T₂) ∪ V(T₃) := by
    rintro z ⟨j, hj⟩
    rw [← hpp j] at hj
    have : z ∈ V(P j) := by rw [hplV j]; exact hj
    fin_cases j
    · exact Or.inl (Or.inl this)
    · exact Or.inl (Or.inr this)
    · exact Or.inr this
  have hqV : ∀ i z, z ∈ s i :: r i → z ∈ V(Pr (σ i)) := by
    intro i z hz
    rw [← hr i] at hz
    rw [hqlV i]
    exact hz
  refine ⟨⟨u, v, s, fun i => y (σ i), pre, post, r, huv, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i
    rw [← hpp i]
    exact hpl i
  · intro i j hij z hzi hzj
    rw [← hpp i] at hzi
    rw [← hpp j] at hzj
    have : z ∈ V(P i) ∩ V(P j) := ⟨by rw [hplV i]; exact hzi, by rw [hplV j]; exact hzj⟩
    rw [hPP i j hij] at this
    simpa using this
  · intro i
    rw [← hr i, ← hσ i]
    exact hql i
  · intro i
    exact hY'Y (hy (σ i))
  · intro i j z hz hzX
    have hzQ : z ∈ V(Pr (σ i)) := hqV i z (List.mem_cons_of_mem _ hz)
    have hzx : z ∈ V(Pr (σ i)) ∩ (V(T₁) ∪ V(T₂) ∪ V(T₃)) := ⟨hzQ, hXmem z ⟨j, hzX⟩⟩
    rw [(hft (σ i)).2.1, mem_singleton_iff, hσ i] at hzx
    have hnd' : (s i :: r i).Nodup := by rw [← hr i]; exact (hql i).1
    exact (List.nodup_cons.mp hnd').1 (hzx ▸ hz)
  · intro i z hz hzΩ
    have hzx : z ∈ V(Pr (σ i)) ∩ S.Ω.bar := ⟨hqV i z hz, hzΩ⟩
    rw [(hft (σ i)).2.2] at hzx
    exact hzx
  · intro i j hij z hzi hzj
    exact disjoint_left.mp (hPrdisj (hσinj.ne hij)) (hqV i z hzi) (hqV j z hzj)

end GraphMinor.Wagner
